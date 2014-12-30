#include <ccan/array_size/array_size.h>
#include <ccan/isaac/isaac64.h>
#include <ccan/ilog/ilog.h>
#include <ccan/err/err.h>
#include <ccan/opt/opt.h>
#include <stdio.h>
#include <assert.h>
#include <string.h>

/* We encode block number and distance (in # hashes) for the previous
 * path. */
struct path {
	int blocknum;
	size_t num_hashes;
};

struct block {
	uint64_t hash;
	/* which prev do we actually jump to. */
	size_t prev_used;
	/* These are merkled into a tree, but we hold them in an array. */
	size_t num_prevs;
	/* This is our distance to the genesis block. */
	size_t hashes_to_genesis;
	struct path *prevs;
};


/* RFC 6962 approach is just to built the tree from an array, in order,
 * using external nodes:
 *
 *         ^
 *        / \
 *       /\  \
 *      /  \  \
 *     /    \  \
 *    /\    /\  \
 *   0  1  2  3  4
 */
static size_t do_proof_len(size_t to, size_t start, size_t end)
{
	size_t len;

	/* Reached the node? */
	if (end - start == 1) {
		assert(to == start);
		return 0;
	}

	len = (1 << (ilog32(end - start - 1) - 1));
	if (to < start + len)
		return 1 + do_proof_len(to, start, start + len);
	return 1 + do_proof_len(to, start + len, end);
}

static size_t rfc6962_proof_len(const struct path *prevs, size_t num_prevs, size_t to)
{
	return do_proof_len(to, 0, num_prevs);
}

static size_t rev_rfc6962_proof_len(const struct path *prevs, size_t num_prevs, size_t to)
{
	return do_proof_len(num_prevs - to - 1, 0, num_prevs);
}

/*
 * See https://github.com/opentimestamps/opentimestamps-server/blob/master/doc/merkle-mountain-range.md
 *
 * We connect the peaks using rfc6962, which means that more recent
 * transactions are shorter.  eg. 7 elements makes three peaks:
 *
 *
 *   (1)     (2)    (3)
 *
 *    /\      /\     6
 *   /  \    4  5
 *  /\  /\ 
 * 0 1  2 3
 *
 * These are connected like so:
 *
 *          /\(3)
 *         /  6
 *        /\
 *       /  \
 *      /    \
 *     /(1)   \ (2)
 *    /\      /\
 *   /  \    4  5
 *  /\  /\ 
 * 0 1  2 3
 */
static size_t mmr_proof_len(const struct path *prevs, size_t num, size_t node)
{
	size_t mtns = __builtin_popcount(num), off = 0, peaknum = 0;
	int i;

	/* Which mountain is 'node' in? */
	for (i = sizeof(size_t) * CHAR_BIT - 1; i >= 0; i--) {
		size_t summit = (size_t)1 << i;
		if (num & summit) {
			off += summit;
			if (node < off)
				break;
			peaknum++;
		}
	}

	/* we need to get to mountain i, then down to element. */
	return rfc6962_proof_len(prevs, mtns, peaknum) + i;
}

/* So we need 1 hash if at depth 0, 3 at depth 1, etc. */
static size_t prooflen_for_internal_node(size_t depth)
{
	if (depth == 0)
		return 1;
	return (depth - 1) * 2 + 1;
}

/* Ideal case would use a breadth first internal node system.  Since
 * short proofs are more common than long proofs, the optimal is a
 * breadth first tree:
 *
 *             N
 *           /   \
 *          /     \
 *       N-1       N-2
 *      /   \     /   \
 *    N-3  N-4  N-5   N-6
 *
 * Of course, generating this to verify gets worse over time.
 *
 * The depth of a node == log2(dist). */
static size_t breadth_proof_len(const struct path *prevs, size_t num_prevs, size_t to)
{
	size_t depth = ilog32(num_prevs - to);

	return prooflen_for_internal_node(depth);
}

static size_t rev_breadth_proof_len(const struct path *prevs,
				    size_t num_prevs, size_t to)
{
	size_t depth = ilog32(to);

	return prooflen_for_internal_node(depth);
}

static size_t naive_proof_len(const struct path *prevs, size_t num_prevs, size_t to)
{
	size_t naive = ilog32(num_prevs);
	assert((1 << naive) >= num_prevs);
	return naive;
}

struct huff_node {
	/* If != -1 depth of target. */
	int depth;
	size_t score;
};

static int compare_scores(const void *va, const void *vb)
{
	const struct huff_node *a = va, *b = vb;

	if (a->score > b->score)
		return -1;
	else if (a->score < b->score)
		return 1;
	/* FIXME: In real life, must define second key for equal (ie. blocknum) */
	return 0;
}

/* Huffman by blocknum. */
static size_t huffman_proof_len(const struct path *prevs,
				size_t num_prevs, size_t to)
{
	struct huff_node huff[num_prevs];
	size_t i;

	for (i = 0; i < num_prevs; i++) {
		if (i == to)
			huff[i].depth = 0;
		else
			huff[i].depth = -1;
		huff[i].score = prevs[i].blocknum;
	}
	qsort(huff, num_prevs, sizeof(huff[0]), compare_scores);

	while (num_prevs != 1) {
		/* Combine least two. */
		struct huff_node comb;
		comb.score = huff[num_prevs-1].score + huff[num_prevs-2].score;
		comb.depth = -1;
		if (huff[num_prevs-1].depth != -1)
			comb.depth = huff[num_prevs-1].depth + 1;
		else if (huff[num_prevs-2].depth != -1)
			comb.depth = huff[num_prevs-2].depth + 1;
		num_prevs--;

		for (i = 0; i < num_prevs - 1; i++)
			if (huff[i].score < comb.score)
				break;
		memmove(huff + i + 1, huff + i, sizeof(huff[i]) * (num_prevs - 1 - i));
		huff[i] = comb;
	}

	assert(huff[0].depth >= 0);
	return huff[0].depth;
}
	
/* How deep is blocknum in the tree of prevs? */
static int proof_len(const struct path *prevs, size_t num_prevs, int blocknum,
		     size_t (*len_func)(const struct path *prevs,
					size_t num_prevs, size_t to))
{
	size_t i;

	/* Find this blocknum. */
	for (i = 0; i < num_prevs; i++) {
		if (prevs[i].blocknum == blocknum) {
			int len = len_func(prevs, num_prevs, i);
			assert(len);
			return len;
		}
	}
	/* It should have been in there... */
	abort();
}

/* make a copy of prevs from previous block, adding previous block in. */
static struct path *append_prev(const struct block *prev, int prev_blocknum,
				size_t *path_len,
				size_t (*len_func)(const struct path *prevs,
						   size_t, size_t))
{
	struct path *prevs;

	/* We want to include the prev they used, and add one. */
	*path_len = prev->prev_used + 2;
	prevs = calloc(sizeof(*prevs), *path_len);
	memcpy(prevs, prev->prevs, sizeof(*prevs) * (prev->prev_used+1));
	prevs[prev->prev_used+1].blocknum = prev_blocknum;
	prevs[prev->prev_used+1].num_hashes = prev->hashes_to_genesis
		+ proof_len(prevs, *path_len, prev_blocknum, len_func);

	return prevs;
}

static void print_incremental_length(size_t num, size_t target, size_t seed,
				     size_t (*len_func)(const struct path *,
							size_t, size_t))
{
	struct block *blocks;
	size_t i;
	struct isaac64_ctx isaac;

	isaac64_init(&isaac, (void *)&seed, sizeof(seed));
	blocks = calloc(sizeof(*blocks), num);
	blocks[0].prevs = calloc(sizeof(*blocks[0].prevs), 1);

	for (i = 1; i < num; i++) {
		uint64_t skip, best_distance;
		int j;

		/* Copy path into this block from previous block, adding
		 * the prev block. */
		blocks[i].prevs = append_prev(&blocks[i-1], i-1,
					      &blocks[i].num_prevs,
					      len_func);

		/* Free up old paths on blocks no longer on our path. */
		for (j = blocks[i-1].prev_used + 1;
		     j < blocks[i-1].num_prevs;
		     j++) {
			free(blocks[blocks[i-1].prevs[j].blocknum].prevs);
		}

		/* Now generate block. */
		blocks[i].hash = isaac64_next_uint64(&isaac);
		skip = -1ULL / blocks[i].hash;
		if (skip > i)
			skip = i;

		/* Find the best previous block we get to (and store in
		 * prev_used) */
		best_distance = -1ULL;
		for (j = 0; j < blocks[i].num_prevs; j ++) {
			size_t plen;

			/* Can't reach it? */
			if (blocks[i].prevs[j].blocknum < i - skip)
				continue;
			/* How many hashes to get to this prev? */
			plen = proof_len(blocks[i].prevs, blocks[i].num_prevs,
					 blocks[i].prevs[j].blocknum,
					 len_func);
			if (blocks[i].prevs[j].num_hashes + plen
			    < best_distance) {
				/* Use this one. */
				best_distance = blocks[i].prevs[j].num_hashes
					+ plen;
				blocks[i].prev_used = j;
			}
		}
		assert(best_distance != -1ULL);
		blocks[i].hashes_to_genesis = best_distance;
	}

	/* If we want to get to a specific target... */
	if (target)
		errx(1, "--target not implemented yet.");

	printf("prooflen: proof path %zu, hashes %zu\n",
	       blocks[num-1].num_prevs-1,
	       blocks[num-1].prevs[blocks[num-1].prev_used].num_hashes
		+ proof_len(blocks[num-1].prevs, blocks[num-1].num_prevs,
			    blocks[num-1].prevs[blocks[num-1].prev_used].blocknum,
			len_func));

#if 0
	for (i = num-1; i; i = blocks[i].prevs[blocks[i].prev_used].blocknum) {
		size_t j;
		printf("Block %zu:\n", i);
		printf("  Hashes to genesis %zu\n", blocks[i].hashes_to_genesis);
		printf("  Can jump %llu\n", -1ULL / blocks[i].hash);
		printf("  Contains %zu in path\n", blocks[i].num_prevs);
		printf("  Jumped to [%zu] (%zu back, %u hashes)\n",
		       blocks[i].prev_used,
		       i - blocks[i].prevs[blocks[i].prev_used].blocknum,
		       proof_len(blocks[i].prevs, blocks[i].num_prevs,
				 blocks[i].prevs[blocks[i].prev_used].blocknum));
		for (j = 0; j < blocks[i].num_prevs; j++) {
			printf("   %zu: %u (%zu hashes)\n",
			       j,
			       blocks[i].prevs[j].blocknum,
			       blocks[i].prevs[j].num_hashes);
		}
	}
#endif
}

static char *opt_set_breadth(size_t (**len_func)(const struct path *prevs,
						 size_t to, size_t start))
{
	*len_func = breadth_proof_len;
	return NULL;
}

static char *opt_set_rfc6962(size_t (**len_func)(const struct path *prevs,
						 size_t to, size_t start))
{
	*len_func = rfc6962_proof_len;
	return NULL;
}

static char *opt_set_rev_breadth(size_t (**len_func)(const struct path *prevs,
						     size_t to, size_t start))
{
	*len_func = rev_breadth_proof_len;
	return NULL;
}

static char *opt_set_rev_rfc6962(size_t (**len_func)(const struct path *prevs,
						     size_t to, size_t start))
{
	*len_func = rev_rfc6962_proof_len;
	return NULL;
}

static char *opt_set_huffman(size_t (**len_func)(const struct path *prevs,
						 size_t to, size_t start))
{
	*len_func = huffman_proof_len;
	return NULL;
}

static char *opt_set_naive(size_t (**len_func)(const struct path *prevs,
					       size_t to, size_t start))
{
	*len_func = naive_proof_len;
	return NULL;
}

int main(int argc, char *argv[])
{
	unsigned int num, seed = 0, target = 0;
	size_t (*len_func)(const struct path *prevs, size_t num_prevs, size_t to)
		= mmr_proof_len;

	opt_register_noarg("--usage|--help|-h", opt_usage_and_exit,
			   "<num>\n"
			   "Calculates proof length for SPV chains of block headers,\n"
			   " using various different prevtree topologies",
			   "Print this message");
	opt_register_arg("--target", opt_set_uintval, opt_show_uintval, &target,
			 "Block number to terminate SPV proof at");
	opt_register_noarg("--breadth", opt_set_breadth, &len_func,
			 "Use breadth-first tree for path");
	opt_register_noarg("--rfc6962", opt_set_rfc6962, &len_func,
			 "Use RFC6962 tree for path");
	opt_register_noarg("--rev-breadth", opt_set_rev_breadth, &len_func,
			 "Use breadth-last tree for path");
	opt_register_noarg("--rev-rfc6962", opt_set_rev_rfc6962, &len_func,
			 "Use reversed RFC6962 tree for path");
	opt_register_noarg("--huffman", opt_set_huffman, &len_func,
			 "Use huffman tree for path");
	opt_register_noarg("--naive", opt_set_naive, &len_func,
			 "Use naive tree for path");
	opt_register_arg("--seed", opt_set_uintval, opt_show_uintval, &seed,
			 "Seed for deterministic RNG");

	opt_parse(&argc, argv, opt_log_stderr_exit);
	if (argc != 2)
		opt_usage_and_exit(NULL);

	num = atoi(argv[1]);
	if (target >= num)
		errx(1, "Don't do that, you'll crash me");
	print_incremental_length(num, target, seed, len_func);

	return 0;
}
