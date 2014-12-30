#include <ccan/array_size/array_size.h>
#include <ccan/isaac/isaac64.h>
#include <ccan/ilog/ilog.h>
#include <ccan/err/err.h>
#include <ccan/opt/opt.h>
#include <stdio.h>
#include <assert.h>
#include <string.h>

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

static size_t rfc6962_proof_len(size_t from, size_t to)
{
	return do_proof_len(to, 0, from);
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
static size_t mmr_proof_len(size_t num, size_t node)
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
	return rfc6962_proof_len(mtns, peaknum) + i;
}

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

/* How deep is blocknum in the tree of prevs? */
static int proof_len(const struct path *prevs, size_t num_prevs, int blocknum)
{
	size_t i;

	/* Find this blocknum. */
	for (i = 0; i < num_prevs; i++) {
		if (prevs[i].blocknum == blocknum) {
			int len = mmr_proof_len(num_prevs, i);
			assert(len);
			return len;
		}
	}
	/* It should have been in there... */
	abort();
}

/* make a copy of prevs from previous block, adding previous block in. */
static struct path *append_prev(const struct block *prev, int prev_blocknum,
				size_t *path_len)
{
	struct path *prevs;

	/* We want to include the prev they used, and add one. */
	*path_len = prev->prev_used + 2;
	prevs = calloc(sizeof(*prevs), *path_len);
	memcpy(prevs, prev->prevs, sizeof(*prevs) * (prev->prev_used+1));
	prevs[prev->prev_used+1].blocknum = prev_blocknum;
	prevs[prev->prev_used+1].num_hashes = prev->hashes_to_genesis
		+ proof_len(prevs, *path_len, prev_blocknum);

	return prevs;
}

static void print_incremental_length(size_t num, size_t target, size_t seed)
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
					      &blocks[i].num_prevs);

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
					 blocks[i].prevs[j].blocknum);
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
			    blocks[num-1].prevs[blocks[num-1].prev_used].blocknum));

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

int main(int argc, char *argv[])
{
	unsigned int num, seed = 0, target = 0;

	opt_register_noarg("--usage|--help|-h", opt_usage_and_exit,
			   "<num>\n"
			   "Calculates proof length for SPV chains of block headers,\n"
			   " using various different prevtree topologies",
			   "Print this message");
	opt_register_arg("--target", opt_set_uintval, opt_show_uintval, &target,
			 "Block number to terminate SPV proof at");
	opt_register_arg("--seed", opt_set_uintval, opt_show_uintval, &seed,
			 "Seed for deterministic RNG");

	opt_parse(&argc, argv, opt_log_stderr_exit);
	if (argc != 2)
		opt_usage_and_exit(NULL);

	num = atoi(argv[1]);
	if (target >= num)
		errx(1, "Don't do that, you'll crash me");
	print_incremental_length(num, target, seed);

	return 0;
}
