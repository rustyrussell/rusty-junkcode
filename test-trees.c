#include "maakutree.h"
#include <ccan/array_size/array_size.h>
#include <ccan/isaac/isaac64.h>
#include <ccan/ilog/ilog.h>
#include <ccan/err/err.h>
#include <ccan/opt/opt.h>
#include <stdio.h>
#include <assert.h>
#include <string.h>

/* Trees with internal values look like so (from Maaku's Merkelized Prefix tree
 * BIP at https://gist.github.com/maaku/2aed2cb628024800044d ):
 *
 *       /\
 *      /  \
 *     /    \
 *  value   /\
 *         /  \
 *        /    \
 *       L      R
 *
 * So we need 1 hash if at depth 0, 3 at depth 1, etc. */
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
static size_t optimal_proof_len(size_t from, size_t to)
{
	size_t depth = ilog32(from - to);

	return prooflen_for_internal_node(depth);
}

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

	/* last node? */
	if (end - start <= 2) {
		assert(to >= start && to < end);
		return 1;
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

static size_t maaku_proof_len(size_t from, size_t to)
{
	struct maaku_tree t;
	size_t i, depth;

	t.max_depth = 0;
	t.root = NULL;
	for (i = 0; i < from; i++)
		add_maaku_node(&t, i);

	depth = find_maaku_node(t.root, to)->depth;
	free_maaku_tree(&t);

	return prooflen_for_internal_node(depth);
}

/*
 * Slightly less optimal, but incrementable, is to have a series of
 * breadth-first trees, in batches of N.
 *
 * eg. 
 *              /\
 *             /  \
 *            /    \
 *           /\    optimal tree for 196605... (under construction)
 *          /  \
 *         /    \
 *        /\  131070-196604
 *       /  \
 *      /    \
 *  0-65534 65535-131069
 *
 * There's also a variant where we simply back onto an rfc6962-style tree.
 */
#define SUBTREE_SIZE 65535

static size_t batch_proof_len(size_t from, size_t to, bool array)
{
	size_t from_tree, to_tree, tree_depth;

	from_tree = from / SUBTREE_SIZE;
	to_tree = to / SUBTREE_SIZE;

	if (from_tree == to_tree) {
		/* It's in the tree we're building.  This falls back to the
		 * optimal case if we only have one subtree so far */
		if (from < SUBTREE_SIZE)
			return optimal_proof_len(from, to);
		return 1 + optimal_proof_len(from, to);
	}

	if (array)
		/* Use rfc6862 for old entries. */
		return 1 + rfc6962_proof_len(from_tree * SUBTREE_SIZE, to);

	/* It's in an older tree.  One to get to the old trees, and
	 * one extra branch for every tree we go back. */
	tree_depth = 1 + from_tree - to_tree;

	/* First tree is just on the left branch, so subtract one. */
	if (to_tree == 0)
		tree_depth--;

	/* One hash to get to get down the tree, plus proof inside the
	 * tree. */
	return tree_depth + optimal_proof_len(SUBTREE_SIZE, to%SUBTREE_SIZE);
}

static size_t breadth_batch_proof_len(size_t from, size_t to)
{
	return batch_proof_len(from, to, false);
}

static size_t rfc6962_batch_proof_len(size_t from, size_t to)
{
	return batch_proof_len(from, to, true);
}

struct node {
	size_t val;
	struct node *child[2];
};

static struct node *new_node(size_t val, struct node *c1, struct node *c2)
{
	struct node *n = malloc(sizeof(*n));
	n->child[0] = c1;
	n->child[1] = c2;
	n->val = val;
	return n;
}

static void free_mmrtree(struct node *n)
{
	if (!n)
		return;
	free_mmrtree(n->child[0]);
	free_mmrtree(n->child[1]);
	free(n);
}

static struct node *fulltree(size_t off, size_t num)
{
	if (num == 1)
		return new_node(off, NULL, NULL);
	return new_node(-1, fulltree(off, num/2), fulltree(off + num/2, num/2));
}

static struct node *join_peaks(struct node **peaks, size_t num)
{
	size_t len;

	if (num == 1)
		return peaks[0];
	if (num == 2)
		return new_node(-1, peaks[0], peaks[1]);
	len = (1 << (ilog32(num - 1) - 1));
	return new_node(-1, join_peaks(peaks, len),
			join_peaks(peaks + len, num - len));
}

static struct node *build_mmrtree(size_t max)
{
	int i, off = 0, peaknum = 0;
	struct node *peaks[sizeof(size_t) * CHAR_BIT];

	/* First, make peaks.*/
	for (i = ARRAY_SIZE(peaks) - 1; i >= 0; i--) {
		size_t summit = (size_t)1 << i;
		if (max & summit) {
			peaks[peaknum++] = fulltree(off, summit);
			off += summit;
		}
	}
	assert(off == max);

	/* Now join peaks a-la RFC6962 */
	return join_peaks(peaks, peaknum);
}

static size_t mmr_tree_depth(const struct node *node, size_t val)
{
	size_t depth;

	if (!node)
		return -1;

	if (node->val == val)
		return 0;

	depth = mmr_tree_depth(node->child[0], val);
	if (depth == -1) {
		depth = mmr_tree_depth(node->child[1], val);
		if (depth == -1)
			return -1;
	}
	return depth + 1;
}

#if 0
static size_t mmr_proof_len_fast(size_t from, size_t to)
{
	size_t mtns = __builtin_popcount(from);
	size_t peak = 0, summit = 0;
	int i;

	for (i = sizeof(size_t)*8-1; i >= 0; --i)
	{
		summit = 1<<i;
		if (from & summit)
		{
			if (to & summit) ++peak;
			else             break;
		}
	}

	return rfc6962_proof_len(mtns, peak) + ilog32(summit);
}
#endif

static size_t mmr_proof_len(size_t from, size_t to)
{
	size_t depth;
	struct node *tree;

	tree = build_mmrtree(from);
	depth = mmr_tree_depth(tree, to);
	free_mmrtree(tree);

	return depth;
}

struct style {
	const char *name;
	bool fast; /* Fast to calculate depth. */
	size_t (*proof_len)(size_t, size_t);
};

struct style styles[] = {
	{ "rfc6862", true, rfc6962_proof_len },
	{ "optimal", true, optimal_proof_len },
	{ "maaku", false, maaku_proof_len },
	{ "breadth-batch", true, breadth_batch_proof_len },
	{ "rfc6962-batch", true, rfc6962_batch_proof_len },
	{ "mmr", false, mmr_proof_len }
};

static void print_proof_lengths(size_t num, size_t target, size_t seed)
{
	int *dist, *step;
	size_t i, s, plen;
	struct isaac64_ctx isaac;

	isaac64_init(&isaac, (void *)&seed, sizeof(seed));

	dist = calloc(sizeof(*dist), num);
	step = calloc(sizeof(*step), num);
	for (i = target+1; i < num; i++) {
		/* We can skip more if we're better than required. */
		uint64_t skip = -1ULL / isaac64_next_uint64(&isaac);
		int j, best;

		if (skip > i)
			skip = i;

		best = i-1;
		for (j = i-1; j >= (int)(i-skip); j--)
			if (1 + dist[j] < dist[best])
				best = j;
		dist[i] = dist[best] + 1;
		step[i] = best;
	}

#if 0
	printf("CPV path (len %u):\n", dist[num-1]);
	for (i = num-1; i != target; i = step[i])
		printf("-> %u (-%zu)\n", step[i], i - step[i]);
#endif

	for (s = 0; s < ARRAY_SIZE(styles); s++) {
		if (!styles[s].name)
			continue;
		plen = 0;
		for (i = num-1; i != target; i = step[i])
			plen += styles[s].proof_len(i, step[i]);
		printf("%s: proof hashes %zu\n", styles[s].name, plen);
	}

	free(dist);
	free(step);
}

/* Calculate the optimal proof lengths for all variants at once. */
struct prooflen {
	unsigned int len[ARRAY_SIZE(styles)];
};

/* This sorts by actual (optimal) proof len, not path len  */
static void print_optimal_length(size_t num, size_t target, size_t seed)
{
	struct prooflen *prooflen;
	size_t i, s;
	struct isaac64_ctx isaac;

	isaac64_init(&isaac, (void *)&seed, sizeof(seed));

	prooflen = calloc(sizeof(*prooflen), num);
	for (i = target+1; i < num; i++) {
		/* We can skip more if we're better than required. */
		uint64_t skip = -1ULL / isaac64_next_uint64(&isaac);
		int j;

		if (skip > i)
			skip = i;

		for (s = 0; s < ARRAY_SIZE(styles); s++) {
			if (!styles[s].fast)
				continue;

			prooflen[i].len[s] = -1;
			for (j = i-1; j >= (int)(i-skip); j--) {
				size_t len = styles[s].proof_len(i, j);
				if (len + prooflen[j].len[s]
				    < prooflen[i].len[s])
					prooflen[i].len[s]
						= len + prooflen[j].len[s];
			}
		}
	}

	for (s = 0; s < ARRAY_SIZE(styles); s++) {
		if (!styles[s].fast)
			continue;
		printf("prooflen-%s: proof hashes %u\n", styles[s].name,
		       prooflen[num-1].len[s]);
	}
	free(prooflen);
}

int main(int argc, char *argv[])
{
	unsigned int num, seed = 0, target = 0;
	bool maaku = true;

	opt_register_noarg("--usage|--help|-h", opt_usage_and_exit,
			   "<num>\n"
			   "Calculates proof length for SPV chains of block headers,\n"
			   " using various different prevtree topologies",
			   "Print this message");
	opt_register_arg("--target", opt_set_uintval, opt_show_uintval, &target,
			 "Block number to terminate SPV proof at");
	opt_register_arg("--seed", opt_set_uintval, opt_show_uintval, &seed,
			 "Seed for deterministic RNG");
	opt_register_noarg("--no-maaku", opt_set_invbool,
			   &maaku, "Skip the maaku tree");

	opt_parse(&argc, argv, opt_log_stderr_exit);
	if (argc != 2)
		opt_usage_and_exit(NULL);

	if (!maaku) {
		assert(strcmp(styles[2].name, "maaku") == 0);
		styles[2].name = NULL;
	}

	num = atoi(argv[1]);
	if (target >= num)
		errx(1, "Don't do that, you'll crash me");
	print_proof_lengths(num, target, seed);
	print_optimal_length(num, target, seed);

	return 0;
}
