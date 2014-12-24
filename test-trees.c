#include "maakutree.h"
#include <ccan/array_size/array_size.h>
#include <ccan/isaac/isaac64.h>
#include <ccan/ilog/ilog.h>
#include <ccan/err/err.h>
#include <ccan/opt/opt.h>
#include <stdio.h>
#include <assert.h>
#include <string.h>

/* We keep a cache of luckiest. */
#define CACHE_SIZE 64
struct cache {
	int blocknum;
	int skip;
};

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
static size_t optimal_proof_len(size_t from, size_t to, const struct cache *c)
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

static size_t rfc6962_proof_len(size_t from, size_t to, const struct cache *c)
{
	return do_proof_len(to, 0, from);
}

static size_t maaku_proof_len(size_t from, size_t to, const struct cache *c)
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
			return optimal_proof_len(from, to, NULL);
		return 1 + optimal_proof_len(from, to, NULL);
	}

	if (array)
		/* Use rfc6862 for old entries. */
		return 1 + rfc6962_proof_len(from_tree * SUBTREE_SIZE, to, NULL);

	/* It's in an older tree.  One to get to the old trees, and
	 * one extra branch for every tree we go back. */
	tree_depth = 1 + from_tree - to_tree;

	/* First tree is just on the left branch, so subtract one. */
	if (to_tree == 0)
		tree_depth--;

	/* One hash to get to get down the tree, plus proof inside the
	 * tree. */
	return tree_depth + optimal_proof_len(SUBTREE_SIZE, to%SUBTREE_SIZE, NULL);
}

static size_t breadth_batch_proof_len(size_t from, size_t to, const struct cache *c)
{
	return batch_proof_len(from, to, false);
}

static size_t rfc6962_batch_proof_len(size_t from, size_t to, const struct cache *c)
{
	return batch_proof_len(from, to, true);
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
 *
 * The linear variant connects the peaks like so:
 *              ...
 *             /
 *            /\(4)
 *           /
 *          /\(3)
 *         /
 *        /\
 *       /  \
 *     (1)  (2)
 */
static size_t mmr_variant_proof_len(size_t from, size_t to, bool linear)
{
	size_t mtns = __builtin_popcount(from), off = 0, peaknum = 0;
	int i;

	/* Which mountain is 'to' in? */
	for (i = sizeof(size_t) * CHAR_BIT - 1; i >= 0; i--) {
		size_t summit = (size_t)1 << i;
		if (from & summit) {
			off += summit;
			if (to < off)
				break;
			peaknum++;
		}
	}

	/* we need to get to mountain i, then down to element. */
	if (linear) {
		if (peaknum == 0)
			return mtns - peaknum - 1 + i;
		else
			return mtns - peaknum + i;
	} else
		return rfc6962_proof_len(mtns, peaknum, NULL) + i;
}

static size_t mmr_proof_len(size_t from, size_t to, const struct cache *c)
{
	return mmr_variant_proof_len(from, to, false);
}

static size_t mmr_linear_proof_len(size_t from, size_t to, const struct cache *c)
{
	return mmr_variant_proof_len(from, to, true);
}

static void init_cache(struct cache *cache)
{
	int i;

	for (i = 0; i < CACHE_SIZE; i++)
		cache[i].skip = cache[i].blocknum = 0;
}

static void add_to_cache(struct cache *cache,
			 int skip, int blocknum)
{
	int i;

	if (skip <= cache[CACHE_SIZE-1].skip)
		return;

	for (i = 0; cache[i].skip >= skip; i++)
		assert(i < CACHE_SIZE);

	memmove(cache + i + 1, cache + i, sizeof(*cache) * (CACHE_SIZE - i - 1));
	cache[i].skip = skip;
	cache[i].blocknum = blocknum;
}

/* FIXME: Store the huff depth in cache, and recalc only when cache changes */
struct huff_info {
	size_t total_skips;
	size_t depth_of_node;
};

static void insert_huff(struct huff_info *info, size_t cachesize,
			const struct huff_info *comb)
{
	size_t i;

	for (i = 0; info[i].total_skips > comb->total_skips; i++);
	memmove(info + i + 1, info + i, sizeof(*info) * (cachesize - i - 1));
	info[i] = *comb;
}

static size_t get_huffman_depth(const struct cache *c, size_t cachesize,
				size_t blocknum)
{
	struct huff_info info[cachesize];
	int i;

	for (i = 0; i < cachesize; i++) {
		info[i].total_skips = c[i].skip;
		if (c[i].blocknum == blocknum)
			info[i].depth_of_node = 0;
		else
			info[i].depth_of_node = -1;
	}

	/* We always keep cache in largest->smallest order, so
	 * just grab last two and combine them. */
	while (cachesize > 1) {
		struct huff_info comb;
		comb.total_skips = info[cachesize-1].total_skips
			+ info[cachesize-2].total_skips;
		if (info[cachesize-1].depth_of_node == -1) {
			if (info[cachesize-2].depth_of_node == -1) {
				comb.depth_of_node = -1;
			} else
				comb.depth_of_node = 1 + info[cachesize-2].depth_of_node;
		} else
			comb.depth_of_node = 1 + info[cachesize-1].depth_of_node;

		insert_huff(info, cachesize, &comb);
		cachesize--;
	}

	return info[0].depth_of_node;
}

/*
 * This simulates a "cache" of the luckiest blocks, ie:
 *
 *           /\
 *          /  \
 *   [ cache]  [ mmr tree ]
 *
 * The cache duplicates blocks in the normal mmr tree.
 */
static size_t mmr_cache_proof_len(size_t from, size_t to, const struct cache *c,
				  size_t cachesize, bool huffman)
{
	int i;

	assert(cachesize <= CACHE_SIZE);

	/* Don't use cache for v. early blocks. */
	if (from < cachesize * 2)
		return mmr_proof_len(from, to, c);

	/* If it's in the cache, use that. */
	for (i = 0; i < cachesize; i++) {
		if (c[i].blocknum == to) {
			/* Simple cache structure is a tree. */
			if (!huffman)
				return 1 + ilog32(cachesize);
			/* huffman encoding FTW. */
			return 1 + get_huffman_depth(c, cachesize, to);
		}
	}

	return 1 + mmr_proof_len(from, to, c);
}

static size_t mmr_cache64_proof_len(size_t from, size_t to,
				    const struct cache *c)
{
	return mmr_cache_proof_len(from, to, c, 64, false);
}

static size_t mmr_cache32_proof_len(size_t from, size_t to,
				    const struct cache *c)
{
	return mmr_cache_proof_len(from, to, c, 32, false);
}

static size_t mmr_cache16_proof_len(size_t from, size_t to,
				    const struct cache *c)
{
	return mmr_cache_proof_len(from, to, c, 16, false);
}

static size_t mmr_cachehuff32_proof_len(size_t from, size_t to,
				      const struct cache *c)
{
	return mmr_cache_proof_len(from, to, c, 32, true);
}

static size_t mmr_cachehuff64_proof_len(size_t from, size_t to,
				      const struct cache *c)
{
	return mmr_cache_proof_len(from, to, c, 64, true);
}

struct style {
	const char *name;
	bool fast; /* Fast to calculate depth. */
	size_t (*proof_len)(size_t, size_t, const struct cache *);
};

struct style styles[] = {
	{ "rfc6862", true, rfc6962_proof_len },
	{ "optimal", true, optimal_proof_len },
	{ "maaku", false, maaku_proof_len },
	{ "breadth-batch", true, breadth_batch_proof_len },
	{ "rfc6962-batch", true, rfc6962_batch_proof_len },
	{ "mmr", true, mmr_proof_len },
	{ "mmr-linear", true, mmr_linear_proof_len },
	{ "mmr-cache-sixtyfour", true, mmr_cache64_proof_len },
	{ "mmr-cache-thirtytwo", true, mmr_cache32_proof_len },
	{ "mmr-cache-sixteen", true, mmr_cache16_proof_len },
	{ "mmr-cachehuff-sixtyfour", true, mmr_cachehuff64_proof_len },
	{ "mmr-cachehuff-thirtytwo", true, mmr_cachehuff32_proof_len }
};

static void print_proof_lengths(size_t num, size_t target, size_t seed)
{
	int *dist, *step;
	struct cache cache[CACHE_SIZE];
	size_t i, s, plen;
	struct isaac64_ctx isaac;

	isaac64_init(&isaac, (void *)&seed, sizeof(seed));

	dist = calloc(sizeof(*dist), num);
	step = calloc(sizeof(*step), num);
	init_cache(cache);
	for (i = target+1; i < num; i++) {
		/* We can skip more if we're better than required. */
		uint64_t skip = -1ULL / isaac64_next_uint64(&isaac);
		int j, best;

		if (skip > i)
			skip = i;
		add_to_cache(cache, skip, i);

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
			plen += styles[s].proof_len(i, step[i], cache);
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
	struct cache cache[CACHE_SIZE];
	size_t i, s;
	struct isaac64_ctx isaac;

	isaac64_init(&isaac, (void *)&seed, sizeof(seed));

	prooflen = calloc(sizeof(*prooflen), num);
	init_cache(cache);

	for (i = target+1; i < num; i++) {
		/* We can skip more if we're better than required. */
		uint64_t skip = -1ULL / isaac64_next_uint64(&isaac);
		int j;

		if (skip > i)
			skip = i;
		add_to_cache(cache, skip, i);

		for (s = 0; s < ARRAY_SIZE(styles); s++) {
			if (!styles[s].fast)
				continue;

			prooflen[i].len[s] = -1;
			for (j = i-1; j >= (int)(i-skip); j--) {
				size_t len = styles[s].proof_len(i, j, cache);
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
