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

/* Array approach is just to built the tree from an array, in order,
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
/* We abuse maaku_node here, for using find_maaku_node */
static struct maaku_node *new_array_node(size_t val, size_t depth)
{
	struct maaku_node *n = malloc(sizeof(*n));
	n->value = val;
	n->depth = depth;
	n->child[0] = n->child[1] = NULL;
	return n;
}

static void build_array_tree(struct maaku_node *n, size_t start, size_t end)
{
	size_t len;

	if (end - start == 1) {
		n->child[0] = new_array_node(start, n->depth+1);
		return;
	}
	if (end - start == 2) {
		n->child[0] = new_array_node(start, n->depth+1);
		n->child[1] = new_array_node(start+1, n->depth+1);
		return;
	}
	n->child[0] = new_array_node(-1, n->depth+1);
	len = (1 << (ilog32(end - start - 1) - 1));
	build_array_tree(n->child[0], start, start + len);
	n->child[1] = new_array_node(-1, n->depth+1);
	build_array_tree(n->child[1], start + len, end);
}

static size_t array_proof_len(size_t from, size_t to)
{
	const struct maaku_node *n;
	size_t depth;
	struct maaku_tree t;

	t.root = new_array_node(-1, 0);
	build_array_tree(t.root, 0, from);
	n = find_maaku_node(t.root, to);

	depth = n->depth;
	free_maaku_tree(&t);

	/* With an external value, proof length == depth */
	return depth;
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

struct style {
	const char *name;
	size_t (*proof_len)(size_t, size_t);
};

struct style styles[] = {
	{ "array", array_proof_len },
	{ "optimal", optimal_proof_len },
	{ "maaku", maaku_proof_len }
};

static void print_proof_lengths(size_t num, size_t target,
				struct isaac64_ctx *isaac)
{
	int *dist, *step;
	size_t i, s, plen;

	dist = calloc(sizeof(*dist), num);
	step = calloc(sizeof(*step), num);
	for (i = target+1; i < num; i++) {
		/* We can skip more if we're better than required. */
		uint64_t skip = -1ULL / isaac64_next_uint64(isaac);
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

int main(int argc, char *argv[])
{
	unsigned int num, seed = 0, target = 0;
	bool maaku = true;
	struct isaac64_ctx isaac;

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
	isaac64_init(&isaac, (void *)&seed, sizeof(seed));
	print_proof_lengths(num, target, &isaac);

	return 0;
}
