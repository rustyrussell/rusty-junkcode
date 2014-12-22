/* maaku came up with this internal-node tree structure for better SPV proofs.
 *
 * maaku's tree contains the last log(N) nodes pretty close to the
 * top, but can be incrementally updated.
 *
 * We consider a subtree fixed when it is completely populated to
 * the maximum depth: no nodes move after that point.  If the whole
 * tree is fixed, we create a new head node.
 *
 * The head node is always N; we swap non-fixed nodes as we go down,
 * preferring the left to the right.
 */

#include <stdio.h>
#include <assert.h>
#include <err.h>

#include "maakutree.h"

/* If this forms a complete tree down to max_depth, it's fixed. */
static bool is_fixed(const struct maaku_tree *tree, struct maaku_node *node)
{
	if (node->fixed)
		return true;

	if (node->depth == tree->max_depth)
		return node->fixed = true;

	if (!node->child[0] || !node->child[1])
		return false;

	node->fixed = is_fixed(tree, node->child[0]) && is_fixed(tree, node->child[1]);
	return node->fixed;
}

/* Swaps the values, leaving @old in the tree. */
static size_t swapcount;
static struct maaku_node *swap(struct maaku_node *old, struct maaku_node *new)
{
	size_t val = old->value;
	old->value = new->value;
	new->value = val;
	swapcount++;
	return new;
}

static void add_at(struct maaku_tree *tree, struct maaku_node *node, struct maaku_node *new)
{
	new = swap(node, new);

	if (!node->child[0]) {
		node->child[0] = new;
		new->depth = node->depth + 1;
		return;
	}
	if (!is_fixed(tree, node->child[0])) {
		add_at(tree, node->child[0], new);
		return;
	}
	if (!node->child[1]) {
		node->child[1] = new;
		new->depth = node->depth + 1;
		return;
	}

	assert(!is_fixed(tree, node->child[1]));
	add_at(tree, node->child[1], new);
}

/* This is dumb, but simple. */
static void inc_depths(struct maaku_node *n)
{
	n->depth++;
	if (n->child[0])
		inc_depths(n->child[0]);
	if (n->child[1])
		inc_depths(n->child[1]);
}

void add_maaku_node(struct maaku_tree *tree, size_t value)
{
	struct maaku_node *new = malloc(sizeof(*new));
	new->value = value;
	new->fixed = false;
	new->child[0] = new->child[1] = NULL;

	if (!tree->root) {
		tree->root = new;
		new->depth = 0;
		tree->max_depth = 0;
		return;
	}

	/* Start a new tree? */
	if (is_fixed(tree, tree->root)) {
		new->child[0] = tree->root;
		tree->root = new;
		new->depth = 0;
		tree->max_depth++;
		inc_depths(new->child[0]);
		return;
	}

	/* Left side should be set. */
	assert(is_fixed(tree, tree->root->child[0]));
	add_at(tree, tree->root, new);
}	

static void check_node(const struct maaku_tree *t,
		       const struct maaku_node *node,
		       size_t depth)
{
	if (!node)
		return;

	assert(node->depth == depth);
	assert(node->depth <= t->max_depth);
	check_node(t, node->child[0], depth+1);
	check_node(t, node->child[1], depth+1);
}	

void check_maaku_tree(const struct maaku_tree *t, size_t max_value)
{
	if (t->root)
		assert(t->root->value == max_value);
	check_node(t, t->root, 0);
}

/* Brute force find; we can do better but this works for testing */
const struct maaku_node *find_maaku_node(const struct maaku_node *n, size_t value)
{
	const struct maaku_node *ret;

	if (!n)
		return NULL;
	if (n->value == value)
		return n;

	ret = find_maaku_node(n->child[0], value);
	if (!ret)
		ret = find_maaku_node(n->child[1], value);
	return ret;
}

static void free_maaku_node(struct maaku_node *n)
{
	if (!n)
		return;
	free_maaku_node(n->child[0]);
	free_maaku_node(n->child[1]);
	free(n);
}

void free_maaku_tree(struct maaku_tree *t)
{
	free_maaku_node(t->root);
	t->root = NULL;
}

#ifdef TEST
int main(int argc, char *argv[])
{
	struct maaku_tree t;

	t.max_depth = 0;
	t.root = NULL;

	if (argc != 2)
		errx(1, "Usage: %s <num>", argv[0]);

	num = atoi(argv[1]);
	check_tree(&t, -1);
	for (i = 0; i < num; i++) {
		add_maaku_node(&t, i);
#ifdef DEBUG
		check_tree(&t, i);
#endif
		printf("Adding node %zu: max_depth %zu, swaps %zu\n",
		       i, t.max_depth, swapcount);
		swapcount = 0;
	}

	check_tree(&t, i);
	for (i = 0; i < num; i++) {
		printf("Depth of %zu = %zu\n", num - i - 1,
		       find_node(t.root, num - i - 1)->depth);
	}
	return 0;
}
#endif
