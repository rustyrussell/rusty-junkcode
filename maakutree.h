#include <stdlib.h>
#include <stdbool.h>

struct maaku_tree {
	size_t max_depth;
	struct maaku_node *root;
};

struct maaku_node {
	/* OK, this is just a block number, but you get the idea. */
	size_t value;
	size_t depth;
	bool fixed;
	struct maaku_node *child[2];
};

void add_maaku_node(struct maaku_tree *tree, size_t value);
void check_maaku_tree(const struct maaku_tree *t, size_t max_value);
const struct maaku_node *find_maaku_node(const struct maaku_node *n, size_t value);
void free_maaku_tree(struct maaku_tree *t);
