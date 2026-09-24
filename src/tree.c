#include "allocate.h"
#include "inlinetree.h"

void kissat_rebuild_tree (tree *tree) {
  const unsigned leaves = tree->leaves;
  if (!leaves)
    return;
  for (unsigned i = leaves - 1; i; i--) {
    tree->args[i] = kissat_tree_children_max (tree, i);
    if (tree->weighted)
      kissat_tree_update_sum (tree, i);
  }
}

void kissat_resize_tree (struct kissat *solver, tree *tree, unsigned size) {
  unsigned new_leaves = 0;
  if (size) {
    new_leaves = 2;
    while (new_leaves < size) {
      assert (new_leaves <= UINT_MAX / 2);
      new_leaves *= 2;
    }
  }
  const unsigned old_leaves = tree->leaves;
  if (new_leaves == old_leaves)
    return;
  const unsigned kept = old_leaves < new_leaves ? old_leaves : new_leaves;
#ifndef NDEBUG
  for (unsigned idx = kept; idx < old_leaves; idx++)
    assert (tree->keys[idx] == TREE_ABSENT);
#endif
  double *keys = 0, *weights = 0, *sums = 0;
  unsigned *args = 0;
  if (new_leaves) {
    keys = kissat_nalloc (solver, new_leaves, sizeof *keys);
    args = kissat_calloc (solver, new_leaves, sizeof *args);
    for (unsigned idx = 0; idx < kept; idx++)
      keys[idx] = tree->keys[idx];
    for (unsigned idx = kept; idx < new_leaves; idx++)
      keys[idx] = TREE_ABSENT;
    if (tree->weighted) {
      weights = kissat_calloc (solver, new_leaves, sizeof *weights);
      sums = kissat_nalloc (solver, new_leaves, sizeof *sums);
      for (unsigned idx = 0; idx < kept; idx++)
        weights[idx] = tree->weights[idx];
    }
  }
  kissat_release_tree (solver, tree);
  tree->leaves = new_leaves;
  tree->keys = keys;
  tree->args = args;
  tree->weights = weights;
  tree->sums = sums;
  kissat_rebuild_tree (tree);
}

void kissat_release_tree (struct kissat *solver, tree *tree) {
  const unsigned leaves = tree->leaves;
  kissat_dealloc (solver, tree->keys, leaves, sizeof *tree->keys);
  kissat_dealloc (solver, tree->args, leaves, sizeof *tree->args);
  if (tree->weighted) {
    kissat_dealloc (solver, tree->weights, leaves, sizeof *tree->weights);
    kissat_dealloc (solver, tree->sums, leaves, sizeof *tree->sums);
  }
  const bool weighted = tree->weighted;
  memset (tree, 0, sizeof *tree);
  tree->weighted = weighted;
}

unsigned kissat_tree_inconsistent_node (const tree *tree) {
  const unsigned leaves = tree->leaves;
  for (unsigned i = 1; i < leaves; i++) {
    if (tree->args[i] != kissat_tree_children_max (tree, i))
      return i;
    if (!tree->weighted)
      continue;
    const unsigned left = 2 * i;
    const double *const s =
        left < leaves ? tree->sums + left : tree->weights + (left - leaves);
    if (!kissat_same_double (tree->sums[i], s[0] + s[1]))
      return i;
  }
  return 0;
}

#ifndef NDEBUG

void kissat_check_tree (const tree *tree) {
  assert (!kissat_tree_inconsistent_node (tree));
  (void) tree;
}

#endif
