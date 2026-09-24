#ifndef _inlinetree_h_INCLUDED
#define _inlinetree_h_INCLUDED

// Hot-path operations of the sum tree with maximum (see 'tree.h').

#include "random.h"
#include "tree.h"

// The variable of largest key among the maxima of the two children of
// internal node 'i', the left one on ties (it has the smaller index).

static inline unsigned kissat_tree_children_max (const tree *tree,
                                                 unsigned i) {
  const unsigned leaves = tree->leaves;
  assert (0 < i), assert (i < leaves);
  const unsigned left = 2 * i;
  unsigned a, b;
  if (left < leaves)
    a = tree->args[left], b = tree->args[left + 1];
  else
    a = left - leaves, b = a + 1;
  assert (a < b);
  const double *const keys = tree->keys;
  return keys[b] > keys[a] ? b : a;
}

static inline void kissat_tree_update_sum (tree *tree, unsigned i) {
  const unsigned leaves = tree->leaves;
  assert (tree->weighted);
  assert (0 < i), assert (i < leaves);
  const unsigned left = 2 * i;
  const double *const s =
      left < leaves ? tree->sums + left : tree->weights + (left - leaves);
  tree->sums[i] = s[0] + s[1];
}

// Sets the leaf of 'idx' to a present leaf with this key and weight (the
// weight is ignored in an unweighted tree), and recomputes its ancestors.
// With a larger key 'idx' climbs while it is or becomes the maximum of an
// ancestor, and stops at the first ancestor whose maximum stays another
// variable, which then holds for every ancestor above.  With a smaller key
// the ancestors whose maximum was 'idx' are recomputed, and the first one
// whose maximum was another variable keeps it, as do those above.

static inline void kissat_tree_set (tree *tree, unsigned idx, double key,
                                    double weight) {
  const unsigned leaves = tree->leaves;
  assert (idx < leaves);
  double *const keys = tree->keys;
  const double old_key = keys[idx];
  keys[idx] = key;
  unsigned *const args = tree->args;
  const unsigned first = (leaves + idx) / 2;
  if (key > old_key) {
    for (unsigned i = first; i; i /= 2)
      if (args[i] != idx) {
        if (kissat_tree_children_max (tree, i) != idx)
          break;
        args[i] = idx;
      }
  } else if (key < old_key) {
    for (unsigned i = first; i && args[i] == idx; i /= 2)
      args[i] = kissat_tree_children_max (tree, i);
  }
  if (tree->weighted) {
    tree->weights[idx] = weight;
    for (unsigned i = first; i; i /= 2)
      kissat_tree_update_sum (tree, i);
  } else
    (void) weight;
}

// Makes the leaf of 'idx' absent.

static inline void kissat_tree_remove (tree *tree, unsigned idx) {
  assert (kissat_tree_contains (tree, idx));
  kissat_tree_set (tree, idx, TREE_ABSENT, 0);
}

// The leaf reached by descending from the root with 'u' in [0, total),
// i.e. the variable 'idx' with 'W(idx) <= u < W(idx) + weight (idx)',
// where 'W(idx)' is the total weight of the leaves before it.  Rounding in
// the sums can make 'u' overshoot a subtree; the descent never enters a
// subtree of weight zero, so the result always has a positive weight.

static inline unsigned kissat_tree_sample (const tree *tree, double u) {
  assert (tree->weighted);
  const unsigned leaves = tree->leaves;
  assert (leaves >= 2);
  const double *const sums = tree->sums;
  assert (sums[1] > 0);
  assert (0 <= u);
  const unsigned half = leaves / 2;
  unsigned i = 1;
  while (i < half) {
    const unsigned left = 2 * i;
    const double s = sums[left];
    if (u < s)
      i = left;
    else if (sums[left + 1] > 0)
      u -= s, i = left + 1;
    else
      i = left;
  }
  const unsigned idx = 2 * i - leaves;
  const double *const w = tree->weights + idx;
  if (u < w[0])
    return idx;
  if (w[1] > 0)
    return idx + 1;
  assert (w[0] > 0);
  return idx;
}

// A leaf drawn with probability proportional to its weight, with one
// draw from 'random'.  The total weight must be positive.

static inline unsigned kissat_tree_draw (const tree *tree,
                                         generator *random) {
  const double u = kissat_pick_double53 (random) * kissat_tree_total (tree);
  return kissat_tree_sample (tree, u);
}

#endif
