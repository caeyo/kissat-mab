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

// The children of internal node 'i' as weights (sums or leaf weights).

static inline const tree_weight *
kissat_tree_children_weights (const tree *tree, unsigned i) {
  const unsigned leaves = tree->leaves;
  assert (tree->weighted);
  assert (0 < i), assert (i < leaves);
  const unsigned left = 2 * i;
  return left < leaves ? tree->sums + left : tree->weights + (left - leaves);
}

static inline void kissat_tree_update_sum (tree *tree, unsigned i) {
  const tree_weight *const s = kissat_tree_children_weights (tree, i);
  tree->sums[i] = kissat_tree_add (s[0], s[1]);
}

// Sets the leaf of 'idx' to a present leaf with this key and the weight
// 2^log2_weight (ignored in an unweighted tree), and recomputes its
// ancestors.
// With a larger key 'idx' climbs while it is or becomes the maximum of an
// ancestor, and stops at the first ancestor whose maximum stays another
// variable, which then holds for every ancestor above.  With a smaller key
// the ancestors whose maximum was 'idx' are recomputed, and the first one
// whose maximum was another variable keeps it, as do those above.

static inline void kissat_tree_set (tree *tree, unsigned idx, double key,
                                    double log2_weight) {
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
    // The sums from the leaf up to the root, the running sum kept in a
    // register rather than read back from the node just written.
    const tree_weight weight = key == TREE_ABSENT
                                   ? kissat_tree_zero_weight ()
                                   : kissat_tree_weight_of_log2 (log2_weight);
    tree_weight *const weights = tree->weights;
    tree_weight *const sums = tree->sums;
    weights[idx] = weight;
    tree_weight sum = kissat_tree_add (weight, weights[idx ^ 1]);
    sums[first] = sum;
    for (unsigned i = first; i > 1; i /= 2) {
      sum = kissat_tree_add (sum, sums[i ^ 1]);
      sums[i / 2] = sum;
    }
  } else
    (void) log2_weight;
}

// Makes the leaf of 'idx' absent.

static inline void kissat_tree_remove (tree *tree, unsigned idx) {
  assert (kissat_tree_contains (tree, idx));
  kissat_tree_set (tree, idx, TREE_ABSENT, -INFINITY);
}

// The leaf reached by descending from the root with 'u' in [0, m), where
// the total weight is 'm * 2^e' and 'u' is in units of 2^e: the variable
// 'idx' with 'W(idx) <= u < W(idx) + weight (idx)', where 'W(idx)' is the
// total weight of the leaves before it.  At every node 'u' is rescaled to
// the units of the child it enters, which is exact (a power of two).
// Rounding in the sums can make 'u' overshoot a subtree; the descent never
// enters a subtree of weight zero, or one left out of its parent's sum as
// negligible, so the result always has a positive weight.

static inline unsigned kissat_tree_sample (const tree *tree, double u) {
  assert (tree->weighted);
  const unsigned leaves = tree->leaves;
  assert (leaves >= 2);
  assert (tree->sums[1].mantissa > 0);
  assert (0 <= u);
  int exponent = tree->sums[1].exponent;
  unsigned i = 1;
  while (i < leaves) {
    const tree_weight *const s = kissat_tree_children_weights (tree, i);
    const double left = kissat_tree_scaled (s[0], exponent);
    const double right = kissat_tree_scaled (s[1], exponent);
    unsigned child;
    if (u < left)
      child = 0;
    else if (right > 0)
      u -= left, child = 1;
    else
      child = 0;
    assert (s[child].mantissa > 0);
    const int d = exponent - s[child].exponent;
    assert (0 <= d), assert (d <= TREE_NEGLIGIBLE);
    u *= kissat_tree_pow2 (d);
    exponent = s[child].exponent;
    i = 2 * i + child;
  }
  return i - leaves;
}

// A leaf drawn with probability proportional to its weight, with one
// draw from 'random'.  The total weight must be positive.

static inline unsigned kissat_tree_draw (const tree *tree,
                                         generator *random) {
  const double u =
      kissat_pick_double53 (random) * kissat_tree_total (tree).mantissa;
  return kissat_tree_sample (tree, u);
}

#endif
