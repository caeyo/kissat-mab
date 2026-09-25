#ifndef _tree_h_INCLUDED
#define _tree_h_INCLUDED

// Sum tree with maximum (a segment tree) over the variables: the data
// structure of the tree policies 'Argmax' and 'Sample' (see 'policy.h').
//
// It has one leaf per variable index.  A leaf is present or absent.  A
// present leaf holds a key, the variable's score, and in a weighted tree a
// sampling weight.  An absent leaf has key minus infinity and weight zero.
// Every internal node holds the variable of largest key in its subtree,
// ties going to the smaller variable index (the key itself is read from
// the leaf), and in a weighted tree the sum of the weights in its subtree.
//
// Weights and sums carry their own binary exponent ('tree_weight'): a
// weight is given by its base-2 logarithm, and every weight and sum is
// 'mantissa * 2^exponent' with an integer exponent that the double's
// exponent range does not bound.  So any weight that is positive is
// represented, however far it lies from the others, and no reference
// point is needed to keep weights in range: nothing underflows to zero or
// overflows.  A leaf's mantissa is in [1, 2).  A sum takes the larger of
// its two children's exponents and adds the other child scaled to it; a
// child more than 'TREE_NEGLIGIBLE' binary orders below is dropped, which
// rounding would do anyway.  So a sum's mantissa is at least 1 and below
// twice the number of its leaves, and never needs normalising.
//
// Internal nodes are recomputed from their children whenever a leaf
// changes, never updated by differences.  The tree is therefore a function
// of its leaves alone: the order of updates leaves no trace, and rounding
// errors of the sums do not accumulate over time.  A subtree whose leaves
// are all absent holds its leftmost leaf.
//
// The layout is implicit.  'leaves' is a power of two (or zero for the
// empty tree), node 1 is the root, the children of node 'i' are '2i' and
// '2i+1', and the leaf of variable 'idx' is node 'leaves + idx'.  So the
// leaves are in index order: the left subtree of a node holds smaller
// indices than its right subtree, which gives the tie-breaking for free,
// and sampling is inverse transform sampling in index order.
//
// Lookups are O(1) (maximum, total weight), a leaf change is O(log n), a
// draw is O(log n) and a rebuild of all internal nodes is O(n).  The
// maxima of a leaf's ancestors are only visited while they can change: an
// increased key climbs while its variable is or becomes the maximum, and a
// decreased key while its variable was the maximum.  Sums of a weighted
// tree are recomputed up to the root.

#include <assert.h>
#include <limits.h>
#include <math.h>
#include <stdbool.h>
#include <stdint.h>
#include <string.h>

typedef struct tree tree;
typedef struct tree_weight tree_weight;

// The value 'mantissa * 2^exponent'.  Zero has mantissa zero and exponent
// 'TREE_ZERO_EXPONENT', below every exponent of a positive weight.

struct tree_weight {
  double mantissa;
  int exponent;
};

struct tree {
  bool weighted;        // keep weights and sums (set before the first
                        // resize or by 'kissat_weigh_tree')
  unsigned leaves;      // number of leaves, a power of two, or zero
  unsigned *args;       // variable of largest key of internal nodes 1 ...
                        // leaves-1 (node 0 unused)
  double *keys;         // key of each leaf, minus infinity if absent
  tree_weight *sums;    // weighted: sums of internal nodes 1 ... leaves-1
  tree_weight *weights; // weighted: weight of each leaf
};

#define TREE_ABSENT (-INFINITY)

// Exponents of positive weights stay within 'TREE_MAX_EXPONENT' of zero,
// so that differences of exponents, the zero one included, fit an 'int'.

#define TREE_MAX_EXPONENT (1 << 28)
#define TREE_ZERO_EXPONENT (-(1 << 29))

// A child whose exponent is more than this below its sibling's is left
// out of their sum.  Its value is then below 2^(33 - TREE_NEGLIGIBLE)
// times the sum's (at most 2^32 leaves), less than half a unit in the last
// place, so rounding would drop it too.

#define TREE_NEGLIGIBLE 128

struct kissat;

// Makes room for variable indices below 'size'.  Leaves below both the
// old and the new number of leaves keep their contents, new leaves are
// absent, and dropped leaves must be absent.  Rebuilds internal nodes.

void kissat_resize_tree (struct kissat *, tree *, unsigned size);
void kissat_release_tree (struct kissat *, tree *);

// Gives an unweighted tree weights and sums.  Every leaf, present or not,
// gets weight zero; the caller sets the weights of present leaves and
// rebuilds.

void kissat_weigh_tree (struct kissat *, tree *);

// Recomputes every internal node from the leaves, in O(n).

void kissat_rebuild_tree (tree *);

// The first internal node (in index order) that differs bitwise from what
// its children give, or zero if there is none.  'kissat_check_tree'
// asserts that there is none.

unsigned kissat_tree_inconsistent_node (const tree *);

#ifndef NDEBUG
void kissat_check_tree (const tree *);
#endif

static inline bool kissat_same_double (double a, double b) {
  uint64_t x, y;
  memcpy (&x, &a, sizeof x);
  memcpy (&y, &b, sizeof y);
  return x == y;
}

static inline tree_weight kissat_tree_zero_weight (void) {
  tree_weight res = {0, TREE_ZERO_EXPONENT};
  return res;
}

// The weight 2^log2_weight, zero for minus infinity.

static inline tree_weight kissat_tree_weight_of_log2 (double log2_weight) {
  if (log2_weight == -INFINITY)
    return kissat_tree_zero_weight ();
  assert (fabs (log2_weight) < TREE_MAX_EXPONENT);
  const double floor_log2 = floor (log2_weight);
  tree_weight res = {exp2 (log2_weight - floor_log2), (int) floor_log2};
  if (res.mantissa >= 2) // rounding just below the next power of two
    res.mantissa = 1, res.exponent++;
  assert (1 <= res.mantissa), assert (res.mantissa < 2);
  return res;
}

// The base-2 logarithm of a weight, minus infinity for zero.

static inline double kissat_tree_log2_of_weight (tree_weight weight) {
  if (!(weight.mantissa > 0))
    return -INFINITY;
  return log2 (weight.mantissa) + weight.exponent;
}

static inline bool kissat_tree_same_weight (tree_weight a, tree_weight b) {
  return a.exponent == b.exponent &&
         kissat_same_double (a.mantissa, b.mantissa);
}

// 2^d for 'd' between the smallest and the largest normal exponent.

static inline double kissat_tree_pow2 (int d) {
  assert (-1022 <= d), assert (d <= 1023);
  const uint64_t bits = (uint64_t) (d + 1023) << 52;
  double res;
  memcpy (&res, &bits, sizeof res);
  return res;
}

// The value of 'weight' in units of 2^exponent, where 'exponent' is at
// least the weight's; zero if the weight is negligible at that exponent.

static inline double kissat_tree_scaled (tree_weight weight, int exponent) {
  assert (weight.exponent <= exponent);
  const int d = weight.exponent - exponent;
  if (d < -TREE_NEGLIGIBLE)
    return 0;
  return weight.mantissa * kissat_tree_pow2 (d);
}

// 2^d for 'd' from '-TREE_NEGLIGIBLE' to 0, and 0 below, without a
// branch.  A scaling exponent of -1023 has bit pattern zero, i.e. 0.

static inline double kissat_tree_scale_factor (int d) {
  assert (d <= 0);
  d = d < -TREE_NEGLIGIBLE ? -1023 : d;
  const uint64_t bits = (uint64_t) (d + 1023) << 52;
  double res;
  memcpy (&res, &bits, sizeof res);
  return res;
}

// The sum of two weights, as the tree computes it: the larger exponent,
// and the other mantissa scaled to it, or dropped if it is negligible.
// Both mantissas are scaled to the larger exponent, one of them by exactly
// 1, so no double is selected by a comparison (which the compiler turns
// into an unpredictable branch), and the result does not depend on the
// order of the arguments: both products are exact, and their sum is
// rounded once.

static inline tree_weight kissat_tree_add (tree_weight a, tree_weight b) {
  const int exponent = a.exponent < b.exponent ? b.exponent : a.exponent;
  const double fa = kissat_tree_scale_factor (a.exponent - exponent);
  const double fb = kissat_tree_scale_factor (b.exponent - exponent);
  tree_weight res = {a.mantissa * fa + b.mantissa * fb, exponent};
  return res;
}

// Sets a leaf without recomputing its ancestors, for bulk changes that
// end with 'kissat_rebuild_tree'.  A key of 'TREE_ABSENT' makes it absent.
// The weight is given by its base-2 logarithm and ignored in an
// unweighted tree.

static inline void kissat_tree_put (tree *tree, unsigned idx, double key,
                                    double log2_weight) {
  assert (idx < tree->leaves);
  tree->keys[idx] = key;
  if (tree->weighted)
    tree->weights[idx] = key == TREE_ABSENT
                             ? kissat_tree_zero_weight ()
                             : kissat_tree_weight_of_log2 (log2_weight);
}

// Moves the key and weight of leaf 'from' to leaf 'to', without
// recomputing ancestors (for compaction, which rebuilds afterwards).

static inline void kissat_tree_move (tree *tree, unsigned from,
                                     unsigned to) {
  assert (from < tree->leaves), assert (to < tree->leaves);
  tree->keys[to] = tree->keys[from];
  if (tree->weighted)
    tree->weights[to] = tree->weights[from];
}

static inline bool kissat_tree_contains (const tree *tree, unsigned idx) {
  assert (idx < tree->leaves);
  return tree->keys[idx] != TREE_ABSENT;
}

static inline double kissat_tree_key (const tree *tree, unsigned idx) {
  assert (idx < tree->leaves);
  return tree->keys[idx];
}

static inline tree_weight kissat_tree_weight (const tree *tree,
                                              unsigned idx) {
  assert (tree->weighted);
  assert (idx < tree->leaves);
  return tree->weights[idx];
}

// Largest key over the present leaves, minus infinity if there are none.

static inline double kissat_tree_max_key (const tree *tree) {
  return tree->leaves ? tree->keys[tree->args[1]] : TREE_ABSENT;
}

// The present variable of largest key, the smallest index among ties, or
// 'UINT_MAX' if no leaf is present.

static inline unsigned kissat_tree_max (const tree *tree) {
  if (!tree->leaves)
    return UINT_MAX;
  const unsigned res = tree->args[1];
  return tree->keys[res] == TREE_ABSENT ? UINT_MAX : res;
}

// Sum of the weights of all leaves.  It is zero exactly when every leaf
// has weight zero.

static inline tree_weight kissat_tree_total (const tree *tree) {
  assert (tree->weighted);
  return tree->leaves ? tree->sums[1] : kissat_tree_zero_weight ();
}

static inline bool kissat_tree_has_weight (const tree *tree) {
  return kissat_tree_total (tree).mantissa > 0;
}

#endif
