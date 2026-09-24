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

struct tree {
  bool weighted;   // keep weights and sums (fixed before first resize)
  unsigned leaves; // number of leaves, a power of two, or zero
  unsigned *args;  // variable of largest key of internal nodes 1 ...
                   // leaves-1 (node 0 unused)
  double *keys;    // key of each leaf, minus infinity if absent
  double *sums;    // weighted: sums of internal nodes 1 ... leaves-1
  double *weights; // weighted: weight of each leaf
};

#define TREE_ABSENT (-INFINITY)

struct kissat;

// Makes room for variable indices below 'size'.  Leaves below both the
// old and the new number of leaves keep their contents, new leaves are
// absent, and dropped leaves must be absent.  Rebuilds internal nodes.

void kissat_resize_tree (struct kissat *, tree *, unsigned size);
void kissat_release_tree (struct kissat *, tree *);

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

// Sets a leaf without recomputing its ancestors, for bulk changes that
// end with 'kissat_rebuild_tree'.  A key of 'TREE_ABSENT' makes it absent.

static inline void kissat_tree_put (tree *tree, unsigned idx, double key,
                                    double weight) {
  assert (idx < tree->leaves);
  tree->keys[idx] = key;
  if (tree->weighted)
    tree->weights[idx] = key == TREE_ABSENT ? 0 : weight;
}

static inline bool kissat_tree_contains (const tree *tree, unsigned idx) {
  assert (idx < tree->leaves);
  return tree->keys[idx] != TREE_ABSENT;
}

static inline double kissat_tree_key (const tree *tree, unsigned idx) {
  assert (idx < tree->leaves);
  return tree->keys[idx];
}

static inline double kissat_tree_weight (const tree *tree, unsigned idx) {
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

// Sum of the weights of all leaves.

static inline double kissat_tree_total (const tree *tree) {
  assert (tree->weighted);
  return tree->leaves ? tree->sums[1] : 0;
}

#endif
