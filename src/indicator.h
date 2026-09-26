#ifndef _indicator_h_INCLUDED
#define _indicator_h_INCLUDED

// Indicator tree: a sum tree of counts over the variables, which the
// decision policy draws the uniform term of its mixing from (see
// 'policy.h').  It has one leaf per variable index, present or absent, and
// every internal node holds the number of present leaves in its subtree.
// A draw takes an integer uniformly below the total and descends to the
// leaf of that rank among the present leaves, so every present leaf is
// equally likely.  The counts are integers, so every sum is exact and the
// tree is a function of its leaves, whatever the order of updates.
//
// The layout is that of the policy's tree ('tree.h'): 'leaves' is a power
// of two (or zero for the empty tree), node 1 is the root, the children of
// node 'i' are '2i' and '2i+1', and the leaf of variable 'idx' is node
// 'leaves + idx'.  All nodes are in one array 'counts' of '2 * leaves'
// entries (entry 0 unused), where a leaf holds 1 if present and 0 if
// absent.  The total is O(1), a leaf change O(log n), a draw O(log n) and
// a rebuild of all internal nodes O(n).
//
// Only the policy's mixing needs the tree, so it is kept only once
// enabled: until then it has no leaves and resizing does nothing.

#include "random.h"

#include <assert.h>
#include <stdbool.h>
#include <stddef.h>

typedef struct indicator indicator;

struct indicator {
  bool enabled;     // kept (set by 'kissat_enable_indicator')
  unsigned leaves;  // number of leaves, a power of two, or zero
  unsigned *counts; // internal nodes 1 ... leaves-1, then the leaves
};

struct kissat;

// Enables the tree with room for variable indices below 'size', every
// leaf absent.

void kissat_enable_indicator (struct kissat *, indicator *, unsigned size);

// Makes room for variable indices below 'size', with as many leaves as the
// policy's tree has for that size.  Leaves below both the old and the new
// number of leaves keep their contents, new leaves are absent, and dropped
// leaves must be absent.  Rebuilds internal nodes.  Does nothing unless
// the tree is enabled.

void kissat_resize_indicator (struct kissat *, indicator *, unsigned size);
void kissat_release_indicator (struct kissat *, indicator *);

// Recomputes every internal node from the leaves, in O(n).

void kissat_rebuild_indicator (indicator *);

// The first internal node (in index order) whose count is not the sum of
// its children's, or zero if there is none.

unsigned kissat_indicator_inconsistent_node (const indicator *);

static inline bool kissat_indicator_contains (const indicator *indicator,
                                              unsigned idx) {
  assert (idx < indicator->leaves);
  return indicator->counts[indicator->leaves + idx];
}

// The number of present leaves.

static inline unsigned kissat_indicator_total (const indicator *indicator) {
  return indicator->leaves ? indicator->counts[1] : 0;
}

// Makes the leaf of 'idx' present or absent, and updates its ancestors.

static inline void kissat_indicator_set (indicator *indicator, unsigned idx,
                                         bool present) {
  const unsigned leaves = indicator->leaves;
  assert (idx < leaves);
  unsigned *const counts = indicator->counts;
  unsigned i = leaves + idx;
  const unsigned old = counts[i];
  if (old == present)
    return;
  counts[i] = present;
  if (present)
    while (i /= 2)
      counts[i]++;
  else
    while (i /= 2)
      counts[i]--;
}

static inline void kissat_indicator_insert (indicator *indicator,
                                            unsigned idx) {
  assert (!kissat_indicator_contains (indicator, idx));
  kissat_indicator_set (indicator, idx, true);
}

static inline void kissat_indicator_remove (indicator *indicator,
                                            unsigned idx) {
  assert (kissat_indicator_contains (indicator, idx));
  kissat_indicator_set (indicator, idx, false);
}

// Sets a leaf without updating its ancestors, for bulk changes that end
// with 'kissat_rebuild_indicator'.

static inline void kissat_indicator_put (indicator *indicator, unsigned idx,
                                         bool present) {
  assert (idx < indicator->leaves);
  indicator->counts[indicator->leaves + idx] = present;
}

// Moves leaf 'from' to leaf 'to' without updating ancestors (for
// compaction, which rebuilds afterwards).

static inline void kissat_indicator_move (indicator *indicator,
                                          unsigned from, unsigned to) {
  const unsigned leaves = indicator->leaves;
  assert (from < leaves), assert (to < leaves);
  indicator->counts[leaves + to] = indicator->counts[leaves + from];
}

// The present leaf of rank 'rank' in index order ('rank' below the
// total).

static inline unsigned kissat_indicator_select (const indicator *indicator,
                                                unsigned rank) {
  const unsigned leaves = indicator->leaves;
  const unsigned *const counts = indicator->counts;
  assert (leaves >= 2);
  assert (rank < counts[1]);
  unsigned i = 1;
  while (i < leaves) {
    i *= 2;
    const unsigned left = counts[i];
    if (rank >= left)
      rank -= left, i++;
  }
  assert (counts[i] == 1), assert (!rank);
  return i - leaves;
}

// A present leaf drawn uniformly, with one draw from 'random': the rank is
// the draw's 53 high bits scaled to the total, rounded down, which is
// below the total.  There must be a present leaf.

static inline unsigned kissat_indicator_draw (const indicator *indicator,
                                              generator *random) {
  const unsigned total = kissat_indicator_total (indicator);
  assert (total);
  const unsigned rank = kissat_pick_double53 (random) * total;
  assert (rank < total);
  return kissat_indicator_select (indicator, rank);
}

#endif
