#include "indicator.h"
#include "allocate.h"

#include <limits.h>

void kissat_rebuild_indicator (indicator *indicator) {
  const unsigned leaves = indicator->leaves;
  if (!leaves)
    return;
  unsigned *const counts = indicator->counts;
  for (unsigned i = leaves - 1; i; i--)
    counts[i] = counts[2 * i] + counts[2 * i + 1];
}

static void allocate_leaves (struct kissat *solver, indicator *indicator,
                             unsigned size) {
  unsigned new_leaves = 0;
  if (size) {
    new_leaves = 2;
    while (new_leaves < size) {
      assert (new_leaves <= UINT_MAX / 2);
      new_leaves *= 2;
    }
  }
  const unsigned old_leaves = indicator->leaves;
  if (new_leaves == old_leaves)
    return;
  const unsigned kept = old_leaves < new_leaves ? old_leaves : new_leaves;
#ifndef NDEBUG
  for (unsigned idx = kept; idx < old_leaves; idx++)
    assert (!kissat_indicator_contains (indicator, idx));
#endif
  unsigned *counts = 0;
  if (new_leaves) {
    counts =
        kissat_calloc (solver, 2 * (size_t) new_leaves, sizeof *counts);
    for (unsigned idx = 0; idx < kept; idx++)
      counts[new_leaves + idx] = indicator->counts[old_leaves + idx];
  }
  kissat_dealloc (solver, indicator->counts, 2 * (size_t) old_leaves,
                  sizeof *indicator->counts);
  indicator->leaves = new_leaves;
  indicator->counts = counts;
  kissat_rebuild_indicator (indicator);
}

void kissat_enable_indicator (struct kissat *solver, indicator *indicator,
                              unsigned size) {
  assert (!indicator->enabled);
  assert (!indicator->leaves);
  indicator->enabled = true;
  allocate_leaves (solver, indicator, size);
}

void kissat_resize_indicator (struct kissat *solver, indicator *indicator,
                              unsigned size) {
  if (indicator->enabled)
    allocate_leaves (solver, indicator, size);
}

void kissat_release_indicator (struct kissat *solver,
                               indicator *indicator) {
  const size_t size = 2 * (size_t) indicator->leaves;
  kissat_dealloc (solver, indicator->counts, size,
                  sizeof *indicator->counts);
  indicator->leaves = 0;
  indicator->counts = 0;
}

unsigned kissat_indicator_inconsistent_node (const indicator *indicator) {
  const unsigned leaves = indicator->leaves;
  const unsigned *const counts = indicator->counts;
  for (unsigned i = 1; i < leaves; i++)
    if (counts[i] != counts[2 * i] + counts[2 * i + 1])
      return i;
  for (unsigned idx = 0; idx < leaves; idx++)
    if (counts[leaves + idx] > 1)
      return leaves + idx;
  return 0;
}
