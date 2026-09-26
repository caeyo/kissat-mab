#include "../src/indicator.h"

#include "test.h"

#include <stdlib.h>

// Brute force: the present leaf of rank 'rank' in index order, or
// 'UINT_MAX'.

static unsigned brute_force_select (const indicator *indicator,
                                    unsigned vars, unsigned rank) {
  for (unsigned idx = 0; idx < vars; idx++)
    if (kissat_indicator_contains (indicator, idx) && !rank--)
      return idx;
  return UINT_MAX;
}

static void test_indicator_basic (void) {
  indicator dummy, *indicator = &dummy;
  memset (indicator, 0, sizeof *indicator);
  kissat_resize_indicator (0, indicator, 5);
  assert (!indicator->leaves), assert (!indicator->counts);
  assert (!kissat_indicator_total (indicator));
  kissat_enable_indicator (0, indicator, 5);
  assert (indicator->enabled);
  assert (indicator->leaves == 8);
  assert (!kissat_indicator_total (indicator));
  for (unsigned idx = 0; idx < 8; idx++)
    assert (!kissat_indicator_contains (indicator, idx));
  kissat_indicator_insert (indicator, 3);
  kissat_indicator_insert (indicator, 0);
  kissat_indicator_insert (indicator, 4);
  assert (kissat_indicator_total (indicator) == 3);
  assert (kissat_indicator_select (indicator, 0) == 0);
  assert (kissat_indicator_select (indicator, 1) == 3);
  assert (kissat_indicator_select (indicator, 2) == 4);
  kissat_indicator_set (indicator, 3, true);
  assert (kissat_indicator_total (indicator) == 3);
  kissat_indicator_remove (indicator, 0);
  kissat_indicator_set (indicator, 0, false);
  assert (kissat_indicator_total (indicator) == 2);
  assert (kissat_indicator_select (indicator, 0) == 3);
  assert (!kissat_indicator_inconsistent_node (indicator));
  kissat_resize_indicator (0, indicator, 100);
  assert (indicator->leaves == 128);
  assert (kissat_indicator_total (indicator) == 2);
  assert (kissat_indicator_contains (indicator, 3));
  assert (kissat_indicator_contains (indicator, 4));
  kissat_indicator_insert (indicator, 99);
  assert (kissat_indicator_select (indicator, 2) == 99);
  kissat_indicator_remove (indicator, 99);
  kissat_resize_indicator (0, indicator, 5);
  assert (indicator->leaves == 8);
  assert (kissat_indicator_total (indicator) == 2);
  assert (!kissat_indicator_inconsistent_node (indicator));
  kissat_release_indicator (0, indicator);
  assert (!indicator->leaves), assert (!indicator->counts);
  assert (indicator->enabled);
}

// Random changes, checked after every change against brute force and
// against a tree rebuilt from its leaves, and every rank selected.

static void test_indicator_random (void) {
  generator random = 42;
  for (unsigned round = 0; round < 20; round++) {
    const unsigned vars = 1 + kissat_next_random32 (&random) % 300;
    indicator dummy, *indicator = &dummy;
    memset (indicator, 0, sizeof *indicator);
    kissat_enable_indicator (0, indicator, vars);
    struct indicator dummy_copy, *copy = &dummy_copy;
    memset (copy, 0, sizeof *copy);
    kissat_enable_indicator (0, copy, vars);
    unsigned present = 0;
    for (unsigned step = 0; step < 2000; step++) {
      const unsigned idx = kissat_next_random32 (&random) % vars;
      const bool before = kissat_indicator_contains (indicator, idx);
      const bool after = kissat_next_random32 (&random) % 2;
      kissat_indicator_set (indicator, idx, after);
      if (after && !before)
        present++;
      else if (!after && before)
        present--;
      assert (kissat_indicator_total (indicator) == present);
      assert (!kissat_indicator_inconsistent_node (indicator));
      if (step % 100)
        continue;
      for (unsigned rank = 0; rank < present; rank++)
        assert (kissat_indicator_select (indicator, rank) ==
                brute_force_select (indicator, vars, rank));
      for (unsigned i = 0; i < indicator->leaves; i++)
        kissat_indicator_put (copy, i,
                              kissat_indicator_contains (indicator, i));
      kissat_rebuild_indicator (copy);
      assert (!memcmp (copy->counts, indicator->counts,
                       2 * indicator->leaves * sizeof *copy->counts));
    }
    kissat_release_indicator (0, indicator);
    kissat_release_indicator (0, copy);
  }
}

// Draws land on present leaves only and hit each about equally often.
// The rank of a draw is below the total even for the largest double the
// generator gives, 1 - 2^-53.

static void test_indicator_draw (void) {
  const double largest = 1 - 1.0 / 9007199254740992.0;
  for (unsigned total = 1; total < 1u << 20; total++)
    assert ((unsigned) (largest * total) == total - 1);
  for (unsigned total = UINT_MAX; total > 1u << 20; total -= total / 1000)
    assert ((unsigned) (largest * total) == total - 1);
  indicator dummy, *indicator = &dummy;
  memset (indicator, 0, sizeof *indicator);
  kissat_enable_indicator (0, indicator, 37);
  const unsigned present[] = {0, 5, 6, 17, 30, 36};
  const unsigned n = sizeof present / sizeof *present;
  for (unsigned i = 0; i < n; i++)
    kissat_indicator_insert (indicator, present[i]);
  unsigned counts[37] = {0};
  generator random = 3;
  const unsigned draws = 60000;
  for (unsigned i = 0; i < draws; i++) {
    const unsigned idx = kissat_indicator_draw (indicator, &random);
    assert (idx < 37);
    assert (kissat_indicator_contains (indicator, idx));
    counts[idx]++;
  }
  for (unsigned i = 0; i < n; i++)
    assert (abs ((int) counts[present[i]] - (int) (draws / n)) < 500);
  // A single present leaf is always drawn.
  for (unsigned i = 1; i < n; i++)
    kissat_indicator_remove (indicator, present[i]);
  for (unsigned i = 0; i < 100; i++)
    assert (!kissat_indicator_draw (indicator, &random));
  kissat_release_indicator (0, indicator);
}

void tissat_schedule_indicator (void) {
  SCHEDULE_FUNCTION (test_indicator_basic);
  SCHEDULE_FUNCTION (test_indicator_random);
  SCHEDULE_FUNCTION (test_indicator_draw);
}
