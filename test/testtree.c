#include "../src/inlinetree.h"

#include "test.h"

#include <stdlib.h>

// Brute force: the present variable of largest key, the smallest index
// among ties, or 'UINT_MAX'.

static unsigned brute_force_max (const tree *tree, unsigned vars) {
  unsigned res = UINT_MAX;
  for (unsigned idx = 0; idx < vars; idx++) {
    if (!kissat_tree_contains (tree, idx))
      continue;
    if (res == UINT_MAX ||
        kissat_tree_key (tree, idx) > kissat_tree_key (tree, res))
      res = idx;
  }
  return res;
}

static void test_tree_basic (void) {
  tree dummy, *tree = &dummy;
  memset (tree, 0, sizeof *tree);
  assert (kissat_tree_max (tree) == UINT_MAX);
  kissat_resize_tree (0, tree, 5);
  assert (tree->leaves == 8);
  assert (kissat_tree_max (tree) == UINT_MAX);
  for (unsigned idx = 0; idx < 8; idx++)
    assert (!kissat_tree_contains (tree, idx));
  kissat_tree_set (tree, 3, 1.0, 0);
  assert (kissat_tree_max (tree) == 3);
  kissat_tree_set (tree, 4, 1.0, 0);
  assert (kissat_tree_max (tree) == 3);
  kissat_tree_set (tree, 1, 1.0, 0);
  assert (kissat_tree_max (tree) == 1);
  kissat_tree_set (tree, 4, 2.0, 0);
  assert (kissat_tree_max (tree) == 4);
  assert (kissat_tree_max_key (tree) == 2.0);
  kissat_tree_remove (tree, 4);
  assert (kissat_tree_max (tree) == 1);
  kissat_tree_set (tree, 0, 0.0, 0);
  assert (kissat_tree_max (tree) == 1);
  kissat_tree_remove (tree, 1);
  kissat_tree_remove (tree, 3);
  assert (kissat_tree_max (tree) == 0);
  assert (kissat_tree_max_key (tree) == 0.0);
  kissat_resize_tree (0, tree, 100);
  assert (tree->leaves == 128);
  assert (kissat_tree_max (tree) == 0);
  assert (!kissat_tree_inconsistent_node (tree));
  kissat_tree_set (tree, 99, 0.0, 0);
  assert (kissat_tree_max (tree) == 0);
  kissat_tree_remove (tree, 99);
  kissat_resize_tree (0, tree, 1);
  assert (tree->leaves == 2);
  assert (kissat_tree_max (tree) == 0);
  kissat_tree_remove (tree, 0);
  assert (kissat_tree_max (tree) == UINT_MAX);
  kissat_release_tree (0, tree);
  assert (!tree->leaves);
}

// Base-2 logarithms of weights, far beyond the range of a double's
// exponent in both directions, and zero weight.

static double random_log2_weight (generator *random) {
  static const double log2_weights[] = {
      -INFINITY, 0.0, 1.0, 2.5, -1100.0, 1100.0, -40000.25, 40000.0, -60.0};
  const unsigned n = sizeof log2_weights / sizeof *log2_weights;
  return log2_weights[kissat_next_random32 (random) % n];
}

static double random_key (generator *random) {
  static const double keys[] = {0.0, 0.5, 1.0, 1.0, 3.0, 1e-300, 1e150};
  const unsigned n = sizeof keys / sizeof *keys;
  return keys[kissat_next_random32 (random) % n];
}

// Random changes with many ties, checked after every change against brute
// force and against a tree rebuilt from scratch.

static void test_tree_random (bool weighted) {
  generator random = 42;
  for (unsigned round = 0; round < 20; round++) {
    const unsigned vars = 1 + kissat_next_random32 (&random) % 300;
    tree dummy, *tree = &dummy;
    memset (tree, 0, sizeof *tree);
    tree->weighted = weighted;
    kissat_resize_tree (0, tree, vars);
    struct tree dummy_copy, *copy = &dummy_copy;
    memset (copy, 0, sizeof *copy);
    copy->weighted = weighted;
    kissat_resize_tree (0, copy, vars);
    for (unsigned step = 0; step < 2000; step++) {
      const unsigned idx = kissat_next_random32 (&random) % vars;
      if (kissat_tree_contains (tree, idx) &&
          !(kissat_next_random32 (&random) % 3))
        kissat_tree_remove (tree, idx);
      else {
        const double key = random_key (&random);
        const double log2_weight = random_log2_weight (&random);
        kissat_tree_set (tree, idx, key, log2_weight);
      }
      assert (kissat_tree_max (tree) == brute_force_max (tree, vars));
      assert (!kissat_tree_inconsistent_node (tree));
      if (step % 100)
        continue;
      for (unsigned i = 0; i < tree->leaves; i++)
        kissat_tree_put (
            copy, i, tree->keys[i],
            weighted ? kissat_tree_log2_of_weight (tree->weights[i]) : 0);
      kissat_rebuild_tree (copy);
      for (unsigned i = 0; i < tree->leaves; i++)
        if (weighted)
          assert (kissat_tree_same_weight (copy->weights[i],
                                           tree->weights[i]));
      for (unsigned i = 1; i < tree->leaves; i++) {
        assert (copy->args[i] == tree->args[i]);
        if (weighted)
          assert (kissat_tree_same_weight (copy->sums[i], tree->sums[i]));
      }
    }
    kissat_release_tree (0, tree);
    kissat_release_tree (0, copy);
  }
}

static void test_tree_random_unweighted (void) { test_tree_random (false); }

static void test_tree_random_weighted (void) { test_tree_random (true); }

// With weights 2^offset times 0, 1, 2, 4 or 8 every sum is exact, so the
// descent must end in the leaf 'idx' with 'W(idx) <= v < W(idx) + w(idx)'
// for the prefix sums 'W' in index order (in units of 2^offset), at every
// multiple of 1/2 'v' below the total.  The offsets put the weights far
// below and above the range of a double's exponent.

static void test_tree_sample_offset (int offset) {
  generator random = 7;
  for (unsigned round = 0; round < 50; round++) {
    const unsigned vars = 1 + kissat_next_random32 (&random) % 200;
    tree dummy, *tree = &dummy;
    memset (tree, 0, sizeof *tree);
    tree->weighted = true;
    kissat_resize_tree (0, tree, vars);
    unsigned *w = calloc (vars, sizeof *w);
    unsigned total = 0;
    for (unsigned idx = 0; idx < vars; idx++) {
      if (kissat_next_random32 (&random) % 4) {
        const unsigned k = kissat_next_random32 (&random) % 5;
        w[idx] = k ? 1u << (k - 1) : 0;
        kissat_tree_set (tree, idx, 1.0,
                         k ? offset + (double) (k - 1) : -INFINITY);
        total += w[idx];
      }
    }
    assert (kissat_tree_has_weight (tree) == (total > 0));
    if (total) {
      const tree_weight sum = kissat_tree_total (tree);
      assert (sum.mantissa * kissat_tree_pow2 (sum.exponent - offset) ==
              total);
      for (double v = 0; v < total; v += 0.5) {
        const double u = v * kissat_tree_pow2 (offset - sum.exponent);
        const unsigned res = kissat_tree_sample (tree, u);
        assert (res < vars);
        unsigned before = 0;
        for (unsigned idx = 0; idx < res; idx++)
          before += w[idx];
        assert (w[res] > 0);
        assert (before <= v);
        assert (v < before + w[res]);
      }
    }
    free (w);
    kissat_release_tree (0, tree);
  }
}

static void test_tree_sample (void) {
  test_tree_sample_offset (0);
  test_tree_sample_offset (-5000);
  test_tree_sample_offset (5000);
  test_tree_sample_offset (-100000);
}

// Absent leaves and leaves of weight zero are never drawn, even for 'u'
// at or beyond the total, where rounding can put it; nor is a leaf too
// small to count in its parent's sum.

static void test_tree_sample_edges (void) {
  tree dummy, *tree = &dummy;
  memset (tree, 0, sizeof *tree);
  tree->weighted = true;
  kissat_resize_tree (0, tree, 16);
  assert (!kissat_tree_has_weight (tree));
  kissat_tree_set (tree, 2, 1.0, 0.0);
  kissat_tree_set (tree, 5, 1.0, -INFINITY);
  kissat_tree_set (tree, 9, 1.0, 1.0);
  kissat_tree_set (tree, 12, 1.0, -INFINITY);
  tree_weight total = kissat_tree_total (tree);
  assert (total.mantissa == 1.5 && total.exponent == 1);
  assert (kissat_tree_sample (tree, 0.0) == 2);
  assert (kissat_tree_sample (tree, 0.4995) == 2);
  assert (kissat_tree_sample (tree, 0.5) == 9);
  assert (kissat_tree_sample (tree, 1.4995) == 9);
  assert (kissat_tree_sample (tree, 1.5) == 9);
  assert (kissat_tree_sample (tree, 50.0) == 9);
  kissat_tree_remove (tree, 9);
  total = kissat_tree_total (tree);
  assert (total.mantissa == 1.0 && total.exponent == 0);
  assert (kissat_tree_sample (tree, 1.0) == 2);
  assert (kissat_tree_sample (tree, 5.0) == 2);
  kissat_tree_set (tree, 7, 1.0, -1000.0);
  assert (kissat_tree_sample (tree, 1.0) == 2);
  kissat_tree_remove (tree, 2);
  total = kissat_tree_total (tree);
  assert (total.mantissa == 1.0 && total.exponent == -1000);
  assert (kissat_tree_sample (tree, 0.0) == 7);
  assert (kissat_tree_sample (tree, 3.0) == 7);
  kissat_tree_set (tree, 3, 1.0, 200.0);
  assert (kissat_tree_sample (tree, 0.0) == 3);
  assert (kissat_tree_sample (tree, 1.0) == 3);
  kissat_tree_remove (tree, 3);
  kissat_tree_remove (tree, 7);
  assert (!kissat_tree_has_weight (tree));
  kissat_release_tree (0, tree);
}

// A weight given by its logarithm comes back as it went in.

static void test_tree_weights (void) {
  const double log2_weights[] = {0.0,     1.0,      -1.0,     0.5,
                                 -1074.5, 1024.25,  -40000.0, 123456.75,
                                 1e-300,  -1e-300, 0.9999999999999999};
  for (unsigned i = 0; i < sizeof log2_weights / sizeof *log2_weights;
       i++) {
    const double l = log2_weights[i];
    const tree_weight w = kissat_tree_weight_of_log2 (l);
    assert (1 <= w.mantissa && w.mantissa < 2);
    assert (fabs (kissat_tree_log2_of_weight (w) - l) <=
            1e-12 * (1 + fabs (l)));
  }
  const tree_weight zero = kissat_tree_weight_of_log2 (-INFINITY);
  assert (zero.mantissa == 0);
  assert (kissat_tree_log2_of_weight (zero) == -INFINITY);
  const tree_weight a = kissat_tree_weight_of_log2 (3000.0);
  const tree_weight b = kissat_tree_weight_of_log2 (3000.0);
  const tree_weight s = kissat_tree_add (a, b);
  assert (s.mantissa == 2 && s.exponent == 3000);
  assert (kissat_tree_same_weight (kissat_tree_add (a, zero), a));
  assert (kissat_tree_same_weight (kissat_tree_add (zero, a), a));
  const tree_weight c = kissat_tree_weight_of_log2 (3000.0 - 200.0);
  assert (kissat_tree_same_weight (kissat_tree_add (a, c), a));
}

void tissat_schedule_tree (void) {
  SCHEDULE_FUNCTION (test_tree_basic);
  SCHEDULE_FUNCTION (test_tree_random_unweighted);
  SCHEDULE_FUNCTION (test_tree_random_weighted);
  SCHEDULE_FUNCTION (test_tree_sample);
  SCHEDULE_FUNCTION (test_tree_sample_edges);
  SCHEDULE_FUNCTION (test_tree_weights);
}
