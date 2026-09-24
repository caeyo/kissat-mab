#include "../src/inlinetree.h"

#include "test.h"

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
        const double weight = kissat_next_random32 (&random) % 8;
        kissat_tree_set (tree, idx, key, weight);
      }
      assert (kissat_tree_max (tree) == brute_force_max (tree, vars));
      assert (!kissat_tree_inconsistent_node (tree));
      if (step % 100)
        continue;
      for (unsigned i = 0; i < tree->leaves; i++)
        kissat_tree_put (copy, i, tree->keys[i],
                         weighted ? tree->weights[i] : 0);
      kissat_rebuild_tree (copy);
      for (unsigned i = 1; i < tree->leaves; i++) {
        assert (copy->args[i] == tree->args[i]);
        if (weighted)
          assert (kissat_same_double (copy->sums[i], tree->sums[i]));
      }
    }
    kissat_release_tree (0, tree);
    kissat_release_tree (0, copy);
  }
}

static void test_tree_random_unweighted (void) { test_tree_random (false); }

static void test_tree_random_weighted (void) { test_tree_random (true); }

// With small integer weights every sum is exact, so the descent must end
// in the leaf 'idx' with 'W(idx) <= u < W(idx) + w(idx)' for the prefix
// sums 'W' in index order, at every integer 'u' and between them.

static void test_tree_sample (void) {
  generator random = 7;
  for (unsigned round = 0; round < 50; round++) {
    const unsigned vars = 1 + kissat_next_random32 (&random) % 200;
    tree dummy, *tree = &dummy;
    memset (tree, 0, sizeof *tree);
    tree->weighted = true;
    kissat_resize_tree (0, tree, vars);
    unsigned present = 0;
    for (unsigned idx = 0; idx < vars; idx++) {
      if (kissat_next_random32 (&random) % 4) {
        const double weight = kissat_next_random32 (&random) % 5;
        kissat_tree_set (tree, idx, 1.0, weight);
        present++;
      }
    }
    if (present && kissat_tree_total (tree) > 0) {
      double total = 0;
      for (unsigned idx = 0; idx < vars; idx++)
        total += tree->weights[idx];
      assert (kissat_tree_total (tree) == total);
      for (double u = 0; u < total; u += 0.5) {
        const unsigned res = kissat_tree_sample (tree, u);
        assert (res < vars);
        double before = 0;
        for (unsigned idx = 0; idx < res; idx++)
          before += tree->weights[idx];
        assert (tree->weights[res] > 0);
        assert (before <= u);
        assert (u < before + tree->weights[res]);
      }
    }
    kissat_release_tree (0, tree);
  }
}

// Absent leaves and leaves of weight zero are never drawn, even for 'u'
// at or beyond the total, where rounding can put it.

static void test_tree_sample_edges (void) {
  tree dummy, *tree = &dummy;
  memset (tree, 0, sizeof *tree);
  tree->weighted = true;
  kissat_resize_tree (0, tree, 16);
  kissat_tree_set (tree, 2, 1.0, 1.0);
  kissat_tree_set (tree, 5, 1.0, 0.0);
  kissat_tree_set (tree, 9, 1.0, 2.0);
  kissat_tree_set (tree, 12, 1.0, 0.0);
  assert (kissat_tree_total (tree) == 3.0);
  assert (kissat_tree_sample (tree, 0.0) == 2);
  assert (kissat_tree_sample (tree, 0.999) == 2);
  assert (kissat_tree_sample (tree, 1.0) == 9);
  assert (kissat_tree_sample (tree, 2.999) == 9);
  assert (kissat_tree_sample (tree, 3.0) == 9);
  assert (kissat_tree_sample (tree, 100.0) == 9);
  kissat_tree_remove (tree, 9);
  assert (kissat_tree_total (tree) == 1.0);
  assert (kissat_tree_sample (tree, 1.0) == 2);
  assert (kissat_tree_sample (tree, 5.0) == 2);
  kissat_release_tree (0, tree);
}

void tissat_schedule_tree (void) {
  SCHEDULE_FUNCTION (test_tree_basic);
  SCHEDULE_FUNCTION (test_tree_random_unweighted);
  SCHEDULE_FUNCTION (test_tree_random_weighted);
  SCHEDULE_FUNCTION (test_tree_sample);
  SCHEDULE_FUNCTION (test_tree_sample_edges);
}
