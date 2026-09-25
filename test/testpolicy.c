#include "../src/decide.h"
#include "../src/inlinepolicy.h"

#include "test.h"

#include <math.h>

#if !defined(HEAPARGMAX) && !defined(NOPTIONS)

// A solver with one clause over 'vars' variables, in stable mode with the
// policy started as the search starts it.  Without the pseudo-activity the
// first variable has Kissat's initial score zero.

static kissat *new_solver (unsigned vars, bool softmax, int etalog2,
                           bool pseudo) {
  kissat *solver = kissat_init ();
  kissat_set_option (solver, "softmax", softmax);
  kissat_set_option (solver, "etalog2", etalog2);
  kissat_set_option (solver, "pseudoactivity", pseudo);
  for (unsigned i = 1; i <= vars; i++)
    kissat_add (solver, (int) i);
  kissat_add (solver, 0);
  solver->stable = true;
  kissat_update_scores (solver);
  kissat_start_policy (solver);
  return solver;
}

static void assign (kissat *solver, unsigned idx) {
  const unsigned lit = LIT (idx);
  solver->values[lit] = 1;
  solver->values[NOT (lit)] = -1;
  solver->unassigned--;
}

static void unassign (kissat *solver, unsigned idx) {
  const unsigned lit = LIT (idx);
  solver->values[lit] = solver->values[NOT (lit)] = 0;
  solver->unassigned++;
  kissat_policy_unassign (solver, idx);
}

// Argmax keeps an unweighted tree; Sample weighs it with score^eta.

static void test_policy_start (void) {
  kissat *solver = new_solver (5, false, 0, true);
  assert (!solver->policy.tree.weighted);
  kissat_release (solver);
  solver = new_solver (5, true, 3, true);
  const tree *const tree = &solver->policy.tree;
  assert (tree->weighted);
  for (unsigned idx = 0; idx < 5; idx++) {
    const double score = kissat_get_score (solver, idx);
    const tree_weight w = kissat_tree_weight (tree, idx);
    assert (fabs (kissat_tree_log2_of_weight (w) - 8 * log2 (score)) <
            1e-12);
  }
  kissat_release (solver);
}

// Sample never picks an assigned variable, removes those its draws meet,
// and backtracking puts them back.

static void test_policy_sample (void) {
  kissat *solver = new_solver (20, true, 0, true);
  const tree *const tree = &solver->policy.tree;
  for (unsigned idx = 0; idx < 20; idx += 2)
    assign (solver, idx);
  for (unsigned i = 0; i < 1000; i++) {
    const unsigned res = kissat_policy_pick (solver);
    assert (res % 2);
  }
  assert (!solver->policy.count.fallbacks[0]);
  unsigned removed = 0;
  for (unsigned idx = 0; idx < 20; idx += 2)
    removed += !kissat_tree_contains (tree, idx);
  assert (removed == 10);
  for (unsigned idx = 0; idx < 20; idx += 2)
    unassign (solver, idx);
  for (unsigned idx = 0; idx < 20; idx++)
    assert (kissat_tree_contains (tree, idx));
  assert (!kissat_tree_inconsistent_node (tree));
  kissat_release (solver);
}

// Without the pseudo-activity the first variable has score zero, hence
// weight zero.  Once every other variable is assigned no draw can reach
// it, and the pick falls back to Argmax's choice.

static void test_policy_fallback (void) {
  kissat *solver = new_solver (4, true, 0, false);
  assert (!kissat_get_score (solver, 0));
  assert (!kissat_tree_weight (&solver->policy.tree, 0).mantissa);
  for (unsigned idx = 1; idx < 4; idx++)
    assign (solver, idx);
  assert (kissat_policy_pick (solver) == 0);
  assert (solver->policy.count.picks[0] == 1);
  assert (solver->policy.count.fallbacks[0] == 1);
  assert (!solver->policy.count.fallbacks[1]);
  unassign (solver, 2);
  assert (kissat_policy_pick (solver) == 2);
  assert (solver->policy.count.fallbacks[0] == 1);
  kissat_release (solver);
  solver = new_solver (4, true, 0, true);
  assert (kissat_get_score (solver, 0) == 1.0);
  for (unsigned idx = 1; idx < 4; idx++)
    assign (solver, idx);
  assert (kissat_policy_pick (solver) == 0);
  assert (!solver->policy.count.fallbacks[0]);
  kissat_release (solver);
}

#ifdef DECISION_METRICS

// Decision metrics.  A sample at every decision, whatever the number of
// variables.

static void sample_every_decision (kissat *solver) {
  kissat_set_option (solver, "metricsint", 1);
  kissat_set_option (solver, "metricsvars", 0);
}

static void set_scores (kissat *solver, unsigned vars,
                        const double *scores) {
  for (unsigned idx = 0; idx < vars; idx++)
    kissat_update_score (solver, idx, scores[idx]);
}

// The statistics of Sample's softmax over the unassigned active variables
// by brute force, with weights score^eta, or exp (eta * Q) with CHB scores:
// entropy, the probability of a variable other than Argmax's choice, and
// of a score below the largest.

struct expected {
  unsigned argmax;
  double entropy, differ, lower;
};

static struct expected expected_softmax (kissat *solver, double eta,
                                         bool chb) {
  struct expected res = {UINT_MAX, 0, 0, 0};
  double weight[64], total = 0, largest = -1;
  assert (VARS <= 64);
  for (all_variables (idx)) {
    weight[idx] = 0;
    if (!ACTIVE (idx) || VALUE (LIT (idx)))
      continue;
    const double s = kissat_get_score (solver, idx);
    weight[idx] = chb ? exp (eta * s) : pow (s, eta);
    total += weight[idx];
    if (s > largest)
      largest = s, res.argmax = idx;
  }
  double top = 0;
  for (all_variables (idx)) {
    if (!weight[idx])
      continue;
    const double p = weight[idx] / total;
    res.entropy -= p * log (p);
    if (kissat_get_score (solver, idx) == largest)
      top += p;
  }
  res.differ = 1 - weight[res.argmax] / total;
  res.lower = 1 - top;
  return res;
}

static bool approx (double a, double b) { return fabs (a - b) < 1e-9; }

// Argmax: every sample puts all mass on the decision, which is Argmax's
// choice; warm-up decisions are kept apart.

static void test_policy_metrics_argmax (void) {
  kissat *solver = new_solver (10, false, 0, true);
  sample_every_decision (solver);
  assign (solver, 9), assign (solver, 4);
  for (unsigned i = 0; i < 3; i++)
    assert (kissat_next_decision_variable (solver) == 8);
  solver->warming = true;
  assert (kissat_next_decision_variable (solver) == 8);
  solver->warming = false;
  const policy_metrics *const m = solver->policy.metrics;
  assert (m[0].decisions == 3), assert (m[1].decisions == 1);
  assert (!m[0].random), assert (!m[1].random);
  assert (m[0].samples == 3), assert (m[1].samples == 1);
  assert (m[0].arms == 3 * 8.0), assert (m[1].arms == 8);
  assert (m[0].entropy == 0), assert (m[0].effective == 3);
  assert (approx (m[0].share, 3 / 8.0));
  assert (!m[0].differ), assert (!m[0].lower);
  assert (!m[0].differed), assert (!m[0].lowered);
#if defined(__x86_64__) || defined(__i386__)
  assert (m[0].ticks), assert (m[1].ticks);
#endif
  kissat_release (solver);
}

// Sample on VSIDS scores at eta 2: the sampled statistics are those of the
// softmax, ties at the largest score included, and the decisions made
// differ from Argmax's choice about as often as the softmax says.

static void test_policy_metrics_sample (void) {
  kissat *solver = new_solver (8, true, 1, true);
  sample_every_decision (solver);
  const double scores[8] = {3, 1, 4, 1, 5, 5, 2, 0.5};
  set_scores (solver, 8, scores);
  assign (solver, 0), assign (solver, 2);
  const struct expected e = expected_softmax (solver, 2, false);
  assert (e.argmax == 4);
  assert (approx (e.differ, 1 - 25 / 56.25));
  assert (approx (e.lower, 1 - 50 / 56.25));
  const unsigned decisions = 20000;
  unsigned differed = 0, lowered = 0;
  for (unsigned i = 0; i < decisions; i++) {
    const unsigned idx = kissat_next_decision_variable (solver);
    assert (idx != 0 && idx != 2);
    differed += idx != 4;
    lowered += scores[idx] < 5;
  }
  const policy_metrics *const m = solver->policy.metrics;
  assert (m->samples == decisions);
  assert (m->differed == differed), assert (m->lowered == lowered);
  assert (approx (m->entropy / decisions, e.entropy));
  assert (approx (m->effective / decisions, exp (e.entropy)));
  assert (approx (m->share / decisions, exp (e.entropy) / 6));
  assert (approx (m->differ / decisions, e.differ));
  assert (approx (m->lower / decisions, e.lower));
  assert (m->arms == 6.0 * decisions);
  assert (fabs ((double) differed / decisions - e.differ) < 0.02);
  assert (fabs ((double) lowered / decisions - e.lower) < 0.02);
  assert (!solver->policy.count.fallbacks[0]);
  kissat_release (solver);
}

// Sample on CHB scores at eta 4: weights exp (4 Q).

static void test_policy_metrics_chb (void) {
  kissat *solver = kissat_init ();
  kissat_set_option (solver, "chb", 1);
  kissat_set_option (solver, "softmax", 1);
  kissat_set_option (solver, "etalog2", 2);
  for (int i = 1; i <= 6; i++)
    kissat_add (solver, i);
  kissat_add (solver, 0);
  solver->stable = true;
  kissat_update_scores (solver);
  kissat_start_policy (solver);
  sample_every_decision (solver);
  const double scores[6] = {0.1, 0.5, 0.5, 0, 0.9, 0.2};
  set_scores (solver, 6, scores);
  assign (solver, 4);
  const struct expected e = expected_softmax (solver, 4, true);
  assert (e.argmax == 1);
  const unsigned idx = kissat_next_decision_variable (solver);
  const policy_metrics *const m = solver->policy.metrics;
  assert (m->samples == 1);
  assert (approx (m->entropy, e.entropy));
  assert (approx (m->differ, e.differ));
  assert (approx (m->lower, e.lower));
  assert (m->differed == (idx != 1));
  assert (m->lowered == (scores[idx] < 0.5));
  kissat_release (solver);
}

// A random decision of a burst: the uniform distribution.  The sample
// changes neither the tree nor the policy's generator.

static void test_policy_metrics_random (void) {
  kissat *solver = new_solver (10, true, 0, true);
  sample_every_decision (solver);
  const double scores[10] = {1, 7, 2, 7, 3, 7, 4, 5, 6, 7};
  set_scores (solver, 10, scores);
  assign (solver, 9), assign (solver, 0), assign (solver, 2);
  const tree *const tree = &solver->policy.tree;
  const unsigned leaves = tree->leaves;
  double keys[16];
  tree_weight weights[16], sums[16];
  unsigned args[16];
  assert (leaves == 16);
  memcpy (keys, tree->keys, sizeof keys);
  memcpy (weights, tree->weights, sizeof weights);
  memcpy (sums, tree->sums, sizeof sums);
  memcpy (args, tree->args, sizeof args);
  const generator random = solver->policy.random;
  kissat_policy_decided (solver, 6, true, kissat_policy_clock ());
  assert (!memcmp (keys, tree->keys, sizeof keys));
  assert (!memcmp (weights, tree->weights, sizeof weights));
  assert (!memcmp (sums, tree->sums, sizeof sums));
  assert (!memcmp (args, tree->args, sizeof args));
  assert (solver->policy.random == random);
  const policy_metrics *const m = solver->policy.metrics;
  assert (m->decisions == 1), assert (m->random == 1);
  assert (m->samples == 1);
  assert (approx (m->entropy, log (7)));
  assert (approx (m->effective, 7)), assert (approx (m->share, 1));
  assert (approx (m->differ, 1 - 1 / 7.0));
  assert (approx (m->lower, 1 - 3 / 7.0));
  assert (m->differed == 1), assert (m->lowered == 1);
  kissat_release (solver);
}

// A fallback puts all mass on Argmax's choice.

static void test_policy_metrics_fallback (void) {
  kissat *solver = new_solver (4, true, 0, false);
  sample_every_decision (solver);
  for (unsigned idx = 1; idx < 4; idx++)
    assign (solver, idx);
  assert (kissat_next_decision_variable (solver) == 0);
  assert (solver->policy.count.fallbacks[0] == 1);
  const policy_metrics *const m = solver->policy.metrics;
  assert (m->samples == 1);
  assert (m->entropy == 0), assert (m->effective == 1);
  assert (!m->differ), assert (!m->lower);
  assert (!m->differed), assert (!m->lowered);
  kissat_release (solver);
}

// A sample is due every 'metricsint' decisions, and none with zero; with
// 'metricsvars' (the default) every 'VARS' decisions if there are more
// variables.  Warm-up decisions are counted apart.

static void test_policy_metrics_schedule (void) {
  kissat *solver = new_solver (8, false, 0, true);
  const policy_metrics *const m = solver->policy.metrics;
  kissat_set_option (solver, "metricsint", 0);
  for (unsigned i = 0; i < 5; i++)
    (void) kissat_next_decision_variable (solver);
  assert (m[0].decisions == 5), assert (!m[0].samples);
  assert (!m[0].since);
  kissat_set_option (solver, "metricsint", 3);
  kissat_set_option (solver, "metricsvars", 0);
  for (unsigned i = 0; i < 7; i++)
    (void) kissat_next_decision_variable (solver);
  assert (m[0].decisions == 12), assert (m[0].samples == 2);
  assert (m[0].since == 1);
  kissat_set_option (solver, "metricsvars", 1);
  for (unsigned i = 0; i < 6; i++)
    (void) kissat_next_decision_variable (solver);
  assert (m[0].samples == 2), assert (m[0].since == 7);
  (void) kissat_next_decision_variable (solver);
  assert (m[0].samples == 3), assert (!m[0].since);
  kissat_set_option (solver, "metricsint", 9);
  for (unsigned i = 0; i < 9; i++)
    (void) kissat_next_decision_variable (solver);
  assert (m[0].samples == 4);
  solver->warming = true;
  for (unsigned i = 0; i < 9; i++)
    (void) kissat_next_decision_variable (solver);
  solver->warming = false;
  assert (m[0].samples == 4), assert (m[1].samples == 1);
  assert (m[1].decisions == 9);
  kissat_release (solver);
}

#endif

#endif

void tissat_schedule_policy (void) {
#if !defined(HEAPARGMAX) && !defined(NOPTIONS)
  SCHEDULE_FUNCTION (test_policy_start);
  SCHEDULE_FUNCTION (test_policy_sample);
  SCHEDULE_FUNCTION (test_policy_fallback);
#ifdef DECISION_METRICS
  SCHEDULE_FUNCTION (test_policy_metrics_argmax);
  SCHEDULE_FUNCTION (test_policy_metrics_sample);
  SCHEDULE_FUNCTION (test_policy_metrics_chb);
  SCHEDULE_FUNCTION (test_policy_metrics_random);
  SCHEDULE_FUNCTION (test_policy_metrics_fallback);
  SCHEDULE_FUNCTION (test_policy_metrics_schedule);
#endif
#endif
}
