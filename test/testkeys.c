#include "../src/backtrack.h"
#include "../src/bump.h"
#include "../src/chb.h"
#include "../src/decide.h"
#include "../src/error.h"
#include "../src/inlinepolicy.h"

#include "test.h"

#include <math.h>
#include <setjmp.h>

#if !defined(HEAPARGMAX) && !defined(NOPTIONS)

// A solver with one clause over 'vars' variables, in stable mode with the
// policy started as the search starts it, after the options were set.

static void start_solver (kissat *solver, unsigned vars) {
  for (unsigned i = 1; i <= vars; i++)
    kissat_add (solver, (int) i);
  kissat_add (solver, 0);
  solver->stable = true;
  kissat_update_scores (solver);
  kissat_start_policy (solver);
}

static kissat *new_solver (unsigned vars, const char *name, int value,
                           const char *other, int other_value) {
  kissat *solver = kissat_init ();
  kissat_set_option (solver, name, value);
  if (other)
    kissat_set_option (solver, other, other_value);
  start_solver (solver, vars);
  return solver;
}

// Assignment by hand (values only), for the tests that do not unassign.
// The others assign on the trail, as decisions, and backtrack.

static void assign (kissat *solver, unsigned idx) {
  const unsigned lit = LIT (idx);
  solver->values[lit] = 1;
  solver->values[NOT (lit)] = -1;
  solver->unassigned--;
}

static bool same (double a, double b) { return kissat_same_double (a, b); }

static bool close (double a, double b) {
  return fabs (a - b) <= 1e-12 * fmax (fabs (a), fabs (b));
}

// Every present leaf holds the variable's key bitwise, and every internal
// node is what its children give.

static void check_keys (kissat *solver) {
  const tree *const tree = &solver->policy.tree;
  for (all_variables (idx))
    if (kissat_tree_contains (tree, idx))
      assert (same (kissat_tree_key (tree, idx),
                    kissat_policy_key (solver, idx)));
  assert (!kissat_tree_inconsistent_node (tree));
}

// The variable of largest key among the unassigned active ones, the
// smallest index among ties, by brute force.

static unsigned largest_key (kissat *solver) {
  unsigned res = INVALID_IDX;
  double largest = -INFINITY;
  for (all_variables (idx)) {
    if (!ACTIVE (idx) || VALUE (LIT (idx)))
      continue;
    const double key = kissat_policy_key (solver, idx);
    if (res == INVALID_IDX || key > largest)
      res = idx, largest = key;
  }
  return res;
}

// Only one of 'softmax', 'perturbed', 'thompson' and 'ucb', none of the
// last three with mixing, and P1 only on VSIDS scores: anything else is a
// fatal error at the start of the search.

static jmp_buf jump_buffer;

static void abort_call_back (void) { longjmp (jump_buffer, 42); }

static bool start_fails (const char *name, int value, const char *other,
                         int other_value) {
  kissat *solver = kissat_init ();
  kissat_set_option (solver, name, value);
  kissat_set_option (solver, other, other_value);
  for (int i = 1; i <= 4; i++)
    kissat_add (solver, i);
  kissat_add (solver, 0);
  solver->stable = true;
  kissat_update_scores (solver);
  bool res = false;
  kissat_call_function_instead_of_abort (abort_call_back);
  if (setjmp (jump_buffer))
    res = true;
  else
    kissat_start_policy (solver);
  kissat_call_function_instead_of_abort (0);
  kissat_release (solver);
  return res;
}

static void test_keys_options (void) {
  assert (start_fails ("softmax", 1, "perturbed", 1));
  assert (start_fails ("perturbed", 1, "thompson", 1));
  assert (start_fails ("thompson", 1, "ucb", 1));
  assert (start_fails ("softmax", 1, "ucb", 1));
  assert (start_fails ("ucb", 1, "gammappm", 100));
  assert (start_fails ("thompson", 1, "gammappm", 1));
  assert (start_fails ("perturbed", 1, "chb", 1));
  assert (!start_fails ("thompson", 1, "chb", 1));
  assert (!start_fails ("ucb", 1, "chb", 1));
  assert (!start_fails ("perturbed", 1, "redraw", 1));
  assert (!start_fails ("softmax", 1, "gammappm", 100));
}

// Each policy keeps an unweighted tree, the arrays it needs, and its keys:
// s * e^x on VSIDS scores, Q + x on CHB scores, with the terms of its
// first draw point at the start of the search.

static void check_start (kissat *solver, unsigned kind, bool chb) {
  const policy *const policy = &solver->policy;
  const keys *const keys = &policy->keys;
  assert (keys->kind == kind);
  assert (policy->chb == chb);
  assert (!policy->tree.weighted);
  assert (keys->draws == 1);
  assert (keys->size == solver->size);
  assert ((keys->normal != 0) == (kind == KEYS_THOMPSON));
  assert ((keys->count != 0) == (kind == KEYS_UCB || chb));
  assert ((keys->opened != 0) == (kind == KEYS_UCB && !chb));
  for (all_variables (idx)) {
    const double score = kissat_get_score (solver, idx);
    const double term = keys->term[idx];
    const double key = kissat_tree_key (&policy->tree, idx);
    if (chb)
      assert (same (key, score + term));
    else {
      assert (term > 0);
      assert (same (key, score * term));
    }
  }
  check_keys (solver);
}

static void test_keys_start (void) {
  kissat *solver = new_solver (10, "perturbed", 1, "etalog2", 3);
  check_start (solver, KEYS_PERTURBED, false);
  assert (solver->policy.keys.noise);
  assert (solver->policy.etalog2 == 3);
  kissat_release (solver);
  solver = new_solver (10, "thompson", 1, "thompsonkappa", 250);
  check_start (solver, KEYS_THOMPSON, false);
  assert (solver->policy.keys.factor == 0.25);
  kissat_release (solver);
  solver = new_solver (10, "ucb", 1, "ucbc", 2000);
  check_start (solver, KEYS_UCB, false);
  assert (solver->policy.keys.factor == 2);
  assert (solver->policy.keys.noise);
  kissat_release (solver);
  solver = kissat_init ();
  kissat_set_option (solver, "chb", 1);
  kissat_set_option (solver, "thompson", 1);
  kissat_set_option (solver, "thompsonkappa", 100);
  start_solver (solver, 10);
  check_start (solver, KEYS_THOMPSON, true);
  kissat_release (solver);
  solver = kissat_init ();
  kissat_set_option (solver, "chb", 1);
  kissat_set_option (solver, "ucb", 1);
  start_solver (solver, 10);
  check_start (solver, KEYS_UCB, true);
  assert (!solver->policy.keys.noise);
  kissat_release (solver);
  solver = new_solver (10, "softmax", 1, 0, 0);
  assert (!solver->policy.keys.kind);
  assert (!solver->policy.keys.draws);
  assert (!solver->policy.keys.term);
  kissat_release (solver);
}

// TS at kappa zero and UCB at c zero: keys equal to the scores bitwise,
// so every pick is Argmax's, on scores with ties, while variables are
// assigned and unassigned.

static void check_zero_noise (kissat *solver) {
  const double scores[12] = {3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5, 9};
  for (unsigned idx = 0; idx < 12; idx++)
    kissat_update_score (solver, idx, scores[idx]);
  for (unsigned round = 0; round < 6; round++) {
    for (all_variables (idx))
      assert (same (kissat_policy_key (solver, idx),
                    kissat_get_score (solver, idx)));
    const unsigned expected = largest_key (solver);
    const unsigned res = kissat_policy_pick (solver);
    assert (res == expected);
    kissat_internal_assume (solver, LIT (res));
  }
  kissat_backtrack_without_updating_phases (solver, 0);
  check_keys (solver);
  assert (kissat_policy_pick (solver) == 5);
}

static void test_keys_zero_noise (void) {
  kissat *solver = new_solver (12, "thompson", 1, "thompsonkappa", 0);
  assert (!solver->policy.keys.noise);
  check_zero_noise (solver);
  kissat_release (solver);
  solver = new_solver (12, "ucb", 1, "ucbc", 0);
  assert (!solver->policy.keys.noise);
  check_zero_noise (solver);
  kissat_release (solver);
  solver = kissat_init ();
  kissat_set_option (solver, "chb", 1);
  kissat_set_option (solver, "thompson", 1);
  start_solver (solver, 12);
  check_zero_noise (solver);
  kissat_release (solver);
}

// P1: the first pick after a draw has Sample's distribution at eta (the
// Gumbel-max trick), here at eta 2, and between draw points every pick is
// the same.

static void test_keys_perturbed (void) {
  kissat *solver = new_solver (8, "perturbed", 1, "etalog2", 1);
  const double scores[8] = {3, 1, 4, 1, 5, 5, 2, 0.5};
  for (unsigned idx = 0; idx < 8; idx++)
    kissat_update_score (solver, idx, scores[idx]);
  check_keys (solver);
  assign (solver, 0), assign (solver, 2);
  const unsigned rounds = 20000;
  unsigned counts[8] = {0};
  for (unsigned i = 0; i < rounds; i++) {
    kissat_draw_keys (solver);
    const unsigned res = kissat_policy_pick (solver);
    counts[res]++;
    if (i < 10)
      for (unsigned j = 0; j < 5; j++)
        assert (kissat_policy_pick (solver) == res);
  }
  assert (solver->policy.keys.draws == rounds + 1);
  double total = 0;
  for (unsigned idx = 0; idx < 8; idx++)
    if (idx != 0 && idx != 2)
      total += scores[idx] * scores[idx];
  for (unsigned idx = 0; idx < 8; idx++) {
    if (idx == 0 || idx == 2) {
      assert (!counts[idx]);
      continue;
    }
    const double p = scores[idx] * scores[idx] / total;
    const double sigma = sqrt (p * (1 - p) / rounds);
    assert (fabs ((double) counts[idx] / rounds - p) < 5 * sigma);
  }
  kissat_release (solver);
}

// The perturbations: P1's at eta 1 are Gumbel (mean Euler's constant,
// variance pi^2 / 6), and TS's normals standard normal.

static void test_keys_draws (void) {
  kissat *solver = new_solver (2000, "perturbed", 1, 0, 0);
  double sum = 0, squares = 0;
  unsigned n = 0;
  for (unsigned i = 0; i < 50; i++) {
    kissat_draw_keys (solver);
    for (all_variables (idx)) {
      const double g = log (solver->policy.keys.term[idx]);
      sum += g, squares += g * g, n++;
    }
  }
  double mean = sum / n, variance = squares / n - mean * mean;
  assert (fabs (mean - 0.5772156649) < 0.02);
  assert (fabs (variance - 1.6449340668) < 0.05);
  kissat_release (solver);
  solver = new_solver (2001, "thompson", 1, "thompsonkappa", 1000);
  sum = squares = 0, n = 0;
  unsigned tail = 0;
  for (unsigned i = 0; i < 50; i++) {
    kissat_draw_keys (solver);
    for (all_variables (idx)) {
      const double z = solver->policy.keys.normal[idx];
      sum += z, squares += z * z, n++;
      tail += z < -1.959963985;
    }
  }
  mean = sum / n, variance = squares / n - mean * mean;
  assert (fabs (mean) < 0.02);
  assert (fabs (variance - 1) < 0.03);
  assert (fabs ((double) tail / n - 0.025) < 0.003);
  kissat_release (solver);
}

// TS on VSIDS scores: a variable's term follows its score at its bumps,
// e^(kappa * z / sqrt (1 + S)) with S the bumped score in units of the
// round's increment, and stays when a score changes otherwise.  A bump
// that the score cannot absorb still moves the term and the leaf.

static double thompson_term (kissat *solver, unsigned idx, double s) {
  const keys *const keys = &solver->policy.keys;
  return exp (keys->factor * keys->normal[idx] / sqrt (1 + s));
}

static void test_keys_thompson (void) {
  kissat *solver = new_solver (8, "thompson", 1, "thompsonkappa", 500);
  const keys *const keys = &solver->policy.keys;
  for (all_variables (idx))
    assert (same (keys->term[idx],
                  thompson_term (solver, idx,
                                 kissat_get_score (solver, idx) /
                                     solver->scinc)));
  const double inc = solver->scinc;
  const double old_score = kissat_get_score (solver, 3);
  PUSH_STACK (solver->analyzed, 3);
  kissat_bump_analyzed (solver);
  CLEAR_STACK (solver->analyzed);
  assert (solver->scinc > inc);
  const double new_score = kissat_get_score (solver, 3);
  assert (new_score == old_score + inc);
  assert (same (keys->term[3],
                thompson_term (solver, 3, new_score / inc)));
  check_keys (solver);
  const double term = keys->term[2];
  kissat_update_score (solver, 2, 7.5);
  assert (same (keys->term[2], term));
  check_keys (solver);
  kissat_update_score (solver, 5, 1e30);
  const double before = keys->term[5];
  PUSH_STACK (solver->analyzed, 5);
  kissat_bump_analyzed (solver);
  CLEAR_STACK (solver->analyzed);
  assert (kissat_get_score (solver, 5) == 1e30);
  assert (keys->term[5] != before);
  check_keys (solver);
  kissat_release (solver);
}

// UCB on VSIDS scores: the counts against brute force.  'expected' holds,
// in the increment's units, the sum of the increments of the bump rounds
// during which each variable was assigned, its interval closed when
// backtracking unassigns it, or when stable mode is left.

static void bump_round (kissat *solver, double *expected,
                        const bool *assigned, unsigned vars) {
  const double inc = solver->scinc;
  for (unsigned idx = 0; idx < vars; idx++)
    if (assigned[idx])
      expected[idx] += inc;
  PUSH_STACK (solver->analyzed, 0);
  kissat_bump_analyzed (solver);
  CLEAR_STACK (solver->analyzed);
}

static void check_counts (kissat *solver, const double *expected,
                          const bool *closed, unsigned vars) {
  const double *const count = solver->policy.keys.count;
  for (unsigned idx = 0; idx < vars; idx++)
    if (closed[idx])
      assert (close (count[idx], expected[idx]));
}

static void test_keys_ucb_vsids (void) {
  enum { vars = 8 };
  kissat *solver = new_solver (vars, "ucb", 1, "ucbc", 1000);
  const keys *const keys = &solver->policy.keys;
  assert (keys->total == 0), assert (keys->scale == 0);
  double expected[vars] = {0};
  bool assigned[vars] = {0}, closed[vars] = {0};
  kissat_internal_assume (solver, LIT (1)), assigned[1] = true;
  kissat_internal_assume (solver, LIT (2)), assigned[2] = true;
  bump_round (solver, expected, assigned, vars);
  kissat_internal_assume (solver, LIT (3)), assigned[3] = true;
  bump_round (solver, expected, assigned, vars);
  bump_round (solver, expected, assigned, vars);
  kissat_backtrack_without_updating_phases (solver, 1);
  assigned[2] = assigned[3] = false, closed[2] = closed[3] = true;
  check_counts (solver, expected, closed, vars);
  assert (!keys->count[1]);
  // A rescale, here forced, multiplies counts and increments with the
  // scores, in the middle of the interval of variable 1.
  const double inc = solver->scinc;
  kissat_rescale_scores (solver);
  const double factor = solver->scinc / inc;
  assert (factor < 1);
  for (unsigned idx = 0; idx < vars; idx++)
    expected[idx] *= factor;
  check_counts (solver, expected, closed, vars);
  kissat_internal_assume (solver, LIT (4)), assigned[4] = true;
  bump_round (solver, expected, assigned, vars);
  // Warm-up and inprocessing span no bump round: nothing to add.
  kissat_internal_assume (solver, LIT (5));
  kissat_backtrack_without_updating_phases (solver, 2);
  closed[5] = true;
  check_counts (solver, expected, closed, vars);
  // Leaving stable mode closes the intervals of 1 and 4.
  kissat_leave_stable_keys (solver);
  closed[1] = closed[4] = true;
  check_counts (solver, expected, closed, vars);
  solver->stable = false;
  kissat_backtrack_without_updating_phases (solver, 0);
  assigned[1] = assigned[4] = false;
  for (unsigned idx = 0; idx < vars; idx++)
    assert (!VALUE (LIT (idx)));
  check_counts (solver, expected, closed, vars);
  // Entering stable mode is a draw point: the sum and every term.
  solver->stable = true;
  const uint64_t draws = keys->draws;
  kissat_update_scores (solver);
  assert (keys->draws == draws + 1);
  double total = 0;
  for (unsigned idx = 0; idx < vars; idx++)
    total += expected[idx];
  total /= solver->scinc;
  assert (close (keys->total, total));
  assert (total > 1);
  assert (close (keys->scale, sqrt (log (total))));
  for (unsigned idx = 0; idx < vars; idx++) {
    const double n = keys->count[idx] / solver->scinc;
    assert (close (keys->term[idx], exp (keys->scale / sqrt (1 + n))));
  }
  check_keys (solver);
  // Unassignment recomputes a variable's term from its new count.
  kissat_internal_assume (solver, LIT (6)), assigned[6] = true;
  bump_round (solver, expected, assigned, vars);
  kissat_backtrack_without_updating_phases (solver, 0);
  closed[6] = true;
  check_counts (solver, expected, closed, vars);
  const double n6 = keys->count[6] / solver->scinc;
  assert (close (keys->term[6], exp (keys->scale / sqrt (1 + n6))));
  check_keys (solver);
  kissat_release (solver);
}

// UCB and TS on CHB scores: a payment adds the counts' increment, which
// grows by 1/d after the payments of every conflict.  UCB recomputes a
// term at unassignment, TS at the payment, and the leaf of a paid variable
// lags until backtracking unassigns it.

static void push (kissat *solver, unsigned idx) {
  const unsigned lit = LIT (idx);
  solver->values[lit] = 1;
  solver->values[NOT (lit)] = -1;
  solver->assigned[idx].trail = SIZE_ARRAY (solver->trail);
  PUSH_ARRAY (solver->trail, lit);
}

static void shrink (kissat *solver, unsigned size) {
  while (SIZE_ARRAY (solver->trail) > size) {
    const unsigned lit = *--solver->trail.end;
    solver->values[lit] = solver->values[NOT (lit)] = 0;
    kissat_policy_unassign (solver, IDX (lit));
  }
  kissat_policy_shrink_trail (solver, size);
}

static void test_keys_chb_counts (bool thompson) {
  kissat *solver = kissat_init ();
  kissat_set_option (solver, "chb", 1);
  kissat_set_option (solver, thompson ? "thompson" : "ucb", 1);
  kissat_set_option (solver, thompson ? "thompsonkappa" : "ucbc", 700);
  start_solver (solver, 6);
  const keys *const keys = &solver->policy.keys;
  const tree *const tree = &solver->policy.tree;
  double expected[6] = {0}, inc = 1;
  const double growth = 1 / 0.95;
  push (solver, 0), push (solver, 1);
  kissat_chb_assign (solver, false);
  expected[0] += inc, expected[1] += inc;
  push (solver, 2);
  kissat_chb_assign (solver, true);
  expected[2] += inc, inc *= growth;
  kissat_chb_assign (solver, true);
  inc *= growth;
  push (solver, 3);
  kissat_chb_assign (solver, false);
  expected[3] += inc;
  assert (close (keys->increment, inc));
  for (unsigned idx = 0; idx < 6; idx++)
    assert (close (keys->count[idx], expected[idx]));
  // Each of 0 to 3 was paid once, so TS's term saw a count of one, in the
  // units of its payment, and the leaves of all four lag.
  for (unsigned idx = 0; idx < 6; idx++) {
    const double n = idx < 4;
    if (thompson)
      assert (close (keys->term[idx],
                     keys->factor * keys->normal[idx] / sqrt (1 + n)));
    if (n)
      assert (kissat_tree_key (tree, idx) !=
              kissat_policy_key (solver, idx));
  }
  // Backtracking refreshes the leaves.
  shrink (solver, 0);
  check_keys (solver);
  // A restart: UCB's sum and scale, and TS's draw.
  kissat_restart_keys (solver);
  if (!thompson) {
    double total = 0;
    for (unsigned idx = 0; idx < 6; idx++)
      total += expected[idx];
    total /= inc;
    assert (close (keys->total, total));
    assert (keys->scale > 0);
    assert (close (keys->scale, 0.7 * sqrt (log (total))));
  }
  for (unsigned idx = 0; idx < 6; idx++)
    push (solver, idx == 0 ? 4 : idx == 4 ? 0 : idx);
  kissat_chb_assign (solver, false);
  shrink (solver, 0);
  for (unsigned idx = 0; idx < 6; idx++) {
    const double n = keys->count[idx] / keys->increment;
    if (thompson)
      assert (close (keys->term[idx],
                     keys->factor * keys->normal[idx] / sqrt (1 + n)));
    else
      assert (same (keys->term[idx], keys->scale / sqrt (1 + n)));
    assert (same (kissat_tree_key (tree, idx),
                  kissat_get_score (solver, idx) + keys->term[idx]));
  }
  check_keys (solver);
  kissat_release (solver);
}

static void test_keys_chb_ucb (void) { test_keys_chb_counts (false); }
static void test_keys_chb_thompson (void) { test_keys_chb_counts (true); }

// Draw points: P1 and TS draw at restarts, or with 'redraw=1' at rephases,
// UCB recomputes at restarts whatever 'redraw' says, and all three at
// every entry to stable mode.

static void check_draw_points (const char *name, const char *factor,
                               bool redraw, unsigned restart,
                               unsigned rephase) {
  kissat *solver = kissat_init ();
  kissat_set_option (solver, name, 1);
  kissat_set_option (solver, "redraw", redraw);
  if (factor)
    kissat_set_option (solver, factor, 500);
  start_solver (solver, 6);
  const keys *const keys = &solver->policy.keys;
  assert (keys->draws == 1);
  const double term = keys->term[3];
  kissat_restart_keys (solver);
  assert (keys->draws == 1 + restart);
  assert ((keys->term[3] != term) == (restart && keys->kind != KEYS_UCB));
  kissat_rephase_keys (solver);
  assert (keys->draws == 1 + restart + rephase);
  kissat_update_scores (solver);
  assert (keys->draws == 2 + restart + rephase);
  check_keys (solver);
  kissat_release (solver);
}

static void test_keys_draw_points (void) {
  check_draw_points ("perturbed", 0, false, 1, 0);
  check_draw_points ("perturbed", 0, true, 0, 1);
  check_draw_points ("thompson", "thompsonkappa", false, 1, 0);
  check_draw_points ("thompson", "thompsonkappa", true, 0, 1);
  check_draw_points ("ucb", "ucbc", false, 1, 0);
  check_draw_points ("ucb", "ucbc", true, 1, 0);
}

// Without the pseudo-activity the first variable has score zero, hence key
// zero.  Once every other variable is assigned it is picked, as Argmax's
// choice, and counted as a fallback.  On CHB scores there is none.

static void check_fallback (const char *name, const char *factor,
                            int value) {
  kissat *solver = kissat_init ();
  kissat_set_option (solver, "pseudoactivity", 0);
  kissat_set_option (solver, name, 1);
  kissat_set_option (solver, factor, value);
  start_solver (solver, 4);
  assert (!kissat_get_score (solver, 0));
  assert (!kissat_tree_key (&solver->policy.tree, 0));
  for (unsigned idx = 1; idx < 4; idx++)
    kissat_internal_assume (solver, LIT (idx));
  assert (kissat_policy_pick (solver) == 0);
  assert (solver->policy.count.fallbacks[0] == 1);
  kissat_backtrack_without_updating_phases (solver, 1);
  assert (kissat_policy_pick (solver) != 0);
  assert (solver->policy.count.fallbacks[0] == 1);
  kissat_release (solver);
}

static void test_keys_fallback (void) {
  check_fallback ("perturbed", "etalog2", 4);
  check_fallback ("thompson", "thompsonkappa", 500);
  check_fallback ("ucb", "ucbc", 500);
  kissat *solver = kissat_init ();
  kissat_set_option (solver, "chb", 1);
  kissat_set_option (solver, "ucb", 1);
  start_solver (solver, 4);
  for (unsigned idx = 1; idx < 4; idx++)
    assign (solver, idx);
  assert (kissat_policy_pick (solver) == 0);
  assert (!solver->policy.count.fallbacks[0]);
  kissat_release (solver);
}

// A variable activated in stable mode draws its own (P1, TS) or gets its
// term (UCB) before its leaf is set.

static void test_keys_activation (void) {
  const char *names[3] = {"perturbed", "thompson", "ucb"};
  for (unsigned i = 0; i < 3; i++) {
    kissat *solver = new_solver (6, names[i], 1, 0, 0);
    keys *const keys = &solver->policy.keys;
    kissat_policy_deactivate (solver, 4);
    assert (!kissat_tree_contains (&solver->policy.tree, 4));
    keys->term[4] = 0;
    kissat_policy_activate (solver, 4);
    assert (keys->term[4] > 0);
    assert (kissat_tree_contains (&solver->policy.tree, 4));
    check_keys (solver);
    kissat_release (solver);
  }
}

#ifdef DECISION_METRICS

// Given its draws a pick is a point mass on its choice: no entropy, one
// effective arm, and 'differ' and 'lower' whether the pick is another
// variable than Argmax's choice, and of a lower score.

static void test_keys_metrics (void) {
  kissat *solver = new_solver (8, "perturbed", 1, "etalog2", 1);
  kissat_set_option (solver, "metricsint", 1);
  kissat_set_option (solver, "metricsvars", 0);
  const double scores[8] = {3, 1, 4, 1, 5, 5, 2, 0.5};
  for (unsigned idx = 0; idx < 8; idx++)
    kissat_update_score (solver, idx, scores[idx]);
  assign (solver, 0), assign (solver, 2);
  const unsigned decisions = 2000;
  unsigned differed = 0, lowered = 0;
  for (unsigned i = 0; i < decisions; i++) {
    kissat_draw_keys (solver);
    const unsigned idx = kissat_next_decision_variable (solver);
    differed += idx != 4;
    lowered += scores[idx] < 5;
  }
  assert (differed > lowered), assert (lowered > 0);
  const policy_metrics *const m = solver->policy.metrics;
  assert (m->samples == decisions);
  assert (m->entropy == 0), assert (m->effective == decisions);
  assert (m->differ == differed), assert (m->differed == differed);
  assert (m->lower == lowered), assert (m->lowered == lowered);
  assert (m->arms == 6.0 * decisions);
  kissat_release (solver);
}

#endif

#endif

void tissat_schedule_keys (void) {
#if !defined(HEAPARGMAX) && !defined(NOPTIONS)
  SCHEDULE_FUNCTION (test_keys_options);
  SCHEDULE_FUNCTION (test_keys_start);
  SCHEDULE_FUNCTION (test_keys_zero_noise);
  SCHEDULE_FUNCTION (test_keys_perturbed);
  SCHEDULE_FUNCTION (test_keys_draws);
  SCHEDULE_FUNCTION (test_keys_thompson);
  SCHEDULE_FUNCTION (test_keys_ucb_vsids);
  SCHEDULE_FUNCTION (test_keys_chb_ucb);
  SCHEDULE_FUNCTION (test_keys_chb_thompson);
  SCHEDULE_FUNCTION (test_keys_draw_points);
  SCHEDULE_FUNCTION (test_keys_fallback);
  SCHEDULE_FUNCTION (test_keys_activation);
#ifdef DECISION_METRICS
  SCHEDULE_FUNCTION (test_keys_metrics);
#endif
#endif
}
