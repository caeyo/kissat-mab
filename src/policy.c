#include "policy.h"
#include "inlinepolicy.h"
#include "logging.h"
#include "print.h"
#include "resources.h"

#include <inttypes.h>

void kissat_print_estimator_statistics (kissat *solver) {
#ifndef QUIET
  const estimator *const estimator = &solver->estimator;
  kissat_message (solver, "estimator-bump-rounds %" PRIu64,
                  estimator->rounds);
  kissat_message (solver, "estimator-rescales %" PRIu64,
                  estimator->rescales);
  kissat_message (solver, "estimator-pseudo-activity %.17g",
                  estimator->pseudo);
  kissat_message (solver, "estimator-pseudo-zero-round %" PRIu64,
                  estimator->zero.round);
  kissat_message (solver, "estimator-pseudo-zero-rescale %" PRIu64,
                  estimator->zero.rescale);
#ifndef HEAPARGMAX
  if (kissat_chb (solver)) {
    kissat_message (solver, "estimator-chb-conflicts %" PRIu64,
                    estimator->chb.conflicts);
    kissat_message (solver, "estimator-chb-analyzed %" PRIu64,
                    estimator->chb.analyzed);
    kissat_message (solver, "estimator-chb-plays %" PRIu64,
                    estimator->chb.plays);
    kissat_message (solver, "estimator-chb-alpha %.17g",
                    kissat_chb_alpha (estimator->chb.conflicts));
  }
#endif
#else
  (void) solver;
#endif
}

#ifdef HEAPARGMAX

static unsigned heap_argmax_pick (kissat *solver) {
  heap *scores = SCORES;
  unsigned res = kissat_max_heap (scores);
  const value *const values = solver->values;
  while (values[LIT (res)]) {
    kissat_pop_max_heap (solver, scores);
    res = kissat_max_heap (scores);
  }
#if defined(LOGGING) || defined(CHECK_HEAP)
  const double score = kissat_get_heap_score (scores, res);
#endif
  LOG ("largest score unassigned %s score %g", LOGVAR (res), score);
#ifdef CHECK_HEAP
  for (all_variables (idx)) {
    if (!ACTIVE (idx))
      continue;
    if (VALUE (LIT (idx)))
      continue;
    const double idx_score = kissat_get_heap_score (scores, idx);
    assert (score >= idx_score);
  }
#endif
  return res;
}

unsigned kissat_policy_pick (kissat *solver) {
  assert (solver->stable);
  assert (solver->unassigned);
  return heap_argmax_pick (solver);
}

unsigned kissat_policy_peek (kissat *solver) {
  assert (solver->stable);
  assert (solver->unassigned);
  return heap_argmax_pick (solver);
}

void kissat_update_scores (kissat *solver) {
  assert (solver->stable);
  heap *scores = SCORES;
  for (all_variables (idx))
    if (ACTIVE (idx) && !kissat_heap_contains (scores, idx))
      kissat_push_heap (solver, scores, idx);
}

#else

#include "error.h"

// Argmax: the tree's maximum, removing assigned variables from the tree
// on the way.  Each assigned variable is removed at most once per
// assignment and put back when backtracking unassigns it.

static unsigned tree_argmax_pick (kissat *solver) {
  tree *const tree = &solver->policy.tree;
  const value *const values = solver->values;
  unsigned res = kissat_tree_max (tree);
  assert (res != INVALID_IDX);
  while (values[LIT (res)]) {
    kissat_tree_remove (tree, res);
    res = kissat_tree_max (tree);
    assert (res != INVALID_IDX);
  }
#if defined(LOGGING) || defined(CHECK_HEAP)
  const double score = kissat_tree_key (tree, res);
#endif
  LOG ("largest score unassigned %s score %g", LOGVAR (res), score);
#ifdef CHECK_HEAP
  // Brute-force check of the argmax and of its tie-breaking ('--check-heap'
  // checks the policy structure of tree builds too).
  for (all_variables (idx)) {
    if (!ACTIVE (idx))
      continue;
    if (VALUE (LIT (idx)))
      continue;
    const double idx_score = kissat_get_score (solver, idx);
    if (idx < res)
      assert (score > idx_score);
    else
      assert (score >= idx_score);
  }
#endif
  return res;
}

// Sample: draws from the tree's weights with the policy's generator, and
// removes every assigned variable a draw meets and draws again.  Once no
// leaf with a positive weight is left, every unassigned variable has score
// zero, and the pick falls back to Argmax's choice.

static unsigned tree_sample_pick (kissat *solver) {
  policy *const policy = &solver->policy;
  tree *const tree = &policy->tree;
  const value *const values = solver->values;
  assert (tree->weighted);
  while (kissat_tree_has_weight (tree)) {
    const unsigned res = kissat_tree_draw (tree, &policy->random);
    assert (kissat_tree_contains (tree, res));
    if (!values[LIT (res)]) {
      LOG ("sampled unassigned %s score %g", LOGVAR (res),
           kissat_tree_key (tree, res));
#ifdef CHECK_HEAP
      assert (kissat_tree_weight (tree, res).mantissa > 0);
#endif
      return res;
    }
    kissat_tree_remove (tree, res);
  }
  if (!(policy->count.fallbacks[0] | policy->count.fallbacks[1]))
    policy->count.first = solver->estimator.rounds;
  policy->count.fallbacks[solver->warming]++;
  LOG ("no positive weight left: falling back to the maximum");
#ifdef CHECK_HEAP
  for (all_variables (idx))
    if (ACTIVE (idx) && !VALUE (LIT (idx)))
      assert (!kissat_get_score (solver, idx));
#endif
  return tree_argmax_pick (solver);
}

#ifdef SHADOW

static void shadow_check_tree (kissat *);

// Under Argmax, HeapArgmax's pick on the shadow heap must find the largest
// score the tree finds.  The two may pick different variables of that
// score, since the heap breaks ties by its history and the tree by
// variable index.  Under Sample the pick is not the maximum, and only the
// complete checks run.

static void shadow_pick (kissat *solver, unsigned res) {
  policy *const policy = &solver->policy;
  const uint64_t pick = ++policy->shadow.picks;
  if (!policy->tree.weighted) {
    heap *const scores = SCORES;
    const value *const values = solver->values;
    policy->shadow.compared++;
    if (kissat_empty_heap (scores))
      kissat_fatal ("shadow mode: heap empty at pick %" PRIu64, pick);
    unsigned top = kissat_max_heap (scores);
    while (values[LIT (top)]) {
      kissat_pop_max_heap (solver, scores);
      if (kissat_empty_heap (scores))
        kissat_fatal ("shadow mode: heap empty at pick %" PRIu64, pick);
      top = kissat_max_heap (scores);
    }
    const double heap_score = kissat_get_heap_score (scores, top);
    const double tree_score = kissat_tree_max_key (&policy->tree);
    if (!kissat_same_double (heap_score, tree_score))
      kissat_fatal ("shadow mode: pick %" PRIu64 ": largest score on the "
                    "heap %.17g (variable %u) differs from the largest in "
                    "the tree %.17g (variable %u)",
                    pick, heap_score, top, tree_score, res);
    if (!kissat_same_double (tree_score, solver->score[res]))
      kissat_fatal ("shadow mode: pick %" PRIu64 ": tree maximum %.17g "
                    "differs from the score %.17g of its variable %u",
                    pick, tree_score, solver->score[res], res);
    if (top != res)
      policy->shadow.differ++;
  }
  if (!(pick % 1000))
    shadow_check_tree (solver);
}

// Every leaf against the estimator, the heap and the assignment; every
// internal node against its children.  In a weighted tree every leaf's
// weight must be the one its score gives, and an absent leaf's zero.

static void shadow_check_tree (kissat *solver) {
  policy *const policy = &solver->policy;
  const tree *const tree = &policy->tree;
  heap *const scores = SCORES;
  const double *const score = solver->score;
  const flags *const flags = solver->flags;
  const value *const values = solver->values;
  const uint64_t check = ++policy->shadow.checks;
  const uint64_t pick = policy->shadow.picks;
  if (policy->bulk)
    kissat_fatal ("shadow mode: check %" PRIu64 " during a bulk change",
                  check);
  const unsigned leaves = tree->leaves;
  if (leaves < VARS)
    kissat_fatal ("shadow mode: check %" PRIu64 ": %u leaves for %u "
                  "variables",
                  check, leaves, VARS);
  for (all_variables (idx)) {
    const double s = score[idx];
    const double h = kissat_get_heap_score (scores, idx);
    if (!kissat_same_double (s, h))
      kissat_fatal ("shadow mode: pick %" PRIu64 ": score %.17g of "
                    "variable %u differs from its heap score %.17g",
                    pick, s, idx, h);
    const bool active = flags[idx].active;
    const bool available = active && !values[LIT (idx)];
    if (kissat_tree_contains (tree, idx)) {
      if (!active)
        kissat_fatal ("shadow mode: pick %" PRIu64 ": inactive variable "
                      "%u in the tree",
                      pick, idx);
      const double k = kissat_tree_key (tree, idx);
      if (!kissat_same_double (k, s))
        kissat_fatal ("shadow mode: pick %" PRIu64 ": leaf key %.17g of "
                      "variable %u differs from its score %.17g",
                      pick, k, idx, s);
      if (tree->weighted) {
        const tree_weight w = kissat_tree_weight (tree, idx);
        const tree_weight e = kissat_tree_weight_of_log2 (
            kissat_policy_log2_weight (policy, s));
        if (!kissat_tree_same_weight (w, e))
          kissat_fatal ("shadow mode: pick %" PRIu64 ": leaf weight "
                        "%.17g * 2^%d of variable %u differs from "
                        "%.17g * 2^%d given by its score %.17g",
                        pick, w.mantissa, w.exponent, idx, e.mantissa,
                        e.exponent, s);
      }
    } else if (available)
      kissat_fatal ("shadow mode: pick %" PRIu64 ": unassigned active "
                    "variable %u missing from the tree",
                    pick, idx);
    if (available && !kissat_heap_contains (scores, idx))
      kissat_fatal ("shadow mode: pick %" PRIu64 ": unassigned active "
                    "variable %u missing from the heap",
                    pick, idx);
  }
  for (unsigned idx = 0; idx < leaves; idx++) {
    const bool present = kissat_tree_contains (tree, idx);
    if (idx >= VARS && present)
      kissat_fatal ("shadow mode: pick %" PRIu64 ": leaf %u beyond the "
                    "%u variables present",
                    pick, idx, VARS);
    if (tree->weighted && !present &&
        kissat_tree_weight (tree, idx).mantissa)
      kissat_fatal ("shadow mode: pick %" PRIu64 ": absent leaf %u with "
                    "a positive weight",
                    pick, idx);
  }
  const unsigned node = kissat_tree_inconsistent_node (tree);
  if (node)
    kissat_fatal ("shadow mode: pick %" PRIu64 ": tree node %u differs "
                  "from what its children give",
                  pick, node);
}

void kissat_print_shadow_statistics (kissat *solver) {
#ifndef QUIET
  const policy *const policy = &solver->policy;
  kissat_message (solver, "shadow-picks %" PRIu64, policy->shadow.picks);
  kissat_message (solver, "shadow-compared %" PRIu64,
                  policy->shadow.compared);
  kissat_message (solver, "shadow-differ %" PRIu64, policy->shadow.differ);
  kissat_message (solver, "shadow-checks %" PRIu64, policy->shadow.checks);
  kissat_message (solver, "shadow-rebuilds %" PRIu64,
                  policy->shadow.rebuilds);
#else
  (void) solver;
#endif
}

#endif

unsigned kissat_policy_pick (kissat *solver) {
  assert (solver->stable);
  assert (solver->unassigned);
  policy *const policy = &solver->policy;
  assert (!policy->bulk);
  policy->count.picks[solver->warming]++;
  const unsigned res = policy->tree.weighted ? tree_sample_pick (solver)
                                             : tree_argmax_pick (solver);
#ifdef SHADOW
  shadow_pick (solver, res);
#endif
  assert (ACTIVE (res));
  assert (!VALUE (LIT (res)));
  return res;
}

unsigned kissat_policy_peek (kissat *solver) {
  assert (solver->stable);
  assert (solver->unassigned);
  assert (!solver->policy.bulk);
  const unsigned res = tree_argmax_pick (solver);
  assert (ACTIVE (res));
  assert (!VALUE (LIT (res)));
  return res;
}

// Every active variable becomes available.  The heap's order of pushes
// does not matter to the tree, which is a function of its leaves.

void kissat_update_scores (kissat *solver) {
  assert (solver->stable);
#ifdef SHADOW
  heap *scores = SCORES;
  for (all_variables (idx))
    if (ACTIVE (idx) && !kissat_heap_contains (scores, idx))
      kissat_push_heap (solver, scores, idx);
#endif
  tree *const tree = &solver->policy.tree;
  bool added = false;
  for (all_variables (idx))
    if (ACTIVE (idx) && !kissat_tree_contains (tree, idx)) {
      kissat_policy_put_leaf (solver, idx);
      added = true;
    }
  if (added)
    kissat_rebuild_policy (solver);
}

// Present leaves take their keys and weights from the estimator again,
// then every internal node is recomputed.

void kissat_rebuild_policy (kissat *solver) {
  tree *const tree = &solver->policy.tree;
  LOG ("rebuilding policy tree");
  for (all_variables (idx))
    if (kissat_tree_contains (tree, idx))
      kissat_policy_put_leaf (solver, idx);
  kissat_rebuild_tree (tree);
#ifdef SHADOW
  solver->policy.shadow.rebuilds++;
#endif
}

// Decision metrics (see 'policy.h').  A sample is one pass over the
// variables at a decision of 'idx', due for a sample, which finds Argmax's
// choice among the unassigned active variables (the largest score, the
// smallest index among ties) and the distribution the decision was drawn
// from.  Sample's weights enter relative to the largest one seen so far,
// as 2^(l - top) with 'l' a weight's base-2 logarithm: 'sum' adds them and
// 'moment' adds each times 'l - top', both rescaled whenever 'top' grows.
// The softmax's entropy is then ln (sum) - ln (2) * moment / sum, the
// variable of largest weight has probability 1 / sum, and the 'ties'
// variables of the largest score, which share that weight, 'ties / sum'.

void kissat_sample_decision (kissat *solver, unsigned idx, bool random) {
  policy *const policy = &solver->policy;
  policy_metrics *const metrics = policy->metrics + solver->warming;
  const uint64_t start = kissat_policy_clock ();
  const bool softmax = !random && policy->tree.weighted;
  const flags *const flags = solver->flags;
  const value *const values = solver->values;
  const double *const score = solver->score;
  unsigned arms = 0, ties = 0, argmax = INVALID_IDX;
  double largest = -1, top = 0, sum = 0, moment = 0;
  for (all_variables (other)) {
    if (!flags[other].active || values[LIT (other)])
      continue;
    arms++;
    const double s = score[other];
    if (s > largest)
      largest = s, argmax = other, ties = 1;
    else if (s == largest)
      ties++;
    if (!softmax)
      continue;
    const double l = kissat_policy_log2_weight (policy, s);
    if (l == -INFINITY)
      continue;
    if (!sum)
      top = l, sum = 1;
    else if (l > top) {
      const double d = top - l, f = exp2 (d);
      moment = f * (moment + d * sum);
      sum = f * sum + 1;
      top = l;
    } else {
      const double d = l - top, f = exp2 (d);
      sum += f;
      moment += f * d;
    }
  }
  assert (arms == solver->unassigned);
  assert (argmax != INVALID_IDX);
  assert (ACTIVE (idx) && !VALUE (LIT (idx)));
  // Argmax's distribution, and Sample's at a fallback (no positive weight
  // left), put all mass on Argmax's choice, and the decision is that.
  double entropy = 0, differ = 0, lower = 0;
  if (random) {
    entropy = log (arms);
    differ = 1 - 1.0 / arms;
    lower = 1 - (double) ties / arms;
  } else if (softmax && sum) {
    const double ln2 = 0.69314718055994530942;
    entropy = log (sum) - ln2 * moment / sum;
    differ = 1 - 1 / sum;
    lower = 1 - ties / sum;
  } else
    assert (idx == argmax);
  if (entropy < 0) // rounding
    entropy = 0;
  const double effective = exp (entropy);
  LOG ("sampled decision %s: %u unassigned, %g effective arms", LOGVAR (idx),
       arms, effective);
  metrics->samples++;
  metrics->arms += arms;
  metrics->entropy += entropy;
  metrics->effective += effective;
  metrics->share += effective / arms;
  metrics->differ += differ;
  metrics->lower += lower;
  metrics->differed += idx != argmax;
  metrics->lowered += score[idx] < largest;
  const uint64_t stop = kissat_policy_clock ();
  if (stop > start)
    policy->clock.ticks += stop - start;
}

#ifndef QUIET

// Clock ticks per second, measured against the wall clock since the start
// of the search; zero if the search has not started.

static double policy_clock_rate (kissat *solver) {
  const policy *const policy = &solver->policy;
  if (!policy->clock.started)
    return 0;
  const double seconds = kissat_wall_clock_time () - policy->clock.started;
  if (seconds <= 0)
    return 0;
  return (kissat_policy_clock () - policy->clock.start) / seconds;
}

#endif

// Seeds the generator and fixes the policy.  Sample weighs the tree, which
// at this point may already hold variables ('kissat_update_scores' with
// '--stable=2').  The clock of the decision metrics starts here.

void kissat_start_policy (kissat *solver) {
  policy *const policy = &solver->policy;
  policy->clock.start = kissat_policy_clock ();
  policy->clock.started = kissat_wall_clock_time ();
  const unsigned seed = GET_OPTION (policyseed);
  policy->random = kissat_policy_generator (seed);
  LOG ("initialized policy random number generator with seed %u", seed);
  if (kissat_chb (solver))
    kissat_very_verbose (solver, "CHB scores in stable mode");
  if (!GET_OPTION (softmax) || policy->tree.weighted)
    return;
  policy->chb = kissat_chb (solver);
  policy->etalog2 = GET_OPTION (etalog2);
  kissat_weigh_tree (solver, &policy->tree);
  kissat_rebuild_policy (solver);
  kissat_very_verbose (solver, "sampling decisions at eta 2^%d",
                       policy->etalog2);
}

void kissat_print_policy_statistics (kissat *solver) {
#ifndef QUIET
  const policy *const policy = &solver->policy;
  kissat_message (solver, "policy-picks %" PRIu64, policy->count.picks[0]);
  kissat_message (solver, "policy-fallbacks %" PRIu64,
                  policy->count.fallbacks[0]);
  kissat_message (solver, "policy-warmup-picks %" PRIu64,
                  policy->count.picks[1]);
  kissat_message (solver, "policy-warmup-fallbacks %" PRIu64,
                  policy->count.fallbacks[1]);
  if (policy->count.fallbacks[0] | policy->count.fallbacks[1])
    kissat_message (solver, "policy-first-fallback-round %" PRIu64,
                    policy->count.first);
  // Decision metrics: means per decision and per sample.
  const double hz = policy_clock_rate (solver);
  kissat_message (solver, "policy-random-decisions %" PRIu64,
                  policy->metrics[0].random);
  for (unsigned warming = 0; warming < 2; warming++) {
    const policy_metrics *const m = policy->metrics + warming;
    const char *const phase = warming ? "policy-warmup" : "policy";
    const double n = m->samples;
    kissat_message (solver, "%s-decision-ns %.9g", phase,
                    hz && m->decisions ? 1e9 * m->ticks / hz / m->decisions
                                       : 0);
    kissat_message (solver, "%s-samples %" PRIu64, phase, m->samples);
    kissat_message (solver, "%s-unassigned %.9g", phase,
                    n ? m->arms / n : 0);
    kissat_message (solver, "%s-effective-arms %.9g", phase,
                    n ? m->effective / n : 0);
    kissat_message (solver, "%s-effective-arms-geomean %.9g", phase,
                    n ? exp (m->entropy / n) : 0);
    kissat_message (solver, "%s-effective-share %.9g", phase,
                    n ? m->share / n : 0);
    kissat_message (solver, "%s-differ %.9g", phase, n ? m->differ / n : 0);
    kissat_message (solver, "%s-differ-observed %" PRIu64, phase,
                    m->differed);
    kissat_message (solver, "%s-lower %.9g", phase, n ? m->lower / n : 0);
    kissat_message (solver, "%s-lower-observed %" PRIu64, phase,
                    m->lowered);
  }
  kissat_message (solver, "policy-metrics-seconds %.9g",
                  hz ? policy->clock.ticks / hz : 0);
  kissat_message (solver, "policy-clock-hz %.9g", hz);
#else
  (void) solver;
#endif
}

#endif
