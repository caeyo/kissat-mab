#include "../src/analyze.h"
#include "../src/backtrack.h"
#include "../src/bump.h"
#include "../src/chb.h"
#include "../src/decide.h"
#include "../src/error.h"
#include "../src/inlinepolicy.h"
#include "../src/propsearch.h"
#include "../src/reorder.h"

#include "test.h"

#include <math.h>
#include <setjmp.h>

#if !defined(HEAPARGMAX) && !defined(NOPTIONS)

// Phase 4's reward (see 'reward.h'): the options it excludes, who starts
// it, the channel weighting's bumps by class and at w = 1 Kissat's bump,
// locality's lazy values against the eager ones on a small trail, a
// rescale with g, 'reorder's weight under locality, the interval reward's
// closes, and the weighting and locality on LRB's estimator.

static jmp_buf jump_buffer;

static void abort_call_back (void) { longjmp (jump_buffer, 42); }

// Whether the start of the search is a fatal error with the options
// 'names' set to 'values' (up to three, ended by a null name).

static bool start_fails (const char *const *names, const int *values) {
  kissat *solver = kissat_init ();
  for (unsigned i = 0; names[i]; i++)
    kissat_set_option (solver, names[i], values[i]);
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

static bool fails1 (const char *a, int x) {
  const char *names[] = {a, 0};
  const int values[] = {x};
  return start_fails (names, values);
}

static bool fails2 (const char *a, int x, const char *b, int y) {
  const char *names[] = {a, b, 0};
  const int values[] = {x, y};
  return start_fails (names, values);
}

static bool fails3 (const char *a, int x, const char *b, int y,
                    const char *c, int z) {
  const char *names[] = {a, b, c, 0};
  const int values[] = {x, y, z};
  return start_fails (names, values);
}

// The reward decides by Argmax; 'wimp' and 'locality' need VSIDS scores
// or LRB's estimator, 'intervalreward' VSIDS scores; feedback builds refuse
// every component.  'localitydecay' alone starts nothing.

static void test_reward_options (void) {
#ifdef FEEDBACK
  assert (fails1 ("wimp", 250));
  assert (fails2 ("locality", 1, "localitydecay", 500));
  assert (fails1 ("intervalreward", 1));
  assert (fails3 ("chb", 1, "lrb", 1, "locality", 1));
  assert (!fails1 ("localitydecay", 500));
  assert (!fails1 ("wimp", 1000));
#else
  const char *components[] = {"wimp", "locality", "intervalreward"};
  const int on[] = {250, 1, 1};
  const char *policies[] = {"softmax", "perturbed", "thompson", "ucb",
                            "gammappm"};
  for (unsigned i = 0; i < 3; i++) {
    assert (!fails1 (components[i], on[i]));
    assert (!fails2 (components[i], on[i], "randecstable", 1));
    for (unsigned j = 0; j < 5; j++)
      assert (fails2 (components[i], on[i], policies[j], 1));
  }
  assert (fails2 ("chb", 1, "wimp", 250));
  assert (fails2 ("chb", 1, "locality", 1));
  assert (fails2 ("chb", 1, "intervalreward", 1));
  assert (fails3 ("chb", 1, "lrb", 1, "intervalreward", 1));
  assert (!fails3 ("chb", 1, "lrb", 1, "wimp", 250));
  assert (!fails3 ("chb", 1, "lrb", 1, "locality", 1));
  assert (!fails2 ("wimp", 0, "locality", 1));
  assert (!fails2 ("wimp", 1000000, "intervalreward", 1));
  assert (!fails1 ("localitydecay", 500));
  assert (!fails2 ("chb", 1, "localitydecay", 500));
#endif
}

// A solver in stable mode over
//
//   (-1 -2 3) (-1 -2 -3) (2 -4 5) (2 -4 -5) (6 7 8 9)
//
// with up to two options set, without on-the-fly strengthening.
// Deciding 1 and 2 propagates 3 and falsifies (-1 -2 -3): the analysis
// learns (-1 -2), backjumps to level 1 and asserts -2.  Deciding 4 then
// propagates 5 and falsifies (2 -4 -5): the analysis learns (2 -4) from
// 2, asserted, 4, decided, and 5, propagated, backjumps to level 1 and
// asserts -4.  Variables are indices: 1 is 0, and so on.

static kissat *new_solver (const char *name, int value, const char *other,
                           int other_value) {
  kissat *solver = kissat_init ();
#ifndef NDEBUG
  kissat_set_option (solver, "check", 0);
#endif
  kissat_set_option (solver, "otfs", 0);
  if (name)
    kissat_set_option (solver, name, value);
  if (other)
    kissat_set_option (solver, other, other_value);
  const int clauses[][5] = {{-1, -2, 3, 0},
                            {-1, -2, -3, 0},
                            {2, -4, 5, 0},
                            {2, -4, -5, 0},
                            {6, 7, 8, 9, 0}};
  for (unsigned i = 0; i < sizeof clauses / sizeof *clauses; i++)
    for (const int *p = clauses[i];; p++) {
      kissat_add (solver, *p);
      if (!*p)
        break;
    }
  solver->stable = true;
  kissat_init_averages (solver, &AVERAGES);
  kissat_update_scores (solver);
  kissat_start_policy (solver);
  return solver;
}

// Who starts what: nothing at default options outside feedback builds;
// each component the reward and the assignment intervals, with LRB's
// interval, the interval reward their k and b, locality the multipliers.

static void test_reward_start (void) {
#ifdef FEEDBACK
  const bool feedback = true;
#else
  const bool feedback = false;
#endif
  kissat *solver = new_solver (0, 0, 0, 0);
  assert (!solver->policy.reward.started);
  assert (solver->policy.intervals.started == feedback);
  assert (!solver->policy.intervals.multiplier);
  kissat_release (solver);
  if (feedback)
    return;
  solver = new_solver ("wimp", 250, 0, 0);
  const reward *reward = &solver->policy.reward;
  const intervals *intervals = &solver->policy.intervals;
  assert (reward->started && reward->weighted && !reward->lrb);
  assert (!reward->locality && !reward->interval);
  assert (reward->wimp == 0.25);
  assert (intervals->started && intervals->interval && intervals->vsids);
  assert (!intervals->reward); // its closes do nothing for the weighting
  assert (!intervals->increments && !intervals->opened);
  assert (!intervals->rounds && !intervals->multiplier);
  kissat_release (solver);
  solver = new_solver ("locality", 1, "localitydecay", 500);
  reward = &solver->policy.reward;
  intervals = &solver->policy.intervals;
  assert (reward->started && reward->locality && !reward->weighted);
  assert (reward->lambda == 0.5 && reward->growth == 2 && reward->g == 1);
  assert (intervals->reward);
  assert (intervals->multiplier && intervals->multiplier[0] == 1);
  kissat_release (solver);
  solver = new_solver ("intervalreward", 1, 0, 0);
  intervals = &solver->policy.intervals;
  assert (solver->policy.reward.interval && intervals->reward);
  assert (intervals->rounds && intervals->start && intervals->bumps);
  kissat_release (solver);
  solver = new_solver ("chb", 1, "lrb", 1);
  assert (!solver->policy.reward.started);
  kissat_release (solver);
}

#ifndef FEEDBACK

// Feedback builds refuse the reward: the helpers and tests below run in
// other builds.

// The two conflicts of 'new_solver', through the solver's own propagation
// and analysis.

static void first_conflict (kissat *solver) {
  kissat_internal_assume (solver, LIT (0));
  assert (!kissat_search_propagate (solver));
  kissat_internal_assume (solver, LIT (1));
  clause *conflict = kissat_search_propagate (solver);
  assert (conflict);
  assert (VALUE (LIT (2)) > 0);
  kissat_analyze (solver, conflict);
  assert (solver->level == 1);
  assert (VALUE (LIT (1)) < 0);
  assert (!VALUE (LIT (2)));
  assert (!kissat_search_propagate (solver));
}

static void second_conflict (kissat *solver) {
  kissat_internal_assume (solver, LIT (3));
  clause *conflict = kissat_search_propagate (solver);
  assert (conflict);
  assert (VALUE (LIT (4)) > 0);
  kissat_analyze (solver, conflict);
  assert (solver->level == 1);
  assert (VALUE (LIT (3)) < 0);
  assert (!VALUE (LIT (4)));
  assert (!kissat_search_propagate (solver));
}

static double score (kissat *solver, unsigned idx) {
  return kissat_get_score (solver, idx);
}

// Kissat's initial score of the k-th activated variable, here the index
// plus one, with the pseudo-activity of the initial increment.

static double initial (unsigned idx) { return 1 - 1.0 / (idx + 1) + 1; }

// A bump round by hand, of 'idx' alone.

static void bump_round (kissat *solver, unsigned idx) {
  PUSH_STACK (solver->analyzed, idx);
  kissat_bump_analyzed (solver);
  CLEAR_STACK (solver->analyzed);
}

// An implied assignment at the current level, with a reason other than
// 'DECISION_REASON', as in 'testintervals.c': propagated, not asserted.

static void imply (kissat *solver, unsigned idx) {
  const unsigned lit = LIT (idx);
  assert (!VALUE (lit));
  solver->values[lit] = 1;
  solver->values[NOT (lit)] = -1;
  assert (solver->unassigned);
  solver->unassigned--;
  assigned *const a = solver->assigned + idx;
  a->level = solver->level;
  a->trail = SIZE_ARRAY (solver->trail);
  a->binary = false;
  a->reason = 0;
  PUSH_ARRAY (solver->trail, lit);
}

// A step by hand: one bump round, bracketed as an analysis step.

static void step (kissat *solver, unsigned idx) {
  kissat_policy_begin_analysis (solver);
  bump_round (solver, idx);
  kissat_policy_end_analysis (solver);
}

// The channel weighting through both conflicts, without reason-side
// bumps: a bump adds inc for a decided interval and inc w for an asserted
// or a propagated one, the asserted literal -2 in its new interval.

static void test_reward_weighted (void) {
  kissat *solver = new_solver ("wimp", 250, "bumpreasons", 0);
  const reward *const reward = &solver->policy.reward;
  const double w = 0.25;
  double s[9];
  for (unsigned idx = 0; idx < 9; idx++)
    s[idx] = initial (idx);
  double inc = solver->scinc;
  first_conflict (solver);
  s[0] = s[0] + inc * 1; // decided, open
  s[1] = s[1] + inc * 1; // decided, ended by the backjump
  s[2] = s[2] + inc * w; // propagated, ended
  assert (reward->count.bumps[INTERVALS_DECIDED] == 2);
  assert (reward->count.bumps[INTERVALS_PROPAGATED] == 1);
  inc = solver->scinc;
  second_conflict (solver);
  s[1] = s[1] + inc * w; // asserted
  s[3] = s[3] + inc * 1; // decided, ended
  s[4] = s[4] + inc * w; // propagated, ended
  assert (reward->count.bumps[INTERVALS_ASSERTED] == 1);
  assert (reward->count.bumps[INTERVALS_DECIDED] == 3);
  assert (reward->count.bumps[INTERVALS_PROPAGATED] == 2);
  assert (!reward->count.bumps[REWARD_NONE]);
  for (unsigned idx = 0; idx < 9; idx++)
    assert (kissat_same_double (score (solver, idx), s[idx]));
  assert (!reward->count.closed[INTERVALS_CLOSE_DEFERRED]); // not called
#ifndef NDEBUG
  assert (reward->check.bumps == 6);
  assert (reward->check.assertions == 2);
#endif
  kissat_release (solver);
}

// At w = 1 the reward's bump is Kissat's, bitwise: the same conflicts,
// reason-side bumps included, under Argmax and under the reward with its
// weight set to one, give every score the same bits and the same picks.

static void test_reward_identity (void) {
  kissat *argmax = new_solver (0, 0, 0, 0);
  kissat *solver = new_solver ("wimp", 250, 0, 0);
  solver->policy.reward.wimp = 1;
  first_conflict (argmax);
  first_conflict (solver);
  second_conflict (argmax);
  second_conflict (solver);
  for (unsigned idx = 0; idx < 9; idx++)
    assert (kissat_same_double (kissat_get_score (argmax, idx),
                                kissat_get_score (solver, idx)));
  assert (kissat_same_double (argmax->scinc, solver->scinc));
  assert (kissat_policy_pick (argmax) == kissat_policy_pick (solver));
  kissat_release (argmax);
  kissat_release (solver);
}

// The lazy value of a variable in true units: over its interval's
// multiplier while its interval is open, else over g.

static double lazy (kissat *solver, unsigned idx) {
  const intervals *const intervals = &solver->policy.intervals;
  const unsigned state = intervals->state[idx];
  const double scale = state & INTERVALS_OPEN ? intervals->multiplier[idx]
                                              : solver->policy.reward.g;
  return score (solver, idx) / scale;
}

static bool close_to (double a, double b) {
  return fabs (a - b) <= 1e-12 * fabs (b);
}

// Locality at lambda = 1/2, without reason-side bumps, against the eager
// form computed here: every variable unassigned at the end of a step that
// bumps decays by lambda, an assigned one does not.  The first step
// decays 3 to 9 (2 and 3 bumped first), the second 3 and 5 to 9 (4 and 5
// bumped at the multiplier of their assignment, g = 2), and a restart then
// moves 1, 2 and 4 to the current g = 4.  The picks are the eager ones.

static void test_reward_locality (void) {
  kissat *solver = new_solver ("locality", 1, "localitydecay", 500);
  kissat_set_option (solver, "bumpreasons", 0);
  const reward *const reward = &solver->policy.reward;
  double e[9];
  for (unsigned idx = 0; idx < 9; idx++)
    e[idx] = initial (idx);
  double inc = solver->scinc;
  first_conflict (solver);
  e[0] += inc, e[1] += inc, e[2] += inc;
  for (unsigned idx = 2; idx < 9; idx++)
    e[idx] *= 0.5;
  assert (reward->g == 2);
  assert (reward->count.steps == 1);
  for (unsigned idx = 0; idx < 9; idx++)
    assert (close_to (lazy (solver, idx), e[idx]));
  inc = solver->scinc;
  second_conflict (solver);
  e[1] += inc, e[3] += inc, e[4] += inc;
  e[2] *= 0.5;
  for (unsigned idx = 4; idx < 9; idx++)
    e[idx] *= 0.5;
  assert (reward->g == 4);
  assert (solver->policy.intervals.multiplier[3] == 2); // asserted at g 2
  for (unsigned idx = 0; idx < 9; idx++)
    assert (close_to (lazy (solver, idx), e[idx]));
  // The pick is the variable of largest eager value among the unassigned.
  unsigned best = INVALID_IDX;
  for (unsigned idx = 0; idx < 9; idx++)
    if (!VALUE (LIT (idx)) && (best == INVALID_IDX || e[idx] > e[best]))
      best = idx;
  assert (kissat_policy_pick (solver) == best);
  kissat_backtrack_without_updating_phases (solver, 0);
  for (unsigned idx = 0; idx < 9; idx++) {
    assert (close_to (score (solver, idx) / reward->g, e[idx]));
    assert (kissat_same_double (kissat_tree_key (&solver->policy.tree, idx),
                                score (solver, idx)));
  }
  best = 0;
  for (unsigned idx = 1; idx < 9; idx++)
    if (e[idx] > e[best])
      best = idx;
  assert (kissat_policy_pick (solver) == best);
  kissat_release (solver);
}

// A rescale with g = 4 and the intervals of 1, -2 and -4 open at
// multipliers 1, 1 and 2: the open intervals take g first, every stored
// value is divided by the largest of them or the increment times g, the
// increment by that over g, and g and every multiplier are set to one.  The
// order of the unassigned variables' values and every variable's value
// over the increment are preserved, and the tree is rebuilt.

static void test_reward_rescale (void) {
  kissat *solver = new_solver ("locality", 1, "localitydecay", 500);
  const reward *const reward = &solver->policy.reward;
  const intervals *const intervals = &solver->policy.intervals;
  first_conflict (solver);
  second_conflict (solver);
  assert (reward->g == 4);
  double before[9];
  const double inc = solver->scinc;
  for (unsigned idx = 0; idx < 9; idx++)
    before[idx] = lazy (solver, idx) / inc;
  double largest = solver->scinc * reward->g;
  for (unsigned idx = 0; idx < 9; idx++) {
    const double moved = intervals->state[idx] & INTERVALS_OPEN
                             ? lazy (solver, idx) * reward->g
                             : score (solver, idx);
    if (moved > largest)
      largest = moved;
  }
  const uint64_t rescales = solver->estimator.rescales;
  kissat_rescale_scores (solver);
  assert (solver->estimator.rescales == rescales + 1);
  assert (reward->g == 1);
  for (unsigned idx = 0; idx < 9; idx++) {
    assert (intervals->multiplier[idx] == 1);
    assert (score (solver, idx) <= 1);
    assert (close_to (lazy (solver, idx) / solver->scinc, before[idx]));
    assert (kissat_same_double (kissat_tree_key (&solver->policy.tree, idx),
                                score (solver, idx)) ||
            !kissat_tree_contains (&solver->policy.tree, idx));
  }
  assert (close_to (solver->scinc, inc * 4 / largest));
  for (unsigned a = 0; a < 9; a++)
    for (unsigned b = 0; b < 9; b++)
      if (!VALUE (LIT (a)) && !VALUE (LIT (b)) && before[a] < before[b])
        assert (score (solver, a) <= score (solver, b));
  // A variable unassigned now moves by g / g_a = 1.
  const double s0 = score (solver, 0);
  kissat_backtrack_without_updating_phases (solver, 0);
  assert (kissat_same_double (score (solver, 0), s0));
  kissat_release (solver);
}

// g above 'MAX_SCORE' rescales: at lambda = 1/2 g doubles a step, steps
// by hand of one bump each, until the 499th takes it above (2^499 is
// about 1.6 10^150).  With w = 0 the bumps, of a propagated variable, add
// nothing, so the stored values stay small against the increment times g,
// which is then the reference: the increment is one after the rescale.

static void test_reward_rescale_g (void) {
  kissat *solver = new_solver ("locality", 1, "localitydecay", 500);
  solver->policy.reward.wimp = 0; // as 'wimp=0' would have started it
  solver->policy.reward.weighted = true;
  const reward *const reward = &solver->policy.reward;
  kissat_internal_assume (solver, LIT (5));
  imply (solver, 6);
  for (unsigned i = 1; i <= 499; i++) {
    step (solver, 6);
    assert (reward->count.rescales == (i == 499));
  }
  assert (reward->count.steps == 499);
  assert (reward->count.bumps[INTERVALS_PROPAGATED] == 499);
  assert (reward->g == 1);
  assert (close_to (solver->scinc, 1));
  assert (solver->policy.intervals.multiplier[5] == 1);
  kissat_backtrack_without_updating_phases (solver, 0);
  for (unsigned idx = 0; idx < 9; idx++)
    assert (score (solver, idx) <= 1);
  kissat_release (solver);
}

// A variable assigned across three rescales of g, 1497 steps at lambda =
// 1/2, each bumping it: the open interval takes the current g at every
// rescale, so that its multiplier, and its stored value with it, never
// fall below one rescale's factor (dividing the multiplier by g instead
// would leave it 2^-1497, which underflows).  At its unassignment its value
// over the increment is what the bumps and the increment's growth give.

static void test_reward_rescale_long (void) {
  kissat *solver = new_solver ("locality", 1, "localitydecay", 500);
  const reward *const reward = &solver->policy.reward;
  kissat_internal_assume (solver, LIT (5));
  double ratio = initial (5) / solver->scinc;
  for (unsigned i = 1; i <= 3 * 499; i++) {
    step (solver, 5);
    ratio = (ratio + 1) * 0.95;
  }
  assert (reward->count.rescales == 3);
  kissat_backtrack_without_updating_phases (solver, 0);
  const double value = score (solver, 5) / reward->g / solver->scinc;
  assert (fabs (value - ratio) <= 1e-9 * ratio);
  kissat_release (solver);
}

// A score written in true units while its variable is unassigned is
// stored times g, as is 'reorder's weight when it is added.

static void test_reward_true_score (void) {
  kissat *solver = new_solver ("locality", 1, "localitydecay", 500);
  kissat_internal_assume (solver, LIT (5));
  step (solver, 5);
  assert (solver->policy.reward.g == 2);
  kissat_update_true_score (solver, 8, 3);
  assert (score (solver, 8) == 6);
  const double weight = kissat_true_weight (solver, 8, 0.5);
  assert (weight == 1);
  kissat_update_score (solver, 8, score (solver, 8) + weight);
  assert (score (solver, 8) / 2 == 3.5);
  kissat_release (solver);
}

// 'reorder's weight under locality: after a step by hand at lambda = 1/2,
// g = 2 at level zero, every variable unassigned; reorder rescales, which
// sets g to one, and adds each variable's weight in true units, from the
// clauses: 1/2 for each ternary clause a literal is in, 1/4 for the clause
// of four, max (pos, neg) + 2 min (pos, neg) a variable.

static void test_reward_reorder (void) {
  kissat *solver = new_solver ("locality", 1, "localitydecay", 500);
  const reward *const reward = &solver->policy.reward;
  kissat_internal_assume (solver, LIT (5));
  step (solver, 5);
  kissat_backtrack_without_updating_phases (solver, 0);
  assert (reward->g == 2);
  double before[9];
  for (unsigned idx = 0; idx < 9; idx++)
    before[idx] = score (solver, idx) / reward->g;
  double largest = solver->scinc * reward->g;
  for (unsigned idx = 0; idx < 9; idx++)
    if (score (solver, idx) > largest)
      largest = score (solver, idx);
  const double unit = reward->g / largest;
  const double weights[9] = {1, 3, 1.5, 1, 1.5, 0.25, 0.25, 0.25, 0.25};
  kissat_reorder (solver);
  assert (reward->g == 1);
  for (unsigned idx = 0; idx < 9; idx++)
    assert (close_to (score (solver, idx),
                      before[idx] * unit + weights[idx]));
  kissat_release (solver);
}

// The interval reward, steps by hand outside analysis: the decision 6 is
// bumped in the first and third of three rounds and closes paying inc (2 /
// 3) at the close; 7, assigned in the third round, closes after one round
// without a bump, paying nothing; 8, assigned after the rounds, closes
// with k = 0.

static void test_reward_interval (void) {
  kissat *solver = new_solver ("intervalreward", 1, 0, 0);
  const reward *const reward = &solver->policy.reward;
  kissat_internal_assume (solver, LIT (5));
  const double s5 = score (solver, 5), s6 = score (solver, 6);
  const double s0 = score (solver, 0);
  bump_round (solver, 5);
  bump_round (solver, 0);
  kissat_internal_assume (solver, LIT (6));
  bump_round (solver, 5);
  assert (kissat_same_double (score (solver, 5), s5));
  assert (kissat_same_double (score (solver, 0), s0)); // in no interval
  assert (reward->count.bumps[REWARD_NONE] == 1);
  kissat_internal_assume (solver, LIT (7));
  const double inc = solver->scinc;
  kissat_backtrack_without_updating_phases (solver, 0);
  assert (kissat_same_double (score (solver, 5),
                              s5 + inc * (2.0 / 3.0) * 1 * 1));
  assert (kissat_same_double (score (solver, 6), s6));
  assert (reward->count.paid == 2 && reward->count.unbumped == 1);
  assert (reward->count.empty == 1);
#ifndef NDEBUG
  assert (reward->check.intervals == 3 && reward->check.payments == 1);
#endif
  kissat_release (solver);
}

// The interval reward with w = 4 and locality at lambda = 1/2: 6 decided
// and 7 propagated at g = 1, two steps, 7 bumped in the first only and 8,
// decided after the first, in the second, then a restart: 6 and 7 pay inc
// (1 / 2) w_c g_a with g_a = 1, 8 inc (1 / 1) g_a with g_a = 2, and each
// moves to g = 4.

static void test_reward_interval_weighted (void) {
  kissat *solver = kissat_init ();
#ifndef NDEBUG
  kissat_set_option (solver, "check", 0);
#endif
  kissat_set_option (solver, "intervalreward", 1);
  kissat_set_option (solver, "wimp", 4000);
  kissat_set_option (solver, "locality", 1);
  kissat_set_option (solver, "localitydecay", 500);
  for (int i = 1; i <= 9; i++)
    kissat_add (solver, i);
  kissat_add (solver, 0);
  solver->stable = true;
  kissat_init_averages (solver, &AVERAGES);
  kissat_update_scores (solver);
  kissat_start_policy (solver);
  const reward *const reward = &solver->policy.reward;
  const double s5 = score (solver, 5), s6 = score (solver, 6);
  const double s7 = score (solver, 7);
  kissat_internal_assume (solver, LIT (5));
  imply (solver, 6);
  step (solver, 6);
  kissat_internal_assume (solver, LIT (7));
  PUSH_STACK (solver->analyzed, 7);
  step (solver, 5);
  CLEAR_STACK (solver->analyzed);
  assert (reward->g == 4);
  assert (kissat_same_double (score (solver, 5), s5));
  assert (kissat_same_double (score (solver, 6), s6));
  assert (kissat_same_double (score (solver, 7), s7));
  assert (solver->policy.intervals.multiplier[7] == 2);
  const double inc = solver->scinc;
  kissat_backtrack_without_updating_phases (solver, 0);
  assert (kissat_same_double (
      score (solver, 5), (s5 + inc * (1.0 / 2.0) * 1 * 1) * (4 / 1.0)));
  assert (kissat_same_double (
      score (solver, 6), (s6 + inc * (1.0 / 2.0) * 4 * 1) * (4 / 1.0)));
  assert (kissat_same_double (
      score (solver, 7), (s7 + inc * (1.0 / 1.0) * 1 * 2) * (4 / 2.0)));
  assert (reward->count.paid == 3 && !reward->count.unbumped);
#ifndef NDEBUG
  assert (reward->check.payments == 3 && reward->check.intervals == 3);
#endif
  kissat_release (solver);
}

// A solver of LRB's line (see 'testlrb.c'), over
//
//   (-1 2) (-3 4) (-2 -4 5) (-2 -4 -5) (6 7 8 9)
//
// deciding 1 propagates 2, and deciding 3 then propagates 4 and 5 and
// falsifies (-2 -4 -5); the analysis learns (-4 -2) from 2, 4 and 5,
// backjumps to level 1 and asserts -4.  At the step's end 3 (decided), 4
// and 5 (propagated) close after one conflict, 4 and 5 with reward 1, and
// 3 with 0 (no reason-side participations).

static kissat *new_lrb_solver (const char *name, int value,
                               const char *other, int other_value) {
  kissat *solver = kissat_init ();
#ifndef NDEBUG
  kissat_set_option (solver, "check", 0);
#endif
  kissat_set_option (solver, "chb", 1);
  kissat_set_option (solver, "lrb", 1);
  kissat_set_option (solver, "otfs", 0);
  kissat_set_option (solver, "bumpreasons", 0);
  if (name)
    kissat_set_option (solver, name, value);
  if (other)
    kissat_set_option (solver, other, other_value);
  const int clauses[][5] = {{-1, 2, 0},
                            {-3, 4, 0},
                            {-2, -4, 5, 0},
                            {-2, -4, -5, 0},
                            {6, 7, 8, 9, 0}};
  for (unsigned i = 0; i < sizeof clauses / sizeof *clauses; i++)
    for (const int *p = clauses[i];; p++) {
      kissat_add (solver, *p);
      if (!*p)
        break;
    }
  solver->stable = true;
  kissat_init_averages (solver, &AVERAGES);
  kissat_update_scores (solver);
  kissat_start_policy (solver);
  return solver;
}

static void lrb_conflict (kissat *solver) {
  kissat_internal_assume (solver, LIT (0));
  assert (!kissat_search_propagate (solver));
  kissat_internal_assume (solver, LIT (2));
  clause *conflict = kissat_search_propagate (solver);
  assert (conflict);
  kissat_analyze (solver, conflict);
  assert (solver->level == 1);
  assert (VALUE (LIT (3)) < 0);
}

static double erwa (double q, double alpha, double reward) {
  return (1 - alpha) * q + alpha * reward;
}

// The weighting on LRB's estimator: the decided interval's step alpha /
// max (1, w), the propagated ones' alpha w / max (1, w), at w = 1/4 and 4.

static void lrb_weighted (int wimp) {
  kissat *solver = new_lrb_solver ("wimp", wimp, 0, 0);
  const reward *const reward = &solver->policy.reward;
  const double w = wimp / 1000.0, m = w > 1 ? w : 1;
  lrb_conflict (solver);
  const double alpha = kissat_chb_alpha (1);
  const double decided = alpha * 1 / m, implied = alpha * w / m;
  assert (kissat_same_double (score (solver, 2), erwa (0, decided, 0)));
  assert (kissat_same_double (score (solver, 3), erwa (0, implied, 1)));
  assert (kissat_same_double (score (solver, 4), erwa (0, implied, 1)));
  assert (reward->count.updates[INTERVALS_DECIDED] == 1);
  assert (reward->count.updates[INTERVALS_PROPAGATED] == 2);
#ifndef NDEBUG
  assert (reward->check.updates == 3);
#endif
  kissat_release (solver);
}

static void test_reward_lrb_weighted (void) {
  lrb_weighted (250);
  lrb_weighted (4000);
}

// Locality on LRB's estimator at lambda = 1/2: the step's closes update Q
// from the stored value over g_a = 1 and store it times g = 1; then every
// unassigned Q decays, by g growing to 2, but 4's, asserted again.  A
// restart closes 1 and 2 (2 participated: reward 1), and -4 and the -3 it
// propagated without a conflict (no update), each moved to g.

static void test_reward_lrb_locality (void) {
  kissat *solver = new_lrb_solver ("locality", 1, "localitydecay", 500);
  const reward *const reward = &solver->policy.reward;
  lrb_conflict (solver);
  const double alpha = kissat_chb_alpha (1);
  double q[9] = {0};
  q[3] = q[4] = erwa (0, alpha, 1);
  for (unsigned idx = 0; idx < 9; idx++)
    if (!VALUE (LIT (idx)))
      q[idx] *= 0.5;
  assert (reward->g == 2 && reward->count.steps == 1);
  for (unsigned idx = 0; idx < 9; idx++)
    assert (close_to (lazy (solver, idx), q[idx]) || !q[idx]);
  assert (!kissat_search_propagate (solver));
  assert (VALUE (LIT (2)) < 0);
  kissat_backtrack_without_updating_phases (solver, 0);
  q[1] = erwa (q[1], alpha, 1);
  for (unsigned idx = 0; idx < 9; idx++)
    assert (close_to (score (solver, idx) / reward->g, q[idx]) || !q[idx]);
  assert (solver->policy.lrb.count.skipped == 2);
  unsigned best = 0;
  for (unsigned idx = 1; idx < 9; idx++)
    if (q[idx] > q[best])
      best = idx;
  assert (kissat_policy_pick (solver) == best);
  // At g = 2 deciding 1 propagates 2, and with the learned clause -4 and
  // -3, all opened at conflict 1.  A step by hand records 2's
  // participation and decays: the four are recorded at g_a = 2 first, and g
  // grows to 4.  A restart one conflict later updates each from its stored
  // value over g_a, and stores the new Q times g.
  kissat_internal_assume (solver, LIT (0));
  assert (!kissat_search_propagate (solver));
  assert (VALUE (LIT (1)) > 0 && VALUE (LIT (3)) < 0);
  assert (VALUE (LIT (2)) < 0);
  kissat_policy_begin_analysis (solver);
  PUSH_STACK (solver->analyzed, 1);
  kissat_chb_analyzed (solver);
  CLEAR_STACK (solver->analyzed);
  kissat_policy_end_analysis (solver);
  assert (reward->g == 4);
  assert (solver->policy.intervals.multiplier[1] == 2);
  for (unsigned idx = 0; idx < 9; idx++)
    if (!VALUE (LIT (idx)))
      q[idx] *= 0.5;
  solver->estimator.chb.conflicts = 2;
  kissat_backtrack_without_updating_phases (solver, 0);
  const double alpha2 = kissat_chb_alpha (2);
  q[0] = erwa (q[0], alpha2, 0);
  q[1] = erwa (q[1], alpha2, 1);
  q[2] = erwa (q[2], alpha2, 0);
  q[3] = erwa (q[3], alpha2, 0);
  for (unsigned idx = 0; idx < 9; idx++)
    assert (close_to (score (solver, idx) / reward->g, q[idx]) || !q[idx]);
  kissat_release (solver);
}

#endif

#endif

void tissat_schedule_reward (void) {
#if !defined(HEAPARGMAX) && !defined(NOPTIONS)
  SCHEDULE_FUNCTION (test_reward_options);
  SCHEDULE_FUNCTION (test_reward_start);
#ifndef FEEDBACK
  SCHEDULE_FUNCTION (test_reward_weighted);
  SCHEDULE_FUNCTION (test_reward_identity);
  SCHEDULE_FUNCTION (test_reward_locality);
  SCHEDULE_FUNCTION (test_reward_rescale);
  SCHEDULE_FUNCTION (test_reward_rescale_g);
  SCHEDULE_FUNCTION (test_reward_rescale_long);
  SCHEDULE_FUNCTION (test_reward_true_score);
  SCHEDULE_FUNCTION (test_reward_reorder);
  SCHEDULE_FUNCTION (test_reward_interval);
  SCHEDULE_FUNCTION (test_reward_interval_weighted);
  SCHEDULE_FUNCTION (test_reward_lrb_weighted);
  SCHEDULE_FUNCTION (test_reward_lrb_locality);
#endif
#endif
}
