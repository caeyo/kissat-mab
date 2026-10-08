#include "bump.h"
#include "analyze.h"
#include "chb.h"
#include "inlinepolicy.h"
#include "inlinequeue.h"
#include "inlinevector.h"
#include "internal.h"
#include "logging.h"
#include "print.h"
#include "rank.h"
#include "sort.h"

#include <inttypes.h>

#define RANK(A) ((A).rank)
#define SMALLER(A, B) (RANK (A) < RANK (B))

#define RADIX_SORT_BUMP_LIMIT 32

static void sort_bump (kissat *solver) {
  const size_t size = SIZE_STACK (solver->analyzed);
  if (size < RADIX_SORT_BUMP_LIMIT) {
    LOG ("quick sorting %zu analyzed variables", size);
    SORT_STACK (datarank, solver->ranks, SMALLER);
  } else {
    LOG ("radix sorting %zu analyzed variables", size);
    RADIX_STACK (datarank, unsigned, solver->ranks, RANK);
  }
}

// The pseudo-activity is rescaled with the scores, as a bump made at time
// zero would be.  The estimator records when it reaches zero.

void kissat_rescale_scores (kissat *solver) {
  INC (rescaled);
  const double max_score = kissat_max_score (solver);
  kissat_phase (solver, "rescale", GET (rescaled),
                "maximum score %g increment %g", max_score, solver->scinc);
  const double rescale = MAX (max_score, solver->scinc);
  assert (rescale > 0);
  const double factor = 1.0 / rescale;
  kissat_scale_scores (solver, factor);
  solver->scinc *= factor;
  estimator *const estimator = &solver->estimator;
  const double old_pseudo = estimator->pseudo;
  const double new_pseudo = old_pseudo * factor;
  estimator->pseudo = new_pseudo;
  estimator->rescales++;
  if (old_pseudo > 0 && !(new_pseudo > 0)) {
    estimator->zero.round = estimator->rounds;
    estimator->zero.rescale = estimator->rescales;
    kissat_phase (solver, "rescale", GET (rescaled),
                  "pseudo-activity zero after %" PRIu64 " bump rounds",
                  estimator->rounds);
  }
  kissat_phase (solver, "rescale", GET (rescaled),
                "rescaled by factor %g (pseudo-activity %g)", factor,
                new_pseudo);
}

// The increment grows by 1/d at every bump round.  With LRB's interval the
// intervals a backtrack of this analysis step ended close after that, so
// that they count this round, and only then are the literals assigned
// since the backtrack recorded, so that their intervals start after it
// (see 'intervals.h'); feedback builds first count the round for their
// brute-force check.

void kissat_bump_score_increment (kissat *solver) {
  const double old_scinc = solver->scinc;
  const double decay = GET_OPTION (decay) * 1e-3;
  assert (0 <= decay), assert (decay <= 0.5);
  const double factor = 1.0 / (1.0 - decay);
  const double new_scinc = old_scinc * factor;
  LOG ("new score increment %g = %g * %g", new_scinc, factor, old_scinc);
  solver->scinc = new_scinc;
#ifndef HEAPARGMAX
#ifdef FEEDBACK
  kissat_feedback_round_end (solver); // the brute force's count
#endif
  if (solver->policy.intervals.deferring) {
    kissat_finish_deferred_intervals (solver);
    kissat_record_intervals (solver);
  }
#endif
  if (new_scinc > MAX_SCORE)
    kissat_rescale_scores (solver);
}

static inline void bump_analyzed_variable_score (kissat *solver,
                                                 unsigned idx) {
  const double old_score = kissat_get_score (solver, idx);
  const double inc = solver->scinc;
  const double new_score = old_score + inc;
  LOG ("new score[%u] = %g = %g + %g", idx, new_score, old_score, inc);
  kissat_bump_score (solver, idx, new_score);
  if (new_score > MAX_SCORE)
    kissat_rescale_scores (solver);
}

void kissat_bump_variable (kissat *solver, unsigned idx) {
  bump_analyzed_variable_score (solver, idx);
}

// A bump round: every analyzed variable, then the increment.  It is
// counted when it starts, so that a rescale during the round, triggered by
// a score or by the increment, sees the number of the round.  The
// assignment intervals of the literals assigned since their last record
// open before the round, so that it counts in them, and feedback builds
// count every bump in the interval it falls in (see 'intervals.h').

static void bump_analyzed_variable_scores (kissat *solver) {
#ifndef HEAPARGMAX
  kissat_record_intervals (solver); // opens intervals before the round
#endif
  solver->estimator.rounds++;
#ifdef SHADOW
  kissat_shadow_round (solver); // recounts UCB's observations
#endif
  flags *flags = solver->flags;

  for (all_stack (unsigned, idx, solver->analyzed))
    if (flags[idx].active) {
#ifdef FEEDBACK
      kissat_feedback_bump (solver, idx); // before the score's bump
#endif
      bump_analyzed_variable_score (solver, idx);
    }

  kissat_bump_score_increment (solver);
}

static void move_analyzed_variables_to_front_of_queue (kissat *solver) {
  assert (EMPTY_STACK (solver->ranks));
  const links *const links = solver->links;
  for (all_stack (unsigned, idx, solver->analyzed)) {
    // clang-format off
    const datarank rank = { .data = idx, .rank = links[idx].stamp };
    // clang-format on
    PUSH_STACK (solver->ranks, rank);
  }

  sort_bump (solver);

  flags *flags = solver->flags;
  unsigned idx;

  for (all_stack (datarank, rank, solver->ranks))
    if (flags[idx = rank.data].active)
      kissat_move_to_front (solver, idx);

  CLEAR_STACK (solver->ranks);
}

// With CHB scores (tree builds, see 'chb.h') a stable-mode conflict bumps
// nothing: it records that the analyzed variables took part in it.  On
// either line feedback builds count the step as a conflict of the open
// picks' intervals (M3, see 'feedback.h').

void kissat_bump_analyzed (kissat *solver) {
  START (bump);
  const size_t bumped = SIZE_STACK (solver->analyzed);
#ifdef FEEDBACK
  if (solver->stable)
    kissat_feedback_observe (solver); // M3's y_obs of the open picks
#endif
  if (!solver->stable)
    move_analyzed_variables_to_front_of_queue (solver);
#ifndef HEAPARGMAX
  else if (kissat_chb (solver))
    kissat_chb_analyzed (solver);
#endif
  else
    bump_analyzed_variable_scores (solver);
  ADD (literals_bumped, bumped);
  STOP (bump);
}
