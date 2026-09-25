#ifndef _chb_h_INCLUDED
#define _chb_h_INCLUDED

// CHB scores: the estimator's second score vector (tree builds, option
// 'chb'), after Liang, Ganesh, Poupart and Czarnecki, 'Exponential
// Recency Weighted Average Branching Heuristic for SAT Solvers', AAAI
// 2016, Algorithm 1.  With 'chb=1' the stable-mode score of a variable is
// its ERWA value Q instead of its VSIDS activity, and the policy reads it
// through 'kissat_get_score' like any score.  Focused mode and its VMTF
// queue are unchanged.
//
// Q starts at zero at activation (no pseudo-activity).  After every
// propagation of the search in stable mode, every active variable assigned
// since the previous one (branched on, propagated or asserted, the
// paper's 'plays') is paid the reward
//
//   r = multiplier / (conflicts - last_conflict[v] + 1)
//
// and Q[v] = (1 - alpha) Q[v] + alpha r, where 'conflicts' counts the
// stable-mode search conflicts before this propagation, the multiplier is
// 1 if the propagation ended in a conflict and 0.9 otherwise, and the step
// size alpha is 0.4 less 10^-6 per conflict, down to 0.06.  Then a
// conflict increments 'conflicts', and conflict analysis sets
// last_conflict[v] = conflicts for every variable in the clauses it used:
// the analyzed variables at the point where VSIDS would bump them
// ('kissat_bump_analyzed'), i.e. those met in 1-UIP resolution and the
// block UIPs of shrinking, without the reason-side literals that Kissat
// adds for bumping (not part of CHB).
//
// The reward is paid per propagation rather than at each assignment since
// the multiplier depends on how the propagation ends.  The variables to
// pay are the trail from the position 'played' up to its end; every
// shrinking of the trail below that position (backtracking, flushing
// units) moves it down, so literals that chronological backtracking keeps
// on the trail are not paid twice.  Warm-up, probing and the other
// inprocessing propagate by other routines and pay nothing.
//
// Nothing decays and nothing is rescaled: Q lies in [0, 1].  In stable
// mode 'reorder' leaves Q alone (it is part of the VSIDS estimator), so
// the tree is never rebuilt for CHB's sake.

#ifndef HEAPARGMAX

#include "internal.h"

#include <stdbool.h>

#define CHB_ALPHA_INITIAL 0.4
#define CHB_ALPHA_DECREMENT 1e-6
#define CHB_ALPHA_MINIMUM 0.06
#define CHB_MULTIPLIER_CONFLICT 1.0
#define CHB_MULTIPLIER_NO_CONFLICT 0.9

static inline bool kissat_chb (struct kissat *solver) {
#ifdef NOPTIONS
  (void) solver;
#endif
  return GET_OPTION (chb);
}

// The step size after 'conflicts' conflicts, computed from their number
// rather than by repeated subtraction, so it carries no rounding from one
// conflict to the next.

static inline double kissat_chb_alpha (uint64_t conflicts) {
  const double alpha =
      CHB_ALPHA_INITIAL - CHB_ALPHA_DECREMENT * (double) conflicts;
  return alpha > CHB_ALPHA_MINIMUM ? alpha : CHB_ALPHA_MINIMUM;
}

// The trail was shrunk to 'size' literals.

static inline void kissat_chb_shrink_trail (struct kissat *solver,
                                            unsigned size) {
  unsigned *const played = &solver->estimator.chb.played;
  if (*played > size)
    *played = size;
}

// Called after every search propagation, with CHB scores: pays every
// variable assigned since the last call in stable mode.

void kissat_chb_assign (struct kissat *, bool conflict);

// Called by 'kissat_bump_analyzed' in stable mode with CHB scores: the
// analyzed variables participated in the current conflict.

void kissat_chb_analyzed (struct kissat *);

#endif

#endif
