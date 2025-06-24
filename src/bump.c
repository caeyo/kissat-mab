#include "bump.h"
#include "analyze.h"
#include "inlineheap.h"
#include "inlinelsidsheap.h"
#include "inlinevector.h"
#include "internal.h"
#include "logging.h"
#include "print.h"
#include "rank.h"
#include "sort.h"

void kissat_rescale_scores (kissat *solver) {
  INC (rescaled);
  heap *scores = &solver->scores;
  const double max_score = kissat_max_score_on_heap (scores);
  kissat_phase (solver, "rescale", GET (rescaled),
                "maximum score %g increment %g", max_score, solver->scinc);
  const double rescale = MAX (max_score, solver->scinc);
  assert (rescale > 0);
  const double factor = 1.0 / rescale;
  kissat_rescale_heap (solver, scores, factor);
  solver->scinc *= factor;
  kissat_phase (solver, "rescale", GET (rescaled), "rescaled by factor %g",
                factor);
}

void kissat_bump_score_increment (kissat *solver) {
  const double old_scinc = solver->scinc;
  const double decay = GET_OPTION (decay) * 1e-3;
  assert (0 <= decay), assert (decay <= 0.5);
  const double factor = 1.0 / (1.0 - decay);
  const double new_scinc = old_scinc * factor;
  LOG ("new score increment %g = %g * %g", new_scinc, factor, old_scinc);
  solver->scinc = new_scinc;
  if (new_scinc > MAX_SCORE)
    kissat_rescale_scores (solver);
}

static inline void bump_analyzed_variable_score (kissat *solver,
                                                 unsigned idx) {
  heap *scores = &solver->scores;
  const double old_score = kissat_get_heap_score (scores, idx);
  const double inc = solver->scinc;
  const double new_score = old_score + inc;
  LOG ("new score[%u] = %g = %g + %g", idx, new_score, old_score, inc);
  kissat_update_heap (solver, scores, idx, new_score);
  if (new_score > MAX_SCORE)
    kissat_rescale_scores (solver);
}

void kissat_bump_variable (kissat *solver, unsigned idx) {
  bump_analyzed_variable_score (solver, idx);
}

static void bump_analyzed_variable_scores (kissat *solver) {
  flags *flags = solver->flags;

  for (all_stack (unsigned, idx, solver->analyzed))
    if (flags[idx].active)
      bump_analyzed_variable_score (solver, idx);

  kissat_bump_score_increment (solver);
}

void lsids_rescale_scores (kissat *solver) {
  INC (rescaled);
  lsidsheap *heap = &solver->lsids_heap;
  const double max_score = lsids_max_score_on_heap (heap);
  kissat_phase (solver, "rescale", GET (rescaled),
                "maximum score %g increment %g", max_score, solver->lsids_scinc);
  const double rescale = MAX (max_score, solver->lsids_scinc);
  assert (rescale > 0);
  const double factor = 1.0 / rescale;
  lsids_rescale_heap (solver, heap, factor);
  solver->lsids_scinc *= factor;
  kissat_phase (solver, "rescale", GET (rescaled), "rescaled by factor %g",
                factor);
}

void lsids_bump_score_increment (kissat *solver) {
  const double old_scinc = solver->lsids_scinc;
  const double decay = GET_OPTION (decay) * 1e-3;
  assert (0 <= decay), assert (decay <= 0.5);
  const double factor = 1.0 / (1.0 - decay);
  const double new_scinc = old_scinc * factor;
  LOG ("new score increment %g = %g * %g", new_scinc, factor, old_scinc);
  solver->lsids_scinc = new_scinc;
  if (new_scinc > MAX_SCORE)
    lsids_rescale_scores (solver);
}

static inline void bump_analyzed_literal_score (kissat *solver,
                                                 unsigned idx,
                                                 unsigned pol) {
  lsidsheap *heap = &solver->lsids_heap;
  const double old_score = lsids_get_heap_score (heap, idx, pol);
  const double inc = solver->lsids_scinc;
  const double new_score = old_score + inc;
  LOG ("new score[%u] = %g = %g + %g", idx, new_score, old_score, inc);
  lsids_update_heap (solver, heap, idx, pol, new_score);
  if (new_score > MAX_SCORE)
    lsids_rescale_scores (solver);
}

static void bump_analyzed_literal_scores (kissat *solver) {
  flags *flags = solver->flags;

  for (all_stack (unsigned, idx, solver->analyzed))
    if (flags[idx].active)
      bump_analyzed_literal_score (solver, idx, solver->analyzed_pol[idx]);

  lsids_bump_score_increment (solver);
}

void kissat_bump_analyzed (kissat *solver) {
  START (bump);
  const size_t bumped = SIZE_STACK (solver->analyzed);
  if (!solver->stable)
    bump_analyzed_literal_scores (solver);
  else
    bump_analyzed_variable_scores (solver);
  ADD (literals_bumped, bumped);
  STOP (bump);
}

void kissat_update_scores (kissat *solver) {
  assert (solver->stable);
  heap *scores = SCORES;
  for (all_variables (idx))
    if (ACTIVE (idx) && !kissat_heap_contains (scores, idx))
      kissat_push_heap (solver, scores, idx);
}

void lsids_update_scores (kissat *solver) {
  assert (!solver->stable);
  lsidsheap *scores = &solver->lsids_heap;
  for (all_variables (idx))
    if (ACTIVE (idx) && !lsids_heap_contains (scores, idx))
      lsids_push_heap (solver, scores, idx);
}
