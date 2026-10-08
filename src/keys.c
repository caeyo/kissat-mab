#include "keys.h"

#ifndef HEAPARGMAX

#include "allocate.h"
#include "error.h"
#include "inline.h"
#include "inlinepolicy.h"
#include "print.h"

#include <math.h>
#include <string.h>

// A uniform from the policy's generator: 53 bits, zero excluded.

static double positive_uniform (generator *random) {
  double res;
  do
    res = kissat_pick_double53 (random);
  while (!res);
  return res;
}

// P1's perturbation: Gumbel, -ln (-ln u), finite for every 'u' in (0, 1).

static double draw_gumbel (generator *random) {
  return -log (-log (positive_uniform (random)));
}

// TS's standard normal: Box-Muller, the radius from one uniform and the
// angle from the next, and the second normal of the pair kept for the
// next draw.

#define TWO_PI 6.283185307179586476925286766559

static double draw_normal (keys *keys, generator *random) {
  if (keys->spared) {
    keys->spared = false;
    return keys->spare;
  }
  const double u = positive_uniform (random);
  const double v = positive_uniform (random);
  const double radius = sqrt (-2 * log (u));
  const double angle = TWO_PI * v;
  keys->spare = radius * sin (angle);
  keys->spared = true;
  return radius * cos (angle);
}

// The increment of the counts: the score increment on VSIDS scores, the
// counts' own on CHB scores.

static double count_increment (kissat *solver) {
  const policy *const policy = &solver->policy;
  return policy->chb ? policy->keys.increment : solver->scinc;
}

// A variable's draw at a draw point or its activation: P1's term
// e^(g / eta), with g / eta exact since eta is a power of two; TS's normal
// and its term from the variable's evidence; UCB's term from its count.

static void draw_variable (kissat *solver, unsigned idx) {
  policy *const policy = &solver->policy;
  keys *const keys = &policy->keys;
  switch (keys->kind) {
  case KEYS_PERTURBED: {
    const double g = draw_gumbel (&policy->random);
    keys->term[idx] = exp (ldexp (g, -policy->etalog2));
  } break;
  case KEYS_THOMPSON: {
    keys->normal[idx] = draw_normal (keys, &policy->random);
    const double evidence =
        policy->chb ? keys->count[idx] / keys->increment
                    : solver->score[idx] / solver->scinc;
    keys->term[idx] = kissat_thompson_term (policy, idx, evidence);
  } break;
  default: {
    assert (keys->kind == KEYS_UCB);
    const double count = keys->count[idx] / count_increment (solver);
    keys->term[idx] = kissat_ucb_term (policy, count);
  } break;
  }
}

// A draw point: every active variable draws, in index order, or under UCB
// gets its term from the counts' new sum, and the tree is rebuilt.

void kissat_draw_keys (kissat *solver) {
  policy *const policy = &solver->policy;
  keys *const keys = &policy->keys;
  assert (keys->kind);
  assert (solver->stable);
  assert (!policy->bulk);
#ifdef DECISION_METRICS
  const uint64_t start = kissat_policy_clock ();
#endif
  keys->draws++;
  if (keys->kind == KEYS_UCB) {
    const double *const count = keys->count;
    double sum = 0;
    for (all_variables (idx))
      if (ACTIVE (idx))
        sum += count[idx];
    const double total = sum / count_increment (solver);
    keys->total = total;
    keys->scale = keys->factor * sqrt (total > 1 ? log (total) : 0);
    LOG ("UCB counts sum %g scale %g", total, keys->scale);
  }
  for (all_variables (idx))
    if (ACTIVE (idx))
      draw_variable (solver, idx);
  kissat_rebuild_policy (solver);
#ifdef DECISION_METRICS
  const uint64_t stop = kissat_policy_clock ();
  if (stop > start)
    keys->ticks += stop - start;
#endif
}

// A stable-mode restart: P1 and TS draw unless they draw at rephases, and
// UCB always recomputes.

void kissat_restart_keys (kissat *solver) {
  const keys *const keys = &solver->policy.keys;
  if (keys->kind == KEYS_UCB || (keys->kind && !keys->redraw))
    kissat_draw_keys (solver);
}

void kissat_rephase_keys (kissat *solver) {
  const keys *const keys = &solver->policy.keys;
  if (keys->kind && keys->kind != KEYS_UCB && keys->redraw)
    kissat_draw_keys (solver);
}

void kissat_activate_keys (kissat *solver, unsigned idx) {
  assert (solver->policy.keys.kind);
  assert (solver->stable);
  draw_variable (solver, idx);
}

// UCB on VSIDS scores: the interval of 'idx' closes (see 'intervals.h'),
// and its count adds the increments of the bump rounds since its
// assignment.  At its unassignment, or after the bump round or at the end
// of the analysis step whose backtrack ended it (LRB's interval), its term
// follows the new count.  A close the step deferred also sets the leaf:
// backtracking put it back with the key it had, and as no pick happens
// inside a step it is still there unless the variable was assigned again;
// an unassignment sets the leaf itself ('kissat_keys_unassign').  When
// stable mode is left the term stays, as the next entry is a draw point.

void kissat_close_keys_interval (kissat *solver, unsigned idx,
                                 unsigned how) {
  policy *const policy = &solver->policy;
  keys *const keys = &policy->keys;
  assert (keys->intervals);
  const double inc = solver->scinc;
  double *const count = keys->count + idx;
  *count += (inc - policy->intervals.opened[idx]) / (keys->growth - 1);
  if (how == INTERVALS_CLOSE_LEFT)
    return;
  keys->term[idx] = kissat_ucb_term (policy, *count / inc);
  if (how != INTERVALS_CLOSE_DEFERRED)
    return;
  tree *const tree = &policy->tree;
  const double key = kissat_policy_key (solver, idx);
  if (kissat_tree_contains (tree, idx) ? kissat_tree_key (tree, idx) != key
                                       : !solver->values[LIT (idx)])
    kissat_tree_set (tree, idx, key, 0);
}

void kissat_rescale_keys (kissat *solver, double factor) {
  keys *const keys = &solver->policy.keys;
  assert (keys->intervals);
  double *const count = keys->count;
  for (all_variables (idx))
    count[idx] *= factor;
}

void kissat_rescale_chb_counts (kissat *solver) {
  keys *const keys = &solver->policy.keys;
  assert (keys->counts);
  const double factor = 1.0 / keys->increment;
  double *const count = keys->count;
  for (all_variables (idx))
    count[idx] *= factor;
  keys->increment *= factor;
  LOG ("rescaled CHB counts by factor %g", factor);
}

// The arrays a policy needs, of 'size' entries each, zero beyond 'old'.

static double *resize_array (kissat *solver, double *array, bool needed,
                             unsigned old_size, unsigned new_size) {
  if (!needed)
    return 0;
  double *res = kissat_calloc (solver, new_size, sizeof *res);
  const unsigned kept = old_size < new_size ? old_size : new_size;
  if (kept)
    memcpy (res, array, kept * sizeof *res);
  kissat_dealloc (solver, array, old_size, sizeof *array);
  return res;
}

#ifdef SHADOW

// The same for the clocks of shadow mode's recount (see 'policy.h').

static uint64_t *resize_clocks (kissat *solver, uint64_t *array,
                                bool needed, unsigned old_size,
                                unsigned new_size) {
  if (!needed)
    return 0;
  uint64_t *res = kissat_calloc (solver, new_size, sizeof *res);
  const unsigned kept = old_size < new_size ? old_size : new_size;
  if (kept)
    memcpy (res, array, kept * sizeof *res);
  kissat_dealloc (solver, array, old_size, sizeof *array);
  return res;
}

#endif

void kissat_resize_keys (kissat *solver, unsigned size) {
  keys *const keys = &solver->policy.keys;
  if (!keys->kind)
    return;
  const unsigned old_size = keys->size;
  if (old_size == size)
    return;
  const bool normals = keys->kind == KEYS_THOMPSON;
  keys->term = resize_array (solver, keys->term, true, old_size, size);
  keys->normal =
      resize_array (solver, keys->normal, normals, old_size, size);
  keys->count =
      resize_array (solver, keys->count, keys->counts, old_size, size);
#ifdef SHADOW
  keys->recount =
      resize_array (solver, keys->recount, keys->counts, old_size, size);
  keys->recounted =
      resize_clocks (solver, keys->recounted, keys->counts, old_size, size);
#endif
  keys->size = size;
}

void kissat_release_keys (kissat *solver) {
  keys *const keys = &solver->policy.keys;
  const unsigned size = keys->size;
  if (keys->term)
    kissat_dealloc (solver, keys->term, size, sizeof *keys->term);
  if (keys->normal)
    kissat_dealloc (solver, keys->normal, size, sizeof *keys->normal);
  if (keys->count)
    kissat_dealloc (solver, keys->count, size, sizeof *keys->count);
  keys->term = keys->normal = keys->count = 0;
#ifdef SHADOW
  RELEASE_STACK (keys->observed);
  if (keys->recount)
    kissat_dealloc (solver, keys->recount, size, sizeof *keys->recount);
  if (keys->recounted)
    kissat_dealloc (solver, keys->recounted, size,
                    sizeof *keys->recounted);
  keys->recount = 0;
  keys->recounted = 0;
#endif
  keys->size = 0;
}

// Checks the combination of the policy's options, and selects P1, TS or
// UCB if one is set: its constants, its arrays, and in stable mode (the
// search starts in stable mode with '--stable=2') its first draw point.
// A later search keeps the policy.

void kissat_start_keys (kissat *solver) {
  const unsigned perturbed = GET_OPTION (perturbed);
  const unsigned thompson = GET_OPTION (thompson);
  const unsigned ucb = GET_OPTION (ucb);
  const unsigned softmax = GET_OPTION (softmax);
  if (softmax + perturbed + thompson + ucb > 1)
    kissat_fatal ("at most one of the options 'softmax', 'perturbed', "
                  "'thompson' and 'ucb' can be set");
  if (!(perturbed | thompson | ucb))
    return;
  if (GET_OPTION (gammappm))
    kissat_fatal ("'perturbed', 'thompson' and 'ucb' do not mix "
                  "('gammappm' must be zero)");
  const bool chb = kissat_chb (solver);
  if (perturbed && chb)
    kissat_fatal ("'perturbed' needs VSIDS scores ('chb=0')");
  policy *const policy = &solver->policy;
  keys *const keys = &policy->keys;
  if (keys->kind)
    return;
  assert (!policy->tree.weighted);
  policy->chb = chb;
  policy->etalog2 = GET_OPTION (etalog2);
  keys->kind = perturbed ? KEYS_PERTURBED
               : thompson ? KEYS_THOMPSON
                          : KEYS_UCB;
  keys->redraw = GET_OPTION (redraw);
  if (thompson)
    keys->factor = GET_OPTION (thompsonkappa) / 1000.0;
  else if (ucb)
    keys->factor = GET_OPTION (ucbc) / 1000.0;
  keys->noise = perturbed || keys->factor > 0;
  keys->counts = ucb || (thompson && chb);
  keys->intervals = ucb && !chb;
  const double decay = GET_OPTION (decay) * 1e-3;
  keys->growth = 1.0 / (1.0 - decay);
  keys->increment = 1;
  kissat_resize_keys (solver, solver->size);
  if (perturbed)
    kissat_very_verbose (solver, "perturbed leader at eta 2^%d drawn at %s",
                         policy->etalog2,
                         keys->redraw ? "rephases" : "restarts");
  else if (thompson)
    kissat_very_verbose (solver,
                         "Thompson sampling at kappa %g drawn at %s",
                         keys->factor,
                         keys->redraw ? "rephases" : "restarts");
  else
    kissat_very_verbose (solver, "upper confidence bounds at c %g%s",
                         keys->factor,
                         keys->intervals && GET_OPTION (ucbinterval)
                             ? " counting LRB's interval"
                             : "");
  if (solver->stable)
    kissat_draw_keys (solver);
}

#else

int kissat_keys_dummy_to_avoid_warning;

#endif
