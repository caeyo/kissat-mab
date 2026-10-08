#include "feedback.h"

#ifdef FEEDBACK

#include "allocate.h"
#include "bump.h"
#include "chb.h"
#include "error.h"
#include "inline.h"
#include "inlinepolicy.h"
#include "print.h"

#include <inttypes.h>
#include <math.h>
#include <string.h>

// The arrays of a line, of 'size' entries each, zero beyond 'old'.

static void *resize_array (kissat *solver, void *array, size_t bytes,
                           unsigned old_size, unsigned new_size) {
  void *res = kissat_calloc (solver, new_size, bytes);
  const unsigned kept = old_size < new_size ? old_size : new_size;
  if (kept)
    memcpy (res, array, (size_t) kept * bytes);
  if (array)
    kissat_dealloc (solver, array, old_size, bytes);
  return res;
}

#define RESIZE(P, ENTRIES) \
  (P) = resize_array (solver, (P), (ENTRIES) * sizeof *(P), old_size, \
                      new_size)

void kissat_resize_feedback (kissat *solver, unsigned new_size) {
  feedback *const fb = &solver->policy.feedback;
  if (!fb->started)
    return;
  const unsigned old_size = fb->size;
  if (old_size == new_size)
    return;
  RESIZE (fb->state, 1);
  RESIZE (fb->yield, 1);
  RESIZE (fb->propagated, 1);
  RESIZE (fb->observed, 1);
#ifndef NDEBUG
  RESIZE (fb->check.propagated, 1);
  RESIZE (fb->check.observed, 1);
#endif
  if (fb->lrb) {
    RESIZE (fb->unassigned, 1);
    RESIZE (fb->slot, 1);
    RESIZE (fb->erwas, 1);
#ifndef NDEBUG
    RESIZE (fb->check.q1, 1);
    RESIZE (fb->check.shadow, 1);
#endif
  } else if (fb->chb) {
    RESIZE (fb->reward, 1);
    for (unsigned c = 0; c < 2; c++) {
      RESIZE (fb->q[c], 1);
      RESIZE (fb->paid[c], 1);
    }
    RESIZE (fb->count, 1);
    RESIZE (fb->latest, 1);
#ifdef SHADOW
    RESIZE (fb->repaid, 1);
#endif
  } else {
    for (unsigned c = 0; c < 2; c++) {
      RESIZE (fb->n[c], 1);
      RESIZE (fb->r[c], 1);
    }
    RESIZE (fb->frozen, FEEDBACK_PREDICTORS);
    RESIZE (fb->last, 1);
#ifndef NDEBUG
    RESIZE (fb->check.rounds, 1);
    RESIZE (fb->check.bumped, 1);
    RESIZE (fb->check.marked, 1);
#endif
    RESIZE (fb->unassigned, 1);
    RESIZE (fb->slot, 1);
    RESIZE (fb->classes, 1);
  }
  fb->size = new_size;
}

#define RELEASE(P, ENTRIES) \
  do { \
    if (P) \
      kissat_dealloc (solver, (P), size, (ENTRIES) * sizeof *(P)); \
    (P) = 0; \
  } while (0)

void kissat_release_feedback (kissat *solver) {
  feedback *const fb = &solver->policy.feedback;
  const unsigned size = fb->size;
  RELEASE (fb->state, 1);
  for (unsigned c = 0; c < 2; c++) {
    RELEASE (fb->n[c], 1);
    RELEASE (fb->r[c], 1);
    RELEASE (fb->q[c], 1);
    RELEASE (fb->paid[c], 1);
  }
  RELEASE (fb->frozen, FEEDBACK_PREDICTORS);
  RELEASE (fb->last, 1);
  RELEASE (fb->count, 1);
  RELEASE (fb->latest, 1);
#ifdef SHADOW
  RELEASE (fb->repaid, 1);
#endif
  RELEASE (fb->yield, 1);
  RELEASE (fb->propagated, 1);
  RELEASE (fb->observed, 1);
  RELEASE (fb->reward, 1);
  RELEASE (fb->unassigned, 1);
  RELEASE (fb->slot, 1);
  RELEASE (fb->classes, 1);
  RELEASE (fb->erwas, 1);
#ifndef NDEBUG
  RELEASE (fb->check.rounds, 1);
  RELEASE (fb->check.bumped, 1);
  RELEASE (fb->check.marked, 1);
  RELEASE (fb->check.propagated, 1);
  RELEASE (fb->check.observed, 1);
  RELEASE (fb->check.q1, 1);
  RELEASE (fb->check.shadow, 1);
  RELEASE_STACK (fb->check.listed);
  RELEASE_STACK (fb->check.staged);
  RELEASE_STACK (fb->check.levels);
#endif
  RELEASE_STACK (fb->staged);
  RELEASE_STACK (fb->records);
  RELEASE_STACK (fb->free);
  fb->size = 0;
}

static void start_factors (feedback *);

// At the start of the search, after LRB: the line, the decay of the counts
// (the score decay, as for UCB's counts, so that their increments are the
// scores'), and the arrays.  A later search keeps them.

void kissat_start_feedback (kissat *solver) {
  feedback *const fb = &solver->policy.feedback;
  if (fb->started)
    return;
  fb->started = true;
  fb->chb = kissat_chb (solver);
  fb->lrb = solver->policy.lrb.started;
  assert (!fb->lrb || fb->chb);
  const double decay = GET_OPTION (decay) * 1e-3;
  fb->growth = 1.0 / (1.0 - decay);
  fb->increment = 1;
  fb->log_lambda = log (FEEDBACK_LOCALITY);
  start_factors (fb);
  kissat_resize_feedback (solver, solver->size);
  kissat_very_verbose (solver, "measuring the decision's feedback on %s",
                       fb->lrb   ? "LRB's reward"
                       : fb->chb ? "CHB scores"
                                 : "VSIDS scores");
}

void kissat_move_feedback (kissat *solver, unsigned from, unsigned to) {
  feedback *const fb = &solver->policy.feedback;
  if (!fb->started)
    return;
  fb->state[to] = fb->state[from];
  fb->yield[to] = fb->yield[from];
  fb->propagated[to] = fb->propagated[from];
  fb->observed[to] = fb->observed[from];
  if (fb->yielding == from + 1)
    fb->yielding = to + 1;
#ifndef NDEBUG
  fb->check.propagated[to] = fb->check.propagated[from];
  fb->check.observed[to] = fb->check.observed[from];
#endif
  if (fb->lrb) {
    fb->unassigned[to] = fb->unassigned[from];
    fb->slot[to] = fb->slot[from];
    fb->erwas[to] = fb->erwas[from];
#ifndef NDEBUG
    fb->check.q1[to] = fb->check.q1[from];
    fb->check.shadow[to] = fb->check.shadow[from];
#endif
    return;
  }
  if (fb->chb) {
    fb->reward[to] = fb->reward[from];
    for (unsigned c = 0; c < 2; c++) {
      fb->q[c][to] = fb->q[c][from];
      fb->paid[c][to] = fb->paid[c][from];
    }
    fb->count[to] = fb->count[from];
    fb->latest[to] = fb->latest[from];
#ifdef SHADOW
    fb->repaid[to] = fb->repaid[from];
#endif
    return;
  }
  for (unsigned c = 0; c < 2; c++) {
    fb->n[c][to] = fb->n[c][from];
    fb->r[c][to] = fb->r[c][from];
  }
  for (unsigned i = 0; i < FEEDBACK_PREDICTORS; i++)
    fb->frozen[FEEDBACK_PREDICTORS * to + i] =
        fb->frozen[FEEDBACK_PREDICTORS * from + i];
  fb->last[to] = fb->last[from];
#ifndef NDEBUG
  fb->check.rounds[to] = fb->check.rounds[from];
  fb->check.bumped[to] = fb->check.bumped[from];
  fb->check.marked[to] = fb->check.marked[from];
#endif
  fb->unassigned[to] = fb->unassigned[from];
  fb->slot[to] = fb->slot[from];
  fb->classes[to] = fb->classes[from];
}

// The entries of a variable index beyond those compaction keeps.  A pending
// pick's record stays: it moved with its variable.

void kissat_clear_feedback (kissat *solver, unsigned idx) {
  feedback *const fb = &solver->policy.feedback;
  if (!fb->started)
    return;
  fb->state[idx] = 0;
  fb->yield[idx] = 0;
  fb->propagated[idx] = 0;
  fb->observed[idx] = 0;
  if (fb->yielding == idx + 1)
    fb->yielding = 0;
#ifndef NDEBUG
  fb->check.propagated[idx] = 0;
  fb->check.observed[idx] = 0;
#endif
  if (fb->lrb) {
    fb->unassigned[idx] = 0;
    fb->slot[idx] = 0;
    memset (fb->erwas + idx, 0, sizeof *fb->erwas);
#ifndef NDEBUG
    fb->check.q1[idx] = 0;
    memset (fb->check.shadow + idx, 0, sizeof *fb->check.shadow);
#endif
    return;
  }
  if (fb->chb) {
    fb->reward[idx] = 0;
    for (unsigned c = 0; c < 2; c++) {
      fb->q[c][idx] = 0;
      fb->paid[c][idx] = 0;
    }
    fb->count[idx] = 0;
    fb->latest[idx] = 0;
#ifdef SHADOW
    fb->repaid[idx] = 0;
#endif
    return;
  }
  for (unsigned c = 0; c < 2; c++)
    fb->n[c][idx] = fb->r[c][idx] = 0;
  for (unsigned i = 0; i < FEEDBACK_PREDICTORS; i++)
    fb->frozen[FEEDBACK_PREDICTORS * idx + i] = 0;
  fb->last[idx] = 0;
#ifndef NDEBUG
  fb->check.rounds[idx] = 0;
  fb->check.bumped[idx] = 0;
  fb->check.marked[idx] = 0;
#endif
  fb->unassigned[idx] = 0;
  fb->slot[idx] = 0;
  memset (fb->classes + idx, 0, sizeof *fb->classes);
}

static inline unsigned class_of (kissat *solver, unsigned idx) {
  return solver->assigned[idx].reason == DECISION_REASON ? FEEDBACK_DEC
                                                         : FEEDBACK_IMP;
}

// An interval's class in 'intervals.h' as this build's: decided, or
// implied (asserted or propagated).

static inline unsigned feedback_class (unsigned c) {
  return c == INTERVALS_DECIDED ? FEEDBACK_DEC : FEEDBACK_IMP;
}

// Phase 4's pre-check (see 'feedback.h').  The weights, as the arithmetic
// takes them and, per mille, as the printed names and the checks give
// them; every one is exact in binary.

static const double two_class_w[FEEDBACK_WEIGHTS] = {0.25, 0.5, 2, 4};
static const double grid_w[FEEDBACK_GRID_W] = {0.25, 0.5, 1, 2, 4};
static const double grid_a[FEEDBACK_GRID_A] = {0, 0.5, 2, 4};

static const unsigned two_class_permille[FEEDBACK_WEIGHTS] = {250, 500,
                                                              2000, 4000};
static const unsigned grid_w_permille[FEEDBACK_GRID_W] = {250, 500, 1000,
                                                          2000, 4000};
static const unsigned grid_a_permille[FEEDBACK_GRID_A] = {0, 500, 2000,
                                                          4000};

// LRB line: the factor of alpha in the step of an update of class 'c' (in
// 'intervals.h') to Q_w, min (1, w) for an implied interval and min (1,
// 1/w) for a decided one, and to Q_{w,a}, w_c / max (1, w, a) with w_dec =
// 1, w_prop = w and w_ast = a.  Each is a power of two or zero, so that the
// step is exact, and Q_{w,w} is Q_w's.

static void start_factors (feedback *fb) {
  for (unsigned c = 0; c < 3; c++) {
    double *const factor = fb->factors[c];
    for (unsigned i = 0; i < FEEDBACK_WEIGHTS; i++) {
      const double w = two_class_w[i];
      if (c == INTERVALS_DECIDED)
        factor[i] = w > 1 ? 1 / w : 1;
      else
        factor[i] = w < 1 ? w : 1;
    }
    for (unsigned i = 0; i < FEEDBACK_GRID; i++) {
      const double w = grid_w[i / FEEDBACK_GRID_A];
      const double a = grid_a[i % FEEDBACK_GRID_A];
      double largest = 1;
      if (w > largest)
        largest = w;
      if (a > largest)
        largest = a;
      const double weight = c == INTERVALS_DECIDED   ? 1
                            : c == INTERVALS_ASSERTED ? a
                                                      : w;
      factor[FEEDBACK_WEIGHTS + i] = weight / largest;
    }
  }
}

// The pending picks' records, one per pending pick on the VSIDS and LRB
// lines, reused once their picks have closed.

static feedback_record *new_record (kissat *solver, unsigned idx) {
  feedback *const fb = &solver->policy.feedback;
  assert (!fb->slot[idx]);
  unsigned res;
  if (EMPTY_STACK (fb->free)) {
    res = SIZE_STACK (fb->records);
    feedback_record record;
    memset (&record, 0, sizeof record);
    PUSH_STACK (fb->records, record);
  } else
    res = POP_STACK (fb->free);
  fb->slot[idx] = res + 1;
  return &PEEK_STACK (fb->records, res);
}

static feedback_record *record_of (feedback *fb, unsigned idx) {
  const unsigned slot = fb->slot[idx];
  assert (slot);
  return &PEEK_STACK (fb->records, slot - 1);
}

static void free_record (kissat *solver, unsigned idx) {
  feedback *const fb = &solver->policy.feedback;
  if (!fb->slot || !fb->slot[idx])
    return;
  PUSH_STACK (fb->free, fb->slot[idx] - 1);
  fb->slot[idx] = 0;
}

#ifndef NDEBUG

// The checks of assertion builds (see 'feedback.h').  An interval's rounds
// and bumped rounds against those counted at every bump round from the
// trail and the analyzed variables.

static void check_interval (kissat *solver, unsigned idx, uint64_t k,
                            uint64_t b) {
  feedback *const fb = &solver->policy.feedback;
  uint64_t *const rounds = fb->check.rounds + idx;
  uint64_t *const bumped = fb->check.bumped + idx;
  if (*rounds != k || *bumped != b)
    kissat_fatal ("feedback: interval of variable %u closed after %" PRIu64
                  " bump rounds, %" PRIu64 " with a bump, but %" PRIu64
                  " and %" PRIu64 " counted (bump round %" PRIu64 ")",
                  idx, k, b, *rounds, *bumped, solver->estimator.rounds);
  *rounds = *bumped = 0;
  fb->check.intervals++;
}

#endif

// VSIDS line: the bump of the active variable 'idx' in the current round,
// before its score, in the interval it falls in, which counts it (see
// 'kissat_interval_bumped'), by class and, if implied, by asserted or
// propagated class too.  A bump in no interval happens only in the unit
// tests, which bump outside analysis steps.

void kissat_feedback_bump (kissat *solver, unsigned idx) {
  feedback *const fb = &solver->policy.feedback;
  if (!fb->started)
    return;
  assert (!fb->chb);
  const unsigned bumped = kissat_interval_bumped (solver, idx);
  if (bumped == INTERVALS_NONE) {
    fb->m1.unobserved++;
    return;
  }
  const unsigned three = bumped & INTERVALS_CLASS;
  const unsigned c = feedback_class (three);
  const unsigned ended = !!(bumped & INTERVALS_ENDED);
  const double inc = solver->scinc;
  fb->m1.bumps[ended][c]++;
  fb->r[c][idx] += inc;
  if (three == INTERVALS_DECIDED)
    return;
  const unsigned j =
      three == INTERVALS_ASSERTED ? FEEDBACK_AST : FEEDBACK_PROP;
  fb->m1.bumps3[ended][j]++;
  fb->classes[idx].r[j] += inc;
}

// Bins and sums.

static unsigned age_bin (uint64_t age) {
  if (age >= 10 * FEEDBACK_WINDOW)
    return FEEDBACK_AGE_OLD;
  if (age >= FEEDBACK_WINDOW)
    return FEEDBACK_AGE_STALE;
  return FEEDBACK_AGE_RECENT;
}

static unsigned count_bin (double count) {
  assert (count >= 0);
  if (!(count > 0))
    return FEEDBACK_COUNT_ZERO;
  if (count < 1)
    return FEEDBACK_COUNT_BELOW1;
  if (count < 5)
    return FEEDBACK_COUNT_BELOW5;
  return FEEDBACK_COUNT_ABOVE5;
}

static unsigned calibration_bin (double p) {
  assert (p >= 0);
  const double tenths = FEEDBACK_BINS * p;
  return tenths < FEEDBACK_BINS - 1 ? (unsigned) tenths : FEEDBACK_BINS - 1;
}

// The predictors defined in each group, by line.

#define BIT(I) (1u << (I))
#define DEC_BIT BIT (FEEDBACK_PREDICT_DEC)
#define IMP_BIT BIT (FEEDBACK_PREDICT_IMP)
#define ALL_BIT BIT (FEEDBACK_PREDICT_ALL)
#define CONST_BIT BIT (FEEDBACK_PREDICT_CONST)

static const unsigned group_mask[2][FEEDBACK_GROUPS] = {
    // VSIDS: p_all is undefined exactly when both counts are zero.
    {DEC_BIT | IMP_BIT | ALL_BIT | CONST_BIT, DEC_BIT | ALL_BIT | CONST_BIT,
     IMP_BIT | ALL_BIT | CONST_BIT, CONST_BIT, 0},
    // CHB: CHB's own Q is always defined.
    {DEC_BIT | IMP_BIT | ALL_BIT | CONST_BIT, DEC_BIT | ALL_BIT | CONST_BIT,
     IMP_BIT | ALL_BIT | CONST_BIT, ALL_BIT | CONST_BIT, 0},
};

static unsigned group_of (const double *p, bool chb) {
  unsigned res;
  if (isnan (p[FEEDBACK_PREDICT_CONST]))
    res = FEEDBACK_GROUP_NO_CONST;
  else {
    const bool dec = !isnan (p[FEEDBACK_PREDICT_DEC]);
    const bool imp = !isnan (p[FEEDBACK_PREDICT_IMP]);
    res = dec && imp ? FEEDBACK_GROUP_BOTH
          : dec      ? FEEDBACK_GROUP_NO_IMP
          : imp      ? FEEDBACK_GROUP_NO_DEC
                     : FEEDBACK_GROUP_NEITHER;
#ifndef NDEBUG
    for (unsigned i = 0; i < FEEDBACK_PREDICTORS; i++)
      assert (!isnan (p[i]) == !!(group_mask[chb][res] & BIT (i)));
#endif
  }
  (void) chb;
  return res;
}

// An interval of 'k' rounds, 'b' of them with a bump, and the errors of
// the predictors in 'mask'.

static void add_interval (feedback_sums *sums, const double *p,
                          unsigned mask, uint64_t k, uint64_t b) {
  assert (k), assert (b <= k);
  sums->n++;
  sums->k += k;
  sums->b += b;
  const double rate = (double) b / k;
  for (unsigned i = 0; i < FEEDBACK_PREDICTORS; i++) {
    if (!(mask & BIT (i)))
      continue;
    const double q = p[i], miss = 1 - q, error = rate - q;
    sums->round[i] += b * miss * miss + (k - b) * q * q;
    sums->interval[i] += error * error;
  }
}

// A decided payment of 'reward', and the errors of the predictors in
// 'mask'.

static void add_payment (feedback_sums *sums, const double *p,
                         unsigned mask, double reward) {
  sums->n++;
  sums->r += reward;
  for (unsigned i = 0; i < FEEDBACK_PREDICTORS; i++) {
    if (!(mask & BIT (i)))
      continue;
    const double error = reward - p[i];
    sums->interval[i] += error * error;
  }
}

// The pre-check's predictors 'v' of an event: each one that is defined
// scores the event, an interval of 'k' rounds, 'b' of them with a bump
// (VSIDS), or a reward (LRB), and counts it.

static void add_extra (feedback_extra *sums, const double *v,
                       unsigned count, uint64_t k, uint64_t b) {
  assert (k), assert (b <= k);
  const double rate = (double) b / k;
  for (unsigned i = 0; i < count; i++) {
    const double q = v[i];
    if (isnan (q))
      continue;
    const double miss = 1 - q, error = rate - q;
    sums->n[i]++;
    sums->round[i] += b * miss * miss + (k - b) * q * q;
    sums->interval[i] += error * error;
  }
}

static void add_extra_payment (feedback_extra *sums, const double *v,
                               unsigned count, double reward) {
  for (unsigned i = 0; i < count; i++) {
    const double q = v[i];
    if (isnan (q))
      continue;
    const double error = reward - q;
    sums->n[i]++;
    sums->interval[i] += error * error;
  }
}

// VSIDS line: the event, closed with k >= 1, joins the cells of the yield
// predictors with its rate b / k.

static void add_cells (feedback_cells *cells, unsigned bin_y,
                       unsigned bin_p, double rate) {
  assert (bin_y < FEEDBACK_YIELDS), assert (bin_p <= FEEDBACK_BINS);
  cells->n_y[bin_y]++;
  cells->y[bin_y] += rate;
  if (bin_p == FEEDBACK_BINS)
    return;
  cells->n_p[bin_p]++;
  cells->p[bin_p] += rate;
  cells->n_yp[bin_y][bin_p]++;
  cells->yp[bin_y][bin_p] += rate;
}

// VSIDS line: the pre-check's predictors of a pick of 'idx' (see
// 'feedback.h'), from its sums and the cells of the yield predictors,
// with p_1 and the bin of 'Y_v' that M1 and M3 freeze.  The three yield
// predictors are defined together, where B_Yp is, with p_1 beside them.

static void freeze_vsids (kissat *solver, unsigned idx,
                          feedback_record *record, double p_1,
                          unsigned bin_y) {
  feedback *const fb = &solver->policy.feedback;
  const feedback_classes *const c = fb->classes + idx;
  const double n_dec = fb->n[FEEDBACK_DEC][idx];
  const double n_imp = fb->n[FEEDBACK_IMP][idx];
  const double r_dec = fb->r[FEEDBACK_DEC][idx];
  const double r_imp = fb->r[FEEDBACK_IMP][idx];
  const double n_ast = c->n[FEEDBACK_AST], n_prop = c->n[FEEDBACK_PROP];
  const double r_ast = c->r[FEEDBACK_AST], r_prop = c->r[FEEDBACK_PROP];
  double *const v = record->extra;
  v[FEEDBACK_V_AST] = n_ast > 0 ? r_ast / n_ast : NAN;
  v[FEEDBACK_V_PROP] = n_prop > 0 ? r_prop / n_prop : NAN;
  for (unsigned i = 0; i < FEEDBACK_WEIGHTS; i++) {
    const double w = two_class_w[i], n = n_dec + w * n_imp;
    v[FEEDBACK_V_W + i] = n > 0 ? (r_dec + w * r_imp) / n : NAN;
  }
  for (unsigned i = 0; i < FEEDBACK_GRID; i++) {
    const double w = grid_w[i / FEEDBACK_GRID_A];
    const double a = grid_a[i % FEEDBACK_GRID_A];
    const double n = n_dec + a * n_ast + w * n_prop;
    v[FEEDBACK_V_GRID + i] =
        n > 0 ? (r_dec + a * r_ast + w * r_prop) / n : NAN;
  }
  const double rate_dec = c->rates[FEEDBACK_DEC];
  const double rate_imp = c->rates[FEEDBACK_IMP];
  const double weight_dec = c->weights[FEEDBACK_DEC];
  const double weight_imp = c->weights[FEEDBACK_IMP];
  const double weights = weight_dec + weight_imp;
  v[FEEDBACK_V_MEAN] = weight_dec > 0 ? rate_dec / weight_dec : NAN;
  v[FEEDBACK_V_MEAN + 1] =
      weights > 0 ? (rate_dec + rate_imp) / weights : NAN;
  v[FEEDBACK_V_MEAN + 2] = weight_imp > 0 ? rate_imp / weight_imp : NAN;
  const unsigned bin_p =
      isnan (p_1) ? FEEDBACK_BINS : calibration_bin (p_1);
  record->bin_y = bin_y;
  record->bin_p = bin_p;
  const feedback_cells *const cells = &fb->m1.cells;
  double *const bins = v + FEEDBACK_V_BIN;
  if (bin_p < FEEDBACK_BINS && cells->n_yp[bin_y][bin_p]) {
    bins[0] = cells->y[bin_y] / cells->n_y[bin_y];
    bins[1] = cells->p[bin_p] / cells->n_p[bin_p];
    bins[2] = cells->yp[bin_y][bin_p] / cells->n_yp[bin_y][bin_p];
    bins[3] = p_1;
  } else
    bins[0] = bins[1] = bins[2] = bins[3] = NAN;
}

// LRB line: M1's four and the pre-check's predictors of a pick of 'idx',
// from its ERWAs, each defined once an update of a class with a positive
// step has reached it.

static void freeze_lrb (kissat *solver, unsigned idx,
                        feedback_record *record) {
  feedback *const fb = &solver->policy.feedback;
  const feedback_erwas *const e = fb->erwas + idx;
  const unsigned dec = e->updates[FEEDBACK_Q_DEC];
  const unsigned ast = e->updates[FEEDBACK_Q_AST];
  const unsigned prop = e->updates[FEEDBACK_Q_PROP];
  double *const p = record->base;
  p[FEEDBACK_PREDICT_DEC] = dec ? e->q[FEEDBACK_Q_DEC] : NAN;
  p[FEEDBACK_PREDICT_IMP] = ast || prop ? e->q[FEEDBACK_Q_IMP] : NAN;
  p[FEEDBACK_PREDICT_ALL] = solver->score[idx];
  p[FEEDBACK_PREDICT_CONST] =
      fb->m1.sum_n ? fb->m1.sum_r / fb->m1.sum_n : NAN;
  double *const v = record->extra;
  v[FEEDBACK_L_AST] = ast ? e->q[FEEDBACK_Q_AST] : NAN;
  v[FEEDBACK_L_PROP] = prop ? e->q[FEEDBACK_Q_PROP] : NAN;
  const bool any = dec || ast || prop;
  for (unsigned i = 0; i < FEEDBACK_WEIGHTS; i++)
    v[FEEDBACK_L_W + i] = any ? e->w[i] : NAN;
  for (unsigned i = 0; i < FEEDBACK_GRID; i++) {
    const bool asserted = ast && grid_a[i % FEEDBACK_GRID_A] > 0;
    v[FEEDBACK_L_GRID + i] = dec || prop || asserted ? e->grid[i] : NAN;
  }
  for (unsigned i = FEEDBACK_L_PREDICTORS; i < FEEDBACK_EXTRA; i++)
    v[i] = NAN;
}

#ifndef NDEBUG

// Check (d) of the pre-check: the predictors of a pick computed a second
// time, by code of its own, with the weights per mille and its own bins:
// on the VSIDS line from the per-variable sums and the shadow tables of the
// cells, on the LRB line from the ERWAs that the check updates itself, and
// the definedness of the weighted ones from the steps' factors.  At the
// event the frozen predictors must equal them bitwise.

static void check_freeze_vsids (kissat *solver, unsigned idx,
                                feedback_record *record) {
  feedback *const fb = &solver->policy.feedback;
  double *const base = record->check_base;
  double *const extra = record->check_extra;
  const double nd = fb->n[FEEDBACK_DEC][idx], ni = fb->n[FEEDBACK_IMP][idx];
  const double rd = fb->r[FEEDBACK_DEC][idx], ri = fb->r[FEEDBACK_IMP][idx];
  base[FEEDBACK_PREDICT_DEC] = nd > 0 ? rd / nd : NAN;
  base[FEEDBACK_PREDICT_IMP] = ni > 0 ? ri / ni : NAN;
  base[FEEDBACK_PREDICT_ALL] = nd + ni > 0 ? (rd + ri) / (nd + ni) : NAN;
  base[FEEDBACK_PREDICT_CONST] =
      fb->m1.sum_k ? (double) fb->m1.sum_b / fb->m1.sum_k : NAN;
  const feedback_classes *const c = fb->classes + idx;
  const double na = c->n[FEEDBACK_AST], np = c->n[FEEDBACK_PROP];
  const double ra = c->r[FEEDBACK_AST], rp = c->r[FEEDBACK_PROP];
  extra[FEEDBACK_V_AST] = na > 0 ? ra / na : NAN;
  extra[FEEDBACK_V_PROP] = np > 0 ? rp / np : NAN;
  for (unsigned i = 0; i < FEEDBACK_WEIGHTS; i++) {
    const double w = two_class_permille[i] / 1000.0;
    const double d = nd + w * ni;
    extra[FEEDBACK_V_W + i] = d > 0 ? (rd + w * ri) / d : NAN;
  }
  unsigned i = FEEDBACK_V_GRID;
  for (unsigned j = 0; j < FEEDBACK_GRID_W; j++)
    for (unsigned l = 0; l < FEEDBACK_GRID_A; l++, i++) {
      const double w = grid_w_permille[j] / 1000.0;
      const double a = grid_a_permille[l] / 1000.0;
      const double d = nd + a * na + w * np;
      extra[i] = d > 0 ? (rd + a * ra + w * rp) / d : NAN;
    }
  assert (i == FEEDBACK_V_MEAN);
  const double sd = c->rates[FEEDBACK_DEC], si = c->rates[FEEDBACK_IMP];
  const double wd = c->weights[FEEDBACK_DEC], wi = c->weights[FEEDBACK_IMP];
  extra[FEEDBACK_V_MEAN] = wd > 0 ? sd / wd : NAN;
  extra[FEEDBACK_V_MEAN + 1] = wd + wi > 0 ? (sd + si) / (wd + wi) : NAN;
  extra[FEEDBACK_V_MEAN + 2] = wi > 0 ? si / wi : NAN;
  const double y = fb->yield[idx];
  const unsigned bin_y = y >= 64  ? FEEDBACK_YIELD_ABOVE64
                         : y >= 16 ? FEEDBACK_YIELD_BELOW64
                         : y >= 4  ? FEEDBACK_YIELD_BELOW16
                         : y >= 2  ? FEEDBACK_YIELD_BELOW4
                         : y > 0   ? FEEDBACK_YIELD_BELOW2
                                   : FEEDBACK_YIELD_NONE;
  const double p_1 = base[FEEDBACK_PREDICT_ALL];
  unsigned bin_p = FEEDBACK_BINS;
  if (!isnan (p_1)) {
    const double tenths = 10 * p_1;
    bin_p = tenths >= 9 ? 9 : (unsigned) tenths;
  }
  record->check_y = bin_y;
  record->check_p = bin_p;
  const feedback_cells *const cells = &fb->check.cells;
  double *const bins = extra + FEEDBACK_V_BIN;
  if (bin_p == FEEDBACK_BINS || !cells->n_yp[bin_y][bin_p])
    bins[0] = bins[1] = bins[2] = bins[3] = NAN;
  else {
    bins[0] = cells->y[bin_y] / cells->n_y[bin_y];
    bins[1] = cells->p[bin_p] / cells->n_p[bin_p];
    bins[2] = cells->yp[bin_y][bin_p] / cells->n_yp[bin_y][bin_p];
    bins[3] = p_1;
  }
}

static void check_freeze_lrb (kissat *solver, unsigned idx,
                              feedback_record *record) {
  feedback *const fb = &solver->policy.feedback;
  const feedback_erwas *const e = fb->check.shadow + idx;
  double *const base = record->check_base;
  double *const extra = record->check_extra;
  const unsigned *const updates = e->updates;
  base[FEEDBACK_PREDICT_DEC] =
      updates[FEEDBACK_Q_DEC] ? e->q[FEEDBACK_Q_DEC] : NAN;
  base[FEEDBACK_PREDICT_IMP] =
      updates[FEEDBACK_Q_AST] + updates[FEEDBACK_Q_PROP]
          ? e->q[FEEDBACK_Q_IMP]
          : NAN;
  base[FEEDBACK_PREDICT_ALL] = solver->score[idx];
  base[FEEDBACK_PREDICT_CONST] =
      fb->check.sum_n ? fb->check.sum_r / fb->check.sum_n : NAN;
  extra[FEEDBACK_L_AST] =
      updates[FEEDBACK_Q_AST] ? e->q[FEEDBACK_Q_AST] : NAN;
  extra[FEEDBACK_L_PROP] =
      updates[FEEDBACK_Q_PROP] ? e->q[FEEDBACK_Q_PROP] : NAN;
  for (unsigned i = 0; i < FEEDBACK_WEIGHTS + FEEDBACK_GRID; i++) {
    bool defined = false;
    for (unsigned c = 0; c < 3; c++)
      if (updates[c] && fb->factors[c][i] > 0)
        defined = true;
    const double q = i < FEEDBACK_WEIGHTS ? e->w[i]
                                          : e->grid[i - FEEDBACK_WEIGHTS];
    extra[FEEDBACK_L_W + i] = defined ? q : NAN;
  }
  for (unsigned i = FEEDBACK_L_PREDICTORS; i < FEEDBACK_EXTRA; i++)
    extra[i] = NAN;
}

// At the event: the frozen predictors ('base' M1's four) against the
// check's, NaN for an undefined one, and on the VSIDS line the cells.

static bool same_predictor (double a, double b) {
  return isnan (a) ? isnan (b) : kissat_same_double (a, b);
}

static void check_record (kissat *solver, unsigned idx, const double *base,
                          const feedback_record *record) {
  feedback *const fb = &solver->policy.feedback;
  for (unsigned i = 0; i < FEEDBACK_PREDICTORS; i++)
    if (!same_predictor (base[i], record->check_base[i]))
      kissat_fatal ("feedback: M1's predictor %u of the pick of variable "
                    "%u frozen as %.17g, but the check gives %.17g",
                    i, idx, base[i], record->check_base[i]);
  for (unsigned i = 0; i < FEEDBACK_EXTRA; i++)
    if (!same_predictor (record->extra[i], record->check_extra[i]))
      kissat_fatal ("feedback: the pre-check's predictor %u of the pick of "
                    "variable %u frozen as %.17g, but the check gives "
                    "%.17g",
                    i, idx, record->extra[i], record->check_extra[i]);
  if (!fb->lrb && (record->bin_y != record->check_y ||
                   record->bin_p != record->check_p))
    kissat_fatal ("feedback: the pick of variable %u in the cell (%u, %u) "
                  "of the yield predictors, but the check gives (%u, %u)",
                  idx, record->bin_y, record->bin_p, record->check_y,
                  record->check_p);
  fb->check.predictors++;
}

#endif

// VSIDS line: the pre-check's part of the event of 'idx', in M1's group
// 'group', of 'k' rounds and 'b' bumped ones.  With k >= 1 its predictors
// score it, but in the group without p_const, p_ast and p_prop add it to
// their calibration bins in the main group, and it joins the cells of the
// yield predictors.  Its record is freed.

static void close_vsids_event (kissat *solver, unsigned idx,
                               unsigned group, uint64_t k, uint64_t b) {
  feedback *const fb = &solver->policy.feedback;
  const feedback_record *const record = record_of (fb, idx);
#ifndef NDEBUG
  check_record (solver, idx, fb->frozen + FEEDBACK_PREDICTORS * idx,
                record);
#endif
  if (k) {
    const double *const v = record->extra;
    if (group != FEEDBACK_GROUP_NO_CONST)
      add_extra (fb->m1.extra + group, v, FEEDBACK_V_PREDICTORS, k, b);
    if (group == FEEDBACK_GROUP_BOTH)
      for (unsigned j = 0; j < 2; j++) {
        const double q = v[FEEDBACK_V_AST + j];
        if (!isnan (q))
          add_interval (&fb->m1.calibration3[j][calibration_bin (q)], v,
                        0, k, b);
      }
    const double rate = (double) b / k;
    add_cells (&fb->m1.cells, record->bin_y, record->bin_p, rate);
#ifndef NDEBUG
    feedback_cells *const cells = &fb->check.cells;
    const unsigned y = record->check_y, p = record->check_p;
    cells->n_y[y] += 1, cells->y[y] += rate;
    if (p < FEEDBACK_BINS) {
      cells->n_p[p] += 1, cells->p[p] += rate;
      cells->n_yp[y][p] += 1, cells->yp[y][p] += rate;
    }
#endif
  }
  free_record (solver, idx);
}

// LRB line: the event of 'idx', with LRB's 'reward' if 'paid', in M1's
// group of its four predictors, their calibration bins and those of Q_ast
// and Q_prop in the main group, and the pre-check's predictors; without a
// reward it is counted apart.  Its record is freed.

static void close_lrb_event (kissat *solver, unsigned idx, bool paid,
                             double reward) {
  feedback *const fb = &solver->policy.feedback;
  const feedback_record *const record = record_of (fb, idx);
  const double *const p = record->base;
#ifndef NDEBUG
  check_record (solver, idx, p, record);
#endif
  fb->m1.events++;
  if (!paid)
    fb->m1.zero++;
  else {
    const unsigned group = group_of (p, true);
    add_payment (fb->m1.group + group, p, group_mask[1][group], reward);
    if (group == FEEDBACK_GROUP_BOTH) {
      for (unsigned d = 0; d < 2; d++) {
        const double q = p[d ? FEEDBACK_PREDICT_IMP : FEEDBACK_PREDICT_DEC];
        add_payment (&fb->m1.calibration[d][calibration_bin (q)], p, 0,
                     reward);
      }
      for (unsigned j = 0; j < 2; j++) {
        const double q = record->extra[FEEDBACK_L_AST + j];
        if (!isnan (q))
          add_payment (&fb->m1.calibration3[j][calibration_bin (q)], p, 0,
                       reward);
      }
    }
    if (group != FEEDBACK_GROUP_NO_CONST)
      add_extra_payment (fb->m1.extra + group, record->extra,
                         FEEDBACK_L_PREDICTORS, reward);
  }
  free_record (solver, idx);
}

// LRB line: an update of Q of 'idx' by an interval of class 'c' with
// 'reward' at step size 'alpha', as LRB's: the ERWA of its class, Q_imp if
// it is implied, and the weighted ones at their steps.  Assertion builds
// update Q_1 and the check's ERWAs, with steps of their own, and hold Q_1
// to LRB's Q.

static inline double erwa (double q, double step, double reward) {
  return (1 - step) * q + step * reward;
}

#ifndef NDEBUG

static void check_update_erwas (kissat *solver, unsigned idx, unsigned c,
                                double reward, double alpha) {
  feedback *const fb = &solver->policy.feedback;
  double *const q1 = fb->check.q1 + idx;
  *q1 = (1 - alpha) * *q1 + alpha * reward;
  if (!kissat_same_double (*q1, solver->score[idx]))
    kissat_fatal ("feedback: Q_1 %.17g of variable %u differs from LRB's "
                  "Q %.17g",
                  *q1, idx, solver->score[idx]);
  fb->check.erwas++;
  feedback_erwas *const e = fb->check.shadow + idx;
  e->q[c] = (1 - alpha) * e->q[c] + alpha * reward;
  if (c != INTERVALS_DECIDED)
    e->q[FEEDBACK_Q_IMP] =
        (1 - alpha) * e->q[FEEDBACK_Q_IMP] + alpha * reward;
  e->updates[c]++;
  for (unsigned i = 0; i < FEEDBACK_WEIGHTS; i++) {
    const unsigned w = two_class_permille[i];
    const double factor = c == INTERVALS_DECIDED
                              ? 1000.0 / (w > 1000 ? w : 1000)
                              : (w < 1000 ? w : 1000) / 1000.0;
    const double step = alpha * factor;
    e->w[i] = (1 - step) * e->w[i] + step * reward;
  }
  unsigned i = 0;
  for (unsigned j = 0; j < FEEDBACK_GRID_W; j++)
    for (unsigned l = 0; l < FEEDBACK_GRID_A; l++, i++) {
      const unsigned w = grid_w_permille[j], a = grid_a_permille[l];
      const unsigned weight = c == INTERVALS_DECIDED   ? 1000
                              : c == INTERVALS_ASSERTED ? a
                                                        : w;
      unsigned largest = w > a ? w : a;
      if (largest < 1000)
        largest = 1000;
      const double step = alpha * ((double) weight / largest);
      if (step > 0)
        e->grid[i] = (1 - step) * e->grid[i] + step * reward;
    }
  if (c == INTERVALS_DECIDED)
    fb->check.sum_n++, fb->check.sum_r += reward;
}

#endif

static void update_erwas (kissat *solver, unsigned idx, unsigned c,
                          double reward, double alpha) {
  feedback *const fb = &solver->policy.feedback;
  feedback_erwas *const e = fb->erwas + idx;
  assert (c <= INTERVALS_PROPAGATED);
  const unsigned q = c == INTERVALS_DECIDED   ? FEEDBACK_Q_DEC
                     : c == INTERVALS_ASSERTED ? FEEDBACK_Q_AST
                                               : FEEDBACK_Q_PROP;
  e->q[q] = erwa (e->q[q], alpha, reward);
  e->updates[q]++;
  if (q == FEEDBACK_Q_DEC)
    fb->m1.intervals[FEEDBACK_DEC]++;
  else {
    e->q[FEEDBACK_Q_IMP] = erwa (e->q[FEEDBACK_Q_IMP], alpha, reward);
    fb->m1.intervals[FEEDBACK_IMP]++;
    fb->m1.intervals3[q == FEEDBACK_Q_AST ? FEEDBACK_AST : FEEDBACK_PROP]++;
  }
  const double *const factor = fb->factors[c];
  for (unsigned i = 0; i < FEEDBACK_WEIGHTS; i++)
    e->w[i] = erwa (e->w[i], alpha * factor[i], reward);
  for (unsigned i = 0; i < FEEDBACK_GRID; i++) {
    const double step = alpha * factor[FEEDBACK_WEIGHTS + i];
    if (step > 0)
      e->grid[i] = erwa (e->grid[i], step, reward);
  }
#ifndef NDEBUG
  check_update_erwas (solver, idx, c, reward, alpha);
#endif
}

// M2: a pending pick that was not followed by its decision, which happens
// only when the unit tests pick without deciding, is void: it is taken back
// from the picks, so that picks stay outcomes plus open picks.  In a run
// every pick is decided at once, and the analysis checks that the picks
// of both kinds are the policy's search picks ('policy-picks').

static void void_pick (feedback *fb, unsigned state) {
  assert (state & FEEDBACK_PENDING);
  const unsigned kind = (state >> FEEDBACK_KIND_SHIFT) & 1;
  assert (fb->m2.picks[kind]);
  fb->m2.picks[kind]--;
}

// M2: the outcome of a pending pick, 'k' and 'b' of its interval (VSIDS)
// or its payment 'reward' (CHB).

static void add_outcome (feedback *fb, unsigned state, uint64_t k,
                         uint64_t b, double reward) {
  assert (state & FEEDBACK_PENDING);
  const unsigned kind = (state >> FEEDBACK_KIND_SHIFT) & 1;
  const unsigned age = (state >> FEEDBACK_AGE_SHIFT) & 3;
  const unsigned count = (state >> FEEDBACK_COUNT_SHIFT) & 3;
  feedback_sums *const sums[2] = {&fb->m2.age[kind][age],
                                  &fb->m2.count[kind][count]};
  for (unsigned i = 0; i < 2; i++) {
    feedback_sums *const s = sums[i];
    s->n++;
    s->k += k;
    s->b += b;
    s->bumped += b > 0;
    s->r += reward;
  }
}

// M3: the bin of 'Y_v', which is at least one once defined.

static unsigned yield_bin (double yield) {
  if (!(yield > 0))
    return FEEDBACK_YIELD_NONE;
  if (yield < 2)
    return FEEDBACK_YIELD_BELOW2;
  if (yield < 4)
    return FEEDBACK_YIELD_BELOW4;
  if (yield < 16)
    return FEEDBACK_YIELD_BELOW16;
  if (yield < 64)
    return FEEDBACK_YIELD_BELOW64;
  return FEEDBACK_YIELD_ABOVE64;
}

// M3: the pending pick of 'idx' is done with, its 'y_prop' and 'y_obs'
// reset.  A pick taken back is taken back from M3's picks as well.

static void reset_yield (feedback *fb, unsigned idx) {
  fb->propagated[idx] = 0;
  fb->observed[idx] = 0;
  if (fb->chb)
    fb->reward[idx] = 0;
  if (fb->yielding == idx + 1)
    fb->yielding = 0;
#ifndef NDEBUG
  fb->check.propagated[idx] = 0;
  fb->check.observed[idx] = 0;
#endif
}

static void void_yield (feedback *fb, unsigned idx, unsigned state) {
  assert (state & FEEDBACK_YIELD);
  const unsigned kind = (state >> FEEDBACK_KIND_SHIFT) & 1;
  assert (fb->m3.picks[kind]);
  fb->m3.picks[kind]--;
  reset_yield (fb, idx);
}

#ifndef NDEBUG

// Check (c) of M3: 'y_prop' and 'y_obs' against their shadow sums, counted
// from the trail.

static void check_yield (kissat *solver, unsigned idx, unsigned prop,
                         uint64_t obs) {
  feedback *const fb = &solver->policy.feedback;
  const unsigned counted_prop = fb->check.propagated[idx];
  const uint64_t counted_obs = fb->check.observed[idx];
  if (counted_prop != prop || counted_obs != obs)
    kissat_fatal ("feedback: pick of variable %u closed with y_prop %u "
                  "and y_obs %" PRIu64 ", but %u and %" PRIu64
                  " counted from the trail",
                  idx, prop, obs, counted_prop, counted_obs);
  fb->check.yields++;
}

#endif

// M3: the interval of the pending pick of 'idx' closed, with M2's outcome,
// 'k' and 'b' (VSIDS) or the payment 'reward' (CHB): its sums by age, by
// count and by the bin of 'Y_v' frozen at the pick, and for a uniform pick
// by that bin crossed with stale against recent.  Then 'Y_v' takes its
// 'y_prop', or starts from it.  A pick whose propagation's end was not
// seen, which only the unit tests make, is taken back.

static void add_yield (kissat *solver, unsigned idx, unsigned state,
                       uint64_t k, uint64_t b, double reward) {
  feedback *const fb = &solver->policy.feedback;
  assert (state & FEEDBACK_YIELD);
  const unsigned prop = fb->propagated[idx];
  const uint64_t obs = fb->observed[idx];
  if (!prop) {
    void_yield (fb, idx, state);
    return;
  }
#ifndef NDEBUG
  check_yield (solver, idx, prop, obs);
#endif
  reset_yield (fb, idx);
  const unsigned kind = (state >> FEEDBACK_KIND_SHIFT) & 1;
  const unsigned age = (state >> FEEDBACK_AGE_SHIFT) & 3;
  const unsigned count = (state >> FEEDBACK_COUNT_SHIFT) & 3;
  const unsigned bin = (state >> FEEDBACK_YIELD_SHIFT) & 7;
  assert (bin < FEEDBACK_YIELDS);
  feedback_yields *sums[4] = {&fb->m3.age[kind][age],
                              &fb->m3.count[kind][count],
                              &fb->m3.yield[kind][bin], 0};
  if (kind == FEEDBACK_UNIFORM)
    sums[3] = &fb->m3.crossed[age == FEEDBACK_AGE_RECENT][bin];
  for (unsigned i = 0; i < 4; i++) {
    feedback_yields *const s = sums[i];
    if (!s)
      continue;
    s->n++;
    s->k += k;
    s->b += b;
    s->bumped += b > 0;
    s->r += reward;
    s->prop += prop;
    s->obs += obs;
  }
  double *const yield = fb->yield + idx;
  const double alpha = FEEDBACK_YIELD_ALPHA;
  *yield = *yield > 0 ? (1 - alpha) * *yield + alpha * prop : prop;
}

// M3: when an analysis step starts, before its backtracks, every open
// pick's level with its variables now, and their trail segments, to be
// added when the step's analyzed variables are bumped or recorded.  A
// level's variables are its frame's count, which chronological
// backtracking may leave below its trail segment, or above.  Assertion
// builds count every level's variables from the trail and hold the
// frames' counts to them.

static void stage_yields (kissat *solver) {
  feedback *const fb = &solver->policy.feedback;
  CLEAR_STACK (fb->staged);
  const unsigned level = solver->level;
  const unsigned size = SIZE_ARRAY (solver->trail);
  const uint16_t *const state = fb->state;
  uint64_t levels = 0, segments = 0;
  for (unsigned l = 1; l <= level; l++) {
    const frame *const frame = &FRAME (l);
    const unsigned idx = IDX (frame->decision);
    if (!(state[idx] & FEEDBACK_YIELD))
      continue;
    assert (solver->assigned[idx].level == l);
    const unsigned end = l < level ? FRAME (l + 1).trail : size;
    assert (frame->trail <= end);
    PUSH_STACK (fb->staged, idx);
    PUSH_STACK (fb->staged, frame->assigned);
    levels += frame->assigned;
    segments += end - frame->trail;
  }
  fb->staged_levels = levels;
  fb->staged_segments = segments;
#ifndef NDEBUG
  unsigneds *const counted = &fb->check.levels;
  CLEAR_STACK (*counted);
  for (unsigned l = 0; l <= level; l++)
    PUSH_STACK (*counted, 0);
  unsigned *const count = BEGIN_STACK (*counted);
  const assigned *const assigned = solver->assigned;
  for (all_stack (unsigned, lit, solver->trail)) {
    const unsigned l = assigned[IDX (lit)].level;
    assert (l <= level);
    count[l]++;
  }
  CLEAR_STACK (fb->check.staged);
  for (unsigned l = 1; l <= level; l++) {
    const frame *const frame = &FRAME (l);
    if (count[l] != frame->assigned)
      kissat_fatal ("feedback: %u variables assigned at level %u, %u "
                    "counted from the trail",
                    frame->assigned, l, count[l]);
    fb->check.steps++;
    const unsigned idx = IDX (frame->decision);
    if (!(state[idx] & FEEDBACK_YIELD))
      continue;
    PUSH_STACK (fb->check.staged, idx);
    PUSH_STACK (fb->check.staged, count[l]);
  }
#endif
}

// M3: a step's analyzed variables are bumped (VSIDS) or recorded as CHB's
// participants (CHB), so the step is a conflict of every open pick's
// interval, which observes its level's variables taken when the step
// started.  Outside a step, which only the unit tests make, they are
// taken now.  The step is one more of the locality key's 'c' ('steps', on
// the VSIDS line the bump round); M3 does not run on the LRB line.

void kissat_feedback_observe (kissat *solver) {
  feedback *const fb = &solver->policy.feedback;
  if (!fb->started)
    return;
  assert (solver->stable);
  fb->steps++;
  if (fb->lrb)
    return;
  if (!solver->policy.intervals.analyzing)
    stage_yields (solver);
  uint64_t *const observed = fb->observed;
  const unsigned *const end = END_STACK (fb->staged);
  for (const unsigned *p = BEGIN_STACK (fb->staged); p != end; p += 2)
    observed[p[0]] += p[1];
  CLEAR_STACK (fb->staged);
  fb->m3.levels += fb->staged_levels;
  fb->m3.segments += fb->staged_segments;
  fb->staged_levels = fb->staged_segments = 0;
#ifndef NDEBUG
  uint64_t *const counted = fb->check.observed;
  const unsigned *const check_end = END_STACK (fb->check.staged);
  for (const unsigned *p = BEGIN_STACK (fb->check.staged); p != check_end;
       p += 2)
    counted[p[0]] += p[1];
  CLEAR_STACK (fb->check.staged);
#endif
}

// M3: a search propagation ends.  If it is the one that follows a pick,
// the pick's 'y_prop' is its level's trail segment, which holds only that
// level, since every variable it assigned has the decision's level.

void kissat_feedback_propagated (kissat *solver) {
  feedback *const fb = &solver->policy.feedback;
  const unsigned yielding = fb->yielding;
  if (!yielding)
    return;
  fb->yielding = 0;
  const unsigned idx = yielding - 1;
  assert (fb->started);
  assert (solver->stable);
  assert (fb->state[idx] & FEEDBACK_YIELD);
  const unsigned level = solver->level;
  const frame *const frame = &FRAME (level);
  assert (IDX (frame->decision) == idx);
  assert (solver->assigned[idx].level == level);
  const unsigned prop = SIZE_ARRAY (solver->trail) - frame->trail;
  assert (prop == frame->assigned);
  assert (prop >= 1);
  fb->propagated[idx] = prop;
#ifndef NDEBUG
  unsigned counted = 0;
  const assigned *const assigned = solver->assigned;
  for (all_stack (unsigned, lit, solver->trail))
    counted += assigned[IDX (lit)].level == level;
  fb->check.propagated[idx] = counted;
#endif
}

// VSIDS line: the interval of the active variable 'idx', of class 'three'
// in 'intervals.h', closes (see 'intervals.h'): at its unassignment in
// stable mode, after the bump round of the analysis step whose backtrack
// ended it, or when stable mode is left.  Its rounds go to the count of
// its class, decided or implied, as UCB's do, and an implied interval's to
// that of its asserted or propagated class too; with a round its rate goes
// to the sums of E_w; a decided interval adds to the sums of p_const; the
// interval of a pending pick is an event of M1, of the pre-check, and the
// pick's outcome in M2 and M3.

static void close_interval (kissat *solver, unsigned idx, unsigned three) {
  feedback *const fb = &solver->policy.feedback;
  const intervals *const intervals = &solver->policy.intervals;
  assert (!fb->chb);
  assert (intervals->rounds);
  const unsigned c = feedback_class (three);
  const double inc = solver->scinc;
  const double rounds = (inc - intervals->opened[idx]) / (fb->growth - 1);
  fb->n[c][idx] += rounds;
  feedback_classes *const classes = fb->classes + idx;
  if (three != INTERVALS_DECIDED) {
    const unsigned j =
        three == INTERVALS_ASSERTED ? FEEDBACK_AST : FEEDBACK_PROP;
    classes->n[j] += rounds;
    fb->m1.intervals3[j]++;
  }
  const uint64_t round = solver->estimator.rounds;
  assert (intervals->start[idx] <= round);
  const uint64_t k = round - intervals->start[idx];
  const uint64_t b = intervals->bumps[idx];
  assert (b <= k);
#ifndef NDEBUG
  check_interval (solver, idx, k, b);
#endif
  fb->m1.intervals[c]++;
  if (k) {
    fb->last[idx] = round;
    classes->rates[c] += inc * ((double) b / k);
    classes->weights[c] += inc;
  }
  if (c == FEEDBACK_DEC) {
    fb->m1.sum_k += k;
    fb->m1.sum_b += b;
  }
  const unsigned state = fb->state[idx];
  assert (!(state & FEEDBACK_YIELD) == !(state & FEEDBACK_PENDING));
  if (state & FEEDBACK_PENDING && c != FEEDBACK_DEC) {
    void_pick (fb, state);
    void_yield (fb, idx, state);
    free_record (solver, idx);
  } else if (state & FEEDBACK_PENDING) {
    fb->m1.events++;
    const double *const p = fb->frozen + FEEDBACK_PREDICTORS * idx;
    unsigned group = FEEDBACK_GROUP_NO_CONST;
    if (!k)
      fb->m1.zero++;
    else {
      group = group_of (p, false);
      add_interval (fb->m1.group + group, p, group_mask[0][group], k, b);
      if (group == FEEDBACK_GROUP_BOTH)
        for (unsigned d = 0; d < 2; d++) {
          const double q = p[d ? FEEDBACK_PREDICT_IMP : FEEDBACK_PREDICT_DEC];
          add_interval (&fb->m1.calibration[d][calibration_bin (q)], p, 0,
                        k, b);
        }
    }
    close_vsids_event (solver, idx, group, k, b);
    add_outcome (fb, state, k, b, 0);
    add_yield (solver, idx, state, k, b, 0);
  }
  fb->state[idx] = 0;
}

// LRB line: the interval of 'idx', of class 'c' in 'intervals.h', closes,
// and LRB's close of it, just before, said what it did ('closing').  The
// decided interval of a pending pick is an event, without a reward if it
// spanned no conflict; a pick whose interval LRB's walk did not open,
// which only the unit tests make, is taken back.  An update of Q feeds the
// ERWAs of the interval's class and the weighted ones, and Q_const's sums
// if the interval is decided.

static void close_lrb (kissat *solver, unsigned idx, unsigned c) {
  feedback *const fb = &solver->policy.feedback;
  const unsigned how = fb->closing.how;
  const double reward = fb->closing.reward, alpha = fb->closing.alpha;
  fb->closing.how = FEEDBACK_LRB_NONE;
  assert (how != FEEDBACK_LRB_NONE);
  const bool paid = how == FEEDBACK_LRB_PAID;
  const bool decided = c == INTERVALS_DECIDED;
  if (fb->state[idx] & FEEDBACK_PENDING) {
    fb->state[idx] = 0;
    if (decided && how != FEEDBACK_LRB_IGNORED)
      close_lrb_event (solver, idx, paid, reward);
    else {
      assert (fb->m1.picks);
      fb->m1.picks--;
      free_record (solver, idx);
    }
  }
  if (!paid)
    return;
  if (decided) {
    fb->m1.sum_n++;
    fb->m1.sum_r += reward;
  }
  update_erwas (solver, idx, c, reward, alpha);
}

void kissat_feedback_lrb_close (kissat *solver, unsigned how, double reward,
                                double alpha) {
  feedback *const fb = &solver->policy.feedback;
  if (!fb->started)
    return;
  assert (fb->lrb);
  assert (fb->closing.how == FEEDBACK_LRB_NONE);
  assert (how != FEEDBACK_LRB_NONE);
  fb->closing.how = how;
  fb->closing.reward = reward;
  fb->closing.alpha = alpha;
}

// CHB line: the interval of the pending pick of 'idx' closes, for M3: at
// its unassignment in stable mode, at the end of the analysis step whose
// backtrack ended it, or when stable mode is left.  M2's outcome, its
// payment, came at the propagation after the pick; a pick without one,
// which only the unit tests make, is taken back from M2 and M3.

static void close_yield (kissat *solver, unsigned idx) {
  feedback *const fb = &solver->policy.feedback;
  assert (fb->chb);
  const unsigned state = fb->state[idx];
  assert (state & FEEDBACK_YIELD);
  if (state & FEEDBACK_PENDING) {
    void_pick (fb, state);
    void_yield (fb, idx, state);
  } else
    add_yield (solver, idx, state, 0, 0, fb->reward[idx]);
  fb->state[idx] = 0;
}

// The assignment interval of 'idx', of class 'c' in 'intervals.h', closes:
// on the VSIDS line M1's interval, on the CHB line M3's pending pick, if
// 'idx' has one, and on the LRB line LRB's interval.  On the CHB and LRB
// lines a close that a backtrack of an analysis step deferred happens at
// the step's end, after its conflict.

void kissat_close_feedback_interval (kissat *solver, unsigned idx,
                                     unsigned c) {
  feedback *const fb = &solver->policy.feedback;
  if (!fb->started)
    return;
  assert (solver->stable);
  if (fb->lrb)
    close_lrb (solver, idx, c);
  else if (!fb->chb)
    close_interval (solver, idx, c);
  else if (fb->state[idx] & FEEDBACK_YIELD)
    close_yield (solver, idx);
}

// A step of conflict analysis starts, before its backtracks.  M3 takes the
// open picks' levels and their variables, on the VSIDS and CHB lines (M3
// does not run on the LRB line).  On the VSIDS
// line assertion builds list the active variables assigned now, which the
// step's bump round observes.

void kissat_feedback_begin_analysis (kissat *solver) {
  feedback *const fb = &solver->policy.feedback;
  if (!fb->started || !solver->stable || fb->lrb)
    return;
  stage_yields (solver);
#ifndef NDEBUG
  if (fb->chb)
    return;
  unsigneds *const listed = &fb->check.listed;
  CLEAR_STACK (*listed);
  const flags *const flags = solver->flags;
  for (all_stack (unsigned, lit, solver->trail))
    if (flags[IDX (lit)].active)
      PUSH_STACK (*listed, IDX (lit));
#endif
}

// The step ends, after its bump round if it had one, before the closes
// still deferred (no round) happen, without a round: M3's levels taken at
// its start are dropped if its analyzed variables were neither bumped nor
// recorded.

void kissat_feedback_end_analysis (kissat *solver) {
  feedback *const fb = &solver->policy.feedback;
  if (!fb->started || !solver->policy.intervals.analyzing)
    return;
  CLEAR_STACK (fb->staged);
  fb->staged_levels = fb->staged_segments = 0;
#ifndef NDEBUG
  CLEAR_STACK (fb->check.staged);
  CLEAR_STACK (fb->check.listed);
#endif
}

// VSIDS line: a bump round ends, after the increment grew, before the
// closes it ends (see 'intervals.h').  Assertion builds count the round and
// the bumps of the variables it observes, the step's listed ones (outside
// a step, in the unit tests, those on the trail).

void kissat_feedback_round_end (kissat *solver) {
  feedback *const fb = &solver->policy.feedback;
  if (!fb->started)
    return;
  assert (!fb->chb);
  assert (solver->stable);
#ifndef NDEBUG
  const uint64_t round = solver->estimator.rounds;
  const flags *const flags = solver->flags;
  uint64_t *const marked = fb->check.marked;
  for (all_stack (unsigned, idx, solver->analyzed))
    if (flags[idx].active)
      marked[idx] = round;
  uint64_t *const rounds = fb->check.rounds;
  uint64_t *const bumped = fb->check.bumped;
  if (solver->policy.intervals.analyzing) {
    for (all_stack (unsigned, idx, fb->check.listed)) {
      rounds[idx]++;
      if (marked[idx] == round)
        bumped[idx]++;
    }
    CLEAR_STACK (fb->check.listed);
  } else
    for (all_stack (unsigned, lit, solver->trail)) {
      const unsigned idx = IDX (lit);
      if (!flags[idx].active)
        continue;
      rounds[idx]++;
      if (marked[idx] == round)
        bumped[idx]++;
    }
#endif
}

// The sums in units of the increment follow the scores' rescale, as the
// increments at assignment do (see 'intervals.h'), those of the three
// classes and of E_w too.

void kissat_rescale_feedback (kissat *solver, double factor) {
  feedback *const fb = &solver->policy.feedback;
  if (!fb->started || fb->chb)
    return;
  for (all_variables (idx)) {
    for (unsigned c = 0; c < 2; c++) {
      fb->n[c][idx] *= factor;
      fb->r[c][idx] *= factor;
    }
    feedback_classes *const classes = fb->classes + idx;
    for (unsigned c = 0; c < 2; c++) {
      classes->n[c] *= factor;
      classes->r[c] *= factor;
      classes->rates[c] *= factor;
      classes->weights[c] *= factor;
    }
  }
}

// CHB line: a payment.  If its variable is decided it is an event of M1,
// whose predictors are read before the update; the ERWA of its class,
// its payments, UCB's count and its latest payment follow; and a pending
// pick of the variable has its outcome in M2, which M3 keeps until the
// pick's interval closes.

void kissat_feedback_paid (kissat *solver, unsigned idx, double reward,
                           double alpha, double old_q,
                           uint64_t conflicts) {
  feedback *const fb = &solver->policy.feedback;
  if (!fb->started)
    return;
  assert (fb->chb);
  assert (VALUE (LIT (idx)));
  const unsigned c = class_of (solver, idx);
  if (c == FEEDBACK_DEC) {
    double p[FEEDBACK_PREDICTORS];
    p[FEEDBACK_PREDICT_DEC] =
        fb->paid[FEEDBACK_DEC][idx] ? fb->q[FEEDBACK_DEC][idx] : NAN;
    p[FEEDBACK_PREDICT_IMP] =
        fb->paid[FEEDBACK_IMP][idx] ? fb->q[FEEDBACK_IMP][idx] : NAN;
    p[FEEDBACK_PREDICT_ALL] = old_q;
    p[FEEDBACK_PREDICT_CONST] =
        fb->m1.sum_n ? fb->m1.sum_r / fb->m1.sum_n : NAN;
    const unsigned group = group_of (p, true);
    add_payment (fb->m1.group + group, p, group_mask[1][group], reward);
    if (group == FEEDBACK_GROUP_BOTH)
      for (unsigned d = 0; d < 2; d++) {
        const double q = p[d ? FEEDBACK_PREDICT_IMP : FEEDBACK_PREDICT_DEC];
        add_payment (&fb->m1.calibration[d][calibration_bin (q)], p, 0,
                     reward);
      }
    fb->m1.events++;
    fb->m1.sum_n++;
    fb->m1.sum_r += reward;
  }
  fb->m1.intervals[c]++;
  double *const q = fb->q[c] + idx;
  *q = (1 - alpha) * *q + alpha * reward;
  fb->paid[c][idx]++;
  fb->count[idx] += fb->increment;
  fb->latest[idx] = conflicts;
  const unsigned state = fb->state[idx];
  if (state & FEEDBACK_PENDING) {
    assert (state & FEEDBACK_YIELD);
    if (c == FEEDBACK_DEC) {
      add_outcome (fb, state, 0, 0, reward);
      fb->reward[idx] = reward;
      fb->state[idx] = state & ~FEEDBACK_PENDING;
    } else {
      void_pick (fb, state);
      void_yield (fb, idx, state);
      fb->state[idx] = 0;
    }
  }
}

// CHB line: the counts' increment grows by 1/d after the payments of
// every stable-mode conflict, and the counts are rescaled with it when it
// exceeds 'MAX_SCORE', as UCB's are ('kissat_keys_chb_conflict').

void kissat_feedback_chb_conflict (kissat *solver) {
  feedback *const fb = &solver->policy.feedback;
  if (!fb->started)
    return;
  assert (fb->chb);
  fb->increment *= fb->growth;
  if (fb->increment <= MAX_SCORE)
    return;
  const double factor = 1.0 / fb->increment;
  double *const count = fb->count;
  for (all_variables (idx))
    count[idx] *= factor;
  fb->increment *= factor;
}

#ifdef SHADOW

// Shadow mode's count of the payments, for the complete check.

void kissat_shadow_feedback_paid (kissat *solver, unsigned idx) {
  feedback *const fb = &solver->policy.feedback;
  if (fb->started)
    fb->repaid[idx]++;
}

#endif

// VSIDS line: the difference between the asserted and propagated sums of
// 'idx' added up and its implied sum, of its rounds ('bumps' false) or of
// its bumps, which differ only by rounding: in units of the increment
// 'inc', relative to one plus the implied sum, as UCB's counts are checked
// (a plain relative difference of sums decayed to subnormal numbers would
// measure their lost precision).

static double classes_difference (const feedback *fb, unsigned idx,
                                  bool bumps, double inc) {
  const feedback_classes *const c = fb->classes + idx;
  const double split =
      bumps ? c->r[FEEDBACK_AST] + c->r[FEEDBACK_PROP]
            : c->n[FEEDBACK_AST] + c->n[FEEDBACK_PROP];
  const double implied =
      bumps ? fb->r[FEEDBACK_IMP][idx] : fb->n[FEEDBACK_IMP][idx];
  return fabs (split / inc - implied / inc) / (1 + implied / inc);
}

#ifndef NDEBUG

// Every 1000 picks: the counts against UCB's (see 'feedback.h'), on VSIDS
// scores those of UCB counting LRB's interval, the only count UCB keeps in
// feedback builds (see 'intervals.h'), on the same intervals.  On the
// VSIDS line the asserted and propagated sums against the implied ones,
// and on the LRB line Q_1 against LRB's Q and the ERWAs against the
// check's.

#define FEEDBACK_CHECK_TOLERANCE 1e-12

static void check_classes (kissat *solver, uint64_t pick) {
  feedback *const fb = &solver->policy.feedback;
  const flags *const flags = solver->flags;
  const double inc = solver->scinc;
  for (all_variables (idx)) {
    if (!flags[idx].active)
      continue;
    for (unsigned bumps = 0; bumps < 2; bumps++) {
      const double error = classes_difference (fb, idx, bumps, inc);
      fb->check.classes++;
      if (error > fb->check.classes_error)
        fb->check.classes_error = error;
      if (!(error <= FEEDBACK_CHECK_TOLERANCE))
        kissat_fatal ("feedback: pick %" PRIu64 ": the asserted and "
                      "propagated %s of variable %u differ from the "
                      "implied ones by %.3g",
                      pick, bumps ? "bumps" : "rounds", idx, error);
    }
  }
}

static void check_erwas (kissat *solver, uint64_t pick) {
  feedback *const fb = &solver->policy.feedback;
  const flags *const flags = solver->flags;
  for (all_variables (idx)) {
    if (!flags[idx].active)
      continue;
    if (!kissat_same_double (fb->check.q1[idx], solver->score[idx]))
      kissat_fatal ("feedback: pick %" PRIu64 ": Q_1 %.17g of variable %u "
                    "differs from LRB's Q %.17g",
                    pick, fb->check.q1[idx], idx, solver->score[idx]);
    const feedback_erwas *const e = fb->erwas + idx;
    const feedback_erwas *const s = fb->check.shadow + idx;
    bool same = true;
    for (unsigned i = 0; i < 4; i++)
      same &= kissat_same_double (e->q[i], s->q[i]);
    for (unsigned i = 0; i < FEEDBACK_WEIGHTS; i++)
      same &= kissat_same_double (e->w[i], s->w[i]);
    for (unsigned i = 0; i < FEEDBACK_GRID; i++)
      same &= kissat_same_double (e->grid[i], s->grid[i]);
    for (unsigned i = 0; i < 3; i++)
      same &= e->updates[i] == s->updates[i];
    if (!same)
      kissat_fatal ("feedback: pick %" PRIu64 ": the ERWAs of variable %u "
                    "differ from the check's",
                    pick, idx);
  }
}

static void complete_check (kissat *solver) {
  feedback *const fb = &solver->policy.feedback;
  if (!fb->started)
    return;
  fb->check.complete++;
  const keys *const keys = &solver->policy.keys;
  const flags *const flags = solver->flags;
  const uint64_t pick = fb->check.picks;
  if (fb->lrb) {
    check_erwas (solver, pick);
    return;
  }
  if (!fb->chb) {
    check_classes (solver, pick);
    if (!keys->intervals)
      return;
    const intervals *const intervals = &solver->policy.intervals;
    assert (intervals->interval);
    const double inc = solver->scinc;
    const double geometric = fb->growth - 1;
    const value *const values = solver->values;
    const assigned *const assigned = solver->assigned;
    for (all_variables (idx)) {
      if (!flags[idx].active)
        continue;
      double mine = fb->n[FEEDBACK_DEC][idx] + fb->n[FEEDBACK_IMP][idx];
      double ucb = keys->count[idx];
      if (values[LIT (idx)] && assigned[idx].trail < intervals->counted) {
        const double open = (inc - intervals->opened[idx]) / geometric;
        mine += open;
        ucb += open;
      }
      const double n = mine / inc, expected = ucb / inc;
      const double error = fabs (n - expected) / (1 + expected);
      fb->check.counts++;
      if (error > fb->check.error)
        fb->check.error = error;
      if (!(error <= FEEDBACK_CHECK_TOLERANCE))
        kissat_fatal ("feedback: pick %" PRIu64 ": count %.17g of variable "
                      "%u differs from UCB's %.17g",
                      pick, n, idx, expected);
    }
    return;
  }
  if (keys->counts) {
    if (!kissat_same_double (fb->increment, keys->increment))
      kissat_fatal ("feedback: pick %" PRIu64 ": CHB counts' increment "
                    "%.17g differs from UCB's %.17g",
                    pick, fb->increment, keys->increment);
    for (all_variables (idx)) {
      if (!flags[idx].active)
        continue;
      if (!kissat_same_double (fb->count[idx], keys->count[idx]))
        kissat_fatal ("feedback: pick %" PRIu64 ": CHB count %.17g of "
                      "variable %u differs from UCB's %.17g",
                      pick, fb->count[idx], idx, keys->count[idx]);
      fb->check.chb++;
    }
  }
#ifdef SHADOW
  for (all_variables (idx)) {
    if (!flags[idx].active)
      continue;
    const uint64_t paid =
        fb->paid[FEEDBACK_DEC][idx] + fb->paid[FEEDBACK_IMP][idx];
    if (paid != fb->repaid[idx])
      kissat_fatal ("feedback: pick %" PRIu64 ": %" PRIu64 " payments of "
                    "variable %u by class, %" PRIu64 " in shadow mode",
                    pick, paid, idx, fb->repaid[idx]);
    fb->check.payments++;
  }
#endif
}

#endif

// LRB line: a pick, pending until its interval closes, with M1's four
// predictors and the pre-check's frozen.  A pending pick not followed by
// its decision, which only the unit tests make, is taken back.

static void pick_lrb (kissat *solver, unsigned idx) {
  feedback *const fb = &solver->policy.feedback;
  if (fb->state[idx] & FEEDBACK_PENDING) {
    assert (fb->m1.picks);
    fb->m1.picks--;
    free_record (solver, idx);
  }
  fb->m1.picks++;
  feedback_record *const record = new_record (solver, idx);
  freeze_lrb (solver, idx, record);
#ifndef NDEBUG
  check_freeze_lrb (solver, idx, record);
#endif
  fb->state[idx] = FEEDBACK_PENDING;
}

// A pick of the policy.  In search, in stable mode, it is pending until
// its outcome, with its kind and its variable's age and count bins, and on
// the VSIDS line the four predictors of M1 are frozen, and the pre-check's
// in a record: the variable is assigned as a decision right after the
// pick, and its sums and those of p_const and of the cells do not change
// before its interval opens.  For M3 it is pending until its interval
// closes, with the bin of 'Y_v', and awaits the end of the propagation
// that follows its decision.  The LRB line has a pick of its own.

void kissat_feedback_pick (kissat *solver, unsigned idx, bool uniform) {
  feedback *const fb = &solver->policy.feedback;
#ifndef NDEBUG
  if (!(++fb->check.picks % 1000))
    complete_check (solver);
#endif
  if (!fb->started || solver->warming)
    return;
  assert (solver->stable);
  assert (!VALUE (LIT (idx)));
  assert (!(solver->policy.intervals.state[idx] & INTERVALS_OPEN));
  if (fb->lrb) {
    pick_lrb (solver, idx);
    return;
  }
  const unsigned old_state = fb->state[idx];
  if (old_state & FEEDBACK_PENDING) {
    void_pick (fb, old_state);
    free_record (solver, idx);
  }
  if (old_state & FEEDBACK_YIELD)
    void_yield (fb, idx, old_state);
  assert (!fb->propagated[idx]), assert (!fb->observed[idx]);
  const unsigned kind = uniform ? FEEDBACK_UNIFORM : FEEDBACK_POLICY;
  fb->m2.picks[kind]++;
  fb->m3.picks[kind]++;
  fb->yielding = idx + 1;
  unsigned age;
  double count;
  if (fb->chb) {
    const uint64_t paid =
        fb->paid[FEEDBACK_DEC][idx] + fb->paid[FEEDBACK_IMP][idx];
    assert (fb->latest[idx] <= solver->estimator.chb.conflicts);
    age = paid ? age_bin (solver->estimator.chb.conflicts - fb->latest[idx])
               : FEEDBACK_AGE_NEVER;
    count = fb->count[idx] / fb->increment;
  } else {
    const uint64_t last = fb->last[idx];
    assert (last <= solver->estimator.rounds);
    age = last ? age_bin (solver->estimator.rounds - last)
               : FEEDBACK_AGE_NEVER;
    const double n_dec = fb->n[FEEDBACK_DEC][idx];
    const double n_imp = fb->n[FEEDBACK_IMP][idx];
    const double r_dec = fb->r[FEEDBACK_DEC][idx];
    const double r_imp = fb->r[FEEDBACK_IMP][idx];
    const double n = n_dec + n_imp;
    count = n / solver->scinc;
    double *const p = fb->frozen + FEEDBACK_PREDICTORS * idx;
    p[FEEDBACK_PREDICT_DEC] = n_dec > 0 ? r_dec / n_dec : NAN;
    p[FEEDBACK_PREDICT_IMP] = n_imp > 0 ? r_imp / n_imp : NAN;
    p[FEEDBACK_PREDICT_ALL] = n > 0 ? (r_dec + r_imp) / n : NAN;
    p[FEEDBACK_PREDICT_CONST] =
        fb->m1.sum_k ? (double) fb->m1.sum_b / fb->m1.sum_k : NAN;
    feedback_record *const record = new_record (solver, idx);
    freeze_vsids (solver, idx, record, p[FEEDBACK_PREDICT_ALL],
                  yield_bin (fb->yield[idx]));
#ifndef NDEBUG
    check_freeze_vsids (solver, idx, record);
#endif
  }
  fb->state[idx] = FEEDBACK_PENDING | kind << FEEDBACK_KIND_SHIFT |
                   age << FEEDBACK_AGE_SHIFT |
                   count_bin (count) << FEEDBACK_COUNT_SHIFT |
                   FEEDBACK_YIELD |
                   yield_bin (fb->yield[idx]) << FEEDBACK_YIELD_SHIFT;
}

// The differ pass's keys of the unassigned variable 'idx', the reference
// last (see 'feedback.h').  The locality key is its key 's' times lambda
// to the steps since the variable's last stable-mode unassignment, in
// logarithms (minus infinity for zero).

static double locality_key (const feedback *fb, unsigned idx, double s) {
  assert (fb->unassigned[idx] <= fb->steps);
  const double age = fb->steps - fb->unassigned[idx];
  return log (s) + age * fb->log_lambda;
}

static void vsids_keys (kissat *solver, unsigned idx, double *key) {
  const feedback *const fb = &solver->policy.feedback;
  const feedback_classes *const c = fb->classes + idx;
  const double r_dec = fb->r[FEEDBACK_DEC][idx];
  const double r_imp = fb->r[FEEDBACK_IMP][idx];
  const double r_ast = c->r[FEEDBACK_AST], r_prop = c->r[FEEDBACK_PROP];
  const double s_1 = r_dec + r_imp;
  key[FEEDBACK_KEY_W] = r_dec;
  for (unsigned i = 0; i < FEEDBACK_WEIGHTS; i++)
    key[FEEDBACK_KEY_W + 1 + i] = r_dec + two_class_w[i] * r_imp;
  key[FEEDBACK_KEY_W + 1 + FEEDBACK_WEIGHTS] = r_imp;
  for (unsigned i = 0; i < FEEDBACK_GRID; i++) {
    const double w = grid_w[i / FEEDBACK_GRID_A];
    const double a = grid_a[i % FEEDBACK_GRID_A];
    key[FEEDBACK_KEY_GRID + i] = r_dec + a * r_ast + w * r_prop;
  }
  const double n = fb->n[FEEDBACK_DEC][idx] + fb->n[FEEDBACK_IMP][idx];
  key[FEEDBACK_KEY_V_RATE] = n > 0 ? s_1 / n : 0;
  key[FEEDBACK_KEY_V_LOCALITY] = locality_key (fb, idx, s_1);
  key[FEEDBACK_KEY_V_INTERVAL] =
      c->rates[FEEDBACK_DEC] + c->rates[FEEDBACK_IMP];
  key[FEEDBACK_KEY_V_SCORE] = solver->score[idx];
  key[FEEDBACK_V_KEYS] = s_1;
}

static void lrb_keys (kissat *solver, unsigned idx, double *key) {
  const feedback *const fb = &solver->policy.feedback;
  const feedback_erwas *const e = fb->erwas + idx;
  key[FEEDBACK_KEY_W] = e->q[FEEDBACK_Q_DEC];
  for (unsigned i = 0; i < FEEDBACK_WEIGHTS; i++)
    key[FEEDBACK_KEY_W + 1 + i] = e->w[i];
  key[FEEDBACK_KEY_W + 1 + FEEDBACK_WEIGHTS] = e->q[FEEDBACK_Q_IMP];
  for (unsigned i = 0; i < FEEDBACK_GRID; i++)
    key[FEEDBACK_KEY_GRID + i] = e->grid[i];
  const double q = solver->score[idx];
  key[FEEDBACK_KEY_L_LOCALITY] = locality_key (fb, idx, q);
  key[FEEDBACK_KEY_L_SCORE] = q;
  key[FEEDBACK_L_KEYS] = q;
}

#ifndef NDEBUG

// Check (d) of the differ pass: the key 'i' of 'idx' alone, by code of its
// own with the weights per mille, and a pass of its own per key, which
// must find the argmaxes that the differ pass found.

static double key_of (kissat *solver, unsigned idx, unsigned i) {
  const feedback *const fb = &solver->policy.feedback;
  const double age = fb->steps - fb->unassigned[idx];
  if (fb->lrb) {
    const feedback_erwas *const e = fb->erwas + idx;
    const double q = solver->score[idx];
    if (i == FEEDBACK_KEY_W)
      return e->q[FEEDBACK_Q_DEC];
    if (i <= FEEDBACK_WEIGHTS)
      return e->w[i - 1];
    if (i < FEEDBACK_KEY_GRID)
      return e->q[FEEDBACK_Q_IMP];
    if (i < FEEDBACK_KEY_L_LOCALITY)
      return e->grid[i - FEEDBACK_KEY_GRID];
    if (i == FEEDBACK_KEY_L_LOCALITY)
      return log (q) + age * fb->log_lambda;
    return q; // the score and the reference
  }
  const double rd = fb->r[FEEDBACK_DEC][idx], ri = fb->r[FEEDBACK_IMP][idx];
  const feedback_classes *const c = fb->classes + idx;
  if (i == FEEDBACK_KEY_W)
    return rd;
  if (i <= FEEDBACK_WEIGHTS)
    return rd + two_class_permille[i - 1] / 1000.0 * ri;
  if (i < FEEDBACK_KEY_GRID)
    return ri;
  if (i < FEEDBACK_KEY_V_RATE) {
    const unsigned j = i - FEEDBACK_KEY_GRID;
    const double w = grid_w_permille[j / FEEDBACK_GRID_A] / 1000.0;
    const double a = grid_a_permille[j % FEEDBACK_GRID_A] / 1000.0;
    return rd + a * c->r[FEEDBACK_AST] + w * c->r[FEEDBACK_PROP];
  }
  if (i == FEEDBACK_KEY_V_RATE) {
    const double n = fb->n[FEEDBACK_DEC][idx] + fb->n[FEEDBACK_IMP][idx];
    return n > 0 ? (rd + ri) / n : 0;
  }
  if (i == FEEDBACK_KEY_V_LOCALITY)
    return log (rd + ri) + age * fb->log_lambda;
  if (i == FEEDBACK_KEY_V_INTERVAL)
    return c->rates[FEEDBACK_DEC] + c->rates[FEEDBACK_IMP];
  if (i == FEEDBACK_KEY_V_SCORE)
    return solver->score[idx];
  return rd + ri; // the reference
}

static void check_differ (kissat *solver, const unsigned *argmax,
                          unsigned keys) {
  feedback *const fb = &solver->policy.feedback;
  for (unsigned i = 0; i <= keys; i++) {
    unsigned best = INVALID_IDX;
    double largest = 0;
    for (all_variables (idx)) {
      if (!ACTIVE (idx) || VALUE (LIT (idx)))
        continue;
      const double key = key_of (solver, idx, i);
      if (best == INVALID_IDX || key > largest)
        best = idx, largest = key;
    }
    if (best != argmax[i])
      kissat_fatal ("feedback: sample %" PRIu64 ": the argmax of key %u "
                    "is variable %u, but the differ pass found %u",
                    fb->differ.samples, i, best, argmax[i]);
  }
  fb->check.differ++;
}

#endif

// The differ pass (see 'feedback.h'), at a search sample of the decision
// metrics: one pass over the unassigned active variables, which only reads,
// takes every key's argmax, the smallest index among ties, and counts the
// keys whose argmax is not the reference's.

void kissat_feedback_differ (kissat *solver) {
  feedback *const fb = &solver->policy.feedback;
  if (!fb->started || (fb->chb && !fb->lrb))
    return;
  assert (solver->stable), assert (!solver->warming);
  const bool lrb = fb->lrb;
  assert (lrb || fb->steps == solver->estimator.rounds);
  const unsigned keys = lrb ? FEEDBACK_L_KEYS : FEEDBACK_V_KEYS;
  unsigned argmax[FEEDBACK_KEYS + 1];
  double largest[FEEDBACK_KEYS + 1], key[FEEDBACK_KEYS + 1];
  for (unsigned i = 0; i <= keys; i++)
    argmax[i] = INVALID_IDX, largest[i] = -INFINITY;
  const flags *const flags = solver->flags;
  const value *const values = solver->values;
  for (all_variables (idx)) {
    if (!flags[idx].active || values[LIT (idx)])
      continue;
    if (lrb)
      lrb_keys (solver, idx, key);
    else
      vsids_keys (solver, idx, key);
    for (unsigned i = 0; i <= keys; i++)
      if (argmax[i] == INVALID_IDX || key[i] > largest[i])
        argmax[i] = idx, largest[i] = key[i];
  }
  assert (argmax[keys] != INVALID_IDX);
  fb->differ.samples++;
  for (unsigned i = 0; i < keys; i++)
    fb->differ.differ[i] += argmax[i] != argmax[keys];
#ifndef NDEBUG
  check_differ (solver, argmax, keys);
#endif
}

#ifndef QUIET
static void print_feedback (kissat *, const char *snapshot);
#endif

bool kissat_feedback_snapshot (kissat *solver) {
  feedback *const fb = &solver->policy.feedback;
  if (fb->snapshot || CONFLICTS < FEEDBACK_SNAPSHOT)
    return false;
  fb->snapshot = true;
#ifndef QUIET
  print_feedback (solver, "snapshot-");
#endif
  return false;
}

#ifndef QUIET

static const char *const predictor_names[2][FEEDBACK_PREDICTORS] = {
    {"dec", "imp", "all", "const"}, {"dec", "imp", "q", "const"}};
static const char *const group_names[FEEDBACK_GROUPS] = {
    "", "imp-undefined-", "dec-undefined-", "both-undefined-",
    "const-undefined-"};
static const char *const class_names[2] = {"dec", "imp"};
static const char *const kind_names[FEEDBACK_KINDS] = {"policy", "uniform"};
static const char *const age_names[FEEDBACK_AGES] = {"never", "old",
                                                     "stale", "recent"};
static const char *const count_names[FEEDBACK_COUNTS] = {
    "zero", "below1", "below5", "above5"};
static const char *const yield_names[FEEDBACK_YIELDS] = {
    "none", "below2", "below4", "below16", "below64", "above64"};
static const char *const cross_names[2] = {"stale", "recent"};

static void print_count (kissat *solver, const char *prefix,
                         const char *name, uint64_t value) {
  kissat_message (solver, "%s%s %" PRIu64, prefix, name, value);
}

static void print_double (kissat *solver, const char *prefix,
                          const char *name, double value) {
  kissat_message (solver, "%s%s %.17g", prefix, name, value);
}

// The sums of a set of intervals (VSIDS) or payments (CHB): 'n', 'k' and
// 'b' or 'r', 'bumped' with 'outcomes', and the errors in 'mask'.

static void print_sums (kissat *solver, const char *prefix,
                        const feedback_sums *sums, bool chb, bool outcomes,
                        unsigned mask) {
  print_count (solver, prefix, "n", sums->n);
  if (chb)
    print_double (solver, prefix, "r", sums->r);
  else {
    print_count (solver, prefix, "k", sums->k);
    print_count (solver, prefix, "b", sums->b);
    if (outcomes)
      print_count (solver, prefix, "bumped", sums->bumped);
  }
  char name[32];
  for (unsigned i = 0; i < FEEDBACK_PREDICTORS; i++) {
    if (!(mask & BIT (i)))
      continue;
    const char *const predictor = predictor_names[chb][i];
    if (chb) {
      snprintf (name, sizeof name, "error-%s", predictor);
      print_double (solver, prefix, name, sums->interval[i]);
    } else {
      snprintf (name, sizeof name, "round-error-%s", predictor);
      print_double (solver, prefix, name, sums->round[i]);
      snprintf (name, sizeof name, "interval-error-%s", predictor);
      print_double (solver, prefix, name, sums->interval[i]);
    }
  }
}

// M3's sums of a set of picks: 'n', M2's outcome with 'outcomes' ('k', 'b'
// and 'bumped', or 'r'), and the sums of 'y_prop' and 'y_obs'.

static void print_yields (kissat *solver, const char *prefix,
                          const feedback_yields *sums, bool chb,
                          bool outcomes) {
  print_count (solver, prefix, "n", sums->n);
  if (outcomes && chb)
    print_double (solver, prefix, "r", sums->r);
  else if (outcomes) {
    print_count (solver, prefix, "k", sums->k);
    print_count (solver, prefix, "b", sums->b);
    print_count (solver, prefix, "bumped", sums->bumped);
  }
  print_count (solver, prefix, "prop", sums->prop);
  print_count (solver, prefix, "obs", sums->obs);
}

// The pre-check's names: of a predictor (in a record's 'extra') and of a
// key of the differ pass, of the VSIDS or the LRB line, with the weights
// per mille.

static void predictor_name (char *name, size_t size, bool lrb, unsigned i) {
  static const char *const rest[FEEDBACK_V_PREDICTORS - FEEDBACK_V_MEAN] = {
      "mean-w0",   "mean-w1000", "mean-winf", "bin-yield",
      "bin-p",     "bin-yield-p", "bin-all"};
  if (i == FEEDBACK_V_AST)
    snprintf (name, size, "ast");
  else if (i == FEEDBACK_V_PROP)
    snprintf (name, size, "prop");
  else if (i < FEEDBACK_V_GRID)
    snprintf (name, size, "w%u", two_class_permille[i - FEEDBACK_V_W]);
  else if (i < FEEDBACK_V_MEAN) {
    const unsigned j = i - FEEDBACK_V_GRID;
    snprintf (name, size, "w%u-a%u", grid_w_permille[j / FEEDBACK_GRID_A],
              grid_a_permille[j % FEEDBACK_GRID_A]);
  } else {
    assert (!lrb), assert (i < FEEDBACK_V_PREDICTORS);
    snprintf (name, size, "%s", rest[i - FEEDBACK_V_MEAN]);
  }
  (void) lrb;
}

static void key_name (char *name, size_t size, bool lrb, unsigned i) {
  static const char *const rest[2][4] = {
      {"rate", "locality", "interval", "score"}, {"locality", "score"}};
  if (i == FEEDBACK_KEY_W)
    snprintf (name, size, "w0");
  else if (i <= FEEDBACK_WEIGHTS)
    snprintf (name, size, "w%u", two_class_permille[i - 1]);
  else if (i < FEEDBACK_KEY_GRID)
    snprintf (name, size, "winf");
  else if (i < FEEDBACK_KEY_GRID + FEEDBACK_GRID) {
    const unsigned j = i - FEEDBACK_KEY_GRID;
    snprintf (name, size, "w%u-a%u", grid_w_permille[j / FEEDBACK_GRID_A],
              grid_a_permille[j % FEEDBACK_GRID_A]);
  } else
    snprintf (name, size, "%s",
              rest[lrb][i - FEEDBACK_KEY_GRID - FEEDBACK_GRID]);
}

// The pre-check's predictors in M1's groups but the one without p_const or
// Q_const: per predictor the events where it is defined, and its errors
// there, per round and per interval on the VSIDS line, of the reward on the
// LRB line.

static void print_extra (kissat *solver, const char *snapshot,
                         const char *line, bool lrb) {
  const feedback *const fb = &solver->policy.feedback;
  const unsigned count =
      lrb ? FEEDBACK_L_PREDICTORS : FEEDBACK_V_PREDICTORS;
  char prefix[96], name[48], predictor[32];
  assert (FEEDBACK_GROUP_NO_CONST + 1 == FEEDBACK_GROUPS);
  for (unsigned g = 0; g < FEEDBACK_GROUP_NO_CONST; g++) {
    const feedback_extra *const sums = fb->m1.extra + g;
    snprintf (prefix, sizeof prefix, "%sfeedback-m1-%s-%s", snapshot, line,
              group_names[g]);
    for (unsigned i = 0; i < count; i++) {
      predictor_name (predictor, sizeof predictor, lrb, i);
      snprintf (name, sizeof name, "n-%s", predictor);
      print_count (solver, prefix, name, sums->n[i]);
      if (lrb) {
        snprintf (name, sizeof name, "error-%s", predictor);
        print_double (solver, prefix, name, sums->interval[i]);
      } else {
        snprintf (name, sizeof name, "round-error-%s", predictor);
        print_double (solver, prefix, name, sums->round[i]);
        snprintf (name, sizeof name, "interval-error-%s", predictor);
        print_double (solver, prefix, name, sums->interval[i]);
      }
    }
  }
}

// The differ pass: its samples, and per key those where its argmax
// differed from the reference's.

static void print_differ (kissat *solver, const char *snapshot,
                          const char *line, bool lrb) {
  const feedback *const fb = &solver->policy.feedback;
  const unsigned keys = lrb ? FEEDBACK_L_KEYS : FEEDBACK_V_KEYS;
  char prefix[96], name[48];
  snprintf (prefix, sizeof prefix, "%sfeedback-%s-differ-", snapshot, line);
  print_count (solver, prefix, "samples", fb->differ.samples);
  for (unsigned i = 0; i < keys; i++) {
    key_name (name, sizeof name, lrb, i);
    print_count (solver, prefix, name, fb->differ.differ[i]);
  }
}

static const char *const split_names[2] = {"ast", "prop"};

// M1, M2 and M3 on the VSIDS and CHB lines, as before Phase 4.  M2's and
// M3's picks still open at the end are those pending, and every pick is an
// outcome or open; M3's outcomes by age, by count and by the bin of 'Y_v'
// are the same, and its uniform outcomes crossed with stale against recent
// are its uniform outcomes by that bin (checked in assertion builds).

static void print_measurements (kissat *solver, const char *snapshot) {
  const feedback *const fb = &solver->policy.feedback;
  const bool chb = fb->started ? fb->chb : kissat_chb (solver);
  const char *const line = chb ? "chb" : "vsids";
  uint64_t open[FEEDBACK_KINDS] = {0, 0};
  uint64_t yielding[FEEDBACK_KINDS] = {0, 0};
  if (fb->started)
    for (all_variables (idx)) {
      const unsigned state = fb->state[idx];
      const unsigned kind = (state >> FEEDBACK_KIND_SHIFT) & 1;
      if (state & FEEDBACK_PENDING)
        open[kind]++;
      if (state & FEEDBACK_YIELD)
        yielding[kind]++;
    }
  for (unsigned kind = 0; kind < FEEDBACK_KINDS; kind++) {
    uint64_t by_age = 0, by_count = 0;
    for (unsigned i = 0; i < FEEDBACK_AGES; i++)
      by_age += fb->m2.age[kind][i].n;
    for (unsigned i = 0; i < FEEDBACK_COUNTS; i++)
      by_count += fb->m2.count[kind][i].n;
    if (by_age != by_count || fb->m2.picks[kind] != by_age + open[kind]) {
#ifndef NDEBUG
      kissat_fatal ("feedback: %" PRIu64 " %s picks, %" PRIu64 " and "
                    "%" PRIu64 " outcomes by age and count, %" PRIu64
                    " open",
                    fb->m2.picks[kind], kind_names[kind], by_age, by_count,
                    open[kind]);
#endif
    }
    uint64_t m3_age = 0, m3_count = 0, m3_yield = 0;
    for (unsigned i = 0; i < FEEDBACK_AGES; i++)
      m3_age += fb->m3.age[kind][i].n;
    for (unsigned i = 0; i < FEEDBACK_COUNTS; i++)
      m3_count += fb->m3.count[kind][i].n;
    for (unsigned i = 0; i < FEEDBACK_YIELDS; i++)
      m3_yield += fb->m3.yield[kind][i].n;
    if (m3_age != m3_count || m3_age != m3_yield ||
        fb->m3.picks[kind] != m3_age + yielding[kind]) {
#ifndef NDEBUG
      kissat_fatal ("feedback: M3: %" PRIu64 " %s picks, %" PRIu64
                    ", %" PRIu64 " and %" PRIu64 " outcomes by age, count "
                    "and yield, %" PRIu64 " open",
                    fb->m3.picks[kind], kind_names[kind], m3_age, m3_count,
                    m3_yield, yielding[kind]);
#endif
    }
  }
  for (unsigned i = 0; i < FEEDBACK_YIELDS; i++) {
    const feedback_yields *const all = &fb->m3.yield[FEEDBACK_UNIFORM][i];
    const feedback_yields *const stale = &fb->m3.crossed[0][i];
    const feedback_yields *const recent = &fb->m3.crossed[1][i];
    if (all->n != stale->n + recent->n ||
        all->prop != stale->prop + recent->prop ||
        all->obs != stale->obs + recent->obs) {
#ifndef NDEBUG
      kissat_fatal ("feedback: M3: %" PRIu64 " uniform outcomes of yield "
                    "%s, %" PRIu64 " stale and %" PRIu64 " recent",
                    all->n, yield_names[i], stale->n, recent->n);
#endif
    }
  }
  char prefix[96], name[32];
  kissat_section (solver, *snapshot ? "feedback snapshot" : "feedback");
  snprintf (prefix, sizeof prefix, "%sfeedback-%s-", snapshot, line);
  for (unsigned c = 0; c < 2; c++) {
    snprintf (name, sizeof name, "%s-%s", chb ? "payments" : "intervals",
              class_names[c]);
    print_count (solver, prefix, name, fb->m1.intervals[c]);
  }
  if (!chb) {
    for (unsigned ended = 0; ended < 2; ended++)
      for (unsigned c = 0; c < 2; c++) {
        snprintf (name, sizeof name, "bumps-%s%s", ended ? "ended-" : "",
                  class_names[c]);
        print_count (solver, prefix, name, fb->m1.bumps[ended][c]);
      }
    print_count (solver, prefix, "bumps-unobserved", fb->m1.unobserved);
  }
  snprintf (prefix, sizeof prefix, "%sfeedback-m1-%s-", snapshot, line);
  print_count (solver, prefix, "events", fb->m1.events);
  if (!chb)
    print_count (solver, prefix, "events-k0", fb->m1.zero);
  for (unsigned g = 0; g < FEEDBACK_GROUPS; g++) {
    snprintf (prefix, sizeof prefix, "%sfeedback-m1-%s-%s", snapshot, line,
              group_names[g]);
    print_sums (solver, prefix, fb->m1.group + g, chb, false,
                group_mask[chb][g]);
  }
  for (unsigned d = 0; d < 2; d++)
    for (unsigned i = 0; i < FEEDBACK_BINS; i++) {
      snprintf (prefix, sizeof prefix, "%sfeedback-m1-%s-calibration-%s-%u-", snapshot,
                line, class_names[d], i);
      print_sums (solver, prefix, &fb->m1.calibration[d][i], chb, false, 0);
    }
  for (unsigned kind = 0; kind < FEEDBACK_KINDS; kind++) {
    snprintf (prefix, sizeof prefix, "%sfeedback-m2-%s-%s-", snapshot, line,
              kind_names[kind]);
    print_count (solver, prefix, "picks", fb->m2.picks[kind]);
    print_count (solver, prefix, "open", open[kind]);
    for (unsigned i = 0; i < FEEDBACK_AGES; i++) {
      snprintf (prefix, sizeof prefix, "%sfeedback-m2-%s-%s-age-%s-", snapshot, line,
                kind_names[kind], age_names[i]);
      print_sums (solver, prefix, &fb->m2.age[kind][i], chb, true, 0);
    }
    for (unsigned i = 0; i < FEEDBACK_COUNTS; i++) {
      snprintf (prefix, sizeof prefix, "%sfeedback-m2-%s-%s-count-%s-", snapshot, line,
                kind_names[kind], count_names[i]);
      print_sums (solver, prefix, &fb->m2.count[kind][i], chb, true, 0);
    }
  }
  for (unsigned kind = 0; kind < FEEDBACK_KINDS; kind++) {
    snprintf (prefix, sizeof prefix, "%sfeedback-m3-%s-%s-", snapshot, line,
              kind_names[kind]);
    print_count (solver, prefix, "picks", fb->m3.picks[kind]);
    print_count (solver, prefix, "open", yielding[kind]);
    for (unsigned i = 0; i < FEEDBACK_AGES; i++) {
      snprintf (prefix, sizeof prefix, "%sfeedback-m3-%s-%s-age-%s-", snapshot, line,
                kind_names[kind], age_names[i]);
      print_yields (solver, prefix, &fb->m3.age[kind][i], chb, false);
    }
    for (unsigned i = 0; i < FEEDBACK_COUNTS; i++) {
      snprintf (prefix, sizeof prefix, "%sfeedback-m3-%s-%s-count-%s-", snapshot, line,
                kind_names[kind], count_names[i]);
      print_yields (solver, prefix, &fb->m3.count[kind][i], chb, false);
    }
    for (unsigned i = 0; i < FEEDBACK_YIELDS; i++) {
      snprintf (prefix, sizeof prefix, "%sfeedback-m3-%s-%s-yield-%s-", snapshot, line,
                kind_names[kind], yield_names[i]);
      print_yields (solver, prefix, &fb->m3.yield[kind][i], chb, true);
    }
  }
  for (unsigned recent = 0; recent < 2; recent++)
    for (unsigned i = 0; i < FEEDBACK_YIELDS; i++) {
      snprintf (prefix, sizeof prefix, "%sfeedback-m3-%s-uniform-%s-yield-%s-", snapshot,
                line, cross_names[recent], yield_names[i]);
      print_yields (solver, prefix, &fb->m3.crossed[recent][i], chb, true);
    }
  snprintf (prefix, sizeof prefix, "%sfeedback-m3-%s-", snapshot, line);
  print_count (solver, prefix, "obs-levels", fb->m3.levels);
  print_count (solver, prefix, "obs-segments", fb->m3.segments);
}

// The VSIDS line's lines of the pre-check: the closed intervals and the
// bumps of the asserted and propagated classes, the steps, the largest
// relative difference of their sums from the implied ones over the active
// variables, the calibration bins of p_ast and p_prop, the pre-check's
// predictors and the differ pass.

static void print_vsids_precheck (kissat *solver, const char *snapshot) {
  const feedback *const fb = &solver->policy.feedback;
  char prefix[96], name[48];
  snprintf (prefix, sizeof prefix, "%sfeedback-vsids-", snapshot);
  for (unsigned j = 0; j < 2; j++) {
    snprintf (name, sizeof name, "intervals-%s", split_names[j]);
    print_count (solver, prefix, name, fb->m1.intervals3[j]);
  }
  for (unsigned ended = 0; ended < 2; ended++)
    for (unsigned j = 0; j < 2; j++) {
      snprintf (name, sizeof name, "bumps-%s%s", ended ? "ended-" : "",
                split_names[j]);
      print_count (solver, prefix, name, fb->m1.bumps3[ended][j]);
    }
  print_count (solver, prefix, "steps", fb->steps);
  double error = 0;
  if (fb->started)
    for (all_variables (idx)) {
      if (!ACTIVE (idx))
        continue;
      for (unsigned bumps = 0; bumps < 2; bumps++) {
        const double difference =
            classes_difference (fb, idx, bumps, solver->scinc);
        if (difference > error)
          error = difference;
      }
    }
  kissat_message (solver, "%sclasses-error %.3g", prefix, error);
  for (unsigned j = 0; j < 2; j++)
    for (unsigned i = 0; i < FEEDBACK_BINS; i++) {
      snprintf (prefix, sizeof prefix,
                "%sfeedback-m1-vsids-calibration-%s-%u-", snapshot,
                split_names[j], i);
      print_sums (solver, prefix, &fb->m1.calibration3[j][i], false, false,
                  0);
    }
  print_extra (solver, snapshot, "vsids", false);
  print_differ (solver, snapshot, "vsids", false);
}

// The LRB line: updates by class, the steps, M1 on LRB's reward (picks,
// those still open, events, those without a conflict, the groups of the
// CHB line and its calibration bins, those of Q_ast and Q_prop too), the
// pre-check's predictors and the differ pass.  Picks are events plus open
// picks (checked in assertion builds).

static void print_lrb (kissat *solver, const char *snapshot) {
  const feedback *const fb = &solver->policy.feedback;
  uint64_t open = 0;
  if (fb->started)
    for (all_variables (idx))
      open += fb->state[idx] & FEEDBACK_PENDING;
  if (fb->m1.picks != fb->m1.events + open) {
#ifndef NDEBUG
    kissat_fatal ("feedback: LRB: %" PRIu64 " picks, %" PRIu64
                  " events, %" PRIu64 " open",
                  fb->m1.picks, fb->m1.events, open);
#endif
  }
  char prefix[96], name[48];
  kissat_section (solver, *snapshot ? "feedback snapshot" : "feedback");
  snprintf (prefix, sizeof prefix, "%sfeedback-lrb-", snapshot);
  for (unsigned c = 0; c < 2; c++) {
    snprintf (name, sizeof name, "updates-%s", class_names[c]);
    print_count (solver, prefix, name, fb->m1.intervals[c]);
  }
  for (unsigned j = 0; j < 2; j++) {
    snprintf (name, sizeof name, "updates-%s", split_names[j]);
    print_count (solver, prefix, name, fb->m1.intervals3[j]);
  }
  print_count (solver, prefix, "steps", fb->steps);
  snprintf (prefix, sizeof prefix, "%sfeedback-m1-lrb-", snapshot);
  print_count (solver, prefix, "picks", fb->m1.picks);
  print_count (solver, prefix, "open", open);
  print_count (solver, prefix, "events", fb->m1.events);
  print_count (solver, prefix, "events-k0", fb->m1.zero);
  for (unsigned g = 0; g < FEEDBACK_GROUPS; g++) {
    snprintf (prefix, sizeof prefix, "%sfeedback-m1-lrb-%s", snapshot,
              group_names[g]);
    print_sums (solver, prefix, fb->m1.group + g, true, false,
                group_mask[1][g]);
  }
  for (unsigned d = 0; d < 4; d++)
    for (unsigned i = 0; i < FEEDBACK_BINS; i++) {
      const char *const name = d < 2 ? class_names[d] : split_names[d - 2];
      const feedback_sums *const sums =
          d < 2 ? &fb->m1.calibration[d][i] : &fb->m1.calibration3[d - 2][i];
      snprintf (prefix, sizeof prefix, "%sfeedback-m1-lrb-calibration-%s-%u-",
                snapshot, name, i);
      print_sums (solver, prefix, sums, true, false, 0);
    }
  print_extra (solver, snapshot, "lrb", true);
  print_differ (solver, snapshot, "lrb", true);
}

// The checks of assertion builds.

static void print_checks (kissat *solver, const char *snapshot) {
#ifndef NDEBUG
  const feedback *const fb = &solver->policy.feedback;
  kissat_message (solver, "%sfeedback-check-complete %" PRIu64, snapshot,
                  fb->check.complete);
  kissat_message (solver, "%sfeedback-check-counts %" PRIu64, snapshot,
                  fb->check.counts);
  kissat_message (solver, "%sfeedback-check-count-error %.3g", snapshot,
                  fb->check.error);
  kissat_message (solver, "%sfeedback-check-chb-counts %" PRIu64, snapshot,
                  fb->check.chb);
  kissat_message (solver, "%sfeedback-check-payments %" PRIu64, snapshot,
                  fb->check.payments);
  kissat_message (solver, "%sfeedback-check-intervals %" PRIu64, snapshot,
                  fb->check.intervals);
  kissat_message (solver, "%sfeedback-check-levels %" PRIu64, snapshot,
                  fb->check.steps);
  kissat_message (solver, "%sfeedback-check-yields %" PRIu64, snapshot,
                  fb->check.yields);
  kissat_message (solver, "%sfeedback-check-predictors %" PRIu64, snapshot,
                  fb->check.predictors);
  kissat_message (solver, "%sfeedback-check-differ %" PRIu64, snapshot,
                  fb->check.differ);
  kissat_message (solver, "%sfeedback-check-classes %" PRIu64, snapshot,
                  fb->check.classes);
  kissat_message (solver, "%sfeedback-check-classes-error %.3g", snapshot,
                  fb->check.classes_error);
  kissat_message (solver, "%sfeedback-check-erwas %" PRIu64, snapshot,
                  fb->check.erwas);
#else
  (void) solver;
  (void) snapshot;
#endif
}

// The 'feedback' section (see 'docs/feedback.md' for every line), each
// line's name after the prefix 'snapshot', which is empty at the end.

static void print_feedback (kissat *solver, const char *snapshot) {
  const feedback *const fb = &solver->policy.feedback;
  const bool chb = fb->started ? fb->chb : kissat_chb (solver);
  const bool lrb = fb->started ? fb->lrb : kissat_lrb (solver);
  if (lrb)
    print_lrb (solver, snapshot);
  else {
    print_measurements (solver, snapshot);
    if (!chb)
      print_vsids_precheck (solver, snapshot);
  }
  print_checks (solver, snapshot);
}

#endif

void kissat_print_feedback_statistics (kissat *solver) {
#ifndef QUIET
  print_feedback (solver, "");
#else
  (void) solver;
#endif
}

#else

int kissat_feedback_dummy_to_avoid_warning;

#endif
