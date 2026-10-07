#ifndef _keys_h_INCLUDED
#define _keys_h_INCLUDED

// Policies with keys of their own (tree builds, see 'policy.h'): P1, the
// perturbed leader per episode (option 'perturbed'), TS, Thompson sampling
// with the posterior sample held for an episode ('thompson'), and UCB,
// upper confidence bounds ('ucb').  At most one of them, or Sample
// ('softmax'), is selected, without mixing ('gammappm' zero), and P1 only
// on VSIDS scores.  Each decides by the tree's maximum over a key per
// variable, ties going to the smaller index, without weights, and the key
// combines the variable's score with a term 'x' of the policy's own:
//
//   VSIDS scores s:   key = s * e^x, and a score of zero keeps key zero,
//   CHB scores Q:     key = Q + x,
//
// so that the order on VSIDS scores is that of ln s + x, and x = 0 gives
// the scores bit for bit.  The term is
//
//   P1:   x = g / eta, g drawn from the Gumbel distribution, with eta =
//         2^etalog2 (Sample's option), so that the first pick after a draw
//         has Sample's distribution at eta (the Gumbel-max trick),
//
//   TS:   x = kappa * z / sqrt (1 + S), z drawn from the standard normal
//         distribution and S = s / inc the score in units of the current
//         score increment, a decayed count of bumps whose posterior has the
//         spread 1 / sqrt (1 + S) on the log scale (prior one pseudo-bump);
//         on CHB scores x = kappa * z / sqrt (1 + N), N the variable's
//         observation count below (one pseudo-observation),
//
//   UCB:  x = c * sqrt (ln T / (1 + N)), N the variable's observation
//         count and T their sum over the active variables (one
//         pseudo-observation; x is zero while T is at most one),
//
// with kappa = thompsonkappa / 1000 and c = ucbc / 1000.  So TS at kappa
// zero and UCB at c zero decide as Argmax.  A rescale multiplies every
// score, and on the VSIDS line every key, by the same factor, and the
// rebuild that follows every rescale and 'reorder' recomputes the keys.
// The keys are kept in the tree's leaves, where Argmax keeps scores; the
// estimator, and every reader of scores outside the policy, keeps scores.
//
// For VSIDS scores 'term' holds e^x, for CHB scores x.  The product s * e^x
// stays a finite double while x stays below about 360, since scores stay
// below about 20 times 'MAX_SCORE': for P1 at eta 1/8 and above (|g| is at
// most 36.7 with 53-bit uniforms), TS up to kappa 40 (|z| at most 8.6) and
// UCB up to c 70 (ln T below 21), which covers every setting the plan
// names.  Beyond, keys may overflow to infinity and tie.
//
// Draw points.  A draw point is the start of the search in stable mode,
// every entry to stable mode, and every stable-mode restart ('redraw=0',
// the default) or every rephase ('redraw=1'), after their backtracking.
// At a draw point P1 draws g and TS draws z for every active variable in
// index order from the policy's generator, each from 53-bit uniforms with
// zero excluded (g = -ln (-ln u); z by Box-Muller, both normals of a pair
// used in turn), the terms are recomputed and the tree is rebuilt.  UCB
// draws nothing: it recomputes the sum T and every term at every
// stable-mode restart and entry to stable mode, whatever 'redraw' says,
// and these count as its draw points.  A variable activated in stable mode
// between draw points draws its own at activation.  In between, P1's terms
// stay fixed, TS recomputes a variable's term at its bumps (VSIDS) or
// payments (CHB), where its evidence changes, and UCB at its unassignment
// in stable mode, with the sum of the last draw point.
//
// Observation counts (UCB, and TS on CHB scores).  N = sum d^age over the
// variable's observations, with d the score decay (option 'decay', d =
// 0.95 by default), kept in inflated units as VSIDS scores are: an
// observation adds the current increment to 'count', and N = count / inc.
//
//   VSIDS scores: an observation is a bump round during which the variable
//   was assigned in stable mode, and 'inc' the score increment, which
//   every bump round grows by 1/d.  When stable-mode backtracking unassigns
//   the variable, 'count' grows by (inc - inc_a) / (1/d - 1), the sum of
//   the increments of the rounds since its assignment, 'inc_a' being the
//   increment then ('opened').  Assignment needs no hook: before the
//   increment changes (a bump round, a rescale), before every stable-mode
//   backtrack and when stable mode is left, the literals assigned since the
//   last record ('counted', a trail position) are recorded with the current
//   increment, which is the one they were assigned at.  Shrinking the trail
//   moves 'counted' down with it; compaction, which renames the trail's
//   literals in place and moves 'opened' with its variables, leaves it.
//   Leaving stable mode closes every open interval, and entering it opens
//   one for every assigned variable.  Counts and 'opened' are rescaled with
//   the scores.
//
//   Kissat bumps after the backjump of a conflict's analysis, so the
//   rounds completed while a variable is assigned never include the
//   conflict whose backjump unassigns it: the count lags LRB's interval
//   (Liang et al. 2016) by that conflict, where most of a variable's bumps
//   land.  This was stage 2's count, which 'ucbinterval=0' keeps.  By
//   default ('ucbinterval=1') the count is LRB's interval, the option being
//   ignored but for UCB on VSIDS scores: a bump round observes every variable
//   assigned when the analysis step that makes it starts, before the
//   step's backtracks.  A step is one round of 'kissat_analyze', between
//   'kissat_policy_begin_analysis' and 'kissat_policy_end_analysis'.  An
//   interval that a backtrack inside a step ends stays open ('deferred')
//   until the step's bump round has grown the increment, so that it counts
//   that round, and the literals assigned since the backtrack (the learned
//   clause's asserted literal) are recorded only then, so that their
//   intervals start after it.  A step without a bump round closes its
//   deferred intervals at its end, with no round added.  The term of a
//   deferred variable is recomputed when its interval closes.
//
//   CHB scores: an observation is a payment, and 'inc' an increment of the
//   counts' own, which grows by 1/d at every stable-mode conflict, after
//   that conflict's payments, and is rescaled, with every count, when it
//   exceeds 'MAX_SCORE'.
//
// A pick is the tree's maximum, removing assigned variables on the way as
// Argmax does.  On VSIDS scores a pick of key zero, which happens when
// every unassigned variable has score zero, takes the smallest index,
// Argmax's choice, and counts as a fallback, as Sample's does; on CHB
// scores there is none.  For the decision metrics a pick is a point mass
// on its choice.

#include "stack.h"

#include <stdbool.h>
#include <stdint.h>

#define KEYS_NONE 0      // Argmax and Sample
#define KEYS_PERTURBED 1 // P1
#define KEYS_THOMPSON 2  // TS
#define KEYS_UCB 3       // UCB

#define KEYS_PRIOR 1.0 // TS's prior bump, the counts' prior observation

typedef struct keys keys;

struct keys {
  unsigned kind;     // 'KEYS_NONE', 'KEYS_PERTURBED', ...
  bool noise;        // keys may differ from scores (P1, TS and UCB with
                     // a positive factor)
  bool redraw;       // P1 and TS draw at rephases, not at restarts
  bool counts;       // observation counts (UCB, TS on CHB scores)
  bool intervals;    // increments at assignment (UCB on VSIDS scores)
  bool interval;     // ... counting LRB's interval ('ucbinterval=1')
  bool analyzing;    // ... inside a step of conflict analysis
  bool deferring;    // ... a backtrack of the step deferred closes
  bool spared;       // TS: 'spare' holds the second normal of a pair
  unsigned size;     // variables the arrays have room for
  unsigned counted;  // UCB on VSIDS scores: trail recorded up to here
  double factor;     // kappa (TS) or c (UCB)
  double scale;      // UCB: c * sqrt (ln T) at the last draw point
  double total;      // UCB: T at the last draw point
  double growth;     // 1/d
  double increment;  // counts on CHB scores: their own increment
  double spare;      // TS: second normal of the last pair
  double *term;      // e^x (VSIDS scores) or x (CHB scores)
  double *normal;    // TS: z
  double *count;     // UCB, TS on CHB scores: inflated counts
  double *opened;    // UCB on VSIDS scores: increment at assignment
  uint64_t draws;    // draw points
  uint64_t ticks;    // clock ticks spent at draw points (metrics)
  unsigneds deferred; // 'interval': variables whose closes are deferred
#ifdef SHADOW
  double *recount;     // shadow mode: the counts recounted (see 'policy.h')
  uint64_t *recounted; // the bump round or conflict 'recount' is decayed to
  unsigneds observed;  // 'interval': assigned when the step started
#endif
};

struct kissat;

// At the start of the search: selects the policy, and if it is one of the
// three allocates its arrays, and in stable mode draws.

void kissat_start_keys (struct kissat *);

// Draw points (see above): every entry to stable mode, every stable-mode
// restart and every rephase, each after its backtracking.

void kissat_draw_keys (struct kissat *);
void kissat_restart_keys (struct kissat *);
void kissat_rephase_keys (struct kissat *);

// 'idx' was activated in stable mode: its own draw, or UCB's term.

void kissat_activate_keys (struct kissat *, unsigned idx);

// Stable mode is left: closes the open intervals of UCB's counts.

void kissat_leave_stable_keys (struct kissat *);

// UCB counting LRB's interval: closes the intervals deferred in the
// current analysis step, at the current increment (see above).

void kissat_finish_deferred_keys (struct kissat *);

// Rescales UCB's counts and increments at assignment on VSIDS scores by
// the scores' factor, and on CHB scores the counts with their increment.

void kissat_rescale_keys (struct kissat *, double factor);
void kissat_rescale_chb_counts (struct kissat *);

void kissat_resize_keys (struct kissat *, unsigned size);
void kissat_release_keys (struct kissat *);

// Compaction: moves the entries of 'from' to 'to', and clears 'idx'.

static inline void kissat_move_keys (keys *keys, unsigned from,
                                     unsigned to) {
  if (!keys->kind)
    return;
  keys->term[to] = keys->term[from];
  if (keys->kind == KEYS_THOMPSON)
    keys->normal[to] = keys->normal[from];
  if (keys->counts)
    keys->count[to] = keys->count[from];
  if (keys->intervals)
    keys->opened[to] = keys->opened[from];
#ifdef SHADOW
  if (keys->counts) {
    keys->recount[to] = keys->recount[from];
    keys->recounted[to] = keys->recounted[from];
  }
#endif
}

static inline void kissat_clear_keys (keys *keys, unsigned idx) {
  if (!keys->kind)
    return;
  keys->term[idx] = 0;
  if (keys->kind == KEYS_THOMPSON)
    keys->normal[idx] = 0;
  if (keys->counts)
    keys->count[idx] = 0;
  if (keys->intervals)
    keys->opened[idx] = 0;
#ifdef SHADOW
  if (keys->counts) {
    keys->recount[idx] = 0;
    keys->recounted[idx] = 0;
  }
#endif
}

#endif
