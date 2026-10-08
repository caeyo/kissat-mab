#ifndef _feedback_h_INCLUDED
#define _feedback_h_INCLUDED

// Feedback builds ('./configure --feedback', '-DFEEDBACK', tree builds
// only) measure the feedback of the stable-mode decision: Phase 3's
// measurements M1, M2 and M3 (research plan, Phase 3, Specification).  Nothing
// in the solver reads them and they draw nothing, so a feedback build
// decides, draws and runs the trajectory of the default build at the same
// commit, whatever the options.  Other builds compile none of this.  The
// measurements run in stable mode: focused mode, warm-up and inprocessing
// make no observation, as for the observation counts of UCB ('keys.h').
//
// Observation classes.  An observation of a variable 'v' is, on the VSIDS
// line, a stable-mode conflict whose bump round happens while 'v' is
// assigned, taken before the conflict's backjump: LRB's interval (Liang et
// al. 2016).  On the CHB line it is a payment.  It is 'decided' if the
// reason of 'v' at the time, 'assigned[v].reason', is 'DECISION_REASON',
// and 'implied' otherwise (propagated, or asserted after a conflict).  The
// reason is fixed over an assignment interval, chronological backtracking
// included, so an interval has one class.
//
// LRB's interval in Kissat's order.  Kissat learns before it bumps: a step
// of conflict analysis backjumps, which unassigns the variables above the
// jump level, asserts the learned clause's literal, and only then bumps
// the analyzed variables, most of them unassigned by then.  So the step's
// bump round observes the variables assigned when the step started, those
// the backtrack unassigned included: an interval that a backtrack inside a
// step ends stays open ('deferred') until the round, the round's bumps of
// its variable fall in it, and it closes after the round's increment has
// grown, so that it counts the round.  The literals assigned since the
// backtrack (the asserted literal) open their intervals only then, after
// the round.  A step without a bump round closes its deferred intervals at
// its end, with no round.  This is UCB's count with 'ucbinterval=1' (see
// 'keys.h'), not stage 2's, which closes at the backtrack.  The intervals,
// their record and their closes are the bookkeeping 'intervals.h' shares
// with UCB, whose closes call 'kissat_close_feedback_interval', and whose
// class of an interval, decided, asserted or propagated, this build reads
// as decided or implied.
//
// M1 on the VSIDS line.  Per active variable four sums in the units of the
// score increment, kept as UCB's counts are (grown by the increment,
// rescaled with the scores, on the intervals of 'intervals.h' with their
// increments at assignment): 'n[c]', the bump rounds of the intervals of
// class 'c', added as (inc - opened) / (1/d - 1) when an interval closes,
// so that 'n[DEC] + n[IMP]' is UCB's count with 'ucbinterval=1'; and
// 'r[c]', the increment at every bump of 'v', in the class of the interval
// it falls in.  So p_c = r[c] / n[c] is a decayed
// bump rate per round assigned, and p_all = (r[DEC] + r[IMP]) / (n[DEC] +
// n[IMP]) the pooled one; r[DEC] + r[IMP] is the sum of the score's bumps.
//
// An event of M1 is a decided interval opened by a search pick of the
// policy in stable mode (warm-up's picks and inprocessing's decisions are
// not picks, and span no bump round).  At the pick the four predictors are
// frozen: p_dec and p_imp (undefined while their 'n' is zero), p_all, and
// p_const = sum b / sum k over the decided intervals closed in stable mode
// so far.  At the close (after the step's bump round, for an interval a
// conflict ends) the interval's rounds 'k' (the round counter then minus at
// its start) and bumped rounds 'b', which 'intervals.h' keeps in feedback
// builds, give each predictor 'p' the
// per-round squared error b (1 - p)^2 + (k - b) p^2 and the per-interval
// error (b / k - p)^2.  Events with k = 0 are counted and excluded.  The
// others are summed in groups by which of p_dec and p_imp are defined,
// with a group apart for the few early events without p_const, before any
// decided interval spanned a bump round, and the events with both defined
// are binned in tenths of p_imp and of p_dec (calibration).
//
// M1 on the CHB line.  Per variable two ERWAs 'q[c]', each updated as Q
// is, q <- (1 - alpha) q + alpha r from zero, by the payments of its class
// only, and undefined until that class's first payment, with the plain
// payment counts 'paid[c]'.  An event is a payment of a decided variable,
// one per decision, at the propagation after it; its predictors, read
// before the update, are Q_dec, Q_imp, CHB's own Q, and Q_const, the mean
// of the decided rewards paid before it, and its errors (r - p)^2.
//
// M2 on both lines.  A search pick in stable mode is 'uniform' if the
// mixing coin took it, and of the 'policy' otherwise.  At the pick the age
// of the variable's last observation is binned (never observed, at least
// 10 W, from W to 10 W, below W, with W = 'FEEDBACK_WINDOW'): on the VSIDS
// line in bump rounds since the close of its last interval with a bump
// round, on the CHB line in stable-mode conflicts since its last payment
// (the conflict ending that payment's propagation included).  So is its
// count N (0, below 1, below 5, at least 5): on the VSIDS line n[DEC] +
// n[IMP] in units of the increment, on the CHB line UCB's count on CHB
// scores, which feedback builds keep whatever the options.  The pick is
// pending until its outcome, at most one per variable: on the VSIDS line
// the 'k' and 'b' of its interval, at the close, and on the CHB line the
// payment at the propagation after the pick.  Picks, outcomes and the
// picks still open at the end are printed per kind, and picks are
// outcomes plus open picks.  A pick not followed by its decision, which
// only the unit tests make, is taken back.
//
// M3 on both lines: the yield of a pick.  M2's picks, each pending until
// its interval closes (on the CHB line too, where M2's outcome comes
// earlier, at the payment), with three more quantities.  'y_prop': the
// variables assigned at the pick's level when the search propagation that
// follows its decision ends, the decision included, so at least one, and
// with a conflict those assigned before it; read from the level's trail
// segment, which then holds that level only.  'y_obs': the sum, over the
// conflicts of the pick's interval, of the variables assigned at its level
// at the conflict, before the backjump.  A conflict here is an analysis
// step whose analyzed variables are bumped (VSIDS: its bump round, M1's
// round) or recorded as CHB's participants (CHB): the same steps on both
// lines.  The variables of each open pick's level are taken when the step
// starts, before its backtracks, and added when its analyzed variables are
// bumped or recorded; a pick whose interval a backtrack of the step ends
// closes after that (VSIDS: with its deferred interval; CHB: at the step's
// end), so that the conflict ending it counts.  The variables assigned at
// a level are counted in its frame ('frames.h') at every assignment, since
// chronological backtracking leaves variables of lower levels in a higher
// level's trail segment: a level keeps its count below any backtrack's new
// level, and a level pushed anew starts from zero.  'Y_v': the variable's
// exponential recency-weighted average of 'y_prop' over its earlier picks,
// Y <- (1 - alpha) Y + alpha y_prop with alpha 'FEEDBACK_YIELD_ALPHA',
// starting at the first 'y_prop' (so Y >= 1) and undefined before, frozen
// at the pick in its bin, and updated when the pick's interval closes.
// Sums per kind of pick: by M2's age and count bins (outcomes, sums of
// 'y_prop' and 'y_obs'), by the bin of 'Y_v' (the same with M2's outcome:
// on the VSIDS line k, b and picks bumped, on the CHB line the payment),
// and for uniform picks by 'Y_v' crossed with stale (age never, old or
// stale) against recent.  Also the sums, over every step's addition, of
// the levels' variables and of their trail segments, which differ where
// chronological backtracking left variables in other levels' segments.  A
// pick whose propagation's end is not seen before its interval closes,
// which only the unit tests make, is taken back.
//
// Phase 4's pre-check (research plan, Phase 4, Specification, part 1).
// Three classes: an interval's class in 'intervals.h' is decided, asserted
// (the literal a step of conflict analysis asserts) or propagated, and
// implied is the pool of the last two, so that every line of M1, M2 and M3
// above is what it was.  On the VSIDS line the sums 'n' and 'r' of the
// asserted and of the propagated intervals are kept beside the implied
// ones ('classes'), and at every close with k >= 1 the interval's rate
// b / k, weighted by the increment then, is added to the sums of its class
// (decided or implied) that give E_w, the decayed mean of the interval
// rates.  At a pick the pre-check's predictors are frozen in a record of
// their own: p_ast and p_prop; the weighted rates p_w = (R_dec + w R_imp) /
// (N_dec + w N_imp) for w = 1/4, 1/2, 2, 4 (w = 0, 1 and infinity are
// p_dec, p_all and p_imp); the three-class p_{w,a} = (R_dec + a R_ast + w
// R_prop) / (N_dec + a N_ast + w N_prop) for w = 1/4, 1/2, 1, 2, 4 and a =
// 0, 1/2, 2, 4; E_0, E_1 and E_inf (decided intervals, both, implied ones);
// and the yield predictors, the mean b / k of the events closed before the
// pick in the event's bin of 'Y_v' (B_Y), in its tenth of p_1 (B_p) and in
// both (B_Yp), which are scored together, at the events where all three
// are defined, with p_1 beside them on the same events.  Each predictor
// scores the event in its group of M1, over the events where it is
// defined, which are counted.
//
// The LRB line ('lrb=1' with 'chb=1', see 'lrb.h'): M1 on LRB's reward.
// Per variable ERWAs, from zero with LRB's step size, of the rewards of
// the decided, asserted, propagated and implied intervals (Q_dec, Q_ast,
// Q_prop, Q_imp), and weighted ones fed by every class: Q_w with the step
// alpha min (1, w) for an implied interval and alpha min (1, 1/w) for a
// decided one (w = 1/4, 1/2, 2, 4), and Q_{w,a} with the step alpha w_c /
// max (1, w, a), where w_dec = 1, w_prop = w and w_ast = a; Q_1 is LRB's own
// Q.  They are updated where LRB updates Q ('kissat_feedback_lrb_close').
// An event is the close of the decided interval of a search pick in stable
// mode, with LRB's reward if it spanned a conflict, else it is counted
// apart, scored against the predictors frozen at the pick: Q_dec, Q_imp,
// LRB's Q and Q_const (the mean reward of the decided intervals closed so
// far), in the groups and calibration bins of the CHB line, and the
// pre-check's.  M2 and M3 do not run on the LRB line.
//
// The argmax-differ pass ('kissat_feedback_differ').  At every search
// sample of the decision metrics (see 'policy.h') one pass over the
// unassigned active variables takes the argmax, the smallest index among
// ties, of each candidate key and counts the samples at which it differs
// from the reference's.  VSIDS line, reference S_1 = R_dec + R_imp: S_w =
// R_dec + w R_imp, S_{w,a} = R_dec + a R_ast + w R_prop, the rate p_1 (zero
// without a count), the locality key S_1 lambda^(c - u), the interval key
// (E_1's numerator) and the score, Argmax's own.  LRB line, reference LRB's
// Q: Q_w, Q_{w,a}, Q lambda^(c - u) and the score.  Here 'c' counts the
// stable-mode steps of conflict analysis whose variables are bumped or
// recorded as CHB's participants (M3's conflicts, 'steps'), 'u' is 'c' at
// the variable's last stable-mode unassignment ('unassigned'), taken at
// the backtrack, and lambda is 'FEEDBACK_LOCALITY'; the locality key is
// compared in logarithms.  The CHB line has no pass.
//
// The snapshot ('kissat_feedback_snapshot').  The first time the search
// tests its conflict limit after 'FEEDBACK_SNAPSHOT' conflicts, the whole
// section is printed, each line under the prefix 'snapshot-', as a run
// with that limit would print it at its end.
//
// Checks in assertion builds ('-c', which '--shadow' implies).  When a step
// of conflict analysis starts, before its backtracks, the active variables
// on the trail are listed; after the step's bump loop each of them has the
// round counted and its bump read from the analyzed variables directly
// (outside a step, which only the unit tests make, the trail's), and at
// every close the interval's 'k' and 'b' must equal those counts.  Every
// 1000 picks, under UCB on VSIDS scores (which in feedback builds counts
// LRB's interval) 'n[DEC] + n[IMP]' must equal UCB's count for every active
// variable, an open interval added as leaving stable mode would add it, to
// 1e-12 of 1 + N; on CHB scores under UCB or TS
// the count must equal UCB's bitwise, and in shadow builds 'paid[DEC] +
// paid[IMP]' the payments that shadow mode counts.  M3 by brute force:
// when a step starts every level's variables are counted from the trail
// and must equal its frame's count, and those of the open picks' levels
// go to a shadow sum of 'y_obs' when the step's variables are bumped or
// recorded; at the end of a pick's propagation its level's variables are
// counted from the trail; both shadow sums must equal 'y_prop' and 'y_obs'
// when the pick's interval closes.  At the end picks must be outcomes plus
// open picks, for M2 and for M3, and M3's outcomes by age, by count and by
// the bin of 'Y_v' must agree.  The pre-check: at a pick every predictor is
// computed a second time, from the per-variable sums and shadow tables of
// the yield predictors' cells, and at the event the frozen one must equal
// it bitwise; every 1000 picks the asserted and propagated sums must add
// up to the implied ones to 1e-12 of one plus the implied sum, in units of
// the increment, as UCB's counts; at every sample a second pass,
// key by key, must find the differ pass's argmaxes; on the LRB line the
// check keeps Q_1, which must equal LRB's Q bitwise at every update.  A
// failed check is a fatal error.

#ifdef FEEDBACK

#ifdef HEAPARGMAX
#error "'FEEDBACK' needs a tree build ('HEAPARGMAX' excludes it)"
#endif

#include "stack.h"

#include <stdbool.h>
#include <stdint.h>

#define FEEDBACK_WINDOW 20 // W, bump rounds (VSIDS) or conflicts (CHB)

#define FEEDBACK_DEC 0 // decided
#define FEEDBACK_IMP 1 // implied

// M1's predictors: p_dec, p_imp, p_all, p_const on the VSIDS line, and
// Q_dec, Q_imp, CHB's Q, Q_const on the CHB line.

#define FEEDBACK_PREDICT_DEC 0
#define FEEDBACK_PREDICT_IMP 1
#define FEEDBACK_PREDICT_ALL 2
#define FEEDBACK_PREDICT_CONST 3
#define FEEDBACK_PREDICTORS 4

// M1's groups of events (with k >= 1 on the VSIDS line).

#define FEEDBACK_GROUP_BOTH 0     // p_dec and p_imp defined
#define FEEDBACK_GROUP_NO_IMP 1   // p_imp undefined
#define FEEDBACK_GROUP_NO_DEC 2   // p_dec undefined
#define FEEDBACK_GROUP_NEITHER 3  // both undefined
#define FEEDBACK_GROUP_NO_CONST 4 // p_const undefined (no error sums)
#define FEEDBACK_GROUPS 5

#define FEEDBACK_BINS 10 // calibration bins, tenths

// M2: kinds of pick, ages of the last observation, counts.

#define FEEDBACK_POLICY 0
#define FEEDBACK_UNIFORM 1
#define FEEDBACK_KINDS 2

#define FEEDBACK_AGE_NEVER 0  // never observed
#define FEEDBACK_AGE_OLD 1    // at least 10 W
#define FEEDBACK_AGE_STALE 2  // from W to 10 W
#define FEEDBACK_AGE_RECENT 3 // below W
#define FEEDBACK_AGES 4

#define FEEDBACK_COUNT_ZERO 0  // N = 0
#define FEEDBACK_COUNT_BELOW1 1 // 0 < N < 1
#define FEEDBACK_COUNT_BELOW5 2 // 1 <= N < 5
#define FEEDBACK_COUNT_ABOVE5 3 // N >= 5
#define FEEDBACK_COUNTS 4

// M3: the step size of 'Y_v', its bins, and the uniform picks' ages
// crossed with them.

#define FEEDBACK_YIELD_ALPHA 0.1

#define FEEDBACK_YIELD_NONE 0    // undefined
#define FEEDBACK_YIELD_BELOW2 1  // 1 <= Y < 2
#define FEEDBACK_YIELD_BELOW4 2  // 2 <= Y < 4
#define FEEDBACK_YIELD_BELOW16 3 // 4 <= Y < 16
#define FEEDBACK_YIELD_BELOW64 4 // 16 <= Y < 64
#define FEEDBACK_YIELD_ABOVE64 5 // Y >= 64
#define FEEDBACK_YIELDS 6

#define FEEDBACK_STALE 0  // age never, old or stale
#define FEEDBACK_RECENT 1 // age recent

// A variable's state: its pending pick with kind, age bin and count bin,
// and M3's pick, pending with the bin of 'Y_v' until its interval closes.

#define FEEDBACK_PENDING 1u
#define FEEDBACK_KIND_SHIFT 1
#define FEEDBACK_AGE_SHIFT 2
#define FEEDBACK_COUNT_SHIFT 4
#define FEEDBACK_YIELD 512u
#define FEEDBACK_YIELD_SHIFT 10

// Phase 4's pre-check.  The implied classes of the three-class sums, the
// snapshot's conflicts and the locality key's lambda.

#define FEEDBACK_AST 0  // asserted
#define FEEDBACK_PROP 1 // propagated

#define FEEDBACK_SNAPSHOT 100000
#define FEEDBACK_LOCALITY 0.95

// The weights: the two-class w beside 0, 1 and infinity (1/4, 1/2, 2, 4),
// and the three-class grid of w (1/4, 1/2, 1, 2, 4) by a (0, 1/2, 2, 4),
// index w * FEEDBACK_GRID_A + a.

#define FEEDBACK_WEIGHTS 4
#define FEEDBACK_GRID_W 5
#define FEEDBACK_GRID_A 4
#define FEEDBACK_GRID (FEEDBACK_GRID_W * FEEDBACK_GRID_A)

// The pre-check's predictors in a pending pick's record.  VSIDS line:
// p_ast, p_prop, p_w, p_{w,a}, E_0, E_1, E_inf, B_Y, B_p, B_Yp, and p_1 on
// the events where those three are scored.  LRB line, beside M1's four:
// Q_ast, Q_prop, Q_w and Q_{w,a}.

#define FEEDBACK_V_AST 0
#define FEEDBACK_V_PROP 1
#define FEEDBACK_V_W 2
#define FEEDBACK_V_GRID (FEEDBACK_V_W + FEEDBACK_WEIGHTS)
#define FEEDBACK_V_MEAN (FEEDBACK_V_GRID + FEEDBACK_GRID)
#define FEEDBACK_V_BIN (FEEDBACK_V_MEAN + 3)
#define FEEDBACK_V_PREDICTORS (FEEDBACK_V_BIN + 4)

#define FEEDBACK_L_AST 0
#define FEEDBACK_L_PROP 1
#define FEEDBACK_L_W 2
#define FEEDBACK_L_GRID (FEEDBACK_L_W + FEEDBACK_WEIGHTS)
#define FEEDBACK_L_PREDICTORS (FEEDBACK_L_GRID + FEEDBACK_GRID)

#define FEEDBACK_EXTRA FEEDBACK_V_PREDICTORS // the larger of the two

// The LRB line's ERWAs by class.

#define FEEDBACK_Q_DEC 0
#define FEEDBACK_Q_AST 1
#define FEEDBACK_Q_PROP 2
#define FEEDBACK_Q_IMP 3

// The differ pass's keys: S_w (VSIDS) or Q_w (LRB) for w = 0, 1/4, 1/2, 2,
// 4 and infinity, the grid, then on the VSIDS line the rate, the locality
// key, the interval key and the score, on the LRB line the locality key
// and the score.

#define FEEDBACK_KEY_W 0
#define FEEDBACK_KEY_GRID 6
#define FEEDBACK_KEY_V_RATE (FEEDBACK_KEY_GRID + FEEDBACK_GRID)
#define FEEDBACK_KEY_V_LOCALITY (FEEDBACK_KEY_V_RATE + 1)
#define FEEDBACK_KEY_V_INTERVAL (FEEDBACK_KEY_V_RATE + 2)
#define FEEDBACK_KEY_V_SCORE (FEEDBACK_KEY_V_RATE + 3)
#define FEEDBACK_V_KEYS (FEEDBACK_KEY_V_RATE + 4)
#define FEEDBACK_KEY_L_LOCALITY (FEEDBACK_KEY_GRID + FEEDBACK_GRID)
#define FEEDBACK_KEY_L_SCORE (FEEDBACK_KEY_L_LOCALITY + 1)
#define FEEDBACK_L_KEYS (FEEDBACK_KEY_L_LOCALITY + 2)
#define FEEDBACK_KEYS FEEDBACK_V_KEYS // the larger of the two

// What LRB's close of an interval did ('kissat_feedback_lrb_close').

#define FEEDBACK_LRB_NONE 0
#define FEEDBACK_LRB_PAID 1    // Q updated with a reward
#define FEEDBACK_LRB_SKIPPED 2 // no conflict in the interval, no update
#define FEEDBACK_LRB_IGNORED 3 // an interval LRB's walk did not open

typedef struct feedback_sums feedback_sums;
typedef struct feedback_yields feedback_yields;
typedef struct feedback_extra feedback_extra;
typedef struct feedback_cells feedback_cells;
typedef struct feedback_classes feedback_classes;
typedef struct feedback_erwas feedback_erwas;
typedef struct feedback_record feedback_record;
typedef struct feedback feedback;

// Sums over a set of events or outcomes: on the VSIDS line intervals ('k'
// rounds, 'b' of them with a bump, 'bumped' with b >= 1), and per
// predictor the per-round ('round') and per-interval ('interval') squared
// errors; on the CHB line payments, their rewards 'r' and per predictor
// the squared error (r - p)^2 ('interval').

struct feedback_sums {
  uint64_t n, k, b, bumped;
  double r;
  double round[FEEDBACK_PREDICTORS];
  double interval[FEEDBACK_PREDICTORS];
};

// M3's sums over a set of picks whose intervals closed: their number, M2's
// outcome ('k', 'b' and 'bumped' on the VSIDS line, the payment 'r' on the
// CHB line), and the sums of 'y_prop' and 'y_obs'.

struct feedback_yields {
  uint64_t n, k, b, bumped;
  double r;
  uint64_t prop, obs;
};

// The pre-check's sums over the events of a group of M1: per predictor the
// events where it is defined, and there its per-round and per-interval
// errors (on the LRB line the reward's, in 'interval').

struct feedback_extra {
  uint64_t n[FEEDBACK_EXTRA];
  double round[FEEDBACK_EXTRA];
  double interval[FEEDBACK_EXTRA];
};

// The yield predictors' cells: the events closed with k >= 1 and the sums
// of their rates b / k, by bin of 'Y_v' frozen at the pick, by tenth of
// p_1, and by both.

struct feedback_cells {
  uint64_t n_y[FEEDBACK_YIELDS], n_p[FEEDBACK_BINS];
  uint64_t n_yp[FEEDBACK_YIELDS][FEEDBACK_BINS];
  double y[FEEDBACK_YIELDS], p[FEEDBACK_BINS];
  double yp[FEEDBACK_YIELDS][FEEDBACK_BINS];
};

// Per variable, VSIDS line: the rounds and bumps of the asserted and of the
// propagated intervals, and the sums of E_w by class, decided and implied,
// all in units of the increment.

struct feedback_classes {
  double n[2], r[2];   // asserted, propagated
  double rates[2];     // decided, implied: increment at the close b / k
  double weights[2];   // and the increment, at closes with k >= 1
};

// Per variable, LRB line: the ERWAs and the updates by class (decided,
// asserted, propagated).

struct feedback_erwas {
  double q[4];                // Q_dec, Q_ast, Q_prop, Q_imp
  double w[FEEDBACK_WEIGHTS]; // Q_w
  double grid[FEEDBACK_GRID]; // Q_{w,a}
  unsigned updates[3];
};

// The predictors of a pending pick frozen for the pre-check: on the LRB
// line M1's four too (on the VSIDS line those are in 'frozen'), on the
// VSIDS line the cells of the yield predictors (a tenth of p_1, or
// 'FEEDBACK_BINS' if p_1 is undefined).  Assertion builds compute them a
// second time.

struct feedback_record {
  double base[FEEDBACK_PREDICTORS];
  double extra[FEEDBACK_EXTRA];
  unsigned bin_y, bin_p;
#ifndef NDEBUG
  double check_base[FEEDBACK_PREDICTORS];
  double check_extra[FEEDBACK_EXTRA];
  unsigned check_y, check_p;
#endif
};

typedef STACK (feedback_record) feedback_records;

struct feedback {
  bool started;      // the arrays exist (from the start of the search)
  bool chb;          // CHB scores (CHB or LRB line), VSIDS line otherwise
  bool lrb;          // LRB line ('lrb=1')
  bool snapshot;     // the snapshot was printed
  unsigned size;     // variables the arrays have room for
  double growth;     // 1/d, d the score decay
  double increment;  // CHB: the counts' own increment, as UCB's
  uint16_t *state;   // pending pick (M2), pick pending its interval (M3)
  double *n[2];      // VSIDS: rounds by class (inflated)
  double *r[2];      // VSIDS: bumps by class (inflated)
  double *frozen;    // VSIDS: the four predictors of a pending pick
  uint64_t *last;    // VSIDS: round counter at the close of the last
                     // interval with a round (zero: never observed)
  double *q[2];      // CHB: ERWAs by class
  uint64_t *paid[2]; // CHB: payments by class
  double *count;     // CHB: UCB's count (inflated)
  uint64_t *latest;  // CHB: stable-mode conflicts at the last payment
#ifdef SHADOW
  uint64_t *repaid; // CHB: payments counted by shadow mode
#endif
  double *yield;        // M3: Y_v (zero: undefined)
  unsigned *propagated; // M3: y_prop of the pending pick (zero: not yet)
  uint64_t *observed;   // M3: y_obs of the pending pick
  double *reward;       // M3, CHB: the payment of the pending pick
  unsigned yielding;    // M3: the pick awaiting its propagation's end + 1
  unsigneds staged;     // M3: the step's open picks and their levels'
                        // variables, pairwise, added at its conflict
  uint64_t staged_levels;   // M3: their sum
  uint64_t staged_segments; // M3: the sum of their trail segments
  uint64_t steps;        // VSIDS, LRB: stable-mode steps that bumped or
                         // recorded participants ('c' of the locality key)
  double log_lambda;     // the logarithm of 'FEEDBACK_LOCALITY'
  uint64_t *unassigned;  // VSIDS, LRB: 'steps' at the last stable-mode
                         // unassignment ('u'), zero if none
  unsigned *slot;        // VSIDS, LRB: the pending pick's record + 1
  feedback_classes *classes; // VSIDS: three classes and E_w's sums
  feedback_erwas *erwas;     // LRB: the ERWAs
  double factors[3][FEEDBACK_WEIGHTS + FEEDBACK_GRID]; // LRB: of alpha in
                             // the steps of Q_w, Q_{w,a} by class
  feedback_records records;  // the pending picks' frozen predictors
  unsigneds free;            // records free for reuse
  struct {
    unsigned how;       // LRB: what its close of the interval just did
    double reward;      // and with which reward
    double alpha;       // and step size
  } closing;
  struct {
    uint64_t intervals[2]; // VSIDS: closed intervals by class (LRB:
                           // updates)
    uint64_t bumps[2][2];  // VSIDS: bumps [in an ended interval][class]
    uint64_t unobserved;   // VSIDS: bumps in no interval (unit tests)
    uint64_t sum_k;        // VSIDS: k and b summed over the closed
    uint64_t sum_b;        // decided intervals (p_const)
    uint64_t sum_n;        // CHB, LRB: decided payments (LRB: updates)
    double sum_r;          // and their rewards (Q_const)
    uint64_t events;       // events (VSIDS, LRB: closed)
    uint64_t zero;         // VSIDS: events with k = 0 (LRB: interval 0)
    feedback_sums group[FEEDBACK_GROUPS];
    feedback_sums calibration[2][FEEDBACK_BINS]; // by p_dec, by p_imp
    uint64_t picks;           // LRB: picks (on the other lines M2's)
    uint64_t intervals3[2];   // VSIDS: closed intervals (LRB: updates),
                              // asserted and propagated
    uint64_t bumps3[2][2];    // VSIDS: bumps [ended][asserted, propagated]
    feedback_extra extra[FEEDBACK_GROUPS - 1]; // groups but 'NO_CONST'
    feedback_sums calibration3[2][FEEDBACK_BINS]; // by p_ast, by p_prop
    feedback_cells cells;     // VSIDS: the yield predictors' cells
  } m1;
  struct {
    uint64_t picks[FEEDBACK_KINDS];
    feedback_sums age[FEEDBACK_KINDS][FEEDBACK_AGES];
    feedback_sums count[FEEDBACK_KINDS][FEEDBACK_COUNTS];
  } m2;
  struct {
    uint64_t picks[FEEDBACK_KINDS];
    feedback_yields age[FEEDBACK_KINDS][FEEDBACK_AGES];
    feedback_yields count[FEEDBACK_KINDS][FEEDBACK_COUNTS];
    feedback_yields yield[FEEDBACK_KINDS][FEEDBACK_YIELDS];
    feedback_yields crossed[2][FEEDBACK_YIELDS]; // uniform: stale, recent
    uint64_t levels;   // every step's additions: the levels' variables
    uint64_t segments; // and their trail segments
  } m3;
  struct {
    uint64_t samples;               // search samples of the metrics
    uint64_t differ[FEEDBACK_KEYS]; // of which the key's argmax differs
  } differ;
#ifndef NDEBUG
  struct {
    unsigneds listed;   // VSIDS: active variables assigned at the step
    uint64_t *rounds;   // VSIDS: rounds counted at the bump rounds
    uint64_t *bumped;   // VSIDS: of which with a bump of the variable
    uint64_t *marked;   // VSIDS: the round in which it was analyzed
    uint64_t picks;     // picks (search and warm-up)
    uint64_t complete;  // complete checks
    uint64_t counts;    // counts compared with UCB's
    double error;       // largest relative difference of those
    uint64_t chb;       // CHB counts compared with UCB's
    uint64_t payments;  // payment counts compared with shadow mode's
    uint64_t intervals; // intervals compared with the counted rounds
    unsigned *propagated; // M3: y_prop counted from the trail
    uint64_t *observed;   // M3: y_obs counted from the trail
    unsigneds staged;     // M3: the step's open picks, counted likewise
    unsigneds levels;     // M3: variables per level, from the trail
    uint64_t steps;       // M3: levels compared with their frames' counts
    uint64_t yields;      // M3: picks compared with the shadow sums
    double *q1;           // LRB: Q_1, which must be LRB's Q
    feedback_erwas *shadow; // LRB: the ERWAs, updated by the check
    uint64_t sum_n;       // LRB: Q_const's sums, by the check
    double sum_r;
    feedback_cells cells; // VSIDS: the shadow tables of the cells
    uint64_t predictors;  // events whose predictors were compared
    uint64_t differ;      // samples whose argmaxes were compared
    uint64_t classes;     // three-class sums compared with the implied
    double classes_error; // the largest relative difference of those
    uint64_t erwas;       // LRB updates whose Q_1 was compared
  } check;
#endif
};

struct kissat;

void kissat_start_feedback (struct kissat *);
void kissat_resize_feedback (struct kissat *, unsigned size);
void kissat_release_feedback (struct kissat *);

// Compaction: moves the entries of 'from' to 'to', and clears 'idx'.

void kissat_move_feedback (struct kissat *, unsigned from, unsigned to);
void kissat_clear_feedback (struct kissat *, unsigned idx);

// VSIDS line: 'idx' is bumped in the current round (before its score), and
// the round ends (after the increment has grown, before the closes it ends
// in 'intervals.h').

void kissat_feedback_bump (struct kissat *, unsigned idx);
void kissat_feedback_round_end (struct kissat *);

// A step of conflict analysis starts, before its backtracks, and ends,
// after its bump round (VSIDS) or its record of CHB's participants (CHB)
// if it has one, before the closes it deferred (see 'intervals.h').

void kissat_feedback_begin_analysis (struct kissat *);
void kissat_feedback_end_analysis (struct kissat *);

// The assignment interval of 'idx', of class 'c' (see 'intervals.h'),
// closes; and the scores are rescaled by 'factor'.

void kissat_close_feedback_interval (struct kissat *, unsigned idx,
                                     unsigned c);
void kissat_rescale_feedback (struct kissat *, double factor);

// CHB line: a payment of 'reward' to 'idx' whose score was 'old_q', at
// step size 'alpha', in a propagation that started after 'conflicts'
// stable-mode conflicts; and a stable-mode conflict, after its payments.

void kissat_feedback_paid (struct kissat *, unsigned idx, double reward,
                           double alpha, double old_q, uint64_t conflicts);
void kissat_feedback_chb_conflict (struct kissat *);

#ifdef SHADOW
void kissat_shadow_feedback_paid (struct kissat *, unsigned idx);
#endif

// Every pick of the policy, 'uniform' if mixing's coin took it.

void kissat_feedback_pick (struct kissat *, unsigned idx, bool uniform);

// M3: a search propagation ends (every one, in either mode), and a step's
// analyzed variables are bumped or recorded as CHB's participants (in
// stable mode).

void kissat_feedback_propagated (struct kissat *);
void kissat_feedback_observe (struct kissat *);

// LRB line: LRB's close of the assignment interval whose close follows
// ('kissat_close_interval'), 'how' as 'FEEDBACK_LRB_...', with its reward
// and step size if it paid one.

void kissat_feedback_lrb_close (struct kissat *, unsigned how,
                                double reward, double alpha);

// A search sample of the decision metrics: the differ pass (VSIDS and LRB
// lines).

void kissat_feedback_differ (struct kissat *);

// Where the search tests its conflict limit: prints the snapshot the first
// time 'FEEDBACK_SNAPSHOT' conflicts are reached.  Always false, so that
// the search goes on as without it.

bool kissat_feedback_snapshot (struct kissat *);

void kissat_print_feedback_statistics (struct kissat *);

#endif

#endif
