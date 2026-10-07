#ifndef _feedback_h_INCLUDED
#define _feedback_h_INCLUDED

// Feedback builds ('./configure --feedback', '-DFEEDBACK', tree builds
// only) measure the feedback of the stable-mode decision: Phase 3's
// measurements M1 and M2 (research plan, Phase 3, Specification).  Nothing
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
// 'keys.h'), not stage 2's, which closes at the backtrack.
//
// M1 on the VSIDS line.  Per active variable four sums in the units of the
// score increment, kept as UCB's counts are (grown by the increment,
// rescaled with the scores, the increment at assignment recorded in
// 'opened' without a hook in propagation, intervals closed at stable-mode
// unassignment, or after the step's bump round, and when stable mode is
// left, the record kept across compaction): 'n[c]', the bump rounds of the
// intervals of class 'c', added as (inc - opened) / (1/d - 1) when an
// interval closes, so that 'n[DEC] + n[IMP]' is UCB's count with
// 'ucbinterval=1'; and 'r[c]', the increment at every bump of 'v', in the
// class of the interval it falls in.  So p_c = r[c] / n[c] is a decayed
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
// its start) and bumped rounds 'b' give each predictor 'p' the
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
// Checks in assertion builds ('-c', which '--shadow' implies).  When a step
// of conflict analysis starts, before its backtracks, the active variables
// on the trail are listed; after the step's bump loop each of them has the
// round counted and its bump read from the analyzed variables directly
// (outside a step, which only the unit tests make, the trail's), and at
// every close the interval's 'k' and 'b' must equal those counts.  Every
// 1000 picks, under UCB with 'ucbinterval=1' 'n[DEC] + n[IMP]' must equal
// UCB's count for every active variable, an open interval added as leaving
// stable mode would add it, to 1e-12 of 1 + N, and both records of the
// increment at assignment must agree bitwise; on CHB scores under UCB or TS
// the count must equal UCB's bitwise, and in shadow builds 'paid[DEC] +
// paid[IMP]' the payments that shadow mode counts.  At the end picks must
// be outcomes plus open picks.  A failed check is a fatal error.

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

// A variable's state: its pending pick with kind, age bin and count bin,
// and on the VSIDS line whether its interval is open (recorded), and
// whether a backtrack inside an analysis step ended it, deferring its close
// to the step's bump round, with its class.

#define FEEDBACK_PENDING 1u
#define FEEDBACK_KIND_SHIFT 1
#define FEEDBACK_AGE_SHIFT 2
#define FEEDBACK_COUNT_SHIFT 4
#define FEEDBACK_OPEN 64u
#define FEEDBACK_DEFERRED 128u
#define FEEDBACK_DEFERRED_IMP 256u

typedef struct feedback_sums feedback_sums;
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

struct feedback {
  bool started;      // the arrays exist (from the start of the search)
  bool chb;          // CHB line, VSIDS line otherwise
  bool analyzing;    // VSIDS: inside a step of conflict analysis
  bool deferring;    // VSIDS: a backtrack of the step deferred closes
  unsigned size;     // variables the arrays have room for
  unsigned counted;  // VSIDS: trail recorded up to here (see 'keys.h')
  double growth;     // 1/d, d the score decay
  double increment;  // CHB: the counts' own increment, as UCB's
  unsigneds deferred; // VSIDS: variables whose closes are deferred
  uint16_t *state;   // pending pick, open and deferred interval
  double *n[2];      // VSIDS: rounds by class (inflated)
  double *r[2];      // VSIDS: bumps by class (inflated)
  double *opened;    // VSIDS: increment at assignment
  double *frozen;    // VSIDS: the four predictors of a pending pick
  uint64_t *start;   // VSIDS: round counter at the interval's start
  uint64_t *bumps;   // VSIDS: bumped rounds of the open interval
  uint64_t *last;    // VSIDS: round counter at the close of the last
                     // interval with a round (zero: never observed)
  double *q[2];      // CHB: ERWAs by class
  uint64_t *paid[2]; // CHB: payments by class
  double *count;     // CHB: UCB's count (inflated)
  uint64_t *latest;  // CHB: stable-mode conflicts at the last payment
#ifdef SHADOW
  uint64_t *repaid; // CHB: payments counted by shadow mode
#endif
  struct {
    uint64_t intervals[2]; // VSIDS: closed intervals by class
    uint64_t bumps[2][2];  // VSIDS: bumps [in an ended interval][class]
    uint64_t unobserved;   // VSIDS: bumps in no interval (unit tests)
    uint64_t sum_k;        // VSIDS: k and b summed over the closed
    uint64_t sum_b;        // decided intervals (p_const)
    uint64_t sum_n;        // CHB: decided payments and their rewards
    double sum_r;          // (Q_const)
    uint64_t events;       // events (VSIDS: closed)
    uint64_t zero;         // VSIDS: events with k = 0
    feedback_sums group[FEEDBACK_GROUPS];
    feedback_sums calibration[2][FEEDBACK_BINS]; // by p_dec, by p_imp
  } m1;
  struct {
    uint64_t picks[FEEDBACK_KINDS];
    feedback_sums age[FEEDBACK_KINDS][FEEDBACK_AGES];
    feedback_sums count[FEEDBACK_KINDS][FEEDBACK_COUNTS];
  } m2;
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

// VSIDS line: the literals assigned since the last record get the current
// increment and round counter (see 'keys.h').  Called at the start of
// every bump round, before every stable-mode backtrack, when stable mode
// is left and before rescales.

void kissat_record_feedback (struct kissat *);

// VSIDS line: a bump round starts (before the round counter is advanced),
// 'idx' is bumped in it (before its score), and the round ends (after the
// increment has grown).

void kissat_feedback_round (struct kissat *);
void kissat_feedback_bump (struct kissat *, unsigned idx);
void kissat_feedback_round_end (struct kissat *);

// VSIDS line: a step of conflict analysis starts, before its backtracks,
// and ends, after its bump round if it has one.

void kissat_feedback_begin_analysis (struct kissat *);
void kissat_feedback_end_analysis (struct kissat *);

// Stable-mode backtracking unassigned 'idx'; stable mode is left; stable
// mode is entered; the scores are rescaled by 'factor'.

void kissat_feedback_unassign (struct kissat *, unsigned idx);
void kissat_leave_stable_feedback (struct kissat *);
void kissat_enter_stable_feedback (struct kissat *);
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

void kissat_print_feedback_statistics (struct kissat *);

#endif

#endif
