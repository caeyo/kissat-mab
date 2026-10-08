#ifndef _reward_h_INCLUDED
#define _reward_h_INCLUDED

// Phase 4's reward (tree builds; research plan, Phase 4, Specification,
// parts 2 and 3): three components on VSIDS scores, each an option off by
// default, and two of them on LRB's estimator ('chb=1 lrb=1', see
// 'lrb.h').  Every component works on the assignment intervals of
// 'intervals.h', which a reward option off its identity starts, with LRB's
// interval: a backtrack inside an analysis step defers its closes to the
// step's bump round, or its end.
//
// The channel weighting ('wimp', w_imp = wimp / 1000).  On VSIDS scores a
// bump of a variable adds inc * w_c, with c the class of the interval the
// bump falls in ('kissat_interval_bumped'): w_c = 1 for a decided interval
// and w_imp for an asserted or a propagated one.  Reason-side bumps are
// weighted by their variable's class like any other.  On LRB's estimator
// the update at the close of an interval of class c takes the step alpha
// w_c / max (1, w_imp) instead of alpha.
//
// Locality ('locality', lambda = localitydecay / 1000; Liang et al. 2016).
// Defined eagerly: at the end of every stable-mode analysis step that
// bumps (VSIDS) or records participants (LRB), after its closes, every
// unassigned active variable's activity (VSIDS) or Q (LRB) is multiplied
// by lambda, and an assigned variable's is not.  Built lazily, with a
// multiplier g, one at the start, grown by 1 / lambda at each such step:
// an unassigned variable stores its value times g, which does not change
// while it stays unassigned; an assigned one stores its value times g_a,
// the g at its interval's start, which the record of 'intervals.h' keeps
// ('multiplier'), as it keeps the increment then.  A bump of a variable
// adds inc * w_c * g_a (g_a of the interval the bump falls in, open or
// deferred), and when its interval closes the stored value is multiplied
// by g / g_a, after the close's payment and before g grows, so that a
// variable that a step's backtrack unassigns is decayed at that step.  On
// LRB's estimator the update at the close uses the true Q, the stored
// value over g_a, and the new Q is stored times g.  A score written in
// true units while its variable is unassigned (activation's initial score,
// that of bounded variable addition, 'reorder's weight) is stored times g.
// So among the unassigned variables, the ones the policy picks from, the
// stored values are the eager values times one g, in the same order.  The
// leaf of a variable whose stored value changes at its unassignment is
// set then (on VSIDS scores every unassignment, an O(log n) path update).
//
// Rescales.  On VSIDS scores every rescale of the scores (an overflow's,
// a stored value or the increment above 'MAX_SCORE', or 'reorder's), and a
// growth of g above 'MAX_SCORE', first gives every open or deferred
// interval the current g (its stored value times g / g_a, and g_a = g),
// then divides the stored values by M, the largest stored value or the
// increment times g, the increment and every quantity in its units by M /
// g, and sets g and every g_a to one, which scales the eager activities
// and the increment by the same factor g / M.  On LRB's estimator a growth
// of g above 'MAX_SCORE' gives the open intervals the current g likewise,
// divides every stored value by g and sets g and every g_a to one, then
// the tree is rebuilt.  Giving the open intervals the current g first,
// rather than dividing their g_a by g, keeps g_a between one and g: a
// variable assigned across more than about 14,000 decays would otherwise
// have g_a, and its stored value with it, underflow, and its value would
// be lost at its unassignment.
//
// The interval reward ('intervalreward', VSIDS scores).  A bump adds
// nothing to the score: the interval counts its rounds k and its rounds
// with a bump b ('intervals.h'), and at its close the score receives inc
// (b / k) w_c g_a once, inc the increment at the close, before locality's
// g / g_a; with k = 0 or b = 0 it receives nothing.  A payment, like a
// bump, that takes a stored value above 'MAX_SCORE' rescales.
//
// Excluded, fatal at the start of the search: a reward option off its
// identity with 'softmax', 'perturbed', 'thompson', 'ucb' or 'gammappm'
// (the policy is Argmax); 'wimp' or 'locality' with 'chb=1' and 'lrb=0';
// 'intervalreward' with 'chb=1'; and any of them in feedback builds, which
// measure the published rewards.  'localitydecay' without 'locality' is
// ignored.  At default options nothing is started, and Argmax, Argmax-CHB,
// Argmax-LRB and every other policy run the code paths they ran before.
//
// Assertion builds check the reward.  Locality: an eager form beside the
// lazy one, one value per variable in true units, decayed at every step;
// at every pick the variable of largest eager value among the unassigned
// ones, the smallest index among ties, must be the pick, or within
// 'REWARD_TOLERANCE' of it (a tie, rounded apart, counted and the first
// ones logged).  The eager pick is the first unassigned one of the
// 'REWARD_CANDIDATES' largest eager values, selected by the pass that
// decays them or, after any other change, by a pass of its own, and again
// when every candidate is assigned.  Every 1000 picks every active
// variable's stored value over g_a (its interval open or deferred) or g
// must equal its eager value to 'REWARD_TOLERANCE' of its size plus
// 'DBL_MIN', so that values decayed below the normal range, which keep few
// significant bits, compare absolutely.  On VSIDS scores: when a step of
// conflict analysis starts the active variables on the trail are listed
// with whether their reason is a decision, and every bump's weight must be
// the one that gives (w = 1 for a decision, w_imp otherwise); the interval
// reward's k and b are counted by brute force from the listed variables
// and the analyzed ones at the end of every bump round, and at every close
// they must equal the interval's, and the score's change the payment they
// give, bitwise.  On LRB's estimator LRB's check (see 'lrb.h') holds every
// close's class to the reason at the walk and its step to the weighting.
// On both: the literal an analysis step asserts must be the last
// assignment, with a clause as its reason, and is noted there; and at
// every record of an interval its class must be decided for a decision,
// asserted for a noted literal and propagated otherwise.  A failed check
// is a fatal error.

#include "stack.h"

#include <stdbool.h>
#include <stdint.h>

#define REWARD_NONE 3 // a bump in no interval, beside the three classes

#define REWARD_TOLERANCE 1e-9 // eager against lazy (assertion builds)
#define REWARD_LOGGED 100     // ties logged per run (assertion builds)
#define REWARD_CANDIDATES 16  // eager picks selected (assertion builds)

typedef struct reward reward;

struct reward {
  bool started;  // a reward option is off its identity
  bool lrb;      // on LRB's estimator, else on VSIDS scores
  bool weighted; // the channel weighting: 'wimp' is not 1000
  bool locality; // locality
  bool interval; // the interval reward (VSIDS scores)
  bool decay;    // locality: the current analysis step decays
  double wimp;   // w_imp
  double lambda; // locality: lambda
  double growth; // locality: 1 / lambda
  double g;      // locality: the multiplier
  struct {
    uint64_t bumps[4];   // VSIDS: bumps by class, and in no interval
    uint64_t closed[3];  // VSIDS: closes by 'INTERVALS_CLOSE_...'
    uint64_t paid;       // interval reward: closes with k >= 1
    uint64_t unbumped;   // of which with b = 0
    uint64_t empty;      // interval reward: closes with k = 0
    uint64_t updates[3]; // LRB: updates of Q by class
    uint64_t steps;      // locality: decays, growths of g
    uint64_t rescales;   // locality: rescales for g above 'MAX_SCORE'
  } count;
#ifndef NDEBUG
  struct {
    unsigned size;        // variables the arrays have room for
    double *eager;        // locality: the eager values
    bool dirty;           // ... changed since the candidates' selection
    unsigned candidates;  // ... the largest of the unassigned variables
    unsigned candidate[REWARD_CANDIDATES]; // in order, largest first
    uint64_t picks;       // picks compared with the eager pick
    uint64_t ties;        // of which the eager pick was another, at a tie
    uint64_t eager_ties;  // ... the eager values equal, the stored apart
    uint64_t lazy_ties;   // ... the stored values equal, the eager apart
    uint64_t complete;    // complete checks
    uint64_t values;      // values compared at those
    double error;         // largest relative difference of those
    uint64_t step;        // VSIDS: steps of conflict analysis
    unsigneds listed;     // active variables on the trail at its start
    uint64_t *listed_at;  // the step a variable was last listed in
    bool *decided;        // whether its reason was a decision then
    uint64_t *marked;     // the bump round of its last bump
    uint64_t *rounds;     // brute force: rounds of its interval
    uint64_t *bumped;     // brute force: of which with a bump
    unsigned *asserted;   // trail position + 1 of an asserted literal
    uint64_t bumps;       // bumps whose weight was checked
    uint64_t classes;     // records whose class was checked
    uint64_t updates;     // LRB: updates whose class and step were checked
    uint64_t assertions;  // asserted literals checked where asserted
    uint64_t intervals;   // closes whose k and b were checked
    uint64_t payments;    // payments checked
  } check;
#endif
};

struct kissat;

// At the start of the search, after LRB, the policy's keys and the
// feedback build's measurements and before the assignment intervals,
// which it starts: checks the options, and fixes the components.  A later
// search keeps the reward.

void kissat_start_reward (struct kissat *);
void kissat_resize_reward (struct kissat *, unsigned size);
void kissat_release_reward (struct kissat *);

// VSIDS scores: the bumps of a bump round, the analyzed variables.

void kissat_reward_bumps (struct kissat *);

// VSIDS scores: the interval of 'idx', of class 'c', closes, as 'how' says
// (see 'intervals.h').

void kissat_close_reward_interval (struct kissat *, unsigned idx,
                                   unsigned c, unsigned how);

// Locality: the current analysis step ends, after its closes; it decays.

void kissat_decay_locality (struct kissat *);

// Locality on VSIDS scores, a rescale of the scores: every open or
// deferred interval takes the current g first, which is returned (one
// without locality); then, after the scores were scaled by M and the
// quantities in the increment's units by 'unit', g and every g_a are set
// to one.

double kissat_begin_locality_rescale (struct kissat *);
void kissat_end_locality_rescale (struct kissat *, double unit);

void kissat_print_reward_statistics (struct kissat *);

#ifndef NDEBUG

// The checks of assertion builds (see above).

void kissat_check_reward_pick (struct kissat *, unsigned idx);
void kissat_check_reward_step (struct kissat *);
void kissat_check_reward_round (struct kissat *);
void kissat_check_reward_record (struct kissat *, unsigned idx,
                                 unsigned c);
void kissat_check_reward_asserted (struct kissat *, unsigned idx);
void kissat_check_reward_true_score (struct kissat *, unsigned idx,
                                     double score, bool added);
void kissat_check_reward_lrb (struct kissat *, unsigned idx, double alpha,
                              double r);

#endif

// Compaction: moves the entries of 'from' to 'to', and clears 'idx'.

static inline void kissat_move_reward (reward *reward, unsigned from,
                                       unsigned to) {
#ifndef NDEBUG
  if (!reward->started)
    return;
  reward->check.eager[to] = reward->check.eager[from];
  reward->check.listed_at[to] = reward->check.listed_at[from];
  reward->check.decided[to] = reward->check.decided[from];
  reward->check.marked[to] = reward->check.marked[from];
  reward->check.rounds[to] = reward->check.rounds[from];
  reward->check.bumped[to] = reward->check.bumped[from];
  reward->check.asserted[to] = reward->check.asserted[from];
  reward->check.dirty = true;
#else
  (void) reward, (void) from, (void) to;
#endif
}

static inline void kissat_clear_reward (reward *reward, unsigned idx) {
#ifndef NDEBUG
  if (!reward->started)
    return;
  reward->check.eager[idx] = 0;
  reward->check.listed_at[idx] = 0;
  reward->check.decided[idx] = false;
  reward->check.marked[idx] = 0;
  reward->check.rounds[idx] = reward->check.bumped[idx] = 0;
  reward->check.asserted[idx] = 0;
  reward->check.dirty = true;
#else
  (void) reward, (void) idx;
#endif
}

#endif
