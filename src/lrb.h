#ifndef _lrb_h_INCLUDED
#define _lrb_h_INCLUDED

// LRB's reward on CHB's ERWA (tree builds, option 'lrb' with 'chb=1'),
// after Liang, Ganesh, Poupart and Czarnecki, 'Learning Rate Based
// Branching Heuristic for SAT Solvers', SAT 2016, Algorithm 1 with its
// reason-side rate, mapped onto Kissat as CHB is (see 'chb.h'; research
// plan, Phase 4, Specification, part 3).  The estimator stays CHB's: one
// value Q per variable in the score storage, zero at activation, no
// pseudo-activity, the step size alpha of 'kissat_chb_alpha' on CHB's
// count of stable-mode search conflicts, and Argmax over Q.  What changes
// is the reward and when it is paid.
//
// An interval of a variable starts at an assignment that CHB's payment
// walk sees ('kissat_chb_assign': the decision, what its propagation
// assigned, the asserted literal), which records CHB's conflict count, the
// one before the walk's own increment when the propagation ended in a
// conflict, so that those literals' intervals count that conflict, and
// resets the variable's two counters.  Warm-up, probing and the other
// inprocessing propagate by routines of their own, and focused mode does
// not walk, so their assignments open no interval and earn nothing.
// Chronological backtracking keeps a literal's interval, as it keeps its
// reason: the walk does not see a kept literal again.
//
// At every step of conflict analysis in stable mode, every active variable
// of the analyzed set, CHB's participants (see 'chb.h'), gets
// 'participated' += 1, and every reason-side literal that Kissat would bump
// on the VSIDS line ('analyze_reason_side_literals', under its gates
// 'bumpreasons', 'bumpreasonsrate' and 'bumpreasonslimit'), which under
// 'lrb' joins the analyzed set as it does there, gets 'reasoned' += 1.  The
// two are told apart at the pass's boundary ('boundary', the size of the
// analyzed set before the reason-side literals); the reward needs only
// their sum.  Each round of on-the-fly strengthening is a step and counts.
//
// The interval closes where the assignment intervals of 'intervals.h'
// close, which this option starts on the CHB line with LRB's interval.
// Kissat backjumps before it records a step's participants, so a variable
// that the step's backtrack unassigns closes at the step's end, after the
// record, with the ending conflict's participation counted; a variable
// unassigned outside a step (a restart, a reduction, rephasing) closes at
// its unassignment, and every assigned one when stable mode is left.  At
// the close, with 'interval' CHB's conflict count now less its count at
// the start (the counter already counts the ending conflict):
//
//   interval >= 1:  r = (participated + reasoned) / interval and
//                   Q = (1 - alpha) Q + alpha r, alpha at the close,
//   interval = 0:   no update.
//
// The reward r exceeds one when reason-side participations outnumber the
// interval's conflicts; nothing clamps it, as nothing does in the paper.
// A close of an interval that the walk never opened (warm-up's, probing's,
// focused mode's) pays nothing.  CHB's 'last_conflict' is not kept.  The
// new Q of an unassigned variable reaches its leaf at once; that of a
// variable assigned again by then (the asserted literal, which closes its
// old interval at the step's end) reaches the estimator only, and its
// leaf lags until backtracking unassigns it, as after CHB's payments (see
// 'inlinepolicy.h').
//
// Excluded, fatal at the start of the search: 'lrb' without 'chb=1', and
// with 'softmax', 'perturbed', 'thompson', 'ucb' or 'gammappm', so that
// the policy is Argmax; and in feedback builds, until they measure LRB's
// reward (research plan, Phase 4, Engineering, the feedback build's
// additions).
//
// Assertion builds check every close against a shadow log of their own:
// per variable the participations and reason-side participations ever
// counted, by a pass of their own over each step's analyzed set, split at
// a boundary taken before the reason-side pass is called, and the conflict
// count and the log's counts at the interval's start, recorded at the
// walk.  At the close the interval, both counts and the reward recomputed
// from the log must equal those paid, the reward bitwise, and a close
// inside an analysis step must be a deferred one, at the step's end.

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#define LRB_CLOSED UINT64_MAX    // 'start' of a variable without interval
#define LRB_NO_BOUNDARY SIZE_MAX // no reason-side literals in the step

typedef struct lrb lrb;

struct lrb {
  bool started;           // the arrays exist
  unsigned size;          // variables the arrays have room for
  size_t boundary;        // size of the analyzed set before the step's
                          // reason-side literals
  uint64_t *start;        // CHB's conflict count at the interval's start
  unsigned *participated; // participations since
  unsigned *reasoned;     // reason-side participations since
  struct {
    uint64_t opened;         // intervals opened by the walk
    uint64_t participations; // participations counted
    uint64_t reasons;        // reason-side participations counted
    uint64_t closed[3];      // closes, by 'INTERVALS_CLOSE_...'
    uint64_t updates;        // closes with interval >= 1: updates of Q
    uint64_t above;          // of which with a reward above one
    uint64_t skipped;        // closes with interval zero
    uint64_t ignored;        // closes of intervals the walk did not open
  } count;
#ifndef NDEBUG
  struct {
    size_t boundary;             // analyzed set before the reason side
    uint64_t *start;             // the walk's conflict count, or closed
    uint64_t *participations;    // the log: participations ever
    uint64_t *reasons;           // and reason-side participations ever
    uint64_t *participations_at; // the log at the interval's start
    uint64_t *reasons_at;
    uint64_t logged[2]; // participations and reason-side ones logged
    uint64_t closes;    // closes checked
  } check;
#endif
};

struct kissat;

// At the start of the search, before the assignment intervals, which it
// starts: checks the options, and allocates the arrays.  A later search
// keeps Q and the counts but closes every interval, since none spans two
// searches.

void kissat_start_lrb (struct kissat *);
void kissat_resize_lrb (struct kissat *, unsigned size);
void kissat_release_lrb (struct kissat *);

// CHB's payment walk in stable mode: the active literals on the trail from
// position 'played' to 'size' open their intervals at conflict count
// 'conflicts'.

void kissat_lrb_assign (struct kissat *, unsigned played, unsigned size,
                        uint64_t conflicts);

// Called by 'kissat_chb_analyzed' (stable mode): the analyzed variables
// took part in the current step, the reason-side ones from 'boundary' on.

void kissat_lrb_analyzed (struct kissat *);

// The assignment interval of 'idx' closes, as 'how' says (see
// 'intervals.h'): LRB's reward, if the walk opened it.

void kissat_close_lrb_interval (struct kissat *, unsigned idx,
                                unsigned how);

void kissat_print_lrb_statistics (struct kissat *);

#ifndef NDEBUG

// The check's boundary, before the reason-side pass of a step is called.

void kissat_check_lrb_boundary (struct kissat *);

#endif

// Compaction: moves the entries of 'from' to 'to', and clears 'idx'.

static inline void kissat_move_lrb (lrb *lrb, unsigned from, unsigned to) {
  if (!lrb->started)
    return;
  lrb->start[to] = lrb->start[from];
  lrb->participated[to] = lrb->participated[from];
  lrb->reasoned[to] = lrb->reasoned[from];
#ifndef NDEBUG
  lrb->check.start[to] = lrb->check.start[from];
  lrb->check.participations[to] = lrb->check.participations[from];
  lrb->check.reasons[to] = lrb->check.reasons[from];
  lrb->check.participations_at[to] = lrb->check.participations_at[from];
  lrb->check.reasons_at[to] = lrb->check.reasons_at[from];
#endif
}

static inline void kissat_clear_lrb (lrb *lrb, unsigned idx) {
  if (!lrb->started)
    return;
  lrb->start[idx] = LRB_CLOSED;
  lrb->participated[idx] = lrb->reasoned[idx] = 0;
#ifndef NDEBUG
  lrb->check.start[idx] = LRB_CLOSED;
  lrb->check.participations[idx] = lrb->check.reasons[idx] = 0;
  lrb->check.participations_at[idx] = lrb->check.reasons_at[idx] = 0;
#endif
}

#endif
