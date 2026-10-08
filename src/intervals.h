#ifndef _intervals_h_INCLUDED
#define _intervals_h_INCLUDED

// The assignment intervals of the variables in stable mode (tree builds):
// one bookkeeping shared by UCB's observation counts on VSIDS scores (see
// 'keys.h'), the feedback build's measurements (see 'feedback.h') and LRB's
// reward on CHB scores (see 'lrb.h'), and later by Phase 4's reward on
// VSIDS scores (research plan, Phase 4, Specification, part 2, The
// bookkeeping).  It is started at the start of the search under UCB on
// VSIDS scores, in feedback builds and under LRB.  Otherwise it is not
// started and every hook below returns at once, so that Argmax, Sample,
// mixing, P1, TS and UCB on CHB scores run the code paths they ran without
// it.
//
// An interval of a variable runs from its assignment to its unassignment
// in stable mode.  Assignment needs no hook: at the start of every bump
// round, before every stable-mode backtrack, before a rescale of the scores
// and when stable mode is left, the active literals assigned since the last
// record ('counted', a trail position) open their intervals, with the
// current score increment ('opened') and bump round ('start') on the VSIDS
// line, which do not change between records.  Shrinking the trail moves
// 'counted' down with it; compaction, which renames the trail's literals in
// place and moves the variables' entries with them, leaves it.  Entering
// stable mode sets it to zero, so that the next record opens an interval
// for every variable assigned then.
//
// Classes.  An interval is 'decided' if the variable's reason is
// 'DECISION_REASON', 'asserted' if conflict analysis assigned it at the end
// of a step, after its backjump, with the learned clause as its reason
// ('learn.c'), or with the conflict clause that Kissat reuses as the driving
// clause without analysis ('analyze.c'), and 'propagated' otherwise.  The
// reason alone cannot tell an asserted literal from a propagated one, so
// those sites mark the literal ('kissat_policy_asserted'), in stable mode
// only, and the record takes the class from the reason and the mark.  A
// learned unit is fixed at level zero and has no interval.  Focused mode
// marks nothing, since none of its unassignments would clear a mark, and
// the marks are cleared when stable mode is left, so an interval opened
// when stable mode is entered takes its class from the reason alone, and
// an asserted literal assigned across a switch counts as propagated.  The
// class is fixed over an interval, chronological backtracking included.
//
// Closes.  An interval closes when stable-mode backtracking unassigns its
// variable, and when stable mode is left.  Kissat learns before it bumps: a
// step of conflict analysis (one round of 'kissat_analyze', between
// 'kissat_policy_begin_analysis' and 'kissat_policy_end_analysis')
// backjumps, which unassigns the variables above the jump level, asserts
// the learned clause's literal, and only then bumps the analyzed variables.
// So with LRB's interval ('interval', Liang et al. 2016), counted by every
// user but UCB with stage 2's count ('ucbinterval=0'), an interval that a
// backtrack inside a step ends stays open ('deferred'), with its class kept
// apart from that of a new assignment of its variable, until the step's
// bump round has grown the increment, so that it counts the round, or
// until the step's end if the step has none (on the CHB line always).  The
// literals assigned since the backtrack (the asserted literal) are recorded
// only after that round, so that their intervals start after it.  Without
// LRB's interval a backtrack closes at once and no record is held back:
// stage 2's count, which only UCB without the feedback build counts.  At a
// close UCB adds the increments of the interval's bump rounds to its count
// ('kissat_close_keys_interval'), the feedback build adds the interval to
// its measurements ('kissat_close_feedback_interval'), and LRB pays its
// reward for the interval of its own that its walk opened, if it opened
// one ('kissat_close_lrb_interval').
//
// Bumps (feedback builds).  A bump of a variable falls in the interval a
// backtrack of the current step ended, if there is one, else in the open
// interval of the assigned variable ('kissat_interval_bumped').  The
// interval counts its rounds with a bump ('bumps', b), and its rounds k are
// the bump round counter at the close minus 'start'.  Every bump in a run
// falls in an interval; only the unit tests bump outside analysis steps.

#include "stack.h"

#include <stdbool.h>
#include <stdint.h>

// The classes of an interval.

#define INTERVALS_DECIDED 0u
#define INTERVALS_ASSERTED 1u
#define INTERVALS_PROPAGATED 2u

// A variable's state, one byte: the class of its open interval (two bits)
// and whether it is open; whether its current assignment was asserted
// (the mark); and whether a backtrack of the current step ended an
// interval of it, with that interval's class (two bits).

#define INTERVALS_CLASS 3u
#define INTERVALS_OPEN 4u
#define INTERVALS_MARKED 8u
#define INTERVALS_DEFERRED 16u
#define INTERVALS_DEFERRED_SHIFT 5
#define INTERVALS_DEFERRED_CLASS (INTERVALS_CLASS << INTERVALS_DEFERRED_SHIFT)

// The interval a bump falls in ('kissat_interval_bumped'): its class, with
// 'INTERVALS_ENDED' if a backtrack of the step ended it, or none.

#define INTERVALS_ENDED 4u
#define INTERVALS_NONE 8u

// How an interval closes: at the unassignment of its variable, after the
// bump round or at the end of the step whose backtrack ended it, or when
// stable mode is left.

#define INTERVALS_CLOSE_UNASSIGNED 0u
#define INTERVALS_CLOSE_DEFERRED 1u
#define INTERVALS_CLOSE_LEFT 2u

typedef struct intervals intervals;

struct intervals {
  bool started;       // the arrays exist
  bool vsids;         // VSIDS line: increments and rounds at assignment
  bool ucb;           // UCB on VSIDS scores counts the intervals
  bool lrb;           // LRB's reward on CHB scores pays at the closes
  bool rounds;        // feedback builds, VSIDS line: k and b
  bool interval;      // LRB's interval: a step's backtracks defer closes
  bool analyzing;     // ... inside a step of conflict analysis
  bool deferring;     // ... a backtrack of the step deferred closes
  unsigned size;      // variables the arrays have room for
  unsigned counted;   // trail recorded up to here
  unsigneds deferred; // variables whose closes are deferred
  uint8_t *state;     // per variable, see above
  double *opened;     // VSIDS line: score increment at the interval's start
  uint64_t *start;    // 'rounds': bump round at the interval's start
  uint64_t *bumps;    // 'rounds': its bump rounds with a bump of the variable
};

struct kissat;

// At the start of the search, after LRB, the policy's keys and the
// feedback build's measurements: whether the bookkeeping runs, and its
// arrays.  In feedback builds UCB on VSIDS scores with stage 2's count is a
// fatal error, since one record cannot give an asserted literal both
// counts' increments at assignment.

void kissat_start_intervals (struct kissat *);
void kissat_resize_intervals (struct kissat *, unsigned size);
void kissat_release_intervals (struct kissat *);

// The interval of 'idx', of class 'c', closes, as 'how' says.

void kissat_close_interval (struct kissat *, unsigned idx, unsigned c,
                            unsigned how);

// The closes a backtrack of the current step deferred happen now.

void kissat_finish_deferred_intervals (struct kissat *);

// Stable mode is left: every open interval closes.

void kissat_leave_stable_intervals (struct kissat *);

// The scores are rescaled by 'factor' (VSIDS line): the literals assigned
// since the last record are recorded first, at the old increment, then the
// increments at assignment, UCB's counts and the feedback's sums follow.

void kissat_rescale_intervals (struct kissat *, double factor);

// Compaction: moves the entries of 'from' to 'to', and clears 'idx'.

static inline void kissat_move_intervals (intervals *intervals,
                                          unsigned from, unsigned to) {
  if (!intervals->started)
    return;
  intervals->state[to] = intervals->state[from];
  if (intervals->vsids)
    intervals->opened[to] = intervals->opened[from];
  if (intervals->rounds) {
    intervals->start[to] = intervals->start[from];
    intervals->bumps[to] = intervals->bumps[from];
  }
}

static inline void kissat_clear_intervals (intervals *intervals,
                                           unsigned idx) {
  if (!intervals->started)
    return;
  intervals->state[idx] = 0;
  if (intervals->vsids)
    intervals->opened[idx] = 0;
  if (intervals->rounds)
    intervals->start[idx] = intervals->bumps[idx] = 0;
}

#endif
