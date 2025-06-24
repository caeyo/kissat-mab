#ifndef _inlinelsidsheap_h_INCLUDED
#define _inlinelsidsheap_h_INCLUDED

#include "allocate.h"
#include "internal.h"
#include "logging.h"

static inline void lsids_bubble_up (kissat *solver, lsidsheap *heap,
                                     unsigned idx) {
  unsigned *stack = BEGIN_STACK (heap->stack);
  unsigned *pos = heap->pos;
  unsigned idx_pos = pos[idx];
  const double *const score = heap->score;
  const double idx_score = score[PREF_SCORE_IDX (idx)];
  while (idx_pos) {
    const unsigned parent_pos = HEAP_PARENT (idx_pos);
    const unsigned parent = stack[parent_pos];
    if (score[PREF_SCORE_IDX (parent)] >= idx_score)
      break;
    LOG ("heap bubble up: %u@%u = %g swapped with %u@%u = %g", parent,
         parent_pos, score[PREF_SCORE_IDX (parent)], idx, idx_pos, idx_score);
    stack[idx_pos] = parent;
    pos[parent] = idx_pos;
    idx_pos = parent_pos;
  }
  stack[idx_pos] = idx;
  pos[idx] = idx_pos;
#ifndef LOGGING
  (void) solver;
#endif
}

static inline void lsids_bubble_down (kissat *solver, lsidsheap *heap,
                                       unsigned idx) {
  unsigned *stack = BEGIN_STACK (heap->stack);
  const unsigned end = SIZE_STACK (heap->stack);
  unsigned *pos = heap->pos;
  unsigned idx_pos = pos[idx];
  const double *const score = heap->score;
  const double idx_score = score[PREF_SCORE_IDX (idx)];
  for (;;) {
    unsigned child_pos = HEAP_CHILD (idx_pos);
    if (child_pos >= end)
      break;
    unsigned child = stack[child_pos];
    double child_score = score[PREF_SCORE_IDX (child)];
    const unsigned sibling_pos = child_pos + 1;
    if (sibling_pos < end) {
      const unsigned sibling = stack[sibling_pos];
      const double sibling_score = score[PREF_SCORE_IDX (sibling)];
      if (sibling_score > child_score) {
        child = sibling;
        child_pos = sibling_pos;
        child_score = sibling_score;
      }
    }
    if (child_score <= idx_score)
      break;
    LOG ("heap bubble down: %u@%u = %g swapped with %u@%u = %g", child,
         child_pos, score[PREF_SCORE_IDX (child)], idx, idx_pos, idx_score);
    stack[idx_pos] = child;
    pos[child] = idx_pos;
    idx_pos = child_pos;
  }
  stack[idx_pos] = idx;
  pos[idx] = idx_pos;
#ifndef LOGGING
  (void) solver;
#endif
}

#define LSIDS_HEAP_IMPORT(IDX) \
  do { \
    assert ((IDX) < UINT_MAX - 1); \
    if (heap->vars <= (IDX)) \
      lsids_enlarge_heap (solver, heap, (IDX) + 1); \
  } while (0)

static inline void lsids_push_heap (kissat *solver, lsidsheap *heap,
                                     unsigned idx) {
  LOG ("push heap %u", idx);
  assert (!lsids_heap_contains (heap, idx));
  LSIDS_HEAP_IMPORT (idx);
  heap->pos[idx] = SIZE_STACK (heap->stack);
  PUSH_STACK (heap->stack, idx);
  lsids_bubble_up (solver, heap, idx);
}

static inline void lsids_pop_heap (kissat *solver, lsidsheap *heap,
                                    unsigned idx) {
  LOG ("pop heap %u", idx);
  assert (lsids_heap_contains (heap, idx));
  const unsigned last = POP_STACK (heap->stack);
  heap->pos[last] = DISCONTAIN;
  if (last == idx)
    return;
  const unsigned idx_pos = heap->pos[idx];
  heap->pos[idx] = DISCONTAIN;
  POKE_STACK (heap->stack, idx_pos, last);
  heap->pos[last] = idx_pos;
  lsids_bubble_up (solver, heap, last);
  lsids_bubble_down (solver, heap, last);
}

static inline unsigned lsids_pop_max_heap (kissat *solver, lsidsheap *heap) {
  assert (!EMPTY_STACK (heap->stack));
  unsigneds *stack = &heap->stack;
  unsigned *const begin = BEGIN_STACK (*stack);
  const unsigned idx = *begin;
  assert (!heap->pos[idx]);
  LOG ("pop max heap %u", idx);
  const unsigned last = POP_STACK (*stack);
  unsigned *const pos = heap->pos;
  pos[last] = DISCONTAIN;
  if (last == idx)
    return idx;
  pos[idx] = DISCONTAIN;
  *begin = last;
  pos[last] = 0;
  lsids_bubble_down (solver, heap, last);
  return idx;
}

static inline void lsids_adjust_heap (kissat *solver, lsidsheap *heap,
                                       unsigned idx) {
  const unsigned new_vars = idx + 1;
  const unsigned old_vars = heap->vars;
  if (new_vars <= old_vars)
    return;
  const unsigned old_size = heap->size;
  if (idx >= old_size) {
    size_t new_size = old_size ? 2 * old_size : 1;
    while (idx >= new_size)
      new_size *= 2;
    assert (new_size < DISCONTAIN);
    lsids_resize_heap (solver, heap, new_size);
  }
  lsids_enlarge_heap (solver, heap, idx + 1);
}

static inline void lsids_update_heap (kissat *solver, lsidsheap *heap,
                                       unsigned idx, unsigned pol,
                                       double new_score) {
  const double old_score = lsids_get_heap_score (heap, idx, pol);
  if (old_score == new_score)
    return;
  LSIDS_HEAP_IMPORT (idx);
  LOG ("update heap %u score from %g to %g", idx, old_score, new_score);
  heap->score[SCORE_IDX (idx, pol)] = new_score;
  if (!heap->tainted) {
    heap->tainted = true;
    LOG ("tainted heap");
  }
  const unsigned opp_pol = pol ^ 1;
  const double opp_score = heap->score[SCORE_IDX (idx, opp_pol)];
  if (pol == heap->pol[idx]) {  // Preferred polarity
    if (new_score > old_score) {
      if (lsids_heap_contains(heap, idx))
        lsids_bubble_up(solver, heap, idx);
    } else {  // new_score < old_score
      if (new_score < opp_score)
        heap->pol[idx] = opp_pol;
      if (lsids_heap_contains(heap, idx))
        lsids_bubble_down(solver, heap, idx);
    }
  } else if (new_score > opp_score) {
    heap->pol[idx] = pol;
    if (lsids_heap_contains(heap, idx))
      lsids_bubble_up(solver, heap, idx);
  }
}

#endif
