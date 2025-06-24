#ifndef _lsidsheap_h_INCLUDED
#define _lsidsheap_h_INCLUDED

#include "stack.h"
#include "utilities.h"

#include <assert.h>
#include <limits.h>
#include <stdbool.h>

#define PREF_SCORE_IDX(IDX) ((IDX << 1) | heap->pol[IDX])
#define SCORE_IDX(IDX, POL) ((IDX << 1) | POL)

typedef struct lsidsheap lsidsheap;

struct lsidsheap {
  bool tainted;
  unsigned vars;
  unsigned size;
  unsigneds stack;
  double *score;
  unsigned *pos;
  unsigned *pol;
};

struct kissat;

void lsids_resize_heap (struct kissat *, lsidsheap *, unsigned size);
void lsids_release_heap (struct kissat *, lsidsheap *);

static inline bool lsids_heap_contains (lsidsheap *heap, unsigned idx) {
  return idx < heap->vars && !DISCONTAINED (heap->pos[idx]);
}

static inline double lsids_get_heap_score (const lsidsheap *heap,
                                            unsigned idx, unsigned pol) {
  return idx < heap->vars ? heap->score[SCORE_IDX (idx, pol)] : 0.0;
}

static inline bool lsids_empty_heap (lsidsheap *heap) {
  return EMPTY_STACK (heap->stack);
}

static inline size_t lsids_size_heap (lsidsheap *heap) {
  return SIZE_STACK (heap->stack);
}

static inline unsigned lsids_max_heap (lsidsheap *heap) {
  assert (!lsids_empty_heap (heap));
  return PEEK_STACK (heap->stack, 0);
}

void lsids_rescale_heap (struct kissat *, lsidsheap *heap, double factor);

void lsids_enlarge_heap (struct kissat *, lsidsheap *, unsigned new_vars);

static inline double lsids_max_score_on_heap (lsidsheap *heap) {
  if (!heap->tainted)
    return 0;
  assert (heap->vars);
  const double *const score = heap->score;
  const double *const end = score + heap->vars * 2;
  double res = score[0];
  for (const double *p = score + 1; p != end; p++)
    res = MAX (res, *p);
  return res;
}


#endif
