#include "allocate.h"
#include "inlineheap.h"
#include "internal.h"
#include "logging.h"

#include <string.h>

void lsids_release_heap (kissat *solver, lsidsheap *heap) {
  RELEASE_STACK (heap->stack);
  DEALLOC (heap->pos, heap->size);
  DEALLOC (heap->score, heap->size * 2);
  DEALLOC (heap->pol, heap->size);
  memset (heap, 0, sizeof *heap);
}

#ifndef NDEBUG

void lsids_check_heap (lsidsheap *heap) {
  const unsigned *const stack = BEGIN_STACK (heap->stack);
  const unsigned end = SIZE_STACK (heap->stack);
  const unsigned *const pos = heap->pos;
  const double *const score = heap->score;
  for (unsigned i = 0; i < end; i++) {
    const unsigned idx = stack[i];
    const unsigned idx_pos = pos[idx];
    assert (idx_pos == i);
    unsigned child_pos = HEAP_CHILD (idx_pos);
    unsigned parent_pos = HEAP_PARENT (child_pos);
    assert (parent_pos == idx_pos);
    if (child_pos < end) {
      unsigned child = stack[child_pos];
      assert (score[PREF_SCORE_IDX (idx)] >= score[PREF_SCORE_IDX (child)]);
      if (++child_pos < end) {
        parent_pos = HEAP_PARENT (child_pos);
        assert (parent_pos == idx_pos);
        child = stack[child_pos];
        assert (score[PREF_SCORE_IDX (idx)] >= score[PREF_SCORE_IDX (child)]);
      }
    }
  }
}

#endif

void lsids_resize_heap (kissat *solver, lsidsheap *heap, unsigned new_size) {
  const unsigned old_size = heap->size;
  if (old_size >= new_size)
    return;
  LOG ("resizing %s heap from %u to %u",
       (heap->tainted ? "tainted" : "untainted"), old_size, new_size);

  heap->pos = kissat_nrealloc (solver, heap->pos, old_size, new_size,
                               sizeof (unsigned));
  heap->pol = kissat_nrealloc (solver, heap->pol, old_size, new_size,
                               sizeof (unsigned));
  if (heap->tainted) {
    heap->score = kissat_nrealloc (solver, heap->score, old_size * 2,
                                   new_size * 2, sizeof (double));
  } else {
    if (old_size)
      DEALLOC (heap->score, old_size * 2);
    heap->score = kissat_calloc (solver, new_size * 2, sizeof (double));
  }
  heap->size = new_size;
}

void lsids_rescale_heap (kissat *solver, lsidsheap *heap, double factor) {
  LOG ("rescaling scores on heap with factor %g", factor);
  double *score = heap->score;
  for (unsigned i = 0; i < heap->vars * 2; i++)
    score[i] *= factor;
#ifndef NDEBUG
  lsids_check_heap (heap);
#endif
#ifndef LOGGING
  (void) solver;
#endif
}

void lsids_enlarge_heap (kissat *solver, lsidsheap *heap, unsigned new_vars) {
  const unsigned old_vars = heap->vars;
  assert (old_vars < new_vars);
  assert (new_vars <= heap->size);
  const size_t delta = new_vars - heap->vars;
  memset (heap->pos + old_vars, 0xff, delta * sizeof (unsigned));
  memset (heap->pol + old_vars, 0, delta * sizeof (unsigned));
  heap->vars = new_vars;
  if (heap->tainted)
    memset (heap->score + old_vars * 2, 0, delta * sizeof (double) * 2);
  LOG ("enlarged heap from %u to %u", old_vars, new_vars);
#ifndef LOGGING
  (void) solver;
#endif
}
