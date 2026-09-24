#ifdef DECHASH

#include "dechash.h"
#include "internal.h"
#include "print.h"

#include <inttypes.h>

void kissat_print_dechash (kissat *solver) {
#ifndef QUIET
  const dechash *const dechash = &solver->dechash;
  for (unsigned k = 0; k < dechash->checkpoints; k++)
    kissat_message (solver, "dechash %" PRIu64 " %016" PRIx64,
                    (uint64_t) 1 << k, dechash->checkpoint[k]);
  kissat_message (solver, "dechash-final %" PRIu64 " %016" PRIx64,
                  dechash->decisions, dechash->hash);
#else
  (void) solver;
#endif
}

#else
int kissat_dechash_dummy_to_avoid_warning;
#endif
