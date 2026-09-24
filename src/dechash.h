#ifndef _dechash_h_INCLUDED
#define _dechash_h_INCLUDED

// Decision-trail hash.  Every decision made by 'kissat_decide' (search and
// warm-up decisions, not assumptions made by 'kissat_internal_assume') is
// folded into a running 64-bit hash together with its decision level and
// whether it was a warm-up decision.  The hash after decision 2^k is kept
// as checkpoint 'k', so two runs can be compared on every checkpoint both
// reached, even if one of them was stopped early.  Only reads solver state.
//
// Compiled in only with './configure --dechash' ('-DDECHASH').  Otherwise
// 'UPDATE_DECHASH' is empty and the hash is neither kept nor printed.

#ifdef DECHASH

#include <stdbool.h>
#include <stdint.h>

#define MAX_DECHASH_CHECKPOINTS 64

typedef struct dechash dechash;

struct dechash {
  uint64_t hash;
  uint64_t decisions;
  unsigned checkpoints;
  uint64_t checkpoint[MAX_DECHASH_CHECKPOINTS];
};

static inline uint64_t kissat_mix_dechash (uint64_t z) {
  z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ull;
  z = (z ^ (z >> 27)) * 0x94d049bb133111ebull;
  return z ^ (z >> 31);
}

static inline void kissat_update_dechash (dechash *dechash, unsigned level,
                                          bool warming, unsigned lit) {
  const uint64_t decision = ((uint64_t) warming << 63) |
                            ((uint64_t) level << 32) | (uint64_t) lit;
  dechash->hash =
      kissat_mix_dechash (dechash->hash + 0x9e3779b97f4a7c15ull + decision);
  const uint64_t decisions = ++dechash->decisions;
  const unsigned checkpoints = dechash->checkpoints;
  if (checkpoints < MAX_DECHASH_CHECKPOINTS &&
      decisions == (uint64_t) 1 << checkpoints) {
    dechash->checkpoint[checkpoints] = dechash->hash;
    dechash->checkpoints = checkpoints + 1;
  }
}

struct kissat;

void kissat_print_dechash (struct kissat *);

#define UPDATE_DECHASH(LIT) \
  kissat_update_dechash (&solver->dechash, solver->level, solver->warming, \
                         (LIT))

#else

#define UPDATE_DECHASH(...) \
  do { \
  } while (0)

#endif

#endif
