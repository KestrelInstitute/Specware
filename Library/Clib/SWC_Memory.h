#ifndef _SWC_Memory_H_
#define _SWC_Memory_H_

#ifdef SWGC
#include <gc.h>
#endif

// allocates heap-space
void *swc_malloc(int bytes);

#include "SWC_Memory.c"

#endif
