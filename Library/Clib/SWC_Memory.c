/**
 * Memory management functions for generated C code from Meta Slang
 */

/**
 * allocates the given amount of bytes on the heap
 */

void *swc_malloc(int bytes) {
  return (void*)
#ifdef SWGC
    GC_malloc(bytes);
#else
    malloc(bytes);
#endif
}
