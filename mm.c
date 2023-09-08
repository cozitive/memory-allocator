/*
 * mm.c - dynamic memory allocation
 * tracking free blocks: explicit free list
 * placement policy: first fit
 * ordering policy: LIFO
 */

#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*
 * constants & macros
 */

// word size: 4 bytes
// alignment requirement: 2 words (8 bytes)
// minimum block size: 4 words (16 bytes)
// minimum heap extend size: 4 KB
#define WSIZE 4
#define DWSIZE 8
#define MINSIZE 16
#define CHUNKSIZE (1 << 12)

// allocated/free status
#define ALLOCATED 1
#define FREE 0

// round up to muptiple of DWSIZE
#define ALIGN(size) (((size) + (DWSIZE - 1)) & ~0x7)

// read/write a word at ptr
#define GET(ptr) (*(unsigned int *)(ptr))
#define SET(ptr, value) (*(unsigned int *)(ptr) = (value))

// pack/seperate header/footer
#define PACK(size, alloc) ((size) | (alloc))
#define SIZE(hdr) (GET((hdr)) & ~0x7)
#define ALLOC(hdr) (GET((hdr)) & 0x1)

// get header/footer of block at ptr
#define HDR(ptr) ((char *)(ptr) - WSIZE)
#define FTR(ptr) ((char *)(ptr) + SIZE(HDR(ptr)) - DWSIZE)

// prev/next block (both allocated/free)
#define NEXT(ptr) ((char *)(ptr) + SIZE((char *)(ptr) - WSIZE))
#define PREV(ptr) ((char *)(ptr) - SIZE((char *)(ptr) - DWSIZE))

// pred/succ block in free list (only free)
#define PRED(fbp) ((char *)(fbp))
#define SUCC(fbp) ((char *)(fbp) + WSIZE)

// head of free list (= prologue block)
static char *head;

/*
 * definition of helper functions
 */
static void *coalesce(void *ptr);

/*
 * main functions (mm_init, mm_malloc, mm_free, mm_realloc)
 */

/*
 * mm_init - initialize heap
 * return 0 on success, -1 on fail
 */
int mm_init() {
    char *heap_btm, *oldbrk;

    // create prologue & epilogue block
    if ((heap_btm = mem_sbrk(6 * WSIZE)) < 0) {
        return -1;
    }
    SET(heap_btm, 0);
    SET(heap_btm + (1 * WSIZE), PACK(4 * WSIZE, ALLOCATED));
    SET(heap_btm + (2 * WSIZE), 0);
    SET(heap_btm + (3 * WSIZE), 0);
    SET(heap_btm + (4 * WSIZE), PACK(4 * WSIZE, ALLOCATED));
    SET(heap_btm + (5 * WSIZE), PACK(0, ALLOCATED));
    head = heap_btm + (2 * WSIZE);

    // extend heap by (CHUNKSIZE) bytes
    if ((oldbrk = mem_sbrk(CHUNKSIZE)) < 0) {
        return -1;
    }

    // create a free block of (CHUNKSIZE) bytes
    SET(HDR(oldbrk), PACK(CHUNKSIZE, FREE));
    SET(FTR(oldbrk), PACK(CHUNKSIZE, FREE));
    SET(HDR(NEXT(oldbrk)), PACK(0, ALLOCATED));
    SET(SUCC(head), (int)oldbrk);
    SET(PRED(oldbrk), (int)head);
    SET(SUCC(oldbrk), 0);

    return 0;
}

/*
 * mm_malloc - allocate block by (size) bytes
 * return allocated block pointer on success, NULL on fail
 */
void *mm_malloc(size_t size) {
    size_t asize, exsize, fsize;
    char *newptr, *oldbrk, *prev, *first, *pred, *succ, *newfree;

    // if size is zero, return NULL
    if (size == 0) {
        return NULL;
    }

    // allocated size: aligned size + 2 words (for header/footer)
    // asize cannot be smaller than MINSIZE
    if (size <= MINSIZE - DWSIZE) {
        asize = MINSIZE;
    } else {
        asize = ALIGN(size) + DWSIZE;
    }

    // choose first fit free block
    newptr = (char *)GET(SUCC(head));
    if (newptr != NULL) {
        while (newptr != NULL) {
            if (SIZE(HDR(newptr)) >= asize) {
                break;
            }
            newptr = (char *)GET(SUCC(newptr));
        }
    }
    // if no fit found, extend heap
    if (newptr == NULL) {
        exsize = (asize > CHUNKSIZE) ? asize : CHUNKSIZE;
        if ((oldbrk = mem_sbrk(exsize)) < 0) {
            return NULL;
        }
        SET(HDR(oldbrk), PACK(exsize, FREE));
        SET(FTR(oldbrk), PACK(exsize, FREE));
        SET(HDR(NEXT(oldbrk)), PACK(0, ALLOCATED));

        // coalesce and insert new free block
        prev = PREV(oldbrk);
        if (ALLOC(HDR(prev))) {
            first = (char *)GET(SUCC(head));
            SET(SUCC(head), (int)oldbrk);
            SET(PRED(oldbrk), (int)head);
            SET(SUCC(oldbrk), (int)first);
            if (first != NULL) {
                SET(PRED(first), (int)oldbrk);
            }
            newptr = oldbrk;
        } else {
            exsize += SIZE(HDR(prev));
            SET(HDR(prev), PACK(exsize, FREE));
            SET(FTR(prev), PACK(exsize, FREE));
            newptr = prev;
        }
    }

    // modify asize to avoid block smaller than MINSIZE
    fsize = SIZE(HDR(newptr));
    if (fsize - asize < MINSIZE) {
        asize = fsize;
    }

    // set header/footer of allocated block
    SET(HDR(newptr), PACK(asize, ALLOCATED));
    SET(FTR(newptr), PACK(asize, ALLOCATED));

    // remove allocated block from free list
    pred = (char *)GET(PRED(newptr));
    succ = (char *)GET(SUCC(newptr));
    SET(SUCC(pred), (int)succ);
    if (succ != NULL) {
        SET(PRED(succ), (int)pred);
    }

    // create remaining free block if it exists
    if (asize < fsize) {
        newfree = NEXT(newptr);
        SET(HDR(newfree), PACK(fsize - asize, FREE));
        SET(FTR(newfree), PACK(fsize - asize, FREE));
        coalesce(newfree);
    }

    return newptr;
}

/*
 * mm_free - free block in (ptr)
 */
void mm_free(void *ptr) {
    size_t size;

    if (ptr != NULL) {
        // set header/footer of freed block and coalesce
        size = SIZE(HDR(ptr));
        SET(HDR(ptr), PACK(size, FREE));
        SET(FTR(ptr), PACK(size, FREE));
        coalesce(ptr);
    }
}

/*
 * mm_realloc - free block in (ptr) and reallocate it by (size) bytes
 * return reallocated block pointer on success, NULL on fail
 */
void *mm_realloc(void *ptr, size_t size) {
    size_t oldsize, asize, exsize, fsize, smallsize;
    char *newptr, *oldbrk, *prev, *first, *pred, *succ, *newfree;

    if (ptr != NULL) {
        oldsize = SIZE(HDR(ptr));
    }

    // if size is zero, free and return NULL
    if (size == 0) {
        if (ptr != NULL) {
            SET(HDR(ptr), PACK(oldsize, FREE));
            SET(FTR(ptr), PACK(oldsize, FREE));
            coalesce(ptr);
        }
        return NULL;
    }

    // allocated size: aligned size + 2 words (for header/footer)
    // asize cannot be smaller than MINSIZE
    if (size <= MINSIZE - DWSIZE) {
        asize = MINSIZE;
    } else {
        asize = ALIGN(size) + DWSIZE;
    }

    // choose first fit free block
    newptr = (char *)GET(SUCC(head));
    if (newptr != NULL) {
        while (newptr != NULL) {
            if (SIZE(HDR(newptr)) >= asize) {
                break;
            }
            newptr = (char *)GET(SUCC(newptr));
        }
    }
    // if no fit found, extend heap
    if (newptr == NULL) {
        exsize = (asize > CHUNKSIZE) ? asize : CHUNKSIZE;
        if ((oldbrk = mem_sbrk(exsize)) < 0) {
            return NULL;
        }
        SET(HDR(oldbrk), PACK(exsize, FREE));
        SET(FTR(oldbrk), PACK(exsize, FREE));
        SET(HDR(NEXT(oldbrk)), PACK(0, ALLOCATED));

        // coalesce and insert new free block
        prev = PREV(oldbrk);
        if (ALLOC(HDR(prev))) {
            first = (char *)GET(SUCC(head));
            SET(SUCC(head), (int)oldbrk);
            SET(PRED(oldbrk), (int)head);
            SET(SUCC(oldbrk), (int)first);
            if (first != NULL) {
                SET(PRED(first), (int)oldbrk);
            }
            newptr = oldbrk;
        } else {
            exsize += SIZE(HDR(prev));
            SET(HDR(prev), PACK(exsize, FREE));
            SET(FTR(prev), PACK(exsize, FREE));
            newptr = prev;
        }
    }

    // modify asize to avoid block smaller than MINSIZE
    fsize = SIZE(HDR(newptr));
    if (fsize - asize < MINSIZE) {
        asize = fsize;
    }

    // set header/footer of allocated block
    SET(HDR(newptr), PACK(asize, ALLOCATED));
    SET(FTR(newptr), PACK(asize, ALLOCATED));

    // remove allocated block from free list
    // BEFORE COPY to preserve old data
    pred = (char *)GET(PRED(newptr));
    succ = (char *)GET(SUCC(newptr));
    SET(SUCC(pred), (int)succ);
    if (succ != NULL) {
        SET(PRED(succ), (int)pred);
    }

    if (ptr != NULL) {
        // copy old data
        smallsize = (oldsize < asize) ? oldsize : asize;
        memcpy(newptr, ptr, (smallsize - DWSIZE));

        // set header/footer of freed block and coalesce
        // AFTER COPY to preserve old data
        SET(HDR(ptr), PACK(oldsize, FREE));
        SET(FTR(ptr), PACK(oldsize, FREE));
        coalesce(ptr);
    }

    // create remaining free block if it exists
    if (asize < fsize) {
        newfree = NEXT(newptr);
        SET(HDR(newfree), PACK(fsize - asize, FREE));
        SET(FTR(newfree), PACK(fsize - asize, FREE));
        coalesce(newfree);
    }

    return newptr;
}

/*
 * helper functions
 */

/*
 * coalesce - merge adjacent free blocks & modify free list
 * return merged block pointer
 */
static void *coalesce(void *ptr) {
    char *first, *prev, *next, *pred, *succ;
    size_t prev_alloc, next_alloc, size;

    prev = PREV(ptr);
    next = NEXT(ptr);
    prev_alloc = ALLOC(HDR(prev));
    next_alloc = ALLOC(HDR(next));
    size = SIZE(HDR(ptr));

    if (prev_alloc && next_alloc) {             // both are allocated
        // insert ptr to free list
        first = (char *)GET(SUCC(head));
        SET(SUCC(head), (int)ptr);
        SET(PRED(ptr), (int)head);
        SET(SUCC(ptr), (int)first);
        if (first != NULL) {
            SET(PRED(first), (int)ptr);
        }
        return ptr;

    } else if (prev_alloc && !next_alloc) {     // next is free
        // merge ptr and next
        size += SIZE(HDR(next));
        SET(HDR(ptr), PACK(size, FREE));
        SET(FTR(ptr), PACK(size, FREE));

        // remove next from free list
        pred = (char *)GET(PRED(next));
        succ = (char *)GET(SUCC(next));
        SET(SUCC(pred), (int)succ);
        if (succ != NULL) {
            SET(PRED(succ), (int)pred);
        }

        // insert ptr to free list
        first = (char *)GET(SUCC(head));
        SET(SUCC(head), (int)ptr);
        SET(PRED(ptr), (int)head);
        SET(SUCC(ptr), (int)first);
        if (first != NULL) {
            SET(PRED(first), (int)ptr);
        }
        return ptr;

    } else if (!prev_alloc && next_alloc) {     // prev is free
        // merge prev and ptr
        size += SIZE(HDR(prev));
        SET(HDR(prev), PACK(size, FREE));
        SET(FTR(prev), PACK(size, FREE));
        return prev;
    } else {                                    // both are free
        // merge prev, ptr, and next
        size += SIZE(HDR(prev)) + SIZE(HDR(next));
        SET(HDR(prev), PACK(size, FREE));
        SET(FTR(prev), PACK(size, FREE));

        // remove next from free list
        pred = (char *)GET(PRED(next));
        succ = (char *)GET(SUCC(next));
        SET(SUCC(pred), (int)succ);
        if (succ != NULL) {
            SET(PRED(succ), (int)pred);
        }
        return prev;
    }
}
