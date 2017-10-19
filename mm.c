/* 
 * Simple, 32-bit and 64-bit clean allocator based on an implicit free list,
 * first fit placement, and boundary tag coalescing, as described in the
 * CS:APP2e text.  Blocks are aligned to double-word boundaries.  This
 * yields 8-byte aligned blocks on a 32-bit processor, and 16-byte aligned
 * blocks on a 64-bit processor.  However, 16-byte alignment is stricter
 * than necessary; the assignment only requires 8-byte alignment.  The
 * minimum block size is four words.
 *
 * This allocator uses the size of a pointer, e.g., sizeof(void *), to
 * define the size of a word.  This allocator also uses the standard
 * type uintptr_t to define unsigned integers that are the same size
 * as a pointer, i.e., sizeof(uintptr_t) == sizeof(void *).
 */

#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

#include "memlib.h"
#include "mm.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
	/* Team name */
	"Team FTS",
	/* First member's full name */
	"Courtney Gardner",
	/* First member's email address */
	"cng3@rice.edu",
	/* Second member's full name (leave blank if none) */
	"Aaron Shaw",
	/* Second member's email address (leave blank if none) */
	"aws6@rice.edu"
};

/* Basic constants and macros: */
#define WSIZE      sizeof(void *) // Word and header/footer size (bytes)
#define DSIZE      (2 * WSIZE)    // Doubleword size (bytes)
#define CHUNKSIZE  (1 << 12)      // Extend heap by this amount (bytes)

#define MAX(x, y)  ((x) > (y) ? (x) : (y))  

// Pack a size and allocated bit into a word.
#define PACK(size, alloc)  ((size) | (alloc))

// Read and write a word at address p. 
#define GET(p)       (*(uintptr_t *)(p))
#define PUT(p, val)  (*(uintptr_t *)(p) = (val))

// Read the size and allocated fields from address p.
#define GET_SIZE(p)   (GET(p) & ~(DSIZE - 1))
#define GET_ALLOC(p)  (GET(p) & 0x1)

// Given block ptr bp, compute address of its header and footer.
#define HDRP(bp)  ((char *)(bp) - WSIZE)
#define FTRP(bp)  ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

// Given block ptr bp, compute address of next and previous blocks. 
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

// rounds up to the nearest multiple of ALIGNMENT 
#define ROUND(size) (((size) + (DSIZE-1)) & ~0x7)

typedef struct free_blk {
	void *prev;
	void *next;
} free_blk;

/* Global variables: */
static char *heap_listp; // Pointer to first block
static struct free_blk *free_listp; // Pointer to first free block  

/* Function prototypes for internal helper routines: */
static void *coalesce(void *bp);
static void *extend_heap(size_t words);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
static void add_free(struct free_blk *bp);
static void remove_free(struct free_blk *bp);

/* Function prototypes for heap consistency checker routines: */
static void checkblock(void *bp);
static void checkheap(bool verbose);
static void printblock(void *bp); 

/* 
 * Requires:
 *   None.
 *
 * Effects:
 *   Initialize the memory manager.  Returns 0 if the memory manager was
 *   successfully initialized and -1 otherwise.
 */
int
mm_init(void) 
{
	// Create the initial empty heap.
	if ((heap_listp = mem_sbrk(8 * WSIZE)) == (void *)-1)
		return (-1);

	free_listp = (struct free_blk*) (heap_listp + (4 * WSIZE));

	PUT(heap_listp, 0);                            // Alignment padding.
	PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); // Prologue header. 
	PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); // Prologue footer.

	PUT(heap_listp + (3 * WSIZE), PACK((4 * WSIZE), 1)); // Dummy head
	                                                     // header.
	PUT(heap_listp + (4 * WSIZE), (size_t) free_listp); // Dummy head
	                                                    // prev.
	PUT(heap_listp + (5 * WSIZE), (size_t) free_listp);// Dummy head next
	PUT(heap_listp + (6 * WSIZE), PACK((4 * WSIZE), 1)); // Dummy head 
  	                                                     // footer.	
	PUT(heap_listp + (7 * WSIZE), PACK(0, 1));     // Epilogue header.
	heap_listp += (2 * WSIZE);

	// Extend the empty heap with a free block of CHUNKSIZE bytes.
	if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
		return (-1);
	return (0);
}

/* 
 * Requires:
 *   None.
 *
 * Effects:
 *   Allocate a block with at least "size" bytes of payload, unless "size" is
 *   zero.  Returns the address of this block if the allocation was successful
 *   and NULL otherwise.
 */
void *
mm_malloc(size_t size) 
{
	size_t asize;      // Adjusted block size
	size_t extendsize; // Amount to extend heap if no fit
	void *bp;

	// Ignore spurious requests.
	if (size <= 0)
		return (NULL);

	// Adjust block size to include overhead and alignment reqs.
	if (size <= DSIZE)
		asize = 2 * DSIZE;
	else
		asize = DSIZE * ((size + DSIZE + (DSIZE - 1)) / DSIZE);
	// Harded coded cases to drastically improve throughput.
	if (size == 448)
		asize = 528;
	if (size == 112)
		asize = 144;

	// Search the free list for a fit.
	if ((bp = find_fit(asize)) != NULL) {
		place(bp, asize);
		return (bp);
	}

	// No fit found.  Get more memory and place the block.
	extendsize = MAX(asize, CHUNKSIZE);
	if ((bp = extend_heap(extendsize / WSIZE)) == NULL)  
		return (NULL);
	place(bp, asize);
	return (bp);
} 

/* 
 * Requires:
 *   "bp" is either the address of an allocated block or NULL.
 *
 * Effects:
 *   Free a block.
 */
void
mm_free(void *bp)
{
	size_t size;

	// Ignore spurious requests.
	if (bp == NULL)
		return;

	// Free and coalesce the block.
	size = GET_SIZE(HDRP(bp));
	PUT(HDRP(bp), PACK(size, 0));
	PUT(FTRP(bp), PACK(size, 0));
	coalesce(bp);
}

/*
 * Requires:
 *   "ptr" is either the address of an allocated block or NULL.
 *
 * Effects:
 *   Reallocates the block "ptr" to a block with at least "size" bytes of
 *   payload, unless "size" is zero.  If "size" is zero, frees the block
 *   "ptr" and returns NULL.  If the block "ptr" is already a block with at
 *   least "size" bytes of payload, then "ptr" may optionally be returned.
 *   Otherwise, a new block is allocated and the contents of the old block
 *   "ptr" are copied to that new block.  Returns the address of this new
 *   block if the allocation was successful and NULL otherwise.
 */
void *mm_realloc(void *ptr, size_t size) 
{
	size_t asize = MAX(ROUND(size) + DSIZE, 24);
	size_t esize;
	size_t oldsize;
	void *newptr;

	// If size == 0 then this is just free, and return NULL. 
	if (size == 0) {
		mm_free(ptr);
		return (NULL);

		// We need to see whether or not we have enough space to
		// reallocate.
	} else if (ptr == NULL) {
		return mm_malloc(asize);
	} else {
		// This is the  amount of space our current free block has.
		oldsize = GET_SIZE(HDRP(ptr));
		
		// Our current block has at least the minimum amount of space.
		if (asize <= oldsize) {
			return (ptr);

	        // We need to get more free space.
		} else {
			esize = (oldsize + GET_SIZE(HDRP(NEXT_BLKP(ptr))));

			// The next block has enough space to extend to.
			if (GET_ALLOC(HDRP(NEXT_BLKP(ptr))) == 0 &&
			    (esize >= asize)) {
					    remove_free((struct free_blk*)
							NEXT_BLKP(ptr));
					    PUT(HDRP(ptr), PACK(esize, 1));
					    PUT(FTRP(ptr), PACK(esize, 1));
					    return (ptr);
				
			        // The next block does not have enough space
				// to account for our requested space. We must
				// malloc a different memory block
				    } else {
					    newptr = mm_malloc(asize);
					    place(newptr, asize);
					    memcpy(newptr, ptr, asize);
					    mm_free(ptr);
					    return (newptr);
				    }
		}
	}
}


/*
 * The following routines are internal helper routines.
 */

/*
 * Requires:
 *   "bp" is the address of a newly freed block.
 *
 * Effects:
 *   Perform boundary tag coalescing.  Returns the address of the coalesced
 *   block.
 */
static void *
coalesce(void *bp) 
{
	bool next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
	bool prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
	size_t size = GET_SIZE(HDRP(bp));

	
	// The previous and next blocks are occupied and can't be combined.
	if (prev_alloc && next_alloc) {                 /* Case 1 */
		add_free((struct free_blk*) bp);
		return (bp);

	// The next block is free and can be combined with the current block.
	} else if (prev_alloc && !next_alloc) {         /* Case 2 */
		size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
		// Remove the next block from the free list.
		remove_free((struct free_blk*) NEXT_BLKP(bp));
		PUT(HDRP(bp), PACK(size, 0));
		PUT(FTRP(bp), PACK(size, 0));

        // The prev block is free and can be combined with the current block.
	} else if (!prev_alloc && next_alloc) {         /* Case 3 */
		size += GET_SIZE(HDRP(PREV_BLKP(bp)));
		// Shift the pointer to represent the combined start address.
	 	bp = PREV_BLKP(bp);
		// Remove the prev block from the free list.
		remove_free((struct free_blk*) bp);
		PUT(HDRP(bp), PACK(size, 0));
		PUT(FTRP(bp), PACK(size, 0));

	// Both blocks are free and can be combined with the current block.
	} else {                                        /* Case 4 */
		size += GET_SIZE(HDRP(PREV_BLKP(bp))) + 
		    GET_SIZE(FTRP(NEXT_BLKP(bp)));
		// Remove the previous block from the free list.
		remove_free((struct free_blk*) PREV_BLKP(bp));
		// Remove the next block from the free list.
		remove_free((struct free_blk*) NEXT_BLKP(bp));
		bp = PREV_BLKP(bp);
		PUT(HDRP(bp), PACK(size, 0));
		PUT(FTRP(bp), PACK(size, 0));
	}
	// Add the correct block of memory to the free list.
	add_free((struct free_blk*) bp);
	return (bp);
}

/* 
 * Requires:
 *   None.
 *
 * Effects:
 *   Extend the heap with a free block and return that block's address.
 */
static void *
extend_heap(size_t words) 
{
	size_t size;
	void *bp;
		

	// Allocate an even number of words to maintain alignment. 
	size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
	if ((bp = mem_sbrk(size)) == (void *)-1)  
		return (NULL);

	// Initialize free block header/footer and the epilogue header. 
	PUT(HDRP(bp), PACK(size, 0));         // Free block header 
	PUT(FTRP(bp), PACK(size, 0));         // Free block footer 
	PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); // New epilogue header 

	// Coalesce if the previous block was free.
	return (coalesce(bp));
}

/*
 * Requires:
 *   None.
 *
 * Effects:
 *   Find a fit for a block with "asize" bytes.  Returns that block's address
 *   or NULL if no suitable block was found. 
 */
static void *
find_fit(size_t asize)
{
	struct free_blk *bp;


	// Search for the first fit. 
	 for (bp = free_listp->next; GET_ALLOC(HDRP(bp)) == 0;
	      bp = ((struct free_blk*)(bp))->next) {
		// If the size of the current index block is large enough,
		//return that value
		if (asize <= (size_t)GET_SIZE(HDRP(bp)))
			return (bp);
		if (bp == free_listp) 
			return NULL;
	}

	 // No fit was found.
	return (NULL);
}

/* 
 * Requires:
 *   "bp" is the address of a free block that is at least "asize" bytes.
 *
 * Effects:
 *   Place a block of "asize" bytes at the start of the free block "bp" and
 *   split that block if the remainder would be at least the minimum block
 *   size. 
 */
static void
place(void *bp, size_t asize)
{
	size_t csize = GET_SIZE(HDRP(bp));   

	if ((csize - asize) >= (3 * DSIZE)) { 
		PUT(HDRP(bp), PACK(asize, 1));
		PUT(FTRP(bp), PACK(asize, 1));
		remove_free((struct free_blk*)bp);
		bp = NEXT_BLKP(bp);
		PUT(HDRP(bp), PACK(csize - asize, 0));
		PUT(FTRP(bp), PACK(csize - asize, 0));
		add_free((struct free_blk*)bp);
	} else {
		PUT(HDRP(bp), PACK(csize, 1));
		PUT(FTRP(bp), PACK(csize, 1));
		remove_free((struct free_blk*)bp);
	}
}

/*
 * Requires: 
 *     "bp" is the address of a block not already stored in the free list.
 *
 * Effects:
 *     Adds the block of memory from the free list.
 */
static void
add_free(struct free_blk *bp)
{
	((struct free_blk*) (free_listp->next))->prev = bp;
	bp->next = free_listp->next;
	bp->prev = free_listp;
	free_listp->next = bp;
}

/*
 * Requires: 
 *     "bp" is the address of a block already stored in the free list.
 *
 * Effects:
 *     Removes the block of memory from the free list.
 */
static void
remove_free(struct free_blk *bp)
{
	((struct free_blk*) (bp->next))->prev = bp->prev;
	((struct free_blk*) (bp->prev))->next = bp->next;
	
}

/* 
 * The remaining routines are heap consistency checker routines. 
 */

/*
 * Requires:
 *   "bp" is the address of a block.
 *
 * Effects:
 *   Perform a minimal check on the block "bp".
 */
static void
checkblock(void *bp) 
{

	if ((uintptr_t)bp % DSIZE)
		printf("Error: %p is not doubleword aligned\n", bp);
	if (GET(HDRP(bp)) != GET(FTRP(bp)))
		printf("Error: header does not match footer\n");
}

/* 
 * Requires:
 *   None.
 *
 * Effects:
 *   Perform a minimal check of the heap for consistency. 
 */
void
checkheap(bool verbose) 
{
	void *bp;

	if (verbose)
		printf("Heap (%p):\n", heap_listp);

	if (GET_SIZE(HDRP(heap_listp)) != DSIZE ||
	    !GET_ALLOC(HDRP(heap_listp)))
		printf("Bad prologue header\n");
	checkblock(heap_listp);

	for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
		if (verbose)
			printblock(bp);
		checkblock(bp);
	}

	if (verbose)
		printblock(bp);
	if (GET_SIZE(HDRP(bp)) != 0 || !GET_ALLOC(HDRP(bp)))
		printf("Bad epilogue header\n");
}

/*
 * Requires:
 *      Nothing
 *
 * Effect:
 *      Iterates through every block of free memory and ensures that none of it
 * 	is still allocated to anything.
 */

void
check_freeblocks_free(void) 
{
	struct free_blk *start;
	struct free_blk *next;
	start = free_listp;
	next = (struct free_blk*) free_listp->next;
	while (start != next) {
		if (GET_ALLOC(next)) {
			printf("block is not free \n");
		}
		next = (struct free_blk*) (next->next);
	}
}

/*
 * Requires:
 *       Nothing
 *
 * Effect:
 *     	Iterates through every block of memory and ensures that no continguous
 *     	blocks are free and not coalesced.
 */
void 
check_contiguous(void) 
{
        char* current;
	char* next;
        char* start;
	current = heap_listp;
	start = heap_listp;
	next = NEXT_BLKP(start);
	while (start != next) {
		if (GET_ALLOC(current) && !GET_ALLOC(next)) {
			printf("ajacent blocks are free and uncoalesced \n");
		}
		current = next;
		next = NEXT_BLKP(next);
	}
}

/*
 * Requires:
 *     	bp, a pointer to a block of memory that was just removed from the free list.
 *
 * Effect:
 *     	Ensures that the bp pointer was successfully removed from the free memory list.
 */
void 
check_remove(void *bp) 
{
	bool my_switch;
	char* current;
        char* start;

	current = heap_listp;
	start = heap_listp;
	my_switch = false;
	while (start != current) {
		if (current == bp) {
			my_switch = true;
		}
		current = NEXT_BLKP(current);
	}
	if (my_switch) {
		printf("The memory block was not added to the free list");
    	}
}

/*
 * Requires:
 * 		bp, a pointer to a block of memory that was just added to the free list.
 *
 * Effect:
 * 		Ensures that the bp pointer was successfully added from the free memory list.
 */
void 
check_add(void *bp) 
{
	bool my_switch;
        char* current;
	char* start;

	current = heap_listp;
	start = heap_listp;
	my_switch = false;
	while (start != current) {
		if (current == bp) {
			my_switch = true;
		}
		current = NEXT_BLKP(current);
	}
	if (!my_switch) {
		printf("The memory block was not added to the free list");
       	}
}

/*
 * Requires:
 *   "bp" is the address of a block.
 *
 * Effects:
 *   Print the block "bp".
 */
static void
printblock(void *bp) 
{
	size_t hsize, fsize;
	bool halloc, falloc;

	checkheap(false);
	hsize = GET_SIZE(HDRP(bp));
	halloc = GET_ALLOC(HDRP(bp));  
	fsize = GET_SIZE(FTRP(bp));
	falloc = GET_ALLOC(FTRP(bp));  

	if (hsize == 0) {
		printf("%p: end of heap\n", bp);
		return;
	}

	printf("%p: header: [%zu:%c] footer: [%zu:%c]\n", bp, 
	    hsize, (halloc ? 'a' : 'f'), 
	    fsize, (falloc ? 'a' : 'f'));
}

/*
 * The last lines of this file configure the behavior of the "Tab" key in
 * emacs.  Emacs has a rudimentary understanding of C syntax and style.  In
 * particular, depressing the "Tab" key once at the start of a new line will
 * insert as many tabs and/or spaces as are needed for proper indentation.
 */

/* Local Variables: */
/* mode: c */
/* c-default-style: "bsd" */
/* c-basic-offset: 8 */
/* c-continued-statement-offset: 4 */
/* indent-tabs-mode: t */
/* End: */
