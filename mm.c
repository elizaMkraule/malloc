/* 
 * This is a 32-bit and 64-bit clean allocator based on segrageted explicit free lists,
 * first fit placement within the appropriate list, and boundary tag coalescing.
 * Blocks are aligned to word boundaries.  
 * This yields 8-byte aligned blocks on a 32-bit processor as well as on a 64-bit processor.
 * The minimum block size is four words.
 *
 * This allocator uses the size of a pointer, e.g., sizeof(void *), to
 * define the size of a word. This allocator also uses the standard
 * type uintptr_t to define unsigned integers that are the same size
 * as a pointer, i.e., sizeof(uintptr_t) == sizeof(void *).
 */

#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <math.h>

#include "memlib.h"
#include "mm.h"


/* Basic constants and macros: */  
#define WSIZE      8            /* Word size */ 
#define DSIZE      (2 * WSIZE)  /* Doubleword size (bytes) */
#define CHUNKSIZE  (1 << 12)    /* Extend heap by this amount (bytes) */
#define NUM_SEGS   12           /* Free lists within size 2^5 2^6 ... 2^17 */
#define ALIGNMENT  8            /* Alignment */

#define MAX(x, y)  ((x) > (y) ? (x) : (y))  
#define ALIGN(size)  (((size) + (ALIGNMENT - 1)) & ~(ALIGNMENT - 1))
#define LOG2(i) 31 - __builtin_clz(i)


/* Pack a size and allocated bit into a word. */
#define PACK(size, alloc)  ((size) | (alloc))


/* Read and write a word at address p. */
#define GET(p)       (*(uintptr_t *)(p))
#define PUT(p, val)  (*(uintptr_t *)(p) = (val))


/* Read the size and allocated fields from address p. */
#define GET_SIZE(p)   (GET(p) & ~(ALIGNMENT - 1)) 
#define GET_ALLOC(p)  (GET(p) & 0x1)


/* Given block ptr bp, compute address of its header and footer. */
#define HDRP(bp)  ((char *)(bp) - WSIZE)
#define FTRP(bp)  ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)


/* Given block ptr bp, compute address of next and previous blocks in the heap. */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))


/* Global variables: */
static void *heap_listp;        /* Pointer to first block */ 
struct pointers* free_lists;    /* Pointer to the array of free lists */

 /* Pointers structur */
struct pointers {
    struct pointers *next; /* next free block */ 
    struct pointers *prev; /* previous block */
};


/* Function prototypes for internal helper routines: */
static void *coalesce(void *bp);
static void *extend_heap(size_t words);
struct pointers *find_fit(size_t asize);
static void place(void *bp, size_t asize);

/* Function prototypes for heap consistency checker routines: */
static void checkblock(void *bp);
static void checkheap(bool verbose);
static void printblock(void *bp); 

/* Helper functions: */
static void insertNode(struct pointers *bp);
static void removeNode(struct pointers *bp);
static struct pointers* get_free_list_head(size_t size);
struct pointers* find_block(struct pointers* list, size_t asize);



/* 
 * Requires:
 *      None.
 *
 * Effects:
 *      Initialize the memory manager.  Returns 0 if the memory manager was
 *      successfully initialized and -1 otherwise.
 */

int
mm_init(void) 
{         
        // Create the heap with the exact size of the array free_lists.
        if ((free_lists = (struct pointers*) mem_sbrk(NUM_SEGS * sizeof(struct pointers))) == (void *)-1)
                return (-1);
        
        // Initialize all the structurs in the lists to point to themself, to create a cycled list. 
        for (int i = 0; i < NUM_SEGS; i++) {
                free_lists[i].next = &free_lists[i]; 
                free_lists[i].prev = &free_lists[i];    
        }



        /* Create the initial empty heap. */
        if ((heap_listp = mem_sbrk(3 * WSIZE)) == (void *)-1)
                return (-1);

        PUT(heap_listp + (0 * WSIZE), PACK(DSIZE, 1)); /* Prologue header */ 
        PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); /* Prologue footer */ 
        PUT(heap_listp + (2 * WSIZE), PACK(0, 1));     /* Epilogue header */
        heap_listp += (WSIZE);                         /* Needed for the heap checker */

        /* Extend the empty heap with a free block of CHUNKSIZE bytes. */
        if (extend_heap(CHUNKSIZE / (WSIZE)) == NULL)
                return (-1);
        
        return (0);     
}

/* 
 * Requires:
 *      asize is an aligned size of bytes.
 *
 * Effects:
 *      Based on the asize input, finds the apropriate free list and returns it's first node (head).
 */
struct pointers*
get_free_list_head(size_t asize)
{
        /* Find the index in the array, based on log(asize) / log(2). */
        int num_segs = NUM_SEGS;
        int idx = LOG2((int)(asize));

        idx = idx - 5;
        /* If the index is beyond the scope of the array, return the last index in the array. */
        if (idx >= num_segs) {
                idx = num_segs - 1;
        }
  
        return &free_lists[idx];
}

/* 
 * Requires:
 *      The given free list 'list' must have at least one block i.e list cannot point to itself.
 *
 * Effects:
 *      Returns a block from the given list if it's big enough to store a block of asize, otherwise returns NULL.
 *      If the list is too long, quits searching after a certain amount of iterations.   
 */
struct pointers*
find_block(struct pointers* list, size_t asize)
{
        struct pointers *cur = list->next;
        int iteration = 0;
        do {
                if (asize <= GET_SIZE(HDRP(cur))) // if the block is big enough, return it.
                        return cur;
                cur = cur->next;
                if (iteration == 50)    // quit after 50 iteratoins.
                        return (NULL);
                iteration++;
        } while (cur != list);
        
        /* No fit was found. */
        return (NULL);
} 


/* 
 * Requires:
 *      None.
 *
 * Effects:
 *      Allocate a block with at least "size" bytes of payload, unless "size" is
 *      zero.  Returns the address of this block if the allocation was successful
 *      and NULL otherwise.
 */
void *
mm_malloc(size_t size)  
{
        size_t asize;           /* Adjusted block size. */
        struct pointers *bp;    /* Initializing a pointer to a block. */
        size_t extendsize;      /* Amount to extend heap if no fit. */ 

        /* Ignore spurious requests. */
        if (size == 0)
                return (NULL);

        /* Adjust block size to include overhead and alignment requests. */
        if (size <= DSIZE) { 
                asize = 2 * WSIZE + sizeof(struct pointers); 
        } else {
                asize = ALIGN(size);
                asize = asize +  2 * WSIZE;
        }


        /* 
         * Find the appropriate free list in the free_lists array,
         * go to the next sized list until found,
         * expands the heap if needed.
         */

        if ((bp = find_fit(asize)) != NULL) {
                place(bp, asize); 
                return bp;
        } 
        
        extendsize = MAX(asize, CHUNKSIZE); // Expend the heap as needed.
        if ((bp = extend_heap(extendsize / WSIZE )) == NULL) {
                return (NULL);
        }

        place(bp, asize); // Place the block with it's appropriate size.
        return (bp);  
} 


/*
 * Requires:
 *      asize is an alinged block size, including the overheads from the explicit, un-NULL list.
 *
 * Effects:
 *      Finds if there is an available block of the correct size in a segragated free list and returns it, 
 *      otherwise returns NULL.
 *   
*/
struct pointers*
find_fit(size_t asize) 
{
        struct pointers* block;

        // 1. Find the correct list.
        int idx = LOG2((int)asize);
        int num_segs = NUM_SEGS;
        idx = idx - 5;  // Minimum block is 2^5
        
        if (idx >= num_segs ) {
                idx = num_segs - 1; // Adjust index if it's larger than array length. 
        }
     
        // 2. Iterate over lists to find a proper block.
        for (; idx < num_segs; idx++) {
                if (free_lists[idx].next != &free_lists[idx]) {     
                        block = find_block(&free_lists[idx], asize);
                        if (block != NULL) {
                                return block;
                        }
                }
        }

        /* Did not find a proper block. */
        return (NULL);
}

/* 
 * Requires:
 *   "bp" is either the address of an allocated block or NULL.
 *
 * Effects:
 *   Free and coalesce the block.
 */
void
mm_free(void *bp)
{
        size_t size;

        /* Ignore spurious requests. */
        if (bp == NULL)
                return;
        
        /* Free and coalesce the block. */
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
void *
mm_realloc(void *ptr, size_t size)
{
        size_t oldsize = GET_SIZE(HDRP(ptr));
        size_t newsize;
        void *newptr;
        size_t min_block_size =  (2 * DSIZE) + sizeof(struct pointers);

        /* If size is 0, just free the pointer. */
        if (size == 0) {
                mm_free(ptr);
                return (NULL);
        }

        /* If size is smaller than minimum size, align to minimum size. */
        if (size <= DSIZE) {
                newsize = 2 * WSIZE + sizeof(struct pointers); 
        }

        /* Else, align the size and add the extra payload for pointers. */
        else {
                newsize = ALIGN((size));
                newsize = newsize + DSIZE;
        }

        /* If oldptr is NULL, then this is just a malloc call. */
        if (ptr == NULL) {
                newptr = mm_malloc(size);
                return (newptr);
        }
        
        /* If newsize smaller or equal to oldsize, return it. */
        if (newsize <= oldsize) {
                return (ptr);
        }
        
        /* We know newsize bigger than oldsize, must obtain more space for the pointer. */
        
        // Case 1: either the previous or next block are free & has enough space to merge the blocks.
        if (!GET_ALLOC(HDRP(PREV_BLKP(ptr)))) { // Previous block is free. 

                size_t free_block_old_size = GET_SIZE(HDRP(PREV_BLKP(ptr)));
                if (free_block_old_size >= newsize - oldsize) { // Previous block is big enough to merge.
                        
                        removeNode((struct pointers*) PREV_BLKP(ptr)); // Remover the prev free block from it's list.
                        newptr = PREV_BLKP(ptr);

                        /* Allocate the new block and adjust the size of the new block. */                         
                        PUT(HDRP(newptr), PACK(free_block_old_size + oldsize, 1)); 
                        PUT(FTRP(newptr), PACK(free_block_old_size + oldsize, 1));

                        /* Copy the data */
                        memcpy(newptr, ptr, oldsize - DSIZE);
                        return (newptr);
                }
        }
        
        if (!GET_ALLOC(HDRP(NEXT_BLKP(ptr)))) { // Next block is free.

                size_t free_block_old_size = GET_SIZE(HDRP(NEXT_BLKP(ptr)));

                if ((free_block_old_size >= newsize - oldsize) && (free_block_old_size > min_block_size)) {
                        
                        // The next free block is big enough for the reminder of the newsize.
                        // First remove the free block from it's list. 
                        removeNode((struct pointers*)NEXT_BLKP(ptr));
                        newptr = ptr;
                        
                        // Check if after combining we can split the rest.
                        if (free_block_old_size - (newsize - oldsize) >= min_block_size) {
                                
                                // Combine the blocks and split.
                                // Adjust the size of the new block.                         
                                PUT(HDRP(newptr), PACK(newsize, 1)); 
                                PUT(FTRP(newptr), PACK(newsize, 1)); 

                                memcpy(newptr, ptr, newsize - DSIZE);
                                
                                // Get a pointer to the next block, after size was changed.
                                void* next_ptr = NEXT_BLKP(newptr);                                

                                // Change the next block (reminder) size, and mark as free.
                                PUT(HDRP(next_ptr), PACK(free_block_old_size - (newsize - oldsize), 0));
                                PUT(FTRP(next_ptr), PACK(free_block_old_size - (newsize - oldsize), 0));
                                
                                // Initialize pointers.
                                ((struct pointers*)next_ptr)->next = NULL;
                                ((struct pointers*)next_ptr)->prev = NULL;

                                // Insert the reminder block to it's proper free list.
                                insertNode((struct pointers*)next_ptr);

                                return (newptr);

                        } else { // The free block is big enough to merge, but can't split it.                                  
                                
                                // Adjust the size of the new block to contain both blocks.                        
                                PUT(HDRP(newptr), PACK(oldsize + free_block_old_size, 1)); 
                                PUT(FTRP(newptr), PACK(oldsize + free_block_old_size, 1)); 
                                
                                // Copy the data.
                                memcpy(newptr, ptr, free_block_old_size + oldsize - DSIZE);
                                return (newptr);
                        }
                }
        }
        
        // Case 2: the prev/next block are not free or dont have enough space: find new space.
        newptr = mm_malloc((int)(2 * size));
        
         /* Copy */
        newsize = ALIGN((int)(2 * size));
        newsize = newsize + DSIZE;
        memcpy(newptr, ptr, newsize - DSIZE);
        
        /* Free the old block. */    
        mm_free(ptr);
        return (newptr);   
}


/*
 * Requires:
 *      "bp" is the address of a newly freed block and has not been placed in free list yet. 
 *
 * Effects:
 *      Perform boundary tag coalescing. 
 *      Returns the address of the coalesced block.
 */
static void *
coalesce(void *bp) 
{
        /* get the size of the block we are pointing at. */ 
        size_t size = GET_SIZE(HDRP(bp));
        
        /* Check if neighbors blocks are allocated. */
        bool prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
        bool next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));             

        if (prev_alloc && next_alloc) {                 /* Case 1: prev and next physical blocks are allocated. */
                insertNode((struct pointers*)bp);  

        } else if (prev_alloc && !next_alloc) {         /* Case 2: only next physical block is allocated: merge with next block. */

                removeNode((struct pointers*)(NEXT_BLKP(bp)));
                size += GET_SIZE(HDRP(NEXT_BLKP(bp))); 
                PUT(HDRP(bp), PACK(size, 0));          
                PUT(FTRP(bp), PACK(size, 0));    
                insertNode((struct pointers*)bp); 

        } else if (!prev_alloc && next_alloc) {         /* Case 3: only prev physical block is allocated: merge with prev block. */

                removeNode((struct pointers*)(PREV_BLKP(bp)));
                size += GET_SIZE(HDRP(PREV_BLKP(bp)));
                PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
                PUT(FTRP(bp), PACK(size, 0)); 
                bp = PREV_BLKP(bp);
                insertNode((struct pointers*)bp); 
        
        } else {                                        /* Case 4: both prev and next physical blocks are free: merge with both. */

                removeNode((struct pointers*)(NEXT_BLKP(bp)));
                removeNode((struct pointers*)(PREV_BLKP(bp)));
                size += (GET_SIZE(HDRP(PREV_BLKP(bp))) + 
                        GET_SIZE(FTRP(NEXT_BLKP(bp))));
                PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
                PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
                bp = PREV_BLKP(bp);
                insertNode((struct pointers*)bp); 
        }
        
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

        /* Allocate an even number of words to maintain alignment. */
        size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
        
        /* Allocate space of size */
        if ((bp = mem_sbrk(size)) == (void *)-1)  // bp is the the first byte in the newly allocated heap area
                return (NULL);

        
        /* Initialize free block header/footer and the epilogue header in the new heap area. */
        PUT(HDRP(bp), PACK(size, 0));         /* Free block header */
        PUT(FTRP(bp), PACK(size, 0));         /* Free block footer */
        PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */

        bp = coalesce(bp);
        return (bp);
}


/*
 * Requires:
 *      "bp" is a pointer to the block that needs to be removed from the free list. 
 *
 * Effects:
 *      Removes "bp" from it's segragated free list.    
 */
static void
removeNode(struct pointers *bp)
{ 
        bp->prev->next = bp->next;
        bp->next->prev = bp->prev;
}

/*
 * Requires:
 *      "bp" is a pointer to the block that needs to be inserted to a free list. 
 *
 * Effects:
 *      Finds the appropriate free list and inserts bp.    
 */
static void
insertNode(struct pointers *bp)
{ 
        // Find the appropriate free list to insert the free block.
        struct pointers *list_head = get_free_list_head(GET_SIZE(HDRP(bp))); 

        // Insert.
        list_head->prev->next = bp;
        bp->prev = list_head->prev;
        list_head->prev = bp;
        bp->next = list_head;
}
        

/* 
 * Requires:
 *      "bp" is the address of a free block that is at least "asize" bytes.
 *
 * Effects:
 *      Place a block of "asize" bytes at the start of the free block "bp" and
 *      split that block if the remainder would be at least the minimum block size. 
 */
static void
place(void *bp, size_t asize)
{
        size_t csize = GET_SIZE(HDRP(bp));  // Get the size of the free block.
        size_t min_block_size =  (2 * WSIZE) + sizeof(struct pointers); // Minimum size of a block.
        
        /* Always need to remove the node. */
        removeNode(bp);
        
        /* 
         * Check if the block we are going to place is smaller than the free block 
         * and if the remainder of the space is enough to be an independent block.
         */

        if ((csize - asize) >= min_block_size) {   /* The case we have enough space to split. */

                /* Allocate asize. */
                PUT(HDRP(bp), PACK(asize, 1)); 
                PUT(FTRP(bp), PACK(asize, 1)); 
                
                /* Get the location of next block. */
                bp = NEXT_BLKP(bp); 
                
                /* Allocated the remainder of the block and mark as free. */
                PUT(HDRP(bp), PACK(csize - asize, 0)); 
                PUT(FTRP(bp), PACK(csize - asize, 0)); 

                /* Insert the reminder of the block into a free list. */
                insertNode((struct pointers*)bp);  
                        
        } else {        /* The case we don't have enough space for another block, allocate whole thing. */ 
                PUT(HDRP(bp), PACK(csize, 1)); 
                PUT(FTRP(bp), PACK(csize, 1));
        }
}

/* 
 * The remaining routines are heap consistency checker routines. 
 */

/*
 * Requires:
 *   "bp" is the address of a block.
 *
 * Effects:
 *   Perform a check on the block "bp".
 */
static void
checkblock(void *bp) 
{
        if ((uintptr_t)bp % WSIZE)
                printf("Error: %p is not singleword aligned\n", bp);
        if (GET(HDRP(bp)) != GET(FTRP(bp)))
                printf("Error: header does not match footer\n");
        if (GET_SIZE(HDRP(bp)) != GET_SIZE(FTRP(bp)))
                printf("Error: size at header does not match size at footer\n");  
        if (GET_ALLOC(HDRP(bp)) != GET_ALLOC(FTRP(bp)))
                printf("Error: allocation at header does not match allocation at footer\n");                  
}

/* 
 * Requires:
 *   None.
 *
 * Effects:
 *   Perform a check of the heap for consistency. 
 */
void
checkheap(bool verbose) 
{
        void *bp;
        if (verbose)
                printf("Heap (%p):\n", heap_listp);

        /* Checks the prologue header size and alloc mark. */
        if (GET_SIZE(HDRP(heap_listp)) != DSIZE ||
            !GET_ALLOC(HDRP(heap_listp)))
                printf("Bad prologue header\n");
        checkblock(heap_listp);

        /* For every block in the heap, do the following checks: */
        for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
                if (verbose)
                       printblock(bp);
                /* Check block */
                checkblock(bp);
                
                /* Check if prev block and current block are both free. */
                if (bp != heap_listp) {
                        if ((!GET_ALLOC(PREV_BLKP(HDRP(bp)))) && (!GET_ALLOC(PREV_BLKP(HDRP(bp))))) {
                                printf("Coalesce error: two continuous free blocks. \n");
                        }
                }
        }

        /* Check that every block in every segrageted free list is actually free. */
        for (int i = 0; i < NUM_SEGS; i++) {
                struct pointers* head = &free_lists[i];
                struct pointers* temp = head->next;
                while (&head != &temp) {
                        if (!GET_ALLOC(HDRP(temp))) {
                                printf("Block %p in list index %i is not free.\n", temp, i);
                        }
                        temp = temp->next;
                }
        }

        /* Checks the epilogue header size and alloc mark. */
        if (verbose)
                printblock(bp);
        if (GET_SIZE(HDRP(bp)) != 0 || !GET_ALLOC(HDRP(bp)))
                printf("Bad epilogue header\n");
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

        void* hdr = HDRP(bp);
        void* ftr = FTRP(bp);

        if (hsize == 0) {
                 printf("%p: end of heap\n", bp);
                return;
        }

        printf("%p: header: %p [%zu:%c] footer: %p [%zu:%c]\n", bp, hdr,
            hsize, (halloc ? 'a' : 'f'), ftr,
            fsize, (falloc ? 'a' : 'f'));
}

