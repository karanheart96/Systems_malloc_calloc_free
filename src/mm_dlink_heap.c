/*
 * mm_dlink_heap.c
 *
 * The heap memory is delimited by a start and end header block so as to avoid complications.
 * There can be any number of blocks inside the heap section (dynamically allocated)
 * Each block will be having 2 headers, one at the beginning of the block and another at the end of the block.
 * Also, for keeping track of the free block, we have implemented 2 pointers to point to the previous and next free nodes.
 * Also there is a freeList that is maintained in order to get the first fit free block.
 * The block has the union - HeadFoot allocated to beginning and end of the block.
 *
 * Sample block ->
 *
 *  ---------- --------------------  ---------
 * | HeadFoot |       payload      | HeadFoot |
 *  ---------- --------------------  ---------
 *
 *
 *  Sample Header ->
 *
 *   ---------------------------------------------
 *  | prev_free | next_free | size | alloc_or_not |
 *   ---------------------------------------------
 *
 * Put the block back into the free list.
 * Two cases:
 * 1) Combine with lower adjacent block -> Check if previous block is in freelist &
 *    Make the block into one bigger block.
 * 2) Combine with upper adjacent block -> Check if next part of memory is in freelist &
 *    Make the block into one bigger block.
 *
 *  Take the block from the list:
 *  Two cases:
 *  1) The block is a perfect fit.In this case unlink the block from the list
 *  and link the previous block to the next block.
 *  2)The block is very big.In this case split the bigger block into two blocks.
 *  Keep the first block in the free list.
 *  Assign the second block to the user.
 *
 *  There are two algorithms which we implemented.
 *  1)First Fit:
 *          This algorithm finds the first block which is large enough to hold all the requested memory.
 *          Returns the block as soon as the first block is found.
 *  2)Best Fit:
 *          This algorithm finds the block which has the least wastage of storage,
 *          at the same time capable of holding all the requested memory.
 *          Traverses through the entire list to find the best fit possible.
 *          Returns the best block in the freelist.
 *
 * mm_malloc() allocates a new memory with a pointer to the newly allocated memory.
 *
 * mm_free() looks for the block which was allocated and whether it resides within the heap.
 *           It frees the memory and puts the freed block to the free list.
 *
 * mm_realloc() looks for the block which was dynamically allocated and reallocates it.
 *              The block should reside within the heap.
 *
 * Analysis done :
 *
 * 1. Implemented Best fit and First fit strategies
 * 2. Safe guards are added inorder to make sure the edge cases
 * 3. We have implemented the free and realloc to pass pointers, we have added capability for every block to point to the previous and next nodes. Therefore if a pointer is
 * passed then we do not need to do a linear search rater, adjusting the previous and next pointers would be sufficient.
 */

#include <stdio.h>
#include <unistd.h>
#include <stdbool.h>
#include <stddef.h>
#include <errno.h>
#include <string.h>
#include "memlib.h"
#include "mm_heap.h"

typedef union HeadFoot {
    struct {
        union HeadFoot * previous_free;     //Pointer to the previous allocated or free block.
        union HeadFoot * next_free;         //Pointer to the next allocated or free block.
        size_t size_of_blk: 4 * sizeof(size_t) - 1; // Size of each block.
        size_t alloc_or_not : 1;            //Value which indicates whether the block has been allocated or not.
    } k;
} HeadFoot;
static const size_t blocks = 4;  // header + footer + prevptr + nextptr
static HeadFoot * freelist = NULL;
static void restart();

/**
 * Initialize the dynamic memory.
 */

void mm_init() {
    if (freelist == NULL) {
        mem_init();
        restart();
    }
}

/**
 * Reset the dynamic memory.
 */

void mm_reset() {
    if (freelist == NULL) {
        mm_init();
    } else {
        mem_reset_brk();
        restart();
    }
}

/**
 * De-initialize the dynamic memory.
 */

void mm_deinit() {
    mem_deinit();
    freelist = NULL;
}

/**
 * Reinitialize the free list.
 * Restart the heap structure with all the initial values set.
 */

static void restart() {
    
    if (mem_sbrk((blocks + 1) * sizeof(HeadFoot)) == NULL) {
        return;
    }
    freelist = mem_heap_lo();
    freelist[blocks-1].k.size_of_blk = blocks;      //Fixing the size of blocks.
    freelist->k.size_of_blk = blocks;
    size_t num = 1;
    freelist[blocks-1].k.alloc_or_not = num;        //Marking blocks as allocated.
    freelist->k.alloc_or_not = num;
    freelist->k.next_free = freelist;
    freelist->k.previous_free = freelist;
    HeadFoot *lastblck = freelist + blocks;
    lastblck->k.alloc_or_not = 1;                 //Marking last block as allocated.
    lastblck->k.size_of_blk = 1;
}


/**
 * Take free block from the freelist.
 * @param head The pointer which corresponds to the block.
 */

static void takefromlist(HeadFoot *head) {
    
    HeadFoot *after = head->k.next_free;         //Fixing the pointer after the block which is to be removed.
    HeadFoot *before = head->k.previous_free;        //Fixing the pointer before the block which is to be removed.
    before->k.next_free = after;                 //Pointing the previous block after the removed block.
    after->k.previous_free = before;                 //Pointing the next block to the block before the removed block.
}


/**
 * Convert the specified header sized chunks to bytes.
 * @param headchunk The size to be converted in header chunks.
 * @return Returns the equivalent size in bytes.
 */

static size_t conv_bytes(size_t headchunk) {
    size_t bc = headchunk * sizeof(HeadFoot);
    return bc;
}


/**
 * Put the block back into the free list.
 * Two cases:
 * 1)Combine with lower adjacent block->Check if previous block is in freelist &
 * Make the block into one bigger block.
 * 2)Combine with upper adjacent block->Check if next part of memory is in freelist &
 * Make the block into one bigger block.
 * @param blockval The blocks which are allocated and needs to be freed.
 */

static void returnfreeblocktolist(HeadFoot *blockval) {
    
    size_t headch = blockval->k.size_of_blk;
    blockval[headch-1].k.alloc_or_not = 0;          //Marking  blocks as free
    blockval->k.alloc_or_not = 0;                 //Marking the first block as free
    if (blockval[-1].k.alloc_or_not == 0) {             //Check if the block is not allocated
        blockval = blockval - blockval[-1].k.size_of_blk;
        headch = headch + blockval->k.size_of_blk;
        blockval[headch-1].k.size_of_blk = headch;
        blockval->k.size_of_blk = headch;
    } else  {
        HeadFoot *after = freelist->k.next_free;
        blockval->k.previous_free = freelist;
        blockval->k.next_free = after;          //Place the block after the specified block.
        after->k.previous_free = blockval;
        freelist->k.next_free = blockval;
    }
    freelist = blockval;
    if (blockval[headch].k.alloc_or_not == 0) {
        takefromlist(blockval+headch);          //Place the block with the upper blocks.
        headch = headch + blockval[headch].k.size_of_blk;
        blockval[headch-1].k.size_of_blk = headch;
        blockval->k.size_of_blk = headch;
    }
}


/**
 * Convert the specified bytes to header sized chunks.
 * @param bytechunks The size to be converted in bytes.
 * @return Returns header sized chunks.
 */

static size_t headchunksize(size_t bytechunks) {
    size_t hc = (bytechunks + sizeof(HeadFoot) - 1);
    hc = hc / sizeof(HeadFoot);
    return hc;
}

/**
 * Increase heap size to include more free blocks.
 * @param heads The number of excess header sized units to be added.
 * @return Returns the extended storage pointer.
 */

static HeadFoot *increaseheapsize(size_t heads) {
    
    size_t allocations = headchunksize((size_t) sysconf(_SC_PAGESIZE));
    if (heads < allocations) {
        heads = allocations;
    }
    size_t bytecounts = conv_bytes(heads);
    void *incr = (void *) mem_sbrk(bytecounts);
    if (incr == (void *) -1) {          //cannot increase space
        return NULL;
    }
    HeadFoot *blck = (HeadFoot*) incr - 1;
    blck[heads-1].k.size_of_blk = heads;
    blck->k.size_of_blk = heads;        //adjust the size of the block to the new size.
    blck[heads-1].k.alloc_or_not = 0;   //Mark blocks free.
    blck->k.alloc_or_not = 0;
    blck[heads].k.alloc_or_not = 1;     //Mark last block as allocated.
    blck[heads].k.size_of_blk = 1;      //Size of the last block
    returnfreeblocktolist(blck);        //put the included storage to the list of free blocks.
    return freelist;                    //return the new free list.
}


/**
 * Find a free block from the free list using the first fit algorithm.
 * @param headc The number of header chunks required.
 * @return a pointer which points to the start of the free blocks.
 */
static HeadFoot *pick_free_block_from_list_first_fit(size_t headc) {
    HeadFoot *blck = freelist;
    while (true) {
        if (( headc <= blck->k.size_of_blk) && (blck->k.alloc_or_not == 0)) {
            if (headc + blocks > blck->k.size_of_blk) {
                if ( blck == freelist) {
                    freelist = blck->k.previous_free;
                    
                }
                takefromlist(blck);         //Get the first fit block from the free list
                size_t alc = blck->k.size_of_blk;
                size_t  val = 1;
                blck[alc-1].k.alloc_or_not = val;       //Mark block as allocated.
                blck->k.alloc_or_not = val;
            }
            else {                               //Fragmentation.
                // We divide the blocks into two blocks.
                // First block stays in the free list.
                // Second block is allocated to the user.
                size_t alc = blck->k.size_of_blk - headc;
                blck->k.size_of_blk = blck->k.size_of_blk - headc;
                blck[alc-1].k.size_of_blk = blck->k.size_of_blk;
                blck[alc+headc-1].k.size_of_blk = headc;
                blck[alc].k.size_of_blk = headc;
                size_t  val = 1;
                blck[alc+headc-1].k.alloc_or_not = val;
                blck[alc].k.alloc_or_not = val;
                blck = blck + alc;
            }
            return blck;
        }
        blck = blck->k.next_free;
        if (blck == freelist) {
            blck = increaseheapsize(headc);   //Increase storage since we cannot find a block which is big enough.
            if (blck == NULL) {
                return NULL;
            }
        }
    }
}

/**
 * Find a free block from the free list using the best fit algorithm.
 * @param headc The number of header chunks required.
 * @return a pointer which points to the start of the free blocks.
 */
static HeadFoot *pick_free_block_from_list_best_fit(size_t headc) {
    int count = 0;
    HeadFoot *temp = freelist;
    HeadFoot *best_fit = freelist;
    HeadFoot *val = freelist;
    //Finds the best fit block by traversing through the free list.
    while(true) {
        if (freelist != NULL) {
            do {
                if ((headc <= temp->k.size_of_blk)
                    && (temp->k.alloc_or_not == 0)
                    && (temp->k.size_of_blk < best_fit->k.size_of_blk)) {
                    best_fit = temp;
                }
                temp = temp->k.next_free;
                count++;
            } while (temp != freelist);
        }
        if (best_fit == val) {
            if (temp == NULL) {
                return NULL;
            }
            break;
        } else {
            break;
        }
    }
    HeadFoot *blck = best_fit;
    while (true) {
        if (( headc <= blck->k.size_of_blk) && (blck->k.alloc_or_not == 0)) {
            if (headc + blocks > blck->k.size_of_blk) {
                if ( blck == freelist) {
                    freelist = blck->k.previous_free;
                    
                }
                takefromlist(blck);
                size_t alc = blck->k.size_of_blk;
                size_t  val1 = 1;
                blck[alc-1].k.alloc_or_not = val1;       //Mark block as allocated.
                blck->k.alloc_or_not = val1;
            }
            else {                               //Fragmentation.
                // We divide the blocks into two blocks.
                // First block stays in the free list.
                // Second block is allocated to the user.
                size_t alc = blck->k.size_of_blk - headc;
                blck->k.size_of_blk = blck->k.size_of_blk - headc;
                blck[alc-1].k.size_of_blk = blck->k.size_of_blk;
                blck[alc+headc-1].k.size_of_blk = headc;
                blck[alc].k.size_of_blk = headc;
                size_t  val1 = 1;
                blck[alc+headc-1].k.alloc_or_not = val1;
                blck[alc].k.alloc_or_not = val1;
                blck = blck + alc;
            }
            return blck;
        }
        blck = blck->k.next_free;
        if (blck == freelist) {
            blck = increaseheapsize(headc);   //Increase storage since we cannot find a block which is big enough.
            if (blck == NULL) {
                return NULL;
            }
        }
    }
}

/**
 * Allocates the specified size and returns a pointer to the allocated storage
 * if storage cannot be allocated sets errno and returns null.
 * @param bytechunks The total amount of bytes which we need to allocate to our storage.
 * @return Returns a pointer to the allocated memory if storage was available or returns null if allocation was not possible.
 */

void *mm_malloc(size_t bytechunks) {
    if (freelist == NULL) {         //Initialize if not already initialized.
        mm_init();
    }
    size_t chunks = headchunksize(bytechunks);
    chunks = chunks + 2;   //Header & Footer is always added.
    if (blocks > chunks) {
        chunks = blocks;
    }
    HeadFoot *headptr = pick_free_block_from_list_first_fit(chunks);  //Get a block based on first fit algorithm.
   //  HeadFoot *headptr = pick_free_block_from_list_best_fit(chunks); //Get a block based on best fit algorithm.
    if (headptr == NULL) {
        errno = ENOMEM;
        return NULL;
    }
    return headptr + 1;         //pointer to the allocated memory.
}


/**
 * Find the required block if it was allocated.
 * @param allocated The allocated block pointer.
 * @return if pointer does not reside within allocated block returns null or returns the pointer to allocated block.
 */

static HeadFoot *allocatedblock(void *allocated) {
    if (allocated <= mem_heap_lo() || allocated >= mem_heap_hi() || allocated == NULL) {        //If the pointer is not within bounds or invalid.
        return NULL;
    }
    HeadFoot *blck_list;
    if((uintptr_t)allocated & (sizeof(max_align_t)-1) == 0)  {
        blck_list = (HeadFoot*)allocated-1;
        if (blck_list->k.alloc_or_not == 1) {     //Check if the block is allocated.
            size_t headvals = blck_list->k.size_of_blk;
            if (blocks <= headvals) {
                if (   (blck_list->k.size_of_blk == blck_list[headvals-1].k.size_of_blk)
                    || (blck_list->k.alloc_or_not == blck_list[headvals-1].k.alloc_or_not)) {
                    return blck_list;
                }
            }
        }
    }
    blck_list = mem_heap_lo();
    for (HeadFoot *proceed = blck_list + blck_list->k.size_of_blk; (void *)proceed <= allocated; proceed = proceed + blck_list->k.size_of_blk) {
        blck_list = proceed;   //move the block pointer until the required position is reached.
    }
    
    if(blck_list->k.alloc_or_not == 1) {
        return blck_list; //returns the block which was allocated.
    }
    else {
        return NULL;
    }
}


/**
 * Reallocates the size of the memory which was already dynamically
 * allocated.Returns the pointer to the newly allocated storage or null if not possible.
 * @param allocatedptr The present storage which was allocated.
 * @param bytechunks The storage size which needs to be resized to this specified size.
 * @return
 */

void *mm_realloc(void *allocatedptr, size_t bytechunks) {
    if (allocatedptr == NULL) {      //If not already allocated.
        return mm_malloc(bytechunks);
    }
    HeadFoot *blockv = allocatedblock(allocatedptr);  //Get the allocated block which is to be reallocated.
    if (blockv == NULL) {            //If the required block is not available set errno.
        errno = EFAULT;
        return NULL;
    }
    size_t hchunks = headchunksize(bytechunks);
    hchunks = hchunks + 2;
    size_t insize = blockv->k.size_of_blk;
    if (insize >= hchunks) {
        return allocatedptr;
    }
    HeadFoot *reblockptr = pick_free_block_from_list_first_fit(hchunks);  //Get a block based on first fit algorithm.
    // HeadFoot *reblockptr = pick_free_block_from_list_best_fit(hchunks);     //Get a block based on best fit algorithm.
    if (reblockptr == NULL) {
        return NULL;
    }
    size_t copysize = insize - 2;
    void *newloc =reblockptr + 1;  //The new payload is received.
    size_t copybytes = conv_bytes(copysize); //Convert the header chunks to corresponding bytes.
    memcpy(newloc, allocatedptr, copybytes); //copy to the new location.
    returnfreeblocktolist(blockv); //return the old allocated storage to the free list.
    return newloc;                 //return the new storage location.
}


/**
 * Frees the memory which the alloc pointer points to.
 * If memory was already freed it is an error and sets errno.
 * @param alloc The storage which was allocated to be freed.
 */

void mm_free(void *alloc) {
    if (alloc != NULL) {
        HeadFoot *heaf = allocatedblock(alloc);  //Get the allocated block which is to be freed.
        if (heaf == NULL) {             //If the required block is not available set errno.
            errno = EFAULT;
        } else {            //return the allocated block to the list of free blocks.
            returnfreeblocktolist(heaf);
        }
    }
}
