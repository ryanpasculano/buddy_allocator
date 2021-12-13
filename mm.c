/*
 * mm.c
 *
 * Name: Ryan Pasculano
 *
 * For this project I tried to implement a buddy allocator. Due to the limitation of global memory
 * I use the first 64 words of memory to store the base pointer to each chuck of a given size
 * in memory. This is indexed by the log base 2 (or power) size of the block of memory. For example
 * the list of blocks of size 1024 are located at index 10 because 2**10 = 1024. When a block is 
 * allocated the first 16 bytes are used for metadata. The only metadata needed is the size of the 
 * block as a power of 2. This value is used to free the memory and find buddy blocks. 
 *
 */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <stdbool.h>
#include <stdint.h>

#include "mm.h"
#include "memlib.h"

/*
 * If you want to enable your debugging output and heap checker code,
 * uncomment the following line. Be sure not to have debugging enabled
 * in your final submission.
 */
//#define DEBUG

#ifdef DEBUG
/* When debugging is enabled, the underlying functions get called */
#define dbg_printf(...) printf(__VA_ARGS__)
#define dbg_assert(...) assert(__VA_ARGS__)
#else
/* When debugging is disabled, no code gets generated */
#define dbg_printf(...)
#define dbg_assert(...)
#endif /* DEBUG */


/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#define memset mem_memset
#define memcpy mem_memcpy
#endif /* DRIVER */

/* What is the correct alignment? */
#define ALIGNMENT 16

/* pointer to block list */ 
static unsigned long * start; // start of area used for allocation 
static unsigned long * base;  // base of alocated area
static unsigned long * end;   // end of area used for allocation

/* Constants */
#define WSIZE 8
#define DSIZE 16
#define DSIZE_POWER 4
#define CHUNKSIZE_POWER 17
#define MAX_POWER 64 // Silly large but makes even sizing
#define MIN_POWER 5
/* Helper functions */

void put(char* location, int data);
unsigned int pack(unsigned int num1, unsigned int num2);
unsigned int get_valid(unsigned int data);
unsigned int get_data(unsigned int data);
char* get_next(char * current);
char* get_prev(char * current);
void set_next(char * current, unsigned int next);
void set_prev(char * current, unsigned int prev);
unsigned int min(unsigned int a, unsigned int b);
unsigned long get_size(unsigned long requested_size);
unsigned long get_power(unsigned long num);
bool isFree(unsigned long* ptr, unsigned long power);
unsigned long* get_buddy(unsigned long* ptr, unsigned long size);
void removeFromList(unsigned long* ptr, unsigned long power);
unsigned long expand_memory();


/* rounds up to the nearest multiple of ALIGNMENT */
static size_t align(size_t x)
{
    return ALIGNMENT * ((x+ALIGNMENT-1)/ALIGNMENT);
}

/*
 * Initialize: returns false on error, true on success.
 */
bool mm_init(void)
{
    // establish size of chunk to allocate
    unsigned long chunksize = 1<<CHUNKSIZE_POWER;
    
    // Create the initial empty heap
    if ((base = mem_sbrk(chunksize)) == (void *)-1)
        return false;

    // calculate start point after metadata
    start = base + MAX_POWER;

    //set end pointer
    end = mem_heap_hi();   
    
    // temprary pointer for allocating each chunk
    unsigned long* ptr = (unsigned long*)(((unsigned char*)base) + (chunksize/2));

    // set metadata region to all zero
    memset((void *) base, 0, MAX_POWER*WSIZE);

    // iterate through each chunk size
    // because we need to use part of memory for the pointers we cannot just allocate the whole 
    // chunk as a single block
    for (int power = CHUNKSIZE_POWER - 2; power >= MIN_POWER && ptr > start; power--){

        #ifdef DEBUG
        printf("Inserting block of size %d at location %p, memory at location %p\n", 1<<power, base+power, ptr);    
        #endif /* DEBUG */
        
        // save pointer to index
        *(base + power) = (unsigned long)ptr;
    
        // save value of zero to location of pointer
        *ptr = (unsigned long)0;

        // update location of ptr for next loop
        ptr = (unsigned long*) ((unsigned char*)ptr - (1 << (power-1)));
    
    }
    mm_checkheap(__LINE__);

    return true;
}

/*
 * malloc
 */
void* malloc(size_t size)
{
    #ifdef DEBUG
    printf("malloc %ld\n", size);
    #endif /* DEBUG */
        
    // check for malloc if size 0
    if (size == 0)
        return NULL;

    // round up to a power of 2 for the buddy allocator
    unsigned long actual_size = get_size(size);
    
    // get power so we can index lists
    unsigned int power = get_power(actual_size);
    
    // temp pointer to find free block
    unsigned long* ptr =  (base + power);

    // temp varialbe to track size of block pointer by ptr
    unsigned int block_power = power;

    #ifdef DEBUG
    printf("Looking for block with size %lu, power %d\n", actual_size, power);
    #endif /* DEBUG */
          
    // iterate though list until a free block is found
    while(ptr < start && *ptr == 0){

        //move to next size up
        ptr = ptr + 1;

        // increment block power to track size
        block_power++;

    }
    // if no free block found 
    if (ptr >= start){
        // temp holder to detect out of memory error
        #ifdef DEBUG
        printf("Too large of memory chunk\n Adding more memory\n");
        printf("Need space for chunk of power %d\n",  power);
        #endif /* DEBUG */

        //
        unsigned long new_chunk_power = 0;
        while(new_chunk_power < power){
            // expand memory
            new_chunk_power = expand_memory();
            #ifdef DEBUG
            printf("trying expand memory again\n");

            #endif /* DEBUG */    
        }
        //  call malloc now that we have expanded memory and know there is a chunk large enough
        return malloc(size);
            
        
    }

    #ifdef DEBUG
    printf("block found with size %lu, power %d\n", (long unsigned int)1<<block_power, block_power);
    #endif /* DEBUG */

    // We now have a free block that will fit our request
    unsigned long* ret_block = (unsigned long*)*ptr; 

    // Remove this block from the list of free blocks
    *(base+block_power) = *( (unsigned long*) *ptr);
    
    // Split block to mimimize internal fragmentation
    while (block_power > power){

        //decrease block_power size
        block_power--;

        // find midpoint of block
        unsigned long* midpoint = (unsigned long*)((unsigned char*)ret_block + (1<<block_power));
        *midpoint = (unsigned long)0;

        // add second half of block to free  list
        *(base + block_power) = (unsigned long)midpoint;
        // Note: this list must be empty because if it wasn't that  block would have been used instead of 
        // the block that was actually used.

    }

    // save power of block to first word so size in known when free is called
    *ret_block = power;

    #ifdef DEBUG
    printf("Writing power of %d into first section of block\n", power);
    printf("Allocated block located at %p\n", ret_block);
    #endif /* DEBUG */

    mm_checkheap(__LINE__);
    
    //return block shifted by 2 8-byte words (16 bytes) becuase we need alignment on 16 bytes
    return (void*) (ret_block + 2);

}


/*
 * free
 */
void free(void* ptr)
{
    // save block size and power
    unsigned long* ptr_base = ((unsigned long*)ptr)-2;
    unsigned long size = 1 << (*ptr_base);
    unsigned long power = get_power(size);


    /*
    // find buddy
    unsigned long* buddy = get_buddy(ptr_base, size);

    #ifdef DEBUG
    printf("freeing block at location %p\n", ptr_base);
    printf("block size: %lu, power %lu\n", size, power);
    printf("Buddy at %p\n", buddy); 
    #endif 

    // merge buddy blocks until we find a non free block
    while (isFree(buddy, power)){

        #ifdef DEBUG
        printf("buddy is free\n");
        #endif 

        // merge buddy
        removeFromList(buddy, power);

        // set ptr_base to lower of the two buddies
        if (buddy < ptr_base){
            ptr_base = buddy;
        }

        // increase size 
        power++;
        size = 1 << power;

        //find new buddy
        buddy = get_buddy(ptr_base, size);
    }
    */
    //add buddy to list
    
    // set first block of our pointer to the head
    *ptr_base = *(base+power);
    
    // set head to our pointer
    *(base+power) = (unsigned long)ptr_base;
    
    mm_checkheap(__LINE__);   
    return;
}

/*
 * realloc
 */
void* realloc(void* oldptr, size_t size)
{
    #ifdef DEBUG
    printf("Call to realloc");
    printf("Allocated block located at %p\n", oldptr-2);
    #endif /* DEBUG */
    if (oldptr == NULL){
	   return malloc(size);
    } else if (size == 0){
	   free(oldptr);
	   return NULL;
    } else {
        unsigned long * old_base = ((unsigned long*)oldptr)-2;
    	unsigned int copy_size = min(size, 1 << *old_base);
    	void* newptr = malloc(size);
    	memcpy(newptr, oldptr, copy_size);
        free(oldptr);
    	return newptr;
    }
    
}

/*
 * calloc
 * This function is not tested by mdriver, and has been implemented for you.
 */
void* calloc(size_t nmemb, size_t size)
{
    void* ptr;
    size *= nmemb;
    ptr = malloc(size);
    if (ptr) {
        memset(ptr, 0, size);
    }
    return ptr;
}

/*
 * Returns whether the pointer is in the heap.
 * May be useful for debugging.
 */
static bool in_heap(const void* p)
{
    return p <= mem_heap_hi() && p >= mem_heap_lo();
}

/*
 * Returns whether the pointer is aligned.
 * May be useful for debugging.
 */
static bool aligned(const void* p)
{
    size_t ip = (size_t) p;
    return align(ip) == ip;
}

/*
 * mm_checkheap
 */
bool mm_checkheap(int lineno)
{
#ifdef DEBUG
    /* Write code to check heap invariants here */
    // go through heap and print infomation about each section of heap
    // requires nested for loop 
    // outer loop iterates through each block size
    // inner loop iterates through each element of that block size
    printf("lineno %d\n", lineno); 
    for (int power = MIN_POWER; power < MAX_POWER; power++){
        unsigned long size = 1<<power;
        //printf("Block size: %lu\nBlock power %d\n", size, power);
        if (*(base+power) == 0){
            printf("No blocks of power %d in free list\n", power);
    	} else {
    	    //print info about each block
    	    unsigned long* ptr = base+power;
    	    int counter = 1;
    	    printf("Block size: %lu\nBlock power %d\n", size, power);
            while (*ptr != 0){
                // get buddy
                unsigned long* buddy = get_buddy(ptr, size);
                // check that the buddy block is not free
                if(isFree(buddy, size)){
                    printf("Buddy block is free and not merged with its buddy");
                    exit(1);
                }

                printf("\tBlock %d located at: %p\n", counter, ptr);
                ptr = (unsigned long*) *ptr;
                counter++;

    	    }
    	}
    }
    printf("lineno %d\n", lineno);
#endif /* DEBUG */
    return true;
}

/* helper functions that I added */

void put(char* location, int data){
     (*(unsigned int *)(location) = (data));
}

unsigned int pack(unsigned int num1, unsigned int num2){
    return num1 | num2;
}

unsigned int get_valid(unsigned int data){
    return data & 1;
}

unsigned int get_data(unsigned int data){
    return data >> 1 << 1;
}

char* get_next(char * current){
    return current + (2 * WSIZE);
}

char* get_prev(char * current){
    return current + (1 * WSIZE);
}

void set_next(char * current, unsigned int next){
    put(current + (2 * WSIZE), next);
}

void set_prev(char * current, unsigned int prev){
    put (current + (1 * WSIZE), prev);
}

unsigned int min(unsigned int a, unsigned int b){
    if (a < b){ return a;}
    return  b; 
}

unsigned long get_size(unsigned long requested_size){

    unsigned long actual_size = 1<<MIN_POWER; //start with min block size size
    //add 8 for storing size
    while (actual_size < requested_size + 16) {
        // double size each time until bigger than requested size
        actual_size = actual_size * 2;
    }
    return actual_size;

}

unsigned long get_power(unsigned long num){
    unsigned int power = 0;
    while (num > 1){
        num = num >> 1;
        power++;
    }
    return power;
} 


unsigned long* get_buddy(unsigned long* ptr, unsigned long size){
    // calculate offset
    unsigned long offset = (unsigned char*) ptr - (unsigned char*)base;
    // see if ptr is first or second block
    if (offset%(size*2) == 0){
        return (unsigned long*)((unsigned char*)ptr + size);
    } else { 
        return (unsigned long*)((unsigned char*)ptr - size);
    }

}


bool isFree(unsigned long* ptr, unsigned long power){
    #ifdef DEBUG
    printf("Looking for ptr %p with power %ld\n", ptr, power);
    #endif /* DEBUG */
    // set pointer to iterate on
    unsigned long* iterator = base+power;
    
    // iterate though list
    while (base < iterator && iterator < end ){
        #ifdef DEBUG
        printf("looking at ptr %p holding value %lu\n", iterator, *iterator);
        #endif /* DEBUG */
        if (iterator == ptr){
            #ifdef DEBUG
            printf("found buddy\n");
            #endif /* DEBUG */
        
            return true;
        }
        iterator = (unsigned long *)*iterator;
        #ifdef DEBUG
        printf("next look at ptr %p\n", iterator);
        #endif /* DEBUG */
        
    }
    #ifdef DEBUG
    printf("Could not find buddy\n");
    #endif /* DEBUG */
    return false;

}

void removeFromList(unsigned long* ptr, unsigned long power){
    unsigned long* iterator = base+power;
    #ifdef DEBUG
    printf("Looking for block %p in blocks of power %ld\n", ptr, power);
    #endif /* DEBUG */
    // iterate though list
    while (*iterator != 0){
        #ifdef DEBUG
        printf("Looking at block %p\n", iterator);
        #endif /* DEBUG */
        // found object thaat points to desired object
        if ((unsigned long*)*iterator == ptr){
            // skip over desired element
            *iterator = *ptr;
            return;
        }
        iterator = (unsigned long *)*iterator;
    }
    // error not in list
    printf("Error: Desired block is not in list\n");
    exit(1);
 
}

unsigned long expand_memory(){

    unsigned long chunksize = 1<<CHUNKSIZE_POWER;
    /* Create the initial empty heap */
    unsigned long* new_chunk;
    if ((new_chunk = (unsigned long*)mem_sbrk(chunksize)) == (void *)-1){
        return false;
    }

    unsigned long power = CHUNKSIZE_POWER;
    unsigned long size = chunksize;
    // attempt to coalese block
    // find buddy
    unsigned long* buddy = get_buddy(new_chunk, size);
    

    // merge buddy blocks until we find a non free block
    while (isFree(buddy, power)){


        // merge buddy
        #ifdef DEBUG
        printf("removing buddy from list\n");
        #endif /* DEBUG */
        removeFromList(buddy, power);
        #ifdef DEBUG
        printf("grouping buddies\n");
        #endif /* DEBUG */
        // set ptr_base to lower of the two buddies
        if (buddy < new_chunk){
            new_chunk = buddy;
        }

        // increase size 
        power++;
        size = (unsigned long)1 << power;

        //find new buddy
        #ifdef DEBUG
        printf("finding new  buddies with power %lu and size %lu\n", power, size);
        #endif /* DEBUG */
        buddy = get_buddy(new_chunk, size);
    }

    
    // set first block of our pointer to the head
    *new_chunk = *(base+power);
    
    // set head to our pointer
    *(base+power) = (unsigned long)new_chunk;
    
    
    //update end pointer
    end = mem_heap_hi();   
    
    //mm_checkheap(__LINE__);
    #ifdef DEBUG
    printf("Created new block with power %lu\n",  power);
    #endif /* DEBUG */

    return power;


}
