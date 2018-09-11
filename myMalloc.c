#include <errno.h>
#include <pthread.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "myMalloc.h"
#include "printing.h"

/* Due to the way assert() prints error messges we use out own assert function
 * for deteminism when testing assertions
 */
#ifdef TEST_ASSERT
  inline static void assert(int e) {
    if (!e) {
      const char * msg = "Assertion Failed!\n";
      write(2, msg, strlen(msg));
      exit(1);
    }
  }
#else
  #include <assert.h>
#endif

/*
 * Mutex to ensure thread safety for the freelist
 */
static pthread_mutex_t mutex;

/*
 * Array of sentinel nodes for the freelists
 */
header freelistSentinels[N_LISTS];

/*
 * Pointer to the second fencepost in the most recently allocated chunk from
 * the OS. Used for coalescing chunks
 */
header * lastFencePost;

/*
 * Pointer to maintian the base of the heap to allow printing based on the
 * distance from the base of the heap
 */ 
void * base;

/*
 * List of chunks allocated by  the OS for printing boundary tags
 */
header * osChunkList [MAX_OS_CHUNKS];
size_t numOsChunks = 0;

/*
 * direct the compiler to run the init function before running main
 * this allows initialization of required globals
 */
static void init (void) __attribute__ ((constructor));

// Helper functions for manipulating pointers to headers
static inline header * get_header_from_offset(void * ptr, ptrdiff_t off);
static inline header * get_left_header(header * h);
static inline header * ptr_to_header(void * p);

// Helper functions for allocating more memory from the OS
static inline void initialize_fencepost(header * fp, size_t left_size);
static inline void insert_os_chunk(header * hdr);
static inline void insert_fenceposts(void * raw_mem, size_t size);
static header * allocate_chunk(size_t size);

// Helper functions for freeing a block
static inline void deallocate_object(void * p);

// Helper functions for allocating a block
static inline header * allocate_object(size_t raw_size);

// Helper functions for verifying that the data structures are structurally 
// valid
static inline header * detect_cycles();
static inline header * verify_pointers();
static inline bool verify_freelist();
static inline header * verify_chunk(header * chunk);
static inline bool verify_tags();

static void init();

static bool isMallocInitialized;

/**
 * @brief Helper function to retrieve a header pointer from a pointer and an 
 *        offset
 *
 * @param ptr base pointer
 * @param off number of bytes from base pointer where header is located
 *
 * @return a pointer to a header offset bytes from pointer
 */
static inline header * get_header_from_offset(void * ptr, ptrdiff_t off) {
	return (header *)((char *) ptr + off);
}

/**
 * @brief Helper function to get the header to the right of a given header
 *
 * @param h original header
 *
 * @return header to the right of h
 */
header * get_right_header(header * h) {
	return get_header_from_offset(h, get_size(h));
}

/**
 * @brief Helper function to get the header to the left of a given header
 *
 * @param h original header
 *
 * @return header to the right of h
 */
inline static header * get_left_header(header * h) {
  return get_header_from_offset(h, -h->left_size);
}

/**
 * @brief Fenceposts are marked as always allocated and may need to have
 * a left object size to ensure coalescing happens properly
 *
 * @param fp a pointer to the header being used as a fencepost
 * @param left_size the size of the object to the left of the fencepost
 */
inline static void initialize_fencepost(header * fp, size_t left_size) {
	set_state(fp,FENCEPOST);
	set_size(fp, ALLOC_HEADER_SIZE);
	fp->left_size = left_size;
}

/**
 * @brief Helper function to maintain list of chunks from the OS for debugging
 *
 * @param hdr the first fencepost in the chunk allocated by the OS
 */
inline static void insert_os_chunk(header * hdr) {
  if (numOsChunks < MAX_OS_CHUNKS) {
    osChunkList[numOsChunks++] = hdr;
  }
}

/**
 * @brief given a chunk of memory insert fenceposts at the left and 
 * right boundaries of the block to prevent coalescing outside of the
 * block
 *
 * @param raw_mem a void pointer to the memory chunk to initialize
 * @param size the size of the allocated chunk
 */
inline static void insert_fenceposts(void * raw_mem, size_t size) {
  // Convert to char * before performing operations
  char * mem = (char *) raw_mem;

  // Insert a fencepost at the left edge of the block
  header * leftFencePost = (header *) mem;
  initialize_fencepost(leftFencePost, ALLOC_HEADER_SIZE);

  // Insert a fencepost at the right edge of the block
  header * rightFencePost = get_header_from_offset(mem, size - ALLOC_HEADER_SIZE);
  initialize_fencepost(rightFencePost, size - 2 * ALLOC_HEADER_SIZE);
}

/**
 * @brief Allocate another chunk from the OS and prepare to insert it
 * into the free list
 *
 * @param size The size to allocate from the OS
 *
 * @return A pointer to the allocable block in the chunk (just after the 
 * first fencpost)
 */
static header * allocate_chunk(size_t size) {
  void * mem = sbrk(size);
  
  insert_fenceposts(mem, size);
  header * hdr = (header *) ((char *)mem + ALLOC_HEADER_SIZE);
  set_state(hdr, UNALLOCATED);
  set_size(hdr, size - 2 * ALLOC_HEADER_SIZE);
  hdr->left_size = ALLOC_HEADER_SIZE;
  return hdr;
}

/**
 * @brief Helper allocate an object given a raw request size from the user
 *
 * @param raw_size number of bytes the user needs
 *
 * @return A block satisfying the user's request
 */
static inline header * allocate_object(size_t raw_size) {
  	// TODO implement allocation
	if(raw_size == 0)return NULL;
 	size_t request_size = ALLOC_HEADER_SIZE + raw_size;
	if(request_size % MIN_ALLOCATION != 0)request_size = request_size + MIN_ALLOCATION - (request_size % MIN_ALLOCATION);
	if(request_size < sizeof(header)){
		request_size = sizeof(header);
	}
	
	int fl_pos = ((request_size-ALLOC_HEADER_SIZE - 1)/MIN_ALLOCATION);	
	if(fl_pos > 58) fl_pos = N_LISTS - 1;
	header * hdr = freelistSentinels[fl_pos].next;
	
	while(fl_pos < 58){
		if(hdr->next == hdr){
			fl_pos++;
			hdr = freelistSentinels[fl_pos].next;
		}
		else{
			//when block size is less greater than request size
			if((get_size(hdr) -request_size) < sizeof(header)){
				hdr->next->prev = hdr->prev;
				hdr->prev->next = hdr->next;
				set_state(hdr, 1);
				return get_header_from_offset(hdr, ALLOC_HEADER_SIZE);
			}
			//block size is greater than request size
			if(request_size < get_size(hdr)){
				size_t right_size = request_size;
				size_t left_size = get_size(hdr) - right_size;
				header * right_hdr = get_header_from_offset(hdr, left_size);
				set_size(hdr, left_size);
				set_size(right_hdr, right_size);
				set_state(right_hdr, 1);
				right_hdr->left_size = left_size;
				header * right_neibr = get_header_from_offset(right_hdr, right_size);
				right_neibr->left_size = right_size; 
				hdr->next->prev = hdr->prev;
				hdr->prev->next = hdr->next;
				int npos = ((get_size(hdr)-ALLOC_HEADER_SIZE-1)/MIN_ALLOCATION);
				header * nfl = &freelistSentinels[npos];
				hdr->next = nfl->next;
				hdr->prev = nfl;
				hdr->next->prev = hdr;
				hdr->prev->next = hdr;
				
				return get_header_from_offset(right_hdr, ALLOC_HEADER_SIZE);	
			}
		}			
		 
	}
	//insert to the last list
	header * list_check = &freelistSentinels[58];
	while(fl_pos == 58){
		//adding additional chunks
		if(hdr == list_check){
			header * new_chunk = allocate_chunk(ARENA_SIZE);
			//new chunk is adj to last chunk 
			if(((char *) new_chunk - (char *) lastFencePost) == 2 * ALLOC_HEADER_SIZE){
				header * l_hdr = get_left_header(lastFencePost);
				//previous chunk has empty blocks
				if(get_state(l_hdr) == 0){
					lastFencePost = get_header_from_offset(new_chunk, get_size(new_chunk));
					int npos = ((get_size(l_hdr)-ALLOC_HEADER_SIZE)/MIN_ALLOCATION) - 1;
					set_size(l_hdr, (get_size(new_chunk) + get_size(l_hdr) + 2 * ALLOC_HEADER_SIZE));
					header * r_neibr = get_right_header(new_chunk);
					r_neibr->left_size = get_size(l_hdr);
					if(npos < 58){
						l_hdr->next->prev = l_hdr->prev;
						l_hdr->prev->next = l_hdr->next;
						header * nfl = &freelistSentinels[58];
						l_hdr->next = nfl->next;
						l_hdr->prev = nfl;
						l_hdr->next->prev = l_hdr;
						l_hdr->prev->next = l_hdr;
					}
				}
				//previous chunk has no empty blocks
				else{
					lastFencePost = get_header_from_offset(new_chunk, get_size(new_chunk));
					header * new_hdr = get_header_from_offset(new_chunk, -2*ALLOC_HEADER_SIZE);
					new_hdr->left_size = get_size(l_hdr);
					set_state(new_hdr, 0);
					set_size(new_hdr, ARENA_SIZE);
					header * nfl = &freelistSentinels[58];
					new_hdr->next = nfl->next;
					new_hdr->prev = nfl;
					new_hdr->next->prev = new_hdr;
					new_hdr->prev->next = new_hdr;
					
				}
			}
			//not adj directly insert to freelist
			else {
				lastFencePost = get_header_from_offset(new_chunk, get_size(new_chunk));
				header * prevFencePost = get_header_from_offset(new_chunk, -ALLOC_HEADER_SIZE);
  				insert_os_chunk(prevFencePost);
				header * nfl = &freelistSentinels[58];
				new_chunk->next = nfl->next;
				new_chunk->prev = nfl;
				new_chunk->next->prev = new_chunk;
				new_chunk->prev->next = new_chunk;
			}
			hdr = hdr->next;
			//lastFencePost = get_header_from_offset(new_chunk, get_size(new_chunk));
		}
		//directly malloc
		if(get_size(hdr) - request_size < sizeof(header)){
			hdr->next->prev = hdr->prev;
			hdr->prev->next = hdr->next;
			set_state(hdr, 1);
			return get_header_from_offset(hdr, ALLOC_HEADER_SIZE);
		}
		//split then malloc
		
		
		if(request_size < get_size(hdr)){
		 	size_t right_size = request_size;
			size_t left_size = get_size(hdr) - right_size;
			header * right_hdr = get_header_from_offset(hdr, left_size);
			set_size(hdr, left_size);
			set_size(right_hdr, right_size);
			set_state(right_hdr, 1);
			right_hdr->left_size = left_size;
			header * neibr_block = get_header_from_offset(right_hdr, right_size);
			neibr_block->left_size = right_size; 
			if(((left_size - 1 - ALLOC_HEADER_SIZE) / MIN_ALLOCATION)  < 59){
				hdr->next->prev = hdr->prev;
				hdr->prev->next = hdr->next;
				int npos = ((get_size(hdr)-ALLOC_HEADER_SIZE - 1)/MIN_ALLOCATION);
				
				header * nfl = &freelistSentinels[npos];
				hdr->next = nfl->next;
				hdr->prev = nfl;
				hdr->next->prev = hdr;
				hdr->prev->next = hdr;
			}
			return get_header_from_offset(right_hdr, ALLOC_HEADER_SIZE);
		}
		hdr = hdr->next;		
	}
	
	
 	//(void) raw_size;
  	//assert(false);
  	//exit(1);
}

/**
 * @brief Helper to get the header from a pointer allocated with malloc
 *
 * @param p pointer to the data region of the block
 *
 * @return A pointer to the header of the block
 */
static inline header * ptr_to_header(void * p) {
  return (header *)((char *) p - ALLOC_HEADER_SIZE); //sizeof(header));
}

/**
 * @brief Helper to manage deallocation of a pointer returned by the user
 *
 * @param p The pointer returned to the user by a call to malloc
 */
static inline void deallocate_object(void * p) {
  	// TODO implement deallocation
	if(p == NULL) return;
	header * hdr = ptr_to_header(p);
	if(get_state(hdr) == 0){
		printf("Double Free Detected\n");
		//printf("Assertion Failed!\n");
		assert(false);
	}
	header * r_hdr = get_right_header(hdr);
	header * l_hdr = get_left_header(hdr);
	header * coal_block;
	size_t hdr_size;
	//no coal
	if((get_state(r_hdr) == 1 || get_state(r_hdr) == 2) && (get_state(l_hdr) == 1 || get_state(l_hdr) == 2)){
		int npos = ((get_size(hdr)-ALLOC_HEADER_SIZE - 1)/MIN_ALLOCATION);
		if(npos >= 58) npos = 58;
		header * nfl = &freelistSentinels[npos];
		set_state(hdr, 0);
		hdr->next = nfl->next;
		hdr->prev = nfl;
		hdr->next->prev = hdr;
		hdr->prev->next = hdr;
		
		
		
		
		return;
	}
	//coal right
	if(get_state(r_hdr) == 0  && (get_state(l_hdr) == 1 || get_state(l_hdr) == 2)){
		set_size(hdr, (get_size(hdr) + get_size(r_hdr)));
		header * r_neibr = get_header_from_offset(r_hdr, get_size(r_hdr));
		r_neibr->left_size = get_size(hdr);
		set_state(hdr, 0);
		int npos = ((get_size(hdr)-ALLOC_HEADER_SIZE - 1)/MIN_ALLOCATION);
		int rpos = ((get_size(r_hdr)-ALLOC_HEADER_SIZE - 1)/MIN_ALLOCATION);
		if(npos >= 58) npos = 58;	
		if(rpos < 58){	
			r_hdr->next->prev = r_hdr->prev;
			r_hdr->prev->next = r_hdr->next;
			header * nfl = &freelistSentinels[npos];
			hdr->next = nfl->next;
			hdr->prev = nfl;
			hdr->next->prev = hdr;
			hdr->prev->next = hdr;
			return;
		} 
		if(rpos >= 58){
			r_hdr->prev->next = hdr;
			r_hdr->next->prev = hdr;
			hdr->prev = r_hdr->prev;
			hdr->next = r_hdr->next;
			return;
		}	
	}
	//coal left
	else if((get_state(r_hdr) == 1 || get_state(r_hdr) == 2)&& get_state(l_hdr) == 0){
		size_t hdr_size = get_size(l_hdr);
		set_state(hdr, 0);
		set_size(l_hdr, (get_size(hdr) + get_size(l_hdr)));
		r_hdr->left_size = get_size(l_hdr);
		coal_block = l_hdr;
	}
	//coal both
	else if(get_state(r_hdr) == 0 && get_state(l_hdr) == 0){
		size_t hdr_size = get_size(l_hdr);
		set_state(hdr, 0);
		r_hdr->next->prev = r_hdr->prev;
		r_hdr->prev->next = r_hdr->next;
		set_size(l_hdr, (get_size(hdr) + get_size(r_hdr) + get_size(l_hdr)));
		header * r_neibr = get_header_from_offset(r_hdr, get_size(r_hdr));
		r_neibr->left_size = get_size(l_hdr);
		coal_block = l_hdr;
	}
	//coal utilize
	int hpos = ((hdr_size-ALLOC_HEADER_SIZE - 1)/MIN_ALLOCATION);
	int npos = ((get_size(coal_block)-ALLOC_HEADER_SIZE - 1)/MIN_ALLOCATION);
	if(npos >= 58) npos = 58;
	if((hpos < 58 && npos >= 58) || npos < 58){
		coal_block->next->prev = coal_block->prev;
		coal_block->prev->next = coal_block->next;
		header * nfl = &freelistSentinels[npos];
		coal_block->next = nfl->next;
		coal_block->prev = nfl;
		coal_block->next->prev = coal_block;
		coal_block->prev->next = coal_block;
	}
	return;
  	//(void) p;
  	//assert(false);
  	//exit(1);
}

/**
 * @brief Helper to detect cycles in the free list
 * https://en.wikipedia.org/wiki/Cycle_detection#Floyd's_Tortoise_and_Hare
 *
 * @return One of the nodes in the cycle or NULL if no cycle is present
 */
static inline header * detect_cycles() {
  for (int i = 0; i < N_LISTS; i++) {
    header * freelist = &freelistSentinels[i];
    for (header * slow = freelist->next, * fast = freelist->next->next; 
         fast != freelist; 
         slow = slow->next, fast = fast->next->next) {
      if (slow == fast) {
        return slow;
      }
    }
  }
  return NULL;
}

/**
 * @brief Helper to verify that there are no unlinked previous or next pointers
 *        in the free list
 *
 * @return A node whose previous and next pointers are incorrect or NULL if no
 *         such node exists
 */
static inline header * verify_pointers() {
  for (int i = 0; i < N_LISTS; i++) {
    header * freelist = &freelistSentinels[i];
    for (header * cur = freelist->next; cur != freelist; cur = cur->next) {
      if (cur->next->prev != cur || cur->prev->next != cur) {
        return cur;
      }
    }
  }
  return NULL;
}

/**
 * @brief Verify the structure of the free list is correct by checkin for 
 *        cycles and misdirected pointers
 *
 * @return true if the list is valid
 */
static inline bool verify_freelist() {
  header * cycle = detect_cycles();
  if (cycle != NULL) {
    fprintf(stderr, "Cycle Detected\n");
    print_sublist(print_object, cycle->next, cycle);
    return false;
  }

  header * invalid = verify_pointers();
  if (invalid != NULL) {
    fprintf(stderr, "Invalid pointers\n");
    print_object(invalid);
    return false;
  }

  return true;
}

/**
 * @brief Helper to verify that the sizes in a chunk from the OS are correct
 *        and that allocated node's canary values are correct
 *
 * @param chunk AREA_SIZE chunk allocated from the OS
 *
 * @return a pointer to an invalid header or NULL if all header's are valid
 */
static inline header * verify_chunk(header * chunk) {
	if (get_state(chunk) != FENCEPOST) {
		fprintf(stderr, "Invalid fencepost\n");
		print_object(chunk);
		return chunk;
	}
	
	for (; get_state(chunk) != FENCEPOST; chunk = get_right_header(chunk)) {
		if (get_size(chunk)  != get_right_header(chunk)->left_size) {
			fprintf(stderr, "Invalid sizes\n");
			print_object(chunk);
			return chunk;
		}
	}
	
	return NULL;
}

/**
 * @brief For each chunk allocated by the OS verify that the boundary tags
 *        are consistent
 *
 * @return true if the boundary tags are valid
 */
static inline bool verify_tags() {
  for (size_t i = 0; i < numOsChunks; i++) {
    header * invalid = verify_chunk(osChunkList[i]);
    if (invalid != NULL) {
      return invalid;
    }
  }

  return NULL;
}

/**
 * @brief Initialize mutex lock and prepare an initial chunk of memory for allocation
 */
static void init() {
  // Initialize mutex for thread safety
  pthread_mutex_init(&mutex, NULL);

#ifdef DEBUG
  // Manually set printf buffer so it won't call malloc when debugging the allocator
  setvbuf(stdout, NULL, _IONBF, 0);
#endif // DEBUG

  // Allocate the first chunk from the OS
  header * block = allocate_chunk(ARENA_SIZE);

  header * prevFencePost = get_header_from_offset(block, -ALLOC_HEADER_SIZE);
  insert_os_chunk(prevFencePost);

  lastFencePost = get_header_from_offset(block, get_size(block));

  // Set the base pointer to the beginning of the first fencepost in the first
  // chunk from the OS
  base = ((char *) block) - ALLOC_HEADER_SIZE; //sizeof(header);

  // Initialize freelist sentinels
  for (int i = 0; i < N_LISTS; i++) {
    header * freelist = &freelistSentinels[i];
    freelist->next = freelist;
    freelist->prev = freelist;
  }

  // Insert first chunk into the free list
  header * freelist = &freelistSentinels[N_LISTS - 1];
  freelist->next = block;
  freelist->prev = block;
  block->next = freelist;
  block->prev = freelist;
}

/* 
 * External interface
 */
void * my_malloc(size_t size) {
  pthread_mutex_lock(&mutex);
  header * hdr = allocate_object(size); 
  pthread_mutex_unlock(&mutex);
  return hdr;
}

void * my_calloc(size_t nmemb, size_t size) {
  return memset(my_malloc(size * nmemb), 0, size * nmemb);
}

void * my_realloc(void * ptr, size_t size) {
  void * mem = my_malloc(size);
  memcpy(mem, ptr, size);
  my_free(ptr);
  return mem; 
}

void my_free(void * p) {
  pthread_mutex_lock(&mutex);
  deallocate_object(p);
  pthread_mutex_unlock(&mutex);
}

bool verify() {
  return verify_freelist() && verify_tags();
}
