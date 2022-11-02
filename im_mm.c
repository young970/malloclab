/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 * 
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "ateam",
    /* First member's full name */
    "Harry Bovik",
    /* First member's email address */
    "bovik@cs.cmu.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

/* Basic constants and macros */
#define WSIZE 4
#define DSIZE 8
#define CHUNKSIZE (1<<12) 

#define MAX(x, y) ((x) > (y)? (x) : (y))

/* pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p)      (*(unsigned int*)(p))   // 인자 p가 참조하는 워드를 읽어서 리턴
#define PUT(p, val) (*(unsigned int*)(p)) = (val)   // 인자p가 가리키는 워드에 val을 저장한다.

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)   (GET(p) & ~0x7)   // 주소 p에 있는 헤더 또는 푸터의 size를 리턴한다.
#define GET_ALLOC(p)  (GET(p) & 0x1)    // 주소 p에 있는 헤더 또는 푸터의 할당 비트를 리턴한다.

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)      ((char*)(bp) - WSIZE)  // 블록 헤더를 가리키는 포인터를 리턴한다.
#define FTRP(bp)      ((char*)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)   // 블록 푸터를 가리키는 포인터를 리턴한다.

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)   ((char*)(bp) + GET_SIZE(((char*)(bp) - WSIZE)))  // 다음 블록의 블록 포인터를 리턴한다.
#define PREV_BLKP(bp)   ((char*)(bp) - GET_SIZE(((char*)(bp) - DSIZE)))  // 이전 블록의 블록 포인터를 리턴한다.

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

static void* heap_listp;
static char* last_bp;
static void *coalesce(void *bp);
static void *extend_heap(size_t words);
static void* first_fit(size_t asize);
static void* next_fit(size_t asize);
static void* best_fit(size_t asize);
static void place(void* bp, size_t asize);

/* 
 * mm_init - initialize the malloc package.
 */
/* mm_init: 패딩 블록과 프롤로그 블록과 에필로그 블록 생성 후 힙을 확장하여 초기 가용 블록 생성 */
int mm_init(void)
{
    /* Create the initial empty heap */
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1)
        return -1;
    PUT(heap_listp, 0);
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));
    heap_listp += (2*WSIZE);  // 프롤로그 블록의 bp

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;
    return 0;
}

/* extend_heap : 워드 단위 메모리를 인자로 받아 힙을 늘려준다. */
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    if ((long) (bp = mem_sbrk(size)) == -1)
        return NULL;

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));  // 에필로그
    /* Coalesce if the previous block was free */
    return coalesce(bp);
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
/* mm_malloc: 요청 받은 사이즈 만큼 메모리를 8의 배수로 할당해 준다. */
void *mm_malloc(size_t size)
{
    /*int newsize = ALIGN(size + SIZE_T_SIZE);
    void *p = mem_sbrk(newsize);
    if (p == (void *)-1)
	return NULL;
    else {
        *(size_t *)p = size;
        return (void *)((char *)p + SIZE_T_SIZE);
    }*/

    size_t asize;
    size_t extendsize;
    char *bp;

    /* Ignore squrious requests */
    if (size == 0)
        return NULL;

    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= DSIZE)
        asize = 2*DSIZE;
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);

    /* Search the free list for a fit */
    if ((bp = best_fit(asize)) != NULL) {
        place(bp, asize);
        last_bp = bp;
        return bp;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL){
        return NULL;
    }
    place(bp, asize);
    last_bp = bp;
    return bp;
}

/* first_fit: 첫 블록부터 시작하여 적절한 사이즈의 가용 블록을 찾아 주소값 반환 */
static void* first_fit(size_t asize)
{
    /* 리스트 처음부터 탐색하여 가용블록 찾기 */
    void* bp;
    // 헤더의 사이즈가 0보다 크다. -> 에필로그까지 탐색.
    for (bp = heap_listp; GET_SIZE(HDRP(bp)) >0; bp = NEXT_BLKP(bp)){
        if(!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
            return bp;
        }
    }
    return NULL;
}

/* next_fit: 마지막으로 탐색한 bp에서부터 탐색을 시작하는 방식(못찾을시 첫 블록부터 그 전 탐색 bp까지 재 탐색) */
static void* next_fit(size_t asize)
{
    /* next-fit search */
    char* bp = last_bp;
    for (bp = NEXT_BLKP(bp); GET_SIZE(HDRP(bp)) !=0; bp = NEXT_BLKP(bp)) {
        if (!GET_ALLOC(HDRP(bp)) && GET_SIZE(HDRP(bp)) >= asize) {
            last_bp = bp;
            return bp;
        }
    }

    bp = heap_listp;
    while (bp < last_bp) 
    {
        bp = NEXT_BLKP(bp);
        if (!GET_ALLOC(HDRP(bp)) && GET_SIZE(HDRP(bp)) >= asize) {
            last_bp = bp;
            return bp;
        }
    }
    
    return NULL;  /* NO fit */
}

/* best_fit: 리스트의 처음부터 탐색하여 가장 적합한(할당 가능한 블록 중 가장 크기가 작은) 가용블록 탐색 */
static void* best_fit(size_t asize)
{
    /* 리스트 처음부터 탐색하여 가용블록 찾기 */
    void* bp;
    void* cur_bp = NULL;
    int prev_min = 20*(1<<20);
    // 헤더의 사이즈가 0보다 크다. -> 에필로그까지 탐색.
    for (bp = heap_listp; GET_SIZE(HDRP(bp)) >0; bp = NEXT_BLKP(bp)){
        if(!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))) && (prev_min > GET_SIZE(HDRP(bp)))) {
            prev_min = GET_SIZE(HDRP(bp));
            cur_bp = bp;
            if (asize == GET_SIZE(HDRP(bp)))
                return bp;
        }
    }
    if (cur_bp == NULL)
        return NULL;
    return cur_bp;
}
/* place: 가용 블록의 크기가 분할해도 될 만큼 크면 분할 그렇지 않으면 그대로 주소값 반환 */
static void place(void* bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));

    if ((csize - asize) >= (2*DSIZE)) {
        PUT(HDRP(bp) , PACK(asize, 1));
        PUT(FTRP(bp) , PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp) , PACK(csize-asize, 0));
        PUT(FTRP(bp) , PACK(csize-asize, 0));
    }
    else {
        PUT(HDRP(bp) , PACK(csize, 1));
        PUT(FTRP(bp) , PACK(csize, 1));
    }
}


/*
 * mm_free - Freeing a block does nothing.
 */
/* mm_free: 할당블록을 가용블록으로 반환 */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}

/* coalesce: free된 가용 블록을 인접한 가용블록들과 병합 */
static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) {   /* Case 1 */
        last_bp = bp;
        return bp;
    }

    else if (prev_alloc && !next_alloc)  {   /* Case 2 */
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size,0));
    }

    else if (!prev_alloc && next_alloc)  {   /* Case 3 */
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    else {                                   /* Case 4 */
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + 
            GET_SIZE(FTRP(NEXT_BLKP(bp)));
            PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
            PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
            bp = PREV_BLKP(bp);
    }
    last_bp = bp;
    return bp;
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
/* mm_realloc: 메모리 추가 할당 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;
    
    newptr = mm_malloc(size);
    if (newptr == NULL)
      return NULL;
    // copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
    copySize = GET_SIZE(HDRP(oldptr)) - DSIZE;
    if (size < copySize)
      copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}














