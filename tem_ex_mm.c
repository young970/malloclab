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
#define MINIMUM 16 

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

/* Free List 상에서의 이전, 이후 블록의 포인터를 리턴한다. */
#define PREC_FREEP(bp)  (*(void**)(bp))             // 이전 블록의 bp
#define SUCC_FREEP(bp)  (*(void**)(bp + WSIZE))     // 이후 블록의 bp

/* global variable & functions */
static char* heap_listp = NULL; // 항상 prologue block을 가리키는 정적 전역 변수 설정
static char* free_listp = NULL; // free list의 맨 첫 블록을 가리키는 포인터

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

static void *coalesce(void *bp);
static void *extend_heap(size_t words);
static void* find_fit(size_t asize);
static void place(void* bp, size_t asize);

/* 
 * mm_init - initialize the malloc package.
 */

/* mm_init: 패딩 블록과 프롤로그 블록과 에필로그 블록 생성 후 힙을 확장하여 초기 가용 블록 생성 */
int mm_init(void)
{
    /* 메모리에서 6words를 가져오고 이걸로 빈 가용 리스트 초기화 */
    /* padding, prol_header, prol_footer, PREC, SUCC, epil_header */
    if ((heap_listp = mem_sbrk(6*WSIZE)) == (void*)-1)
        return -1;

    PUT(heap_listp, 0);  // Alignment padding. 더블 워드 경계로 정렬된 미사용 패딩.
    PUT(heap_listp + (1*WSIZE), PACK(MINIMUM, 1));  // prologue header
    PUT(heap_listp + (2*WSIZE), NULL);  // prologue block안의 PREC 포인터 NULL로 초기화
    PUT(heap_listp + (3*WSIZE), NULL);  // prologue block안의 SUCC 포인터 NULL로 초기화
    PUT(heap_listp + (4*WSIZE), PACK(MINIMUM, 1));  // prologue footer
    PUT(heap_listp + (5*WSIZE), PACK(0, 1));      // epliogue header

    free_listp = heap_listp + 2*WSIZE; // free_listp를 탐색의 시작점으로 둔다. 


    /* 그 후 CHUNKSIZE만큼 힙을 확장해 초기 가용 블록을 생성한다. */
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL) //실패하면 -1 리턴
        return -1;

    return 0;
}

/*
    extend_heap : 워드 단위 메모리를 인자로 받아 힙을 늘려준다.
*/
static void* extend_heap(size_t words){ // 워드 단위로 받는다.
    char* bp;
    size_t size;
    
    /* 더블 워드 정렬에 따라 메모리를 mem_sbrk 함수를 이용해 할당받는다. */
    size = (words % 2) ? (words + 1) * WSIZE : (words) * WSIZE; // size를 짝수 word && byte 형태로 만든다.
    if ((long)(bp = mem_sbrk(size)) == -1) // 새 메모리의 첫 부분을 bp로 둔다. 주소값은 int로는 못 받아서 long으로 casting한 듯.
        return NULL;
    
    /* 새 가용 블록의 header와 footer를 정해주고 epilogue block을 가용 블록 맨 끝으로 옮긴다. */
    PUT(HDRP(bp), PACK(size, 0));  // 헤더. 할당 안 해줬으므로 0으로.
    PUT(FTRP(bp), PACK(size, 0));  // 풋터.
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));  // 새 에필로그 헤더

    /* 만약 이전 블록이 가용 블록이라면 연결시킨다. */
    return coalesce(bp);
}


/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */

/* mm_malloc: 요청 받은 사이즈 만큼 메모리를 8의 배수로 할당해 준다. */
void *mm_malloc(size_t size)
{
    size_t asize;       // Adjusted block size
    size_t extendsize;  // Amount for extend heap if there is no fit
    char* bp;

    // 가짜 요청 spurious request 무시
    if (size == 0)
        return NULL;

    // 요청 사이즈에 header와 footer를 위한 dword 공간(SIZE_T_SIZE)을 추가한 후 align해준다.
    asize = ALIGN(size + SIZE_T_SIZE);  

    // 할당할 가용 리스트를 찾아 필요하다면 분할해서 할당한다!
    if ((bp = find_fit(asize)) != NULL){  // first fit으로 추적한다.
        place(bp, asize);  // 필요하다면 분할하여 할당한다.
        return bp;
    }

    // 만약 맞는 크기의 가용 블록이 없다면 새로 힙을 늘려서 새 힙에 메모리를 할당한다.
    extendsize = MAX(asize, CHUNKSIZE);  // 둘 중 더 큰 값으로 사이즈를 정한다.
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL) 
        return NULL;
    place(bp, asize);
    return bp;
}

/* find_fit: first fit 방식으로 적절한 사이즈의 가용 블록을 찾아 주소값 반환 */
static void* find_fit(size_t asize){
    /* First-fit */
    void* bp;

    // free list의 맨 뒤는 프롤로그 블록이다. Free list에서 유일하게 할당된 블록이므로 얘를 만나면 탐색 종료.
    for (bp = free_listp; GET_ALLOC(HDRP(bp)) != 1; bp = SUCC_FREEP(bp)){
        if(asize <= GET_SIZE(HDRP(bp))){
            return bp;
        }
    }

    // 못 찾으면 NULL을 리턴한다.
    return NULL;
}

/* place: 가용 블록의 크기가 분할해도 될 만큼 크면 분할 후 프리리스트에 연결시켜 주소값 반환 */
static void place(void* bp, size_t asize){
    // 현재 할당할 수 있는 후보 가용 블록의 주소
    size_t csize = GET_SIZE(HDRP(bp));

    // 할당될 블록이므로 free list에서 없애준다.
    removeBlock(bp);

    // 분할이 가능한 경우
    if ((csize - asize) >= (2*DSIZE)){
        // 앞의 블록은 할당 블록으로
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        // 뒤의 블록은 가용 블록으로 분할한다.
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize-asize, 0));
        PUT(FTRP(bp), PACK(csize-asize, 0));

        // free list 첫번째에 분할된 블럭을 넣는다.
        putFreeBlock(bp);
    }
    else{
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

/*
 * mm_free - Freeing a block does nothing.
 */

/* mm_free: 할당블록을 가용블록으로 반환 (가용리스트 연결은 coalesce()에서 해줌) */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}

/* coalesce: free된 가용 블록을 인접한 가용블록들과 병합 및 가용리스트 연결 */
static void* coalesce(void* bp){
    // 직전 블록의 footer, 직후 블록의 header를 보고 가용 여부를 확인.
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));  // 직전 블록 가용 여부
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));  // 직후 블록 가용 여부
    size_t size = GET_SIZE(HDRP(bp));

    // case 1 : 직전, 직후 블록이 모두 할당 -> 해당 블록만 free list에 넣어주면 된다.

    // case 2 : 직전 블록 할당, 직후 블록 가용
    if(prev_alloc && !next_alloc){
        removeBlock(NEXT_BLKP(bp));    // free 상태였던 직후 블록을 free list에서 제거한다.
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }

    // case 3 : 직전 블록 가용, 직후 블록 할당
    else if(!prev_alloc && next_alloc){
        removeBlock(PREV_BLKP(bp));    // 직전 블록을 free list에서 제거한다.
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        bp = PREV_BLKP(bp); 
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));  
    }

    // case 4 : 직전, 직후 블록 모두 가용
    else if (!prev_alloc && !next_alloc) {
        removeBlock(PREV_BLKP(bp));
        removeBlock(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        bp = PREV_BLKP(bp);
        PUT(HDRP(bp), PACK(size, 0));  
        PUT(FTRP(bp), PACK(size, 0));  
    }

    // 연결된 새 가용 블록을 free list에 추가한다.
    putFreeBlock(bp);

    #ifdef NEXT_FIT
        last_freep = bp;
    #endif

    return bp;
}

/* putFreeBlock: 가용리스트에 연결 */
void putFreeBlock(void* bp){
    SUCC_FREEP(bp) = free_listp;
    PREC_FREEP(bp) = NULL;
    PREC_FREEP(free_listp) = bp;
    free_listp = bp;
}

/* removeBlock: 가용리스트에 연결 끊음 */
void removeBlock(void *bp){
    // free list의 첫번째 블록을 없앨 때
    if (bp == free_listp){
        PREC_FREEP(SUCC_FREEP(bp)) = NULL;
        free_listp = SUCC_FREEP(bp);
    }
    // free list 안에서 없앨 때
    else{
        SUCC_FREEP(PREC_FREEP(bp)) = SUCC_FREEP(bp);
        PREC_FREEP(SUCC_FREEP(bp)) = PREC_FREEP(bp);
    }
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














