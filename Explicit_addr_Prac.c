/*
 * EXPLICIT - Address 순으로 정렬
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
#include <stdbool.h>
/*********************************************************
  * NOTE TO STUDENTS: Before you do anything else, please
  * provide your team information in the following struct.
  ********************************************************/
team_t team = {
    /* Team name */
    "team1",
    /* First member's full name */
    "Firecat",
    /* First member's email address */
    "karockai@gmail.com",
    /* Second member's full name (leave blank if none) */
    "VictoryPeaple",
    /* Third member's full name (leave blank if none) */
    "YouStone"};
/*------------------------------------- Macro ---------------------------------*/
// [bytes] word, header, footer size
#define WSIZE 4

// [bytes] double word size
#define DSIZE 8

// [bytes] extend heap by this amount 하나의 페이지는 4[kb]
#define CHUNKSIZE (1 << 12)

// max 값 반환
#define MAX(x, y) ((x) > (y) ? (x) : (y))

// size 뒤의 000 공간에 allocation 여부를 저장한 비트를 반환
#define PACK(size, alloc) ((size) | (alloc))

// 주소값에서 값 읽어옴
#define GET(p) (*(unsigned int *)(p))

// 주소값에다 값 씀
#define PUT(p, val) (*(unsigned int *)(p) = (val))

// 블록 사이즈 읽어옴
#define GET_SIZE(p) (GET(p) & ~0x7)

// 할당 여부를 읽어옴
#define GET_ALLOC(p) (GET(p) & 0x1)

//bp = block pointer
// 헤더의 주소값을 반환
#define HDRP(bp) ((char *)(bp)-WSIZE)

// 푸터의 주소값을 반환, 헤더에서 사이즈를 안 다음 double word를 빼줌.
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

// 해당 블록에

//blkp = block pointer
// 다음 블록의 주소값을 반환, 헤더에서 내 사이즈 더해주고 word를 빼줌.
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp)-WSIZE)))
// 전 블록의 주소값을 반환, 헤더에서 double word를 빼고 전 블록의 사이즈를 알아낸다.
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp)-DSIZE)))

#define PREV(bp) ((char *)(bp))
#define NEXT(bp) ((char *)(bp) + WSIZE)

/*------------------------------------- Declaration ---------------------------------*/
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
static char *heap_listp;
void *compare(void *bp, void *next_bp);
void Insert_Block(void *new_bp, void *next_bp);
void Cut_Connection(void *bp);
void mm_free(void *bp);

/*------------------------------------- INIT ---------------------------------*/
// prev와 next가 들어가므로 Prologue Block을 4word 배치한다.
int mm_init(void)
{
    // mem_sbrk 호출해서 9W 메모리 request하는 데, 실패 하면 -1 리턴
    if ((heap_listp = mem_sbrk(5 * WSIZE)) == (void *)-1)
    {
        return -1;
    }

    /* ------------------- Prologue ------------------ */
    PUT(heap_listp, 0);

    // heap:0에 DSIZE와 allocated 넣음 (PROLOGUE HEADER)
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE * 2, 1));

    // heap:1에는 PREV가 들어간다.
    // Prologue 이므로 PREV는 NULL을 해준다.
    PUT(heap_listp + (2 * WSIZE), NULL);

    // heap:2에는 NEXT가 들어간다.
    PUT(heap_listp + (3 * WSIZE), heap_listp + (6 * WSIZE));

    // heap:3에는 FOOTER가 들어간다.
    PUT(heap_listp + (4 * WSIZE), PACK(DSIZE * 2, 1));

    /* ------------------- Epilogue ------------------ */
    // heap:4에 DSIZE와 allocated 넣음 (PROLOGUE HEADER)
    PUT(heap_listp + (5 * WSIZE), PACK(DSIZE * 2, 1));

    // heap:5에는 PREV가 들어간다.
    PUT(heap_listp + (6 * WSIZE), heap_listp + 2 * WSIZE);

    // Epilogue 이므로 NEXT는 NULL을 해준다.
    // heap:6에는 NEXT가 들어간다.
    PUT(heap_listp + (7 * WSIZE), NULL);

    // heap:7에는 FOOTER가 들어간다.
    PUT(heap_listp + (8 * WSIZE), PACK(DSIZE * 2, 1));

    // heap_lisp 포인터를 옮겨줌
    heap_listp += DSIZE;

    // chunk size 확인(받을수 있는 사이즈인지)??
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
    {
        return -1;
    }
    return 0;
}
/*------------------------------------- Extend_Heap ---------------------------------*/
static void *extend_heap(size_t words)
{
    // printf("extend heap\n");
    char *bp;
    size_t size;
    // 짝수로 만듬
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    // 너무 커서 할당 못받으면 return -1
    
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;
    // printf("sbrk, bp = %p\n", bp);
    // 현재 bp가 가용 블록의 맨 처음이므로 해당 블록의 bp자리로 옮겨준다
    bp = bp + 4;

    // block header free
    PUT(HDRP(bp), PACK(size, 0));
    // block putter free
    PUT(FTRP(bp), PACK(size, 0));

    void* last_free = GET(PREV(bp));

    // 새로운 epilogue 배치
    void *EBP = NEXT_BLKP(bp);
    PUT(HDRP(EBP), PACK(DSIZE * 2, 1));
    PUT(PREV(EBP), last_free);
    PUT(NEXT(EBP), NULL);
    PUT(FTRP(EBP), PACK(DSIZE * 2, 1));
    // extend를 실행했다는 것은, extend size보다 큰 블록이 없다는 뜻이다.
    PUT(NEXT(last_free), EBP);
    PUT(PREV(bp), 0);
    PUT(NEXT(bp), 0);

    // 만약 전 block이 프리였다면 합친다.
    // return coalesce(bp);
    return coalesce(bp);
}

/* ----------------------------------- Malloc -------------------------------------*/
void *mm_malloc(size_t size)
{
    // printf("malloc----------------------------------------------------------------------------------\n");
    // printf("size needed:%d\n",size);
    // 생성할 size
    size_t asize;
    // 만약 chunksize를 넘긴 사이즈
    size_t extendsize;
    char *bp;
    // 만약 입력받은 사이즈가 0 이면 무시
    if (size == 0)
        return NULL;

    // 만약 입력받은 사이즈가 dsize보다 작아도 4size로 생성
    if (size <= DSIZE)
        asize = 2 * DSIZE;

    // 2의 배수(Dsize)로 생성
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);
    // 들어갈 free 블록이 있다면 넣어준다.
    if ((bp = find_fit(asize)) != NULL)
    {
        Cut_Connection(bp);
        place(bp, asize);
        // printf("malloc_bp:%p, bp_value:%d\n", bp, GET(bp));
        return bp;
    }

    // 만약 chunksize를 넘긴 사이즈라면
    extendsize = MAX(asize, CHUNKSIZE);
    // 넘긴 사이즈만큼의 힙을 할당받음
    // printf("no space -> extend heap\n");
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
        return NULL;
    // printf("after extend, bp : %p\n", bp);
    Cut_Connection(bp);
    place(bp, asize);
    return bp;
}

/* ----------------------------------- Find Fit -------------------------------------*/
static void *find_fit(size_t asize)
{
    // printf("find_fit, size needed: %d\n", asize);
    void *bp = GET(NEXT(heap_listp));
    // printf("heaplistp: %p\n", heap_listp);
    // printf("NEXT of heaplistp : %p\n", bp);
    // printf("nextbp : %p\n", GET(NEXT(bp)));
    // bp 처음부터 블록단위로 for문 0(epilogue)
    while (GET(NEXT(bp)) != NULL)
    {
        // printf("%p, %p/n", bp, NEXT(bp));
        // printf("freeblock_Size:%d\n", GET_SIZE(HDRP(bp)));
        if (GET_SIZE(HDRP(bp)) >= asize)
        {
            // printf("find success, bp = %p, next_bp = %p\n" , bp, GET(NEXT(bp)));
            // printf("get size: %d, size needed : %d\n", GET(HDRP(bp)), asize);
            return bp;
        }
        bp = GET(NEXT(bp));
        // printf("bp in find:%p\n", bp);
    }
    // printf("find failed, bp = %p, next_bp = %p\n" , bp, GET(NEXT(bp)));
    return NULL;
}

/* ----------------------------------- Place -------------------------------------*/
static void place(void *bp, size_t asize)
{
    // printf("place, bp : %p\n", bp);
    // 헤더의 사이즈를 읽어옴
    size_t csize = GET_SIZE(HDRP(bp));
    // printf("csize:%d\n", csize);
    // prev, next가 필요하므로 최소 분리 사이즈를 6으로 해준다.
    // 삽입하고 자리가 남으면 SPLIT 해준다.
    if ((csize - asize) >= (4 * WSIZE))
    {
        // printf("after place, remain block\n");
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        // printf("remain bp : %p\n", bp);
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));

        PUT(PREV(bp), 0);
        PUT(NEXT(bp), 0);
        // prologue의 다음 가용 블록부터 시작한다.
        void *next_bp = compare(bp, GET(NEXT(heap_listp)));
        Insert_Block(bp, next_bp);
    }
    // 딱 맞는다면 그냥 넣어준다.
    else
    {
        // printf("no remained\n");
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
    // printf("????\n");
}

/* ----------------------------------- Free -------------------------------------*/
void mm_free(void *bp)
{
    // printf("free<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<< : %p\n", bp);
    // 헤더의 사이즈를 읽어옴
    size_t size = GET_SIZE(HDRP(bp));

    // 헤더에 free 입력
    PUT(HDRP(bp), PACK(size, 0));
    // 푸터에 free 입력
    PUT(FTRP(bp), PACK(size, 0));
    PUT(PREV(bp), 0);
    PUT(NEXT(bp), 0);

    // coalesce 시켜주고 병합된 가용 블록의 bp 받아옴
    void *new_bp = coalesce(bp);
}

// compare는 반환된 블록의 크기와 연결 리스트 상의 블록과 비교한다.
void *compare(void *bp, void *next_bp)
{
    // printf("compare, next_bp : %p\n", next_bp);
    while (!(GET(NEXT(next_bp)) == NULL))
    {
        if (next_bp > bp)
        {
            return next_bp;
        }
        next_bp = GET(NEXT(next_bp));
        // printf("next_bp : %p\n", next_bp);
    }

    // 다음 자리에 next_bp가 온다는 뜻이다
    return next_bp;
}

// 새로운 가용 블록을 next_bp의 PREV에 이어주기 위한 작업. 
void Insert_Block(void *new_bp, void *next_bp)
{
    // printf("Insert Block, new_bp: %p, next_bp : %p\n", new_bp, next_bp);
    // 우선 next_bp로 prev_bp를 받아온다.
    void *prev_bp = GET(PREV(next_bp));

    // 1. 전 블록의 next를 현 블록으로 이어준다.
    PUT(NEXT(prev_bp), new_bp);

    // 2. 현 블록의 next를 후 블록으로 이어준다.
    PUT(NEXT(new_bp), next_bp);

    // 3. 후 블록의 prev를 현 블록으로 이어준다.
    PUT(PREV(next_bp), new_bp);

    // 4. 현 블록의 prev를 전 블록으로 이어준다.
    PUT(PREV(new_bp), prev_bp);

    // 5. 현 블록의 pb을 다음 블록의 pb로 바꿔준다.
    // -> 필요 없다. 실제로는 현 블록이 이동하는 것이 아니기때문
}

/* ----------------------------------- Coalesce -------------------------------------*/
// explicit에서는 prev, next도 이어줘야 하므로 포인터를 반환하도록 한다.
static void *coalesce(void *bp)
{
    // printf("coal, bp : %p\n", bp);
    // 좌측 블록이 alloc 인가
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    // 우측 블록이 alloc 인가
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    // 현재 노드의 사이즈
    size_t size = GET_SIZE(HDRP(bp));

    // case 1 : 좌, 우 모두 할당 상태일 때,	병합없이 반환
    if (prev_alloc && next_alloc)
    {
        // printf("coal:no free\n");
        PUT(PREV(bp), 0);
        PUT(NEXT(bp), 0);
        PUT(NEXT(bp), GET(NEXT(heap_listp)));
    }

    // case 2 : 우측 블록이 가용 상태일 때 :
    else if (prev_alloc && !next_alloc)
    {
        // printf("coal:right_free\n");
        // 우측 블록의 prev와 next 정보를 저장한다.
        void *right_bp = NEXT_BLKP(bp);
        // void *old_prev = GET(PREV(right_bp));
        // void *old_next = GET(NEXT(right_bp));
        Cut_Connection(right_bp);

        // 다음 블록의 사이즈까지 합쳐서 free시킴
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));

        // 블록 정보 갱신
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(PREV(bp), 0);
        PUT(NEXT(bp), 0);
        // PUT(PREV(bp), old_prev);
        PUT(NEXT(bp), GET(NEXT(heap_listp)));
    }

    // case 3 : 좌측 블록만 가용 블록일 때,
    // 전의 사이즈까지 합쳐서 free시킴
    else if (!prev_alloc && next_alloc)
    {
        // printf("coal:left_free\n");
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
        Cut_Connection(bp);
        PUT(PREV(bp), 0);
        PUT(NEXT(bp), 0);
        PUT(NEXT(bp), GET(NEXT(heap_listp)));
    }

    // case 4 : 앞 뒤 다 free
    else
    {
        // printf("coal:both free\n");
        // 일단 크기 비교
        size_t left_size = GET_SIZE(HDRP(PREV_BLKP(bp)));
        size_t right_size = GET_SIZE(FTRP(NEXT_BLKP(bp)));

        void* left_bp = PREV_BLKP(bp);
        void* right_bp = NEXT_BLKP(bp);
        Cut_Connection(left_bp);
        Cut_Connection(right_bp);
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        PUT(PREV(bp), 0);
        PUT(NEXT(bp), 0);
        bp = left_bp;
        PUT(NEXT(bp), GET(NEXT(heap_listp)));

    }

    void* next_bp = compare(bp, GET(NEXT(heap_listp)));
    Insert_Block(bp, next_bp);
    return bp;
}

/* ----------------------------------- Realloc -------------------------------------*/
void *mm_realloc(void *bp, size_t size)
{
    // printf("realloc, bp:%p\n", bp);
    void *old_bp = bp;
    void *new_bp;
    size_t copySize;
    // 다른데다가 다시 할당 받기
    new_bp = mm_malloc(size);
    // 실패하면 NULL 리턴
    if (new_bp == NULL)
        return NULL;

    // 원래 블록의 사이즈
    copySize = GET_SIZE(HDRP(old_bp));

    // 요청한 사이즈가 작다면 작은사이즈로 카피
    if (size < copySize)
        copySize = size;
    memcpy(new_bp, old_bp, copySize);
    // 기존 사이즈는 삭제
    mm_free(old_bp);
    return new_bp;
}

/* ----------------------------------- Missing_Connect  -------------------------------------*/
// bp의 블록 PREV, NEXT를 끊어주고, PREV 블록과 NEXT 블록을 이어준다.
void Cut_Connection(void *bp)
{

    void* next_bp = GET(NEXT(bp));
    void* prev_bp = GET(PREV(bp));

    PUT(NEXT(prev_bp), next_bp);
    PUT(PREV(next_bp), prev_bp);


    PUT(PREV(bp), 0);
    PUT(NEXT(bp), 0);
    return;
}

