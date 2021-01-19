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
	"team1",
	/* First member's full name */
	"Firecat",
	/* First member's email address */
	"karockai@gmail.com",
	/* Second member's full name (leave blank if none) */
	"VictoryPeaple",
	/* Third member's full name (leave blank if none) */
	"YouStone"
};
/*------------------------------------- Macro ---------------------------------*/
// [bytes] word, header, footer size
#define WSIZE 4

// [bytes] double word size
#define DSIZE 8

// [bytes] extend heap by this amount 하나의 페이지는 4[kb]
#define CHUNKSIZE (1<<12)

// max 값 반환
#define MAX(x,y)		 ((x)>(y) ? (x):(y))

// size 뒤의 000 공간에 allocation 여부를 저장한 비트를 반환
#define PACK(size,alloc) ((size) | (alloc))

// 주소값에서 값 읽어옴
#define GET(p)			 (*(unsigned int *)(p))

// 주소값에다 값 씀
#define PUT(p,val)		 (*(unsigned int *)(p) = (val))

// 블록 사이즈 읽어옴
#define GET_SIZE(p)		 (GET(p) & ~0x7)

// 할당 여부를 읽어옴
#define GET_ALLOC(p)	 (GET(p) & 0x1)

//bp = block pointer
// 헤더의 주소값을 반환																		 
#define HDRP(bp)		 ((char*)(bp) - WSIZE)

// 푸터의 주소값을 반환, 헤더에서 사이즈를 안 다음 double word를 빼줌.
#define FTRP(bp)		 ((char*)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

// 해당 블록에 

//blkp = block pointer
// 다음 블록의 주소값을 반환, 헤더에서 내 사이즈 더해주고 word를 빼줌.
#define NEXT_BLKP(bp) 	 ((char*)(bp) + GET_SIZE(((char *)(bp) -WSIZE)))
// 전 블록의 주소값을 반환, 헤더에서 double word를 빼고 전 블록의 사이즈를 알아낸다.                                                    
#define PREV_BLKP(bp) 	 ((char*)(bp) - GET_SIZE(((char *)(bp) -DSIZE))) 

#define PREV(bp)	 ((char*)(bp) + WSIZE)
#define NEXT(bp)	 ((char*)(bp) + DSIZE)



/*------------------------------------- Declaration ---------------------------------*/
static void* extend_heap(size_t words);
static void* coalesce(void* bp);
static void* find_fit(size_t asize);
static void place(void* bp, size_t asize);
static char* heap_listp;
static char* heap_lastp;
bool compare(void* new_bp, void* next_bp);
void exchange(void* new_bp, void* next_bp);
void missing_connect(void *missing_bp);


/*------------------------------------- INIT ---------------------------------*/
// prev와 next가 들어가므로 Prologue Block을 4word 배치한다. 
int mm_init(void)
	// mem_sbrk 호출해서 4W 메모리 request하는 데, 실패 하면 -1 리턴
	if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void*)-1) return -1;
	// heap:0에  free 넣음 (Alignment padding)
	PUT(heap_listp, 0);

	/* ------------------- Prologue ------------------ */
	// heap:1에 DSIZE와 allocated 넣음 (PROLOGUE HEADER)
	PUT(heap_listp + (1 * WSIZE), PACK(DSIZE*2, 1));

	// heap:2에는 PREV가 들어간다.
	// Prologue 이므로 PREV는 NULL을 해준다.
	void *init_prev = NULL;
	PUT(heap_listp + (2 * WSIZE), init_prev);
	
	// heap:3에는 NEXT가 들어간다.
	PUT(heap_listp + (3 * WSIZE), heap_listp + 6 * WSIZE);

	// heap:4에는 FOOTER가 들어간다.
	PUT(heap_listp + (4 * WSIZE), PACK(DSIZE*2, 1));

	/* ------------------- Epilogue ------------------ */
	// heap:5에 DSIZE와 allocated 넣음 (PROLOGUE HEADER)
	PUT(heap_listp + (5 * WSIZE), PACK(DSIZE*2, 1));

	// heap:6에는 PREV가 들어간다.
	PUT(heap_listp + (6 * WSIZE), heap_listp + 2 * WSIZE);
	
	// Epilogue 이므로 NEXT는 NULL을 해준다.
	// heap:7에는 NEXT가 들어간다.
	void *init_next = NULL;
	PUT(heap_listp + (7 * WSIZE), init_next);

	// heap:8에는 FOOTER가 들어간다.
	PUT(heap_listp + (8 * WSIZE), PACK(DSIZE*2, 1));

	// heap_lisp 포인터를 옮겨줌
	heap_listp += (2 * WSIZE);

	// heap_lastp 포인터를 옮겨줌
	heap_lastp += (6 * WSIZE); 

	// chunk size 확인(받을수 있는 사이즈인지)??
	if (extend_heap(CHUNKSIZE / WSIZE) == NULL)	return -1;

	return 0;
}


/*------------------------------------- Extend_Heap ---------------------------------*/
static void* extend_heap(size_t words) {
	char* bp;
	size_t size;
	// 짝수로 만듬
	size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
	// 너무 커서 할당 못받으면 return -1
	if ((long)(bp = mem_sbrk(size)) == -1)	return NULL;

	// block header free
	PUT(HDRP(bp), PACK(size, 0));

	// block putter free
	PUT(FTRP(bp), PACK(size, 0));

	// heap_lastp 앞에 현 블록을 삽입함.
	exchange(bp, heap_lastp);

	// 새로운 epiloge 헤더
	PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));

	// 만약 전 block이 프리였다면 합친다.
	return coalesce(bp);
}

/* ----------------------------------- Malloc -------------------------------------*/
void* mm_malloc(size_t size)
{
	// 생성할 size
	size_t asize;
	// 만약 chunksize를 넘긴 사이즈														 
	size_t extendsize;
	char* bp;
	// 만약 입력받은 사이즈가 0 이면 무시
	if (size == 0)														 
		return NULL;

	// 만약 입력받은 사이즈가 dsize보다 작아도 최소 size로 생성
	if (size <= DSIZE)
		asize = 2 * DSIZE;

	// 2의 배수(Dsize)로 생성
	else
		asize = DSIZE * ((size + (DSIZE)+(DSIZE - 1)) / DSIZE);

	// 들어갈 free 블록이 있다면 넣어준다.
	if ((bp = find_fit(asize)) != NULL) {
		place(bp, asize);
		return bp;
	}

	// 만약 chunksize를 넘긴 사이즈라면
	extendsize = MAX(asize, CHUNKSIZE);
	// 넘긴 사이즈만큼의 힙을 할당받음
	if ((bp = extend_heap(extendsize / WSIZE)) == NULL)	
		return NULL;
	place(bp, asize);
	return bp;
}

/* ----------------------------------- Find Fit -------------------------------------*/
static void* find_fit(size_t asize) {									 
	void* bp;
	// bp 처음부터 블록단위로 for문 0(epilogue) 
	while (bp != NULL)
	{
		if (GET_SIZE(bp) > asize)
		{
			return bp;
		}
		bp = GET(NEXT(bp));
	}
	return;
}


/* ----------------------------------- Place -------------------------------------*/
static void place(void* bp, size_t asize) {
	// 헤더의 사이즈를 읽어옴
	size_t csize = GET_SIZE(HDRP(bp));								      
    // prev, next가 필요하므로 최소 분리 사이즈를 6으로 해준다.
	// 삽입하고 자리가 남으면 SPLIT 해준다.
	if ((csize - asize) >= (6 * DSIZE)) {								  
		PUT(HDRP(bp), PACK(asize, 1));
		PUT(FTRP(bp), PACK(asize, 1));
		bp = NEXT_BLKP(bp);
		PUT(HDRP(bp), PACK(csize - asize, 0));
		PUT(FTRP(bp), PACK(csize - asize, 0));
	}
	// 딱 맞는다면 그냥 넣어준다.
	else {																  
		PUT(HDRP(bp), PACK(csize, 1));
		PUT(FTRP(bp), PACK(csize, 1));
	}
}



/* ----------------------------------- Free -------------------------------------*/
void mm_free(void* bp)													  
{
	// 헤더의 사이즈를 읽어옴
	size_t size = GET_SIZE(HDRP(bp));

	// 헤더에 free 입력
	PUT(HDRP(bp), PACK(size, 0));
	// 푸터에 free 입력
	PUT(FTRP(bp), PACK(size, 0));
	
	// coalesce 시켜주고 병합된 가용 블록의 bp 받아옴
	void* new_bp = coalesce(bp);
}

// compare는 반환된 블록의 크기와 연결 리스트 상의 블록과 비교한다.
// 만약 한 블록이 반환 블록보다 크다면 1을 반환한다.
bool compare(void* new_bp, void* next_bp)
{
	if (next_bp == NULL) return 0;
	size_t new_size = GET_SIZE(HDRP(new_bp));
	size_t next_size = GET_SIZE(HDRP(next_bp));
	if (next_size > new_size)
	{
		exchange(new_bp, next_bp);
		return 1;
	}
	return 0;
}

void exchange(void* new_bp, void* next_bp)
{
	// 우선 next_bp로 prev_bp를 받아온다. 
	void* prev_bp = PREV(next_bp);

	// 1. 전 블록의 next를 현 블록으로 이어준다.
	PUT(NEXT(prev_bp),new_bp);

	// 2. 현 블록의 next를 후 블록으로 이어준다.
	PUT(NEXT(new_bp)),next_bp);

	// 3. 후 블록의 prev를 현 블록으로 이어준다.
	PUT(PREV(next_bp)), new_bp);

	// 4. 현 블록의 prev를 전 블록으로 이어준다.
	PUT(PREV(new_bp)), prev_bp);

	// 5. 현 블록의 pb을 다음 블록의 pb로 바꿔준다.
}


/* ----------------------------------- Coalesce -------------------------------------*/
// explicit에서는 prev, next도 이어줘야 하므로 포인터를 반환하도록 한다.
static void* coalesce(void* bp)
{
	// 전에 블록이 alloc 인가
	size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
	// 다음 블록이 alloc 인가
	size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
	// 현재 노드의 사이즈
	size_t size = GET_SIZE(HDRP(bp));
	int flag;

	// case 1 : 전, 후 모두 할당 상태일 때,	병합없이 반환  
	if (prev_alloc && next_alloc) {
		return bp;
	}

	// case 2 : 후 블록이 가용 상태일 때, 
	else if (prev_alloc && !next_alloc) {
		void *old_prev = GET(PREV(NEXT_BLKP(bp)));
		void *old_next = GET(NEXT(NEXT_BLKP(bp)));

		// 다음 블록의 사이즈까지 합쳐서 free시킴						 
		size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
		// 블록 정보 갱신
		PUT(HDRP(bp), PACK(size, 0));
		PUT(FTRP(bp), PACK(size, 0));
		PUT(PREV(bp), old_prev);
		PUT(NEXT(bp), old_next);

		// 정렬 해줌
		int result = 0;
		while (result == 1)
		{
			result = compare(bp, NEXT(bp));
		}
	}

	// case 3 : 전 블록만 가용 블록일 때,
	// 전의 사이즈까지 합쳐서 free시킴
	else if (!prev_alloc && next_alloc) {
		size += GET_SIZE(HDRP(PREV_BLKP(bp)));
		PUT(FTRP(bp), PACK(size, 0));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));

		// 정렬 해줌
		int result = 0;
		while (result == 1)
		{
			result = compare(bp, NEXT(bp));
		}

		bp = PREV_BLKP(bp);
	}

	// case 4 : 앞 뒤 다 free 
	else {
		// 일단 크기 비교
		size_t left_size = GET_SIZE(HDRP(PREV_BLKP(bp)));
		size_t right_size = GET_SIZE(FTRP(NEXT_BLKP(bp)));
		
		if(left_size >= right_size)
		{
			// missing -> right
			void* missing_bp = NEXT_BLKP(bp);
			missing_connect(missing_bp);
		}
		// left size < right_size
		else
		{
			void* missing_bp = PREV_BLKP(bp);
			missing_connect(missing_bp);
			void* prev_bp = GET(PREV(NEXT_BLKP(bp)));
			void* next_bp = GET(NEXT(NEXT_BLKP(bp)));
			
			// 전 블록의 NEXT에 left bp를 넣음
			PUT(NEXT(prev_bp), PREV_BLKP(bp));
			// 현 블록의 PREV에 prev bp를 넣음
			PUT(PREV(PREV_BLKP(bp)), prev_bp);
			// 현 블록의 NEXT에 next bp를 넣음
			PUT(NEXT(PREV_BLKP(bp)), next_bp);
			// 후 블록의 PREV에 left bp를 넣음
			PUT(PREV(next_bp), PREV_BLKP(bp));
		}
		
		size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
		PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
		bp = PREV_BLKP(bp);


		// 정렬 해줌
		int result = 0;
		while (result == 1)
		{
			result = compare(bp, NEXT(bp));
		}
	}

	return bp;
}

/* ----------------------------------- Realloc -------------------------------------*/
void* mm_realloc(void* bp, size_t size)
{
	void* old_dp = bp;
	void* new_dp;
	size_t copySize;
	// 다른데다가 다시 할당 받기
	new_dp = mm_malloc(size);
	// 실패하면 NULL 리턴
	if (new_dp == NULL)	
		return NULL;

	// 원래 블록의 사이즈
	copySize = GET_SIZE(HDRP(old_dp));

	// 요청한 사이즈가 작다면 작은사이즈로 카피
	if (size < copySize)
		copySize = size;
	memcpy(new_dp, old_dp, copySize);
	// 기존 사이즈는 삭제
	mm_free(old_dp);
	return new_dp;
}

/* ----------------------------------- Missing_Connect  -------------------------------------*/
void missing_connect(void *missing_bp)
{
	void *prev_bp = GET(*(PREV(bp)));
	void *next_bp = GET(*(NEXT(bp)));

	PUT(PREV(next_bp), prev_bp);
	PUT(NEXT(prev_bp), next_bp);
	return;
}