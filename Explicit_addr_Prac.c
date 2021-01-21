/*
 * EXPLICIT - Address ������ ����
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

// [bytes] extend heap by this amount �ϳ��� �������� 4[kb]
#define CHUNKSIZE (1 << 12)

// max �� ��ȯ
#define MAX(x, y) ((x) > (y) ? (x) : (y))

// size ���� 000 ������ allocation ���θ� ������ ��Ʈ�� ��ȯ
#define PACK(size, alloc) ((size) | (alloc))

// �ּҰ����� �� �о��
#define GET(p) (*(unsigned int *)(p))

// �ּҰ����� �� ��
#define PUT(p, val) (*(unsigned int *)(p) = (val))

// ��� ������ �о��
#define GET_SIZE(p) (GET(p) & ~0x7)

// �Ҵ� ���θ� �о��
#define GET_ALLOC(p) (GET(p) & 0x1)

//bp = block pointer
// ����� �ּҰ��� ��ȯ
#define HDRP(bp) ((char *)(bp)-WSIZE)

// Ǫ���� �ּҰ��� ��ȯ, ������� ����� �� ���� double word�� ����.
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

// �ش� ��Ͽ�

//blkp = block pointer
// ���� ����� �ּҰ��� ��ȯ, ������� �� ������ �����ְ� word�� ����.
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp)-WSIZE)))
// �� ����� �ּҰ��� ��ȯ, ������� double word�� ���� �� ����� ����� �˾Ƴ���.
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp)-DSIZE)))

//***** �ٷ� �� ��ũ���� NEXT_BLKP, PREV_BLKP�� ���� �̸��� ȥ���� �� �����ϴ�. ���� ������ NEXT_FREEBLKP �Ǵ� PRED, SUCC ������ ����� ������ �� �����ϴ�!
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
//***** �����Ͱ� ���� �����ؼ� ���䰡 ������ �Ǿ��� �� �𸣰ڳ׿� ��.. 
//***** ��ü������ �ڵ尡 ���� ����� �� �����ϴ�. ���ֽ��ϴ�! 
//***** �̵� �ڵ� ���� �ѹ� ������ ���ڽ��ϴ�. ���� �����̽��ϴ�~ 

// prev�� next�� ���Ƿ� Prologue Block�� 4word ��ġ�Ѵ�.
int mm_init(void)
{   
    //***** �� �κ��� ���� �ٸ��� �����ϼż� Ȥ�� ���� �߸� �����ϰ� ������ �������ֽø� �����ϰڽ��ϴ�!
    //***** ���� ���� ����Ʈ�� ó���� �� �κп� �̸� prologue, epilogue����� �־ �����ڸ� ������ �Ű� �Ƚᵵ �ǰ� ����� �� ������ ���̵� ���� �� �����ϴ�. 

    //***** �� 9W�� request�ؾ��ϴ� �� ������ 5W�� request�ϴ� �� �����ϴ�. 
    //***** �Ʒ� 5 * WSIZE�� 9 * WSIZE�� �ٲ�ôµ� seg fault�� �߳׿�.. 
    //***** ����� Ȧ�� ���� W�� �Ҵ������ �ּҰ� �������� ������ �ȵ� ���� ���� �� �����ϴ�. ���ѷα� ��� �տ� �е��� ���ּ� ¦�� ���� ���� �� ���� �� �����ϴ�. 

    // mem_sbrk ȣ���ؼ� 9W �޸� request�ϴ� ��, ���� �ϸ� -1 ����
    if ((heap_listp = mem_sbrk(5 * WSIZE)) == (void *)-1)
    {
        return -1;
    }

    /* ------------------- Prologue ------------------ */
    PUT(heap_listp, 0);

    // heap:0�� DSIZE�� allocated ���� (PROLOGUE HEADER)
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE * 2, 1));

    // heap:1���� PREV�� ����.
    // Prologue �̹Ƿ� PREV�� NULL�� ���ش�.
    PUT(heap_listp + (2 * WSIZE), NULL);

    // heap:2���� NEXT�� ����.
    PUT(heap_listp + (3 * WSIZE), heap_listp + (6 * WSIZE));

    // heap:3���� FOOTER�� ����.
    PUT(heap_listp + (4 * WSIZE), PACK(DSIZE * 2, 1));


    ///***** ������ 5W��ŭ �Ҵ��� �޾����� �Ʒ� epilogue ������ �Ҵ��� ���� ���� ������ ���� �ְ� �ִ� �� �����ϴ�. 

    /* ------------------- Epilogue ------------------ */
    // heap:4�� DSIZE�� allocated ���� (PROLOGUE HEADER)
    PUT(heap_listp + (5 * WSIZE), PACK(DSIZE * 2, 1));

    // heap:5���� PREV�� ����.
    PUT(heap_listp + (6 * WSIZE), heap_listp + 2 * WSIZE);

    // Epilogue �̹Ƿ� NEXT�� NULL�� ���ش�.
    // heap:6���� NEXT�� ����.
    PUT(heap_listp + (7 * WSIZE), NULL);

    // heap:7���� FOOTER�� ����.
    PUT(heap_listp + (8 * WSIZE), PACK(DSIZE * 2, 1));

    // heap_lisp �����͸� �Ű���
    heap_listp += DSIZE;

    // chunk size Ȯ��(������ �ִ� ����������)??
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
    // ¦���� ����
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    // �ʹ� Ŀ�� �Ҵ� �������� return -1
    
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;
    // printf("sbrk, bp = %p\n", bp);
    // ���� bp�� ���� ����� �� ó���̹Ƿ� �ش� ����� bp�ڸ��� �Ű��ش�
    bp = bp + 4;

    // block header free
    PUT(HDRP(bp), PACK(size, 0));
    // block putter free
    PUT(FTRP(bp), PACK(size, 0));

    void* last_free = GET(PREV(bp));

    //***** size ��ŭ�� �޸𸮸� �Ҵ� �޾Ƽ� size��ŭ �� ä���ָ� ���ο� epligue ����� ���� ������ ���� �� ������ ��.. �̵� ���� ������ ���ڽ��ϴ�~
    // ���ο� epilogue ��ġ
    void *EBP = NEXT_BLKP(bp);
    PUT(HDRP(EBP), PACK(DSIZE * 2, 1));
    PUT(PREV(EBP), last_free);
    PUT(NEXT(EBP), NULL);
    PUT(FTRP(EBP), PACK(DSIZE * 2, 1));
    // extend�� �����ߴٴ� ����, extend size���� ū ����� ���ٴ� ���̴�.
    PUT(NEXT(last_free), EBP);
    PUT(PREV(bp), 0);
    PUT(NEXT(bp), 0);

    // ���� �� block�� �������ٸ� ��ģ��.
    // return coalesce(bp);
    return coalesce(bp);
}

/* ----------------------------------- Malloc -------------------------------------*/
void *mm_malloc(size_t size)
{
    // printf("malloc----------------------------------------------------------------------------------\n");
    // printf("size needed:%d\n",size);
    // ������ size
    size_t asize;
    // ���� chunksize�� �ѱ� ������
    size_t extendsize;
    char *bp;
    // ���� �Է¹��� ����� 0 �̸� ����
    if (size == 0)
        return NULL;

    // ���� �Է¹��� ����� dsize���� �۾Ƶ� 4size�� ����
    if (size <= DSIZE)
        asize = 2 * DSIZE;

    // 2�� ���(Dsize)�� ����
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);
    // �� free ����� �ִٸ� �־��ش�.
    if ((bp = find_fit(asize)) != NULL)
    {
        Cut_Connection(bp);
        place(bp, asize);
        // printf("malloc_bp:%p, bp_value:%d\n", bp, GET(bp));
        return bp;
    }

    // ���� chunksize�� �ѱ� ��������
    extendsize = MAX(asize, CHUNKSIZE);
    // �ѱ� �����ŭ�� ���� �Ҵ����
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
    // bp ó������ ��ϴ����� for�� 0(epilogue)
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
    // ����� ����� �о��
    size_t csize = GET_SIZE(HDRP(bp));
    // printf("csize:%d\n", csize);
    // prev, next�� �ʿ��ϹǷ� �ּ� �и� ����� 6���� ���ش�.
    // �����ϰ� �ڸ��� ������ SPLIT ���ش�.
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
        // prologue�� ���� ���� ��Ϻ��� �����Ѵ�.
        void *next_bp = compare(bp, GET(NEXT(heap_listp)));
        Insert_Block(bp, next_bp);
    }
    // �� �´´ٸ� �׳� �־��ش�.
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
    // ����� ����� �о��
    size_t size = GET_SIZE(HDRP(bp));

    // ����� free �Է�
    PUT(HDRP(bp), PACK(size, 0));
    // Ǫ�Ϳ� free �Է�
    PUT(FTRP(bp), PACK(size, 0));
    PUT(PREV(bp), 0);
    PUT(NEXT(bp), 0);

    // coalesce �����ְ� ���յ� ���� ����� bp �޾ƿ�
    void *new_bp = coalesce(bp);
}

//***** �Լ����� ������ ����ϰ� �� ¥�ô� �� �����ϴ�! �Ѽ� ���� ���ϴ�.
// compare�� ��ȯ�� ����� ũ��� ���� ����Ʈ ���� ��ϰ� ���Ѵ�.
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

    // ���� �ڸ��� next_bp�� �´ٴ� ���̴�
    return next_bp;
}

//***** ���Ḯ��Ʈ�� �� �ڿ� �̸� ����� �־�ξ �׷��� ������ ����ϳ׿�. 
// ���ο� ���� ����� next_bp�� PREV�� �̾��ֱ� ���� �۾�. 
void Insert_Block(void *new_bp, void *next_bp)
{
    // printf("Insert Block, new_bp: %p, next_bp : %p\n", new_bp, next_bp);
    // �켱 next_bp�� prev_bp�� �޾ƿ´�.
    void *prev_bp = GET(PREV(next_bp));

    // 1. �� ����� next�� �� ������� �̾��ش�.
    PUT(NEXT(prev_bp), new_bp);

    // 2. �� ����� next�� �� ������� �̾��ش�.
    PUT(NEXT(new_bp), next_bp);

    // 3. �� ����� prev�� �� ������� �̾��ش�.
    PUT(PREV(next_bp), new_bp);

    // 4. �� ����� prev�� �� ������� �̾��ش�.
    PUT(PREV(new_bp), prev_bp);

    // 5. �� ����� pb�� ���� ����� pb�� �ٲ��ش�.
    // -> �ʿ� ����. �����δ� �� ����� �̵��ϴ� ���� �ƴϱ⶧��
}

/* ----------------------------------- Coalesce -------------------------------------*/
// explicit������ prev, next�� �̾���� �ϹǷ� �����͸� ��ȯ�ϵ��� �Ѵ�.
static void *coalesce(void *bp)
{
    // printf("coal, bp : %p\n", bp);
    // ���� ����� alloc �ΰ�
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    // ���� ����� alloc �ΰ�
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    // ���� ����� ������
    size_t size = GET_SIZE(HDRP(bp));

    // case 1 : ��, �� ��� �Ҵ� ������ ��,	���վ��� ��ȯ
    if (prev_alloc && next_alloc)
    {
        // printf("coal:no free\n");
        PUT(PREV(bp), 0);
        PUT(NEXT(bp), 0);
        PUT(NEXT(bp), GET(NEXT(heap_listp)));
    }

    // case 2 : ���� ����� ���� ������ �� :
    else if (prev_alloc && !next_alloc)
    {
        // printf("coal:right_free\n");
        // ���� ����� prev�� next ������ �����Ѵ�.
        void *right_bp = NEXT_BLKP(bp);
        // void *old_prev = GET(PREV(right_bp));
        // void *old_next = GET(NEXT(right_bp));
        Cut_Connection(right_bp);

        // ���� ����� ��������� ���ļ� free��Ŵ
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));

        // ��� ���� ����
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(PREV(bp), 0);
        PUT(NEXT(bp), 0);
        // PUT(PREV(bp), old_prev);
        PUT(NEXT(bp), GET(NEXT(heap_listp)));
    }

    // case 3 : ���� ��ϸ� ���� ����� ��,
    // ���� ��������� ���ļ� free��Ŵ
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

    // case 4 : �� �� �� free
    else
    {
        // printf("coal:both free\n");
        // �ϴ� ũ�� ��
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
    // �ٸ����ٰ� �ٽ� �Ҵ� �ޱ�
    new_bp = mm_malloc(size);
    // �����ϸ� NULL ����
    if (new_bp == NULL)
        return NULL;

    // ���� ����� ������
    copySize = GET_SIZE(HDRP(old_bp));

    // ��û�� ����� �۴ٸ� ����������� ī��
    if (size < copySize)
        copySize = size;
    memcpy(new_bp, old_bp, copySize);
    // ���� ������� ����
    mm_free(old_bp);
    return new_bp;
}

/* ----------------------------------- Missing_Connect  -------------------------------------*/
// bp�� ��� PREV, NEXT�� �����ְ�, PREV ��ϰ� NEXT ����� �̾��ش�.
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