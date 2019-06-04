/* Runtime library */

# include <stdio.h>
# include <string.h>
# include <stdarg.h>
# include <stdlib.h>
# include <sys/mman.h>
# include <assert.h>
# include <errno.h>

#define NIMPL fprintf (stderr, "Internal error: "			\
		       "function %s at file %s, line %d is not implemented yet", \
		       __func__, __FILE__, __LINE__);			\
  exit(1);

extern void nimpl (void) { NIMPL }

# define STRING_TAG 0x00000001
# define ARRAY_TAG  0x00000003
# define SEXP_TAG   0x00000005

# define LEN(x) ((x & 0xFFFFFFF8) >> 3)
# define TAG(x) (x & 0x00000007)

# define TO_DATA(x) ((data*)((char*)(x)-sizeof(int)))
# define TO_SEXP(x) ((sexp*)((char*)(x)-2*sizeof(int)))

# define UNBOXED(x) ( ((int) (x)) & 0x0001)
# define UNBOX(x)   ( ((int) (x)) >> 1)
# define BOX(x)     ((((int) (x)) << 1) | 0x0001)

//# define LOGGING1
# ifdef LOGGING1
#define LOG1(...) printf (__VA_ARGS__)
# else
#define LOG1(...)
#endif

//# define LOGGING2
# ifdef LOGGING2
#define LOG2(...) printf (__VA_ARGS__)
# else
#define LOG2(...)
#endif

# define LOGGING3
# ifdef LOGGING3
#define LOG3(...) printf (__VA_ARGS__)
# else
#define LOG3(...)
#endif


typedef struct {
  int tag; 
  char contents[0];
} data; 

typedef struct {
  int tag; 
  data contents; 
} sexp; 

extern void* alloc (size_t);

int alloc_by;

extern int Blength (void *p) {
  data *a = (data*) BOX (NULL);
  a = TO_DATA(p);
  return BOX(LEN(a->tag));
}

char* de_hash (int n) {
  static char *chars = (char*) BOX (NULL);
  static char buf[6] = {0,0,0,0,0,0};
  char *p = (char *) BOX (NULL);
  chars =  "_abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNJPQRSTUVWXYZ";
  p = &buf[5];

  *p-- = 0;

  while (n != 0) {
    *p-- = chars [n & 0x003F];
    n = n >> 6;
  }
  
  return ++p;
}

typedef struct {
  char *contents;
  int ptr;
  int len;
} StringBuf;

static StringBuf stringBuf;

# define STRINGBUF_INIT 128

static void createStringBuf () {
  stringBuf.contents = (char*) malloc (STRINGBUF_INIT);
  stringBuf.ptr      = 0;
  stringBuf.len      = STRINGBUF_INIT;
}

static void deleteStringBuf () {
  free (stringBuf.contents);
}

static void extendStringBuf () {
  int len = stringBuf.len << 1;

  stringBuf.contents = (char*) realloc (stringBuf.contents, len);
  stringBuf.len      = len;
}

static void printStringBuf (char *fmt, ...) {
  va_list args    = (va_list) BOX(NULL);
  int     written = 0,
    rest    = 0;
  char   *buf     = (char*) BOX(NULL);

 again:
  va_start (args, fmt);
  buf     = &stringBuf.contents[stringBuf.ptr];
  rest    = stringBuf.len - stringBuf.ptr;
  written = vsnprintf (buf, rest, fmt, args);
  
  if (written >= rest) {
    extendStringBuf ();
    goto again;
  }

  stringBuf.ptr += written;
}

static void printValue (void *p) {
  data *a = (data*) BOX(NULL);
  int i   = BOX(0);
  if (UNBOXED(p)) printStringBuf ("%d", UNBOX(p));
  else {
    a = TO_DATA(p);

    switch (TAG(a->tag)) {      
    case STRING_TAG:
      printStringBuf ("\"%s\"", a->contents);
      break;
      
    case ARRAY_TAG:
      printStringBuf ("[");
      for (i = 0; i < LEN(a->tag); i++) {
        printValue ((void*)((int*) a->contents)[i]);
	if (i != LEN(a->tag) - 1) printStringBuf (", ");
      }
      printStringBuf ("]");
      break;
      
    case SEXP_TAG:
      printStringBuf ("`%s", de_hash (TO_SEXP(p)->tag));
      if (LEN(a->tag)) {
	printStringBuf (" (");
	for (i = 0; i < LEN(a->tag); i++) {
	  printValue ((void*)((int*) a->contents)[i]);
	  if (i != LEN(a->tag) - 1) printStringBuf (", ");
	}
	printStringBuf (")");
      }
      break;
      
    default:
      printStringBuf ("*** invalid tag: %p ***", TAG(a->tag));
    }
  }
}

extern void* Belem (void *p, int i) {
  data *a = (data *) BOX (NULL);
  a = TO_DATA(p);
  i = UNBOX(i);
  
  if (TAG(a->tag) == STRING_TAG) {
    return (void*) BOX(a->contents[i]);
  }
  void* result = (void*) ((int*) a->contents)[i];
  return result;
}

extern void* Bstring (void *p) {
  __pre_gc();
  alloc_by = 1;
  int n   = BOX(0);
  data *r = NULL;

  n = strlen (p);
  r = (data*) alloc (n + 1 + sizeof (int));

  r->tag = STRING_TAG | (n << 3);
  strncpy (r->contents, p, n + 1);

  __post_gc();
  alloc_by = 0;
  return r->contents;
}

extern void* Bstringval (void *p) {
  void *s = (void *) BOX (NULL);

  createStringBuf ();
  printValue (p);

  s = Bstring (stringBuf.contents);
  
  deleteStringBuf ();

  return s;
}

extern void* Barray (int n, ...) {
  __pre_gc();
  alloc_by = 2;
  va_list args = (va_list) BOX (NULL);
  int     i    = BOX(0),
    ai   = BOX(0);
  data    *r   = (data*) BOX (NULL);

  r = (data*) alloc (sizeof(int) * (n+1));

  r->tag = ARRAY_TAG | (n << 3);
  
  va_start(args, n);
  
  for (i = 0; i<n; i++) {
    ai = va_arg(args, int);
    ((int*)r->contents)[i] = ai; 
  }
  
  va_end(args);

  __post_gc();
  alloc_by = 0;
  return r->contents;
}

extern void* Bsexp (int n, ...) {
  __pre_gc();
  alloc_by = 3;
  va_list args = (va_list) BOX (NULL);
  int     i    = BOX(0);
  int     ai   = BOX(0);
  size_t * p   = NULL;
  sexp   *r    = (sexp *) BOX (NULL);
  data   *d    = (data *) BOX (NULL);

  r = (sexp*) alloc (sizeof(int) * (n+1));
  d = &(r->contents);
  r->tag = 0;
    
  d->tag = SEXP_TAG | ((n-1) << 3);
  
  va_start(args, n);
  
  for (i=0; i<n-1; i++) {
    ai = va_arg(args, int);
    
    p = (size_t*) ai;
    ((int*)d->contents)[i] = ai;

    /* LOG3("After some Bsexp code:\n"); */
    /* Ldescribe(); */
  }

  r->tag = va_arg(args, int);
  va_end(args);


  __post_gc();
  alloc_by = 0;
  return d->contents;
}

extern int Btag (void *d, int t, int n) {
  data *r = (data*) BOX (NULL);
  r = TO_DATA(d);
  return BOX(TAG(r->tag) == SEXP_TAG && TO_SEXP(d)->tag == t && LEN(r->tag) == n);
}

extern int Barray_patt (void *d, int n) {
  data *r = BOX(NULL);
  if (UNBOXED(d)) return BOX(0);
  else {
    r = TO_DATA(d);
    return BOX(TAG(r->tag) == ARRAY_TAG && LEN(r->tag) == n);
  }
}

extern int Bstring_patt (void *x, void *y) {
  data *rx = (data *) BOX (NULL),
    *ry = (data *) BOX (NULL);
  if (UNBOXED(x)) return BOX(0);
  else {
    rx = TO_DATA(x); ry = TO_DATA(y);

    if (TAG(rx->tag) != STRING_TAG) return BOX(0);
    
    return BOX(strcmp (rx->contents, ry->contents) == 0 ? 1 : 0);
  }
}

extern int Bboxed_patt (void *x) {
  return BOX(UNBOXED(x) ? 0 : 1);
}

extern int Bunboxed_patt (void *x) {
  return BOX(UNBOXED(x) ? 1 : 0);
}

extern int Barray_tag_patt (void *x) {
  if (UNBOXED(x)) return BOX(0);
  
  return BOX(TAG(TO_DATA(x)->tag) == ARRAY_TAG);
}

extern int Bstring_tag_patt (void *x) {
  if (UNBOXED(x)) return BOX(0);
  
  return BOX(TAG(TO_DATA(x)->tag) == STRING_TAG);
}

extern int Bsexp_tag_patt (void *x) {
  if (UNBOXED(x)) return BOX(0);
  return BOX(TAG(TO_DATA(x)->tag) == SEXP_TAG);
}

extern void Bsta (int n, int v, void *s, ...) {
  va_list args = (va_list) BOX (NULL);
  int i = 0, k = 0;
  data *a = (data*) BOX (NULL);
  
  va_start(args, s);

  for (i = 0; i < n-1; i++) {
    k = UNBOX(va_arg(args, int));
    s = ((int**) s) [k];
  }

  k = UNBOX(va_arg(args, int));
  a = TO_DATA(s);
  
  if (TAG(a->tag) == STRING_TAG)((char*) s)[k] = (char) UNBOX(v);
  else ((int*) s)[k] = v;
}

extern int Lraw (int x) {
  return UNBOX(x);
}

extern void Lprintf (char *s, ...) {
  va_list args = (va_list) BOX (NULL);

  va_start (args, s);
  vprintf  (s, args); // vprintf (char *, va_list) <-> printf (char *, ...) 
  va_end   (args);
}

extern void* Lstrcat (void *a, void *b) {
  data *da = (data*) BOX (NULL);
  data *db = (data*) BOX (NULL);
  data *d  = (data*) BOX (NULL);

  da = TO_DATA(a);
  db = TO_DATA(b);

  d  = (data *) alloc (sizeof(int) + LEN(da->tag) + LEN(db->tag) + 1);

  d->tag = LEN(da->tag) + LEN(db->tag);

  strcpy (d->contents, da->contents);
  strcat (d->contents, db->contents);

  return d->contents;
}

extern void Lfprintf (FILE *f, char *s, ...) {
  va_list args = (va_list) BOX (NULL);

  va_start (args, s);
  vfprintf (f, s, args);
  va_end   (args);
}

extern FILE* Lfopen (char *f, char *m) {
  return fopen (f, m);
}

extern void Lfclose (FILE *f) {
  fclose (f);
}
   
/* Lread is an implementation of the "read" construct */
extern int Lread () {
  int result = BOX(0);

  printf ("> "); 
  fflush (stdout);
  scanf  ("%d", &result);

  return BOX(result);
}

/* Lwrite is an implementation of the "write" construct */
extern int Lwrite (int n) {
  printf ("%d\n", UNBOX(n));
  fflush (stdout);

  return 0;
}

/* ======================================== */
/*         GC: Mark-and-Copy                */
/* ======================================== */

/* Heap is devided on two semi-spaces called active (to-) space and passive (from-) space. */
/* Each space is a continuous memory area (aka pool, see @pool). */
/* Note, it have to be no external fragmentation after garbage collection. */
/* Memory is allocated by function @alloc. */
/* Garbage collection has to be performed by memory allocator if there is not enough space to */
/* allocate the requested size memory area. */

/* The section implements stop-the-world mark-and-copy garbage collection. */
/* Formally, it consists of 4 stages: */
/* 1. Root set constraction */
/* 2. Mark phase */
/*   I.e. marking each reachable from the root set via a chain of pointers object as alive. */
/* 3. Copy */
/*   I.e. copying each alive object from active space into passive space. */
/* 4. Fix pointers. */
/* 5. Swap spaces */
/*   I.e. active space becomes passive and vice versa. */
/* In the implementation, the first four steps are performed together. */
/* Where root can be found in: */
/* 1) Static area. */
/*   Globals @__gc_data_end and @__gc_data_start are used to idenfity the begin and the end */
/*   of the static data area. They are defined while generating X86 code in src/X86.ml */
/*   (function genasm). */
/* 2) Program stack. */
/*   Globals @__gc_stack_bottom and @__gc_stack_top (see runctime/gc_runtime.s) have to be set */
/*   as the begin and the end of program stack or its part where roots can be found. */
/* 3) Traditionally, roots can be also found in registers but our compiler always saves all */
/*   registers on program stack before any external function call. */
/* You have to implement functions that perform traverse static area (@gc_root_scan_data) */
/* and program stack (@__gc_root_scan_stack, see runtime/gc_runtime.s) as well as a function */
/* (@gc_test_and_copy_root) that checks if a word is a valid heap pointer, and, if so, */
/* call copy-function. Copy-function (@gc_copy) has to move an object into passive semi-space, */
/* rest a forward pointer instead of the object, scan object for pointers, call copying */
/* for each found pointer. */

extern size_t __gc_stack_bottom, __gc_stack_top;
// The begin and the end of static area (are specified in src/X86.ml fucntion genasm)
extern const size_t __gc_data_end, __gc_data_start;

// @L__gc_init is defined in runtime/runtime.s
//   it sets up stack bottom and calls init_pool
//   it is called from the main function (see src/X86.ml function genasm)
extern void L__gc_init ();

// You also have to define two functions @__pre_gc and @__post_gc in runtime/gc_runtime.s.
// These auxiliary functions have to be defined in oder to correctly set @__gc_stack_top.
// Note that some of our functions (from runtime.c) activation records can be on top of the
// program stack. These activation records contain usual values and thus we do not have a
// way to distinguish pointers from non-pointers. And some of these values may accidentally be
// equal to pointers into active semi-space but maybe not to the begin of an object.
// Calling @gc_copy on such values leads to undefined behavior.
// Thus, @__gc_stack_top has to point before these activation records. 
// Note, you also have to find a correct place(-s) for @__pre_gc and @__post_gc to be called.
// @__pre_gc  sets up @__gc_stack_top if it is not set yet
extern void __pre_gc  ();
// @__post_gc sets @__gc_stack_top to zero if it was set by the caller
extern void __post_gc ();

/* memory semi-space */
typedef struct {
  void * begin;
  void * end;
  void * current;
  size_t   size;
} pool;

static pool   from_space; // From-space (active ) semi-heap
static pool   to_space;   // To-space   (passive) semi-heap
/* static size_t *current;   // Pointer to the free space begin in active space */

// initial semi-space size
static size_t SPACE_SIZE = 32;
//static size_t SPACE_SIZE = 128;
# define POOL_SIZE (2*SPACE_SIZE)

// swaps active and passive spaces
static void gc_swap_spaces (void) {
  pool tmp = from_space;
  from_space = to_space;
  to_space = tmp;
}

// checks if @p is a valid pointer to the active (from-) space
# define IS_VALID_HEAP_POINTER(p)		\
  (!UNBOXED(p) &&				\
   from_space.begin <= p &&			\
   from_space.end   >=  p)

// checks if @p points to the passive (to-) space
# define IN_PASSIVE_SPACE(p)			\
  (to_space.begin <= p	&&			\
   to_space.end   >=  p)

// chekcs if @p is a forward pointer
# define IS_FORWARD_PTR(p)			\
  (!UNBOXED(p) && IN_PASSIVE_SPACE(p))

/* // @copy_elements */
/* //   1) copies @len words from @from to @where */
/* //   2) calls @gc_copy for those of these words which are valid pointers to from_space */
/* static void copy_elements (size_t *where, size_t *from, int len) { NIMPL } */

static int extend_pool(int new_size){  
  int ptr = mremap(to_space.begin, to_space.size, new_size, 0);
  if (ptr == MAP_FAILED){
    printf("Map failed for new size = %d\n", new_size);
    return 0;
  } else {
    to_space.begin = ptr;
    to_space.size = new_size;
    to_space.end = to_space.begin + to_space.size;
    to_space.current = to_space.begin;
    return 1;
  }
}

// @extend_spaces extends size of to-space before copying from from-space
static void extend_spaces (int required_size) {
  if (to_space.size < required_size){
    int new_size = required_size;
    /* int new_size = to_space.size * 3; */
    if (new_size < required_size){
      printf("Unexpectedly large heap required: %d, expected max %d\n", required_size, new_size);
      exit(1);
    }
    int success = extend_pool(new_size);
    if (!success){
      printf("extend failed\n");
      exit(1);
    } else {
      LOG3("Pool extended: now %p..%p\n", to_space.begin, to_space.end);
    }
  } else {
    to_space.current = to_space.begin;
  }
}

// @init_pool is a memory pools initialization function
//   (is called by L__gc_init from runtime/gc_runtime.s)
extern void init_pool (void) {
  int success = init_one_pool(&from_space) && init_one_pool(&to_space);
  if (!success){
    printf("Pool initialization failed\n");
    exit(1);
  }  
}

int init_one_pool(pool *p){
  p->begin = mmap(NULL, SPACE_SIZE, PROT_READ | PROT_WRITE,
		  MAP_PRIVATE | MAP_32BIT | MAP_ANONYMOUS, 0, 0);
  if (p->begin == MAP_FAILED){
    return 0;
  }
  p->current = p->begin;
  p->size = SPACE_SIZE;
  p->end = p->begin + p->size;
  p->current = p->begin;
  return 1;
}

// @free_pool frees memory pool p
static int free_pool (pool * p) {
  munmap(p->begin, p->size);
}

// copy to passive, update passive's current, keep forward pointer in active
// assume that ptrFrom points to active 
static void* copyObject(void* ptrFrom, size_t size, size_t fpShift){
  void* target = to_space.current;
  int curValue = *(int*)ptrFrom;
  if (IS_FORWARD_PTR(curValue)){
    LOG3("Copying forward pointer from %p\n", ptrFrom);
    memcpy(target, ptrFrom, 1*sizeof(int));
    to_space.current += 1*sizeof(int);
  } else {
    LOG3("Copying %p..%p to %p..%p (size=%d)\n", ptrFrom, ptrFrom+size, target, target+size, size);
    void* ptrTo = memcpy(target, ptrFrom, size);
    to_space.current += size;
    //*((void**)(ptrFrom+fpShift)) = ptrTo+fpShift;
    *((void**)(ptrFrom)) = ptrTo + fpShift;
  }
  
}

static void processRegion (void* ptrFrom, void* ptrTo, int depth){
  void *address;
  for (address = ptrFrom; address < ptrTo;  address += sizeof(int)){
    LOG1("%0*cAt %p: ", depth, ' ', address);
    int value = *((int*)address);
    if (!UNBOXED(value)){
      if (IS_VALID_HEAP_POINTER(value)){	
	data* ptr = TO_DATA(value);
	int tag = TAG(ptr->tag);
	int blockSize;
	LOG1("Pointer, tag = %d", tag);
	if (tag == STRING_TAG){
	  LOG1(", str: %s\n", ptr->contents);
	  int strSize = sizeof(int)+1+strlen(ptr->contents);
	  copyObject(ptr, strSize, 1*sizeof(int));
	} else if (tag == ARRAY_TAG){
	  int size = LEN(ptr->tag);	
	  LOG1(", size: %d\n", size);
	  int arrSize = sizeof(int) * (size + 1);
	  copyObject((void*)ptr, arrSize, 1*sizeof(int));
	  processRegion(ptr->contents, ptr->contents + sizeof(int)*size, depth+1);
	} else if (tag == SEXP_TAG){
	  sexp* se = TO_SEXP(value);
	  int size = LEN(ptr->tag);
	  LOG1(", ptr->%p, size: %d, taghash: %d\n", se, size, se->tag);
	  int sexpSize = sizeof(int) * (size + 2);
	  LOG3("will copy sexp of size %d from %p\n", size, (void*)se);
	  copyObject((void*)se, sexpSize, 2*sizeof(int));
	  LOG3("after copying sexp from %p:\n", (void*)se);
	  Ldescribe();
	  processRegion(ptr->contents, ptr->contents + sizeof(int)*size, depth+1);
	}
      } else {
	LOG1("Neither value nor pointer\n");
      }
    } else {
      LOG1("Non-ptr, unboxed = %d\n", UNBOX(value));
    }
  }
}

// @gc performs stop-the-world mark-and-copy garbage collection
//   and extends pools (i.e. calls @extend_spaces) if necessarily
// @size is a size of the block that @alloc failed to allocate
// returns a pointer the new free block
// I.e.
//   1) call @gc_root_scan_data (finds roots in static memory
//        and calls @gc_test_and_copy_root for each found root)
//   2) call @__gc_root_scan_stack (finds roots in program stack
//        and calls @gc_test_and_copy_root for each found root)
/* static void * gc (size_t size) { */
static void * gc () {
  LOG1("%%%%%%%%%%%%%%%%%%%%\n");
  LOG1("Static data block: %p..%p\n", &__gc_data_start, &__gc_data_end);
  processRegion(&__gc_data_start, &__gc_data_end, 1);
  LOG1("Stack: %p..%p\n", __gc_stack_bottom, __gc_stack_top);
  // stack bounds are set up at this moment
  processRegion(__gc_stack_top, __gc_stack_bottom, 1);
  LOG1("====================\n");
}

static int countRegionSpace (void* ptrFrom, void* ptrTo, int depth){
  void *address;
  int regionSpace = 0;
  /* if (depth <= 3){ */
  /*   LOG3("%0*cCounting space at %p..%p\n", depth, ' ', ptrFrom, ptrTo); */
  /* } */
  for (address = ptrFrom; address < ptrTo;  address += sizeof(int)){
    int value = *((int*)address);
    if (IS_VALID_HEAP_POINTER(value)){	
      data* ptr = TO_DATA(value);
      int tag = TAG(ptr->tag);
      if (tag == STRING_TAG){
	int strSize = sizeof(int)+1+strlen(ptr->contents);
	regionSpace += strSize;
      } else if (tag == ARRAY_TAG){
	int size = LEN(ptr->tag);	
	int arrSize = sizeof(int) * (size + 1);
	regionSpace += arrSize + countRegionSpace(ptr->contents, ptr->contents + sizeof(int)*size, depth+1);
      } else if (tag == SEXP_TAG){
	sexp* se = TO_SEXP(value);
	int size = LEN(ptr->tag);
	int sexpSize = sizeof(int) * (size + 2);
	regionSpace += sexpSize + countRegionSpace(ptr->contents, ptr->contents + sizeof(int)*size, depth+1);
      }
    }
  }
  return regionSpace;
}


static int countActiveSpace(){
  // may count more space than is actually used since it may account a pointer multiple times
  int spaceUsed = 0;
  spaceUsed += countRegionSpace(&__gc_data_start, &__gc_data_end, 1);
  // stack bounds are set up at this moment
  spaceUsed += countRegionSpace(__gc_stack_top, __gc_stack_bottom, 1);
  return spaceUsed;
}

static int updateRegionPointers(void* ptrFrom, void* ptrTo){
  /* LOG3("  updating in %p..%p\n", ptrFrom, ptrTo);   */
  void *address;
  for (address = ptrFrom; address < ptrTo;  address += sizeof(int)){
    int value = *((int*)address);
    if (IS_VALID_HEAP_POINTER(value)){
      void* possibleFpr = ((void*)value) - 1*sizeof(int);
      int ptr = *(int*)possibleFpr;
      if (IS_FORWARD_PTR(ptr)){
	*(int*)address = ptr;
      } else {
	possibleFpr -= 1*sizeof(int);
	ptr = *(int*)possibleFpr;
	if (IS_FORWARD_PTR(ptr)){
	  *(int*)address = ptr;
	}
      }
    }

    /* int value = *((int*)address); */
    /* while (IS_VALID_HEAP_POINTER(value)){ */
    /*   value = *((int*)value); */
    /* } */
    /* if (IS_FORWARD_PTR(value)){ */
    /*   int nextValue = *((int*)value); */
    /*   while (IS_FORWARD_PTR(nextValue)){ */
    /* 	value = nextValue; */
    /* 	nextValue = *((int*)value); */
    /* 	if (nextValue == value){ */
    /* 	  break; */
    /* 	} */
    /*   } */
    /*   //LOG3("Found FP at %p\n", address); */
    /*   *(int*)address = value; */
    /* } else { */
    /*   //LOG3("Found ? at %p\n", address); */
    /* } */


    
    /* int value = address; */
    /* int nextValue = *((int*)value); */
    /* while (IS_VALID_HEAP_POINTER(nextValue) || IS_FORWARD_PTR(nextValue)){ */
    /*   value = nextValue; */
    /*   nextValue = *((int*)value); */
    /* } */
    /* if (IS_FORWARD_PTR(value)){ */
    /*   //LOG3("Found FP at %p\n", address); */
    /*   *(int*)address = value; */
    /* } else { */
    /*   //LOG3("Found ? at %p\n", address); */
    /* } */
  }
}

static void updatePointers(){
  /* LOG3("urp passive...\n"); */
  updateRegionPointers(to_space.begin, to_space.current);
  /* LOG3("data...\n"); */
  updateRegionPointers(&__gc_data_start, &__gc_data_end);
  /* LOG3("stack ...\n");   */
  updateRegionPointers(__gc_stack_top, __gc_stack_bottom);
  /* LOG3("finished urp..\n"); */
  /* LOG3("urp active...\n"); */
  /* updateRegionPointers(from_space.begin, from_space.current); */
}


// @alloc allocates @size memory words
//   it enaibles garbage collection if out-of-memory,
//   i.e. calls @gc when @current + @size > @from_space.end
// returns a pointer to the allocated block of size @size
extern void * alloc (size_t size) {
  // called by string (+cat), array, sexp
  LOG2("before: %d, used: %d, needed: %d\n", from_space.size, from_space.current - from_space.begin, size);  
  if (from_space.current + size >= from_space.end){
    LOG2("Active pool space exhausted, calling gc\n");
    LOG3("GC called: before: %d, used: %d, needed: %d\n", from_space.size, from_space.current - from_space.begin, size);
    int requiredSize = countActiveSpace() + size;
    extend_spaces(requiredSize);
    LOG3("before gc:\n");
    Ldescribe();
    gc();
    LOG3("after gc:\n");
    Ldescribe();
    updatePointers();
    gc_swap_spaces();
    /* LOG3("after swap:\n"); */
    /* Ldescribe(); */
  } else {
    LOG2("Successfully allocated\n");
  }
  LOG2("after: %d\n", from_space.size);
  void* address = from_space.current;
  LOG3("allocating at %p, raw = %d\n", address, (int)address);
  from_space.current += size;
  /* LOG3("after allocation:\n"); */
  /* Ldescribe(); */
  return address;
}

static void describeRegion (void* ptrFrom, void* ptrTo, int depth){
  void *address = ptrFrom;
  for (address = ptrFrom; address < ptrTo; address += sizeof(int)){
    LOG3("@ %p, ", address);
    int value = *((int*)address);
    if (!UNBOXED(value)){
      void* ptr = (void*)value;
      if (IS_VALID_HEAP_POINTER(ptr)){
	LOG3("Pointer to %p\n", ptr);
      } else if (IS_FORWARD_PTR(ptr)){
	LOG3("FP to %p\n", ptr);
      } else {
	LOG3("?; raw = %d\n", value);
      }
    } else {
      LOG3("Non-ptr, raw = %d, unboxed = %d\n", value, UNBOX(value));
    }
  }
}


extern void Ldescribe () {
  static int counter;
  __pre_gc();
  LOG3("++++++++++++++++++++ %d\n", counter);
  LOG3("Active semiheap: %p..%p, passive semiheap: %p..%p\n", from_space.begin, from_space.end, to_space.begin, to_space.end);
  LOG3("Static data block: %p..%p\n", &__gc_data_start, &__gc_data_end);
  describeRegion(&__gc_data_start, &__gc_data_end, 1);
  LOG3("Stack: %p..%p\n", __gc_stack_bottom, __gc_stack_top);
  // stack bounds are set up at this moment
  describeRegion(__gc_stack_top, __gc_stack_bottom, 1);
  LOG3("Active semiheap:\n", from_space.begin, from_space.current);
  describeRegion(from_space.begin, from_space.current, 1);
  LOG3("Passive semiheap:\n", to_space.begin, to_space.current);
  describeRegion(to_space.begin, to_space.current, 1);
  LOG3("^^^^^^^^^^^^^^^^^^^^ %d\n", counter++);
  __post_gc();
}
