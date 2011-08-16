/**
 * This is the standard include file that is included into all Specware generated
 * C sources.
 */

#include <stdint.h>
#include <string.h>
#include <stdio.h>
#include <math.h>

#include "SWC_Memory.h"

#define int_22 int

/* 
 *  BUILT IN TYPES: 
 *
 *    #define void int
 *    typedef char Char_Char;
 *    
 *
 *  BUILT IN OPS: 
 *
 *    Bool_show
 *    Bool_toString
 *
 *    Integer_isucc
 *    Integer_ipred
 *    Integer_show
 *    Integer_toString
 *
 *    Nat_show
 *    Nat_toString
 *
 *    Char_chr
 *    Char_ord
 *    Char_compare
 *
 *    String_length
 *    String_compare
 *    String_append
 *    String_PlusPlus
 *    String_Caret
 *    String_Less
 *    String_newline
 *
 *    Float_one_half
 *    Float_one
 *    Float_two
 *    Float_three
 *    Float_zero
 *    epsilon
 *    Float_abs
 *    unary_float_$
 *    Float_Slash
 *    Float_EqualEqual
 * 
 *    System_writeLine
 *    System_toScreen 
 *
 *    System_fail
 *
 */

/*********************  TYPES  ***************************/

#define void int

/*********************  MEMORY  **************************/

#define New(_TYPE_) swc_malloc(sizeof(_TYPE_))

/*********************  CONSTRUCTORS  ********************/

/*
#define COPRDCTSELSIZE 20
#define SetConstructor(_X_,_SELSTR_) strncpy((_X_).sel,_SELSTR_,COPRDCTSELSIZE)
#define ConstructorEq(_X_,_SELSTR_) (strncmp((_X_).sel,_SELSTR_,COPRDCTSELSIZE)==0)
#define ConstructorArg(_X_,_CONSTR_) (_X_).alt._CONSTR_
#define hasConstructor(_VARNAME_,_CONSTRSTR_) ((strncmp ((_VARNAME_) -> sel, _CONSTRSTR_, COPRDCTSELSIZE)) == 0)
*/

#define SetConstructor(_X_,_N_) (((_X_) -> sel) =  _N_)
#define hasConstructor(_X_,_N_) (((_X_) -> sel) == _N_)

/*********************  BOOLEANS  ************************/

#define FALSE 0
#define TRUE 1

char* Bool_show(int n) {
  char *res = swc_malloc(sizeof(char)*6);
  if (n) {
    strcpy(res,"true");
  } else {
    strcpy(res,"false");
  }
  return res;
}

char* Bool_toString(int n) {
  char *res = swc_malloc(sizeof(char)*6);
  if (n) {
    strcpy(res,"true");
  } else {
    strcpy(res,"false");
  }
  return res;
}

/*********************  COMPARISONS  *********************/

/* temporary hack to avoid compilation issues with comparisons */

typedef struct {
  uint8_t sel;
} COMPSTRUCT;

typedef COMPSTRUCT* COMPARISON;

COMPSTRUCT Comparison__EQ;
COMPSTRUCT Comparison__GT;
COMPSTRUCT Comparison__LT;


/*********************  INTEGERS  ************************/

typedef signed char   s1;	// 8 bits always (standard ANSI C)
typedef int16_t       s2;	// 16 bits (signed), see <stdint.h>
typedef int32_t       s4;	// 32 bits (signed)
typedef int64_t       s8;	// 64 bits (signed)

typedef int Integer_Int0;

/* "+", "-", "*", "div", "rem", "<=", "<", "~", ">", ">=", "**" */

int Integer_isucc (int i) {
  {return (i + 1);}
}

int Integer_ipred (int i) {
  {return (i - 1);}
}

// char* Integer_show(int n) {
//   char buf[12];
//   char *res;
//   sprintf(buf,"%d",n);
//   res = swc_malloc(strlen(buf)+1);
//   strcpy(res,buf);
//   return res;
// }

char* Integer_toString(int n) {
  char buf[12];
  char *res;
  sprintf(buf,"%d",n);
  res = swc_malloc(strlen(buf)+1);
  strcpy(res,buf);
  return res;
}

/*********************  NATS  ****************************/

typedef unsigned char u1;	// 8 bits always (standard ANSI C)
typedef uint16_t      u2;	// 16 bits (unsigned), see <stdint.h>
typedef uint32_t      u4;	// 32 bits (unsigned)
typedef uint64_t      u8;	// 64 bits (unsigned)

#define Nat_show Integer_show
#define Nat_toString Integer_toString

/*********************  LISTS  **************************/

/*********************  CHARACTERS  *********************/

typedef char Char_Char;

#define Char_chr(_Int_)  ((char)_Int_)
#define Char_ord(_Char_) ((uint32_t)_Char_)

COMPARISON Char_compare(char c1, char c2) {
  /* 
   *  TODO:  Would prefer to have the effect of the calls to SetConstructor
   *         built in at compile time, or done once during initialization.
   *
   *  But this is a reasonable workaround...
   */
  if (c1 == c2) {
    SetConstructor(&Comparison__EQ, 1); // "Equal"
    return &Comparison__EQ;}
  else if (c1 > c2) {
    SetConstructor(&Comparison__GT, 2); // "Greater"
    return &Comparison__GT;}
  else {
    SetConstructor(&Comparison__LT, 3); // "Less"
    return &Comparison__LT;
  }
}

/*********************  STRINGS  ************************/

#define String_length strlen

COMPARISON String_compare(char *s1, char *s2) {
  /* 
   *  TODO:  Would prefer to have the effect of the calls to SetConstructor
   *         built in at compile time, or done once during initialization.
   *
   *  But this is a reasonable workaround...
   */
  int n = strcmp (s1, s2);
  if (n == 0) {
    SetConstructor(&Comparison__EQ, 1); // "Equal"
    return &Comparison__EQ;}
  else if (n > 0) {
    SetConstructor(&Comparison__GT, 2); // "Greater"
    return &Comparison__GT;}
  else {
    SetConstructor(&Comparison__LT, 3); // "Less"
    return &Comparison__LT;
  }
}

char* String_append(char *s1, char *s2) {
  char *res = swc_malloc(strlen(s1)+strlen(s2)+1);
  strcpy(res,s1);
  strcpy(res+strlen(s1),s2);
  return res;
}

#define String_PlusPlus String_append
#define String_Caret String_append
#define String_Less strcmp

#define String_newline "\n"

/*********************  FLOATS  *************************/

typedef double Float_Float;

Float_Float Float_one_half = 0.5;
Float_Float Float_one   = 1.0;
Float_Float Float_two   = 2.0;
Float_Float Float_three = 3.0;
Float_Float Float_zero  = 0.0;
Float_Float epsilon     = 3.0e-8;

Float_Float Float_abs (Float_Float x) {
  return (fabs (x));
}

Float_Float unary_float_$ (Float_Float x) {
  return (- x);
}

Float_Float Float_Slash (Float_Float x, Float_Float y) {
  return (x / y);
}

int Float_EqualEqual (Float_Float x, Float_Float y) {
  if (x = y) {
    return 1;
  } else {
    return 0;
  }
}

/*
 * TODO:  ?? What was this doing here ??
 * Float_Float f (Float_Float x) {
 *  return ((34 * x * x * x) - (99.0 * x * x) + (1047 * x) + 12345.0);
 * }
 */

/*********************  IO  *****************************/

void System_writeLine(char *s) {
  printf("%s\n",s);
}

#define System_toScreen System_writeLine

/*********************  ERRORS  *************************/

#define NONEXHAUSTIVEMATCH_ERROR(_FUNNAME_) printf("Nonexhaustive match failure in %s\n",_FUNNAME_)

int _error (char* s) {
  printf ("\n\nError: %s\n\n", s);
  return 0;
}

int System_fail(char* msg) {
  fprintf(stderr,"Error: %s\n",msg);
  exit(1);
}

int TranslationBuiltIn_mkFail (char* msg) {
  fprintf(stderr,"Failure: %s\n",msg);
  exit(1);
}

/*********************  UNQUALIFIED  ********************/

#define Any long long

#define Less      Integer_Less
#define Greater   Integer_Greater

#define Caret     String_Caret

#define writeLine System_writeLine
#define fail      System_fail

#define show      Integer_show
#define toString  Integer_toString


/*********************  ACCORD  *************************/

typedef int Accord_ProcType ();
#define Accord_Object int

/*********************  Pattern Matcher *************************/

int MatchSuccess;
int MatchValue;

#define TranslationBuiltIn_block(form)     (form)
#define TranslationBuiltIn_failWith(aa,bb) ((aa), (char*) (MatchSuccess == TRUE) ? MatchValue : (bb))
#define TranslationBuiltIn_mkSuccess(cc)   (MatchSuccess = TRUE, MatchValue = (int) cc)
#define TranslationBuiltIn_mkBreak         (MatchSuccess = FALSE)
#define TranslationBuiltIn_mkFail(msg)     (MatchSuccess = FALSE)

