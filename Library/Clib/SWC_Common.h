/**
 * This is the standard include file that is included into all Specware generated
 * C sources.
 */


#include <stdint.h>
#include <string.h>
#include <stdio.h>
#include <math.h>

#include "SWC_Memory.h"

/* Definitions */

typedef unsigned char u1;	// 8 bits always (standard ANSI C)
typedef uint16_t      u2;	// 16 bits (unsigned), see <stdint.h>
typedef uint32_t      u4;	// 32 bits (unsigned)
typedef uint64_t      u8;	// 64 bits (unsigned)

typedef signed char   s1;	// 8 bits always (standard ANSI C)
typedef int16_t       s2;	// 16 bits (signed), see <stdint.h>
typedef int32_t       s4;	// 32 bits (signed)
typedef int64_t       s8;	// 64 bits (signed)

#define Any long long

#define NONEXHAUSTIVEMATCH_ERROR(_FUNNAME_) printf("Nonexhaustive match failure in %s\n",_FUNNAME_)
#define COPRDCTSELSIZE 20
#define FALSE 0
#define TRUE 1
#define SetConstructor(_X_,_SELSTR_) strncpy((_X_).sel,_SELSTR_,COPRDCTSELSIZE)
#define ConstructorEq(_X_,_SELSTR_) (strncmp((_X_).sel,_SELSTR_,COPRDCTSELSIZE)==0)
#define ConstructorArg(_X_,_CONSTR_) (_X_).alt._CONSTR_

#define New(_TYPE_) swc_malloc(sizeof(_TYPE_))
#define hasConstructor(_VARNAME_,_CONSTRSTR_) ((strncmp ((_VARNAME_) -> sel, _CONSTRSTR_, COPRDCTSELSIZE)) == 0)

/* temporary? hack for Accord */
typedef int Accord_ProcType ();
#define Accord_Object int

#define void int

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

int _error (char* s) {
  printf ("\n\nError: %s\n\n", s);
  return 0;
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

Float_Float f (Float_Float x) {
  return ((34 * x * x * x) - (99.0 * x * x) + (1047 * x) + 12345.0);
    }

/*#define append String_append*/
char* String_append(char *s1, char *s2) {
  char *res = swc_malloc(strlen(s1)+strlen(s2)+1);
  strcpy(res,s1);
  strcpy(res+strlen(s1),s2);
  return res;
}

int String_compare (char *s1, char *s2) {
  return strcmp(s1,s2);
}

int String_Less (char *s1, char *s2) {
  return strcmp(s1,s2);
}

typedef char Char_Char;
int Char_compare(char c1, char c2) {
  return (c1 < c2);
}


#define String_PlusPlus String_append
#define String_Caret String_append
#define Caret String_Caret

#define writeLine System_writeLine
#define System_toScreen System_writeLine
#define String_toScreen System_writeLine
void System_writeLine(char *s) {
  printf("%s\n",s);
}


#define show Integer_show
#define Nat_show Integer_show
char* Integer_show(int n) {
  char buf[12];
  char *res;
  sprintf(buf,"%d",n);
  res = swc_malloc(strlen(buf)+1);
  strcpy(res,buf);
  return res;
}
char* Bool_show(int n) {
  char *res = swc_malloc(sizeof(char)*6);
  if (n) {
    strcpy(res,"true");
  } else {
    strcpy(res,"false");
  }
  return res;
}

#define toString Integer_toString
#define Nat_toString Integer_toString
char* Integer_toString(int n) {
  char buf[12];
  char *res;
  sprintf(buf,"%d",n);
  res = swc_malloc(strlen(buf)+1);
  strcpy(res,buf);
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

#define Less Integer_Less
int Integer_Less(int n, int m) {
  return n<m;
}

#define Greater Integer_Greater
int Integer_Greater(int n, int m) {
  return n>m;
}

int Integer_min (int i, int j) {
  if (i <= j) {return i;} {return j;}
}

int Integer_max (int i, int j) {
  if (i >= j) {return i;} {return j;}
}

int Integer_abs (int i) {
  if (i >= 0) {return i;} {return (- i);}
}

int Integer_isucc (int i) {
  {return (i + 1);}
}

int Integer_ipred (int i) {
  {return (i - 1);}
}

#define fail System_fail
int System_fail(char* msg) {
  fprintf(stderr,"Error: %s\n",msg);
  exit(0);
}
