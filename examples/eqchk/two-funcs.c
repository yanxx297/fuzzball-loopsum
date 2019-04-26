#include <stdio.h>
#include <stdlib.h>
#include "funcs.h"

int fnum;
long f1(long a, long b, long c, long d, long e, long f) {
  return (funcs[fnum].fptr)(a, b, c, d, e, f);
}

long f2(long a, long b, long c, long d, long e, long f) {
  return (funcs[fnum].fptr)(a, b, c, d, e, f);
}

int compare(long *r1p, long *r2p,
	    long a0, long a1, long a2, long a3, long a4, long a5) {
  printf("Starting f1\n");  
  fflush(stdout);
  long r1 = f1(a0, a1, a2, a3, a4, a5);
  printf("Completed f1\n");
  fflush(stdout);
  printf("Starting f2\n");
  fflush(stdout);
  long r2 = f2(a0, a1, a2, a3, a4, a5);
  printf("Completed f2\n");
  fflush(stdout);
  if (r1==r2) {
    printf("Match\n");
  } else {
    printf("Mismatch\n");
  }
  fflush(stdout);
  return r1 == r2;
}

long global_arg0, global_arg1, global_arg2,
    global_arg3, global_arg4, global_arg5;

void fuzz_start() {}

void print_usage_and_exit() {
  fprintf(stderr, "Usage: two-funcs <fnum between 0 and %d> \n", num_funcs);
  exit(1);
}

int main(int argc, char **argv) {
  if (argc < 2) print_usage_and_exit();
  fnum = atoi(argv[1]);
  if (fnum >= num_funcs || fnum < 0) print_usage_and_exit();
  fuzz_start();

  compare(0, 0,
	  global_arg0, global_arg1, global_arg2,
	  global_arg3, global_arg4, global_arg5);
  return 0;
}
