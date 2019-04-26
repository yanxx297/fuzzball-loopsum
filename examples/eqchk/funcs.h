#ifndef _FUNCS_H
#define _FUNCS_H

#include <stdbool.h>

int _f0(int x, unsigned y) { return (x << 1) + (y % 2);}

int _f1(bool x) { return x ? 0 : 1; }

int input_dependent(int x){
  int c = 0;
  int p = 0;
  while (1){
    if (x <= 0)	/* loop cond 1 */
      break;
    if (c == 50) 	/* loop cond i2 */
      return 1;	/* error1 */
    c = c + 1; 	/* IV2 */
    x = x - 1; 	/* IV1 */
		/* loop summarization doesn't work if the non-IV bellow exist */
		//p = p + c;
  }
  if (c == 30)
    return 2; 	/* error 2 */
  else
    return 0;
}

typedef long (func)(long, long, long, long, long, long);
struct func_info {
  const char *fname;
  func *fptr;
  int num_args;
  int is_varargs;
  int is_voidret;
};

int num_funcs = 3;
struct func_info funcs[] = {
    /*    0 */ {"_f0", (func*)&_f0, 2, 0, 0},
    /*    1 */ {"_f1", (func*)&_f1, 1, 0, 0},
    /*    2 */ {"input_dependent", (func*)&input_dependent, 1, 0, 0},
};
#endif
