// A toy example to show the benefit of our loopsum implementation based on 
// online symbolic execution.

#include <stdio.h>
#include <stdlib.h>

int input;

void func(int x){
    char str[30];
    int c = 0;
    int var = 0xffffffff;
    while (1){
	if (x <= 0)	/* Guard */
	    break;
	if (x % 2 == 0)
	    c = c + 1; 	/* iv2 */
	else c = c + 2; /* iv2' */
	x = x - 2; 	/* iv1 */
    }

    if (c <= 33){
	str[c] = 0;
    }
}

int main(int argc, char **argv){
    func(input);
    return 0;
}
