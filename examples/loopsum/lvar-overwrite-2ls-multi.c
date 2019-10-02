// A toy example to show the benefit of our loopsum implementation based on 
// online symbolic execution.
// Designed to test context awareness

#include <stdio.h>
#include <stdlib.h>

int input;

int func(int x){
    char str[30];
    int c = 0;
    int res = 0; 
    int var = 0xffffffff;
    while (1){
	if (x <= 0)	/* Guard */
	    break;
	if (x % 2 == 0)
	    c = c + 1; 	/* iv2 */
	else c = c + 2; /* iv2' */
	x = x - 2; 	/* iv1 */
	res += 1;
    }

    if (c <= 33){
	str[c] = 0;
    }

    return res;
}

int main(int argc, char **argv){
    int res = func(input);
    func(res);
    return 0;
}
