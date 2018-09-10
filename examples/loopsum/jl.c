// An very simple program used as a introducing example in Automatic Partial 
// Loop Summarization in Dynamic Test Generation (ISSTA'11)

#include <stdio.h>
#include <stdlib.h>

// Test loop condition operation jl/jge.
int func(int x){
	int c = 0;
	int p = 0;
	while (1){
		if (x < -10)	/* loop cond 1 */
			break;
		if (c == 50)	/* loop cond i2 */
			return 1; 	/* error1 */
		c = c + 1;	/* IV2 */
		x = x - 1;	/* IV1 */
	}
	if (c == 30)
		return 2; 	/* error 2 */
	else
		return 0;
}

int main(int argc, char **argv){
	int input;
	int res = 0;
	if (argc != 2){
		fprintf(stderr, "Usage: jl <integer>\n");
		exit(-1);
	}
	input = atoi(argv[1]);
	if (input <= 1000){
		res = func(input);
	}
	if (res == 1)
		printf("Error code 1.\n");
	else if(res == 2)
		printf("Error code 2.\n");
	else
		printf("End with normal result.\n");
	return 0;
}
