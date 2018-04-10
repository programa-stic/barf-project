#include <stdio.h>
#include <sys/types.h>
#include <unistd.h>

/*
 * Basic sample, one function calling two other functions.
 *
 */

void func_1(void) {
    printf("func_1\n");
}

void func_2(void) {
    printf("func_2\n");
}

int main(int argc, char *argv[]) {
    if (getpid() & 0x1) {
        func_1();
    } else {
        func_2();
    }

    return 0;
}
