#include <stdio.h>
#include <stdlib.h>

int main(int argc, char * argv[]) {
    unsigned int i;
    unsigned int a;
    unsigned int l;

    if (argc != 2) {
        printf("Usage: %s <iterations>\n", argv[0]);
        exit(-1);
    }

    l = (unsigned int) atoi(argv[1]);

    for (i = 0; i < l; i++) {
        a++;
    }

    printf("Finished!\n");

    return 0;
}
