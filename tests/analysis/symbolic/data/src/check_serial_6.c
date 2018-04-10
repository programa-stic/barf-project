#include <stdio.h>
#include <stdlib.h>

void expand(unsigned char *out, unsigned char *in, unsigned int x, unsigned int y) {
    for (int i = 0; i < 4; i++) {
        out[i] = (in[i] - x) ^ y;
        x = x << 1;
        y = y << 1;
    }
}

int main(int argc, char *argv[]) {
    unsigned char out[4];
    unsigned char in[4] = {0x2, 0x3, 0x5, 0x7};
    unsigned int x = atoi(argv[1]);
    unsigned int y = atoi(argv[2]);

    expand(out, in, x, y);

    printf("%02hhx\n", (unsigned int) out[0]);
    printf("%02hhx\n", (unsigned int) out[1]);
    printf("%02hhx\n", (unsigned int) out[2]);
    printf("%02hhx\n", (unsigned int) out[3]);

    return 0;
}
