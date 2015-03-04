#include <stdio.h>

int main() {
    int cookie1;
    int cookie2;
    int cookie3;
    int rv = 1;

    if (cookie1 == 0x41424344) {
        if (cookie2 == 0x45464748) {
            if (cookie3 == 0x00ABCDEF) {
                rv = 0;
            }
        }
    }

    return rv;
}