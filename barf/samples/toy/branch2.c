#include <stdio.h>

int main() {
    int cookie1;
    int cookie2;

    if (cookie1 == 0x41424344) {
        if (cookie2 == 0x45464748) {
            printf("you win!\n");
        }
    }
}