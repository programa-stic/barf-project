#include <stdio.h>

int main() {
    unsigned int a = 0;
    unsigned int counter = 10;

    while (counter > 0) {
        a++;
        counter--;
    }

    return a;
}