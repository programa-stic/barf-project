#include <stdio.h>

char *serial = "\x31\x27\x30\x2b\x23\x2e";

int compare_byte(char *a, char *b) {
    return  ((a[0] ^ 0x42) != b[0]);
}

int check_serial(char *password, int length, int (*compare_fn)(char *, char *)) {
    int i = 0;

    while(i < length) {
        if (compare_fn(&password[i], &serial[i])) {
            return 0;
        }

        i++;
    }

    return 1;
}

int main(int argc, char *argv[]) {
    int  rv;
    char *password = argv[1];

    rv = check_serial(password, 6, compare_byte);

    if (rv == 0x1) {
        printf("Success!\n");
    } else {
        printf("Fail!\n");
    }

    return 0;
}
