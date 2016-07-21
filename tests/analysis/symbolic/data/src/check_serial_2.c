#include <stdio.h>

char *serial = "\x31\x27\x30\x2b\x23\x2e";

int check_serial(char *password, int length) {
    int i = 0;

    while(i < length) {
        if ((password[i] ^ 0x42) != serial[i]) {
            return 0;
        }

        i++;
    }

    return 1;
}

int main(int argc, char *argv[]) {
    int  rv;
    char *password = argv[1];

    rv = check_serial(password, 6);

    if (rv == 0x1) {
        printf("Success!\n");
    } else {
        printf("Fail!\n");
    }

    return 0;
}
