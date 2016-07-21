#include <stdio.h>

char *serial = "\x31\x27\x30\x2b\x23\x2e";

typedef int (*compare_fn)(char *);

int compare_byte_0(char *password) {
    return  ((password[0] ^ 0x42) != serial[0]);
}

int compare_byte_1(char *password) {
    return  ((password[1] ^ 0x42) != serial[1]);
}

int compare_byte_2(char *password) {
    return  ((password[2] ^ 0x42) != serial[2]);
}

int compare_byte_3(char *password) {
    return  ((password[3] ^ 0x42) != serial[3]);
}

int compare_byte_4(char *password) {
    return  ((password[4] ^ 0x42) != serial[4]);
}

int compare_byte_5(char *password) {
    return  ((password[5] ^ 0x42) != serial[5]);
}

int check_serial(char *password, int length) {
    int i = 0;

    compare_fn compare_table[6] = {
        compare_byte_0,
        compare_byte_1,
        compare_byte_2,
        compare_byte_3,
        compare_byte_4,
        compare_byte_5,
    };

    while(i < length) {
        if (compare_table[i](password)) {
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
