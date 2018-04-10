#include <stdio.h>

int check_serial(char *password) {
    int i = 0;

    while(i < 6) {
        if (password[i] != 'A') {
            return 0;
        }

        i++;
    }

    return 1;
}

int main(int argc, char *argv[]) {
    int  rv;
    char *password = argv[1];

    rv = check_serial(password);

    if (rv == 0x1) {
        printf("Success!\n");
    } else {
        printf("Fail!\n");
    }

    return 0;
}
