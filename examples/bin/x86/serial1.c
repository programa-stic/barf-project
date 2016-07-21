#include <stdio.h>
#include <stdlib.h>
#include <string.h>

int main(int argc, char * argv[]) {
    char serial[256];

    if (argc != 2) {
        printf("Usage: %s <serial>\n", argv[0]);
        exit(1);
    }

    /* check length of input */
    size_t serial_len = strlen(argv[1]);

    if (256 <= serial_len) {
        printf("[-] Serial too long.\n");
        exit(1);
    }

    if (3 > serial_len) {
        printf("[-] Serial too short.\n");
        exit(1);
    }

    /* read serial from command line */
    strncpy(serial, argv[1], serial_len);

    /* check serial */
    if (serial[0] != 's') {
        return 0;
    }

    if (serial[1] != 'e') {
        return 0;
    }

    if (serial[2] != 'r') {
        return 0;
    }

    /* tests passed */
    printf("Serial's fine!\n");

    return 0;
}
