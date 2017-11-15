X86_CC = gcc
ARM_CC = arm-linux-gnueabi-gcc

.PHONY: all clean

all: loop-simple

loop-simple: src/loop-simple.c
	$(X86_CC) -m32    -o bin/loop-simple.x86       src/loop-simple.c
	$(X86_CC) -m64    -o bin/loop-simple.x86_64    src/loop-simple.c
	$(ARM_CC) -marm   -o bin/loop-simple.arm       src/loop-simple.c
	$(ARM_CC) -mthumb -o bin/loop-simple.arm_thumb src/loop-simple.c

clean:
	rm -f bin/loop-simple.*
