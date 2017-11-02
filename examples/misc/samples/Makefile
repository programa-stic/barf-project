X86_CC = gcc
ARM_CC = arm-linux-gnueabi-gcc

.PHONY: all clean

all: \
	example1 \
	branch4 \
	constraint1 constraint3 \
	loop2

example1: src/example1.c
	$(X86_CC) -m64 -o bin/example1.x86_64 src/example1.c

branch4: src/branch4.c
	$(X86_CC) -m32    -o bin/branch4.x86       src/branch4.c
	$(ARM_CC) -marm   -o bin/branch4.arm       src/branch4.c
	$(ARM_CC) -mthumb -o bin/branch4.arm_thumb src/branch4.c

constraint1: src/constraint1.c
	$(X86_CC) -m32  -O0 -o bin/constraint1.x86 src/constraint1.c
	$(ARM_CC) -marm -O0 -o bin/constraint1.arm src/constraint1.c

constraint3: src/constraint3.c
	$(X86_CC) -m32 -O0 -o bin/constraint3.x86 src/constraint3.c

loop2: src/loop2.c
	$(X86_CC) -m32  -o bin/loop2.x86 src/loop2.c
	$(ARM_CC) -marm -o bin/loop2.arm src/loop2.c

clean:
	rm -f bin/example1.*
	rm -f bin/branch4.*
	rm -f bin/constraint1.* bin/constraint3.*
	rm -f bin/loop2.*
