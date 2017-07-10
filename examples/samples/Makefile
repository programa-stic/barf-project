X86_CC = gcc
ARM_CC = arm-linux-gnueabi-gcc

.PHONY: all clean

all: \
	example1 \
	branch1 branch2 branch3 branch4 \
	complex1 \
	constraint1 constraint2 constraint3 \
	gadget1 gadget2 \
	helloworld1 \
	loop1 loop2 \
	serial1 \
	stack1

example1: src/example1.c
	$(X86_CC) -m64 -o bin/example1.x86_64 src/example1.c

branch1: src/branch1.c
	$(X86_CC) -m32 -o bin/branch1.x86 src/branch1.c

branch2: src/branch2.c
	$(X86_CC) -m32 -o bin/branch2.x86 src/branch2.c

branch3: src/branch3.c
	$(X86_CC) -m32 -o bin/branch3.x86 src/branch3.c

branch4: src/branch4.c
	$(X86_CC) -m32 -o bin/branch4.x86 src/branch4.c

complex1: src/complex1.c
	$(X86_CC) -ggdb -m32 -O0 -o bin/complex1.x86 src/complex1.c

constraint1: src/constraint1.c
	$(X86_CC) -m32 -O0 -o bin/constraint1.x86 src/constraint1.c

constraint2: src/constraint2.c
	$(X86_CC) -m32 -O0 -o bin/constraint2.x86 src/constraint2.c

constraint3: src/constraint3.c
	$(X86_CC) -m32 -O0 -o bin/constraint3.x86 src/constraint3.c

gadget1: src/gadget1.asm
	nasm -felf32 src/gadget1.asm -o gadget1.o
	ld -melf_i386 gadget1.o -o bin/gadget1.x86
	rm gadget1.o

gadget2: src/gadget2.asm
	nasm -felf64 src/gadget2.asm -o gadget2.o
	ld gadget2.o -o bin/gadget2.x86
	rm gadget2.o

helloworld1: src/helloworld1.c
	$(X86_CC) -m32 -o bin/helloworld1.x86 src/helloworld1.c

loop1: src/loop1.asm
	nasm -felf32 src/loop1.asm -o loop1.o
	ld -melf_i386 loop1.o -o bin/loop1
	rm loop1.o

loop2: src/loop2.c
	$(X86_CC) -m32 -o bin/loop2.x86 src/loop2.c

serial1: src/serial1.c
	$(X86_CC) -m32 -o bin/serial1.x86 src/serial1.c

stack1: src/stack1.c
	$(X86_CC) -Wformat=0 -Wno-deprecated-declarations -m32 -o bin/stack1.x86 src/stack1.c

clean:
	rm -f bin/example1.*
	rm -f bin/branch1.* bin/branch2.* bin/branch3.* bin/branch4.*
	rm -f bin/complex1.*
	rm -f bin/constraint1.* bin/constraint2.* bin/constraint3.*
	rm -f bin/gadget1.* bin/gadget2.*
	rm -f bin/helloworld1.*
	rm -f bin/loop1.* bin/loop2.*
	rm -f bin/serial1.*
	rm -f bin/stack1.*
