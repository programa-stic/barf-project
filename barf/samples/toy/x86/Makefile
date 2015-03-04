CC = gcc

.PHONY: all clean

all: branch1 branch2 branch3 branch4 complex1 constraint1 constraint2 \
	constraint3 helloworld1 gadget1 gadget2 serial1 stack1 loop1 loop2

branch1: branch1.c
	$(CC) -m32 -o branch1 branch1.c

branch2: branch2.c
	$(CC) -m32 -o branch2 branch2.c

branch3: branch3.c
	$(CC) -m32 -o branch3 branch3.c

branch4: branch4.c
	$(CC) -o branch4 branch4.c

complex1: complex1.c
	$(CC) -ggdb -m32 -O0 -o complex1 complex1.c

constraint1: constraint1.c
	$(CC) -m32 -O0 -o constraint1 constraint1.c

constraint2: constraint2.c
	$(CC) -m32 -O0 -o constraint2 constraint2.c

constraint3: constraint3.c
	$(CC) -m32 -O0 -o constraint3 constraint3.c

helloworld1: helloworld1.c
	$(CC) -m32 -o helloworld1 helloworld1.c

gadget1: gadget1.asm
	nasm -felf32 gadget1.asm -o gadget1.o
	ld -melf_i386 gadget1.o -o gadget1
	rm gadget1.o

gadget2: gadget2.asm
	nasm -felf64 gadget2.asm -o gadget2.o
	ld gadget2.o -o gadget2
	rm gadget2.o

serial1: serial1.c
	$(CC) -m32 -o serial1 serial1.c

stack1: stack1.c
	$(CC) -Wformat=0 -Wno-deprecated-declarations -m32 -o stack1 stack1.c

loop1: loop1.asm
	nasm -felf32 loop1.asm -o loop1.o
	ld -melf_i386 loop1.o -o loop1
	rm loop1.o

loop2: loop2.c
	$(CC) -m32 -o loop2 loop2.c

clean:
	rm -f branch1
	rm -f branch2
	rm -f branch3
	rm -f branch4
	rm -f complex1
	rm -f constraint1
	rm -f constraint2
	rm -f constraint3
	rm -f helloworld1
	rm -f gadget1
	rm -f gadget2
	rm -f serial1
	rm -f stack1
	rm -f loop1
	rm -f loop2
