CC = gcc

.PHONY: all clean

all: branch1 branch2 branch3 branch4 complex1 constraint1 constraint2 \
	constraint3 helloworld1 serial1 stack1 loop2

branch1: branch1.c
	$(CC)  -o branch1 branch1.c

branch2: branch2.c
	$(CC)  -o branch2 branch2.c

branch3: branch3.c
	$(CC)  -o branch3 branch3.c

branch4: branch4.c
	$(CC) -o branch4 branch4.c

complex1: complex1.c
	$(CC) -ggdb  -O0 -o complex1 complex1.c

constraint1: constraint1.c
	$(CC)  -O0 -o constraint1 constraint1.c

constraint2: constraint2.c
	$(CC)  -O0 -o constraint2 constraint2.c

constraint3: constraint3.c
	$(CC)  -O0 -o constraint3 constraint3.c

helloworld1: helloworld1.c
	$(CC)  -o helloworld1 helloworld1.c

serial1: serial1.c
	$(CC)  -o serial1 serial1.c

stack1: stack1.c
	$(CC) -Wformat=0 -Wno-deprecated-declarations  -o stack1 stack1.c

loop2: loop2.c
	$(CC)  -o loop2 loop2.c

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
	rm -f serial1
	rm -f stack1
	rm -f loop2
