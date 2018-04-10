.PHONY: all clean

src := src
dst := bin

all: x86_sample_1 x86_sample_2

x86_sample_1: $(src)/x86_sample_1.c
	gcc -m32 -o $(dst)/$@ $<

x86_sample_2: $(src)/x86_sample_2.c
	gcc -m32 -o $(dst)/$@ $<

clean:
	rm -f $(dst)/x86_sample_1 $(dst)/x86_sample_2
