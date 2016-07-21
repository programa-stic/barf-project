.PHONY: all clean

src := src
dst := bin

all: check_serial_1 check_serial_2 check_serial_3 check_serial_4 \
	check_serial_5 check_serial_6

check_serial_1: $(src)/check_serial_1.c
	gcc -m32 -o $(dst)/$@ $<

check_serial_2: $(src)/check_serial_2.c
	gcc -m32 -o $(dst)/$@ $<

check_serial_3: $(src)/check_serial_3.c
	gcc -m32 -o $(dst)/$@ $<

check_serial_4: $(src)/check_serial_4.c
	gcc -m32 -o $(dst)/$@ $<

check_serial_5: $(src)/check_serial_5.c
	gcc -m32 -o $(dst)/$@ $<

check_serial_6: $(src)/check_serial_6.c
	gcc -ggdb -m32 -o $(dst)/$@ $<

clean:
	rm -f $(dst)/check_serial_1 $(dst)/check_serial_2 $(dst)/check_serial_3 $(dst)/check_serial_4 $(dst)/check_serial_5 $(dst)/check_serial_6
