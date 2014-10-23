.PHONY: all clean

python_dir		:= /usr/include/python2.7

inc_32_dir		:= $(python_dir)
inc_32_param	:= $(foreach d,$(inc_32_dir),-I $d)

inc_64_dir		:= $(python_dir)
inc_64_param	:= $(foreach d,$(inc_64_dir),-I $d)

all: pyasmjit

pyasmjit: pyasmjit.c Makefile
	gcc -Wall -m32 -ggdb -pedantic -std=c99 -shared -fPIC \
		$(inc_32_param) \
		-o pyasmjit.so pyasmjit.c \
		-lpython2.7

# pyasmjit: pyasmjit.c Makefile
	# gcc -ggdb -std=c99 -shared -fPIC \
	# 	$(inc_64_param) \
	# 	-o pyasmjit.so pyasmjit.c \
	# 	-lpython2.7

clean:
	rm -rf pyasmjit.so
