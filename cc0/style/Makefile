CCFLAGS = -Wall -Wextra -Werror -std=c99 -pedantic
GCC = gcc

untabify: untabify.c
	$(GCC) $(CCFLAGS) untabify.c -o untabify.bin

.PHONY: install
install:
	cp -p untabify.bin ../bin/
	cp -p untabify.sh ../bin/untabify

.PHONY: clean
clean:
	rm untabify.bin
