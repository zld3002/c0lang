CCFLAGS = -Wall -Wextra -Werror -std=c99 -pedantic
GCC = gcc

untabify: untabify-exec.c
	$(GCC) $(CCFLAGS) untabify-exec.c -o untabify-exec

.PHONY: install
install:
	cp -p untabify-exec ../bin/
	cp -p untabify.sh ../bin/untabify

.PHONY: clean
clean:
	rm untabify-exec
