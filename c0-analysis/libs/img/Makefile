# If copying, just change this variable
LIBNAME = img
DEPTH = ../..
# REQUIRES = png z

include ../../lib.mk

LIBS += -lpng -lz

CFLAGS += -std=c99 -pedantic
LDFLAGS += -search_paths_first -L$(DEPTH)/lib
