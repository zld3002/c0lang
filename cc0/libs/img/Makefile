# If copying, just change this variable
LIBNAME = img
DEPTH = ../..
# REQUIRES = png z

include ../../lib.mk

LIBS += $(shell pkg-config libpng --libs)

CFLAGS += -std=c99 -pedantic $(shell pkg-config libpng --cflags)
LDFLAGS += -L$(DEPTH)/lib
