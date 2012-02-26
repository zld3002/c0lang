AR = ar
CC = gcc
CXX = g++
LD = g++
RM = rm
DEPTH ?= ../..

include $(DEPTH)/config.mk
include $(DEPTH)/util.mk

ifdef STATIC
TARGET = $(call staticlibname,$(LIBNAME))
else
TARGET = $(call dllname,$(LIBNAME))
endif

# These libs are handled specially by this file
NATIVELIBS = gc ncurses
C0LIBS = $(filter-out $(NATIVELIBS),$(REQUIRES))
LIBS = -L$(abspath $(DEPTH)/lib) $(patsubst %,$(DEPTH)/lib/$(call dllname,%),$(C0LIBS))
LDFLAGS = 

# -fPIC is not supported on Windows and is not necessary there because we link statically
# on Windows
# define CYGWIN so that libs/curses can use the proper location for curses.h
ifeq ($(PLATFORM),cygwin)
CFLAGS = -g -I$(DEPTH)/include $(patsubst %,-I../%/,$(C0LIBS)) -DCYGWIN
else
CFLAGS = -g -fPIC -I$(DEPTH)/include $(patsubst %,-I../%/,$(C0LIBS))
endif

ifeq ($(PLATFORM),osx)
LDFLAGS += -dynamiclib
LDFLAGS += -install_name @rpath/$(TARGET)
# when building libraries, the runtime is unknown -- resolve symbols at runtime
LDFLAGS += -undefined dynamic_lookup
else
LDFLAGS += -shared
LDFLAGS += -Wl,-soname,$(TARGET)
endif

# build explicitly 32-bit libraries (for C0VM, mostly) if $(LIB32) non-empty
ifneq ($(LIB32),)
CFLAGS += -m32
LDFLAGS += -m32
endif

# If they haven't specified sources, assume a reasonable default
# Note that this implicitly also guesses $(LIBNAME).cpp
SOURCES ?= $(LIBNAME).c
ifeq ($(RUNTIME),)
FFISUPPORT = $(LIBNAME)_c0ffi.c
endif
OBJECTS = $(patsubst %.c,%.o,$(patsubst %.cpp,%.o,$(SOURCES) $(FFISUPPORT)))

ifeq ($(findstring gc,$(REQUIRES)),gc)
CFLAGS += -I$(DEPTH)/../externals/gc/include
LIBS += -lgc -lpthread
endif

ifeq ($(findstring ncurses,$(REQUIRES)),ncurses)
LIBS += -lncurses
endif

all: $(TARGET)

$(TARGET): $(OBJECTS)
	for l in $(C0LIBS); do $(MAKE) -C $(DEPTH)/libs/$$l; done
ifdef STATIC
	$(AR) rcs $(TARGET) $(OBJECTS)
else
	$(LD) $(LDFLAGS) -o $(TARGET) $(OBJECTS) $(LIBS)
endif

$(LIBNAME)_c0ffi.o: $(LIBNAME).h0
	$(DEPTH)/bin/wrappergen $(LIBNAME)
	$(CC) $(CFLAGS) -c $(LIBNAME)_c0ffi.c -o $@

%.o: %.c $(DEPTH)/include/c0runtime.h
	$(CC) $(CFLAGS) -c $< -o $@

%.o: %.cpp $(DEPTH)/include/c0runtime.h
	$(CXX) $(CFLAGS) -c $< -o $@

clean:
	-$(RM) -f $(OBJECTS) $(TARGET)

