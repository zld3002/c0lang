# Include the platform-specific configuration from ./configure
include config.mk

include util.mk

SHELL   = /bin/sh
RM      = rm
COPY    = cp -p
CPP     = cpp
DEPTH = .
SML     = sml
MLTON_VERB = 0
MLTON_FLAGS = -default-ann "redundantMatch error" -default-ann "sequenceNonUnit error"
# Enable and remove the 'handle _ => ' from go.sml and top.sml
# to record backtraces (albeit very imprecise ones)
#MLTON_FLAGS += -const 'Exn.keepHistory true'
MLTON_BASIC = mlton $(MLTON_FLAGS) -verbose $(MLTON_VERB)  -output

#Uncomment to use SMLNJ, which has significantly faster compile times than mlton
# NJ=1

MLTON_NATIVE := mlton -default-ann "redundantMatch error" -default-ann "sequenceNonUnit error"
MLTON_NATIVE += -link-opt "-lpthread -ldl -rdynamic" -cc-opt "-Iinclude" -default-ann "allowFFI true"
MLTON_NATIVE += -cc-opt "-I../externals/"
MLTON_NATIVE += -link-opt "../externals/readline/libreadline.a ../externals/readline/libhistory.a"
MLTON_NATIVE += -link-opt "$(shell pkg-config libpng --libs)"

# libreadline dependencies
ifeq ($(PLATFORM),osx)
MLTON_NATIVE += -link-opt "-ltermcap"
else
# (Assuming Linux)
MLTON_NATIVE += -link-opt "-ltinfo"
endif

MLTON_NATIVE += -cc-opt -Wall
MLTON_NATIVE += -cc-opt -Wextra
MLTON_NATIVE += -cc-opt -Werror
MLTON_NATIVE += -output

# $EXTERNALS is set by ./configure in config.mk

## removing codex from default build
#all: cc0 coin codex externals libs
all: cc0 coin externals libs

.PHONY: externals
externals: $(EXTERNALS)

bin:
	mkdir -p bin

runtime:
	mkdir -p runtime


### External libraries

# If you change this, you will have to change lib.mk
GCDIR = ../externals/bdwgc

# We statically link the garbage collector into a dynamic library (libc0rt.so)
# so it needs to be compiled with --with-pic and --enable-static.
# --disable-threads means that the GC will not install signal handlers for
# a bunch of signals, so we can use those signals in the test harness.
# Note that Concurrent CC0 may need this feature of the garbage collector
GC_CC0_CONFIG_FLAGS=--with-pic --enable-static --disable-threads

$(GCDIR)/Makefile:
	(cd $(GCDIR); ./autogen.sh; ./configure $(GC_CC0_CONFIG_FLAGS))

.PHONY: gc
gc: lib $(GCDIR)/Makefile
	$(MAKE) -C $(GCDIR)
	$(COPY) $(GCDIR)/.libs/libgc.a lib


# The backtrace library for C0RT
LIBBACKTRACEDIR := ../externals/libbacktrace

$(LIBBACKTRACEDIR)/Makefile:
	cd $(LIBBACKTRACEDIR) && ./configure --with-pic

.PHONY: libbacktrace
libbacktrace: $(LIBBACKTRACEDIR)/Makefile
	$(MAKE) -C $(LIBBACKTRACEDIR)
	$(COPY) $(LIBBACKTRACEDIR)/.libs/libbacktrace.a lib/
	$(COPY) $(LIBBACKTRACEDIR)/backtrace.h c0rt/

READLINEDIR := ../externals/readline

$(READLINEDIR)/Makefile:
	cd $(READLINEDIR) && ./configure

# For readline we won't copy it from externals/
.PHONY: readline
readline: $(READLINEDIR)/Makefile
	$(MAKE) -C $(READLINEDIR)

### Runtimes

RUNTIMES = alt bare c0rt unsafe
all: $(RUNTIMES)

define runtime_template
.PHONY: $(1)
ifdef STATIC
$(1)/$(call staticlibname,$(1)): $(1)/$(1).h include/c0runtime.h
	$(MAKE) -C $(1)
$(1): runtime $(1)/$(call staticlibname,$(1))
	$(COPY) $(1)/$(call staticlibname,$(1)) $(1)/$(1).h runtime
else
$(1)/$(call dllname,$(1)): $(1)/$(1).h include/c0runtime.h
	$(MAKE) -C $(1)
$(1): runtime $(1)/$(call dllname,$(1))
	$(COPY) $(1)/$(call dllname,$(1)) $(1)/$(1).h runtime
ifeq ($(PLATFORM),osx)
	codesign -s - runtime/$(call dllname,$(1))
endif
endif
endef

$(foreach rt,$(RUNTIMES),$(eval $(call runtime_template,$(rt))))

c0rt/$(call dllname,c0rt): gc libbacktrace

unsafe/$(call dllname,unsafe): gc


### cc0 - the C0 compiler

CC0_DEPS = compiler/sources.cm compiler/*.mlb compiler/*.sml compiler/*/*.sml


.PHONY: cc0
cc0: bin/cc0
bin/cc0: bin $(CC0_DEPS)
	$(MAKE) -C compiler clean
	$(MAKE) -C compiler buildid
ifdef NJ
	$(MAKE) -C compiler cc0
	$(COPY) compiler/bin/cc0.heap.* bin
	$(COPY) compiler/bin/cc0-sml-with-o0-support bin/cc0
	cat compiler/bin/cc0-o0-support >> bin/cc0
else
	$(MLTON_BASIC) bin/cc0.bin compiler/sources-go.mlb
	$(COPY) compiler/bin/cc0-mlton-with-o0-support bin/cc0
	cat compiler/bin/cc0-o0-support >> bin/cc0
endif
	$(COPY) compiler/bin/cpfiles bin
	chmod +x bin/cc0 bin/cpfiles
	touch bin/cc0

csharp: bin bare
#	$(MAKE) -C compiler clean
	$(MAKE) -C compiler buildid
	$(MAKE) -C compiler csharp
	$(COPY) compiler/bin/cc0-sml bin/cc0
	$(COPY) compiler/bin/cc0.heap.* bin
	$(COPY) compiler/bin/cpfiles bin
	chmod +x bin/cc0 bin/cpfiles


### C0 Libraries

.PHONY: wrappergen
wrappergen: bin/wrappergen
bin/wrappergen: makelibs/* bin $(CC0_DEPS)
	$(MAKE) -C compiler buildid
ifdef NJ
	echo 'use "makelibs/wrappergen.sml";' | ${SML}
	$(COPY) compiler/bin/coin-sml bin/wrappergen
	cat compiler/bin/coin-o0-support >> bin/wrappergen
else
	$(MLTON_BASIC) bin/wrappergen.bin makelibs/wrappergen.mlb
	$(COPY) compiler/bin/coin-mlton bin/wrappergen
	cat compiler/bin/coin-o0-support >> bin/wrappergen
endif

.PHONY: libs/*
libs/*: bin/wrappergen
	$(MAKE) -C $@
ifdef STATIC
	$(COPY) $@/$(notdir $@).h0 $@/$(call staticlibname,$(notdir $@)) lib
else
	$(COPY) $@/$(notdir $@).h0 $@/$(call dllname,$(notdir $@)) lib
endif

.PHONY: libsplus/*
libsplus/*: bin/wrappergen
	$(MAKE) -C $@
ifdef STATIC
	$(COPY) $@/$(notdir $@).h0 $@/$(call staticlibname,$(notdir $@)) lib
else
	$(COPY) $@/$(notdir $@).h0 $@/$(call dllname,$(notdir $@)) lib
endif

.PHONY: libs
libs: bin/wrappergen
	$(COPY) libsc0/*.h0 libsc0/*.c0 lib
	for l in libs/*; do $(MAKE) $$l; done
ifdef LIBSPLUS
	for l in libsplus/*; do $(MAKE) $$l; done
endif

.PHONY: libsclean
libsclean:
	for l in libs/*; do $(MAKE) -C $$l clean; done
ifdef LIBSPLUS
	for l in libsplus/*; do $(MAKE) -C $$l clean; done
endif


### Coin - The C0 Interpreter

NATIVE_CYMBOL  = bare/bare.c bare/cstr.c cymbol/sizeof.c
NATIVE_CALLING = cymbol/extern-lib.c cymbol/extern-call.c
NATIVE_COIN    = $(NATIVE_CYMBOL) $(NATIVE_CALLING)

# readline implementation
NATIVE_COIN += coin/c0readline.c

COIN_DEPS = $(CC0_DEPS) $(NATIVE_COIN) cymbol/cymbol*.cm cymbol/*.sml cymbol/*.mlb coin/coin*.cm coin/*.sml coin/*.sml
COIN_DEPS += readline

.PHONY: coin
coin: bin/coin
bin/coin: bin $(COIN_DEPS)
	$(MAKE) -C compiler buildid
ifdef NJ
	echo "coin is unsupported using SML/NJ -- compile with coin"
#	$(MAKE) -C coin
#	$(COPY) coin/coin.heap.* bin
#	$(COPY) compiler/bin/coin-sml-with-o0-support bin/coin
#	cat compiler/bin/coin-o0-support >> bin/coin
else
	$(MLTON_NATIVE) bin/coin.bin coin/coin.mlb $(NATIVE_COIN)
	$(COPY) compiler/bin/coin-mlton-with-o0-support bin/coin
	cat compiler/bin/coin-o0-support >> bin/coin
endif
#	chmod +x bin/coin
#	touch bin/coin

.PHONY: coin-exec
coin-exec: bin/coin-exec
bin/coin-exec: bin $(COIN_DEPS)
	$(MAKE) -C compiler buildid
ifdef NJ
	echo "coin-exec is unsupported using SML/NJ -- compile with coin"
#	$(MAKE) -C coin coin-exec
#	$(COPY) coin/coin-exec.heap.* bin
#	$(COPY) compiler/bin/coin-sml bin/coin-exec
#	cat compiler/bin/coin-o0-support >> bin/coin-exec
else
	$(MLTON_NATIVE) bin/coin-exec.bin coin/coin-exec.mlb $(NATIVE_COIN)
	$(COPY) compiler/bin/coin-mlton bin/coin-exec
	cat compiler/bin/coin-o0-support >> bin/coin-exec
endif
#	chmod +x bin/coin-exec
#	touch bin/coin-exec


### codex - The C0 Debugger

CODEX_DEPS = $(CC0_DEPS) $(COIN_DEPS) codex/debug.cm codex/*.mlb codex/*.sml

.PHONY: codex
codex: bin/codex
bin/codex: bin $(CODEX_DEPS)
	$(MAKE) -C compiler buildid
ifdef NJ
	echo "codex is unsupported using SML/NJ -- compile with coin"
#	$(MAKE) -C codex
#	$(COPY) codex/codex.heap.* bin
#	$(COPY) compiler/bin/coin-sml bin/codex
#	cat compiler/bin/coin-o0-support >> bin/codex
else
	$(MLTON_NATIVE) bin/codex.bin codex/debug.mlb $(NATIVE_COIN)
	$(COPY) compiler/bin/coin-mlton bin/codex
	cat compiler/bin/coin-o0-support >> bin/codex
endif
#	chmod +x bin/codex
#	touch bin/codex


### Cleanup

.PHONY: clean
clean: libsclean
	-$(MAKE) -C bare clean
	-$(MAKE) -C c0rt clean
	-$(MAKE) -C unsafe clean
	-$(MAKE) -C compiler clean
	-$(MAKE) -C coin clean
	-$(MAKE) -C codex clean
	-$(RM) -f lib/*$(DLLSUFFIX) lib/*.a lib/*.h0
	-$(RM) -rf bin runtime

.PHONY: reallyclean
reallyclean: clean
	-$(MAKE) -C $(GCDIR) distclean
	-$(MAKE) -C $(ZLIBDIR) distclean
	rm -f $(ZLIBDIR)/Makefile
	-$(MAKE) -C $(LIBPNGDIR) distclean
	-$(MAKE) -C $(LIBBACKTRACEDIR) distclean
	-$(MAKE) -C $(READLINEDIR) distclean


### Testing harnesses

.PHONY: cc0-test
cc0-test: bin/cc0-test
bin/cc0-test: bin tests/drivers/*
	$(MLTON_BASIC) $@ tests/drivers/$(notdir $@).mlb

vm/c0vm: vm/*.h vm/*.c vm/include/*.h0
	$(MAKE) -C vm

.PHONY: c0vm-test
c0vm-test: vm/c0vm bin/c0vm-test
bin/c0vm-test: bin tests/drivers/*
	$(MLTON_BASIC) $@ tests/drivers/$(notdir $@).mlb

.PHONY: coin-test
coin-test: bin/coin-test
bin/coin-test: bin tests/drivers/*
	$(MLTON_BASIC) $@ tests/drivers/$(notdir $@).mlb

# The Csharp test driver is different from the normal one in a few ways
csharp-test: bin/csharp-test
bin/csharp-test: bin tests/drivers/*
	$(MLTON_BASIC) $@ tests/drivers/$(notdir $@).mlb

# If I add the explicit dependency, it always builds cc0-test which is probably
# not the desired behavior most of the time
TESTDIRS = rjs-basic fp-simple fp-basic wjl-basic lib-basic ibhargav-c1vm
TESTFILES = tests/*/*.c0 tests/*/*.c1 tests/*/*.test # $(patsubst %,tests/%/sources.test tests/%/*.c0,$(TESTDIRS))
.PHONY: check checkunsafe checkc0rt checkall checkvm checkcsharp checkcoin
check: bin/cc0-test
	bin/cc0-test $(TESTFILES)
checkbare: bin/cc0-test
	bin/cc0-test -r bare $(TESTFILES)
checkunsafe: bin/cc0-test
	bin/cc0-test -r unsafe $(TESTFILES)
checkc0rt: bin/cc0-test
	bin/cc0-test -r c0rt $(TESTFILES)
checkall: checkbare checkc0rt checkunsafe

checkvm: vm/c0vm bin/c0vm-test
	bin/c0vm-test $(TESTFILES)

checkcsharp: bin/csharp-test
	bin/csharp-test $(TESTFILES)

checkcoin: bin/coin-test
	bin/coin-test $(TESTFILES)


### Distribution

# Install target -- copy contents of bin, lib, runtime, and include
# TODO: make PREFIX configure-able
PREFIX ?= ../..
.PHONY: install install-c0-mode install-libs package
install: install-libs install-c0-mode
	mkdir -p $(PREFIX)/bin $(PREFIX)/runtime $(PREFIX)/include
	$(COPY) bin/* $(PREFIX)/bin
	$(COPY) runtime/* $(PREFIX)/runtime
	$(COPY) include/c0runtime.h include/cc0lib.h $(PREFIX)/include

install-c0-mode:
	mkdir -p $(PREFIX)/c0-mode
	$(COPY) c0-mode/* $(PREFIX)/c0-mode

# separate target for installing just the libs, so we can upgrade them
# without rolling out a new compiler
install-libs:
	mkdir -p $(PREFIX)/lib
	$(COPY) lib/cc0main.c lib/*.c0 lib/*.h0 lib/*$(DLLSUFFIX) $(PREFIX)/lib

VERSION=$(shell ./get_version.sh)

PACKAGE_FILES = bin/cc0 bin/cc0.bin bin/coin bin/coin.bin bin/codex bin/codex.bin
PACKAGE_FILES += lib/*.c0 lib/*.h0 lib/*$(DLLSUFFIX) lib/*.c
PACKAGE_FILES += runtime/ include
# Packages all the necessary files for redistribution into a tarball
package:
	tar czvf cc0-v$(VERSION)-$(PLATFORM)-$(MACHINE).tgz $(PACKAGE_FILES) README_CC0.txt
	@echo Warning: make package does NOT recompile CC0!
