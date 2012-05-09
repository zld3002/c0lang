SHELL   = /bin/sh
RM      = rm
COPY    = cp -p
SML     = sml
MLTON   = mlton -default-ann "redundantMatch error" -default-ann "sequenceNonUnit error" -output 

ifdef STATIC
ifdef LIBSPLUS
MLTON_NATIVE = mlton -default-ann "redundantMatch error" -default-ann "sequenceNonUnit error" -link-opt "-lpthread -ldl -Llib -Lruntime -lfile -lconio -lstring -lparse -lcurses -limg -lclock -lbare -lpng -lz /usr/lib/libcurses.a" -cc-opt "-Iinclude" -default-ann "allowFFI true" -output 
else
MLTON_NATIVE = mlton -default-ann "redundantMatch error" -default-ann "sequenceNonUnit error" -link-opt "-lpthread -ldl -Llib -Lruntime -lfile -lconio -lstring -lparse -lcurses -limg -lbare -lpng -lz /usr/lib/libcurses.a" -cc-opt "-Iinclude" -default-ann "allowFFI true" -output 
endif
else
MLTON_NATIVE = mlton -default-ann "redundantMatch error" -default-ann "sequenceNonUnit error" -link-opt "-lpthread -ldl -rdynamic" -cc-opt "-Iinclude" -default-ann "allowFFI true" -output 
endif

CPP     = cpp


DEPTH = .

# $EXTERNALS is set by ./configure in config.mk
# currently libpng for mac os x, empty for linux

# Include the platform-specific configuration from ./configure
include config.mk

include util.mk

all: cc0 externals libs

.PHONY: externals
externals: $(EXTERNALS)

bin:
	mkdir -p bin

runtime:
	mkdir -p runtime

# If you change this, you will have to change lib.mk
GCDIR = ../externals/gc

$(GCDIR)/Makefile:
	(cd $(GCDIR); ./configure --with-pic)

.PHONY: gc
gc: lib $(GCDIR)/Makefile
	$(MAKE) -C $(GCDIR)
	$(COPY) $(GCDIR)/.libs/libgc.a lib

ZLIBDIR = ../externals/zlib

$(ZLIBDIR)/Makefile:
	(cd $(ZLIBDIR); ./configure --prefix=$(abspath $(ZLIBDIR)/installdir) )

# copy .a and .h files manually, so that dynamic libraries
# are not available to the linker (for standalone binary export)
.PHONY: zlib
zlib: lib $(ZLIBDIR)/Makefile
	$(MAKE) -C $(ZLIBDIR)
	$(MAKE) -C $(ZLIBDIR) install
	$(COPY) $(ZLIBDIR)/installdir/lib/*.a lib
	$(COPY) $(ZLIBDIR)/installdir/include/*.h include
#	-$(COPY) -a $(ZLIBDIR)/installdir/lib/*.so* lib

LIBPNGDIR = ../externals/libpng

$(LIBPNGDIR)/Makefile:
	(cd $(LIBPNGDIR); ./configure --with-pic --with-zlib-prefix=$(abspath $(ZLIBDIR)/installdir) --prefix=$(abspath $(LIBPNGDIR)/installdir) )

# copy .a and .h files manually, so that dynamic libraries
# are not available to the linker (for standalone binary export)
.PHONY: libpng
libpng: zlib lib $(LIBPNGDIR)/Makefile
	$(MAKE) -C $(LIBPNGDIR)
	$(MAKE) -C $(LIBPNGDIR) install
	$(COPY) $(LIBPNGDIR)/installdir/lib/*.a lib
	$(COPY) $(LIBPNGDIR)/installdir/include/*.h include
#	-$(COPY) -a $(LIBPNGDIR)/installdir/lib/*.so* lib

RUNTIMES = bare c0rt unsafe
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
endif
endef

$(foreach rt,$(RUNTIMES),$(eval $(call runtime_template,$(rt))))

c0rt/$(call dllname,c0rt): gc

unsafe/$(call dllname,unsafe): gc

## cc0 - the C0 compiler

.PHONY: cc0
cc0 parse3: bin bare
	$(MAKE) -C compiler clean
	$(MAKE) -C compiler buildid
	$(MAKE) -C compiler cc0
	$(COPY) compiler/bin/cc0-sml bin/cc0
	$(COPY) compiler/bin/cc0.heap.* bin
	$(COPY) compiler/bin/cpfiles bin
	chmod +x bin/cc0 bin/cpfiles

parse2: bin bare
	$(MAKE) -C compiler clean
	$(MAKE) -C compiler buildid
	$(MAKE) -C compiler parse2
	$(COPY) compiler/bin/cc0-sml bin/cc0
	$(COPY) compiler/bin/cc0.heap.* bin
	$(COPY) compiler/bin/cpfiles bin
	chmod +x bin/cc0 bin/cpfiles

parse1: bin bare
	$(MAKE) -C compiler clean
	$(MAKE) -C compiler buildid
	$(MAKE) -C compiler parse1
	$(COPY) compiler/bin/cc0-sml bin/cc0
	$(COPY) compiler/bin/cc0.heap.* bin
	$(COPY) compiler/bin/cpfiles bin
	chmod +x bin/cc0 bin/cpfiles

csharp: bin bare
	# $(MAKE) -C compiler clean
	$(MAKE) -C compiler buildid
	$(MAKE) -C compiler csharp
	$(COPY) compiler/bin/cc0-sml bin/cc0
	$(COPY) compiler/bin/cc0.heap.* bin
	$(COPY) compiler/bin/cpfiles bin
	chmod +x bin/cc0 bin/cpfiles

cc0-mlton : bin bare
	$(MAKE) -C compiler buildid
	$(MLTON) bin/cc0.exe compiler/sources-go.mlb 
	$(COPY) compiler/bin/cc0-mlton bin/cc0
	$(COPY) compiler/bin/cpfiles bin
	chmod +x bin/cc0 bin/cpfiles

bin/wrappergen: makelibs/* bin 
	$(MAKE) -C compiler buildid
	echo 'use "makelibs/wrappergen.sml";' | ${SML}
	$(COPY) makelibs/wrappergen.sh bin/wrappergen
	touch bin/wrappergen

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

.PHONY: clean
clean: libsclean
	$(MAKE) -C bare clean
	$(MAKE) -C c0rt clean
	$(MAKE) -C unsafe clean
	$(MAKE) -C compiler clean
	$(RM) -f lib/*$(DLLSUFFIX) lib/*.a lib/*.h0
	$(RM) -rf bin runtime

.PHONY: reallyclean
reallyclean: clean
	$(MAKE) -C $(GCDIR) distclean
	$(MAKE) -C $(ZLIBDIR) distclean
	$(MAKE) -C $(LIBPNGDIR) distclean

## Coin - The C0 Interpreter

NATIVE_CYMBOL  = bare/bare.c bare/cstr.c cymbol/sizeof.c
NATIVE_CALLING = cymbol/extern-lib.c cymbol/extern-call.c
NATIVE_COIN    = $(NATIVE_CYMBOL) $(NATIVE_CALLING)

.PHONY: coin 
coin: bin
	$(MAKE) -C compiler buildid
	$(MLTON_NATIVE) bin/coin.exe coin/coin.mlb $(NATIVE_COIN)
	$(COPY) coin/coin-mlton.sh bin/coin
	chmod +x bin/coin

.PHONY: coin-exec
coin-exec: bin
	$(MAKE) -C compiler buildid
	$(MLTON_NATIVE) bin/coin-exec coin/coin-exec.mlb $(NATIVE_COIN)

## code - The C0 Debugger

.PHONY: code
code: bin
	$(MAKE) -C compiler buildid
	$(MLTON_NATIVE) bin/code debugger-s12/debug.mlb $(NATIVE_COIN)

## Testing harnesses

cymbol-native-test: cymbol-mlton-parser bin
	$(MLTON) bin/$@ -link-opt "-lpthread -ldl -rdynamic" -cc-opt -Iinclude -default-ann "allowFFI true" tests/drivers/$@.mlb $(CODE_NATIVE_FILES)

cymbol-test: cymbol-mlton-parser bin
	$(MLTON) bin/$@ tests/drivers/$@.mlb

.PHONY: cc0-test bin/cc0-test
cc0-test: bin/cc0-test
bin/cc0-test: bin tests/drivers/*
	$(MLTON) $@ tests/drivers/$(notdir $@).mlb

vm/c0vm: vm/*.h vm/*.c vm/*.h0
	$(MAKE) -C vm

.PHONY: c0vm-test bin/c0vm-test
c0vm-test: vm/c0vm bin/c0vm-test
bin/c0vm-test: bin tests/drivers/*
	$(MLTON) $@ tests/drivers/$(notdir $@).mlb

.PHONY: coin-test bin/coin-test
coin-test: bin/coin-test
bin/coin-test: bin tests/drivers/*
	$(MLTON) $@ tests/drivers/$(notdir $@).mlb

# The Csharp test driver is different from the normal one in a few ways
csharp-test: bin/csharp-test
bin/csharp-test: bin tests/drivers/*
	$(MLTON) $@ tests/drivers/$(notdir $@).mlb

# If I add the explicit dependency, it always builds cc0-test which is probably
# not the desired behavior most of the time
TESTDIRS = rjs-basic fp-simple fp-basic wjl-basic lib-basic
TESTFILES = tests/*/*.c0 tests/*/*.test # $(patsubst %,tests/%/sources.test tests/%/*.c0,$(TESTDIRS))
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

# Install target -- copy contents of bin, lib, runtime, and include
# TODO: make PREFIX configure-able
PREFIX=../..
.PHONY: install install-c0-mode install-libs
install: install-libs install-c0-mode
	mkdir -p $(PREFIX)/bin $(PREFIX)/runtime $(PREFIX)/include
	$(COPY) bin/* $(PREFIX)/bin
	$(COPY) runtime/* $(PREFIX)/runtime
	$(COPY) include/* $(PREFIX)/include

install-c0-mode:
	mkdir -p $(PREFIX)/c0-mode
	$(COPY) c0-mode/* $(PREFIX)/c0-mode

# separate target for installing just the libs, so we can upgrade them
# without rolling out a new compiler
install-libs:
	mkdir -p $(PREFIX)/lib
	$(COPY) lib/* $(PREFIX)/lib
