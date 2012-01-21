ifeq ($(PLATFORM),osx)
dllname = $(addprefix lib,$(addsuffix .dylib,$(1)))
else
dllname = $(addprefix lib,$(addsuffix .so,$(1)))
endif

staticlibname = $(addprefix lib,$(addsuffix .a,$(1)))
