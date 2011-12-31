# Setup to build a static library named stdc0
TEMPLATE = lib
TARGET = stdc0
CONFIG += dll
VERSION = 0.1

CONFIG += qt # link in qt
GFX_SOURCES = src/gfx.cpp src/gfxpath.cpp src/gfximg.cpp src/gfxtransform.cpp src/gfxpattern.cpp src/gfxcontext.cpp
SOURCES += src/gui.cpp $$GFX_SOURCES src/timer.cpp src/io.cpp src/audio.cpp
HEADERS += stdc0/api.h stdc0/gui.h stdc0/gfx.h src/gfxprivate.h src/guiprivate.h stdc0/timer.h stdc0/io.h stdc0/audio.h stdc0/apidefs.h
INCLUDEPATH += stdc0 src
DEFINES += STDC0_LIB

# c0rt dependency
C0RT_DIR = ../c0rt
QMAKE_LIBDIR *= $$C0RT_DIR
LIBS += -lc0rt
INCLUDEPATH += $$C0RT_DIR

# gc dependency
INCLUDEPATH += ../gc/include
