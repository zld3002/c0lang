This directory collects some versions/parts of files that were
relevant to building C0 with Qt.  This may be useful if it is decided
at some point that the use ot Qt may be resurrected - as of r8 it has
been replace by libpng.

----------------------------------------------------------------------
From ../README.txt

Build instructions:

    $ ./configure   # decide whether a Qt build is necessary and set paths

If you don't have Qt 4.6 or higher installed, run:

    $ make qt

edit Makefile, set PREFIX to your desired installation directory

NB from William Lovas: On Mac OS X, if you have installed a binary
version of Qt before, you need to uninstall it first, because the
build will look in the wrong place.  sudo
/Developer/Tools/uninstall-qt.py before running ./configure.

NB from Ron Garcia: BTW, regarding QT, I have gotten it to build on
Mac OS X 10.6 Snow Leopard.  I ultimately had to make a change to the
build process to do this.  In the Makefile for c0, I had to add "-arch
x86_64" to the configure spec for Qt.  Apparently Qt builds in 32-bit
mode by default under Snow Leopard, but gcc/g++ compiles in 64-bit
mode by default.  I had to explicitly build it in 64-bit mode.
Addendum by fp: see Makefile.snow_leopard
