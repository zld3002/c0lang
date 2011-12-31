Requirements:
Standard GNU/Unix-like environment (rm, cp, GNU make, etc...)
SML/NJ 110.67 or higher
MLton (needed for the Coin interactive toplevel and interpreter)

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

Using libpng as a replacement for qt, depends on zcat ?

NB from Ron Garcia: on Mac OS X 10.6 (Snow Leopard), make gc
will fail out of the box.  Either edit ../externals/gc/os_dep.c
and ../externals/gc/mac_dep.c to change <ucontext.h> to
<sys/ucontext.h>, or use gc7.2alpha
(see http://code.google.com/p/uhc/issues/detail?id=20)

Upgraded to gc7.2alpha, Nov 3, 2011, so the comment
above is now obsolete. -fp

Then:
    $ make            # build the compiler, gc, and runtimes
    $ make libs       # build the libraries (Qt required for libimg)
  [ $ make cc0-mlton  # build cc0 with mlton, for standalone binary export
  [ $ make cc0-test   # build the testing framework ]
    $ make check      # run the regression suite

  [ $ make coin       # build the interactive toplevel ]
  [ $ make coin-exec  # build the interpreter ]
  [ $ make checkcoin  # run the regression suite on the interpreter ]

  [ $ cd vm; make     # build c0vm, must run make libs first ]
  [ $ make checkvm    # test cc0 -b together with c0vm ]

If all tests succeed, you can roll out the current build with:

    $ make install    # install binaries, libs, runtimes, and include files

Alternatively, to only roll out the current libraries, you can run:

    $ make install-libs

NB: to run make cc0-test, you may need to put MLton on your PATH, e.g., by
adding /afs/andrew/usr/wlovas/public/mlton/usr/bin to it on Andrew.

NB: running "make cc0-test" before "make check" is optional -- the Makefile
target for "make check" should rebuild the cc0-test framework if necessary.

NB: "make check" tests the default runtime.  You can also run "make checkbare"
to test the bare runtime, "make checkc0rt" to test the c0rt runtime, or "make
checkunsafe" to check the unsafe runtime.  "make checkall" tests them all.

Compiler is built as bin/cc0, installed as $(PREFIX)/bin/cc0.
Libraries and runtimes are placed in lib/* and runtime/*, and
are installed as $(PREFIX)/lib/* and $(PREFIX)/runtime/*, respectively.
Include files in include/* are installed as $(PREFIX)/include/*.

Removed prototypes/ subdirectory as of revision > 2412.

dist-bin.txt is the list of files for a binary distribution of
coin and cc0.  It was used to create
http://www.cs.cmu.edu/~fp/misc/c0-v2379-osx10.5.8-bin.tgz
on Sep 26, 2011 on Mac OS X 10.5.8 (Leopard), svn revision
2379 with
cd ..
tar --exclude-vcs --files-from=c0/dist-bin.txt -cvzf c0-v2379-osx10.5.8-bin.tgz

http://www.cs.cmu.edu/~fp/misc/c0-v2379-osx10.5.8-bin.tgz
http://www.cs.cmu.edu/~fp/misc/c0-v2403-osx10.6.8-bin.tgz
Requirements:
- cc0 : you need Xcode.  Get it from your MacOS X install disk
  or download from the Apple Developers website.
- coin : you need gmp.  First download and install
  MacPorts, then do "sudo /opt/local/bin/port install gmp"
- c0-mode : for editing C0 code with Acquamacs or Emacs

--------------------------------------------------
For a preliminary source dist, without qt:

tar -cvzf c0-src-v2760.tgz --exclude .svn --exclude vm 15-122/externals/gc 15-122/c0

--------------------------------------------------
To build a standalone executable, cc0 should be compiled
with mlton.  However, notice the following remarks regarding
mlton, since some version like to link the libgmp library
dynamically, which many systems don't have.
From: Rob Simmons

Step 1: Get and install the *statically linked* version of MLton from
mlton.org.

Step 2: Rename *every* libgmp thing in my /opt/local/lib
(see bin/hide-libgmp)

$ ls -la /opt/local/lib | grep gmp
-rwxr-xr-x   1 root  admin   453736 Jul 22 15:23 libgmpxxx.10.dylib
lrwxr-xr-x   1 root  admin       12 Jul 22 15:23 libgmpxxx.3.dylib ->
libgmp.dylib
-rwxr-xr-x   1 root  admin    22160 Jul 22 15:23 libgmpxxx.4.dylib
-rw-r--r--   1 root  admin   802384 Jul 22 15:23 libgmpxxx.a
lrwxr-xr-x   1 root  admin       15 Jul 22 15:23 libgmpxxx.dylib ->
libgmp.10.dylib
-rwxr-xr-x   1 root  admin      927 Jul 22 15:23 libgmpxxx.la

Step 3: Confirm that "make cc0-mlton" still works but produces a
link error - this meant that it couldn't find any libgmp to link
against whatsoever.

$ sudo mv /opt/local/lib/libgmpxxx.a /opt/local/lib/libgmp.a
$ make cc0-mlton

Since the latter command then succeeds, I have to assume it's linking
(statically, as it must) against libgmp.a.
--------------------------------------------------
To set svn properties:

svn propset svn:svnignore -F svnignore .
----------------------------------------------------------------------


To build the C0 to C# compiler, use "make csharp". This will replace bin/cc0,
so you'll need to run make again to get the normal compiler back. To run the
regression suite for C0 to C#, you need to use a modified test driver, so do
"make csharp-test" and then "make checkcsharp".

Environment variables:
    C0_RESULT_FILE:   If set to a filename, dump a 0 byte followed by the
                      4-byte return value of main() to that filename
        - if the result file is not created, either the program failed to
          dynamically link or it failed with an OS error
        - if the result file ends up with only the 0 byte, the C0 program
          aborted with some kind of exception
        - if the result file has all 5 bytes, the C0 program finished
          successfully
