Requirements for source distribution:

    Standard GNU/Unix-like environment (rm, cp, GNU make, etc...)
    SML/NJ 110.67 or higher (can be replaced by mlton)
    MLton (needed for the Coin interactive toplevel and c0vm)

Requirements for binary distribution:

    gcc (which comes with the Xcode developer tools under Mac OS X)

Qt: as of C0 r7, Qt is no longer part of the distribution or standard
libraries.  It's use in the <img> image library has been replaced by
libpng.  Some information on Qt can be found in the qt/ subdirectory

gc: On Mac OS X 10.7 (Lion), 'make gc' will fail.  The latest version of
libgc works under Lion, but we have been unable to installed the update
so far.  The binary distribution for Mac OS X 10.6 (Snow Leopard) has
been reported to run under Lion.

----------------------------------------------------------------------
Minimal check of binary distribution
----------------------------------------------------------------------

    $ bin/cc0 -d doc/src/exp.c0 doc/src/exp-test.c0
    $ ./a.out
    All tests passed!
    0

    $ bin/coin -l conio doc/src/exp.c0
    --> print("Hello World!\n");
    Hello World!
    --> exp(2,3);
    8 (int)
    --> #quit

----------------------------------------------------------------------
Building from source
----------------------------------------------------------------------

    $ ./configure

    $ make            # build the cc0 compiler, gc, runtimes, and libraries
  [ $ make libs       # build the libraries separately (libpng required for libimg) ]
  [ $ make cc0-mlton  # build cc0 with mlton, for standalone binary export ]
    $ make check      # run the regression suite

    $ make coin       # build the interactive toplevel
  [ $ make coin-exec  # build the interpreter ]
  [ $ make checkcoin  # run the regression suite on the interpreter ]

  [ $ cd vm; make     # build c0vm, must run make libs first ]
  [ $ make checkvm    # test cc0 -b together with c0vm ]

If all tests succeed, you can roll out the current build with:

    $ make install    # install binaries, libs, runtimes, and include files

Alternatively, to only roll out the current libraries, you can run:

    $ make install-libs

NB: to run make check, you may need to put MLton on your PATH, e.g., by
adding /afs/andrew/usr/wlovas/public/mlton/usr/bin to it on Andrew.

NB: "make check" tests the default runtime.  You can also run "make checkbare"
to test the bare runtime, "make checkc0rt" to test the c0rt runtime, or "make
checkunsafe" to check the unsafe runtime.  "make checkall" tests them all.
The regression testing for the unsafe runtime has falled behind: some test
cases should be disabled for this.  We recommend only c0rt (the default)
and bare (omitting the garbage collector).

The compiler is built as bin/cc0, installed as $(PREFIX)/bin/cc0.
Libraries and runtimes are placed in lib/* and runtime/*, and
are installed as $(PREFIX)/lib/* and $(PREFIX)/runtime/*, respectively.
Include files in include/* are installed as $(PREFIX)/include/*.

----------------------------------------------------------------------
Creating a binary distribution
----------------------------------------------------------------------
cc0 version 4, on Jan 2, 2012 on Mac OS X 10.6.8 (Snow Leopard) svn
revision 4 with
  cd cc0/doc/reference ; pdflatex c0-reference.tex ; pdflatex c0-reference.tex
  pdflatex c0-libraries.tex pdflatex c0-libraries.tex
  rm -f *.aux *.log *.out *.synctex.gz
  cd ../../..
tar --exclude .svn -p -T cc0/dist-bin.txt -cvzf cc0-v0004-osx10.6.8-bin.tgz

Find version with
svn info https://svn.concert.cs.cmu.edu/c0

Older versions:

http://www.cs.cmu.edu/~fp/misc/c0-v2379-osx10.5.8-bin.tgz
http://www.cs.cmu.edu/~fp/misc/c0-v2403-osx10.6.8-bin.tgz

Requirements for building a binary distribution
- cc0 : you need Xcode.  Get it from your MacOS X install disk
  or download from the Apple Developers website.
- coin : you need gmp.  First download and install
  MacPorts, then do "sudo /opt/local/bin/port install gmp"
- c0-mode : for editing C0 code with Acquamacs or Emacs

Step 1. Get and install the *statically linked* version of
MLton from mlton.org

Step 2. Delete all *libgmp* files in /opt/local/lib *except* libgmp.a
(on OS X).

Step 3. make cc0-mlton

----------------------------------------------------------------------
Source distribution
----------------------------------------------------------------------
Access at https://svn.concert.cs.cmu.edu/c0, username c0guest.
Ask fp@cs.cmu.edu for the password

Older versions:

tar -cvzf c0-src-v2760.tgz --exclude .svn --exclude vm 15-122/externals/gc 15-122/c0

--------------------------------------------------
To set svn properties:

svn propset svn:svnignore -F svnignore .
----------------------------------------------------------------------
The C0 to C# compiler is no longer current; the instructions
need to be updated

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
----------------------------------------------------------------------
