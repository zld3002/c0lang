This is the reference implementation for the VM.

The specification and writeup can be found in c0vm-ref.txt (original
in 15-122/hw/8/c0vm-ref.txt)

The files file.h0, parse.h0, string.h0 are adapted from the interface
files in ../lib/*.h0 to work for C.  We include c0.h, stdbool.h, and
stdlib.h, defining types like bool and string.  They are used in
read_program.c and read_file.c.  The have to be updated when the
libraries change in incompatible ways.  Generally, replacing
'[]' by '*' is sufficient to make the C0 header files usable for C.
xs
The version number, defined in c0vm.h must be incremented whenever
there is an incompatible change in the libraries that c0vm code can
use.

The library header (files c0vm_c0ffi.*) are created automatically with
the wrappergen program, for example, when make libs indicates an
incompatible change in the library interface.  An appropriate warning
message is issued when the c0vm version number must increase.

Regression tests can be protected with the condition "!cc0_c0vm =>",
in case code does not compile due to resource constraints in the
simple c0vm format.

To regression-test the vm, do:

% cd 15-122/c0
% make libs

# consider warning; may need to increment version in files:
# BC0_VERSION in vm/c0vm.h and val c0vm_version in compiler/top/top.sml,

% cd vm
% make
% cd ..
% make cc0
% make checkvm
