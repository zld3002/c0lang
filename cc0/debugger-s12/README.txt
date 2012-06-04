Requirements for distribution are as for coin, and can be found in
'../README.txt'.

At the moment, the interactive shell debugger (code -i) is lagging
behind the debugger as an inferior process to Emacs (code -e).  It
offers the rudimentary functionality explained below.  Other features
are always under developments.  Coming soon: evaluating arbitrary
expressions in the current environment, examining memory (store and
call-stack).

----------------------------------------------------------------------
Emacs
----------------------------------------------------------------------
In your .emacs file (for Emacs or Carbon Emacs) you need something
like:

;; Setup for c0-mode
(setq c0-root "/Users/fp/programs/c0/cc0/")
(load (concat c0-root "c0-mode/c0.el"))

When you visit a file, you will be in C0 mode.  To use the debugger,
visit the file with the 'main' function and type C-c C-d (CTRL-c
CTRL-d).  Add the '-d' option at the prompt to the arguments of 'code'
to enable dynamic checking of contracts.

A second buffer *code-locals* should be created with the current
values for all local variables (initiall empty), or error messages.
Also keep an eye on the mini-buffer at the bottom of your frame.

SYNTAX OR TYPE ERRORS.  If your program has a syntax or type error, an
error message will be displayed and the putative error region
highlighted in pink.  Edit the file, go back to the buffer with
'main', and try C-c C-d again.

STEPPING.  Once your program parses and type-checks, you can step
through it with simple keystrokes.  They are:

n             - next command, skipping over function calls
<return> or s - step to the next command or into the next function call
q             - quit the execution
? or h        - display a short help message

While stepping through your program, code will continuously display
the values of all local variables in the buffer *code-locals*.

EXCEPTIONS.  If an exception is raised or the program is aborted due
to a failed contract, an error message is displayed and the code
process is terminated.  In case of a contract violation, the
particular contract is highlighted in pink.  You can get rid of the
highlight with C-c C-g, if you need to.  You can always restart the
code by going to the file with the 'main' function and typing C-c C-d.

----------------------------------------------------------------------
Usage
----------------------------------------------------------------------
Usage: bin/code code [OPTIONS_AND_SOURCEFILES...]
  -v        --verbose        Give verbose status and error messages
  -h        --help           Give short usage message and exit
  -d        --dyn-check      Check contracts dynamically
  -l <lib>  --library=<lib>  Include the library <lib>
  -L <dir>                   Add <dir> to the search path for libraries
  -V        --version        Print version number and compile info
  -t        --trace          Trace execution of interpreted code
  --print-codes    Print out the internal language's representation
  -i        --interactive    Run code in interactive mode for command line use
  -e        --emacs_mode     Run in mode compatible with emacs plugin

  NOTE: the --print-codes and -V options currently are meaningless to
  the debugger.

----------------------------------------------------------------------
Debugger commands
----------------------------------------------------------------------
Code - the C0 debugger.                                            
                                                                   
The code shown is the internal representation of your C0 program.  
The debugger will display the NEXT command to be executed. To      
proceed, hit enter, or any key other than the following special    
inputs listed below. Default behavior is to step into function     
calls.                                                             
                                                                   
The following inputs allow you to control the debugger.            
 v           - Display local variables                             
 h           - Display this help message                           
 n           - Execute command, skipping over function calls       
 q           - Exit the debugger


----------------------------------------------------------------------
Minimal check of binary distribution
----------------------------------------------------------------------

From the cc0 folder,
  
  $ bin/code -i doc/src/exp.c0 doc/src/exp-test.c0
  Assert _tmp_2 == 1 "doc/src/exp-test.c0:6.3-6.25: assert failed" in function main
  (c0de) Assert _tmp_3 == 0 "doc/src/exp-test.c0:7.3-7.25: assert failed" in function main
  (c0de) Assert _tmp_4 == 1 "doc/src/exp-test.c0:8.3-8.25: assert failed" in function main
  (c0de) Assert _tmp_5 == 1 "doc/src/exp-test.c0:9.3-9.26: assert failed" in function main
  (c0de) Assert _tmp_6 == 128 "doc/src/exp-test.c0:10.3-10.27: assert failed" in function main
  (c0de) Assert _tmp_7 == (-128) "doc/src/exp-test.c0:11.3-11.29: assert failed" in function main
  (c0de) Assert _tmp_8 == 81 "doc/src/exp-test.c0:12.3-12.26: assert failed" in function main
  (c0de) Assert _tmp_9 == 81 "doc/src/exp-test.c0:13.3-13.27: assert failed" in function main
  (c0de) Assert _tmp_10 == (1 << 30) "doc/src/exp-test.c0:14.3-14.32: assert failed" in function main
  (c0de) print("All tests passed!\n") in function main
  (c0de) Return 0 in function main
  (c0de) All tests passed!

In emacs mode, the output takes this format:
  
  *file name*:*location information* in function *current function name*

Where location information is the standard format used throughout cc0.

The debugger will give a compilation error if no main function is found
in any of the files passed as command line arguments.

----------------------------------------------------------------------
Building from source
----------------------------------------------------------------------

  Once you've built coin using the instructions in '../README.txt',
  simply use the command "make code" to build the debugger.

  
----------------------------------------------------------------------
Notes on source code
----------------------------------------------------------------------

  All source for the debugger is in debug.sml, with most
  debugger-specific logic found in the dstep function. It simulates compilation
  using similar code as found in coin/coin-exec.sml. It then enters the
  repl and makes use of coin/exec.sml's "step" and "call_step"
  functions. When the user asks for a list of local variables, the
  function "print_locals" in coin/exec.sml is called. The logic for that
  function is found in cymbol/state.sml. 
  
