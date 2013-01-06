Requirements for distribution are as for coin, and can be found in
'../README.txt'.

----------------------------------------------------------------------
Emacs
----------------------------------------------------------------------
In your .emacs file (for Emacs, Carbon Emacs, or Aquamacs) you need something
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
e EXP         - evaluate EXP in current context
r EXP         - run EXP in current context, in stepping mode
c             - complete execution to the end, or until breakpoint
b F1 ...      - break at F1 ...
b             - breakpoints are shown
u F1 ...      - unbreak F1 ...
u             - unbreak all functions
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
  -r '<call>' --run='<call>' Run <call> instead of 'main()'
                             <call> must be quoted and may not contain whitespace

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
 i           - Interrupt the debugger (if in infinite loop)
 q           - Exit the debugger


----------------------------------------------------------------------
Minimal check of binary distribution
----------------------------------------------------------------------
The below is obsolete

From the cc0 directory,
   $ bin/codex -i doc/src/exp.c0 -r 'exp(2,3)'
   doc/src/exp.c0:4.7-4.13 in function exp
     if (e == 0)
         ~~~~~~ 
   (codex) 
   doc/src/exp.c0:7.16-7.27 in function exp
       return b * exp(b, e-1);
                  ~~~~~~~~~~~ 
   (codex) c
   finished run of 'exp(2,3)'
   $

In emacs mode, the output takes this format:
  
  *file name*:*location information*

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

  All source for the debugger is in debug.sml.

