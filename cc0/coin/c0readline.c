#ifndef _GNU_SOURCE
#define _GNU_SOURCE  
#endif

#include <stdlib.h>
#include <stdio.h>
#include <stdbool.h>
#include <assert.h>
#include <string.h>

#include <unistd.h> // access()
#include <signal.h>
#include <setjmp.h>

#include <readline/readline.h>
#include <readline/history.h>

/// Checks system call
#define CHECK(e) if ((e) < 0) { perror(#e); abort(); }

/// A NULL-terminated array of NUL-terminated strings
/// for things we can complete to. This array is provided
/// by the caller of c0_readline()
static const char** c0_completions = NULL;

static const char* default_inputrc = 
    "set colored-completion-prefix on\n"
    "set blink-matching-paren on\n"
    "set show-all-if-ambiguous on\n";

/// Successively returns completions.
/// This function is called multiple times by the library, and each time
/// 'state' is incremented. Therefore we basically use state along with
/// static variables to figure out which completion to return 
static char* c0_readline_completion_generator(const char* input, int state) {
    static size_t completion_index;
    static size_t input_length;

    if (state == 0) {
        // First time calling this function
        completion_index = 0;
        input_length = strlen(input);
    }

    const char* completion;
    while ((completion = c0_completions[completion_index++]) != NULL) {
        if (strncmp(completion, input, input_length) == 0) {
            return strdup(completion);
        }
    }

    return NULL;
}

/// Returns completion function
static char** c0_readline_completion(const char* input, int _start, int _end) {
    rl_attempted_completion_over = true;
    rl_completion_suppress_append = true; 
    return rl_completion_matches(input, c0_readline_completion_generator);
}

static char* history_file = NULL;

/// Sets up history and completion i.e. global state
void c0_readline_init(void) {
    // Set up history
    const char* home = getenv("HOME");
    using_history();

    if (home != NULL) {
        CHECK(asprintf(&history_file, "%s/.coin_history", home));

        // Check if an ~/.inputrc exists.
        // If not, then create one with some nice defaults
        char* inputrc_path;
        CHECK(asprintf(&inputrc_path, "%s/.inputrc", home));

        if (access(inputrc_path, F_OK) != 0) {
            // .inputrc doesn't exist
            FILE* inputrc = fopen(inputrc_path, "w");
            if (inputrc != NULL) {
                fputs(default_inputrc, inputrc);
                CHECK(fclose(inputrc));
            }
        }

        read_history(history_file);
    }

    // Set up completion
    rl_attempted_completion_function = c0_readline_completion;
}

/// Saves history for this session
void c0_readline_finish(void) {
    if (history_file != NULL) {
        if (write_history(history_file) != 0) {
            perror("Couldn't save history");
        }
    }
}

/// Allows us to jump back into c0_readline if the user
/// interrupts by pressing Ctrl-C
static sigjmp_buf jumpbuf;
/// Saves MLTon's signal handler 
static struct sigaction old_sigint_action;

/// Jumps back into c0_readline() on SIGINT
static void c0_readline_handle_sigint(int _signal) {
    // This may seem unsafe, but it's somewhat fine because of
    // how readline does signals.
    // When we call readline() in c0_readline(), the library
    // will swap out this signal handler for its own signal handler.
    // That handler is simple and only sets a flag. The flag is 
    // checked after each character is entered 
    // i.e. when no non-async-signal-safe function is being called.
    // If readline detects a signal, it does its own work and then
    // "calls" this function using kill(). Therefore it safe for us
    // to longjmp back into c0_readline()
    //
    // There is a race where if the user presses Ctrl-C between
    // when we install this signal handler and when readline() installs
    // its own signal handler. So that would be a problem but I'm not 
    // quite sure how to solve it
    siglongjmp(jumpbuf, true);
}

/// Saves MLTon's SIGINT handler and installs our own 
static void c0_readline_setup_signals(void) {
    struct sigaction sigint_action = {
        .sa_handler = c0_readline_handle_sigint
    };

    CHECK(sigaction(SIGINT, &sigint_action, &old_sigint_action));
}

/// Restores MLTon's signal handler
static void c0_readline_teardown_signals(void) {
    CHECK(sigaction(SIGINT, &old_sigint_action, NULL));
}

/// Prints prompt and uses 'completions' to provide TAB-completions.
/// Returns NUL-terminated string or NULL if EOF (Ctrl-D)
const char* c0_readline(const char* prompt, const char** completions) {
    c0_completions = completions;

    c0_readline_setup_signals();

    while (sigsetjmp(jumpbuf, true)) {
        CHECK(write(STDOUT_FILENO, "\n", 1));
        rl_free_line_state();
        rl_cleanup_after_signal(); 
    }

    // This shouldn't cause any problems with conio's readline()
    // because coin uses dlsym to get a function pointer
    // It could potentially cause issues if coin is statically linked
    // but was only used on Cygwin which should be deprecated in favor
    // of WSL 
    const char* line = readline(prompt);
    if (line != NULL) {
        add_history(line);
    }

    c0_completions = NULL;

    c0_readline_teardown_signals();

    return line;
}
