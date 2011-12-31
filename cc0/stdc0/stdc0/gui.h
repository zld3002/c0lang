#ifndef __STDC0GUI_H__
#define __STDC0GUI_H__

#include "apidefs.h"

#include "gfx.h"

typedef struct window_context *window_context_t;
typedef struct window *window_t;

#ifdef __cplusplus
typedef void (*paint_callback)(window_context_t ctx, context_t c);
typedef void (*resize_callback)(window_context_t ctx, int width, int height);
typedef void (*mouse_down_callback)(window_context_t ctx, int x, int y);
typedef void (*mouse_up_callback)(window_context_t ctx, int x, int y);
typedef void (*mouse_move_callback)(window_context_t ctx, int x, int y);

typedef struct : public gc {
  // Invoked when the window needs to paint itself
  paint_callback paint;
  // Invoked when the window is resized
  resize_callback resize;
  // Invoked when a mouse button is pressed down
  mouse_down_callback mouse_down;
  // Invoked when a mouse button is released
  mouse_up_callback mouse_up;
  // Invoked when the mouse moves over the window
  mouse_move_callback mouse_move;
} window_callbacks;

#else // defined(__cplusplus)

// XXX: punt on function types
typedef struct _window_callbacks *window_callbacks;

#endif // !define(__cplusplus)

// Initializes the library
STDC0API void stdc0_init(int argc, char **argv);
// Shutsdown the library
STDC0API void stdc0_teardown();
// Runs the event loop for the GUI. This method doesn't return until all the
// windows are closed. (TODO: verify this is the case)
STDC0API void runeventloop();

// Returns true if the current process is attached to a graphical display device
STDC0API bool have_gui();

// Creates a new window of the given width and height for its client area
STDC0API window_t window_create(int width, int height);

// Destroys a window
STDC0API void window_destroy(window_t window);

// Sets the title of the window
STDC0API void window_set_title(window_t window, c0rt_string_t text);

// Sets a pointer to user data to be associated with the window. This is passed
// back in every callback.
STDC0API void window_set_context(window_t window, window_context_t context);

// Retrieves the user data associated with this window.
STDC0API window_context_t window_get_context(window_t window);

// Sets the callbacks for this window to use. Function pointers may be null.
STDC0API void window_set_callbacks(window_t window, window_callbacks *cb);

// Notifies the window manager that the window contents are no longer valid and
// the window should be repainted.
STDC0API void window_request_redraw(window_t window);

#endif // __STDC0GUI_H__
