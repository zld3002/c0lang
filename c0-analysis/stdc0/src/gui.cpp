#include <assert.h>
#include <QApplication>

#include "guiprivate.h"

static QApplication *gApp = NULL;
static const char *gAppName;

STDC0API void stdc0_init(int argc, char **argv) {
  assert(!gApp && "QApplication is already initialized!");
  gApp = new QApplication(argc, argv, have_gui());
  gAppName = argv[0];
}

STDC0API void stdc0_teardown() {
  delete gApp;
  gApp = NULL;
}

STDC0API bool have_gui() {
  // For X11-systems (i.e. Linux/BSD), we have to check if it's available.
  // For Windows/OS X, just assume we can.
#ifdef Q_WS_X11
  return getenv("DISPLAY") != 0;
#else
  return true;
#endif
}

STDC0API void runeventloop() {
  assert(gApp && "You must call init before invoking the run loop");
  gApp->exec();
}

STDC0API window_t window_create(int width, int height) {
  window_t win = new window;
  win->resize(width,height);
  win->setWindowTitle(gAppName);
  win->show();
  return win;
}

STDC0API void window_destroy(window_t window) {
  delete window;
}

STDC0API void window_set_title(window_t window, c0rt_string_t t) {
  c0rt::AutoCStr text(t);
  window->setWindowTitle(text);
}

STDC0API void window_set_context(window_t window, window_context_t context) {
  window->mUserContext = context;
}

STDC0API window_context_t window_get_context(window_t window) {
  return window->mUserContext;
}

STDC0API void window_set_callbacks(window_t window, window_callbacks *cb) {
  window->mCallbacks = cb;
}

STDC0API void window_request_redraw(window_t window) {
  window->update();
}
