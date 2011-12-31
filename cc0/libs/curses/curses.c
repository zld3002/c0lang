#include <curses.h>
#include <c0runtime.h>

WINDOW *c_initscr() { return initscr(); }
void c_cbreak() { cbreak(); }
void c_noecho() { noecho(); }
void c_keypad(WINDOW *w, bool b) { keypad(w, b); }
int c_getch() { return getch(); }
void c_addch(chtype c) { addch(c); }
void c_waddch(WINDOW *w, chtype c) { waddch(w, c); }
void c_wstandout(WINDOW *w) { wstandout(w); }
void c_wstandend(WINDOW *w) { wstandend(w); }
void c_waddstr(WINDOW *w, c0_string s) {
    const char *cstr = c0_string_tocstr(s);
    waddstr(w, cstr);
    c0_string_freecstr(cstr);
}
void c_delch() { delch(); }
void c_erase() { erase(); }
void c_werase(WINDOW *w) { werase(w); }
void c_wclear(WINDOW *w) { wclear(w); }
void c_move(int y, int x) { move(y, x); }
void c_wmove(WINDOW *w, int y, int x) { wmove(w, y, x); }
void c_refresh() { refresh(); }
void c_wrefresh(WINDOW *w) { wrefresh(w); }
int c_endwin() { return endwin(); }
int c_curs_set(int visibility) { return curs_set(visibility); }
WINDOW *c_subwin(WINDOW *o, int nl, int nc, int by, int bx)
  { return subwin(o, nl, nc, by, bx); }

void cc_wboldon (WINDOW *w) { wattron (w, A_BOLD); }
void cc_wboldoff(WINDOW *w) { wattroff(w, A_BOLD); }
void cc_wdimon (WINDOW *w) { wattron (w, A_DIM); }
void cc_wdimoff(WINDOW *w) { wattroff(w, A_DIM); }
void cc_wreverseon (WINDOW *w) { wattron(w, A_REVERSE); }
void cc_wreverseoff(WINDOW *w) { wattroff(w, A_REVERSE); }
void cc_wunderon (WINDOW *w) { wattron (w, A_UNDERLINE); }
void cc_wunderoff(WINDOW *w) { wattroff(w, A_UNDERLINE); }

/* NB: depends on chtype == unsigned, which has same size as C0 int */
chtype cc_highlight(chtype c) {
    return c | A_REVERSE;
}

int cc_getx(WINDOW *w) { int x, y; getyx(w, y, x); return x; }
int cc_gety(WINDOW *w) { int x, y; getyx(w, y, x); return y; }
int cc_getmaxx(WINDOW *w) { int x, y; getmaxyx(w, y, x); return x; }
int cc_getmaxy(WINDOW *w) { int x, y; getmaxyx(w, y, x); return y; }
int cc_getbegx(WINDOW *w) { int x, y; getbegyx(w, y, x); return x; }
int cc_getbegy(WINDOW *w) { int x, y; getbegyx(w, y, x); return y; }

bool cc_key_is_enter(int key) { return key == KEY_ENTER || key == '\n'; }
bool cc_key_is_backspace(int key) { return key == KEY_BACKSPACE || key == KEY_DC
                                        || key == '\x08' || key == '\x7f'; }
bool cc_key_is_left(int key) { return key == KEY_LEFT; }
bool cc_key_is_right(int key) { return key == KEY_RIGHT; }
bool cc_key_is_up(int key) { return key == KEY_UP; } 
bool cc_key_is_down(int key) { return key == KEY_DOWN; }
