/* curses_c0ffi.c
 * This file automatically generated by the command 
 * 'wrappergen curses' - editing is probably bad.
 * 
 * The call to wrappergen was likely probably by 
 * 'make libs/curses', which in turn was likely
 * invoked by 'make libs'. */

#include <inttypes.h>
#include <c0runtime.h>
#include <stdio.h>

/* Headers */

struct _win_st;
struct _win_st * c_initscr();
void c_cbreak();
void c_noecho();
void c_keypad(struct _win_st * w, bool b);
int c_getch();
void c_addch(int c);
void c_waddch(struct _win_st * w, int c);
void c_waddstr(struct _win_st * w, c0_string s);
void c_wstandout(struct _win_st * w);
void c_wstandend(struct _win_st * w);
void c_delch();
void c_erase();
void c_werase(struct _win_st * w);
void c_wclear(struct _win_st * w);
void c_move(int y, int x);
void c_wmove(struct _win_st * w, int y, int x);
void c_refresh();
void c_wrefresh(struct _win_st * w);
int c_endwin();
int c_curs_set(int visibility);
struct _win_st * c_subwin(struct _win_st * orig, int nlines, int ncols, int begin_y, int begin_x);
void cc_wboldon(struct _win_st * w);
void cc_wboldoff(struct _win_st * w);
void cc_wdimon(struct _win_st * w);
void cc_wdimoff(struct _win_st * w);
void cc_wreverseon(struct _win_st * w);
void cc_wreverseoff(struct _win_st * w);
void cc_wunderon(struct _win_st * w);
void cc_wunderoff(struct _win_st * w);
int cc_highlight(int c);
int cc_getx(struct _win_st * w);
int cc_gety(struct _win_st * w);
int cc_getmaxx(struct _win_st * w);
int cc_getmaxy(struct _win_st * w);
int cc_getbegx(struct _win_st * w);
int cc_getbegy(struct _win_st * w);
bool cc_key_is_enter(int key);
bool cc_key_is_backspace(int key);
bool cc_key_is_left(int key);
bool cc_key_is_right(int key);
bool cc_key_is_up(int key);
bool cc_key_is_down(int key);

/* Wrappers */

c0_value __c0ffi_c_initscr(c0_value *args) {
   //fprintf(stderr, "Calling c_initscr\n");
  (void) args; /* suppress error */
  return ptr2val((void *)c_initscr());
}

c0_value __c0ffi_c_cbreak(c0_value *args) {
   //fprintf(stderr, "Calling c_cbreak\n");
  (void) args; /* suppress error */
  c_cbreak();
  return ptr2val(NULL);
}

c0_value __c0ffi_c_noecho(c0_value *args) {
   //fprintf(stderr, "Calling c_noecho\n");
  (void) args; /* suppress error */
  c_noecho();
  return ptr2val(NULL);
}

c0_value __c0ffi_c_keypad(c0_value *args) {
   //fprintf(stderr, "Calling c_keypad\n");
  c_keypad((struct _win_st *)val2ptr(args[0]), (bool)val2int(args[1]));
  return ptr2val(NULL);
}

c0_value __c0ffi_c_getch(c0_value *args) {
   //fprintf(stderr, "Calling c_getch\n");
  (void) args; /* suppress error */
  return int2val(c_getch());
}

c0_value __c0ffi_c_addch(c0_value *args) {
   //fprintf(stderr, "Calling c_addch\n");
  c_addch(val2int(args[0]));
  return ptr2val(NULL);
}

c0_value __c0ffi_c_waddch(c0_value *args) {
   //fprintf(stderr, "Calling c_waddch\n");
  c_waddch((struct _win_st *)val2ptr(args[0]), val2int(args[1]));
  return ptr2val(NULL);
}

c0_value __c0ffi_c_waddstr(c0_value *args) {
   //fprintf(stderr, "Calling c_waddstr\n");
  c_waddstr((struct _win_st *)val2ptr(args[0]), (c0_string)val2ptr(args[1]));
  return ptr2val(NULL);
}

c0_value __c0ffi_c_wstandout(c0_value *args) {
   //fprintf(stderr, "Calling c_wstandout\n");
  c_wstandout((struct _win_st *)val2ptr(args[0]));
  return ptr2val(NULL);
}

c0_value __c0ffi_c_wstandend(c0_value *args) {
   //fprintf(stderr, "Calling c_wstandend\n");
  c_wstandend((struct _win_st *)val2ptr(args[0]));
  return ptr2val(NULL);
}

c0_value __c0ffi_c_delch(c0_value *args) {
   //fprintf(stderr, "Calling c_delch\n");
  (void) args; /* suppress error */
  c_delch();
  return ptr2val(NULL);
}

c0_value __c0ffi_c_erase(c0_value *args) {
   //fprintf(stderr, "Calling c_erase\n");
  (void) args; /* suppress error */
  c_erase();
  return ptr2val(NULL);
}

c0_value __c0ffi_c_werase(c0_value *args) {
   //fprintf(stderr, "Calling c_werase\n");
  c_werase((struct _win_st *)val2ptr(args[0]));
  return ptr2val(NULL);
}

c0_value __c0ffi_c_wclear(c0_value *args) {
   //fprintf(stderr, "Calling c_wclear\n");
  c_wclear((struct _win_st *)val2ptr(args[0]));
  return ptr2val(NULL);
}

c0_value __c0ffi_c_move(c0_value *args) {
   //fprintf(stderr, "Calling c_move\n");
  c_move(val2int(args[0]), val2int(args[1]));
  return ptr2val(NULL);
}

c0_value __c0ffi_c_wmove(c0_value *args) {
   //fprintf(stderr, "Calling c_wmove\n");
  c_wmove((struct _win_st *)val2ptr(args[0]), val2int(args[1]), val2int(args[2]));
  return ptr2val(NULL);
}

c0_value __c0ffi_c_refresh(c0_value *args) {
   //fprintf(stderr, "Calling c_refresh\n");
  (void) args; /* suppress error */
  c_refresh();
  return ptr2val(NULL);
}

c0_value __c0ffi_c_wrefresh(c0_value *args) {
   //fprintf(stderr, "Calling c_wrefresh\n");
  c_wrefresh((struct _win_st *)val2ptr(args[0]));
  return ptr2val(NULL);
}

c0_value __c0ffi_c_endwin(c0_value *args) {
   //fprintf(stderr, "Calling c_endwin\n");
  (void) args; /* suppress error */
  return int2val(c_endwin());
}

c0_value __c0ffi_c_curs_set(c0_value *args) {
   //fprintf(stderr, "Calling c_curs_set\n");
  return int2val(c_curs_set(val2int(args[0])));
}

c0_value __c0ffi_c_subwin(c0_value *args) {
   //fprintf(stderr, "Calling c_subwin\n");
  return ptr2val((void *)c_subwin((struct _win_st *)val2ptr(args[0]), val2int(args[1]), val2int(args[2]), val2int(args[3]), val2int(args[4])));
}

c0_value __c0ffi_cc_wboldon(c0_value *args) {
   //fprintf(stderr, "Calling cc_wboldon\n");
  cc_wboldon((struct _win_st *)val2ptr(args[0]));
  return ptr2val(NULL);
}

c0_value __c0ffi_cc_wboldoff(c0_value *args) {
   //fprintf(stderr, "Calling cc_wboldoff\n");
  cc_wboldoff((struct _win_st *)val2ptr(args[0]));
  return ptr2val(NULL);
}

c0_value __c0ffi_cc_wdimon(c0_value *args) {
   //fprintf(stderr, "Calling cc_wdimon\n");
  cc_wdimon((struct _win_st *)val2ptr(args[0]));
  return ptr2val(NULL);
}

c0_value __c0ffi_cc_wdimoff(c0_value *args) {
   //fprintf(stderr, "Calling cc_wdimoff\n");
  cc_wdimoff((struct _win_st *)val2ptr(args[0]));
  return ptr2val(NULL);
}

c0_value __c0ffi_cc_wreverseon(c0_value *args) {
   //fprintf(stderr, "Calling cc_wreverseon\n");
  cc_wreverseon((struct _win_st *)val2ptr(args[0]));
  return ptr2val(NULL);
}

c0_value __c0ffi_cc_wreverseoff(c0_value *args) {
   //fprintf(stderr, "Calling cc_wreverseoff\n");
  cc_wreverseoff((struct _win_st *)val2ptr(args[0]));
  return ptr2val(NULL);
}

c0_value __c0ffi_cc_wunderon(c0_value *args) {
   //fprintf(stderr, "Calling cc_wunderon\n");
  cc_wunderon((struct _win_st *)val2ptr(args[0]));
  return ptr2val(NULL);
}

c0_value __c0ffi_cc_wunderoff(c0_value *args) {
   //fprintf(stderr, "Calling cc_wunderoff\n");
  cc_wunderoff((struct _win_st *)val2ptr(args[0]));
  return ptr2val(NULL);
}

c0_value __c0ffi_cc_highlight(c0_value *args) {
   //fprintf(stderr, "Calling cc_highlight\n");
  return int2val(cc_highlight(val2int(args[0])));
}

c0_value __c0ffi_cc_getx(c0_value *args) {
   //fprintf(stderr, "Calling cc_getx\n");
  return int2val(cc_getx((struct _win_st *)val2ptr(args[0])));
}

c0_value __c0ffi_cc_gety(c0_value *args) {
   //fprintf(stderr, "Calling cc_gety\n");
  return int2val(cc_gety((struct _win_st *)val2ptr(args[0])));
}

c0_value __c0ffi_cc_getmaxx(c0_value *args) {
   //fprintf(stderr, "Calling cc_getmaxx\n");
  return int2val(cc_getmaxx((struct _win_st *)val2ptr(args[0])));
}

c0_value __c0ffi_cc_getmaxy(c0_value *args) {
   //fprintf(stderr, "Calling cc_getmaxy\n");
  return int2val(cc_getmaxy((struct _win_st *)val2ptr(args[0])));
}

c0_value __c0ffi_cc_getbegx(c0_value *args) {
   //fprintf(stderr, "Calling cc_getbegx\n");
  return int2val(cc_getbegx((struct _win_st *)val2ptr(args[0])));
}

c0_value __c0ffi_cc_getbegy(c0_value *args) {
   //fprintf(stderr, "Calling cc_getbegy\n");
  return int2val(cc_getbegy((struct _win_st *)val2ptr(args[0])));
}

c0_value __c0ffi_cc_key_is_enter(c0_value *args) {
   //fprintf(stderr, "Calling cc_key_is_enter\n");
  return int2val((c0_int)cc_key_is_enter(val2int(args[0])));
}

c0_value __c0ffi_cc_key_is_backspace(c0_value *args) {
   //fprintf(stderr, "Calling cc_key_is_backspace\n");
  return int2val((c0_int)cc_key_is_backspace(val2int(args[0])));
}

c0_value __c0ffi_cc_key_is_left(c0_value *args) {
   //fprintf(stderr, "Calling cc_key_is_left\n");
  return int2val((c0_int)cc_key_is_left(val2int(args[0])));
}

c0_value __c0ffi_cc_key_is_right(c0_value *args) {
   //fprintf(stderr, "Calling cc_key_is_right\n");
  return int2val((c0_int)cc_key_is_right(val2int(args[0])));
}

c0_value __c0ffi_cc_key_is_up(c0_value *args) {
   //fprintf(stderr, "Calling cc_key_is_up\n");
  return int2val((c0_int)cc_key_is_up(val2int(args[0])));
}

c0_value __c0ffi_cc_key_is_down(c0_value *args) {
   //fprintf(stderr, "Calling cc_key_is_down\n");
  return int2val((c0_int)cc_key_is_down(val2int(args[0])));
}

