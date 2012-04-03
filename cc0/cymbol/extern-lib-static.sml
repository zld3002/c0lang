(* Automatically generated by bin/wrappergen
 * Do not edit this file directly! *)

structure NativeLibrary :> NATIVELIBRARY where type function = NativeFn.t =
struct

structure Map = 
SplayMapFn (struct type ord_key = string  val compare = String.compare end)

type fnptr = MLton.Pointer.t -> MLton.Pointer.t
type function = NativeFn.t
type library = function Map.map

val mapN = List.map (fn (x, y) => (x, NativeFn.Native y))

(* Library conio *)
val lib_conio = List.foldr Map.insert' Map.empty (mapN (
("error",                _import "__c0ffi_error" public: fnptr;) ::
("print",                _import "__c0ffi_print" public: fnptr;) ::
("printbool",            _import "__c0ffi_printbool" public: fnptr;) ::
("printchar",            _import "__c0ffi_printchar" public: fnptr;) ::
("printint",             _import "__c0ffi_printint" public: fnptr;) ::
("println",              _import "__c0ffi_println" public: fnptr;) ::
("readline",             _import "__c0ffi_readline" public: fnptr;) ::
[]))

(* Library curses *)
val lib_curses = List.foldr Map.insert' Map.empty (mapN (
("c_addch",              _import "__c0ffi_c_addch" public: fnptr;) ::
("c_cbreak",             _import "__c0ffi_c_cbreak" public: fnptr;) ::
("c_curs_set",           _import "__c0ffi_c_curs_set" public: fnptr;) ::
("c_delch",              _import "__c0ffi_c_delch" public: fnptr;) ::
("c_endwin",             _import "__c0ffi_c_endwin" public: fnptr;) ::
("c_erase",              _import "__c0ffi_c_erase" public: fnptr;) ::
("c_getch",              _import "__c0ffi_c_getch" public: fnptr;) ::
("c_initscr",            _import "__c0ffi_c_initscr" public: fnptr;) ::
("c_keypad",             _import "__c0ffi_c_keypad" public: fnptr;) ::
("c_move",               _import "__c0ffi_c_move" public: fnptr;) ::
("c_noecho",             _import "__c0ffi_c_noecho" public: fnptr;) ::
("c_refresh",            _import "__c0ffi_c_refresh" public: fnptr;) ::
("c_subwin",             _import "__c0ffi_c_subwin" public: fnptr;) ::
("c_waddch",             _import "__c0ffi_c_waddch" public: fnptr;) ::
("c_waddstr",            _import "__c0ffi_c_waddstr" public: fnptr;) ::
("c_wclear",             _import "__c0ffi_c_wclear" public: fnptr;) ::
("c_werase",             _import "__c0ffi_c_werase" public: fnptr;) ::
("c_wmove",              _import "__c0ffi_c_wmove" public: fnptr;) ::
("c_wrefresh",           _import "__c0ffi_c_wrefresh" public: fnptr;) ::
("c_wstandend",          _import "__c0ffi_c_wstandend" public: fnptr;) ::
("c_wstandout",          _import "__c0ffi_c_wstandout" public: fnptr;) ::
("cc_getbegx",           _import "__c0ffi_cc_getbegx" public: fnptr;) ::
("cc_getbegy",           _import "__c0ffi_cc_getbegy" public: fnptr;) ::
("cc_getmaxx",           _import "__c0ffi_cc_getmaxx" public: fnptr;) ::
("cc_getmaxy",           _import "__c0ffi_cc_getmaxy" public: fnptr;) ::
("cc_getx",              _import "__c0ffi_cc_getx" public: fnptr;) ::
("cc_gety",              _import "__c0ffi_cc_gety" public: fnptr;) ::
("cc_highlight",         _import "__c0ffi_cc_highlight" public: fnptr;) ::
("cc_key_is_backspace",  _import "__c0ffi_cc_key_is_backspace" public: fnptr;) ::
("cc_key_is_down",       _import "__c0ffi_cc_key_is_down" public: fnptr;) ::
("cc_key_is_enter",      _import "__c0ffi_cc_key_is_enter" public: fnptr;) ::
("cc_key_is_left",       _import "__c0ffi_cc_key_is_left" public: fnptr;) ::
("cc_key_is_right",      _import "__c0ffi_cc_key_is_right" public: fnptr;) ::
("cc_key_is_up",         _import "__c0ffi_cc_key_is_up" public: fnptr;) ::
("cc_wboldoff",          _import "__c0ffi_cc_wboldoff" public: fnptr;) ::
("cc_wboldon",           _import "__c0ffi_cc_wboldon" public: fnptr;) ::
("cc_wdimoff",           _import "__c0ffi_cc_wdimoff" public: fnptr;) ::
("cc_wdimon",            _import "__c0ffi_cc_wdimon" public: fnptr;) ::
("cc_wreverseoff",       _import "__c0ffi_cc_wreverseoff" public: fnptr;) ::
("cc_wreverseon",        _import "__c0ffi_cc_wreverseon" public: fnptr;) ::
("cc_wunderoff",         _import "__c0ffi_cc_wunderoff" public: fnptr;) ::
("cc_wunderon",          _import "__c0ffi_cc_wunderon" public: fnptr;) ::
[]))

(* Library file *)
val lib_file = List.foldr Map.insert' Map.empty (mapN (
("file_close",           _import "__c0ffi_file_close" public: fnptr;) ::
("file_eof",             _import "__c0ffi_file_eof" public: fnptr;) ::
("file_read",            _import "__c0ffi_file_read" public: fnptr;) ::
("file_readline",        _import "__c0ffi_file_readline" public: fnptr;) ::
[]))

(* Library img *)
val lib_img = List.foldr Map.insert' Map.empty (mapN (
("image_clone",          _import "__c0ffi_image_clone" public: fnptr;) ::
("image_create",         _import "__c0ffi_image_create" public: fnptr;) ::
("image_data",           _import "__c0ffi_image_data" public: fnptr;) ::
("image_destroy",        _import "__c0ffi_image_destroy" public: fnptr;) ::
("image_height",         _import "__c0ffi_image_height" public: fnptr;) ::
("image_load",           _import "__c0ffi_image_load" public: fnptr;) ::
("image_save",           _import "__c0ffi_image_save" public: fnptr;) ::
("image_subimage",       _import "__c0ffi_image_subimage" public: fnptr;) ::
("image_width",          _import "__c0ffi_image_width" public: fnptr;) ::
[]))

(* Library parse *)
val lib_parse = List.foldr Map.insert' Map.empty (mapN (
("parse_bool",           _import "__c0ffi_parse_bool" public: fnptr;) ::
("parse_int",            _import "__c0ffi_parse_int" public: fnptr;) ::
[]))

(* Library string *)
val lib_string = List.foldr Map.insert' Map.empty (mapN (
("char_chr",             _import "__c0ffi_char_chr" public: fnptr;) ::
("char_ord",             _import "__c0ffi_char_ord" public: fnptr;) ::
("string_charat",        _import "__c0ffi_string_charat" public: fnptr;) ::
("string_compare",       _import "__c0ffi_string_compare" public: fnptr;) ::
("string_equal",         _import "__c0ffi_string_equal" public: fnptr;) ::
("string_from_chararray",_import "__c0ffi_string_from_chararray" public: fnptr;) ::
("string_frombool",      _import "__c0ffi_string_frombool" public: fnptr;) ::
("string_fromchar",      _import "__c0ffi_string_fromchar" public: fnptr;) ::
("string_fromint",       _import "__c0ffi_string_fromint" public: fnptr;) ::
("string_join",          _import "__c0ffi_string_join" public: fnptr;) ::
("string_length",        _import "__c0ffi_string_length" public: fnptr;) ::
("string_sub",           _import "__c0ffi_string_sub" public: fnptr;) ::
("string_terminated",    _import "__c0ffi_string_terminated" public: fnptr;) ::
("string_to_chararray",  _import "__c0ffi_string_to_chararray" public: fnptr;) ::
("string_tolower",       _import "__c0ffi_string_tolower" public: fnptr;) ::
[]))

fun load _ "" = NONE
  | load _ "conio" = SOME (lib_conio)
  | load _ "curses" = SOME (lib_curses)
  | load _ "file" = SOME (lib_file)
  | load _ "img" = SOME (lib_img)
  | load _ "parse" = SOME (lib_parse)
  | load _ "string" = SOME (lib_string)
  | load _ _ = NONE

fun close _ = ()

fun get lib sym = Map.find (lib, sym)

end
