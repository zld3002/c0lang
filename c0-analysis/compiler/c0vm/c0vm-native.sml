(* Native function indices
 * copied from hw/8/c0vm_natives.h
 *)
(*************
 * obsolete!
 *************)

signature C0VM_NATIVE =
sig
    val native_index : string -> int
end

structure C0VMNative :> C0VM_NATIVE =
struct

(* conio *)
fun ni("print") =                     0
  | ni("println") =                   1
  | ni("printint") =                  2
  | ni("printbool") =                 3
  | ni("printchar") =                 4
  | ni("readline") =                  5
  | ni("error") =                     6

(* string *)
  | ni("string_length") =             7
  | ni("string_charat") =             8
  | ni("string_join") =               9
  | ni("string_sub") =                10
  | ni("string_equal") =              11
  | ni("string_compare") =            12
  | ni("string_frombool") =           13
  | ni("string_fromint") =            14
  | ni("string_fromchar") =           15
  | ni("string_tolower") =            16
  | ni("string_to_chararray") =       17
  | ni("string_from_chararray") =     18
  | ni("char_ord") =                  19
  | ni("char_chr") =                  20

(* file *)
  | ni("file_read") =                 21
  | ni("file_close") =                22
  | ni("file_eof") =                  23
  | ni("file_readline") =             24

(* parse *)
  | ni("parse_bool") =                25
  | ni("parse_int") =                 26

(* args *)
  | ni("args_flag") =                 27
  | ni("args_int") =                  28
  | ni("args_string") =               29
  | ni("args_parse") =                30

(* abort *)
  | ni("c0_abort") =                  31

(* curses *)
  | ni("c_initscr") =                 32
  | ni("c_cbreak") =                  33
  | ni("c_noecho") =                  34
  | ni("c_keypad") =                  35
  | ni("c_getch") =                   36
  | ni("c_addch") =                   37
  | ni("c_waddch") =                  38
  | ni("c_waddstr") =                 39
  | ni("c_wstandout") =               40
  | ni("c_wstandend") =               41
  | ni("c_delch") =                   42
  | ni("c_erase") =                   43
  | ni("c_werase") =                  44
  | ni("c_wclear") =                  45
  | ni("c_move") =                    46
  | ni("c_wmove") =                   47
  | ni("c_refresh") =                 48
  | ni("c_wrefresh") =                49
  | ni("c_endwin") =                  50
  | ni("c_curs_set") =                51
  | ni("c_subwin") =                  52
  | ni("cc_wboldon") =                53
  | ni("cc_wboldoff") =               54
  | ni("cc_wdimon") =                 55
  | ni("cc_wdimoff") =                56
  | ni("cc_wreverseon") =             57
  | ni("cc_wreverseoff") =            58
  | ni("cc_wunderon") =               59
  | ni("cc_wunderoff") =              60
  | ni("cc_highlight") =              61
  | ni("cc_getx") =                   62
  | ni("cc_gety") =                   63
  | ni("cc_getmaxx") =                64
  | ni("cc_getmaxy") =                65
  | ni("cc_getbegx") =                66
  | ni("cc_getbegy") =                67
  | ni("cc_key_is_enter") =           68
  | ni("cc_key_is_backspace") =       69
  | ni("cc_key_is_left") =            70
  | ni("cc_key_is_right") =           71
  | ni("cc_key_is_up") =              72
  | ni("cc_key_is_down") =            73

(* unknown *)
  | ni _ =                            ~1

fun native_index(s) = ni(s)

end
