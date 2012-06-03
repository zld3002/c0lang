;;; c0-code.el --- Interaction with 'code', the C0 debugger

;; Author:     2010 Jakob Max Uecker
;; Maintainer: 
;; Created:    August 2010
;; Modified:   August 2010
;; Version:    0.1
;; Keywords:   c0 debugger

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 2 of the License, or
;; (at your option) any later version.
;; 
;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.
;; 
;; You should have received a copy of the GNU General Public License
;; along with this program; see the file COPYING.  If not, write to
;; the Free Software Foundation, Inc., 59 Temple Place - Suite 330,
;; Boston, MA 02111-1307, USA.

;;; Commentary:
;;
;;    This code interacts with the 'code' debugger. It expects
;;    the variable 'code-path' to be set to the 'code' executable

;;; Known Bugs:
;;    
;;
;;

;;; Versions:
;;
;;    0.1 - Initial release

;; Faces for highlighting the active portion of code
(defface code-normal-face
  '((((class color)
      (background dark))
     (:background "Yellow" :bold t :foreground "Black"))
    (((class color)
      (background light))
     (:background "Yellow" :bold t))
    (t
     ()))
  "*Face used for the next expression to be evaluated."
  :group 'code)

(defface code-error-face
  '((((class color)
      (background dark))
     (:background "Red" :bold t :foreground "Black"))
    (((class color)
      (background light))
     (:background "Red" :bold t))
    (t
     ()))
  "*Face used for highlighting erroneous expressions."
  :group 'code)

(defvar code-locals-buffer nil
  "Buffer which will display values of local variables")

(defvar code-locals-accum nil
  "Accumulator for local variable values for 'v' command")

(defvar code-highlight-overlay nil
  "Overlay to highlight currently evaluated region")

;; Column positions given by ml-yacc are one off compared to
;; emacs. This should probably be taken care of in parsing though
(defun code-get-pos
  (line column)
  "Get buffer position from line:column position"
  (+
   (line-beginning-position (- (+ line 1) (line-number-at-pos)))
   (- column 1)))

;;; Functions for highlighting

(defun code-highlight
  (line-begin column-begin line-end column-end)
  "Move highlight overlay to specified region, point to beginning of region"
  (let ((pos-begin (code-get-pos line-begin column-begin))
	(pos-end (code-get-pos line-end column-end))
	)
    (progn
      (if (not (null code-highlight-overlay))
	  (move-overlay code-highlight-overlay pos-begin pos-end)
	(progn
	  (setq code-highlight-overlay (make-overlay pos-begin pos-end))
	  ))
      (goto-char pos-begin))))

(defun code-highlight-normal
  (line-begin column-begin line-end column-end)
  "Set normal highlight"
  (code-highlight line-begin column-begin line-end column-end)
  (overlay-put code-highlight-overlay 'face 'code-normal-face))

(defun code-highlight-error
  (line-begin column-begin line-end column-end)
  "Set highlight to indicate error"
  (code-highlight line-begin column-begin line-end column-end)
  (overlay-put code-highlight-overlay 'face 'code-error-face))

(defun code-delete-highlight ()
  "Remove highlight overlay"
  (if (not (null code-highlight-overlay))
      (progn
	(delete-overlay code-highlight-overlay)
	(setq code-highlight-overlay nil))))

;;; Functions for parsing of debugger output
;;
;; Positional informations is assumed to have format
;; filename:line1.column1-line2.column2
;;
;; The output is parsed one line at a time

(defun code-parse-position (string)
  "Parse 2 integers separated by '.' from STRING"
  (let ((dot-pos (string-match "[.]" string)))
    (if (not dot-pos)
	(list (string-to-number string) 0)
      (let ((string1 (substring string 0 dot-pos))
	    (string2 (substring string (+ 1 dot-pos))))
	(list (string-to-number string1) (string-to-number string2))))))

(defun code-parse-positions (string)
  "Parse 4 position integers from STRING"
  (let ((colon-pos (string-match ":" string)))
    (if (not colon-pos)
	'(0 0 0 0)
      (let ((dash-pos (string-match "-" string colon-pos)))
	(if (not dash-pos)
	    '(0 0 0 0)
	  (let ((string1 (substring string (+ 1 colon-pos) dash-pos))
		(string2 (substring string (+ 1 dash-pos))))
	    (append (code-parse-position string1)
		    (code-parse-position string2))))))))

(defun begins-with (string prefix)
  "Returns t if STRING begins with PREFIX. Beware of '.'"
  (eq (string-match prefix string) 0))

(defun code-parse (string)
    (if (string-match "\n" string)
      (let ((newline-pos (string-match "\n" string)))
	(progn
	  ;; (message (number-to-string newline-pos))
	  (code-parse-line (substring string 0 newline-pos))
	  (code-parse (substring string (+ 1 newline-pos)))))
      (code-parse-line string)))

(defun code-parse-line (string)
  "Parse one line of output from code program"
  (cond ;; ((begins-with string "Value") (message "%s" string))
	((begins-with string "(code)")
	 (if (not (null code-locals-accum))
	     (progn
	       ;; (message "%d" (length code-locals-accum))
	       (with-current-buffer code-locals-buffer
		 (delete-region (point-min) (point-max))
		 (insert code-locals-accum)
		 (goto-char (point-max)))
	       (setq code-locals-accum nil))))
	;; ((begins-with string "Error") (setq code-error string))
	((begins-with string "main function")
	 (code-exit-debug)
	 (message "%s" string))
	((string-match " in function " string)
	 (if (and (boundp 'code-error) code-error) ; currently not used
	     (progn
	       (apply 'code-highlight-error (code-parse-positions string))
	       ;; (message "%s" (concat code-error (substring string (string-match ":" string))))
	       (setq code-error nil))
	   (progn
	     (apply 'code-highlight-normal (code-parse-positions string))
	     ;; (message "%s" (substring string (+ 1 (string-match ":" string))))
	     )))
	((string-match "^\\w*: " string)
	 ;; \\w* matches variable names, but not those starting
	 ;; with '_' (underscore)
	 (setq code-locals-accum (concat code-locals-accum string "\n"))
	 ())
	((string-match "^_result: " string)
	 ;; display _result temporary variable since it carries useful info
	 (setq code-locals-accum (concat code-locals-accum string "\n"))
	 ())
	;; suppress empty output at end
	((string-equal "\n" string) ())
	((string-equal "" string) ())
	(t ;; (message "%s" string)
	 )))

;;; Filter and Sentinel functions

;; Receives output from the debugger. Logs all output in
;; the debugger's associated buffer before passing it on
;; to the parsing function
(defun code-filter (proc string)
  "Filter function for code interaction"
  (with-current-buffer (process-buffer proc)
    (let ((moving (= (point) (process-mark proc))))
      (save-excursion
	(goto-char (process-mark proc))
	(insert string)
	(set-marker (process-mark proc) (point)))
      (if moving (goto-char (process-mark proc)))))
  (code-parse string))
	 
;; Is called if the debugger process receives a signal
;; or exits
(defun code-sentinel (proc string)
  "Sentinel for code process"
  (cond
   ;; ((begins-with string "Goodbye")
   ;; (message "%s" "quit code"))
   ((begins-with string "exited abnormally")
    (code-exit-debug)
    (message "%s" "program aborted")
    ;; (message "%s" (concat "Debugger crashed, please report to developer.\n"
    ;;           "Message : Process code " string))))))
    )))

;;; Functions for sending input to the debugger

(defun code-send-string (string)
  "Send STRING to code process"
  (process-send-string code-proc string))

(defun code-step ()
  "Step to next statement, potentially entering a function"
  (interactive)
  (code-send-string "s\n")
  (code-send-string "v\n"))

(defun code-next ()
  "Step to next statement, passing over functions unless they
include a breakpoint"
  (interactive)
  (code-send-string "n\n")
  (code-send-string "v\n"))

;; (defun code-continue ()
;;   "Go to the next breakpoint"
;;   (interactive)
;;   (code-send-string "c\n"))

;; (defun code-reverse-step ()
;;   "Step backwards"
;;   (interactive)
;;   (code-send-string "rs\n"))

;; (defun code-reverse-next ()
;;   "Next backwards"
;;   (interactive)
;;   (code-send-string "rn\n"))

;; (defun code-reverse-continue ()
;;   "Continue backwards"
;;   (interactive)
;;   (code-send-string "cn\n"))

;; (defun code-eval-exp ()
;;   "Evaluate an expression"
;;   (interactive)
;;   (progn
;;     (setq exp (read-string "Evaluate Expression: " exp))
;;     (code-send-string (concat "e " exp "\n"))))

(defun code-locals ()
  "Show the value of local variables"
  (interactive)
  (code-send-string "v\n"))

(defun code-interrupt ()
  "Interrupt the debugger"
  (interactive)
  (interrupt-process "code"))

(defun code-help ()
  "Show the Emacs help for code"
  (interactive)
  (message "%s\n%s\n%s\n%s\n%s"
	   "return or s - step"
	   "n - next (skip function calls)"
	   "q - quit"
	   "i - interrupt code"
	   "? or h - this help"))

;;; The keymap used for debugging
(setq code-map
      (let ((map (make-sparse-keymap)))
	(define-key map "s" 'code-step)
	(define-key map (kbd "RET") 'code-step)
	(define-key map "n" 'code-next)
	;; (define-key map "c" 'code-continue)
	;; (define-key map "rs" 'code-reverse-step)
	;; (define-key map "rn" 'code-reverse-next)
	;; (define-key map "rc" 'code-reverse-continue)
	;; (define-key map "e" 'code-eval-exp)
	(define-key map "v" 'code-locals)
	(define-key map "q" 'code-exit-debug)
	(define-key map "i" 'code-interrupt)
	(define-key map "?" 'code-help)
	(define-key map "h" 'code-help)
	map))

;;; Enter and Exit functions

;; Start the debugger on the current buffer. The buffer must
;; be associated with ('visiting') a file.
;; After initial checks, the function
;; -makes the buffer read only
;; -saves the current keymap and point
;; -adds a hook that quits the debugger if the buffer is killed
;; -runs the debugger

(defun code-enter-debug ()
  "Enter debugging mode. This saves the buffer."
  (interactive)
  (if (get-process "code")
      (message "%s" "debugger already running")
    (if (not (boundp 'code-path))
	(message "%s" "debugger path not set")
      (if (and (buffer-modified-p) (yes-or-no-p "save buffer? "))
	  (save-buffer))
      (setq args (read-string "Call debugger with: code" 
			      (concat " -e " (file-relative-name (buffer-file-name)))))
      (setq buffer-read-only t)
      ;; (save-buffer) ; see above
      (setq old-local-map (current-local-map))
      (use-local-map code-map)
      (setq code-proc
	    (start-process-shell-command
	     "code"
	     "*code*"
	     code-path
	     args))
      (setq exp "")
      (add-hook 'kill-buffer-hook 'code-kill-process)
      (setq point-old (point))
      (set-process-filter code-proc 'code-filter)
      (set-process-sentinel code-proc 'code-sentinel)
      (setq code-locals-buffer (get-buffer-create "*code-locals*"))
      (display-buffer code-locals-buffer)
      (save-window-excursion
	(switch-to-buffer-other-window code-locals-buffer)
	(delete-region (point-min) (point-max)))
      (message "Type '?' for help")
      )))

;; Hook to be run if the buffer is killed while debugging
;; Kills the debugger
(defun code-kill-process ()
  (if (get-process "code")
      (delete-process "code")))

;; Quit the debugger. Restores the buffers keymap and point
(defun code-exit-debug ()
  "Exit debugging mode"
  (interactive)
  (code-kill-process)
  ;; for now, keep buffers
  ;; (kill-buffer "*code*")
  ;; (kill-buffer code-locals-buffer)
  (remove-hook 'kill-buffer-hook 'code-kill-process)
  (code-delete-highlight)
  (use-local-map old-local-map)
  (goto-char point-old)
  (setq buffer-read-only nil)
  (message "%s" "code exited"))

(provide 'c0-code)

;;; c0-code.el ends here
