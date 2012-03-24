;;; c0-c0de.el --- Interaction with 'c0de', the C0 debugger

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
;;    This code interacts with the c0de debugger. It expects
;;    the variable 'c0de-path' to be set to the c0de executable

;;; Known Bugs:
;;    
;;
;;

;;; Versions:
;;
;;    0.1 - Initial release

;; Faces for c0de highlighting
(defface c0de-normal-face
  '((((class color)
      (background dark))
     (:background "Yellow" :bold t :foreground "Black"))
    (((class color)
      (background light))
     (:background "Yellow" :bold t))
    (t
     ()))
  "*Face used for the next expression to be evaluated."
  :group 'c0de)

(defface c0de-error-face
  '((((class color)
      (background dark))
     (:background "Red" :bold t :foreground "Black"))
    (((class color)
      (background light))
     (:background "Red" :bold t))
    (t
     ()))
  "*Face used for highlighting erroneous expressions."
  :group 'c0de)

;; Column positions given by ml-yacc are one off compared to
;; emacs. This should probably be taken care of in parsing though
(defun c0de-get-pos
  (line column)
  "Get buffer position from line:column position"
  (+
   (line-beginning-position (- (+ line 1) (line-number-at-pos)))
   (- column 1)))

;;; Functions for highlighting

(defun c0de-highlight
  (line-begin column-begin line-end column-end)
  "Move highlight overlay to specified region, point to beginning of region"
  (let ((pos-begin (c0de-get-pos line-begin column-begin))
	(pos-end (c0de-get-pos line-end column-end))
	)
    (progn
      (if (boundp 'highlight)
	  (move-overlay highlight pos-begin pos-end)
	(progn
	  (setq highlight (make-overlay pos-begin pos-end))
	  ))
      (goto-char pos-begin))))

(defun c0de-highlight-normal
  (line-begin column-begin line-end column-end)
  "Set normal highlight"
  (progn
    (c0de-highlight line-begin column-begin line-end column-end)
    (overlay-put highlight 'face 'c0de-normal-face)))

(defun c0de-highlight-error
  (line-begin column-begin line-end column-end)
  "Set highlight to indicate error"
  (progn
    (c0de-highlight line-begin column-begin line-end column-end)
    (overlay-put highlight 'face 'c0de-error-face)))

(defun c0de-delete-highlight ()
  "Remove highlight overlay"
  (if (boundp 'highlight)
	(delete-overlay highlight)))

;;; Functions for parsing of debugger output
;;
;; Positional informations is assumed to have format
;; filename:line1.column1-line2.column2
;;
;; The output is parsed one line at a time

(defun c0de-parse-position
  (string)
  "Parse 2 integers separated by '.' from STRING"
  (let ((dot-pos (string-match "[.]" string)))
    (let ((string1 (substring string 0 dot-pos))
	  (string2 (substring string (+ 1 dot-pos))))
      (list (string-to-number string1) (string-to-number string2)))))

(defun c0de-parse-positions
  (string)
  "Parse 4 position integers from STRING"
  (let ((colon-pos (string-match ":" string)))
    (let ((dash-pos (string-match "-" string colon-pos)))
      (let ((string1 (substring string (+ 1 colon-pos) dash-pos))
	    (string2 (substring string (+ 1 dash-pos))))
	(append (c0de-parse-position string1)
		(c0de-parse-position string2))))))

(defun begins-with (string prefix)
  "Returns t if STRING begins with PREFIX. Beware of '.'"
  (eq (string-match prefix string) 0))

(defun c0de-parse (string)
    (if (string-match "\n" string)
      (let ((newline-pos (string-match "\n" string)))
	(progn
	  (message (number-to-string newline-pos))
	  (c0de-parse-line (substring string 0 newline-pos))
	  (c0de-parse (substring string (+ 1 newline-pos)))))
      (c0de-parse-line string)))

(defun c0de-parse-line (string)
  "Parse one line of output from c0de program"
  (cond ((begins-with string "Value") (message string))
	((begins-with string "(c0de)") ())
	((begins-with string "Error") (setq c0de-error string))
	((begins-with string "Finished")
	 (progn
	   (c0de-exit-debug)
	   (message string)))
	((string-match " in function " string)
	 (if (and (boundp 'c0de-error) c0de-error)
	     (progn
	       (eval-expression
		(append (list 'c0de-highlight-error) (c0de-parse-positions string)))
	       (message (concat c0de-error
				(substring string (string-match ":" string))))
	       (setq c0de-error nil))
	   (progn
	     (eval-expression
	      (append (list 'c0de-highlight-normal) (c0de-parse-positions string)))
	     (message (substring string
				 (+ 1 (string-match ":" string)))))))
	(t (message string))))

;;; Filter and Sentinel functions

;; Receives output from the debugger. Logs all output in
;; the debugger's associated buffer before passing it on
;; to the parsing function
(defun c0de-filter (proc string)
  "Filter function for c0de interaction"
  (progn
    (with-current-buffer (process-buffer proc)
      (let ((moving (= (point) (process-mark proc))))
	(save-excursion
	  (goto-char (process-mark proc))
	  (insert string)
	  (set-marker (process-mark proc) (point)))
	(if moving (goto-char (process-mark proc)))))
    (c0de-parse string)))
	 
;; Is called if the debugger process receives a signal
;; or exits
(defun c0de-sentinel (proc string)
  "Sentinel for c0de process"
  (cond
   ((begins-with string "finished") ())
   ((begins-with string "exited abnormally")
    (progn
      (c0de-exit-debug)
      (message (concat "Debugger crashed, please report to developer.\n"
		       "Message : Process c0de " string))))))

;;; Functions for sending input to the debugger

(defun c0de-send-string (string)
  "Send STRING to c0de process"
  (process-send-string c0de-proc string))

(defun c0de-step ()
  "Step to next statement, potentially entering a function"
  (interactive)
  (c0de-send-string "s\n"))

(defun c0de-next ()
  "Step to next statement, passing over functions unless they
include a breakpoint"
  (interactive)
  (c0de-send-string "n\n"))

(defun c0de-continue ()
  "Go to the next breakpoint"
  (interactive)
  (c0de-send-string "c\n"))

(defun c0de-reverse-step ()
  "Step backwards"
  (interactive)
  (c0de-send-string "rs\n"))

(defun c0de-reverse-next ()
  "Next backwards"
  (interactive)
  (c0de-send-string "rn\n"))

(defun c0de-reverse-continue ()
  "Continue backwards"
  (interactive)
  (c0de-send-string "cn\n"))

(defun c0de-eval-exp ()
  "Evaluate an expression"
  (interactive)
  (progn
    (setq exp (read-string "Evaluate Expression: " exp))
    (c0de-send-string (concat "e " exp "\n"))))

(defun c0de-interrupt ()
  "Interrupt the debugger"
  (interactive)
  (interrupt-process "c0de"))

;;; The keymap used for debugging
(setq c0de-map
      (let ((map (make-sparse-keymap)))
	(define-key map "s" 'c0de-step)
	(define-key map (kbd "RET") 'c0de-step)
	(define-key map "n" 'c0de-next)
	(define-key map "c" 'c0de-continue)
	(define-key map "rs" 'c0de-reverse-step)
	(define-key map "rn" 'c0de-reverse-next)
	(define-key map "rc" 'c0de-reverse-continue)
	(define-key map "e" 'c0de-eval-exp)
	(define-key map "q" 'c0de-exit-debug)
	(define-key map "i" 'c0de-interrupt)
	map))

;;; Enter and Exit functions

;; Start the debugger on the current buffer. The buffer must
;; be associated with ('visiting') a file.
;; After initial checks, the function
;; -makes the buffer read only
;; -saves the buffer
;; -saves the current keymap and point
;; -adds a hook that quits the debugger if the buffer is killed
;; -runs the debugger

(defun c0de-enter-debug ()
  "Enter debugging mode. This saves the buffer."
  (interactive)
  (if (get-process "c0de")
      (message "Debugger already running.")
    (if (not (boundp 'c0de-path))
	(message "Debugger path not set.")
      (if (not (buffer-file-name))
	(message "Please save the buffer to a file before running the debugger")
	(progn
          (setq args (read-string "Call debugger with: c0de" 
               (concat 
                   " " 
                   (file-relative-name (buffer-file-name)))))
	  (setq buffer-read-only t)
	  (save-buffer)
	  (setq old-local-map (current-local-map))
	  (use-local-map c0de-map)
	  (setq c0de-proc
		(start-process-shell-command
		 "c0de"
		 "*c0de*"
		 c0de-path
		 args))
	  (setq exp "")
	  (add-hook 'kill-buffer-hook 'c0de-kill-buffer)
	  (setq point-old (point))
	  (set-process-filter c0de-proc 'c0de-filter)
	  (set-process-sentinel c0de-proc 'c0de-sentinel))))))

;; Hook to be run if the buffer is killed while debugging
;; Kills the debugger
(defun c0de-kill-buffer ()
  (progn
    (if (get-process "c0de")
       (delete-process "c0de"))))

;; Quit the debugger. Restores the buffers keymap and point
(defun c0de-exit-debug ()
  "Exit debugging mode"
  (interactive)
  (progn
    (if (get-process "c0de")
	(delete-process "c0de"))
    (kill-buffer "*c0de*")
    (remove-hook 'kill-buffer-hook 'c0de-kill-buffer)
    (c0de-delete-highlight)
    (use-local-map old-local-map)
    (goto-char point-old)
    (setq buffer-read-only nil)))

(provide 'c0-c0de)

;;; c0-c0de.el ends here
