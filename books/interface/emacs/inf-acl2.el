;;; inf-acl2.el --- an inferior-acl2 mode
;;; Copyright (C) 1988, 1993, 1994 Free Software Foundation, Inc.

;; Copied from inf-lisp.el
;; As modified for Acl2 by M. K. Smith (mksmith@cli.com), Feb 17 94
;; Keywords: processes, acl2

;; Original Author: Olin Shivers <shivers@cs.cmu.edu>
;; Keywords: processes, lisp

;;; This file is for use with GNU Emacs.

;;; GNU Emacs is free software; you can redistribute it and/or modify
;;; it under the terms of the GNU General Public License as published by
;;; the Free Software Foundation; either version 2, or (at your option)
;;; any later version.

;;; GNU Emacs is distributed in the hope that it will be useful,
;;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;;; GNU General Public License for more details.

;;; You should have received a copy of the GNU General Public License
;;; along with GNU Emacs; see the file COPYING.  If not, write to
;;; the Free Software Foundation, 675 Mass Ave, Cambridge, MA 02139, USA.

;;; Commentary:

;;; Hacked from inf-lisp.el,  Feb 17 94 MKS 
;;; Hacked from tea.el by Olin Shivers (shivers@cs.cmu.edu). 8/88

;;; This file defines an acl2-in-a-buffer package (inferior-acl2
;;; mode) built on top of comint mode.  This version is more
;;; featureful, robust, and uniform than the Emacs 18 version.  The
;;; key bindings are also more compatible with the bindings of Hemlock
;;; and Zwei (the Lisp Machine emacs).

;;; Since this mode is built on top of the general command-interpreter-in-
;;; a-buffer mode (comint mode), it shares a common base functionality, 
;;; and a common set of bindings, with all modes derived from comint mode.
;;; This makes these modes easier to use.

;;; For documentation on the functionality provided by comint mode, and
;;; the hooks available for customising it, see the file comint.el.
;;; For further information on inferior-lisp mode, see the comments below.

;;; Needs fixin:
;;; The load-file/compile-file default mechanism could be smarter -- it
;;; doesn't know about the relationship between filename extensions and
;;; whether the file is source or executable. If you compile foo.lisp
;;; with compile-file, then the next load-file should use foo.bin for
;;; the default, not foo.lisp. This is tricky to do right, particularly
;;; because the extension for executable files varies so much (.o, .bin,
;;; .lbin, .mo, .vo, .ao, ...).
;;;
;;; It would be nice if inferior-lisp (and inferior scheme, T, ...) modes
;;; had a verbose minor mode wherein sending or compiling defuns, etc.
;;; would be reflected in the transcript with suitable comments, e.g.
;;; ";;; redefining fact". Several ways to do this. Which is right?
;;;
;;; When sending text from a source file to a subprocess, the process-mark can 
;;; move off the window, so you can lose sight of the process interactions.
;;; Maybe I should ensure the process mark is in the window when I send
;;; text to the process? Switch selectable?

;;; Code:

(require 'comint)
(require 'acl2-mode)

;; Was defined in comint, but not any more.
;; (defun full-copy-sparse-keymap (km)
;;  "Recursively copy the sparse keymap KM."
;;  (cond ((consp km)
;;	 (cons (full-copy-sparse-keymap (car km))
;;	       (full-copy-sparse-keymap (cdr km))))
;;	(t km)))


;;;###autoload
(defvar inferior-acl2-program "acl2"
  ;; or perhaps, "nacl2" or "/slocal/src/acl2/new/allegro-saved_acl2"
  "*Program name for invoking an inferior Acl2 for inferior Acl2 mode.")

;;;###autoload
;;;(defvar inferior-acl2-initialization "(in-package \"acl2\")(lp)\n"
;;;  "String sent to set initial Acl2 state.")
(defvar inferior-acl2-initialization ""
  "String sent to set initial Acl2 state.")

;;;###autoload
(defvar inferior-acl2-load-command
  "(ld \"%s\" :ld-pre-eval-print t :ld-error-action :return :ld-verbose nil)\n"
  "*Format-string for building an Acl2 expression to load a file.
This format string should use `%s' to substitute a file name
and should result in an expression that will command the inferior Acl2
to load that file.

The default setting commands the inferior Acl2 to load the file,
printing the form before evaling but suppressing the ACL2 version
info.")

;; (defvar inferior-acl2-silent-load-command
;;   "(ld \"%s\" :ld-pre-eval-print nil :ld-error-action :return :ld-verbose nil )\n"
;;   "*Format-string for building an Acl2 expression to load a temporary file.
;; This format string should use `%s' to substitute a file name
;; and should result in an expression that will command the inferior Acl2
;; to load that file with a minimum of verbosity.")

;;;###autoload
(defvar inferior-acl2-prompt "^[ACL2]* *[!+]*>+ *"
  "Regexp to recognise prompts in the inferior Acl2 mode.
This variable is used to initialize `comint-prompt-regexp' in the 
inferior Acl2 buffer.")

;;;###autoload
(defvar inferior-acl2-filter-regexp "\\`\\s *\\(:\\(\\w\\|\\s_\\)\\)?\\s *\\'"
  "*What not to save on inferior Acl2's input history.
Input matching this regexp is not saved on the input history in inferior Acl2
mode.  Default is whitespace followed by 0 or 1 single-letter colon-keyword 
(as in :a, :c, etc.)")

(defvar inferior-acl2-mode-map nil)
(cond ((not inferior-acl2-mode-map)
       (setq inferior-acl2-mode-map (copy-keymap comint-mode-map))
       (set-keymap-parent inferior-acl2-mode-map (acl2-shared-lisp-mode-map))))


;;; This function exists for backwards compatibility.
;;; Previous versions of this package bound commands to C-c <letter>
;;; bindings, which is not allowed by the gnumacs standard.

;;;  "This function binds many inferior-acl2 commands to C-c <letter> bindings,
;;;where they are more accessible. C-c <letter> bindings are reserved for the
;;;user, so these bindings are non-standard. If you want them, you should
;;;have this function called by the inferior-acl2-load-hook:
;;;    (setq inferior-acl2-load-hook '(inferior-acl2-install-letter-bindings))
;;;You can modify this function to install just the bindings you want."

;;; ??? This function was commented out.  Added back. Jul 22 94 MKS 

(defun temporary-filename (id)
  (format "/tmp/lisp%d.lisp" id))

(defvar inferior-acl2-buffer "*inferior-acl2*"
"*The current inferior-acl2 process buffer.

MULTIPLE PROCESS SUPPORT
===========================================================================
To run multiple Lisp processes, you start the first up
with \\[inferior-acl2].  It will be in a buffer named `*inferior-acl2*'.
Rename this buffer with \\[rename-buffer].  You may now start up a new
process with another \\[inferior-acl2].  It will be in a new buffer,
named `*inferior-acl2*'.  You can switch between the different process
buffers with \\[switch-to-buffer].

Commands that send text from source buffers to Lisp processes --
like `acl2-eval-event' or `acl2-show-arglist' -- have to choose a process
to send to, when you have more than one Lisp process around.  This
is determined by the global variable `inferior-acl2-buffer'.  Suppose you
have three inferior Acl2 running:
    Buffer              Process
    foo                 inferior-acl2
    bar                 inferior-acl2<2>
    *inferior-acl2*     inferior-acl2<3>
If you do a \\[acl2-eval-event] command on some Lisp source code, 
what process do you send it to?

- If you're in a process buffer (foo, bar, or *inferior-acl2*), 
  you send it to that process.
- If you're in some other buffer (e.g., a source file), you
  send it to the process attached to buffer `inferior-acl2-buffer'.
This process selection is performed by function `inferior-acl2-proc'.

Whenever \\[inferior-acl2] fires up a new process, it resets
`inferior-acl2-buffer' to be the new process's buffer.  If you only run
one process, this does the right thing.  If you run multiple
processes, you can change `inferior-acl2-buffer' to another process
buffer with \\[set-variable].")

;;;###autoload
(defvar inferior-acl2-mode-hook '()
  "*Hook for customising inferior Acl2 mode.")

(defvar inferior-acl2-filter-regexp "\\`\\s *\\(:\\(\\w\\|\\s_\\)\\)?\\s *\\'"
  "*What not to save on inferior Acl2's input history.
Input matching this regexp is not saved on the input history in Inferior Acl2
mode.  Default is whitespace followed by 0 or 1 single-letter colon-keyword 
(as in :a, :c, etc.)")

(defvar comint-input-sentinel)

(defun inferior-acl2-mode () 
  "Major mode for interacting with an inferior Acl2 process.  
Runs Acl2 as a subprocess of Emacs, with Acl2 I/O through an
Emacs buffer.  Variable `inferior-acl2-program' controls which version of
Acl2 is run.  Variables `inferior-acl2-prompt', `inferior-acl2-filter-regexp' and
`inferior-acl2-load-command' can customize this mode for different 
keyword sensitive effects.

For information on running multiple processes in multiple buffers, see
documentation for variable `inferior-acl2-buffer'.

\\{inferior-acl2-mode-map}

Customisation: Entry to this mode runs the hooks on `comint-mode-hook' and
`inferior-acl2-mode-hook' (in that order).

You can send text to the inferior Acl2 process from other buffers containing
Acl2 source.  
    switch-to-acl2 switches the current buffer to the Lisp process buffer.
    acl2-eval-event sends the current defun to the Acl2 process.
    acl2-eval-region sends the current region to the Acl2 process.

    Prefixing the acl2-eval-event/region commands with
    a \\[universal-argument] causes a switch to the Acl2 process buffer 
    after sending the text.

Commands:
Return after the end of the process' output sends the text from the 
    end of process to point.
Return before the end of the process' output copies the sexp ending at point
    to the end of the process' output, and sends it.
Delete converts tabs to spaces as it moves back.
Tab indents for Acl2; with argument, shifts rest
    of expression rigidly with the current line.
C-M-q does Tab on each line starting within following expression.
Paragraphs are separated only by blank lines.  Semicolons start comments.
If you accidentally suspend your process, use \\[comint-continue-subjob]
to continue it."
  (interactive)
  (comint-mode)
  (setq comint-prompt-regexp inferior-acl2-prompt)
  (setq major-mode 'inferior-acl2-mode)
  (setq mode-name "Inferior Acl2")
  ;; ???
  (setq mode-line-process '(": %s"))

  ;;; ??? This was changed to (lisp-mode-variables nil).
  ;;; Back to acl2-mode.   Jul 22 94 MKS 

  (acl2-mode-variables t)
  (use-local-map inferior-acl2-mode-map)
  ;; Extend acl2-mode, now that we have an inferior.
  ;; (inferior-acl2-extend-acl2-mode-map)
  ;; Now done in acl2-interface.
  (setq comint-get-old-input (function acl2-get-old-input))
  (setq comint-input-filter (function acl2-input-filter))
  (setq comint-input-sentinel 'ignore)
  (run-hooks 'inferior-acl2-mode-hook))

(defun acl2-get-old-input ()
  "Return a string containing the sexp ending at point."
  (save-excursion
    (let ((end (point)))
      (backward-sexp)
      (buffer-substring (point) end))))

(defun acl2-input-filter (str)
  "t if STR does not match `inferior-acl2-filter-regexp'."
  (not (string-match inferior-acl2-filter-regexp str)))

;;;###autoload
(defun inferior-acl2 (cmd)
  "Run an inferior Acl2 process, input and output via buffer `*inferior-acl2*'.
If there is a process already running in `*inferior-acl2*', just switch
to that buffer.
With argument, allows you to edit the command line (default is value
of `inferior-acl2-program').  Runs the hooks from
`inferior-acl2-mode-hook' (after the `comint-mode-hook' is run).
\(Type \\[describe-mode] in the process buffer for a list of commands.)"

  ;; Note comment from MAKE-COMINT:
  ;;   Make a comint process NAME in a buffer, running PROGRAM.
  ;;   The name of the buffer is made by surrounding NAME with `*'s."
  ;; Thus the apply below will create a buffer named "*inferior-acl2*"

  (interactive (list (if current-prefix-arg
			 (read-string "Run lisp: " inferior-acl2-program)
		       inferior-acl2-program)))
  (if (not (executable-find inferior-acl2-program))
      (error "ACL2 executable not found; in Emacs, evaluate a suitable form:\n%s"
	     '(setq inferior-acl2-program "<path_to_acl2>")))
  (if (not (comint-check-proc "*inferior-acl2*"))
      (let ((cmdlist (inferior-acl2-args-to-list cmd)))
	(set-buffer (apply (function make-comint)
			   "inferior-acl2" (car cmdlist) nil (cdr cmdlist)))
	(inferior-acl2-mode)
	(comint-send-string (inferior-acl2-proc) inferior-acl2-initialization)))
  (setq inferior-acl2-buffer "*inferior-acl2*")
  (switch-to-buffer "*inferior-acl2*"))

;;;###autoload
(defalias 'run-acl2 'inferior-acl2)

;;; Break a string up into a list of arguments.
;;; This will break if you have an argument with whitespace, as in
;;; string = "-ab +c -x 'you lose'".
(defun inferior-acl2-args-to-list (string)
  (let ((where (string-match "[ \t]" string)))
    (cond ((null where) (list string))
	  ((not (= where 0))
	   (cons (substring string 0 where)
		 (inferior-acl2-args-to-list (substring string (+ 1 where)
							(length string)))))
	  (t (let ((pos (string-match "[^ \t]" string)))
	       (if (null pos)
		   nil
		 (inferior-acl2-args-to-list (substring string pos
							(length string)))))))))

;; send-region-to-acl2-process disappeared
;; ??? Restored.   Jul 22 94 MKS 

;; Hacked for inf-acl2 mode.  Feb 28 94 MKS 
(defun send-region-to-acl2-process (begin end other-window-p)
  "Writes the region of the current buffer delimited by begin and end
   to a temporary file.  If other-window-p is not nil the buffer is selected
   in the other window, otherwise it is selected in the current window (unless
   it is currently exposed in another window)."
	  
  (let* ((process (inferior-acl2-proc))
	 (buffer-to-select (process-buffer process))
	 (cmd-string inferior-acl2-load-command)
	 (filename (temporary-filename (process-id process)))
	 (in-package-form-written nil))
    
    ;; Write any IN-PACKAGE form (occuring immediately after a linefeed) 
    ;; preceeding this region. Bevier. 11/5/90
    (save-excursion
      (goto-char begin)
      (if (re-search-backward "\n(in-package" 0 t)
	  (let ((b (point)))
	    (forward-sexp 1)
	    (let ((e (point)))
	      (setq in-package-form-written t)
	      (write-region b e filename nil 'nomessage)))))

    (write-region begin end filename in-package-form-written 'nomessage)
    (process-send-string process (format cmd-string filename))
    (if other-window-p (switch-to-acl2 t))))

(defvar *inf-acl2-debug-send* nil)
(defvar *inf-acl2-debug-send-string* nil)

(defvar verify-wrapper "(lisp %s)\n")
(defvar verify-prompt-string "->: ")

(defvar *inf-acl2-echo* t)

(defun inf-acl2-send-string (command &optional arg)
  ;; Some printing by Acl2 assumes you are already on 
  ;; a new line.  But since comint-send-string doesn't
  ;; echo this is not always a correct assumption. 
  (if (bufferp (get-buffer inferior-acl2-buffer))
      (let ((string (format command arg)))
	(let ((process (inferior-acl2-proc))
	      (string (format command arg))
	      verify)
	  (set-buffer inferior-acl2-buffer)
	  (goto-char (process-mark process))
	  (save-excursion
	    (beginning-of-line)
	    (setq verify (looking-at verify-prompt-string)))
	  (if verify (setq string (format verify-wrapper string)))
	  ;; The \n below adds a blank line that makes things more 
	  ;; readable.
	  (if *inf-acl2-echo* (progn (insert string) (insert "\n")))
	  (set-marker (process-mark process) (point))
	  ;; (set-marker comint-last-output-start (point))
	  ;; (set-marker comint-last-input-end (point))
	  (if *inf-acl2-debug-send*
	      (setq *inf-acl2-debug-send-string* string))
	  (comint-send-string process string)))
      (error "No inferior Acl2 buffer")))

;; acl2-eval-region, acl2-eval-event, and acl2-eval-last-sexp disappeared
;; ??? Restored.   Jul 22 94 MKS 

(defun acl2-eval-region (start end &optional and-go)
  "Send the current region to the inferior Acl2 process.
Prefix argument means switch to the inferior Acl2 buffer afterwards."
  (interactive "r\nP")
  (goto-char end)
  (send-region-to-acl2-process start end (or and-go *acl2-eval-and-go*)))

(defun acl2-eval-event (&optional and-go)
  "Send the current defun to the inferior Acl2 process.
Prefix argument means switch to the inferior Acl2 buffer afterwards."
  (interactive "P")
  (save-excursion
    (condition-case nil
	(end-of-defun)
      (error (error "Current form unbalanced")))
    (skip-chars-backward " \t\n\r\f") ;  Makes allegro happy
    (let ((end (point)))
      (beginning-of-defun)
      ;; Rather than passing the and-go to eval-region we 
      ;; start the eval and then reposition in this buffer
      ;; before switching.
      (acl2-eval-region (point) end)))
  ;; Same as lisp-eval-defun-and-move
  ;; Deleted at Bevier's request  Apr 20 95 MKS 
  ;; (end-of-defun)
  (if (or and-go *acl2-eval-and-go*) (switch-to-acl2 t)))

(defun acl2-eval-last-sexp (&optional and-go)
  "Send the previous sexp to the inferior Acl2 process.
Prefix argument means switch to the inferior Acl2 buffer afterwards."
  (interactive "P")
  (acl2-eval-region (save-excursion (backward-sexp) (point)) (point)
		    (or and-go *acl2-eval-and-go*)))

(defun switch-to-acl2 (eob-p)
  "Switch to the inferior Acl2 process buffer.
With argument, positions cursor at end of buffer."
  (interactive "P")
  (if (get-buffer inferior-acl2-buffer)
      (pop-to-buffer inferior-acl2-buffer)
    (error "No current inferior Acl2 buffer"))
  (cond (eob-p
	 (push-mark)
	 (goto-char (point-max)))))

(defun switch-to-acl2-eof ()
  "Switch to the inferior Acl2 process buffer &
position cursor at end of buffer."
  (interactive)
  (if (get-buffer inferior-acl2-buffer)
      (pop-to-buffer inferior-acl2-buffer)
    (error "No current inferior Acl2 buffer"))
  (push-mark)
  (goto-char (point-max)))


;;; Now that acl2-compile/eval-event/region takes an optional prefix arg,
;;; these commands are redundant. But they are kept around for the user
;;; to bind if he wishes, for backwards functionality, and because it's
;;; easier to type C-c e than C-u C-c C-e.

(defun acl2-eval-region-and-go (start end)
  "Send the current region to the inferior Acl2, and switch to its buffer."
  (interactive "r")
  (acl2-eval-region start end t))

(defun acl2-eval-event-and-go ()
  "Send the current defun to the inferior Acl2, and switch to its buffer."
  (interactive)
  (acl2-eval-event t))

(defvar acl2-prev-l/c-dir/file nil
  "Record last directory and file used in loading or compiling.
This holds a cons cell of the form `(DIRECTORY . FILE)'
describing the last `acl2-load-file' or `acl2-compile-file' command.")

(defvar acl2-source-modes '(acl2-mode)
  "Used to determine if a buffer contains Acl2 source code.
If it's loaded into a buffer that is in one of these major modes, it's
considered an Acl2 source file by `acl2-load-file' and `acl2-compile-file'.
Used by these commands to determine defaults.")

(defun acl2-load-file (file-name)
  "Load an Acl2 file into the inferior Acl2 process."
  ;; 4th param below is NIL because LOAD doesn't need an exact name.
  ;; But what about LD?
  (interactive (comint-get-source "Load Acl2 file: " acl2-prev-l/c-dir/file
				  acl2-source-modes nil)) 
  (comint-check-source file-name) ; Check to see if buffer needs saved.
  (setq acl2-prev-l/c-dir/file (cons (file-name-directory    file-name)
				     (file-name-nondirectory file-name)))
  (comint-send-string (inferior-acl2-proc)
		      (format inferior-acl2-load-command file-name))
  (switch-to-acl2 t))


;;; Documentation functions: function doc, var doc, arglist, and
;;; describe symbol.
;;; ===========================================================================

;;; Ancillary functions
;;; ===================

;;; Reads a string from the user.
(defun acl2-symprompt (prompt default)
  (list (let* ((prompt (if default
			   (format "%s (default %s): " prompt default)
			 (concat prompt ": ")))
	       (ans (read-string prompt)))
	  (if (zerop (length ans)) default ans))))


;;; Adapted from function-called-at-point in help.el.
(defun acl2-fn-called-at-pt ()
  "Returns the name of the function called in the current call.
The value is nil if it can't find one."
  (condition-case nil
      (save-excursion
	(save-restriction
	  (narrow-to-region (max (point-min) (- (point) 1000)) (point-max))
	  (backward-up-list 1)
	  (forward-char 1)
	  (let ((obj (acl2-var-at-pt)))
	    (and (symbolp obj) obj))))
    (error nil)))

;;; Adapted from variable-at-point in help.el.
(defun acl2-var-at-pt ()
  (condition-case ()
      (save-excursion
	(forward-sexp 1)
	(forward-sexp -1)
	(skip-chars-forward "'")
	(let* ((begin (point))
	       (max (save-excursion (end-of-line) (point)))
	       (end (- (re-search-forward "[ ,()\\.!?#|`';']" max t) 1))
	       (obj (car (read-from-string (buffer-substring begin end)))))
	  (and (symbolp obj) obj)))
    (error nil)))


;;; Documentation functions: fn and var doc, arglist, and symbol describe.
;;; ======================================================================

(defun inf-acl2-last-line-to-top ()
  (save-excursion
    (set-buffer inferior-acl2-buffer)
    (goto-char (point-max))
    (this-line-to-top)))

(defun inferior-acl2-proc ()
  "Returns the current inferior Acl2 process.
See variable `inferior-acl2-buffer'."
  (let ((proc (get-buffer-process (if (eq major-mode 'inferior-acl2-mode)
				      (current-buffer)
				    inferior-acl2-buffer))))
    (or proc
	(error "No Acl2 subprocess; see variable `inferior-acl2-buffer'"))))

;; Try to unwedge Acl2.

(defun acl2-abort-mystery-wedge ()
  (interactive)
  ;; (let ((inferior-acl2-load-command ":q\n"))
  ;;   (acl2-send-sexp-and-go))
  (comint-send-string (inferior-acl2-proc) ":q\n"))


;;; Do the user's customisation...
;;;===============================
(defvar inferior-acl2-load-hook nil
  "This hook is run when the library `inf-acl2' is loaded.
This is a good place to put keybindings.")

(run-hooks 'inferior-acl2-load-hook)

;;; CHANGE LOG
;;; ===========================================================================
;;;  Feb 17 94 MKS - See inf-lisp.el

(provide 'inf-acl2)

;;; inf-acl2.el ends here.


;;; Unused
;; 
;; (defun acl2-show-function-documentation (fn)
;;   "Send a command to the inferior Acl2 to give documentation for function FN.
;; See variable `acl2-function-doc-command'."
;;   (interactive (acl2-symprompt "Function doc" (acl2-fn-called-at-pt)))
;;   (inf-acl2-last-line-to-top)
;;   (comint-proc-query (inferior-acl2-proc)
;; 		     (format acl2-function-doc-command fn)))
;; 
;; (defun acl2-describe-sym (sym)
;;   "Send a command to the inferior Acl2 to describe symbol SYM.
;; See variable `acl2-describe-sym-command'."
;;   (interactive (acl2-symprompt "Describe" (acl2-var-at-pt)))
;;   (inf-acl2-last-line-to-top)
;;   (comint-proc-query (inferior-acl2-proc)
;; 		     (format acl2-describe-sym-command sym)))
;; 
;; 
;; (defun acl2-show-function-documentation (fn)
;;   "Send a command to the inferior Acl2 to give documentation for function FN.
;; See variable `acl2-function-doc-command'."
;;   (interactive (acl2-symprompt "Function doc" (acl2-fn-called-at-pt)))
;;   (inf-acl2-last-line-to-top)
;;   (comint-proc-query (inferior-acl2-proc)
;; 		     (format acl2-function-doc-command fn)))
;; 
;; (defun acl2-show-variable-documentation (var)
;;   "Send a command to the inferior Acl2 to give documentation for function FN.
;; See variable `acl2-var-doc-command'."
;;   (interactive (acl2-symprompt "Variable doc" (acl2-var-at-pt)))
;;   (inf-acl2-last-line-to-top)
;;   (comint-proc-query (inferior-acl2-proc) (format acl2-var-doc-command var)))
;; 
;; (defun acl2-show-arglist (fn)
;;   "Send a query to the inferior Acl2 for the arglist for function FN.
;; See variable `acl2-arglist-command'."
;;   (interactive (acl2-symprompt "Arglist" (acl2-fn-called-at-pt)))
;;   (inf-acl2-last-line-to-top)
;;   (comint-proc-query (inferior-acl2-proc) (format acl2-arglist-command fn)))
;; 
;; (defun acl2-describe-sym (sym)
;;   "Send a command to the inferior Acl2 to describe symbol SYM.
;; See variable `acl2-describe-sym-command'."
;;   (interactive (acl2-symprompt "Describe" (acl2-var-at-pt)))
;;   (inf-acl2-last-line-to-top)
;;   (comint-proc-query (inferior-acl2-proc)
;; 		     (format acl2-describe-sym-command sym)))
;; 
;; (defun acl2-show-arglist (fn)
;;   "Send a query to the inferior Acl2 for the arglist for function FN.
;; See variable `acl2-arglist-command'."
;;   (interactive (acl2-symprompt "Arglist" (acl2-fn-called-at-pt)))
;;   (inf-acl2-last-line-to-top)
;;   (comint-proc-query (inferior-acl2-proc) (format acl2-arglist-command fn)))
;; 
;; (defun acl2-show-variable-documentation (var)
;;   "Send a command to the inferior Acl2 to give documentation for function FN.
;; See variable `acl2-var-doc-command'."
;;   (interactive (acl2-symprompt "Variable doc" (acl2-var-at-pt)))
;;   (inf-acl2-last-line-to-top)
;;   (comint-proc-query (inferior-acl2-proc) (format acl2-var-doc-command var)))
