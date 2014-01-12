
;; ----------------------------------------------------------------------
;; Define the functions.

(defvar *acl2-eval-and-go* nil)

(defun acl2-eval-event-at-click (click)
  "Go to click and execute acl2-eval-event"
  (interactive "e")
  (let ((posn (event-start click))
	(end (event-end click)))
    (select-window (posn-window posn))
    (if (numberp (posn-point posn))
	(goto-char (posn-point posn)))
    ;; If mark is highlighted, no need to bounce the cursor.
    (acl2-eval-event  *acl2-eval-and-go*)))

(defun acl2-mouse-eval-region ()
  (interactive)
  (save-excursion
    (let ((start (point))
	(end (mark)))
    (if (<= start end)
	(acl2-eval-region start end *acl2-eval-and-go*)
	(acl2-eval-region end start *acl2-eval-and-go*)))))

(defun acl2-mouse-eval-buffer ()
  (interactive)
  (save-excursion (acl2-eval-region (point-min) (point-max) *acl2-eval-and-go*)))

(defun this-line-to-top () (interactive) (recenter 0))

(defun inf-acl2-last-line-to-top ()
  (save-excursion
    (set-buffer inferior-acl2-buffer)
    (goto-char (point-max))
    (this-line-to-top)))

(defun acl2-menu-help ()
  (interactive)
  "Provides information about ACL2 menus, esp. where they get
their arguments."
  (with-output-to-temp-buffer "*Help*"
	(princ "ACL2 Menu Use.
-----------------------------------------------------------------
If a menu bar entry is of the form

   Print event ...

the \"...\" indicates that you will be prompted in the minibuffer 
for an argument.  The system normally tries to find a default based 
on where the cursor is in the buffer.

If a menu bar entry is of the form

   Mode >

the \">\" indicates that a suborninate menu will pop up if you 
release on this menu item.

Pop-up menu items indicate that they take an argument by a
preceding \".\".  The argument is determined by what you clicked on to
bring up the menu.  Arguments derived from things that appear in the
chronology are somewhat robust.  So that if you had a list of events
on the screen like:

         13  (DEFMACRO TEXT (X) ...)
 L       14  (DEFUN MSG-P (X) ...)
 L       15  (DEFUN MAKE-PACKET (X Y Z) ...)
 L       16  (DEFUN HISTORY-P (L) ...)
         17  (DEFMACRO INFROM (X) ...)

to see event 14 you could mouse-right anywhere on that line and select
either \". Print Event\" or \". Print Command\".
")))

(defun acl2-mouse-verify (click)
  (interactive "e")
  (send-verify-sexp-to-acl2-process click))

;; Sep 16 94 MKSmith - new version
(defun send-verify-sexp-to-acl2-process (click)
  "Writes a form consisting of `(verify ' and the region of the current buffer 
delimited by point and the click to a temporary file.  Closes with ')\n'.
If other-window-p is not nil the buffer is selected
in the other window, otherwise it is selected in the current window (unless
it is currently exposed in another window)."
  (let* ((process (inferior-acl2-proc))
	 (cmd-string inferior-acl2-load-command)
	 (filename (temporary-filename (process-id process))))
    
    (save-excursion
      (let ((posn (event-start click)))
	(select-window (posn-window posn))
	(if (numberp (posn-point posn))
	    (goto-char (posn-point posn)))
	(let ((b (point)))
	  ;; WRITE-REGION has the `feature' that if start is a string
	  ;; it gets written, rather than the region.
	  (write-region "(acl2::verify " nil filename nil 'nomessage)
	  (forward-sexp 1)
	  (write-region b (point) filename t 'nomessage)
	  (write-region ")\n" nil filename t 'nomessage))
	(process-send-string process (format cmd-string filename))))
    (switch-to-acl2 t)))

(defvar inf-acl2-saved-menu-bar-items nil)

;; These are used by the prooftree menus.

(defun acl2-menu-checkpoint () (interactive) (checkpoint nil))

(defun acl2-menu-checkpoint-suspend () (interactive) (checkpoint t))

(defun goto-subgoal-menu (click)
  (interactive "e")
  (let ((posn (event-start click))
	(end (event-end click)))
    (select-window (posn-window posn))
    (if (numberp (posn-point posn))
	(goto-char (posn-point posn)))
    (goto-subgoal (checkpoint-on-line))))

(defun acl2-mouse-checkpoint (click)
  "Go to checkpoint clicked on in the \"prooftree\" buffer with
the character \"c\" in the first column. "
  (interactive "e")
  (let ((posn (event-start click))
	(end (event-end click)))
    (select-window (posn-window posn))
    (if (numberp (posn-point posn))
	(goto-char (posn-point posn)))
    (checkpoint nil)))

(defun acl2-mouse-checkpoint-suspend (click)
  "Go to checkpoint clicked on in the \"prooftree\" buffer with
the character \"c\" in the first column. "
  (interactive "e")
  (let ((posn (event-start click))
	(end (event-end click)))
    (select-window (posn-window posn))
    (if (numberp (posn-point posn))
	(goto-char (posn-point posn)))
    (checkpoint t)))

;; ----------------------------------------------------------------------

(defun read-event-name-with-default ()
  (let* (this-event
	 (x (read-string (format "Event name (default: %s)"
		       (setq this-event (event-at-cursor))))))
    (if (string-equal x "")
	this-event
	x)))

(defun read-cd-with-default () 
  (let* (this-event
	 (x (read-string (format "Command id (default: %s)"
				 (setq this-event (cd-at-cursor))))))
    (if (string-equal x "")
	this-event
	x)))

(setq menu-interactive-arg
      (append menu-interactive-arg 
	      '((event   (interactive (list (read-event-name-with-default))))
		(cd      (interactive (list (read-cd-with-default))))
		(command (interactive (list (read-cd-with-default)))))))

(setq popup-menu-interactive-arg
      (append menu-interactive-arg
	      '((event (interactive "e"))
		(cd (interactive "X"))
		(command  (interactive "X")))))

(setq menu-arg-name
      (append menu-arg-name
	      '((cd cd) (command cd) (event event))))

;; Syntax for event in history
;;       L d     52 (DEFUN FOO (X) X)
;;       P d     52 (DEFUN FOO (X) X)
;;       PLd     52 (DEFUN FOO (X) X)
;;      >           (DEFTHM TRUE-LISTP-APP
;;      /LVd     52 (DEFUN FOO (X) X)
;;       LV      53 (DEFUN BAR (X) (CONS X X))
;;      \        54 (DEFUN FOO (X) X)

;; In each of the following patterns the command descriptor # is in
;;  (string-to-number (buffer-substring (match-beginning 1) (match-end 1)))
;; And the event begins at (match-end 0), though it may not be an event.  

(defconst *acl2-history-cd-line-format1*
  "^[/\\ \t][PLV ][PLV ][d ][ \t]+\\([-0-9]+\\)[:x ]+")

(defconst *acl2-history-cd-line-format2* "^>[ \t]+")

(defconst *acl2-history-cd-line-format3* "^[ \trgbp]+\\([-0-9]+\\)[:x ]+"
  "From older version of Acl2.")

(defconst *acl2-def-beginning* "([Dd][Ed][Ff][a-zA-z]+[ \t]+")

(defun event-at-cursor ()
  ;; Wants to return a string = event name.
  (save-excursion
    (beginning-of-line) 
    (if (save-excursion
	  (beginning-of-line)
	  (or (looking-at *acl2-history-cd-line-format1*)
	      (looking-at *acl2-history-cd-line-format2*)
	      (looking-at *acl2-history-cd-line-format3*)))
	(goto-char (match-end 0)))
    (if (looking-at *acl2-def-beginning*)
	(goto-char (match-end 0)))
    (symbol-at-cursor)))

(defun cd-at-cursor ()
  ;; Wants to return a command descriptor, preferably a number.
  (save-excursion
    (cond ((save-excursion
	     (beginning-of-line)
	     (or (looking-at *acl2-history-cd-line-format1*)
		 (looking-at *acl2-history-cd-line-format3*)))
	   (string-to-number (buffer-substring (match-beginning 1) (match-end 1))))
	  ((looking-at *acl2-history-cd-line-format2*)
	   (goto-char (match-end 0))
	   (if (looking-at *acl2-def-beginning*)
	       (progn (goto-char (match-end 0))))
	   (symbol-at-cursor))
	  (t (symbol-at-cursor)))))


;; ----------------------------------------------------------------------
;; More utilities

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

;;; Ancillary functions
;;; ===================

;;; Reads a string from the user.
(defun acl2-symprompt (prompt default)
  (list (let* ((prompt (if default
			   (format "%s (default %s): " prompt default)
			 (concat prompt ": ")))
	       (ans (read-string prompt)))
	  (if (zerop (length ans)) default ans))))


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


;; ----------------------------------------------------------------------
;; NOT currently used

;; Adapted from function-called-at-point in help.el.
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


;; NEEDED FOR KEY COMMANDS

(defvar acl2-function-doc-command
  "(acl2::doc '%s)\n"
  "Command to query inferior Acl2 for a function's documentation.")

(defvar acl2-var-doc-command
  "(acl2::doc '%s)\n"
  "Command to query inferior Acl2 for a variable's documentation.")

(defvar acl2-arglist-command
  "(acl2::args '%s)\n"
  "Command to query inferior Acl2 for a function's arglist.")

(defvar acl2-describe-sym-command
  "(acl2::doc '%s)\n"
  "Command to query inferior Acl2 for a variable's documentation.")

(defun acl2-show-function-documentation (fn)
  "Send a command to the inferior Acl2 to give documentation for function FN.
See variable `acl2-function-doc-command'."
  (interactive (acl2-symprompt "Function doc" (acl2-fn-called-at-pt)))
  (inf-acl2-last-line-to-top)
  (comint-proc-query (inferior-acl2-proc)
		     (format acl2-function-doc-command fn)))

(defun acl2-describe-sym (sym)
  "Send a command to the inferior Acl2 to describe symbol SYM.
See variable `acl2-describe-sym-command'."
  (interactive (acl2-symprompt "Describe" (acl2-var-at-pt)))
  (inf-acl2-last-line-to-top)
  (comint-proc-query (inferior-acl2-proc)
		     (format acl2-describe-sym-command sym)))

(defun acl2-show-arglist (fn)
  "Send a query to the inferior Acl2 for the arglist for function FN.
See variable `acl2-arglist-command'."
  (interactive (acl2-symprompt "Arglist" (acl2-fn-called-at-pt)))
  (inf-acl2-last-line-to-top)
  (comint-proc-query (inferior-acl2-proc) (format acl2-arglist-command fn)))

(defun acl2-show-variable-documentation (var)
  "Send a command to the inferior Acl2 to give documentation for function FN.
See variable `acl2-var-doc-command'."
  (interactive (acl2-symprompt "Variable doc" (acl2-var-at-pt)))
  (inf-acl2-last-line-to-top)
  (comint-proc-query (inferior-acl2-proc) (format acl2-var-doc-command var)))


;; HINTS:
;; Click in defun or defthm to add a hint.

(defconst hint-x-popup-menu
  '("Hints"
   ("Do not induct"      ":do-not-induct t ")
   ("Do not generalize"  ":do-not 'generalize ")
   ("Do not fertilize"   ":do-not 'fertilize ")
   ("Expand"    ":expand (%s) "            sexp)
   ("Hands off" ":hands-off (%s) "         symbol)
   ("Disable"   ":in-theory (disable %s) " symbol)
   ("Enable"    ":in-theory (enable %s) "  symbol)
   ("Induct"    ":induct %s "              sexp)
   ("Cases"     ":cases (%s) "             sexp)))

;; (defun foo () "bar"
;;   (declare (xargs ... :guard-hints (("Goal" . <hints>)))))
;; 
;; (defthm foo "bar" body
;;   :rule-classes (a .b)
;;   :hints (("Goal" <hints>)))

;; Need to be able to do rule classes, multiple enable, disable

(defun find-hint-insertion-point ()
  "Returns a list of the form (POINT STRING), where STRING
is the format string in which to insert the hint, and POINT is
where to put it"
  (interactive)
  (save-excursion
    (end-of-defun)
    (skip-chars-backward " \t\n\r\f") ;  Makes allegro happy
    (let ((end (point)))
      (beginning-of-defun)
      (cond ((looking-at "(defun ") 
	     (cond ((re-search-forward ":guard-hints[ \t]*(" end t)
		    (cond ((re-search-forward "\"Goal\"" end t)
			   (if (looking-at "[ \t]")
			       (progn (forward-char 1) (list (point) "%s"))
			       (list (point) " %s")))
			  (t (list (point) "(\"Goal\" %s)"))))
		   ((re-search-forward "(declare[ \t]+(xargs[ \t]+" end t)
		    (list (point) " :guard-hints ((\"Goal\" %s)) "))
		   (t (forward-char 1)
		      (forward-sexp 3)
		      (if (looking-at "[ \t]*\n")
			  (skip-chars-forward " \t\n"))
		      (list (point) "(declare (xargs :guard-hints ((\"Goal\" %s))))\n"))))
	    ((looking-at "(defthm ") 
	     (cond ((re-search-forward ":hints[ \t]*(" end t)
		    (cond ((re-search-forward "\"Goal\"" end t)
			   (if (looking-at "[ \t]")
			       (progn (forward-char 1) (list (point) "%s"))
			       (list (point) " %s")))
			  (t (list (point) "(\"Goal\" %s)"))))
		   (t (goto-char (- end 1))
		      (list (point) "\n  :hints ((\"Goal\" %s))"))))
	    (t (error "Not a function or theorem"))))))

(defun add-hint-to-defun-at-click (click)
  "Go to click, figure out where to insert, and add selected hint."
  (interactive "e")
  (let ((pos1 (event-start click))
	(end (event-end click))
	(hint (x-popup-dialog click hint-x-popup-menu)))
    (select-window (posn-window pos1))
    (if (numberp (posn-point pos1))
	(goto-char (posn-point pos1)))
    (save-excursion
      (let* ((pair (find-hint-insertion-point))
	     (pos (car pair))
	     (schema (car (cdr pair)))
	     arg)
	(cond ((not (cdr hint)) (goto-char pos) (insert (format schema (car hint))))
	      ((setq arg (get-hint-arg (car (cdr hint))))
	       (goto-char pos)
	       (insert (format schema (format (car hint) arg))))))
      (beginning-of-defun)
      (indent-sexp))))

(defun get-hint-arg (kind)
  (message (format "Click on %s." kind))
  (let ((click (read-event))
	x)
    (setq x (thing-at-click click kind))
    (cond ((null x) nil)
	  ((memq kind '(event symbol)) (if (symbolp x) x))
	  ((memq kind '(number integer)) (if (numberp x) x))
	  ((equal kind 'filename)      (if (stringp x) x))
	  ((memq kind '(cd command)) (if (or (numberp x) (symbolp x)) x))
	  ((memq kind '(sexp sexpr))
	   (if (or (numberp x) (symbolp x) (stringp x) (consp x)) x))
	  (t nil))))

(define-key acl2-mode-map [C-mouse-3] 'add-hint-to-defun-at-click)


