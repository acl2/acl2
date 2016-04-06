;; Copyright (C) 1985 Free Software Foundation, Inc.
;; Copyright (C) 1994 Free Software Foundation, Inc.

;; Author  : MKSmith (mksmith@cli.com)
;; Begun   : Feb 27 94 
;; Origin  : lisp-mode.el
;; Keywords: acl2, languages

;; This file is for use with GNU Emacs.

;; GNU Emacs is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 2, or (at your option)
;; any later version.

;; GNU Emacs is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;;; Commentary:

;; The base major mode for editing Acl2 code.
;; This mode extends very slightly lisp-mode.el (documented in the Emacs manual).
;; See also inf-acl2.el inf-acl2-mouse.el and inf-acl2-menu.el

;;; Code:

(require 'lisp-mode)

(defvar acl2-mode-syntax-table nil "")
(defvar acl2-mode-abbrev-table nil "")

(if (not acl2-mode-syntax-table)
    (setq acl2-mode-syntax-table
	  (copy-syntax-table lisp-mode-syntax-table)))

(define-abbrev-table 'acl2-mode-abbrev-table ())

(defun acl2-mode-variables (acl2-syntax)
  (lisp-mode-variables nil)
  (cond (acl2-syntax
	  (set-syntax-table acl2-mode-syntax-table)))
  (setq local-abbrev-table acl2-mode-abbrev-table)
  (make-local-variable 'lisp-indent-function)
  (setq lisp-indent-function 'acl2-indent-function))

(defun acl2-shared-lisp-mode-map ()
  "Return the shared lisp-mode-map, independent of Emacs version."
  (if (boundp 'shared-lisp-mode-map)
      shared-lisp-mode-map
    lisp-mode-shared-map))

(defvar acl2-mode-map nil
  "Keymap for ordinary Acl2 mode.  All commands in 
`acl2-shared-lisp-mode-map' are inherited by this map.")

(if (not acl2-mode-map)
    (progn
      (setq acl2-mode-map (make-sparse-keymap))
      (set-keymap-parent acl2-mode-map (acl2-shared-lisp-mode-map))))

(defvar acl2-mode-hook nil)

(defun acl2-mode ()
  "Major mode for editing Acl2 code.
Commands:
Delete converts tabs to spaces as it moves back.
Blank lines separate paragraphs.  Semicolons start comments.
\\{acl2-mode-map}
Note that `run-acl2' may be used either to start an inferior Acl2 job
or to switch back to an existing one.

Entry to this mode calls the value of `acl2-mode-hook'
if that value is non-nil."
  (interactive)
  (kill-all-local-variables)
  (use-local-map acl2-mode-map)
  (setq major-mode 'acl2-mode)
  (setq mode-name "Acl2")
  (acl2-mode-variables t)
  (set-syntax-table acl2-mode-syntax-table)
  (run-hooks 'acl2-mode-hook))

;; Trying this as a local variable
;; See last entry in ACL2-MODE-VARIABLES function.
;; (defconst lisp-indent-function 'acl2-indent-function "")

(defvar last-sexp nil)

;; Identical to LISP-INDENT-FUNCTION except checks acl2-indent-hook
;; first for indentation.  Allows user to format Acl2 differently from
;; lisp.
(defun acl2-indent-function (indent-point state)
  (let ((normal-indent (current-column))
	(last-sexp (point)))
    (goto-char (1+ (elt state 1)))
    (parse-partial-sexp (point) last-sexp 0 t)
    (if (and (elt state 2)
             (not (looking-at "\\sw\\|\\s_")))
        ;; car of form doesn't seem to be a a symbol
        (progn
          (if (not (> (save-excursion (forward-line 1) (point))
                      last-sexp))
              (progn (goto-char last-sexp)
                     (beginning-of-line)
                     (parse-partial-sexp (point) last-sexp 0 t)))
          ;; Indent under the list or under the first sexp on the
          ;; same line as last-sexp.  Note that first thing on that
          ;; line has to be complete sexp since we are inside the
          ;; innermost containing sexp.
          (backward-prefix-chars)
          (current-column))
      (let ((function (buffer-substring (point)
					(progn (forward-sexp 1) (point))))
	    method)
	(setq method (or (get (intern-soft function) 'acl2-indent-hook)
			 (get (intern-soft function) 'lisp-indent-function)
			 ;; Why does -hook follow -function?
			 (get (intern-soft function) 'lisp-indent-hook)))
	(cond ((or (eq method 'defun)
		   (and (null method)
			(> (length function) 3)
			(string-match "\\`def" function)))
	       (lisp-indent-defform state indent-point))
	      ((integerp method)
	       (lisp-indent-specform method state
				     indent-point normal-indent))
	      (method
		(funcall method state indent-point)))))))

;; (put 'progn 'lisp-indent-function 0), say, causes progn to be indented
;; like defun if the first form is placed on the next line, otherwise
;; it is indented like any other form (i.e. forms line up under first).

(put 'if 'acl2-indent-hook nil)	;changed from 2 in lisp.
(put 'mv-let 'acl2-indent-hook 2)

(provide 'acl2-mode)

;;; acl2-mode.el ends here


