; ACL2 Version 1.9

; Copyright (C) 1989-1996 Computational Logic, Inc. (CLI).  All rights reserved.

; Use of this software constitutes agreement with the terms of the
; license agreement, found in the file LICENSE.

(in-package "ACL2")

(defparameter *infix-error-flg* nil)

(symbol-name 'acl2-output-channel::standard-error-output-0)
(setf (get 'acl2-output-channel::standard-error-output-0
           *open-output-channel-type-key*) :character)
(setf (get 'acl2-output-channel::standard-error-output-0
           *open-output-channel-key*) *standard-output*)

(defconst *standard-eo* 'acl2-output-channel::standard-error-output-0)

(f-put-global 'standard-eo 'acl2-output-channel::standard-error-output-0 state)

(defun infix-error-fmt (hardp ctx str alist state)

; Almost the same as ACL2 error-fmt.

  (setq *infix-error-flg* t)

  (let ((channel *standard-eo*))	;(f-get-global 'standard-co state)
    (mv-let (col state)
      (fmt1 (if hardp
                "~%~%HARD ACL2 ERROR"
              "~%~%ACL2 Error")
            nil 0 channel state nil)
      (mv-let (col state)
        (fmt-in-ctx ctx col channel state)
        (mv-let (col state)
          (fmt1 str alist col channel state (default-evisc-tuple state))
          (fmt1 "~%~%" nil col channel state nil))))))

(defun string-output-fn (form)
  `(let ((saved-stream (get 'acl2-output-channel::standard-character-output-0
                            *open-output-channel-key*))
         *infix-error-flg*
         (saved-fn (symbol-function 'error-fmt)))
     (unwind-protect
         (progn
           (setf (symbol-function 'error-fmt)
                 (symbol-function 'infix-error-fmt))
           (let ((ans
                  (with-output-to-string
                   (foo)
                   (setf (get 'acl2-output-channel::standard-character-output-0
                              *open-output-channel-key*)
                         foo)
                   ,form)))
             (cons *infix-error-flg* ans)))
       (setf (symbol-function 'error-fmt)
             saved-fn)
       (setf (get 'acl2-output-channel::standard-character-output-0
                  *open-output-channel-key*)
             saved-stream))))

(defmacro string-output (form)
  (string-output-fn form))

(defun set-infix-markup-table (tbl state)
  (f-put-global 'infix-markup-table tbl state))

(defun infix-markup-table (state)
  (or (and (f-boundp-global 'infix-markup-table state)
           (f-get-global 'infix-markup-table state))
      (doc-markup-table state)))

(defun set-infix-char-subst-table (tbl state)
  (f-put-global 'infix-char-subst-table tbl state))

(defun infix-char-subst-table (state)
  (or (and (f-boundp-global 'infix-char-subst-table state)
           (f-get-global 'infix-char-subst-table state))
      (doc-char-subst-table state)))

;; For examples of markup-tables and char-subst-tables see
;; scribe-init.lisp and latex-init.lisp

(defun infix-preprocess-doc (str &key
                              (markup-table (infix-markup-table *the-live-state*))
                              (char-subst-table (infix-char-subst-table *the-live-state*))
                              (prefix "")
                              fmt-alist
                              (name '|<some name>|)
                              par-p
                              &aux (state *the-live-state*))
  (string-output
   (cond
    ((doc-stringp str)
     (pprogn
      (print-doc-string-part 0 str prefix markup-table char-subst-table fmt-alist
                             *standard-co* name par-p state)
      (print-doc-string-part 1 str prefix markup-table char-subst-table fmt-alist
                             *standard-co* name par-p state)
      (print-doc-string-part 2 str prefix markup-table char-subst-table fmt-alist
                             *standard-co* name par-p state)))
    ;; Otherwise, print the string, stopping at the first ~/ (if any, else to end of string).
    ;; Note that unlike the other case, no special effort is made to
    ;; strip off leading spaces using get-doc-string-de-indent [see below].
    (t (print-doc-string-part1 str
                               0
                               (length str)
                               0;;(get-doc-string-de-indent str)
                               prefix
                               markup-table
                               char-subst-table
                               fmt-alist
                               *standard-co*
                               name
                               state
                               (if par-p :par 0))))))

;;; Compute args for key.

(defun keyword-command-arg-number (key state)
  (declare (xargs :mode :program))
  (let ((temp (assoc-eq key (ld-keyword-aliases state))))
    (cond (temp (cadr temp))
	  ((eq key :q) 0)
	  (t
	   (let ((sym (intern (symbol-name key) "ACL2"))
		 (wrld (w state)))
	     (cond
	      ((function-symbolp sym wrld)
	       (length (formals sym wrld)))
	      ((getprop sym 'macro-body nil 'current-acl2-world wrld)
	       (let ((args (getprop sym 'macro-args nil 'current-acl2-world wrld)))
		 (if (no-lambda-keywordsp args)
		     (length args)
		     nil)))
	      (t nil)))))))

;; The following two functions support the reading of
;; keyword commands, using ACL2 mechanisms for computing
;; number of args, if allowed.

(proclaim '(ftype (function (t t) t)
		  user::read-keyword-form))

(defvar user::acl2-markup-table)
(defvar user::acl2-char-subst-table)

(defun user::acl2-parse-string (doc)
  (infix-preprocess-doc doc
			:markup-table user::acl2-markup-table
			:char-subst-table user::acl2-char-subst-table))

(defun user::acl2-keywordp (key) (keywordp key))

(defun user::read-keyword-command (key)
  (user::read-keyword-form key
			   (keyword-command-arg-number key *the-live-state*)))
