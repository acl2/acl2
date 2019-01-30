#|$ACL2s-Preamble$;
; Copyright (C) 2018, Northeastern University
; Written by Pete Manolios
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.
(include-book ;; Newline to fool ACL2/cert.pl dependency scanner
 "portcullis")
(begin-book t);$ACL2s-Preamble$|#

(in-package "ACL2S")
(include-book "kestrel/utilities/proof-builder-macros" :dir :system)

(defxdoc ACL2s-utilities
  :parents (acl2::acl2-sedan)
  :short "Utilities used in ACL2s."
  :long "This is a collection of utilities used in ACL2s, the ACL2 Sedan.")

(defxdoc acl2-pc::repeat-until-done
  :parents (acl2::proof-builder-commands acl2s-utilities)
  :short "A proof-builder command that repeats the given instructions
  until all goals have been proved" 
  :long "@({
 Example:
 (repeat-until-done induct (repeat bash))

 General Form:
 (repeat-until-done instr1 ... instrk)
 })

 <p>where each @('instri') is a proof-builder instruction.</p>")

(define-pc-macro repeat-until-done (&rest instrs)
  (value
   `(repeat (do-all
             ,@(append instrs 
                       `((negate (when-not-proved fail))))))))

(defxdoc make-n-ary-macro
  :parents (acl2s-utilities)
  :short "A macro that 
creates an arbitrary-arity macro given a binary function
and associates the function name with the macro name using
@(see add-macro-fn)."
  :long "@({
 Examples:
 (make-n-ary-macro set-union binary-set-union nil t)

 (make-n-ary-macro ^ expt 1)

 General Form:
 (make-n-ary-macro new-macro-name binary-fun-name identity right-associate-p)
 })

 <p>where @('new-macro-name') is the name of the macro to define,
@('binary-fun-name') is the name of an existing binary function and
@('identity') is what the macro should return with no arguments.
@('right-associate-p') is an optional argument, which when set to
@('t') flattens right-associated arguments (see @(see add-macro-fn)).
</p>

<p>
Given
one argument, the macro will just return that argument. Given more
than one argument, the macro will expand to a right-associated call of
the function. For example:

@({
(set-union) expands to nil

(set-union arg1) expands to arg1

(set-union arg1 arg2) expands to (binary-set-union arg1 arg2)

(set-union arg1 arg2 arg3) expands to 
(binary-set-union arg1 (binary-set-union arg2 arg3))

and so on.
})
</p>")

(defmacro make-n-ary-macro (macro bin-fun id &optional
                                  right-associate-p)
  (declare (xargs :guard (and (symbolp macro) (symbolp bin-fun)
                              (booleanp right-associate-p))))
  `(progn
     (defmacro ,macro (&rest rst)
       (cond ((null rst) ,id)
             ((null (cdr rst)) (car rst))
             (t (xxxjoin ',bin-fun rst))))
     (add-macro-fn ,macro ,bin-fun ,right-associate-p)))

(defxdoc test-then-skip-proofs
  :parents (acl2s-utilities)
  :short "The ACL2s version of skip-proofs."
  :long
"A macro that is similar to skip-proofs, except that we first perform
testing. The macro supports testing for @(see thm), 
@(see defthm), @(see defcong), @(see defequiv), and
@(see defrefinement) forms. All other forms are just turned into
skip-proofs forms, without testing."
)

;; If there are opportunities to do so, we should extend
;; test-then-skip-proofs so that it supports more forms.

(defmacro test-then-skip-proofs (thm)
  (declare (xargs :guard (true-listp thm)))
  (cond
   ((equal (car thm) 'defthm)
    `(progn!
      (acl2s::test? ,(third thm))
      (skip-proofs ,thm)))
   ((equal (car thm) 'thm)
    `(progn!
      (acl2s::test? ,(second thm))
      (skip-proofs ,thm)))
   ((member (car thm) '(acl2::defcong acl2::defequiv acl2::defrefinement))
    `(make-event
      (er-let* ((defthm (acl2::macroexpand1* ',thm 'ctx (w state) state)))
               (value `(progn! (acl2s::test? ,(second (third defthm)))
                               (skip-proofs ,',thm))))))
   (t `(skip-proofs ,thm))))

(defmacro thm-no-test (&rest args)
  `(acl2::with-outer-locals
    (local (acl2s-defaults :set testing-enabled nil))
    (make-event (mv-let (erp val state)
                        (thm ,@args)
                        (declare (ignore val))
                        (cond (erp (er soft 'thm "The thm failed"))
                              (t (value `(value-triple :passed))))))))

(defmacro defthm-no-test (name &rest args)
  `(acl2::with-outer-locals
    (local (acl2s-defaults :set testing-enabled nil))
    (defthm ,name ,@args)))

#|
(defunc symbol-string-app (l)
  :input-contract (symbol-listp l)
  :output-contract (stringp (symbol-string-app l))
  (if (endp l)
      ""
    (concatenate 'string (symbol-name (car l))
                 (symbol-string-app (cdr l)))))

(defunc make-symbl (l)
  :input-contract (and (symbol-listp l) l)
  :output-contract (symbolp (make-symbl l))
  (intern-in-package-of-symbol
   (symbol-string-app l)
   (car l)))
|#

(defun symbol-string-app (l)
  (declare (xargs :guard (symbol-listp l)))
  (if (endp l)
      ""
    (concatenate 'string (symbol-name (car l))
                 (symbol-string-app (cdr l)))))

(defun make-symbl (l)
  (declare (xargs :guard (symbol-listp l)))
  (intern-in-package-of-symbol
   (symbol-string-app l)
   (car l)))

(defun make-sym (s suf)
; Returns the symbol s-suf.
  (declare (xargs :guard (and (symbolp s) (symbolp suf))))
  (make-symbl (list s '- suf)))

(defun get-alist (key alist)
  (declare (xargs :guard (alistp alist)))
  (cdr (assoc-equal key alist)))

