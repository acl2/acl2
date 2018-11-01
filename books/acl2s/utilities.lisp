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
  :parents (acl2-sedan)
  :short "A macro that 
creates an arbitrary-arity macro given a binary function
and associates the function name with the macro name using
[add-macro-fn]."
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
@('right-associate-p') is an optional argument, which 
 Given
one argument, the macro will just return that argument. Given more
than one argument, the macro will expand to a right-associated call of
the function. For example:

(set-union) expands to nil

(set-union arg1) expands to arg1

(set-union arg1 arg2) expands to (binary-set-union arg1 arg2)

(set-union arg1 arg2 arg3) expands to 
(binary-set-union arg1 (binary-set-union arg2 arg3))

and so on.

Since [add-macro-fn] is used, 
</p>")

(defxdoc acl2-pc::repeat-until-done
  :parents (proof-builder-commands acl2-sedan)
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
[add-macro-fn]."
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
@('right-associate-p) is an optional argument, which 
 Given
one argument, the macro will just return that argument. Given more
than one argument, the macro will expand to a right-associated call of
the function. For example:

(set-union) expands to nil

(set-union arg1) expands to arg1

(set-union arg1 arg2) expands to (binary-set-union arg1 arg2)

(set-union arg1 arg2 arg3) expands to 
(binary-set-union arg1 (binary-set-union arg2 arg3))

and so on.

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


;; Similar to skip-proofs, except that we first perform
;; testing. Supports testing for thm, defthm, defcong, defequiv, and
;; defrefinement form. All other forms are just turned into
;; skip-proofs forms, without testing. If there are opportunities to
;; do so, we can try supporting testing for other types of forms.
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

(defmacro tlp (x)
  `(true-listp ,x))

(add-macro-fn tlp true-listp)

(defmacro tl-fix (x)
  `(acl2::true-list-fix ,x))

(add-macro-fn tl-fix acl2::true-list-fix)

(defmacro app (&rest rst)
  `(append ,@rst))

(add-macro-fn app binary-append)
