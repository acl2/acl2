;; definline.lisp - The definline and definlined macros.
;; Jared Davis <jared@cs.utexas.edu>
;;
;; This file is in the public domain.  You can freely redistribute it and
;; modify it for any purpose.  This file comes with absolutely no warranty,
;; including the implied warranties of merchantibility and fitness for a
;; particular purpose.

(in-package "ACL2")

; Modified 2014-08 by Jared Davis to remove documentation, to try to discourage
; folks from using this.

(defmacro definline (name formals &rest args)
  ;; Alias for @(see defun-inline)
  ;; Examples:
  ;; @({
  ;;   (include-book \"misc/definline\")
  ;;   (definline car-alias (x)
  ;;     (car x))
  ;; })
  ;; @('definline') is a wrapper for @(see defun-inline).

  ;; We probably shouldn't have this wrapper.  But until ACL2 5.0 there was no
  ;; @('defun-inline'), and @('definline') was implemented using a @(see trust-tag).
  ;; When @('defun-inline') was introduced, we already had many books with
  ;; @('definline') and liked the shorter name, so we dropped the trust tag and
  ;; turned it into a wrapper for @('defun-inline').
  `(defun-inline ,name ,formals . ,args))

(defmacro definlined (name formals &rest args)
  ;; Alias for @(see defund-inline)
  ;; This is a @(see defund)-like version of @(see definline).
  `(defund-inline ,name ,formals . ,args))


(local
 (progn

(defun test (x)
  (declare (xargs :guard (natp x)))
  (+ 1 x))

(definline test2 (x)
  (declare (xargs :guard (natp x)))
  (+ 1 x))

(defun f (x) (test x))
(defun g (x) (test2 x))

;; (disassemble$ 'f) ;; not inlined, as expected
;; (disassemble$ 'g) ;; inlined, as expected
  ))
