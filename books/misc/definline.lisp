;; definline.lisp - The definline and definlined macros.
;; Jared Davis <jared@cs.utexas.edu>
;;
;; This file is in the public domain.  You can freely redistribute it and
;; modify it for any purpose.  This file comes with absolutely no warranty,
;; including the implied warranties of merchantibility and fitness for a
;; particular purpose.

(in-package "ACL2")
(include-book "doc-section")

(defmacro definline (name formals &rest args)
  ":Doc-Section misc
  Alias for ~ilc[defun-inline]~/
  Examples:
  ~bv[]
    (include-book \"misc/definline\")
    (definline car-alias (x)
      (car x))
  ~ev[]
  ~c[definline] is a wrapper for ~ilc[defun-inline].

  We probably shouldn't have this wrapper.  But until ACL2 5.0 there was no
  ~c[defun-inline], and ~c[definline] was implemented using a ~il[trust-tag].
  When ~c[defun-inline] was introduced, we already had many books with
  ~c[definline] and liked the shorter name, so we dropped the trust tag and
  turned it into a wrapper for ~c[defun-inline].~/~/"
  `(defun-inline ,name ,formals . ,args))

(defmacro definlined (name formals &rest args)
  ":Doc-Section misc
  Alias for ~ilc[defund-inline]~/
  This is a ~il[defund]-like version of ~il[definline].~/~/"
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
