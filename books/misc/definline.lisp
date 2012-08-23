;; definline.lisp - The definline and definlined macros.
;; Jared Davis <jared@cs.utexas.edu>
;;
;; This file is in the public domain.  You can freely redistribute it and
;; modify it for any purpose.  This file comes with absolutely no warranty,
;; including the implied warranties of merchantibility and fitness for a
;; particular purpose.

(in-package "ACL2")
(include-book "doc-section")

;; BOZO -- as a temporary hack, we need a way to mangle the formals since we
;; can't use stobj names as macro args.  Matt's probably going to fix this, or
;; fix defun-inline to work with stobj arguments in some other way, at which
;; point we can change definline to just be a wrapper for defun-inline.

(defun definline-mangle-formal (x)
  (declare (xargs :guard (symbolp x)))
  ;; I use the ACL2 package because if we just use the package-of X, we can get
  ;; into trouble when args nave names like "string" that are in the Common
  ;; Lisp package: we're not allowed to intern new symbols into COMMON-LISP::
  (intern$ (concatenate 'string "MANGLED_" (symbol-name x)) "ACL2"))

(defun definline-mangle-formals (x)
  (declare (xargs :guard (symbol-listp x)))
  (if (atom x)
      nil
    (cons (definline-mangle-formal (car x))
          (definline-mangle-formals (cdr x)))))

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
  (declare (xargs :guard (symbol-listp formals)))
  (let ((name$inline
         (intern-in-package-of-symbol
          (concatenate 'string (symbol-name name) *inline-suffix*)
          name))
        (mangled-formals
         (definline-mangle-formals formals)))
    `(progn (defmacro ,name ,mangled-formals
              (list ',name$inline . ,mangled-formals))
            (add-macro-fn ,name ,name$inline)
            (defun ,name$inline ,formals . ,args))))

(defmacro definlined (name formals &rest args)
  ":Doc-Section misc
  Alias for ~ilc[defund-inline]~/
  This is a ~il[defund]-like version of ~il[definline].~/~/"
  (declare (xargs :guard (symbol-listp formals)))
  (let ((name$inline
         (intern-in-package-of-symbol
          (concatenate 'string (symbol-name name) *inline-suffix*)
          name))
        (mangled-formals
         (definline-mangle-formals formals)))
    `(progn (defmacro ,name ,mangled-formals
              (list ',name$inline . ,mangled-formals))
            (add-macro-fn ,name ,name$inline)
            (defund ,name$inline ,formals . ,args))))


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
