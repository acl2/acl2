; RTL - A Formal Theory of Register-Transfer Logic and Computer Arithmetic
; Copyright (C) 1995-2013 Advanced Mirco Devices, Inc.
;
; Contact:
;   David Russinoff
;   http://www.russinoff.com/
;
; See license file books/rtl/rel11/license.txt.
;
; Author: David M. Russinoff (david@russinoff.com)

(in-package "ACL2")

;;These macros facilitate localization of events:

(defmacro local-defun (&rest body)
  (list 'local (cons 'defun body)))

(defmacro local-defund (&rest body)
  (list 'local (cons 'defund body)))

(defmacro local-defthm (&rest body)
  (list 'local (cons 'defthm body)))

(defmacro local-defthmd (&rest body)
  (list 'local (cons 'defthmd body)))

(defmacro local-in-theory (&rest body)
  (cons 'local
	(cons (cons 'in-theory (append body 'nil))
	      'nil)))
