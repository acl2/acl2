; Copyright (C) 2014, Regents of the University of Texas
; Written by Matt Kaufmann (original date March, 2014)
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Warning: If you change this book, consider changing the documentation in
; with-supporters.lisp, which refers to this book.

(in-package "ACL2")

(defun mac1-fn (x)
  x)

(defmacro mac1 (x)
  (mac1-fn x))

(defun g1 (x)
  (declare (xargs :guard t))
  (mac1 x))

(defun mac2-fn-b (x)
  x)

(defun mac2-fn (x)
  (mac2-fn-b x))

(defmacro mac2 (x)
  (mac2-fn x))

(add-macro-alias mac2 g2)

(defun g2 (x)
  (declare (xargs :guard (g1 x)))
  (mac2 x))

(defun g3 (x)
  (g2 x))

