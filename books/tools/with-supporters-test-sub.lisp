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

(defund g4 (x)
  (declare (xargs :guard t))
  (consp x))

(defun g5 (x)
  (declare (xargs :guard (g4 x)))
  (car x))

(defstobj st fld)

(defstub stub1 (x) t)

(defun g6 (x)
  (declare (xargs :guard t))
  x)

(defattach stub1 g6)

(defstub stub2 (x) t)

(defun g7 (x)
  (declare (xargs :guard t))
  (cons x x))

(defun g8 (x)
  (declare (xargs :guard t))
  (list x x))

(defattach (stub1 g7) (stub2 g8))

(defstub stub3 (x) t)

(defund g9 (x)
  (declare (xargs :guard t))
  (len x))

(defattach stub3 g9)

; Test that with-supporters includes (essentially) necessary verify-guards
; events.

(defun g10 (x)
  x)

(verify-guards g10)

(defun g11 (x)
  (declare (xargs :guard t))
  (g10 x))

; Test that with-supporters includes necessary verify-termination events.

(defun g12 (x)
  (declare (xargs :mode :program))
  x)

(verify-termination g12)

(defun g13 (x)
  (g12 x))

; Test getting :program mode right.

(encapsulate
  ()

  (program)

  (defun g-prog (x)
    x))

(defmacro mac (x)
  (g-prog x))

; Test table events.

(table my-tbl nil nil
       :guard (g13 val))

(table my-tbl 3 4)

(table my-tbl 3 5)

; Test non-trivial encapsulate

(defun g14 (x) x)

(encapsulate
  ((e1 (x) t))
  (local (defun e1 (x) x))
  (defthm e1-prop
    (equal (g14 (e1 x)) x)))

; Test more complex encapsulate

(defun g15 (x y) (< x y))

(defun-sk g16 (x)
  (exists y (g15 x y)))
