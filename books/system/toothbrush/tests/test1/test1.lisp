; Copyright (C) 2014, ForrestHunt, Inc.
; Written by Matt Kaufmann, November, 2014
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(defun who-cares (x)
  x)

(defun f (x) x)

(defun g (x) (cdr x))

; Irrelevant function, which shouldn't be included in the toothbrush:
(defun h (x)
  (g x))

; Test that supporters of macros are picked up.

(defmacro id-fn3 (x)
  x)

(defmacro id-mac3 (x)
  (id-fn3 x))

(defmacro id-mac2 (x)
  (id-mac3 x))

(defun id-fn2 (x)
  (id-mac2 x))

(defun id-fn (x)
  (id-fn2 x))

(defmacro id-mac (x)
  (id-fn x))

(defun len-test (x)
  (id-mac (cond ((consp x) (len (g x)))
                (t (* 2 (length (append (make-list (f x))
                                        (cons x nil))))))))

; The following is harmless -- included only to show that it's harmless.
(defevaluator evl evl-list
  ((length x) (member-equal x y)))

; Define default function for dependencies (see Makefile):
(defun top (x)
  (len-test x))
