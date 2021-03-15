; Copyright (C) 2021, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This is boiled down from books/centaur/vl/loader/lexer/tokens.lisp.  As of
; 2/10 we got a slow-alist error when including this certified book with an
; earlier version of our final changes to early loading of compiled files in
; mid-February 2021.

; The local event below was critical for getting the error.  So was loading the
; compiled file at include-book time.

; Below, "t1l" comes from the filename.

(in-package "ACL2")

(local (defun t1l-fn (x) x))

(defconst *t1l*
  (make-fast-alist '((:c . t) (:d . t))))

(defun t1l-p (x)
  (consp (hons-get x *t1l*)))

(defthm symbolp-when-t1l-p ; symbolp-when-vl-plaintokentype-p
  (implies (t1l-p x)
           (and (symbolp x)
                (not (equal x t))
                (not (equal x nil))))
  :rule-classes :compound-recognizer)
