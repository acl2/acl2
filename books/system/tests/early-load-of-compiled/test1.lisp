; Copyright (C) 2021, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This is just a gratuitous extra test; see test1-local.lisp for a similar test
; that caused an error at one point during development.

; Below, "t2" comes from the filename.

(in-package "ACL2")

(defconst *t1*
  (make-fast-alist '((:a . t) (:b . t))))

(defun t1-p (x)
  (consp (hons-get x *t1*)))

(defthm symbolp-when-t1-p ; symbolp-when-vl-plaintokentype-p
  (implies (t1-p x)
           (and (symbolp x)
                (not (equal x t))
                (not (equal x nil))))
  :rule-classes :compound-recognizer)
