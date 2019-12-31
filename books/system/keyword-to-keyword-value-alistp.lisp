; Copyright (C) 2013, Regents of the University of Texas
; Written by Matt Kaufmann and J Strother Moore
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.
; Contributions by Alessandro Coglio

(in-package "ACL2")

; Recognize an alist from keywords to keyword-value lists.
; A keyword-value list is a true list of even length
; whose even-position elements are keywords
; (see :doc keyword-value-listp).

(defun keyword-to-keyword-value-list-alistp (x)
  (declare (xargs :guard t))
  (cond ((atom x) (null x))
        (t (and (consp (car x))
                (keywordp (car (car x)))
                (keyword-value-listp (cdr (car x)))
                (keyword-to-keyword-value-list-alistp (cdr x))))))
