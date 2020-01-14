; Copyright (C) 2013, Regents of the University of Texas
; Written by Matt Kaufmann and J Strother Moore
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.
; Contributions by Alessandro Coglio

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)

(defsection keyword-to-keyword-value-list-alistp
  :parents (std/typed-alists)
  :short "Recognize alists from keywords to keyword-value lists."
  :long
  "<p>A keyword-value list is a true list of even length
      whose even-position elements are keywords;
      see @(tsee keyword-value-listp).</p>"

  (defun keyword-to-keyword-value-list-alistp (x)
    (declare (xargs :guard t))
    (cond ((atom x) (null x))
          (t (and (consp (car x))
                  (keywordp (car (car x)))
                  (keyword-value-listp (cdr (car x)))
                  (keyword-to-keyword-value-list-alistp (cdr x)))))))
