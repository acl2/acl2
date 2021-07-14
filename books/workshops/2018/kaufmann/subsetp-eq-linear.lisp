; Copyright (C) 2018, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)

(defun subsetp-eq-linear (lst1 lst2)
  (declare (xargs :mode :logic
                  :guard (and (symbol-listp lst1)
                              (symbol-listp lst2)
                              (strict-symbol<-sortedp lst1)
                              (strict-symbol<-sortedp lst2))))
  (cond ((endp lst1) t)
        (t (let ((tail (member-eq (car lst1) lst2)))
             (and tail
                  (subsetp-eq-linear (cdr lst1) (cdr tail)))))))

; Challenge: Prove that this is logically equal to subsetp, and perhaps even
; use mbe so that logically, this is trivially just subsetp.

(defxdoc subsetp-eq-linear
  :parents (kestrel-utilities)
  :short "A linear-time subset test for sorted lists of symbols"
  :long "
 @({
 General Form:

 (subsetp-eq-linear lst1 lst2)
 })

 <p>where the @(see guard) specifies that both arguments are true-lists of
 symbols, sorted by @(tsee symbol<).  This computes the same result as
 @('(subsetp-eq lst1 lst2)') (challenge: prove this!), but unlike @(tsee
 subsetp-eq), it does so in linear time.</p>")
