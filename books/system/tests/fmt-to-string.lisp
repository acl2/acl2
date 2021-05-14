; Copyright (C) 2017, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; The tests in this file could serve as examples for :doc printing-to-strings.
; But the main point is to include them in the regression, since as commented
; below, the behavior was wrong through ACL2 Version 7.4.

(in-package "ACL2")

(defconst *s1*
  "abc
defge")

(defconst *s2*
  (string-append-lst (make-list 20 :initial-element *s1*)))

(assert-event
 (mv-let (col str)
   (fmt1-to-string "~s0"
                   (list (cons #\0 *s2*))
                   0
                   :fmt-control-alist '((write-for-read . nil)))
   (and (eql col 5) ; for Version 7.4 and before: 24, and str had "\" breaks
        (equal str *s2*))))

(assert-event
 (mv-let (col str)
   (fmt1-to-string "~S0"
                   (list (cons #\0 *s2*))
                   0
                   :fmt-control-alist '((write-for-read . nil)))
   (and (eql col 5) ; for Version 7.4 and before: 180
        (equal str *s2*))))

; The following used the global evisc-table to get the wrong value for *c* (13,
; instead of 7 in this encapsulate) until the fmt1-to-string was fixed on
; 5/13/2021.  This allowed for proving (equal *c* 7) outside the encapsulate
; and thus driving nil.
(encapsulate
  ()
  (local (table evisc-table '(a b c) "<my-abc-list>"))
  (defconst *c*
    (mv-let (col s)
      (fmt1-to-string "~x0" (list (cons #\0 '(a b c))) 0)
      (declare (ignore s))
      col))
  (defthm it-is-7
    (equal *c* 7)
    :rule-classes nil))
