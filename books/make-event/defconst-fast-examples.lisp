; Copyright (C) 2013, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Here we illustrate the defconst-fast macro, defined in defconst-fast.lisp.
; An interesting experiment, after certifying this book, is as follows:

; Start up ACL2.
; (trace$ binary-append)
; (include-book "defconst-fast-examples")

; Then the trace should show calls of binary-append on '(test0 a b c) and
; '(test3 a b c), but not on '(test1-fast a b c) or '(test2-fast a b c).

(in-package "ACL2")

(include-book "defconst-fast")

(defconst *test0* ; old defconst
  (append '(test0 a b c) nil))

(defconst-fast *test1-fast*
  (append '(test1-fast a b c) nil))

(defconst-fast *test2-fast*
  (append '(test2-fast a b c) nil)
;; [Jared] removed the doc section here in my effort to remove the legacy
;; documentation system
; Matt K. mod: Comment out doc string (disallowed after ACL2 8.3).
#|
 "*test2* is just a test of defconst-fast~/~/

  Not much to say about *test2*.....~/"
|#)

(defconst *test3* ; old defconst
  (append '(test3 a b c) nil))
