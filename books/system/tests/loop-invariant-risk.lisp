; Copyright (C) 2026, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This book is based on feedback from Claude that was passed along by Eric
; Smith.  Specifically, it is based closely on community book
; system/tests/compress1-invariant-risk.lisp, together with an example from
; Claude illustrating that the 'invariant-risk property was (unfortunately) not
; being set based on function calls within loop$.  This book illustrates a bug
; in ACL2 Version 8.7 (evidenced with ACL2 built on SBCL but not on CCL) that
; was fixed on 9/26/2026.

(in-package "ACL2")

; Two ACL2 arrays, allocated back-to-back so their raw simple-vectors are
; adjacent in the heap.
(defconst *ab*
  (list (compress1 'a '((:header :dimensions (4) :maximum-length 6
                                 :default 0 :name a)
                        (0 . 0) (1 . 0) (2 . 0) (3 . 0)))
        (compress1 'b '((:header :dimensions (4) :maximum-length 6
                                 :default 9 :name b)
                        (0 . 9) (1 . 9) (2 . 9) (3 . 9)))))
(defconst *b* (cadr *ab*))

; TRUE, and proved by evaluation before any corruption.
(defthm lemma
  (equal (aref1 'b *b* 0) 9)
  :rule-classes nil)

(defun poke (i v) (declare (xargs :mode :program))
  (loop$ for j from 0 to 0 collect (prog2$ j (aset1 'a (car *ab*) i v))))

(include-book "std/testing/must-fail" :dir :system)

(must-fail
(local (value-triple (poke 10 'boom)))
)

; The rest, commented out by Matt K., is no longer admissible after the bug fix.
#|
(local (assert-event (equal (aref1 'b *b* 0) 'boom)))

; Now (aref1 'b *b* 0) *executes* to BOOM although it is logically 9.
(defthm nil-proved
  nil
  :hints (("Goal" :use lemma))
  :rule-classes nil)
|#
