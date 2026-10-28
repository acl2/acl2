; This book was produced by Claude and passed along by Eric Smith.  It
; illustrates a soundness bug (evidenced with ACL2 built on SBCL) fixed before
; ACL2 Version 8.8.  It is based closely on community book
; system/tests/compress1-invariant-risk.lisp.

; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; The bug: *boot-strap-invariant-risk-alist* (defuns.lisp) still had an entry
; (check-sum-inc . nil), left over from a built-in function of that name that
; was removed from ACL2 in 2023.  Put-invariant-risk consults that alist for
; user-defined functions too, so a user's :program-mode function named
; CHECK-SUM-INC got no 'invariant-risk property, even when it called aset1.
; Then a call of it went straight to raw Lisp, where aset1 does no bounds check
; and can write into a different array.

(in-package "ACL2")

(include-book "std/testing/must-fail" :dir :system)

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

; A :program-mode wrapper around aset1, which has invariant-risk, so the
; wrapper should have invariant-risk too.  Before the fix it did not, solely
; because of its name.
(defun check-sum-inc (i v)
  (declare (xargs :mode :program))
  (aset1 'a (car *ab*) i v))

; This holds on every host Lisp after the fix.
(assert-event (getpropc 'check-sum-inc 'invariant-risk))

; Before the fix, this out-of-bounds write overwrote the first element of
; array b (in ACL2 built on SBCL).  Now it causes a guard violation.
(must-fail
 (local (value-triple (check-sum-inc 10 'boom))))

(must-fail
 (local (assert-event (equal (aref1 'b *b* 0) 'boom))))

; Before the fix, (aref1 'b *b* 0) *executed* to BOOM although it is logically
; 9, so this proof of nil succeeded.
(must-fail
 (defthm nil-proved
   nil
   :hints (("Goal" :use lemma))
   :rule-classes nil))
