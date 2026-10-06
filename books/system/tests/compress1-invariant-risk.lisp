; This book, modified only as noted below, was produced by Claude and passed
; along by Eric Smith.  It illustrates a bug in ACL2 Version 8.7 (evidenced
; with ACL2 built on SBCL but not on CCL) that was fixed on 9/20/2026, before
; the release of ACL2 Version 8.8.

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

; Added by Matt Kaufmann:
(include-book "std/testing/must-fail" :dir :system)

; A :program-mode wrapper around COMPRESS1 with a guard-violating alist.
; PUT-INVARIANT-RISK gives POKE no 'invariant-risk property, because
; COMPRESS1 is deliberately absent from *BOOT-STRAP-INVARIANT-RISK-ALIST*
; (defuns.lisp).  So the call goes straight to raw Lisp, and raw COMPRESS1
; does (setf (svref ar index) ...) with no bounds check.
(defun poke (i v) (declare (xargs :mode :program))
  (compress1 'a (list '(:header :dimensions (4) :maximum-length 6
                                :default 0 :name a)
                      (cons i v))))

(must-fail ; The must-fail wrapper was added by Matt Kaufmann:
(local (value-triple (poke 10 'boom)))
)

(must-fail ; The must-fail wrapper was added by Matt Kaufmann:
(local (assert-event (equal (aref1 'b *b* 0) 'boom)))
)

(must-fail ; The must-fail wrapper was added by Matt Kaufmann:
; Now (aref1 'b *b* 0) *executes* to BOOM although it is logically 9.
(defthm nil-proved
  nil
  :hints (("Goal" :use lemma))
  :rule-classes nil)
)
