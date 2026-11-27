; This book was produced by Claude and passed along by Eric Smith.  It
; illustrates a soundness bug fixed before ACL2 Version 8.8.

; Logically, (maybe-flush-and-compress1 name ar) is (compress1 name ar).  But
; its raw Lisp code returned ar unchanged whenever ar was the alist currently
; associated with name, even though that alist need not be compressed: aset1
; conses a new pair onto it.  So evaluation disagreed with the definition.

(in-package "ACL2")

(include-book "std/testing/must-fail" :dir :system)

(defconst *h*
  '((:header :dimensions (3) :maximum-length 10 :default 0)))

; Before the fix, the call of maybe-flush-and-compress1 below evaluated to
; ((0 . 1) (:header ...)), while compress1 puts the header first.

(must-fail
 (defthm nil-proved
   nil
   :hints (("Goal" :use (:instance maybe-flush-and-compress1
                                   (name 'a)
                                   (ar (aset1 'a (compress1 'a *h*) 0 1)))))
   :rule-classes nil))

(assert-event
 (equal (maybe-flush-and-compress1 'a (aset1 'a (compress1 'a *h*) 0 1))
        (cons (car *h*) '((0 . 1)))))

; An array that is already compressed is returned unchanged.

(assert-event
 (equal (maybe-flush-and-compress1 'a (compress1 'a (cons '(2 . 3) *h*)))
        (cons (car *h*) '((2 . 3)))))
