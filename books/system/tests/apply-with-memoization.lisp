; Copyright (C) 2019, Regents of the University of Texas and ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Before February 2019, the following book failed to certify because
; memoization tables weren't cleared when removing badges.

; The assert! tests below failed because instead of the expected value, a stale
; value of '(3 . 4) was returned.  Now, ACL2 notices that foo-1 (resp. foo-2)
; depends ancestrally on apply$-userfn, and the undoing of the badge of g-1
; (resp. g-2) in a preceding encapsulate thus triggers flushing of the memo
; table of foo1 (resp. foo-2).  Similar issues apply to the final two examples,
; regarding badges.

; See the Essay on Memoization with Attachments in the ACL2 sources for how
; this happens, but here is a summary.  Global *defattach-fns* is extended by
; *special-cltl-cmd-attachment-mark* when undoing the badge on g above (when
; the defwarrant is undone after the first pass of encapsulate), and indeed
; when any badge is undone.  That special mark in *defattach-fns* triggers
; flushing of the memo table for foo by function
; update-memo-entries-for-attachments, because foo has apply$-userfn as an
; (extended) ancestor.

(in-package "ACL2")

(include-book "projects/apply/top" :dir :system)

(include-book "misc/assert" :dir :system)

(defun foo-1 (fn args)
  (declare (xargs :guard (true-listp args)))
  (apply$-userfn fn args))

(memoize 'foo-1 :aokp t) ; problem goes away without :aokp t

(defconst *list-3* (list 3))

(encapsulate
  ()
  (local (defun g-1 (x)
           (declare (xargs :guard t))
           (cons x 4)))
  (local (defwarrant g-1))
  (make-event (prog2$ (foo-1 'g-1 *list-3*) ; (3 . 4)
                      '(value-triple t))))

(defun$ g-1 (x) (declare (xargs :guard t)) (cons x 5))

(assert! (equal (foo-1 'g-1 *list-3*)
; See the comment near the top of this file.
                '(3 . 5)))

; Here is the analogous example using apply$ instead of apply$-userfn.

(defun foo-2 (fn args)
  (declare (xargs :guard (and (true-listp args)
                              (symbolp fn))))
  (apply$ fn args))

(memoize 'foo-2 :aokp t) ; problem goes away without :aokp t

; Redundant:
(defconst *list-3* (list 3))

(encapsulate
  ()
  (local (defun g-2 (x)
           (declare (xargs :guard t))
           (cons x 4)))
  (local (defwarrant g-2))
  (make-event (prog2$ (foo-2 'g-2 *list-3*) ; (3 . 4)
                      '(value-triple t))))

(defun$ g-2 (x) (declare (xargs :guard t)) (cons x 5))

(assert! (equal (foo-2 'g-2 *list-3*)
; See the comment near the top of this file.
                '(3 . 5)))

; Here is the analogous example using badge-userfn.

(defun foo-3 (fn)
  (declare (xargs :guard (symbolp fn)))
  (badge-userfn fn))

(memoize 'foo-3 :aokp t) ; problem goes away without :aokp t

(encapsulate
  ()
  (local (defun g-3 (x)
           (declare (xargs :guard t))
           (cons x 4)))
  (local (defwarrant g-3))
  (make-event (prog2$ (foo-3 'g-3) ; (APPLY$-BADGE 1 1 . T)
                      '(value-triple t))))

(defun$ g-3 (x y)
  (declare (xargs :guard t))
  (cons x y))

(assert! (equal (foo-3 'g-3)
; See the comment near the top of this file.
                '(APPLY$-BADGE 2 1 . T)))

; Here is the analogous example using badge.

(defun foo-4 (fn)
  (declare (xargs :guard (symbolp fn)))
  (badge fn))

(memoize 'foo-4 :aokp t) ; problem goes away without :aokp t

(encapsulate
  ()
  (local (defun g-4 (x)
           (declare (xargs :guard t))
           (cons x 4)))
  (local (defwarrant g-4))
  (make-event (prog2$ (foo-4 'g-4) ; (APPLY$-BADGE 1 1 . T)
                      '(value-triple t))))

(defun$ g-4 (x y)
  (declare (xargs :guard t))
  (cons x y))

(assert! (equal (foo-4 'g-4)
; See the comment near the top of this file.
                '(APPLY$-BADGE 2 1 . T)))

; The examples above formerly broke and now work.  Here is a related example
; that uses doppelganger-apply$-userfn, which has been fixed simply by making
; doppelganger-apply$-userfn untouchable (similarly, doppelganger-badge-userfn
; is also now untouchable).

#||
(include-book "projects/apply/top" :dir :system) ; apply-lemmas in v8-1
(defun foo (fn args)
  (declare (xargs :guard (true-listp args)))
  (doppelganger-apply$-userfn fn args))
(memoize 'foo)
(defconst *list-3* (list 3))
(defun$ g (x) (declare (xargs :guard t)) (cons x 4))
(foo 'g *list-3*) ; (3 . 4)
(u)
(defun$ g (x) (declare (xargs :guard t)) (cons x 5))
(foo 'g *list-3*) ; still (3 . 4), but should be (3 . 5)!
||#
