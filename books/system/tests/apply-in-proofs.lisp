; Copyright (C) 2019, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This book tests execution of apply$ and loop$ during proofs.  Until March,
; 2019 it was impossible during rewriting to execute any call of apply$ or
; badge on a user-defined function, because attachments are disallowed during
; rewriting.  The implementation introduced the function ev-fncall+ and its use
; to support the use of warrants during rewriting; see :doc note-8-2.

(in-package "ACL2")

(include-book "projects/apply/top" :dir :system)

(include-book "misc/eval" :dir :system)

; Avoid distracting warnings produced by :hints in this file that insist on
; using executing for the proof.
(set-inhibit-warnings "Theory" "Disable")

(defun$ f1 (x) (cons x x))

(defun g1 (fn x)
  (declare (xargs :guard ; based on apply$-guard
                  (or (symbolp fn)
                      (and (consp fn)
                           (consp (cdr fn))
                           (equal (len (cadr fn)) 1)))
; Test first that this all works without guard verification.
                  :verify-guards nil))
  (apply$ fn (list x)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Basic tests of apply$ing f1, some indirectly via g1.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The following uses apply$-f1 to rewrite the apply$ call to (f1 3), and then
; uses (:e f1) to evaluate that call.
(thm (implies (warrant f1)
              (equal (apply$ 'f1 '(3))
                     '(3 . 3)))
     :hints (("Goal" :in-theory '((:e f1) apply$-f1))))

; The following uses (:e g) to rewrite the call of g1, and requires apply$-f1
; to justify the subsidiary evaluation of (apply$ 'f1 '(3)).
(thm (implies (warrant f1)
              (equal (g1 'f1 3)
                     '(3 . 3)))
     :hints (("Goal" :in-theory '((:e g1) apply$-f1))))

(must-fail
 (thm (implies (warrant f1)
               (equal (apply$ 'f1 '(3))
                      '(3 . 3)))
      :hints (("Goal" :in-theory '((:e f1)))))
 )

(must-fail
 (thm (implies (warrant f1)
               (equal (g 'f1 3)
                      '(3 . 3)))
      :hints (("Goal" :in-theory '((:e g1)))))
 )

(defun warrant-f1-wrapper ()
  (warrant f1))

(in-theory (disable warrant-f1-wrapper (:e warrant-f1-wrapper)))

(thm (implies (warrant-f1-wrapper)
              (equal (apply$ 'f1 '(3))
                     '(3 . 3)))
     :hints (("Goal" :in-theory '((:e f1) apply$-f1 (:e force)))
             ("[1]Goal" :in-theory (enable warrant-f1-wrapper))))

(thm (implies (warrant-f1-wrapper)
              (equal (g1 'f1 3)
                     '(3 . 3)))
     :hints (("Goal" :in-theory '((:e g1) apply$-f1 (:e force)))
             ("[1]Goal" :in-theory (enable warrant-f1-wrapper))))

(thm (implies (warrant-f1-wrapper)
              (equal (apply$ 'f1 '(3))
                     '(3 . 3)))
     :hints (("Goal" :in-theory '((:e f1) apply$-f1 (:e force)))
             ("[1]Goal" :in-theory '(warrant-f1-wrapper))))

(thm (implies (warrant-f1-wrapper)
              (equal (g1 'f1 3)
                     '(3 . 3)))
     :hints (("Goal" :in-theory '((:e g1) apply$-f1 (:e force)))
             ("[1]Goal" :in-theory '(warrant-f1-wrapper))))

(must-fail ; Apply$-f must be enabled at the time we need it.
 (thm (implies (warrant-f1-wrapper)
               (equal (apply$ 'f1 '(3))
                      '(3 . 3)))
      :hints (("Goal" :in-theory '((:e f1) (:e force)))
              ("[1]Goal" :in-theory (enable apply$-f1 warrant-f1-wrapper))))
 )

(must-fail ; Apply$-f must be enabled at the time we need it.
 (thm (implies (warrant-f1-wrapper)
               (equal (g1 'f1 3)
                      '(3 . 3)))
      :hints (("Goal" :in-theory '((:e g1) (:e force)))
              ("[1]Goal" :in-theory (enable apply$-f1 warrant-f1-wrapper))))
 )

(must-fail ; Forcing must be enabled at the time we need it.
 (thm (implies (warrant-f1-wrapper)
               (equal (apply$ 'f1 '(3))
                      '(3 . 3)))
      :hints (("Goal" :in-theory '((:e f1) apply$-f1))
              ("[1]Goal" :in-theory (enable (:e force) warrant-f1-wrapper))))
 )

(must-fail ; Forcing must be enabled at the time we need it.
 (thm (implies (warrant-f1-wrapper)
               (equal (g1 'f1 3)
                      '(3 . 3)))
      :hints (("Goal" :in-theory '((:e g1) apply$-f1))
              ("[1]Goal" :in-theory (enable (:e force) warrant-f1-wrapper))))
 )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; The events above still go through with guard-verified f1 and g1.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(verify-guards f1)
(verify-guards g1)

(thm (implies (warrant f1)
              (equal (apply$ 'f1 '(3))
                     '(3 . 3)))
     :hints (("Goal" :in-theory '((:e f1) apply$-f1))))

(thm (implies (warrant f1)
              (equal (g1 'f1 3)
                     '(3 . 3)))
     :hints (("Goal" :in-theory '((:e g1) apply$-f1))))

(must-fail
 (thm (implies (warrant f1)
               (equal (apply$ 'f1 '(3))
                      '(3 . 3)))
      :hints (("Goal" :in-theory '((:e f1)))))
 )

(must-fail
 (thm (implies (warrant f1)
               (equal (g 'f1 3)
                      '(3 . 3)))
      :hints (("Goal" :in-theory '((:e g1)))))
 )

(thm (implies (warrant-f1-wrapper)
              (equal (apply$ 'f1 '(3))
                     '(3 . 3)))
     :hints (("Goal" :in-theory '((:e f1) apply$-f1 (:e force)))
             ("[1]Goal" :in-theory (enable warrant-f1-wrapper))))

(thm (implies (warrant-f1-wrapper)
              (equal (g1 'f1 3)
                     '(3 . 3)))
     :hints (("Goal" :in-theory '((:e g1) apply$-f1 (:e force)))
             ("[1]Goal" :in-theory (enable warrant-f1-wrapper))))

(thm (implies (warrant-f1-wrapper)
              (equal (apply$ 'f1 '(3))
                     '(3 . 3)))
     :hints (("Goal" :in-theory '((:e f1) apply$-f1 (:e force)))
             ("[1]Goal" :in-theory '(warrant-f1-wrapper))))

(thm (implies (warrant-f1-wrapper)
              (equal (g1 'f1 3)
                     '(3 . 3)))
     :hints (("Goal" :in-theory '((:e g1) apply$-f1 (:e force)))
             ("[1]Goal" :in-theory '(warrant-f1-wrapper))))

(must-fail ; Apply$-f must be enabled at the time we need it.
 (thm (implies (warrant-f1-wrapper)
               (equal (apply$ 'f1 '(3))
                      '(3 . 3)))
      :hints (("Goal" :in-theory '((:e f1) (:e force)))
              ("[1]Goal" :in-theory (enable apply$-f1 warrant-f1-wrapper))))
 )

(must-fail ; Apply$-f must be enabled at the time we need it.
 (thm (implies (warrant-f1-wrapper)
               (equal (g1 'f1 3)
                      '(3 . 3)))
      :hints (("Goal" :in-theory '((:e g1) (:e force)))
              ("[1]Goal" :in-theory (enable apply$-f1 warrant-f1-wrapper))))
 )

(must-fail ; Forcing must be enabled at the time we need it.
 (thm (implies (warrant-f1-wrapper)
               (equal (apply$ 'f1 '(3))
                      '(3 . 3)))
      :hints (("Goal" :in-theory '((:e f1) apply$-f1))
              ("[1]Goal" :in-theory (enable (:e force) warrant-f1-wrapper))))
 )

(must-fail ; Forcing must be enabled at the time we need it.
 (thm (implies (warrant-f1-wrapper)
               (equal (g1 'f1 3)
                      '(3 . 3)))
      :hints (("Goal" :in-theory '((:e g1) apply$-f1))
              ("[1]Goal" :in-theory (enable (:e force) warrant-f1-wrapper))))
 )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Basic tests involving lambdas
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(thm (implies (warrant f1)
              (equal (g1 '(lambda (x) (f1 x)) 3)
                     '(3 . 3)))
     :hints (("Goal" :in-theory '((:e g1) apply$-f1))))

(thm (implies (warrant-f1-wrapper)
              (equal (g1 '(lambda (x) (f1 x)) 3)
                     '(3 . 3)))
     :hints (("Goal" :in-theory '((:e g1) apply$-f1 (:e force)))
             ("[1]Goal" :in-theory (enable warrant-f1-wrapper))))

(thm (implies (warrant-f1-wrapper)
              (equal (g1 '(lambda (x) (f1 x)) 3)
                     '(3 . 3)))
     :hints (("Goal" :in-theory '((:e g1) apply$-f1 (:e force)))
             ("[1]Goal" :in-theory '(warrant-f1-wrapper))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Basic tests involving lambda$
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; But we can't use lambda$ until there is a warrant for g1.
(must-fail
 (thm (implies (warrant f1)
               (equal (g1 (lambda$ (x) (f1 x)) 3)
                      '(3 . 3)))
      :hints (("Goal" :in-theory '((:e g1) apply$-f1)))))

(defwarrant g1)

; same as before:
(thm (implies (warrant f1)
              (equal (g1 '(lambda (x) (f1 x)) 3)
                     '(3 . 3)))
     :hints (("Goal" :in-theory '((:e g1) apply$-f1))))

; now lambda$ is OK:
(thm (implies (warrant f1)
              (equal (g1 (lambda$ (x) (f1 x)) 3)
                     '(3 . 3)))
     :hints (("Goal" :in-theory '((:e g1) apply$-f1))))

(thm (implies (warrant-f1-wrapper)
              (equal (g1 (lambda$ (x) (f1 x)) 3)
                     '(3 . 3)))
     :hints (("Goal" :in-theory '((:e g1) apply$-f1 (:e force)))
             ("[1]Goal" :in-theory (enable warrant-f1-wrapper))))

(thm (implies (warrant-f1-wrapper)
              (equal (g1 (lambda$ (x) (f1 x)) 3)
                     '(3 . 3)))
     :hints (("Goal" :in-theory '((:e g1) apply$-f1 (:e force)))
             ("[1]Goal" :in-theory '(warrant-f1-wrapper))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Basic tests involving loop$, not guard-verified
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun f2 (x)
  (declare (xargs :guard (true-listp x)
                  :verify-guards nil))
  (loop$ for a in x collect (g1 'f1 a)))

(thm (implies (warrant f1 g1)
              (equal (f2 '(a b c))
                     '((a . a) (b . b) (c . c))))
     :hints (("Goal" :in-theory '((:e f2)
                                  apply$-f1 apply$-g1))))

(defwarrant f2)

(thm (implies (warrant f1 f2 g1)
              (equal (apply$ 'f2 '((a b c)))
                     '((a . a) (b . b) (c . c))))
     :hints (("Goal" :in-theory '((:e f2)
                                  apply$-f1 apply$-f2 apply$-g1))))

; The test above appropriately fails without all three warrants.

(must-fail
 (thm (implies (warrant f2 g1) ; omit f1
               (equal (apply$ 'f2 '((a b c)))
                      '((a . a) (b . b) (c . c))))
      :hints (("Goal" :in-theory '((:e f2)
                                   apply$-f1 apply$-f2 apply$-g1)))))

(must-fail
 (thm (implies (warrant f1 g1) ; omit f2
               (equal (apply$ 'f2 '((a b c)))
                      '((a . a) (b . b) (c . c))))
      :hints (("Goal" :in-theory '((:e f2)
                                   apply$-f1 apply$-f2 apply$-g1)))))

(must-fail
 (thm (implies (warrant f1 f2) ; omit g1
               (equal (apply$ 'f2 '((a b c)))
                      '((a . a) (b . b) (c . c))))
      :hints (("Goal" :in-theory '((:e f2)
                                   apply$-f1 apply$-f2 apply$-g1)))))

; The test above appropriately fails without all three apply$-xx rules.

(must-fail
 (thm (implies (warrant f1 f2 g1)
               (equal (apply$ 'f2 '((a b c)))
                      '((a . a) (b . b) (c . c))))
      :hints (("Goal" :in-theory '((:e f2)
                                   apply$-f2 apply$-g1)))))

(must-fail
 (thm (implies (warrant f1 f2 g1)
               (equal (apply$ 'f2 '((a b c)))
                      '((a . a) (b . b) (c . c))))
      :hints (("Goal" :in-theory '((:e f2)
                                   apply$-f1 apply$-g1)))))

(must-fail
 (thm (implies (warrant f1 f2 g1)
               (equal (apply$ 'f2 '((a b c)))
                      '((a . a) (b . b) (c . c))))
      :hints (("Goal" :in-theory '((:e f2)
                                   apply$-f1 apply$-f2)))))

; Here is a test of direct evaluation of loop$ in a theorem (as opposed to
; calling a function that leads to a call of loop$).  We enable the
; executable-counterpart of collect$ because the loop$ call translates to a
; collect$ call.
(thm (implies (warrant f1 g1)
              (equal (loop$ for a in '(a b c) collect (g1 'f1 a))
                     '((a . a) (b . b) (c . c))))
     :hints (("Goal" :in-theory '((:e f2)
                                  (:e collect$)
                                  apply$-f1 apply$-g1))))

(must-fail
 (thm (implies (warrant f1 g1)
               (equal (loop$ for a in '(a b c) collect (g1 'f1 a))
                      '((a . a) (b . b) (c . c))))
      :hints (("Goal" :in-theory '((:e f2)
                                   ;; (:e collect$)
                                   apply$-f1 apply$-g1)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Basic tests involving loop$, guard-verified
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; These are exactly as above, except we verify guards for f2.

(verify-guards f2)

(thm (implies (warrant f1 g1)
              (equal (f2 '(a b c))
                     '((a . a) (b . b) (c . c))))
     :hints (("Goal" :in-theory '((:e f2)
                                  apply$-f1 apply$-g1))))

(thm (implies (warrant f1 f2 g1)
              (equal (apply$ 'f2 '((a b c)))
                     '((a . a) (b . b) (c . c))))
     :hints (("Goal" :in-theory '((:e f2)
                                  apply$-f1 apply$-f2 apply$-g1))))

; The test above appropriately fails without all three warrants.

(must-fail
 (thm (implies (warrant f2 g1) ; omit f1
               (equal (apply$ 'f2 '((a b c)))
                      '((a . a) (b . b) (c . c))))
      :hints (("Goal" :in-theory '((:e f2)
                                   apply$-f1 apply$-f2 apply$-g1)))))

(must-fail
 (thm (implies (warrant f1 g1) ; omit f2
               (equal (apply$ 'f2 '((a b c)))
                      '((a . a) (b . b) (c . c))))
      :hints (("Goal" :in-theory '((:e f2)
                                   apply$-f1 apply$-f2 apply$-g1)))))

(must-fail
 (thm (implies (warrant f1 g1) ; omit f3
               (equal (apply$ 'f2 '((a b c)))
                      '((a . a) (b . b) (c . c))))
      :hints (("Goal" :in-theory '((:e f2)
                                   apply$-f1 apply$-f2 apply$-g1)))))

; The test above appropriately fails without all three apply$-xx rules.

(must-fail
 (thm (implies (warrant f1 f2 g1)
               (equal (apply$ 'f2 '((a b c)))
                      '((a . a) (b . b) (c . c))))
      :hints (("Goal" :in-theory '((:e f2)
                                   apply$-f2 apply$-g1)))))

(must-fail
 (thm (implies (warrant f1 f2 g1)
               (equal (apply$ 'f2 '((a b c)))
                      '((a . a) (b . b) (c . c))))
      :hints (("Goal" :in-theory '((:e f2)
                                   apply$-f1 apply$-g1)))))

(must-fail
 (thm (implies (warrant f1 f2 g1)
               (equal (apply$ 'f2 '((a b c)))
                      '((a . a) (b . b) (c . c))))
      :hints (("Goal" :in-theory '((:e f2)
                                   apply$-f1 apply$-f2)))))

; Here is a test of direct evaluation of loop$ in a theorem (as opposed to
; calling a function that leads to a call of loop$).  We enable the
; executable-counterpart of collect$ because the loop$ call translates to a
; collect$ call.
(thm (implies (warrant f1 g1)
              (equal (loop$ for a in '(a b c) collect (g1 'f1 a))
                     '((a . a) (b . b) (c . c))))
     :hints (("Goal" :in-theory '((:e f2)
                                  (:e collect$)
                                  apply$-f1 apply$-g1))))

(must-fail
 (thm (implies (warrant f1 g1)
               (equal (loop$ for a in '(a b c) collect (g1 'f1 a))
                      '((a . a) (b . b) (c . c))))
      :hints (("Goal" :in-theory '((:e f2)
                                   ;; (:e collect$)
                                   apply$-f1 apply$-g1)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Test for early exit from eval when warrant isn't available
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun$ my-natp (x)
  (declare (xargs :guard t))
  (natp x))

(defun$ f3 (n)
  (declare (xargs :guard (natp n)))
  (if (zp n)
      t
    (and (apply$ 'my-natp (list n))
         (f3 (1- n)))))

; Without the :hints, it has taken more than 3 seconds in CCL to fail with siz
; fewer zeros.  And if you evaluate (trace$ apply$-userfn) you'll see only six
; calls in the attempt below; if instead you evaluate (trace$ (apply$-userfn
; :entry (break$))), then you'll see that you're under expand-abbreviations --
; so its call of ev-fncall+ is exiting early, as it should.
(must-fail
 (thm (equal (f3 10000000000000) t)
      :hints (("Goal" :do-not '(simplify)))))

; Note: At one time I tried the following test instead, but it was too slow
; because a big list was being built for always$.
#||
(defun f3 (n)
  (declare (xargs :guard (natp n)))
  (loop$ for i from 1 to n always (my-natp i)))
(thm (equal (f3 1000000000000) t)
     :hints (("Goal" :do-not '(simplify))))
||#

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Test for handling ill-guarded loops
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun f4 (x)
  (declare (xargs :guard (true-listp x)))
  (loop$ for a in x collect (cons x x)))

(thm (equal (f4 'a) nil))

(defun$ my-car (x)
  (declare (xargs :guard (consp x)))
  (car x))

(defun f5 (x)
  (declare (xargs :guard (and (true-listp x)
                              (equal (len x) 1)
                              (consp (car x)))))
  (apply$ (lambda$ (x) (declare (xargs :guard (consp x))) (my-car x)) x))


