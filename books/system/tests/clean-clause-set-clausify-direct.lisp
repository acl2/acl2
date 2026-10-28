; This book, modified only as noted below by Matt Kaufmann, was produced by
; Claude and passed along by Eric Smith.  It illustrates a soundness bug fixed
; before ACL2 Version 8.8.  See clean-clause-set-by-hint.lisp for an
; explanation.

(in-package "ACL2") ; Added by Matt K. to make a certifiable book

; Added by Matt K.:
(include-book "std/testing/must-fail" :dir :system)

; ISSUE B2.  Example B2-b: direct observation; the second clause must keep (NOT A).
; EXPECT-AFTER-FIX: every clause returned is valid; in particular no clause equal to (B (CAR (CONS A C))).

; Non-event commented out by Matt K.:
#|
(clausify '(if (if a (not (not a)) 't) (if b 't (if a (car (cons a c)) 't)) 'nil) nil t nil)
|#

(assert-event (not (member-equal '(b (car (cons a c)))
                                 (clausify '(if (if a (not (not a)) 't) (if b 't (if a (car (cons a c)) 't)) 'nil) nil t nil))))
