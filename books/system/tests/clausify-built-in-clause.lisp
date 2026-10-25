; Copyright (C) 2026, Regents of the University of Texas
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This book tests the fix for a soundness bug in clausify (specifically,
; functions if-interp-assumed-value and arg1-almost-subsumes-arg2 in
; rewrite.lisp) when combined with :built-in-clause rules.

; Prior to the fix:
; 1. if-interp-assumed-value stripped only a single NOT call (calling
;    if-interp-assumed-value-x on the argument) whereas if-interp-assume-true
;    stripped nested NOT calls recursively.  Consequently, testing (not (not b))
;    under an assumption on b produced the tautology clause (B (NOT B)) from
;    strip-branches.
; 2. arg1-almost-subsumes-arg2 allowed a tautology clause such as (B (NOT B)) or
;    ((NOT B) B) to resolve with ((NOT B) A) and replace it with (A) in
;    subsumption-replacement-loop.
; 3. Installing a theorem of the form
;      (if (not (car nil)) (if (not (not (car nil))) nil t) a)
;    as a :built-in-clause rule therefore installed the unit clause (A), which
;    subsumed every clause and allowed proving nil.

(in-package "ACL2")

(include-book "std/testing/must-fail" :dir :system)
(include-book "std/testing/must-succeed" :dir :system)

; 1. Verify that strip-branches recognizes (not (not b)) is false when (not b)
; is assumed true, rather than emitting the tautology clause (B (NOT B)).
(assert-event
 (equal (strip-branches '(if (not b) (if (not (not b)) 'nil 't) a) nil t)
        '(((not b) a))))

(assert-event
 (equal (clausify '(if (not b) (if (not (not b)) 'nil 't) a) nil t 500)
        '(((not b) a))))

; 2. Verify that arg1-almost-subsumes-arg2 and subsumption-replacement-loop do
; not use a tautology clause to drop a complementary literal from another
; clause.
(assert-event
 (equal (arg1-almost-subsumes-arg2 '(b (not b)) '((not b) a))
        nil))

(assert-event
 (equal (arg1-almost-subsumes-arg2 '((not b) b) '((not b) a))
        nil))

(assert-event
 (equal (subsumption-replacement-loop
         (merge-sort-length '((b (not b)) ((not b) a)))
         nil nil)
        '(((not b) a) (b (not b)))))

(assert-event
 (equal (subsumption-replacement-loop
         (merge-sort-length '(((not b) b) ((not b) a)))
         nil nil)
        '(((not b) a) ((not b) b))))

; 3. Verify that valid replacement resolution still succeeds when arg1 is not
; tautological on the resolved literal.
(assert-event
 (equal (arg1-almost-subsumes-arg2 '(b a) '((not b) a))
        '(b a)))

(assert-event
 (equal (subsumption-replacement-loop
         (merge-sort-length '((b a) ((not b) a)))
         nil nil)
        '((a))))

; 4. Verify that the formerly successful proof of nil via :built-in-clause now
; fails.
(defthm built-in-anything-attempt
  (if (not (car nil))
      (if (not (not (car nil))) nil t)
    a)
  :rule-classes :built-in-clause)

(must-fail
 (defthm nil-is-true
   nil
   :rule-classes nil))
