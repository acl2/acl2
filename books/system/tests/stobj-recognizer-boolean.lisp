; This book was produced by Claude and passed along by Eric Smith.  It
; illustrates a soundness bug in ACL2 Version 8.7 fixed before ACL2 Version
; 8.8.

; Finding 63: the RAW top-level stobj recognizer omits the final T that the
; AXIOMATIC one has, and the comment above the axiomatic one explains why it is
; there and names the consumer that relies on it.
;
; defstobj-component-recognizer-axiomatic-defs (basis-a.lisp:9336-9340) ends the
; conjunction with t, under this comment:
;
;   "Note: The recognizer for a stobj must be Boolean! ... The individual field
;    recognizers need not be Boolean and sometimes are not!  For example, a field
;    with :TYPE (MEMBER e1 ... ek) won't be Boolean ... The reason we want the
;    stobj recognizer to be Boolean is so that we can replace it by T in guard
;    conjectures for functions that have been translated with the stobj
;    syntactic restrictions.  See optimize-stobj-recognizers."
;
; defstobj-raw-defs (basis-a.lisp:9441-9449) replaces that definition and drops
; the final t:
;
;   `((,recog (,name)
;             (cond ((live-stobjp ,name) t)
;                   (t (and (true-listp ,name)
;                           (= (length ,name) ,(length field-templates))
;                           ,@(defstobj-component-recognizer-calls ...)))))
;
; <name>p accepts a non-live argument (its stobjs-in (name) means the stobj MAY
; be supplied) and its guard is T, so the raw definition is reached on ordinary
; data -- while ACL2 stores a :TYPE-PRESCRIPTION saying <name>p is Boolean, and
; optimize-stobj-recognizers (basis-b.lisp:2541) replaces the call by T in guard
; conjectures.
;
; Measured: (f1p 3) = (3 4), (stp (list 3)) = (3 4),
; (equal (stp (list 3)) t) = NIL.
;
; Only the LAST conjunct's Booleanness matters, since (and A B) returns B.
; Measured non-Boolean for a last field of type (member 3 4),
; (or (member 3 4) null), (and integer (member 3 4)), (member #\a #\b) and
; (satisfies <non-Boolean>); Boolean for (integer 0 10) and symbol.
;
; defabsstobj does NOT have this bug (defabsstobj-raw-defs emits
; (cond ((live-stobjp y) t) (t (,logic y))) with logic the real recognizer), and
; neither do the raw FIELD recognizers (defstobj-raw-defs reuses the axiomatic
; ones verbatim).
;
; POLARITY: the MUST-FAIL states the CORRECT behaviour -- the recognizer is
; Boolean in the logic.  RED while present.
(in-package "ACL2")
(include-book "std/testing/must-fail" :dir :system)

(defstobj st (f1 :type (member 3 4) :initially 3))

; The logic says the recognizer is Boolean.  Must stay provable.
(defthm logic-says-t
  (equal (stp (list 3)) t)
  :hints (("Goal" :in-theory (disable (:executable-counterpart stp))))
  :rule-classes nil)

; THE DEFECT: raw evaluation returns the field recognizer's value, (3 4).
(must-fail
 (defthm raw-says-not-t (not (equal (stp (list 3)) t)) :rule-classes nil))

; CONTROL 1: a Boolean last field -- raw agrees with the logic.
(defstobj st2 (g1 :type integer :initially 3))
(defthm control-integer-agrees (equal (st2p (list 3)) t) :rule-classes nil)

; CONTROL 2: the same (member 3 4) field with a trailing Boolean field, so the
; LAST conjunct is Boolean.  This pins the defect to the final conjunct rather
; than to the presence of a member field.
(defstobj st3 (h1 :type (member 3 4) :initially 3) (h2 :type integer :initially 0))
(defthm control-lastfield-agrees (equal (st3p (list 3 0)) t) :rule-classes nil)
