; This book, modified only as noted below, was produced by Claude and passed
; along by Eric Smith.  It illustrates a soundness bug fixed before ACL2
; Version 8.8.

; PROOF OF NIL.  Finding 14 residue: the :TYPE-SET-INVERTER acceptability check
; is still skipped in encapsulate pass 2 / at include-book, while
; add-type-set-inverter-rule installs a re-derived :ts without re-running the
; tautologyp gate that ties :ts to :terms.
;
; No ttag, no skip-proofs, no defaxiom, no include-book.
(in-package "ACL2")

(defun my-num (x) (integerp x))
(defun my-num2 (x) (my-num x))

; Step 1 (fully checked, non-local): make (MY-NUM X) the canonical term that
; convert-type-set-to-term produces for *ts-integer*.
(defthm my-num-tsi
  (equal (my-num x) (integerp x))
  :rule-classes ((:type-set-inverter)))

; Step 2 (non-local): a WEAK compound recognizer.  (MY-NUM X) => acl2-numberp.
(defthm my-num-cr-weak
  (implies (my-num x) (acl2-numberp x))
  :rule-classes :compound-recognizer)

; Added by Matt Kaufmann:
(include-book "std/testing/must-fail" :dir :system)

(must-fail ; The must-fail wrapper was added by Matt Kaufmann:
; Step 3: the attack.  chk-acceptable-type-set-inverter-rule runs in pass 1
; only.  There, the LOCAL strong compound recognizer makes
;   (type-set-implied-by-term 'X nil '(my-num x)) = *ts-integer* = 23,
; and the tautologyp gate
;   (iff (my-num x) (convert-type-set-to-term 'X 23 ...)) = (iff (my-num x) (my-num x))
; holds.  In pass 2 the local rule is gone, add-type-set-inverter-rule
; RE-DERIVES ts = *ts-acl2-number* = 127 from the weak recognizer, and installs
;   :ts 127  :terms ((MY-NUM2 X))
; without re-checking the gate.  ACL2 now believes
;   "x has type-set *ts-acl2-number*  <=>  (MY-NUM2 X)",
; i.e. "acl2-numberp <=> integerp".
(encapsulate
  ()
  (local (defthm my-num-cr-strong
           (implies (my-num x) (integerp x))
           :rule-classes :compound-recognizer))
  (defthm evil-tsi
    (equal (my-num2 x) (my-num x))
    :rule-classes ((:type-set-inverter))))
)

; F returns an acl2-number; its :basic-ts is exactly 127.  tau-visit turns the
; type-prescription into a tau rule via convert-type-prescription-to-term, which
; now emits (MY-NUM2 (F X)) -- i.e. (INTEGERP (F X)).
(defun f (x) (if (acl2-numberp x) x 0))

(must-fail ; The must-fail wrapper was added by Matt Kaufmann:
(defthm bad
  (integerp (f x))
  :rule-classes nil)
)

(must-fail ; The must-fail wrapper was added by Matt Kaufmann:
(defthm nil-proved
  nil
  :rule-classes nil
  :hints (("Goal" :use (:instance bad (x 1/2)))))
)
