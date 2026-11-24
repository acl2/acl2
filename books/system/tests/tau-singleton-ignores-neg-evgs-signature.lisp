; This book, modified only as noted below by Matt Kaufmann, was produced by
; Claude and passed along by Eric Smith.  It illustrates a soundness bug fixed
; before ACL2 Version 8.8.

; S-276 (route: a vacuous :type-prescription rule becomes the false tau signature rule (integerp (f 0))).
; Expected: proves nil (prints NIL-PROVED); no trust tags; certifies; SBCL and CCL.
;
; G165 candidate (soundness), signature-rule route of
; G165-tau-singleton-ignores-neg-evgs.lisp (see there for the defect).
;
; The hypotheses of the vacuous :type-prescription rule F-TYPE are added to
; its hypothesis tau last first: x <= 0 and 0 <= x give the NIL-domain
; interval [0,0], x /= 0 is kept in :neg-evgs (0 is not strengthened away in
; the NIL domain), and (acl2-numberp x) then makes the domain ACL2-NUMBERP with
; both bounds unchanged, so tighten-bound's singleton case turns the tau into
; "x = 0" without looking at :neg-evgs.  Tau (default automatic mode) thus
; stores the signature rule (integerp (f 0)), which is false.
;
; Control: with (acl2-numberp x) listed last (added first), the contradiction
; is detected, no signature rule is stored, and LEMMA fails.
(in-package "ACL2")

(defun f (x) (if (equal x 0) 'a 0))

(defthm f-type
  (implies (and (acl2-numberp x)
                (not (equal x 0))
                (<= 0 x)
                (<= x 0))
           (integerp (f x)))
  :rule-classes :type-prescription)

(in-theory (disable f (:e f)))

; Added by Matt K.:
(include-book "std/testing/must-fail" :dir :system)

(must-fail ; This must-fail wrapper was added by Matt K.
(defthm lemma
  (integerp (f 0))
  :rule-classes nil)
)

; The following were commented out by Matt K. since the event just above now
; fails.
#|
(defthm nil-proved nil
  :hints (("Goal" :use lemma
                  :in-theory (enable (:e f))))
  :rule-classes nil)

(value-triple (cw "~%NIL-PROVED~%"))
|#
