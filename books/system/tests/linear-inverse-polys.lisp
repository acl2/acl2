; Regression tests for soundness fix to inverse-polys
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; These tests were created by the AI, with the goal of testing 4 related
;; changes to inverse-polys (referred to as "change1" through "change4" below)
;; that are present in ACL2 Version 8.8.  All of these proofs went through
;; before the changes.  After the changes, none of them go through.  (Note: I
;; have not reviewed the comments below.)

(include-book "std/testing/must-fail" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-fail
 (defthm bad-change1
   (implies (and (rationalp x)
                 (<= 1 (expt x 3)) ; inv-var-lbd = 1 > 0 : enters branch B
                 (<= -3 (expt x -3))) ; var-lbd = -3 < 0 : misused by bounds-polys3
            nil)
   :rule-classes nil
   :hints (("Goal" :nonlinearp t))))

; The hypotheses are satisfiable (x = 1: 1 <= 1^3 and -3 <= 1/1^3), so
; bad-change1 is not a theorem; it is admitted only via the unsound inversion.
(must-fail
 (defthm contradiction-change1
   nil
   :rule-classes nil
   :hints (("Goal" :use ((:instance bad-change1 (x 1)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-fail
 (defthm bad-change2
   (implies (and (rationalp x)
                 (<= 1 (/ x)) ; var-lbd = 1 > 0 : enters branch B
                 (<= -3 x))   ; inv-var-lbd = -3 < 0 : misused by bounds-polys4
            nil)
   :rule-classes nil
   :hints (("Goal" :nonlinearp t))))

; The hypotheses are satisfiable (x = 1: 1 <= 1/1 and -3 <= 1), so bad-change2
; is not a theorem; it is admitted only via the unsound inversion.
(must-fail
 (defthm contradiction-change2
   nil
   :rule-classes nil
   :hints (("Goal" :use ((:instance bad-change2 (x 1)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-fail
 (defthm bad-change3
   (implies (and (rationalp x)
                 (<= (expt x 3) -1) ; inv-var-ubd = -1 < 0 : enters branch C
                 (<= (expt x -3) 3)) ; var-ubd = 3 > 0 : misused by bounds-polys3
            nil)
   :rule-classes nil
   :hints (("Goal" :nonlinearp t))))

; The hypotheses are satisfiable (x = -1: (-1)^3 = -1 <= -1 and 1/(-1)^3 = -1 <= 3),
; so bad-change3 is not a theorem; it is admitted only via the unsound inversion.
(must-fail
 (defthm contradiction-change3
   nil
   :rule-classes nil
   :hints (("Goal" :use ((:instance bad-change3 (x -1)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-fail
 (defthm bad-change4
   (implies (and (rationalp x)
                 (<= (/ x) -1) ; inv-var-ubd path: var-ubd = -1 < 0 : enters branch C
                 (<= x 5))     ; inv-var-ubd = 5 > 0 : misused by bounds-polys4
            nil)
   :rule-classes nil
   :hints (("Goal" :nonlinearp t))))

; The hypotheses are satisfiable (x = -1: 1/-1 = -1 <= -1 and -1 <= 5), so
; bad-change4 is not a theorem; it is admitted only via the unsound inversion.
(must-fail
 (defthm contradiction-change4
   nil
   :rule-classes nil
   :hints (("Goal" :use ((:instance bad-change4 (x -1)))))))
