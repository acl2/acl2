; Copyright (C) 2026, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This book is based on feedback from Claude that was passed along by Eric
; Smith, as explained below.

(in-package "ACL2")

(defun e1 (x y) (declare (xargs :guard t)) (equal (nfix x) (nfix y)))
(defequiv e1)

; As noted by Claude, the following sort of duplication of :equivalence rules
; was rejected in ACL2 Version 8.7, even though the include-book events below
; were accepted (see below for further explanation).

(defthm e1-is-an-equivalence-again
  (and (booleanp (e1 x y)) (e1 x x)
       (implies (e1 x y) (e1 y x))
       (implies (and (e1 x y) (e1 y z)) (e1 x z)))
  :rule-classes :equivalence)

; The following, which is essentially Claude's original example, is as above
; but with e1 replaced by ee and with books included.  The second include-book
; below succeeded with a new equivalence rule for the same equivalence
; relation, as above, even though that had been prohibited for the events
; above.  Thus, include-book was being too generous.  We have since fixed the
; handling of duplicate equivalence relations so that such duplication of
; equivalence rules is permitted but ignored, with an Observation printed to
; that effect.

(include-book "eqdup/eq1")
(include-book "eqdup/eq2")
