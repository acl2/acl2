; Rules about the ARM model
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ARM")

(include-book "pseudocode")

(defthm conditionpassed-of-set-reg
  (equal (conditionpassed cond (set-reg n val arm))
         (conditionpassed cond arm))
  :hints (("Goal" :in-theory (enable conditionpassed))))

(defthm conditionpassed-of-write
  (equal (conditionpassed cond (write n addr val arm))
         (conditionpassed cond arm))
  :hints (("Goal" :in-theory (enable conditionpassed))))

;; Here we recharacterize conditionpassed.  This scheme can result in fewer
;; branches during symbolic execution compared to just opening everything up
;; (consider the complex conditions like gt-condition).

(defund eq-condition (z) (declare (xargs :guard (bitp z))) (== z 1))
(defund ne-condition (z) (declare (xargs :guard (bitp z))) (not (== z 1))) ; or do (== z 0)

(defund cs-condition (c) (declare (xargs :guard (bitp c))) (== c 1))
(defund cc-condition (c) (declare (xargs :guard (bitp c))) (== c 0))

(defund mi-condition (n) (declare (xargs :guard (bitp n))) (== n 1))
(defund pl-condition (n) (declare (xargs :guard (bitp n))) (== n 0))

(defund vs-condition (v) (declare (xargs :guard (bitp v))) (== v 1))
(defund vc-condition (v) (declare (xargs :guard (bitp v))) (== v 0))

(defund hi-condition (c z) (declare (xargs :guard (and (bitp c) (bitp z)))) (and (== c 1) (== z 0)))
(defund ls-condition (c z) (declare (xargs :guard (and (bitp c) (bitp z)))) (not (and (== c 1) (== z 0))))

(defund ge-condition (n v) (declare (xargs :guard (and (bitp n) (bitp v)))) (== n v))
(defund lt-condition (n v) (declare (xargs :guard (and (bitp n) (bitp v)))) (not (== n v)))

(defund gt-condition (n v z) (declare (xargs :guard (and (bitp n) (bitp v) (bitp z)))) (and (== n v) (== z 0)))
(defund le-condition (n v z) (declare (xargs :guard (and (bitp n) (bitp v) (bitp z)))) (not (and (== n v) (== z 0))))

(defthm conditionpassed-of-0 (equal (conditionpassed 0 arm) (eq-condition (apsr.z arm))) :hints (("Goal" :in-theory (enable conditionpassed eq-condition))))
(defthm conditionpassed-of-1 (equal (conditionpassed 1 arm) (ne-condition (apsr.z arm))) :hints (("Goal" :in-theory (enable conditionpassed ne-condition))))

(defthm conditionpassed-of-2 (equal (conditionpassed 2 arm) (cs-condition (apsr.c arm))) :hints (("Goal" :in-theory (enable conditionpassed cs-condition))))
(defthm conditionpassed-of-3 (equal (conditionpassed 3 arm) (cc-condition (apsr.c arm))) :hints (("Goal" :in-theory (enable conditionpassed cc-condition))))

(defthm conditionpassed-of-4 (equal (conditionpassed 4 arm) (mi-condition (apsr.n arm))) :hints (("Goal" :in-theory (enable conditionpassed mi-condition))))
(defthm conditionpassed-of-5 (equal (conditionpassed 5 arm) (pl-condition (apsr.n arm))) :hints (("Goal" :in-theory (enable conditionpassed pl-condition))))

(defthm conditionpassed-of-6 (equal (conditionpassed 6 arm) (vs-condition (apsr.v arm))) :hints (("Goal" :in-theory (enable conditionpassed vs-condition))))
(defthm conditionpassed-of-7 (equal (conditionpassed 7 arm) (vc-condition (apsr.v arm))) :hints (("Goal" :in-theory (enable conditionpassed vc-condition))))

(defthm conditionpassed-of-8 (equal (conditionpassed 8 arm) (hi-condition (apsr.c arm) (apsr.z arm))) :hints (("Goal" :in-theory (enable conditionpassed hi-condition))))
(defthm conditionpassed-of-9 (equal (conditionpassed 9 arm) (ls-condition (apsr.c arm) (apsr.z arm))) :hints (("Goal" :in-theory (enable conditionpassed ls-condition))))

(defthm conditionpassed-of-10 (equal (conditionpassed 10 arm) (ge-condition (apsr.n arm) (apsr.v arm))) :hints (("Goal" :in-theory (enable conditionpassed ge-condition))))
(defthm conditionpassed-of-11 (equal (conditionpassed 11 arm) (lt-condition (apsr.n arm) (apsr.v arm))) :hints (("Goal" :in-theory (enable conditionpassed lt-condition))))

(defthm conditionpassed-of-12 (equal (conditionpassed 12 arm) (gt-condition (apsr.n arm) (apsr.v arm) (apsr.z arm))) :hints (("Goal" :in-theory (enable conditionpassed gt-condition))))
(defthm conditionpassed-of-13 (equal (conditionpassed 13 arm) (le-condition (apsr.n arm) (apsr.v arm) (apsr.z arm))) :hints (("Goal" :in-theory (enable conditionpassed le-condition))))

(defthm conditionpassed-of-14 (equal (conditionpassed 14 arm) t) :hints (("Goal" :in-theory (enable conditionpassed))))
(defthm conditionpassed-of-15 (equal (conditionpassed 15 arm) t) :hints (("Goal" :in-theory (enable conditionpassed))))
