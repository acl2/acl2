; Telling the lifter how many steps to take
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; A step-increment tells the lifter how many steps to take at once, before pausing to reset the memoization.
(defund step-incrementp (step-increment)
  (declare (xargs :guard t))
  (or (posp step-increment) ; a simple increment (always step this many times);
      ;; it's of the form: (list normal-increment total-step-threshold increment-after-threshold).  Means step normal-increment times until the total steps reaches the threshold, after which step increment-after-threshold times per chunk.
      (and (true-listp step-increment)
           (eql 3 (len step-increment))
           (posp (first step-increment))
           (natp (second step-increment))
           (posp (third step-increment)))))

(defund this-step-increment (step-increment total-steps)
  (declare (xargs :guard (and (step-incrementp step-increment)
                              (natp total-steps))
                  :guard-hints (("Goal" :in-theory (enable step-incrementp)))))
  (if (natp step-increment)
      step-increment
    (let ((normal-increment (first step-increment))
          (threshold (second step-increment))
          (step-increment-after-threshold (third step-increment)))
      (if (<= threshold total-steps)
          step-increment-after-threshold
        ;; Don't use the full normal increment if it would take us past the threshold:
        (min normal-increment
             (- threshold total-steps))))))

(defthm posp-of-this-step-increment
  (implies (and (step-incrementp step-increment)
                (natp total-steps))
           (posp (this-step-increment step-increment total-steps)))
  :hints (("Goal" :in-theory (enable this-step-increment step-incrementp))))

(defthm posp-of-this-step-increment-type
  (implies (and (step-incrementp step-increment)
                (natp total-steps))
           (posp (this-step-increment step-increment total-steps)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable this-step-increment step-incrementp))))
