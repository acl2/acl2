; Finding the largest nodenum in a list of DAG function args ("dargs")
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2022 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "all-dargp")

;;;
;;; largest-non-quotep
;;;

;; Return the largest nodenum in the ITEMS, each of which should be a nodenum
;; or a quoted constant.  If ITEMS contains no nodenums, return -1.
(defund largest-non-quotep (items)
  (declare (xargs :guard (and (true-listp items)
                              (all-dargp items))))
  (if (endp items)
      -1 ;think about this as the default
    (let ((item (car items)))
      (if (consp item) ; skip quoteps
          (largest-non-quotep (cdr items))
        (max (mbe :logic (nfix item)
                  :exec item)
             (largest-non-quotep (cdr items)))))))

(defthm integerp-of-largest-non-quotep
  (integerp (largest-non-quotep items))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable all-dargp largest-non-quotep))))

(defthm <=-of--1-and-largest-non-quotep-linear
  (<= -1 (largest-non-quotep dags))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable largest-non-quotep))))

(defthmd not-<-of-largest-non-quotep-and--1
  (not (< (largest-non-quotep dags) -1)))

(defthm largest-non-quotep-of-cons
  (implies (and (dargp arg)
                (all-dargp args))
           (equal (largest-non-quotep (cons arg args))
                  (if (consp arg)
                      (largest-non-quotep args)
                    (max arg (largest-non-quotep args)))))
  :hints (("Goal" :in-theory (enable largest-non-quotep))))

(defthm largest-non-quotep-of-cdr-bound
  (<= (largest-non-quotep (cdr items)) (largest-non-quotep items))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable largest-non-quotep))))

(defthm largest-non-quotep-bound-linear
  (<= -1 (largest-non-quotep items))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable largest-non-quotep))))

(defthm largest-non-quotep-bound
  (implies (natp (car items))
           (<= (car items) (largest-non-quotep items)))
  :rule-classes (:rewrite (:linear :trigger-terms ((largest-non-quotep items))))
  :hints (("Goal" :in-theory (enable largest-non-quotep))))

(defthm largest-non-quotep-bound-alt
  (implies (natp (nth 0 items))
           (<= (nth 0 items) (largest-non-quotep items)))
  :rule-classes (:rewrite (:linear :trigger-terms ((largest-non-quotep items))))
  :hints (("Goal" :use (:instance largest-non-quotep-bound)
           :in-theory (disable largest-non-quotep-bound))))

(defthm natp-of-largest-non-quotep
  (implies (and (all-dargp items)
                (not (all-myquotep items)))
           (natp (largest-non-quotep items)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable ALL-DARGP LARGEST-NON-QUOTEP))))

(defthm natp-of-largest-non-quotep-2
  (implies (all-dargp items)
           (equal (natp (largest-non-quotep items))
                  (not (equal -1 (largest-non-quotep items))))))

(defthm equal-of--1-and-largest-non-quotep
  (implies (all-dargp items)
           (equal (equal -1 (largest-non-quotep items))
                  (all-myquotep items)))
  :hints (("Goal" :in-theory (enable largest-non-quotep))))

(defthm largest-non-quotep-when-all-myquotep-cheap
  (implies (all-myquotep items)
           (equal (largest-non-quotep items)
                  -1))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable largest-non-quotep))))

(defthm largest-non-quotep-when-all-consp-cheap
  (implies (all-consp items)
           (equal (largest-non-quotep items)
                  -1))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable largest-non-quotep))))

(defthm natp-of-+-of-1-and-largest-non-quotep
  (natp (+ 1 (largest-non-quotep items)))
  :hints (("Goal" :in-theory (enable largest-non-quotep))))
