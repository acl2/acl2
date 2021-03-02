; Bounded variant of dag-parent-arrayp
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "dag-parent-arrayp")

;;;
;;; bounded-dag-parent-entriesp
;;;

;; Check that all entries from n down to 0 are lists (of numbers) less than limit.
(defund bounded-dag-parent-entriesp (n dag-parent-array-name dag-parent-array limit)
  (declare (xargs :measure (nfix (+ 1 n))
                  :guard (and (integerp n)
                              (natp limit)
                              (array1p dag-parent-array-name dag-parent-array)
                              (< n (alen1 dag-parent-array-name dag-parent-array))
                              (all-dag-parent-entriesp n dag-parent-array-name dag-parent-array))
                  :guard-hints (("Goal" :in-theory (enable all-dag-parent-entriesp)))))
  (if (not (natp n))
      t
    (let ((parents (aref1 dag-parent-array-name dag-parent-array n)))
      (and (all-< parents limit)
           (bounded-dag-parent-entriesp (+ -1 n) dag-parent-array-name dag-parent-array limit)))))

(defthm all-<-of-aref1-when-bounded-dag-parent-entriesp
  (implies (and (bounded-dag-parent-entriesp m dag-parent-array-name dag-parent-array limit2)
                (<= limit2 limit)
                (<= n m)
                (integerp m)
                (natp n))
           (all-< (aref1 dag-parent-array-name dag-parent-array n) limit))
  :hints (("Goal" :in-theory (enable bounded-dag-parent-entriesp))))

(defthm bounded-dag-parent-entriesp-monotone
  (implies (and (bounded-dag-parent-entriesp n dag-parent-array-name dag-parent-array limit2)
                (<= limit2 limit))
           (bounded-dag-parent-entriesp n dag-parent-array-name dag-parent-array limit))
  :hints (("Goal" :in-theory (enable bounded-dag-parent-entriesp))))

(defthm bounded-dag-parent-entriesp-monotone-gen
  (implies (and (bounded-dag-parent-entriesp n dag-parent-array-name dag-parent-array limit2)
                (<= (nfix m) n)
                (<= limit2 limit)
                (natp n))
           (bounded-dag-parent-entriesp m dag-parent-array-name dag-parent-array limit))
  :hints (("Goal"  :expand (bounded-dag-parent-entriesp m dag-parent-array-name dag-parent-array limit)
           :in-theory (enable bounded-dag-parent-entriesp))))

(defthm bounded-dag-parent-entriesp-of-maybe-expand-array
  (implies (and (array1p dag-parent-array-name dag-parent-array)
                (natp index)
                (<= index 2147483645))
           (equal (bounded-dag-parent-entriesp n dag-parent-array-name (maybe-expand-array dag-parent-array-name dag-parent-array index) limit)
                  (bounded-dag-parent-entriesp n dag-parent-array-name dag-parent-array limit)))
  :hints (("Goal" :in-theory (enable bounded-dag-parent-entriesp))))



;; it's sufficient for all legal entries to be okay, since aref1 returns the default if the index is too large
(defthmd bounded-dag-parent-entriesp-suff
  (implies (and (bounded-dag-parent-entriesp (+ -1 (alen1 dag-parent-array-name dag-parent-array)) dag-parent-array-name dag-parent-array limit)
                (array1p dag-parent-array-name dag-parent-array)
                (equal (default dag-parent-array-name dag-parent-array) nil)
                (natp n))
           (bounded-dag-parent-entriesp n dag-parent-array-name dag-parent-array limit))
  :hints (("Subgoal *1/5" :cases ((< n (alen1 dag-parent-array-name dag-parent-array))))
          ("Goal" :in-theory (enable bounded-dag-parent-entriesp))))

(defthm bounded-dag-parent-entriesp-of-make-empty-array
  (implies (and (symbolp dag-parent-array-name)
                (integerp n)
                (<= n parent-array-len)
                (posp parent-array-len)
                (< parent-array-len 2147483647))
           (bounded-dag-parent-entriesp n dag-parent-array-name (make-empty-array dag-parent-array-name parent-array-len) limit))
  :hints (("Goal" :expand ((bounded-dag-parent-entriesp
                            0 dag-parent-array-name
                            (make-empty-array dag-parent-array-name parent-array-len)
                            limit))
           :in-theory (enable bounded-dag-parent-entriesp))))

;;;
;;; bounded-dag-parent-arrayp
;;;

;; Recognize a dag-parent-array such that the entries in the dag-parent-array only contain nodenums less than the dag-len
(defund bounded-dag-parent-arrayp (dag-parent-array-name dag-parent-array dag-len)
  (declare (xargs :guard (natp dag-len)
                  :guard-hints (("Goal" :in-theory (enable dag-parent-arrayp)))))
  (and (dag-parent-arrayp dag-parent-array-name dag-parent-array)
       (bounded-dag-parent-entriesp (+ -1 (alen1 dag-parent-array-name dag-parent-array))
                                    dag-parent-array-name
                                    dag-parent-array
                                    dag-len)))

(defthm bounded-dag-parent-arrayp-forward-to-bounded-dag-parent-arrayp
  (implies (bounded-dag-parent-arrayp dag-parent-array-name dag-parent-array dag-len)
           (dag-parent-arrayp dag-parent-array-name dag-parent-array))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable bounded-dag-parent-arrayp))))

(defthm bounded-dag-parent-arrayp-of-make-empty-array
  (implies (and (posp dag-len)
                (<= dag-len 2147483646)
                (symbolp dag-parent-array-name))
           (bounded-dag-parent-arrayp dag-parent-array-name (make-empty-array dag-parent-array-name dag-len) dag-len))
  :hints (("Goal" :in-theory (enable bounded-dag-parent-arrayp))))

(defthm bounded-dag-parent-arrayp-of-make-empty-array-gen
  (implies (and (posp dag-len)
                (<= dag-len 2147483646)
                (symbolp dag-parent-array-name)
                (<= lim dag-len))
           (bounded-dag-parent-arrayp dag-parent-array-name (make-empty-array dag-parent-array-name dag-len) lim))
  :hints (("Goal" :in-theory (enable bounded-dag-parent-arrayp))))

(defthm all-<-of-aref1-when-bounded-dag-parent-arrayp
  (implies (and (bounded-dag-parent-arrayp dag-parent-array-name dag-parent-array dag-len)
                (< n (alen1 dag-parent-array-name dag-parent-array))
                (natp n))
           (all-< (aref1 dag-parent-array-name dag-parent-array n) dag-len))
  :hints (("Goal" :in-theory (enable bounded-dag-parent-arrayp))))

(defthm bounded-dag-parent-arrayp-monotone
  (implies (and (bounded-dag-parent-arrayp dag-parent-array-name dag-parent-array dag-len)
                (<= dag-len n)
                (natp dag-len)
                (natp n))
           (bounded-dag-parent-arrayp dag-parent-array-name dag-parent-array n))
  :hints (("Goal" :in-theory (enable bounded-dag-parent-arrayp))))
