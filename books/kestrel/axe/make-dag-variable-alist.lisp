; Making the dag-variable-alist
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

(include-book "dag-variable-alist")
(include-book "dag-arrays")
(include-book "kestrel/utilities/acons-fast" :dir :system)

;;;
;;; make-dag-variable-alist-aux
;;;

;returns the dag-variable-alist.
;if we have the dag-lst in hand, can we do better?
(defund make-dag-variable-alist-aux (n ;counts up
                                    dag-array-name dag-array dag-len
                                    ;;gets populated:
                                    dag-variable-alist)
  (declare (xargs :measure (nfix (+ 1 (- dag-len n)))
                  :guard (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (natp n)
                              (<= n dag-len)
                              (dag-variable-alistp dag-variable-alist))))
  (if (or (>= n dag-len)
          (not (mbt (natp n)))
          (not (mbt (natp dag-len))))
      dag-variable-alist
    (let* ((expr (aref1 dag-array-name dag-array n)))
      (make-dag-variable-alist-aux (+ 1 n)
                                   dag-array-name dag-array dag-len
                                   (if (atom expr) ;tests for variable
                                       (acons-fast expr n dag-variable-alist)
                                     dag-variable-alist)))))

(defthm dag-variable-alistp-of-make-dag-variable-alist-aux
  (implies (and (dag-variable-alistp dag-variable-alist)
                (pseudo-dag-arrayp-aux dag-array-name dag-array (+ -1 dag-len)))
           (dag-variable-alistp (make-dag-variable-alist-aux n dag-array-name dag-array dag-len dag-variable-alist)))
  :hints (("Goal" :in-theory (enable make-dag-variable-alist-aux))))

(defthm all-<-of-strip-cdrs-of-make-dag-variable-alist-aux
  (implies (and ;(pseudo-dag-arrayp-aux dag-array-name dag-array (+ -1 dag-len))
                (all-< (strip-cdrs dag-variable-alist) dag-len)
                )
           (all-< (strip-cdrs (make-dag-variable-alist-aux n dag-array-name dag-array dag-len dag-variable-alist))
                  dag-len))
  :hints (("Goal" :in-theory (enable make-dag-variable-alist-aux))))

(defthm bounded-dag-variable-alistp-of-make-dag-variable-alist-aux
  (implies (and (pseudo-dag-arrayp-aux dag-array-name dag-array (+ -1 dag-len))
                (bounded-dag-variable-alistp dag-variable-alist dag-len))
           (bounded-dag-variable-alistp (make-dag-variable-alist-aux n dag-array-name dag-array dag-len dag-variable-alist)
                                        dag-len))
  :hints (("Goal" :in-theory (enable make-dag-variable-alist-aux))))

(defthm member-equal-of-strip-cars-of-make-dag-variable-alist-aux
  (implies (member-equal var (strip-cars dag-variable-alist))
           (member-equal var (strip-cars (make-dag-variable-alist-aux n dag-array-name dag-array dag-len dag-variable-alist))))
  :hints (("Goal" :in-theory (enable make-dag-variable-alist-aux))))

(defthm member-equal-of-aref1-and-strip-cars-of-make-dag-variable-alist-aux
  (implies (and (not (consp (aref1 dag-array-name dag-array nodenum)))
                (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (natp nodenum)
                (< nodenum dag-len)
                (<= n nodenum)
                (natp n))
           (member-equal (aref1 dag-array-name dag-array nodenum)
                    (strip-cars (make-dag-variable-alist-aux n dag-array-name dag-array dag-len dag-variable-alist))))
  :hints (("Goal" :in-theory (enable make-dag-variable-alist-aux))))

(defthm make-dag-variable-alist-aux-base
  (equal (make-dag-variable-alist-aux dag-len dag-array-name array dag-len dag-variable-alist)
         dag-variable-alist)
  :hints (("Goal" :expand (make-dag-variable-alist-aux dag-len dag-array-name array dag-len dag-variable-alist)
           :in-theory (enable make-dag-variable-alist-aux))))

(defthm make-dag-variable-alist-aux-of-aset1-expandable
  (implies (and (natp dag-len)
                (natp n)
                (<= n dag-len)
                (<= dag-len 2147483645)
                (pseudo-dag-arrayp dag-array-name dag-array dag-len))
           (equal (make-dag-variable-alist-aux n dag-array-name (aset1-expandable dag-array-name dag-array dag-len expr) (+ 1 dag-len) dag-variable-alist)
                  (if (consp expr)
                      (make-dag-variable-alist-aux n dag-array-name dag-array dag-len dag-variable-alist)
                    (acons-fast expr dag-len (make-dag-variable-alist-aux n dag-array-name dag-array dag-len dag-variable-alist)))))
  :hints (("Goal" :expand ((make-dag-variable-alist-aux n dag-array-name
                                                        (aset1-expandable dag-array-name dag-array dag-len expr)
                                                        (+ 1 dag-len)
                                                        dag-variable-alist)
                           (make-dag-variable-alist-aux dag-len dag-array-name
                                                        (aset1-expandable dag-array-name dag-array dag-len var)
                                                        (+ 1 dag-len)
                                                        dag-variable-alist))
           :in-theory (enable make-dag-variable-alist-aux))))

;;;
;;; make-dag-variable-alist
;;;

;; See also make-dag-indices.
(defund make-dag-variable-alist (dag-array-name dag-array dag-len)
  (declare (xargs :guard (pseudo-dag-arrayp dag-array-name dag-array dag-len)))
  (make-dag-variable-alist-aux 0 dag-array-name dag-array dag-len nil))

(defthm dag-variable-alistp-of-make-dag-variable-alist
  (implies (pseudo-dag-arrayp dag-array-name dag-array dag-len)
           (dag-variable-alistp (make-dag-variable-alist dag-array-name dag-array dag-len)))
  :hints (("Goal" :in-theory (enable make-dag-variable-alist pseudo-dag-arrayp))))

(defthm make-dag-variable-alist-of-0
  (equal (make-dag-variable-alist dag-array-name dag-array 0)
         nil)
  :hints (("Goal" :in-theory (enable make-dag-variable-alist))))

(defthm all-<-of-strip-cdrs-of-make-dag-variable-alist
  (implies (pseudo-dag-arrayp dag-array-name dag-array dag-len)
           (all-< (strip-cdrs (make-dag-variable-alist dag-array-name dag-array dag-len))
                  dag-len))
  :hints (("Goal" :in-theory (enable make-dag-variable-alist pseudo-dag-arrayp))))

(defthm bounded-dag-variable-alistp-of-make-dag-variable-alist
  (implies (pseudo-dag-arrayp dag-array-name dag-array dag-len)
           (bounded-dag-variable-alistp (make-dag-variable-alist dag-array-name dag-array dag-len) dag-len))
  :hints (("Goal" :in-theory (enable make-dag-variable-alist pseudo-dag-arrayp))))

(defthm member-equal-of-aref1-and-strip-cars-of-make-dag-variable-alist
  (implies (and (not (consp (aref1 dag-array-name dag-array nodenum)))
                (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (natp nodenum)
                (< nodenum dag-len))
           (member-equal (aref1 dag-array-name dag-array nodenum)
                         (strip-cars (make-dag-variable-alist dag-array-name dag-array dag-len))))
  :hints (("Goal" :in-theory (enable make-dag-variable-alist))))

;covers extending the dag by one node
(defthm make-dag-variable-alist-of-aset1-expandable
  (implies (and (natp dag-len)
                (<= dag-len 2147483645)
                (pseudo-dag-arrayp dag-array-name dag-array dag-len))
           (equal (make-dag-variable-alist dag-array-name (aset1-expandable dag-array-name dag-array dag-len expr) (+ 1 dag-len))
                  (if (consp expr)
                      (make-dag-variable-alist dag-array-name dag-array dag-len)
                    (acons-fast expr dag-len (make-dag-variable-alist dag-array-name dag-array dag-len)))))
  :hints (("Goal" :expand ((make-dag-variable-alist-aux
                            0 dag-array-name
                            (aset1-expandable dag-array-name dag-array dag-len expr)
                            (+ 1 dag-len)
                            nil))
           :in-theory (enable make-dag-variable-alist make-dag-variable-alist-aux))))

(defthm <-of-cdr-of-assoc-equal-when-all-<-of-strip-cdrs
  (implies (and (all-< (strip-cdrs alist) bound)
                (ASSOC-EQUAL key alist))
           (< (CDR (ASSOC-EQUAL key alist)) bound)))

(defthm <-of-cdr-of-assoc-equal-of-make-dag-variable-alist-aux
  (implies (and (assoc-equal var (make-dag-variable-alist-aux n dag-array-name dag-array dag-len dag-variable-alist))
                (bounded-dag-variable-alistp dag-variable-alist dag-len)
                ;; (pseudo-dag-arrayp-aux dag-array-name dag-array (+ -1 dag-len))
                ;;(<= n dag-len)
                )
           (< (cdr (assoc-equal var (make-dag-variable-alist-aux n dag-array-name dag-array dag-len dag-variable-alist)))
              dag-len))
  :hints (("Goal" :in-theory (enable make-dag-variable-alist-aux bounded-dag-variable-alistp))))

(defthm <-of-cdr-of-assoc-equal-of-make-dag-variable-alist
  (implies (assoc-equal var (make-dag-variable-alist 'dag-array dag-array dag-len))
           (< (cdr (assoc-equal var (make-dag-variable-alist 'dag-array dag-array dag-len)))
              dag-len))
  :hints (("Goal" :in-theory (enable make-dag-variable-alist))))

(defthm <-of-cdr-of-assoc-equal-of-make-dag-variable-alist-alt
  (implies (and (<= dag-len bound)
                (assoc-equal var (make-dag-variable-alist 'dag-array dag-array dag-len)))
           (< (cdr (assoc-equal var (make-dag-variable-alist 'dag-array dag-array dag-len)))
              bound))
  :hints (("Goal" :use (:instance <-of-cdr-of-assoc-equal-of-make-dag-variable-alist)
           :in-theory (disable <-of-cdr-of-assoc-equal-of-make-dag-variable-alist))))
