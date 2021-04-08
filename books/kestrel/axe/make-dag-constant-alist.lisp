; Making the dag-constant-alist
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

(include-book "dag-arrays")
(include-book "dag-constant-alist")

;;;
;;; make-dag-constant-alist-aux
;;;

;returns the dag-constant-alist.
;if we have the dag-lst in hand, can we do better?
(defund make-dag-constant-alist-aux (n ;counts up
                                    dag-array-name dag-array dag-len
                                    ;;gets populated:
                                    dag-constant-alist)
  (declare (xargs :measure (nfix (+ 1 (- dag-len n)))
                  :guard (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (natp n)
                              (<= n dag-len)
                              (dag-constant-alistp dag-constant-alist))))
  (if (or (>= n dag-len)
          (not (mbt (natp n)))
          (not (mbt (natp dag-len))))
      dag-constant-alist
    (let* ((expr (aref1 dag-array-name dag-array n)))
      (make-dag-constant-alist-aux (+ 1 n)
                                   dag-array-name dag-array dag-len
                                   (if (and (consp expr) ;not a variable
                                            (or (eq 'quote (ffn-symb expr))
                                                (all-consp (dargs expr))))
                                       (acons-fast expr n dag-constant-alist)
                                     dag-constant-alist)))))

(defthm dag-constant-alistp-of-make-dag-constant-alist-aux
  (implies (dag-constant-alistp dag-constant-alist)
           (dag-constant-alistp (make-dag-constant-alist-aux n dag-array-name dag-array dag-len dag-constant-alist)))
  :hints (("Goal" :in-theory (enable make-dag-constant-alist-aux))))

(defthm all-<-of-strip-cdrs-of-make-dag-constant-alist-aux
  (implies (and (pseudo-dag-arrayp-aux dag-array-name dag-array (+ -1 dag-len))
                (all-< (strip-cdrs dag-constant-alist) dag-len))
           (all-< (strip-cdrs (make-dag-constant-alist-aux n dag-array-name dag-array dag-len dag-constant-alist))
                  dag-len))
  :hints (("Goal" :in-theory (enable make-dag-constant-alist-aux))))

(defthm bounded-dag-constant-alistp-of-make-dag-constant-alist-aux
  (implies (and (bounded-dag-constant-alistp dag-constant-alist dag-len)
                (pseudo-dag-arrayp-aux dag-array-name dag-array (+ -1 dag-len)))
           (bounded-dag-constant-alistp (make-dag-constant-alist-aux n dag-array-name dag-array dag-len dag-constant-alist) dag-len))
  :hints (("Goal" :in-theory (enable bounded-dag-constant-alistp))))

(defthm make-dag-constant-alist-aux-base
  (equal (make-dag-constant-alist-aux dag-len dag-array-name array dag-len dag-constant-alist)
         dag-constant-alist)
  :hints (("Goal" :expand (make-dag-constant-alist-aux dag-len dag-array-name array dag-len dag-constant-alist)
           :in-theory (enable make-dag-constant-alist-aux))))

(defthm make-dag-constant-alist-aux-of-aset1-expandable
  (implies (and (natp dag-len)
                (natp n)
                (<= n dag-len)
                (<= dag-len 2147483645)
                (pseudo-dag-arrayp dag-array-name dag-array dag-len))
           (equal (make-dag-constant-alist-aux n dag-array-name (aset1-expandable dag-array-name dag-array dag-len expr) (+ 1 dag-len) dag-constant-alist)
                  (if (and (consp expr)
                           (or (eq 'quote (ffn-symb expr))
                               (all-consp (fargs expr))))
                      (acons-fast expr dag-len (make-dag-constant-alist-aux n dag-array-name dag-array dag-len dag-constant-alist))
                    (make-dag-constant-alist-aux n dag-array-name dag-array dag-len dag-constant-alist))))
  :hints (("Goal" :expand ((make-dag-constant-alist-aux n dag-array-name
                                                        (aset1-expandable dag-array-name dag-array dag-len expr)
                                                        (+ 1 dag-len)
                                                        dag-constant-alist)
                           (make-dag-constant-alist-aux dag-len dag-array-name
                                                        (aset1-expandable dag-array-name dag-array dag-len var)
                                                        (+ 1 dag-len)
                                                        dag-constant-alist))
           :in-theory (enable make-dag-constant-alist-aux))))

;;;
;;; make-dag-constant-alist
;;;

;; See also make-dag-indices.
(defund make-dag-constant-alist (dag-array-name dag-array dag-len)
  (declare (xargs :guard (pseudo-dag-arrayp dag-array-name dag-array dag-len)))
  (make-dag-constant-alist-aux 0 dag-array-name dag-array dag-len nil))

(defthm dag-constant-alistp-of-make-dag-constant-alist
  (dag-constant-alistp (make-dag-constant-alist dag-array-name dag-array dag-len))
  :hints (("Goal" :in-theory (enable make-dag-constant-alist))))

(defthm make-dag-constant-alist-of-0
  (equal (make-dag-constant-alist dag-array-name dag-array 0)
         nil)
  :hints (("Goal" :in-theory (enable make-dag-constant-alist))))

(defthm bounded-dag-constant-alistp-of-make-dag-constant-alist
  (implies (pseudo-dag-arrayp dag-array-name dag-array dag-len)
           (bounded-dag-constant-alistp (make-dag-constant-alist dag-array-name dag-array dag-len) dag-len))
  :hints (("Goal" :in-theory (enable make-dag-constant-alist pseudo-dag-arrayp))))

(defthm all-<-of-strip-cdrs-of-make-dag-constant-alist
  (implies (pseudo-dag-arrayp dag-array-name dag-array dag-len)
           (all-< (strip-cdrs (make-dag-constant-alist dag-array-name dag-array dag-len))
                  dag-len))
  :hints (("Goal" :in-theory (enable make-dag-constant-alist pseudo-dag-arrayp))))

;covers extending the dag by one node
(defthm make-dag-constant-alist-of-aset1-expandable
  (implies (and (natp dag-len)
                (<= dag-len 2147483645)
                (pseudo-dag-arrayp dag-array-name dag-array dag-len))
           (equal (make-dag-constant-alist dag-array-name (aset1-expandable dag-array-name dag-array dag-len expr) (+ 1 dag-len))
                  (if (and (consp expr)
                           (or (eq 'quote (ffn-symb expr))
                               (all-consp (fargs expr))))
                      (acons-fast expr dag-len (make-dag-constant-alist dag-array-name dag-array dag-len))
                    (make-dag-constant-alist dag-array-name dag-array dag-len))))
  :hints (("Goal" :expand ((make-dag-constant-alist-aux
                            0 dag-array-name
                            (aset1-expandable dag-array-name dag-array dag-len expr)
                            (+ 1 dag-len)
                            nil))
           :in-theory (enable make-dag-constant-alist make-dag-constant-alist-aux))))
