; Arrays for renumbering DAG nodes
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

;; See also translation-array.lisp.

;; TODO: Can we define this using def-typed-acl2-array?

;;;
;;; the renaming-array
;;;

;; Checks that, for all indices from top-nodenum-to-check down to 0, the array
;; maps the index to either a quotep or a nodenum.
(defund renaming-arrayp-aux (array-name array top-nodenum-to-check)
  (declare (xargs :measure (nfix (+ 1 top-nodenum-to-check))
                  :guard (and (array1p array-name array)
                              (integerp top-nodenum-to-check)
                              (< top-nodenum-to-check (alen1 array-name array)))))
  (if (not (natp top-nodenum-to-check))
      t
    (let ((val (aref1 array-name array top-nodenum-to-check)))
      (and (or (myquotep val)
               (natp val))
           (renaming-arrayp-aux array-name array (+ -1 top-nodenum-to-check))))))

(defthm renaming-arrayp-aux-of--1
  (renaming-arrayp-aux array-name array -1)
  :hints (("Goal" :in-theory (enable renaming-arrayp-aux))))

(defthm renaming-arrayp-aux-monotone
  (implies (and (renaming-arrayp-aux renaming-array-name renaming-array n) ;n is a free var
                (<= m n)
                (integerp n)
                (integerp m))
           (renaming-arrayp-aux renaming-array-name renaming-array m))
  :hints (("Goal" :in-theory (enable renaming-arrayp-aux))))

;; the aset1 is irrelevant
(defthm renaming-arrayp-aux-of-aset1-too-large
  (implies (and (< n index) ;this case
                (array1p renaming-array-name renaming-array)
                (< n (alen1 renaming-array-name renaming-array))
                (< index (alen1 renaming-array-name renaming-array))
                (integerp index)
                (integerp n))
           (equal (renaming-arrayp-aux renaming-array-name (aset1 renaming-array-name renaming-array index val) n)
                  (renaming-arrayp-aux renaming-array-name renaming-array n)))
  :hints (("Goal" :expand ((renaming-arrayp-aux renaming-array-name (aset1 renaming-array-name renaming-array 0 val) 0))
           :in-theory (e/d (renaming-arrayp-aux) (myquotep)))))

(defthm renaming-arrayp-aux-of-aset1
  (implies (and (renaming-arrayp-aux renaming-array-name renaming-array n)
                (dargp val)
                (array1p renaming-array-name renaming-array)
                (< n (alen1 renaming-array-name renaming-array))
                (< index (alen1 renaming-array-name renaming-array))
                (natp index)
                (integerp n))
           (renaming-arrayp-aux renaming-array-name (aset1 renaming-array-name renaming-array index val) n))
  :hints (("Goal" :expand ((renaming-arrayp-aux renaming-array-name (aset1 renaming-array-name renaming-array 0 val) 0))
           :in-theory (e/d (renaming-arrayp-aux) (myquotep)))))

(defthm renaming-arrayp-aux-of-aset1-special
  (implies (and (equal index n) ;this case
                (renaming-arrayp-aux renaming-array-name renaming-array (+ -1 n)) ;n-1 since we are overwriting index n
                (dargp val)
                (array1p renaming-array-name renaming-array)
                (< index (alen1 renaming-array-name renaming-array))
                (integerp index))
           (renaming-arrayp-aux renaming-array-name (aset1 renaming-array-name renaming-array index val) n))
  :hints (("Goal" :expand ((renaming-arrayp-aux renaming-array-name (aset1 renaming-array-name renaming-array index val) index)
                           (renaming-arrayp-aux renaming-array-name (aset1 renaming-array-name renaming-array 0 val) 0))
           :cases ((equal index 0))
           :in-theory (e/d () (myquotep)))))

;;;
;;; renaming-arrayp
;;;

(defund renaming-arrayp (array-name array array-len)
  (declare (xargs :guard t))
  (and (array1p array-name array)
       (natp array-len)
       (<= array-len (alen1 array-name array))
       (renaming-arrayp-aux array-name array (+ -1 array-len))))

(defthm renaming-arrayp-of-0
  (equal (renaming-arrayp array-name array 0)
         (array1p array-name array))
  :hints (("Goal" :in-theory (enable renaming-arrayp))))

;; Rename any of the ARGS that are nodenums according to the RENAMING-ARRAY.
(defund rename-args (args renaming-array-name renaming-array)
  (declare (xargs :guard (and (array1p renaming-array-name renaming-array)
                              (true-listp args)
                              (all-dargp-less-than args (alen1 renaming-array-name renaming-array))
                              (renaming-arrayp-aux renaming-array-name renaming-array (largest-non-quotep args)))))
  (if (endp args)
      nil
    (let* ((arg (first args)))
      (cons (if (consp arg)
                ;;quoted constant, do nothing:
                arg
              ;;nodenum to fixup:
              (aref1 renaming-array-name renaming-array arg))
            (rename-args (rest args) renaming-array-name renaming-array)))))

;normalize to whether it is a consp
(defthm integerp-of-aref1-when-renaming-arrayp-aux
  (implies (and (renaming-arrayp-aux renaming-array-name renaming-array top-nodenum-to-check)
                (integerp top-nodenum-to-check)
                (natp nodenum)
                (<= nodenum top-nodenum-to-check))
           (equal (integerp (aref1 renaming-array-name renaming-array nodenum))
                  (not (consp (aref1 renaming-array-name renaming-array nodenum)))
                  ))
  :hints (("Goal" :in-theory (enable renaming-arrayp-aux))))

(defthm <=-of-0-of-aref1-when-renaming-arrayp-aux
  (implies (and (renaming-arrayp-aux renaming-array-name renaming-array top-nodenum-to-check)
       ;         (not (consp (aref1 renaming-array-name renaming-array nodenum)))
                (integerp top-nodenum-to-check)
                (natp nodenum)
                (<= nodenum top-nodenum-to-check))
           (<= 0 (aref1 renaming-array-name renaming-array nodenum)))
  :hints (("Goal" :in-theory (enable renaming-arrayp-aux))))

(defthm myquotep-of-aref1-when-renaming-arrayp-aux
  (implies (and (renaming-arrayp-aux renaming-array-name renaming-array top-nodenum-to-check)
                (integerp top-nodenum-to-check)
                (natp nodenum)
                (<= nodenum top-nodenum-to-check))
           (equal (myquotep (aref1 renaming-array-name renaming-array nodenum))
                  (consp (aref1 renaming-array-name renaming-array nodenum))))
  :hints (("Goal" :in-theory (enable renaming-arrayp-aux))))

(defthm dargp-of-aref1-when-renaming-arrayp-aux
  (implies (and (renaming-arrayp-aux renaming-array-name renaming-array top-nodenum-to-check) ;free var
                (integerp top-nodenum-to-check)
                (natp nodenum)
                (<= nodenum top-nodenum-to-check))
           (dargp (aref1 renaming-array-name renaming-array nodenum)))
  :hints (("Goal" :in-theory (enable renaming-arrayp-aux))))

(defthm dargp-of-aref1-when-renaming-arrayp-aux-alt
  (implies (and (renaming-arrayp-aux renaming-array-name renaming-array nodenum)
                (natp nodenum))
           (dargp (aref1 renaming-array-name renaming-array nodenum)))
  :hints (("Goal" :in-theory (enable renaming-arrayp-aux))))

(defthm true-listp-of-aref1-when-renaming-arrayp-aux
  (implies (and (renaming-arrayp-aux renaming-array-name renaming-array top-nodenum-to-check)
                (integerp top-nodenum-to-check)
                (natp nodenum)
                (<= nodenum top-nodenum-to-check))
           (equal (true-listp (aref1 renaming-array-name renaming-array nodenum))
                  (consp (aref1 renaming-array-name renaming-array nodenum))))
  :hints (("Goal" :in-theory (enable renaming-arrayp-aux))))

(defthm equal-of-quote-and-car-of-aref1-when-renaming-arrayp-aux
  (implies (and (renaming-arrayp-aux renaming-array-name renaming-array top-nodenum-to-check)
                (integerp top-nodenum-to-check)
                (natp nodenum)
                (<= nodenum top-nodenum-to-check))
           (equal (equal 'quote (car (aref1 renaming-array-name renaming-array nodenum)))
                  (consp (aref1 renaming-array-name renaming-array nodenum))))
  :hints (("Goal" :in-theory (enable renaming-arrayp-aux))))

(defthm not-cddr-of-aref1-when-renaming-arrayp-aux
  (implies (and (renaming-arrayp-aux renaming-array-name renaming-array top-nodenum-to-check)
                (integerp top-nodenum-to-check)
                (natp nodenum)
                (<= nodenum top-nodenum-to-check))
           (not (cddr (aref1 renaming-array-name renaming-array nodenum))))
  :hints (("Goal" :in-theory (enable renaming-arrayp-aux))))

(defthm cdr-of-aref1-when-renaming-arrayp-aux-iff
  (implies (and (renaming-arrayp-aux renaming-array-name renaming-array top-nodenum-to-check)
                (integerp top-nodenum-to-check)
                (natp nodenum)
                (<= nodenum top-nodenum-to-check))
           (iff (cdr (aref1 renaming-array-name renaming-array nodenum))
                (consp (aref1 renaming-array-name renaming-array nodenum))))
  :hints (("Goal" :in-theory (enable renaming-arrayp-aux))))

(defthm all-dargp-of-rename-args
  (implies (and (renaming-arrayp-aux renaming-array-name renaming-array (largest-non-quotep args))
                (all-dargp args))
           (all-dargp (rename-args args renaming-array-name renaming-array)))
  :hints (("Goal" :in-theory (e/d (rename-args all-dargp) (myquotep))
           :expand (all-dargp args)
           :do-not '(generalize eliminate-destructors))))

(defthm consp-of-cdr-of-aref1-when-renaming-arrayp-aux
  (implies (and (renaming-arrayp-aux renaming-array-name renaming-array top-nodenum-to-check)
                (integerp top-nodenum-to-check)
                (natp nodenum)
                (<= nodenum top-nodenum-to-check))
           (equal (consp (cdr (aref1 renaming-array-name renaming-array nodenum)))
                  (consp (aref1 renaming-array-name renaming-array nodenum))))
  :hints (("Goal" :in-theory (enable renaming-arrayp-aux))))

;; Check that all elements from n down to 0 are less than limit, assuming they are not conses (quoteps)
(defund bounded-renaming-entriesp (n renaming-array-name renaming-array limit)
  (declare (xargs :guard (and (integerp n)
                              (natp limit)
                              (array1p renaming-array-name renaming-array)
                              (< n (alen1 renaming-array-name renaming-array))
                              (renaming-arrayp-aux renaming-array-name renaming-array n))
                  :guard-hints (("Goal" :in-theory (enable renaming-arrayp-aux)))))
  (declare (xargs :measure (nfix (+ 1 n))))
  (if (not (natp n))
      t
    (let ((entry (aref1 renaming-array-name renaming-array n)))
      (and (or (consp entry)
               (< entry limit))
           (bounded-renaming-entriesp (+ -1 n) renaming-array-name renaming-array limit)))))

(defthm <-of-aref1-when-bounded-renaming-entriesp
  (implies (and (bounded-renaming-entriesp n renaming-array-name renaming-array bound)
                (natp n)
                (natp m)
                (<= m n)
                (not (consp (aref1 renaming-array-name renaming-array m))))
           (< (aref1 renaming-array-name renaming-array m) bound))
  :hints (("Goal" :in-theory (enable bounded-renaming-entriesp))))

(defthm bounded-renaming-entriesp-monotone
  (implies (and (bounded-renaming-entriesp n renaming-array-name renaming-array limit) ;n is a free var
                (<= m n)
                (integerp n)
                (integerp m))
           (bounded-renaming-entriesp m renaming-array-name renaming-array limit))
  :hints (("Goal" :in-theory (enable bounded-renaming-entriesp))))

(defthm bounded-renaming-entriesp-monotone-gen
  (implies (and (bounded-renaming-entriesp n renaming-array-name renaming-array limit2) ;n is a free var
                (<= limit2 limit)
                (<= m n)
                (natp limit)
                (natp limit2)
                (integerp n)
                (integerp m))
           (bounded-renaming-entriesp m renaming-array-name renaming-array limit))
  :hints (("Goal" :in-theory (enable bounded-renaming-entriesp))))

(defthm bounded-renaming-entriesp-of-aset1-too-large
  (implies (and (< n index) ;this case
                (natp index)
                (array1p renaming-array-name renaming-array)
                (< index (alen1 renaming-array-name renaming-array)))
           (equal (bounded-renaming-entriesp n renaming-array-name (aset1 renaming-array-name renaming-array index val) limit)
                  (bounded-renaming-entriesp n renaming-array-name renaming-array limit)))
  :hints (("Goal" :in-theory (enable bounded-renaming-entriesp))))

(defthm bounded-renaming-entriesp-of-aset1
  (implies (and (bounded-renaming-entriesp n renaming-array-name renaming-array limit)
                (natp index)
                (dargp-less-than val limit)
                (array1p renaming-array-name renaming-array)
                (< index (alen1 renaming-array-name renaming-array))
                (< n (alen1 renaming-array-name renaming-array))
                (natp n))
           (bounded-renaming-entriesp n renaming-array-name (aset1 renaming-array-name renaming-array index val) limit))
  :hints (("Goal" :expand ((bounded-renaming-entriesp 0 renaming-array-name
                                                      (aset1 renaming-array-name
                                                             renaming-array 0 val)
                                                      limit))
           :in-theory (e/d (bounded-renaming-entriesp) (dargp-less-than)))))

(defthm bounded-renaming-entriesp-of-aset1-special
  (implies (and (bounded-renaming-entriesp (+ -1 n) renaming-array-name renaming-array limit)
                (natp n)
                (array1p renaming-array-name renaming-array)
                (< n (alen1 renaming-array-name renaming-array))
                (natp limit)
                )
           (equal (bounded-renaming-entriesp n renaming-array-name (aset1 renaming-array-name renaming-array n val) limit)
                  (implies (not (consp val))
                           (< val limit))))
  :hints (("Goal" :cases ((equal 0 n))
           :expand ((bounded-renaming-entriesp 0 renaming-array-name
                                               (aset1 renaming-array-name
                                                      renaming-array 0 val)
                                               limit)
                    (bounded-renaming-entriesp n renaming-array-name
                                               (aset1 renaming-array-name
                                                      renaming-array n val)
                                               limit)))))

(defthmd bounded-renaming-entriesp-of-aset1-special-gen
  (implies (and (equal n2 n)
                (bounded-renaming-entriesp (+ -1 n) renaming-array-name renaming-array limit)
                (natp n)
                (array1p renaming-array-name renaming-array)
                (< n (alen1 renaming-array-name renaming-array))
                (natp limit)
                )
           (equal (bounded-renaming-entriesp n renaming-array-name (aset1 renaming-array-name renaming-array n2 val) limit)
                  (implies (not (consp val)) (< val limit))))
  :hints (("Goal" :use (:instance bounded-renaming-entriesp-of-aset1-special)
           :in-theory (disable bounded-renaming-entriesp-of-aset1-special))))

(defthm dargp-less-than-of-aref1-when-renaming-arrayp-aux-free
  (implies (and (renaming-arrayp-aux renaming-array-name renaming-array n) ;free var
                (bounded-renaming-entriesp n renaming-array-name renaming-array limit)
                (<= nodenum n)
                (natp nodenum)
                (integerp n)
                )
           (dargp-less-than (aref1 renaming-array-name renaming-array nodenum) limit))
  :hints (("Goal" :in-theory (e/d (bound-lemma-for-car-when-all-dargp-less-than dargp-less-than) (myquotep)))))

(defthm dargp-less-than-of-aref1-when-renaming-arrayp-aux
  (implies (and (renaming-arrayp-aux renaming-array-name renaming-array nodenum)
                (bounded-renaming-entriesp nodenum renaming-array-name renaming-array limit)
                (natp nodenum))
           (dargp-less-than (aref1 renaming-array-name renaming-array nodenum) limit))
  :hints (("Goal" :in-theory (e/d (bound-lemma-for-car-when-all-dargp-less-than) (myquotep)))))

(defthm all-dargp-less-than-of-rename-args
  (implies (and (renaming-arrayp-aux renaming-array-name renaming-array n)
                (bounded-renaming-entriesp n renaming-array-name renaming-array limit)
                (all-dargp-less-than args (+ 1 n))
                (integerp n)
                )
           (all-dargp-less-than (rename-args args renaming-array-name renaming-array) limit))
  :hints (("Goal" :in-theory (e/d (rename-args bound-lemma-for-car-when-all-dargp-less-than) (myquotep)))))

(defthm bounded-renaming-entriesp-of--1
  (bounded-renaming-entriesp -1 renaming-array-name renaming-array limit)
  :hints (("Goal" :in-theory (enable bounded-renaming-entriesp))))

(defthm renaming-arrayp-aux-of-make-empty-array
  (implies (and (posp size)
                (symbolp array-name)
                (< size 2147483647))
           (renaming-arrayp-aux array-name (make-empty-array array-name size) -1))
  :hints (("Goal" :in-theory (enable renaming-arrayp-aux))))


(defun rename-var-or-fn-call-expr (expr renaming-array highest-node-in-renaming)
  (declare (xargs :guard (and (or (symbolp expr)
                                  (dag-function-call-exprp expr))
                              (integerp highest-node-in-renaming)
                              (<= -1 highest-node-in-renaming)
                              (if (consp expr)
                                  (and ;(not (equal 'quote (car expr)))
                                   (all-dargp-less-than (dargs expr) (+ 1 highest-node-in-renaming)))
                                t)
                              (array1p 'renaming-array renaming-array)
                              (< highest-node-in-renaming (alen1 'renaming-array renaming-array))
                              (renaming-arrayp-aux 'renaming-array renaming-array highest-node-in-renaming))
                  :guard-hints (("Goal" :cases ((equal -1 highest-node-in-renaming))))))
  (declare (ignore highest-node-in-renaming))
  (if (variablep expr)
      expr
    (let* ((fn (ffn-symb expr))
           (args (dargs expr)))
      (cons fn (rename-args args 'renaming-array renaming-array)))))
