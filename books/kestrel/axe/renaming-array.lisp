; Arrays for renumbering DAG nodes
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2024 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "dag-arrays")
(local (include-book "kestrel/acl2-arrays/acl2-arrays" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))

;; A renaming-array maps all nodes, up to a given node, to nodenums or
;; myquoteps.  NOTE: No node in that range can map to nil, but see
;; translation-array.lisp.  The renaming-array may be appropriate for bottom-up
;; algorithms that touch every node.

;; See a faster version of essentially the same concept as this book, see renumbering-stobj.lisp.

;; TODO: Can we define this using def-typed-acl2-array?

;;;
;;; renaming-arrayp-aux
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
      (and (or (myquotep val) ;could call dargp here
               (natp val))
           (renaming-arrayp-aux array-name array (+ -1 top-nodenum-to-check))))))

;; -1 means no nodes to check
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
           :in-theory (disable myquotep))))

(defthm dargp-of-aref1-when-renaming-arrayp-aux
  (implies (and (renaming-arrayp-aux renaming-array-name renaming-array nodenum)
                (natp nodenum))
           (dargp (aref1 renaming-array-name renaming-array nodenum)))
  :hints (("Goal" :in-theory (enable renaming-arrayp-aux))))

(defthm dargp-of-aref1-when-renaming-arrayp-aux-free
  (implies (and (renaming-arrayp-aux renaming-array-name renaming-array top-nodenum-to-check) ;free var
                (integerp top-nodenum-to-check)
                (natp nodenum)
                (<= nodenum top-nodenum-to-check))
           (dargp (aref1 renaming-array-name renaming-array nodenum)))
  :hints (("Goal" :in-theory (disable dargp))))

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

(defthm renaming-arrayp-aux-of-make-empty-array
  (implies (and (posp size)
                (symbolp array-name)
                (<= size *max-1d-array-length*))
           (renaming-arrayp-aux array-name (make-empty-array array-name size) -1))
  :hints (("Goal" :in-theory (enable renaming-arrayp-aux))))

;; enabling dargp-rulesy may avoid the need for these:

(defthm true-listp-of-aref1-when-renaming-arrayp-aux
  (implies (and (renaming-arrayp-aux renaming-array-name renaming-array top-nodenum-to-check)
                (integerp top-nodenum-to-check)
                (natp nodenum)
                (<= nodenum top-nodenum-to-check))
           (equal (true-listp (aref1 renaming-array-name renaming-array nodenum))
                  (consp (aref1 renaming-array-name renaming-array nodenum))))
  :hints (("Goal" :in-theory (enable renaming-arrayp-aux true-listp-when-dargp))))

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
  :hints (("Goal" :in-theory (enable renaming-arrayp-aux not-cddr-when-dargp))))

(defthm cdr-of-aref1-when-renaming-arrayp-aux-iff
  (implies (and (renaming-arrayp-aux renaming-array-name renaming-array top-nodenum-to-check)
                (integerp top-nodenum-to-check)
                (natp nodenum)
                (<= nodenum top-nodenum-to-check))
           (iff (cdr (aref1 renaming-array-name renaming-array nodenum))
                (consp (aref1 renaming-array-name renaming-array nodenum))))
  :hints (("Goal" :in-theory (enable renaming-arrayp-aux))))

(defthm consp-of-cdr-of-aref1-when-renaming-arrayp-aux
  (implies (and (renaming-arrayp-aux renaming-array-name renaming-array top-nodenum-to-check)
                (integerp top-nodenum-to-check)
                (natp nodenum)
                (<= nodenum top-nodenum-to-check))
           (equal (consp (cdr (aref1 renaming-array-name renaming-array nodenum)))
                  (consp (aref1 renaming-array-name renaming-array nodenum))))
  :hints (("Goal" :in-theory (enable renaming-arrayp-aux consp-of-cdr-when-dargp))))

;;;
;;; renaming-arrayp
;;;

;; Checks that ARRAY is a valid array, with name ARRAY-NAME, and length at
;; least NUM-NODES-TO-CHECK, that maps each index from NUM-NODES-TO-CHECK - 1
;; down to 0 to either a myquotep or a nodenum.
(defund renaming-arrayp (array-name array num-nodes-to-check)
  (declare (xargs :guard t))
  (and (array1p array-name array)
       (natp num-nodes-to-check)
       (<= num-nodes-to-check (alen1 array-name array))
       (renaming-arrayp-aux array-name array (+ -1 num-nodes-to-check))))

;; 0 means no nodes to check
(defthm renaming-arrayp-of-0
  (equal (renaming-arrayp array-name array 0)
         (array1p array-name array))
  :hints (("Goal" :in-theory (enable renaming-arrayp))))

(defthm renaming-arrayp-forward-to-array1p
  (implies (renaming-arrayp array-name array num-nodes-to-check)
           (array1p array-name array))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable renaming-arrayp))))

(defthm renaming-arrayp-forward-to-natp
  (implies (renaming-arrayp array-name array num-nodes-to-check)
           (natp num-nodes-to-check))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable renaming-arrayp))))

(defthm array1p-when-renaming-arrayp
  (implies (renaming-arrayp array-name array num-nodes-to-check) ;free var
           (array1p array-name array))
  :hints (("Goal" :in-theory (enable renaming-arrayp))))

(defthm renaming-arrayp-of-aset1
  (implies (and (renaming-arrayp renaming-array-name renaming-array num)
                (dargp val)
                (<= num (alen1 renaming-array-name renaming-array))
                (< index (alen1 renaming-array-name renaming-array))
                (natp index)
                (integerp num))
           (renaming-arrayp renaming-array-name (aset1 renaming-array-name renaming-array index val) num))
  :hints (("Goal" :in-theory (enable renaming-arrayp))))

(defthm renaming-arrayp-of-aset1-special
  (implies (and (equal (+ 1 index) n) ;this case
                (renaming-arrayp renaming-array-name renaming-array index)
                (dargp val)
                (< index (alen1 renaming-array-name renaming-array))
                (natp index))
           (renaming-arrayp renaming-array-name (aset1 renaming-array-name renaming-array index val) n))
  :hints (("Goal" :in-theory (enable renaming-arrayp))))

;;other properties should follow from this
(defthm dargp-of-aref1-when-renaming-arrayp
  (implies (and (renaming-arrayp renaming-array-name renaming-array (+ 1 nodenum))
                (natp nodenum))
           (dargp (aref1 renaming-array-name renaming-array nodenum)))
  :hints (("Goal" :in-theory (enable renaming-arrayp))))

(defthm dargp-of-aref1-when-renaming-arrayp-free
  (implies (and (renaming-arrayp renaming-array-name renaming-array num-nodes-to-check) ;free var
                (integerp num-nodes-to-check)
                (natp nodenum)
                (< nodenum num-nodes-to-check))
           (dargp (aref1 renaming-array-name renaming-array nodenum)))
  :hints (("Goal" :in-theory (enable renaming-arrayp))))

;normalize to whether it is a consp
(defthm myquotep-of-aref1-when-renaming-arrayp-free
  (implies (and (renaming-arrayp renaming-array-name renaming-array num-nodes-to-check) ;free var
                (integerp num-nodes-to-check)
                (natp nodenum)
                (< nodenum num-nodes-to-check))
           (equal (myquotep (aref1 renaming-array-name renaming-array nodenum))
                  (consp (aref1 renaming-array-name renaming-array nodenum))))
  :hints (("Goal" :use dargp-of-aref1-when-renaming-arrayp-free
           :in-theory (disable dargp-of-aref1-when-renaming-arrayp-free
                               dargp-of-aref1-when-renaming-arrayp))))

;normalize to whether it is a consp
(defthm natp-of-aref1-when-renaming-arrayp-free
  (implies (and (renaming-arrayp renaming-array-name renaming-array num-nodes-to-check) ;free var
                (integerp num-nodes-to-check)
                (natp nodenum)
                (< nodenum num-nodes-to-check))
           (equal (natp (aref1 renaming-array-name renaming-array nodenum))
                  (not (consp (aref1 renaming-array-name renaming-array nodenum)))))
  :hints (("Goal" :use dargp-of-aref1-when-renaming-arrayp-free
           :in-theory (disable dargp-of-aref1-when-renaming-arrayp-free
                               dargp-of-aref1-when-renaming-arrayp))))

(defthm renaming-arrayp-monotone
  (implies (and (renaming-arrayp renaming-array-name renaming-array num-nodes-to-check-free) ; free var
                (<= num-nodes-to-check num-nodes-to-check-free)
                ;(natp num-nodes-to-check)
                )
           (equal (renaming-arrayp renaming-array-name renaming-array num-nodes-to-check)
                  (natp num-nodes-to-check)))
  :hints (("Goal" :in-theory (enable renaming-arrayp))))

;;;
;;; rename-darg
;;;

(defund-inline rename-darg (darg renaming-array-name renaming-array)
  (declare (xargs :guard (and (dargp darg)
                              (if (consp darg) ;test for quotep
                                  t
                                (renaming-arrayp renaming-array-name renaming-array (+ 1 darg))))
                  :guard-hints (("Goal" :in-theory (enable renaming-arrayp)))))
  (if (consp darg)
      darg ; quoted constant, do nothing
    ;; nodenum to fixup:
    (aref1 renaming-array-name renaming-array darg)))

(defthm dargp-of-rename-darg
  (implies (and (dargp darg)
                (if (consp darg) ;test for quotep
                    t
                  (renaming-arrayp renaming-array-name renaming-array (+ 1 darg))))
           (dargp (rename-darg darg renaming-array-name renaming-array)))
  :hints (("Goal" :in-theory (e/d (rename-darg) (dargp natp)))))

(defthm natp-of-rename-darg
  (implies (and (dargp darg)
                (if (consp darg) ;test for quotep
                    t
                  (renaming-arrayp renaming-array-name renaming-array (+ 1 darg))))
           (equal (natp (rename-darg darg renaming-array-name renaming-array))
                  (not (consp (rename-darg darg renaming-array-name renaming-array)))))
  :hints (("Goal" :in-theory (e/d (rename-darg) (dargp natp)))))

(defthm integerp-of-rename-darg
  (implies (and (dargp darg)
                (if (consp darg) ;test for quotep
                    t
                  (renaming-arrayp renaming-array-name renaming-array (+ 1 darg))))
           (equal (integerp (rename-darg darg renaming-array-name renaming-array))
                  (not (consp (rename-darg darg renaming-array-name renaming-array)))))
  :hints (("Goal" :in-theory (e/d (rename-darg) (dargp natp)))))

;;;
;;; rename-dargs
;;;

;; Renames any of the DARGS that are nodenums according to the RENAMING-ARRAY.
(defund rename-dargs (dargs renaming-array-name renaming-array)
  (declare (xargs :guard (and (darg-listp dargs)
                              (renaming-arrayp renaming-array-name renaming-array (+ 1 (largest-non-quotep dargs))))
                  :guard-hints (("Goal" :in-theory (enable RENAMING-ARRAYP)))
                  ))
  (if (endp dargs)
      nil
    (cons (rename-darg (first dargs) renaming-array-name renaming-array)
          (rename-dargs (rest dargs) renaming-array-name renaming-array))))

(defthm darg-listp-of-rename-dargs
  (implies (and (renaming-arrayp renaming-array-name renaming-array (+ 1 (largest-non-quotep dargs)))
                (darg-listp dargs))
           (darg-listp (rename-dargs dargs renaming-array-name renaming-array)))
  :hints (("Goal" :in-theory (e/d (rename-dargs darg-listp dargp) (myquotep))
           :expand (darg-listp dargs)
           :do-not '(generalize eliminate-destructors))))

;;;
;;; bounded-renaming-entriesp
;;;

;; Check that all elements from n down to 0 are less than limit, assuming they are not conses (quoteps)
(defund bounded-renaming-entriesp (n renaming-array-name renaming-array limit)
  (declare (xargs :guard (and (integerp n)
                              (natp limit)
                              (array1p renaming-array-name renaming-array)
                              (< n (alen1 renaming-array-name renaming-array))
                              (renaming-arrayp renaming-array-name renaming-array (+ 1 n)))
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
                (integerp n)
                (natp m)
                (<= m n)
                (not (consp (aref1 renaming-array-name renaming-array m))))
           (< (aref1 renaming-array-name renaming-array m) bound))
  :hints (("Goal" :in-theory (enable bounded-renaming-entriesp))))

(defthm <-of-rename-darg-when-bounded-renaming-entriesp
  (implies (and (bounded-renaming-entriesp n renaming-array-name renaming-array bound)
                (integerp n)
                (natp m)
                (<= m n)
                (not (consp (rename-darg m renaming-array-name renaming-array))))
           (< (rename-darg m renaming-array-name renaming-array) bound))
  :hints (("Goal" :in-theory (enable rename-darg))))

(defthm <-of-rename-darg-when-bounded-renaming-entriesp-simple
  (implies (and (bounded-renaming-entriesp m renaming-array-name renaming-array bound)
                (natp m)
                (not (consp (rename-darg m renaming-array-name renaming-array))))
           (< (rename-darg m renaming-array-name renaming-array) bound))
  :hints (("Goal" :in-theory (enable rename-darg))))

(defthm bounded-renaming-entriesp-monotone
  (implies (and (bounded-renaming-entriesp n renaming-array-name renaming-array limit) ;n is a free var
                (<= m n)
                (integerp n)
                (integerp m))
           (bounded-renaming-entriesp m renaming-array-name renaming-array limit))
  :hints (("Goal" :in-theory (enable bounded-renaming-entriesp))))

(defthm bounded-renaming-entriesp-monotone-alt
  (implies (and (bounded-renaming-entriesp m renaming-array-name renaming-array limit2) ;limit2 is a free var
                (<= limit2 limit))
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
                ;(natp n)
                )
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
  :hints (("Goal" :in-theory (e/d (bound-lemma-for-car-when-bounded-darg-listp dargp-less-than) (myquotep)))))

(defthm dargp-less-than-of-aref1-when-renaming-arrayp-aux
  (implies (and (renaming-arrayp-aux renaming-array-name renaming-array nodenum)
                (bounded-renaming-entriesp nodenum renaming-array-name renaming-array limit)
                (natp nodenum))
           (dargp-less-than (aref1 renaming-array-name renaming-array nodenum) limit))
  :hints (("Goal" :in-theory (e/d (bound-lemma-for-car-when-bounded-darg-listp) (myquotep)))))

(defthm dargp-less-than-of-rename-darg
  (implies (and (if (consp darg)
                    t
                  (renaming-arrayp renaming-array-name renaming-array (+ 1 darg)))
                (if (consp darg)
                    t
                  (bounded-renaming-entriesp darg renaming-array-name renaming-array limit))
                (dargp darg))
           (dargp-less-than (rename-darg darg renaming-array-name renaming-array) limit))
  :hints (("Goal" :in-theory (e/d (renaming-arrayp
                                   rename-darg bound-lemma-for-car-when-bounded-darg-listp
                                   dargp)
                                  (myquotep)))))

(defthm bounded-darg-listp-of-rename-dargs
  (implies (and (renaming-arrayp renaming-array-name renaming-array (+ 1 (largest-non-quotep dargs)))
                (bounded-renaming-entriesp (largest-non-quotep dargs) renaming-array-name renaming-array limit)
                (darg-listp dargs))
           (bounded-darg-listp (rename-dargs dargs renaming-array-name renaming-array) limit))
  :hints (("Goal" :in-theory (e/d (dargp ;renaming-arrayp
                                   rename-dargs bound-lemma-for-car-when-bounded-darg-listp) (myquotep)))))

(defthm bounded-renaming-entriesp-of--1
  (bounded-renaming-entriesp -1 renaming-array-name renaming-array limit)
  :hints (("Goal" :in-theory (enable bounded-renaming-entriesp))))

(defthm dargp-less-than-of-aref1-when-renaming-arrayp
  (implies (and (renaming-arrayp renaming-array-name renaming-array (+ 1 nodenum))
                (bounded-renaming-entriesp nodenum renaming-array-name renaming-array limit)
                (natp nodenum))
           (dargp-less-than (aref1 renaming-array-name renaming-array nodenum) limit))
  :hints (("Goal" :in-theory (enable renaming-arrayp))))

(defthm dargp-less-than-of-aref1-when-renaming-arrayp-free
  (implies (and (renaming-arrayp renaming-array-name renaming-array free)
                (bounded-renaming-entriesp nodenum renaming-array-name renaming-array limit)
                (natp free)
                (< nodenum free)
                (natp nodenum))
           (dargp-less-than (aref1 renaming-array-name renaming-array nodenum) limit))
  :hints (("Goal" :in-theory (e/d (bound-lemma-for-car-when-bounded-darg-listp) (myquotep)))))

;;;
;;; bounded-renaming-arrayp
;;;

;; Check that all elements from n down to 0 are less than limit, assuming they are not conses (quoteps)
(defund bounded-renaming-arrayp (renaming-array-name renaming-array num-nodes-to-check bound)
  (declare (xargs :guard (and (integerp num-nodes-to-check)
                              (natp bound))
                  :guard-hints (("Goal" :in-theory (enable RENAMING-ARRAYP)))))
  (and (renaming-arrayp renaming-array-name renaming-array num-nodes-to-check)
       (bounded-renaming-entriesp (+ -1 num-nodes-to-check) renaming-array-name renaming-array bound)))

(defthm bounded-renaming-arrayp-forward-to-renaming-arrayp
  (implies (bounded-renaming-arrayp renaming-array-name renaming-array num-nodes-to-check bound)
           (renaming-arrayp renaming-array-name renaming-array num-nodes-to-check))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable bounded-renaming-arrayp))))

(defthm bounded-renaming-arrayp-of-0-arg3
  (equal (bounded-renaming-arrayp array-name array 0 bound)
         (renaming-arrayp array-name array 0))
  :hints (("Goal" :in-theory (enable bounded-renaming-arrayp))))

(defthm dargp-less-than-of-aref1-when-bounded-renaming-arrayp
  (implies (and (bounded-renaming-arrayp renaming-array-name renaming-array (+ 1 nodenum) limit)
                (natp nodenum))
           (dargp-less-than (aref1 renaming-array-name renaming-array nodenum) limit))
  :hints (("Goal" :in-theory (enable bounded-renaming-arrayp
                                     renaming-arrayp))))

(defthm bounded-darg-listp-of-rename-dargs-when-bounded-renaming-arrayp
  (implies (and (bounded-renaming-arrayp renaming-array-name renaming-array (+ 1 (largest-non-quotep dargs)) limit)
                ;(bounded-darg-listp args (+ 1 n))
;(integerp n)
                (darg-listp dargs)
                )
           (bounded-darg-listp (rename-dargs dargs renaming-array-name renaming-array) limit))
  :hints (("Goal" :in-theory (enable bounded-renaming-arrayp
                                     renaming-arrayp))))

(defthm bounded-renaming-arrayp-monotone1
  (implies (and (bounded-renaming-arrayp renaming-array-name renaming-array num-nodes-to-check2 bound)
                (<= num-nodes-to-check num-nodes-to-check2)
                (natp num-nodes-to-check)
                (natp num-nodes-to-check2)
                )
           (bounded-renaming-arrayp renaming-array-name renaming-array num-nodes-to-check bound))
  :hints (("Goal" :in-theory (enable bounded-renaming-arrayp))))

(defthm bounded-renaming-arrayp-monotone2
  (implies (and (bounded-renaming-arrayp renaming-array-name renaming-array num-nodes-to-check bound2)
                (<= bound2 bound)
                (natp bound)
                (natp bound2)
                )
           (bounded-renaming-arrayp renaming-array-name renaming-array num-nodes-to-check bound))
  :hints (("Goal" :in-theory (enable bounded-renaming-arrayp))))

(defthm bounded-renaming-arrayp-monotone3
  (implies (and (bounded-renaming-arrayp renaming-array-name renaming-array num-nodes-to-check2 bound2)
                (<= bound2 bound)
                (natp bound)
                (natp bound2)
                (<= num-nodes-to-check num-nodes-to-check2)
                (natp num-nodes-to-check)
                (natp num-nodes-to-check2)
                )
           (bounded-renaming-arrayp renaming-array-name renaming-array num-nodes-to-check bound))
  :hints (("Goal" :in-theory (enable bounded-renaming-arrayp))))

(defthm bounded-renaming-arrayp-of-aset1
  (implies (and (bounded-renaming-arrayp renaming-array-name renaming-array num-nodes-to-check bound)
                (natp num-nodes-to-check)
                (<= num-nodes-to-check (alen1 renaming-array-name renaming-array))
                (natp n)
                (< n (alen1 renaming-array-name renaming-array))
                (dargp-less-than val bound)
                )
           (bounded-renaming-arrayp renaming-array-name (aset1 renaming-array-name renaming-array n val) num-nodes-to-check bound))
  :hints (("Goal" :in-theory (enable bounded-renaming-arrayp))))

;;;
;;; rename-var-or-fn-call-expr
;;;

;; only used once, in old rewriter
(defun rename-var-or-fn-call-expr (expr renaming-array highest-node-in-renaming)
  (declare (xargs :guard (and (or (symbolp expr)
                                  (dag-function-call-exprp expr))
                              (integerp highest-node-in-renaming)
                              (<= -1 highest-node-in-renaming)
                              (if (consp expr)
                                  (and ;(not (equal 'quote (car expr)))
                                   (bounded-darg-listp (dargs expr) (+ 1 highest-node-in-renaming)))
                                t)
                              (array1p 'renaming-array renaming-array)
                              (< highest-node-in-renaming (alen1 'renaming-array renaming-array))
                              (renaming-arrayp 'renaming-array renaming-array (+ 1 highest-node-in-renaming)))
                  :guard-hints (("Goal" :in-theory (enable renaming-arrayp)
                                 :cases ((equal -1 highest-node-in-renaming))))))
  (declare (ignore highest-node-in-renaming))
  (if (variablep expr)
      expr
    (let* ((fn (ffn-symb expr))
           (args (dargs expr)))
      (cons fn (rename-dargs args 'renaming-array renaming-array)))))
