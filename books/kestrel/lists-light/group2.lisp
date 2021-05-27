; A variant of group that drops any incomplete final group.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;ffixme harvest good lemmas from this book

(include-book "kestrel/typed-lists-light/items-have-len" :dir :system)
(include-book "kestrel/typed-lists-light/all-true-listp" :dir :system)
(include-book "firstn") ;todo: use take instead?
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod2" :dir :system))
(local (include-book "kestrel/arithmetic-light/ceiling" :dir :system))
(local (include-book "kestrel/library-wrappers/arithmetic-inequalities" :dir :system)) ;todo
(local (include-book "nth"))
(local (include-book "nthcdr"))
(local (include-book "len"))
(local (include-book "cdr"))
(local (include-book "cons"))
(local (include-book "append"))
(local (include-book "take"))
(local (include-book "true-list-fix"))

;(local (in-theory (disable LIST::EQUAL-APPEND-REDUCTION!-alt LIST::EQUAL-APPEND-REDUCTION! LIST::FIRSTN-1-REWRITE-STRONG)))

;(in-theory (disable LIST::EQUAL-APPEND-REDUCTION!-ALT LIST::EQUAL-APPEND-REDUCTION!))

;;
;; group2
;;

;drops any extra elements
(defund group2 (n x)
  (declare (xargs :measure (+ 1 (len x))
                  :guard (true-listp x) ;would be nice for firstn's guard to not require true-listp
                  ))
  (if (or (not (posp n))
          (< (len x) n) ;drop any partial final group
          )
      nil
    (cons (firstn n x)
          (group2 n (nthcdr n x)))))

(defthmd group2-unroll
  (implies (not  (or (not (posp n))
                     (< (len x) n) ;drop any partial final group
                     ))
           (equal (group2 n x)
                  (cons (firstn n x)
                        (group2 n (nthcdr n x)))))
  :hints (("Goal" :in-theory (enable group2))))

(defthm group2-base
  (implies (or (not (posp n))
               (< (len x) n) ;drop any partial final group
               )
           (equal (group2 n x)
                  nil))
  :hints (("Goal" :in-theory (enable group2))))

(defthm consp-of-group2
  (implies (posp n)
           (equal (consp (group2 n list))
                  (<= n (len list))))
  :hints (("Goal" :in-theory (enable group2))))

(defthm group2-of-true-list-fix
  (equal (group2 n (true-list-fix x))
         (group2 n x))
  :hints (("Goal" :in-theory (enable group2))))

;dup
(defun firstn-of-group-induct (x n m)
  (if (zp m)
      (list x n m)
    (firstn-of-group-induct (nthcdr n x) n (+ -1 m))))

(defthm nthcdr-of-group2
  (implies (and (posp n)
                (natp m))
           (equal (nthcdr m (group2 n x))
                  (group2 n (nthcdr (* m n) x))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :induct (firstn-of-group-induct x n m)
           :in-theory (e/d (group2 nthcdr)
                           (NTHCDR-OF-CDR-COMBINE NTHCDR-OF-CDR-COMBINE-STRONG)))))
(defthm car-of-group2
  (implies (and (posp n)
                (<= n (len list)))
           (equal (car (group2 n list))
                  (take n list)))
  :hints (("Goal" :in-theory (enable group2))))

(defthm cdr-of-group2
  (implies (posp n)
           (equal (cdr (group2 n x))
                  (group2 n (nthcdr n x))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :induct (firstn-of-group-induct x n m)
           :expand (group2 n x)
           :in-theory (e/d (group2 nthcdr)
                           (NTHCDR-OF-CDR-COMBINE
                            NTHCDR-OF-CDR-COMBINE-strong)))))

(defthm nth-of-group2
  (implies (and (natp m)
                (< m (floor (len x) n))
                (posp n))
           (equal (nth m (group2 n x))
                  (firstn n (nthcdr (* m n) x))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :expand ((GROUP2 N X))
           :induct (firstn-of-group-induct x n m)
           :in-theory (e/d (group2 ;nthcdr
                            ;LIST::NTH-OF-CONS
                            )
                           ( ;NTHCDR-OF-CDR-COMBINE-strong NTHCDR-OF-CDR-COMBINE
                            )))))

(defthm len-of-group2
  (implies (posp n)
           (equal (len (group2 n list))
                  (floor (len list) n)))
  :hints (("Goal" :in-theory (enable group2))))

(defthm group2-when-n-is-too-large
  (IMPLIES (< (LEN X) N)
           (equal (GROUP2 N X)
                  nil))
  :hints (("Goal" :in-theory (enable GROUP2))))

(defthm nth-of-group2-gen
  (implies (and (natp m)
                (posp n))
           (equal (nth m (group2 n x))
                  (if (< m (floor (len x) n))
                      (firstn n (nthcdr (* m n) x))
                    nil)))
  :hints (("Goal" :in-theory (enable ;LIST::NTH-WITH-LARGE-INDEX
                              NTH-WHEN-<=-LEN
                              ))))

(defthm true-listp-of-group2
  (true-listp (group2 n x)))

(defthm items-have-len-of-group2
  (implies (natp n)
           (equal (items-have-len n (group2 n lst))
                  t))
  :hints (("Goal" :in-theory (enable group2 items-have-len))))

(defthm all-true-listp-of-group2
  (all-true-listp (group2 n lst))
  :hints (("Goal" :in-theory (enable group2 items-have-len))))
