; Conjunctions and disjunctions in Axe
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
(include-book "possibly-negated-nodenums")
(include-book "kestrel/booleans/boolif" :dir :system) ; since we handle boolif specially
(include-book "kestrel/booleans/booland" :dir :system) ; since we handle booland specially
(include-book "kestrel/booleans/boolor" :dir :system) ; since we handle boolor specially
(include-book "tools/flag" :dir :system)
(local (include-book "kestrel/acl2-arrays/acl2-arrays" :dir :system))
(local (include-book "kestrel/booleans/booleans" :dir :system))
(local (include-book "kestrel/lists-light/nth" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))
(local (include-book "kestrel/lists-light/cdr" :dir :system))
(local (include-book "kestrel/arithmetic-light/natp" :dir :system))

(local (in-theory (enable ;NOT-CDDR-OF-NTH-WHEN-DARG-LISTP
;                   not-cddr-when-dag-exprp-and-quotep
                   )))

;(local (in-theory (disable myquotep))) ;todo

(local
 (defthm <-of-+-of-1-when-integers
   (implies (and (syntaxp (not (quotep y)))
                 (integerp x)
                 (integerp y))
            (equal (< x (+ 1 y))
                   (<= x y)))))

(local
 (defthm arith-hack-cheap
  (implies (< x y)
           (not (< y x)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))))

(local
 (defthm <-of-+-of-1-when-integerp
   (implies (and (integerp x)
                 (integerp y))
            (equal (< x (+ 1 y))
                   (<= x y)))))

(defthm car-of-nth-of-dargs-of-aref1
  (implies (and (pseudo-dag-arrayp-aux dag-array-name dag-array nodenum)
                (consp (nth n (dargs (aref1 dag-array-name dag-array nodenum)))) ;the arg is a constant
                (not (equal 'quote (nth 0 (aref1 dag-array-name dag-array nodenum)))) ; the whole expr is not constant
                (< n (len (dargs (aref1 dag-array-name dag-array nodenum))))
                (natp n)
                (natp nodenum)
                )
           (equal (car (nth n (dargs (aref1 dag-array-name dag-array nodenum))))
                  'quote))
  :hints (("Goal" :expand ((pseudo-dag-arrayp-aux dag-array-name dag-array nodenum))
           :in-theory (e/d (pseudo-dag-arrayp-aux car-becomes-nth-of-0
                                                  ;;LIST::LEN-OF-CDR-BETTER
                                                  )
                           (len)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Shows that the representation of disjunctions/conjunctions is not ambiguous.
(defthm possibly-negated-nodenumsp-cannot-be-quotep
  (not (and (possibly-negated-nodenumsp x)
            (quotep x)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable possibly-negated-nodenumsp))))

;items is a list of nodenums and negated nodenums
;only preserves iff?
;todo: rename
(defun negate-possibly-negated-nodenums (items)
  (declare (xargs :guard (possibly-negated-nodenumsp items)
                  :guard-hints (("Goal" :in-theory (enable possibly-negated-nodenumsp
                                                           possibly-negated-nodenump)))))
  (if (endp items)
      nil
    (let ((item (first items)))
      (cons (if (consp item) ;checks for not
                ;strip off the not:
                (farg1 item)
              `(not ,item))
              (negate-possibly-negated-nodenums (rest items))))))

(defthm possibly-negated-nodenumsp-of-negate-possibly-negated-nodenums
  (implies (possibly-negated-nodenumsp items)
           (possibly-negated-nodenumsp (negate-possibly-negated-nodenums items)))
  :hints (("Goal" :in-theory (enable possibly-negated-nodenumsp
                                     possibly-negated-nodenump))))

(defthm bounded-possibly-negated-nodenumsp-of-negate-possibly-negated-nodenums
  (implies (bounded-possibly-negated-nodenumsp items bound)
           (bounded-possibly-negated-nodenumsp (negate-possibly-negated-nodenums items) bound))
  :hints (("Goal" :in-theory (enable bounded-possibly-negated-nodenumsp
                                     bounded-possibly-negated-nodenump))))

;; (defthm all-<-of-strip-nots-from-possibly-negated-nodenums-of-negate-possibly-negated-nodenums
;;   (implies (and (possibly-negated-nodenumsp items)
;;                 (all-< (strip-nots-from-possibly-negated-nodenums items) dag-len)
;;                 )
;;            (all-< (strip-nots-from-possibly-negated-nodenums (negate-possibly-negated-nodenums items)) dag-len))
;;   :hints (("Goal" :in-theory (enable negate-possibly-negated-nodenums strip-nots-from-possibly-negated-nodenums
;;                                      strip-not-from-possibly-negated-nodenum
;;                                      possibly-negated-nodenump))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Either a quoted boolean constant or a non-empty list of possibly-negated-nodenums.
;; Same format as axe-disjunctionp but interpreted differently.
(defund axe-conjunctionp (item)
  (declare (xargs :guard t))
  (or (and (myquotep item)
           (booleanp (unquote item)))
      (and (possibly-negated-nodenumsp item)
           (consp item))))

(defthm axe-conjunctionp-of-singleton
  (implies (natp nodenum)
           (axe-conjunctionp (list nodenum)))
  :hints (("Goal" :in-theory (enable axe-conjunctionp))))

(defthm possibly-negated-nodenumsp-when-axe-conjunctionp
  (implies (axe-conjunctionp x)
           (iff (possibly-negated-nodenumsp x)
                (not (myquotep x))))
  :hints (("Goal" :in-theory (enable axe-conjunctionp
                                     possibly-negated-nodenumsp))))

;; restrict to nth of aref1?
(defthmd axe-conjunctionp-when-myquotep
  (implies (myquotep x)
           (equal (axe-conjunctionp x)
                  (booleanp (unquote x))))
  :hints (("Goal" :in-theory (enable axe-conjunctionp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Either a quoted boolean constant or a non-empty list of possibly-negated-nodenums.
;; Same format as axe-conjunctionp but interpreted differently.
(defund axe-disjunctionp (item)
  (declare (xargs :guard t))
  (or (and (myquotep item)
           (booleanp (unquote item)))
      (and (possibly-negated-nodenumsp item)
           (consp item))))

(defthm axe-disjunctionp-of-singleton
  (implies (natp nodenum)
           (axe-disjunctionp (list nodenum)))
  :hints (("Goal" :in-theory (enable axe-disjunctionp))))

(defthm possibly-negated-nodenumsp-when-axe-disjunctionp
  (implies (axe-disjunctionp x)
           (iff (possibly-negated-nodenumsp x)
                (not (myquotep x))))
  :hints (("Goal" :in-theory (enable axe-disjunctionp
                                     possibly-negated-nodenumsp))))

(defthm axe-disjunctionp-forward-to-true-listp
  (implies (axe-disjunctionp item)
           (true-listp item))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable axe-disjunctionp))))

(defthm axe-disjunctionp-forward-to-consp
  (implies (axe-disjunctionp x)
           (consp x))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable axe-disjunctionp))))

;; restrict to nth of aref1?
(defthmd axe-disjunctionp-when-myquotep
  (implies (myquotep x)
           (equal (axe-disjunctionp x)
                  (booleanp (unquote x))))
  :hints (("Goal" :in-theory (enable axe-disjunctionp))))

(defthmd consp-of-cdr-when-axe-disjunctionp-lemma
  (implies (and (axe-disjunctionp d)
                (equal (car d) 'quote))
           (consp (cdr d)))
  :hints (("Goal" :in-theory (enable axe-disjunctionp possibly-negated-nodenumsp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;TODO: Add 'axe' to some of these names:

;; These are unique (except non-nil constants may differ) because we disallow empty lists of conjuncts/disjuncts:
(defun false-disjunction () (declare (xargs :guard t)) *nil*)
(defun true-disjunction () (declare (xargs :guard t)) *t*)
(defun false-conjunction () (declare (xargs :guard t)) *nil*)
(defun true-conjunction () (declare (xargs :guard t)) *t*)

;; Checks whether X is a true (non-nil) quoted constant.
(defun disjunction-is-truep (x)
  (declare (xargs :guard (axe-disjunctionp x)
                  :guard-hints (("Goal" :in-theory (enable axe-disjunctionp)))))
  (and (quotep x)
       (unquote x)))

(defun disjunction-is-falsep (x)
  (declare (xargs :guard (axe-disjunctionp x)
                  :guard-hints (("Goal" :in-theory (enable axe-disjunctionp)))))
  (equal x (false-disjunction)))

(defthmd axe-disjunctionp-of-false-disjunction (axe-disjunctionp (false-disjunction)))
(defthmd axe-disjunctionp-of-true-disjunction (axe-disjunctionp (true-disjunction)))
(defthmd axe-conjunctionp-of-false-conjunction (axe-conjunctionp (false-conjunction)))
(defthmd axe-conjunctionp-of-true-conjunction (axe-conjunctionp (true-conjunction)))

;only preserves iff?
;item is a quotep or a list of nodenums and negated nodenums
;Returns a conjunction
(defund negate-axe-disjunction (item)
  (declare (xargs :guard (axe-disjunctionp item)
                  :guard-hints (("Goal" :in-theory (enable axe-disjunctionp)))))
  (if (quotep item)
      (if (unquote item)
          *nil*
        *t*)
    (negate-possibly-negated-nodenums item)))

(defthm quotep-of-negate-axe-disjunction
  (implies (axe-disjunctionp item)
           (equal (quotep (negate-axe-disjunction item))
                  (quotep item)))
  :hints (("Goal" :expand (negate-possibly-negated-nodenums item)
           :in-theory (enable negate-axe-disjunction
                              axe-disjunctionp
                              possibly-negated-nodenump))))

(defthm equal-of-quote-nil-and-negate-axe-disjunction
  (implies (axe-disjunctionp item)
           (equal (equal ''nil (negate-axe-disjunction item))
                  (equal ''t item)))
  :hints (("Goal" :expand (negate-possibly-negated-nodenums item)
           :in-theory (enable negate-axe-disjunction axe-disjunctionp))))

(defthm equal-of-quote-t-and-negate-axe-disjunction
  (implies (axe-disjunctionp item)
           (equal (equal ''t (negate-axe-disjunction item))
                  (equal ''nil item)))
  :hints (("Goal" :expand (negate-possibly-negated-nodenums item)
           :in-theory (enable negate-axe-disjunction axe-disjunctionp))))

(defthm axe-conjunctionp-of-negate-axe-disjunction
  (implies (axe-disjunctionp conj)
           (axe-conjunctionp (negate-axe-disjunction conj)))
  :hints (("Goal" :in-theory (enable axe-conjunctionp
                                     axe-disjunctionp
                                     negate-axe-disjunction
                                     possibly-negated-nodenump))))

;Returns a disjunction
(defund negate-axe-conjunction (item)
  (declare (xargs :guard (axe-conjunctionp item)
                  :guard-hints (("Goal" :in-theory (enable axe-conjunctionp)))))
  (if (quotep item)
      (if (unquote item)
          *nil*
        *t*)
    (negate-possibly-negated-nodenums item)))

(defthm axe-disjunctionp-of-negate-axe-conjunction
  (implies (axe-conjunctionp conj)
           (axe-disjunctionp (negate-axe-conjunction conj)))
  :hints (("Goal" :in-theory (enable axe-conjunctionp
                                     axe-disjunctionp
                                     negate-axe-conjunction
                                     possibly-negated-nodenump))))

;; Since it's an axe-disjunction
(defthm consp-of-negate-axe-conjunction
  (implies (axe-conjunctionp conj)
           (consp (negate-axe-conjunction conj)))
  :hints (("Goal" :use (:instance axe-disjunctionp)
           :in-theory (disable axe-disjunctionp))))

(defund bounded-axe-conjunctionp (item bound)
  (declare (xargs :guard (and (axe-conjunctionp item)
                              (natp bound))))
  (if (quotep item)
      t
    (bounded-possibly-negated-nodenumsp item bound)))

(defthm bounded-axe-conjunctionp-of-quote-nil
  (bounded-axe-conjunctionp ''nil bound)
  :hints (("Goal" :in-theory (enable bounded-axe-conjunctionp))))

(defthm bounded-axe-conjunctionp-of-nil
  (bounded-axe-conjunctionp nil bound)
  :hints (("Goal" :in-theory (enable bounded-axe-conjunctionp))))

(defthm bounded-axe-conjunctionp-of-quote-t
  (bounded-axe-conjunctionp ''t bound)
  :hints (("Goal" :in-theory (enable bounded-axe-conjunctionp))))

(defthm bounded-axe-conjunctionp-of-singleton-when-natp
  (implies (natp item)
           (equal (bounded-axe-conjunctionp (list item) bound)
                  (< item bound)))
  :hints (("Goal" :in-theory (enable bounded-axe-conjunctionp))))

(defthm bounded-possibly-negated-nodenumsp-when-bounded-axe-conjunctionp
  (implies (bounded-axe-conjunctionp x bound)
           (iff (bounded-possibly-negated-nodenumsp x bound)
                (not (quotep x))))
  :hints (("Goal" :in-theory (enable bounded-axe-conjunctionp
                                     bounded-possibly-negated-nodenumsp))))

(defthm bounded-axe-conjunctionp-monotone
  (implies (and (bounded-axe-conjunctionp item bound1)
                (<= bound1 bound2)
                (natp bound1)
                (natp bound2))
           (bounded-axe-conjunctionp item bound2))
  :hints (("Goal" :in-theory (enable bounded-axe-conjunctionp))))

;; (defthmd all-<-of-strip-nots-from-possibly-negated-nodenums-when-bounded-axe-conjunctionp
;;   (implies (and (axe-conjunctionp d)
;;                 (bounded-axe-conjunctionp d bound)
;;                 (not (quotep d)))
;;            (all-< (strip-nots-from-possibly-negated-nodenums d) bound))
;;   :hints (("Goal" :in-theory (enable bounded-axe-conjunctionp axe-conjunctionp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund bounded-axe-disjunctionp (item bound)
  (declare (xargs :guard (and (axe-disjunctionp item)
                              (natp bound))))
  (if (quotep item)
      t
    (bounded-possibly-negated-nodenumsp item bound)))

(defthm bounded-axe-disjunctionp-of-quote-t
  (bounded-axe-disjunctionp ''t bound)
  :hints (("Goal" :in-theory (enable bounded-axe-disjunctionp))))

(defthm bounded-axe-disjunctionp-of-quote-nil
  (bounded-axe-disjunctionp ''nil bound)
  :hints (("Goal" :in-theory (enable bounded-axe-disjunctionp))))

(defthm bounded-axe-disjunctionp-of-singleton-when-natp
  (implies (natp item)
           (equal (bounded-axe-disjunctionp (list item) bound)
                  (< item bound)))
  :hints (("Goal" :in-theory (enable bounded-axe-disjunctionp))))

(defthm bounded-axe-conjunctionp-of-negate-axe-disjunction
  (implies (and (axe-disjunctionp item)
                (natp bound)
                (bounded-axe-disjunctionp item bound)
                )
           (bounded-axe-conjunctionp (negate-axe-disjunction item) bound))
  :hints (("Goal" :in-theory (enable negate-axe-disjunction
                                     bounded-axe-conjunctionp
                                     bounded-axe-disjunctionp))))

(defthm bounded-axe-disjunctionp-of-negate-axe-conjunction
  (implies (and (axe-conjunctionp item)
                (natp bound)
                (bounded-axe-conjunctionp item bound)
                )
           (bounded-axe-disjunctionp (negate-axe-conjunction item) bound))
  :hints (("Goal" :in-theory (enable negate-axe-conjunction
                                     bounded-axe-disjunctionp
                                     bounded-axe-conjunctionp))))

(defthm bounded-possibly-negated-nodenumsp-when-bounded-axe-disjunctionp
  (implies (bounded-axe-disjunctionp x bound)
           (iff (bounded-possibly-negated-nodenumsp x bound)
                (not (quotep x))))
  :hints (("Goal" :in-theory (enable bounded-axe-disjunctionp
                                     bounded-possibly-negated-nodenumsp))))

(defthm bounded-axe-disjunctionp-monotone
  (implies (and (bounded-axe-disjunctionp item bound1)
                (<= bound1 bound2)
                (natp bound1)
                (natp bound2))
           (bounded-axe-disjunctionp item bound2))
  :hints (("Goal" :in-theory (enable bounded-axe-disjunctionp))))

;; (defthmd all-<-of-strip-nots-from-possibly-negated-nodenums-when-bounded-axe-disjunctionp
;;   (implies (and (axe-disjunctionp d)
;;                 (bounded-axe-disjunctionp d bound)
;;                 (not (disjunction-is-truep d))
;;                 (not (disjunction-is-falsep d)))
;;            (all-< (strip-nots-from-possibly-negated-nodenums d) bound))
;;   :hints (("Goal" :in-theory (enable bounded-axe-disjunctionp axe-disjunctionp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;x is a list of nodenums and negated nodenums
;y is a list of nodenums and negated nodenums
(defun combine-axe-disjunctions-aux (x y)
  (declare (xargs :guard (and (possibly-negated-nodenumsp x)
                              (possibly-negated-nodenumsp y)
                              (consp y) ;prevents and empty result
                              )
                  :guard-hints (("Goal" :in-theory (enable possibly-negated-nodenumsp
                                                           possibly-negated-nodenump)))))
  (if (endp x)
      y
    (let ((item (first x)))
      (if (consp item)
          ;;item is (not <nodenum>):
          (if (member (farg1 item) y)
              *t*
            (combine-axe-disjunctions-aux (rest x) (cons item y)))
        ;;item is <nodenum>
        (if (member-equal `(not ,item) ;don't build this?
                          y)
            *t*
          (combine-axe-disjunctions-aux (rest x) (cons item y)))))))

(defthm axe-disjunctionp-of-combine-axe-disjunctions-aux
  (implies (and (possibly-negated-nodenumsp x)
                (possibly-negated-nodenumsp y)
                (consp y))
           (axe-disjunctionp (combine-axe-disjunctions-aux x y)))
  :hints (("Goal" :in-theory (enable possibly-negated-nodenumsp axe-disjunctionp))))

(defthm bounded-axe-disjunctionp-of-combine-axe-disjunctions-aux
  (implies (and (possibly-negated-nodenumsp x)
                (possibly-negated-nodenumsp y)
                (bounded-axe-disjunctionp x bound)
                (bounded-axe-disjunctionp y bound))
           (bounded-axe-disjunctionp (combine-axe-disjunctions-aux x y) bound))
  :hints (("Goal" :in-theory (enable combine-axe-disjunctions-aux bounded-axe-disjunctionp))))

;x is a quotep or a list of nodenums and negated nodenums
;y is a quotep or a list of nodenums and negated nodenums
(defund combine-axe-disjunctions (x y)
  (declare (xargs :guard (and (axe-disjunctionp x)
                              (axe-disjunctionp y))
                  :guard-hints (("Goal" :in-theory (enable axe-disjunctionp)))))
  (if (quotep x)
      (if (unquote x)
          *t*
        y)
    (if (quotep y)
        (if (unquote y)
            *t*
          x)
      ;;neither is a quotep:
      (combine-axe-disjunctions-aux x y))))

(defthm axe-disjunctionp-of-combine-axe-disjunctions
  (implies (and (axe-disjunctionp x)
                (axe-disjunctionp y))
           (axe-disjunctionp (combine-axe-disjunctions x y)))
  :hints (("Goal" :in-theory (enable axe-disjunctionp combine-axe-disjunctions))))

(defthm bounded-axe-disjunctionp-of-combine-axe-disjunctions
  (implies (and (axe-disjunctionp x)
                (axe-disjunctionp y)
                (bounded-axe-disjunctionp x bound)
                (bounded-axe-disjunctionp y bound))
           (bounded-axe-disjunctionp (combine-axe-disjunctions x y)
                                     bound))
  :hints (("Goal" :in-theory (enable combine-axe-disjunctions))))

(defthm consp-of-combine-axe-disjunctions
  (implies (and (axe-disjunctionp x)
                (axe-disjunctionp y))
           (consp (combine-axe-disjunctions x y)))
  :hints (("Goal" :in-theory (enable combine-axe-disjunctions axe-disjunctionp possibly-negated-nodenumsp))))

;x is a list of nodenums and negated nodenums
;y is a list of nodenums and negated nodenums
(defun combine-axe-conjunctions-aux (x y)
  (declare (xargs :guard (and (possibly-negated-nodenumsp x)
                              (possibly-negated-nodenumsp y)
                              (consp y) ;prevents an empty result
                              )
                  :guard-hints (("Goal" :in-theory (enable axe-conjunctionp
                                                           possibly-negated-nodenumsp
                                                           possibly-negated-nodenump)))))
  (if (endp x)
      y
    (let ((item (first x)))
      (if (consp item)
          ;;item is (not <nodenum>):
          (if (member (farg1 item) y)
              *nil*
            (combine-axe-conjunctions-aux (rest x) (cons item y)))
        ;;item is <nodenum>
        (if (member-equal `(not ,item) ;don't build this?
                          y)
            *nil*
          (combine-axe-conjunctions-aux (rest x) (cons item y)))))))

;; (defthm axe-conjunctionp-when-possibly-negated-nodenumsp
;;   (implies (possibly-negated-nodenumsp y)
;;            (axe-conjunctionp y))
;;   :hints (("Goal" :in-theory (enable conjunction-or-disjunctionp))))

(defthm axe-conjunctionp-of-combine-axe-conjunctions-aux
  (implies (and (possibly-negated-nodenumsp x)
                (possibly-negated-nodenumsp y)
                (consp y))
           (axe-conjunctionp (combine-axe-conjunctions-aux x y)))
  :hints (("Goal" :in-theory (enable possibly-negated-nodenumsp axe-conjunctionp))))

(defthm bounded-axe-conjunctionp-of-combine-axe-conjunctions-aux
  (implies (and (possibly-negated-nodenumsp x)
                (possibly-negated-nodenumsp y)
                (bounded-axe-conjunctionp x bound)
                (bounded-axe-conjunctionp y bound))
           (bounded-axe-conjunctionp (combine-axe-conjunctions-aux x y)
                                     bound))
  :hints (("Goal" :in-theory (enable combine-axe-conjunctions-aux bounded-axe-conjunctionp))))


;x is a quotep or a list of nodenums and negated nodenums
;y is a quotep or a list of nodenums and negated nodenums
(defund combine-axe-conjunctions (x y)
  (declare (xargs :guard (and (axe-conjunctionp x)
                              (axe-conjunctionp y))
                  :guard-hints (("Goal" :in-theory (enable axe-conjunctionp
                                                           true-listp-when-possibly-negated-nodenumsp)))))
  (if (quotep x)
      (if (unquote x)
          y
        *nil*)
    (if (quotep y)
        (if (unquote y)
            x
          *nil*)
      ;;neither is a quotep:
      (combine-axe-conjunctions-aux x y))))

(defthm axe-conjunctionp-of-combine-axe-conjunctions
  (implies (and (axe-conjunctionp x)
                (axe-conjunctionp y))
           (axe-conjunctionp (combine-axe-conjunctions x y)))
  :hints (("Goal" :in-theory (enable combine-axe-conjunctions
                                     axe-conjunctionp))))

(defthm bounded-axe-conjunctionp-of-combine-axe-conjunctions
  (implies (and (axe-conjunctionp x)
                (axe-conjunctionp y)
                (bounded-axe-conjunctionp x bound)
                (bounded-axe-conjunctionp y bound))
           (bounded-axe-conjunctionp (combine-axe-conjunctions x y)
                                     bound))
  :hints (("Goal" :in-theory (enable combine-axe-conjunctions))))

(local
 ;; used to justify the operation of get-axe-conjunction-from-dag-item below
 (defthmd boolif-of-nil-arg3
   (iff (boolif x y 'nil)
        (booland x y))))

(local
 ;; used to justify the operation of get-axe-conjunction-from-dag-item below
 (defthmd if-of-nil-arg3
   (iff (if x y 'nil)
        (booland x y))
   :hints (("Goal" :in-theory (enable booland)))))

(local
 ;; used to justify the operation of get-axe-conjunction-from-dag-item below
 (defthmd myif-of-nil-arg3
   (iff (myif x y 'nil)
        (booland x y))
   :hints (("Goal" :in-theory (enable booland)))))

(local
 ;; used to justify the operation of get-axe-disjunction-from-dag-item below
 (defthmd boolif-of-t-arg2
   (iff (boolif x 't y)
        (boolor x y))))

(local
 ;; used to justify the operation of get-axe-disjunction-from-dag-item below
 (defthmd if-of-t-arg2
   (iff (if x 't y)
        (boolor x y))))

(local
 ;; used to justify the operation of get-axe-disjunction-from-dag-item below
 (defthmd myif-of-t-arg2
   (iff (myif x 't y)
        (boolor x y))
   :hints (("Goal" :in-theory (enable boolor)))))

(local
 ;; used to justify the operation of get-axe-disjunction-from-dag-item below
 (defthmd if-of-t-arg3
   (iff (if x y 't)
        (boolor (not x) y))))

(local
 ;; used to justify the operation of get-axe-conjunction-from-dag-item below
 (defthmd if-of-nil-arg2
   (iff (if x 'nil y)
        (booland (not x) y))))

;; (defthm if-becomes-or-iff
;;   (iff (if x x y)
;;        (boolor x y)))

;; Constants are the smallest, followed by nodenums in order
(defund dag-item-measure (item)
  (declare (xargs :guard (or (myquotep item)
                             (natp item))))
  (if (consp item)
      0
    (+ 1 (nfix item))))

(defthm o-p-of-dag-item-measure
  (o-p (dag-item-measure item))
  :hints (("Goal" :in-theory (enable dag-item-measure))))

;move
(defthm <-of-dag-item-measure-nth-of-dargs-of-aref1-when-pseudo-dag-arrayp-aux
  (implies (and (pseudo-dag-arrayp-aux dag-array-name dag-array nodenum)
                (< n
                   (len (dargs (aref1 dag-array-name dag-array nodenum))))
                (natp nodenum)
                (natp n)
                (not (equal 'quote
                            (car (aref1 dag-array-name dag-array nodenum)))))
           (< (dag-item-measure (nth n (dargs (aref1 dag-array-name dag-array nodenum))))
              (dag-item-measure nodenum)))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable dag-item-measure car-becomes-nth-of-0)
           :expand ((pseudo-dag-arrayp-aux dag-array-name dag-array nodenum)))))

(defthm <-of-dag-item-measure-nth-of-dargs-of-aref1-when-pseudo-dag-arrayp
  (implies (and (pseudo-dag-arrayp dag-array-name dag-array (+ 1 nodenum))
                (< n
                   (len (dargs (aref1 dag-array-name dag-array nodenum))))
                (natp nodenum)
                (natp n)
                (not (equal 'quote
                            (car (aref1 dag-array-name dag-array nodenum)))))
           (< (dag-item-measure (nth n (dargs (aref1 dag-array-name dag-array nodenum))))
              (dag-item-measure nodenum)))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable pseudo-dag-arrayp))))

(defthmd consp-of-nth-when-ALL-MYQUOTEP-of-cdr
  (implies (and (ALL-MYQUOTEP (CDR items))
                (posp n)
                (< n (len items)))
           (consp (nth n items)))
  :hints (("Goal" :in-theory (e/d (nth ALL-MYQUOTEP)
                                  (NTH-OF-CDR)))))

;; (defthm consp-of-nth-of-aref1-of-0
;;   (implies (and (PSEUDO-DAG-ARRAYP-AUX DAG-ARRAY-NAME DAG-ARRAY 0)
;;                 (not (equal (nth 0 (AREF1 DAG-ARRAY-NAME DAG-ARRAY 0))
;;                             'quote))
;;                 (< n (len (dargs (AREF1 DAG-ARRAY-NAME DAG-ARRAY 0))))
;;                 (natp n))
;;            (consp (nth n (dargs (AREF1 DAG-ARRAY-NAME DAG-ARRAY 0)))))
;;   :hints (("Goal" :expand (PSEUDO-DAG-ARRAYP-AUX DAG-ARRAY-NAME DAG-ARRAY 0)
;;            :in-theory (e/d (PSEUDO-DAG-ARRAYP-AUX ;nth
;;                             ) (;NTH-OF-CDR
;;                                )))))

(defthm not-consp-of-nth-of-dargs-of-aref1
  (implies (and (pseudo-dag-arrayp-aux dag-array-name dag-array nodenum)
                (not (EQUAL 'QUOTE (CAR (AREF1 DAG-ARRAY-NAME DAG-ARRAY NODENUM))))
                ;; means it must be a nodenum
                (not (equal (car (nth n (dargs (aref1 dag-array-name dag-array nodenum))))
                            'quote))
        ;        (< n (len (dargs (aref1 dag-array-name dag-array nodenum))))
                (natp n)
                (natp nodenum)
                )
           (not (consp (nth n (dargs (aref1 dag-array-name dag-array nodenum))))))
  :hints (("Goal" :expand (pseudo-dag-arrayp-aux dag-array-name dag-array nodenum)
           :use (:instance BOUNDED-DAG-EXPRP-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP-AUX (m nodenum)
                           (n nodenum))
           :in-theory (e/d ( ;pseudo-dag-arrayp-aux nth
                            )
                           (;nth-of-cdr
                            BOUNDED-DAG-EXPRP-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP-AUX)))))

;move
;may loop if myquotep is enabled
;; (defthm consp-of-nth-of-aref1-strengthen
;;   (implies (and (syntaxp (want-to-strengthen (consp (nth n (aref1 dag-array-name dag-array nodenum)))))
;;                 (posp n)
;;                 (pseudo-dag-arrayp-aux dag-array-name dag-array nodenum2) ;nodenum2 is a free var
;;                 ;; the whole expr is not a function call:
;;                 (not (equal 'quote (car (aref1 dag-array-name dag-array nodenum))))
;;                 (<= nodenum nodenum2)
;;                 (natp nodenum)
;;                 (natp nodenum2))
;;            (equal (consp (nth n (aref1 dag-array-name dag-array nodenum)))
;;                   (quotep (nth n (aref1 dag-array-name dag-array nodenum)))
;;                   ;;(myquotep (nth n (aref1 dag-array-name dag-array nodenum)))))
;;                   ))
;;   :hints (("Goal" ;:expand (pseudo-dag-arrayp-aux dag-array-name dag-array nodenum)
;;            :use (:instance bounded-dag-exprp-of-aref1-when-pseudo-dag-arrayp-aux (m nodenum)
;;                            (n nodenum2))
;;            :in-theory (e/d ( ;pseudo-dag-arrayp-aux nth
;;                             )
;;                            (nth-of-cdr
;;                             bounded-darg-listp-of-dargs-of-aref1
;;                             bounded-dag-exprp-of-aref1-when-pseudo-dag-arrayp-aux-helper
;;                             quote-lemma-for-bounded-darg-listp-gen-alt
;;                             bounded-dag-exprp-of-aref1-when-pseudo-dag-arrayp-aux)))))

;; (defthm consp-of-nth-of-aref1-weaken
;;   (implies (and (syntaxp (want-to-strengthen (consp (nth n (aref1 dag-array-name dag-array nodenum)))))
;;                 (posp n)
;;                 (< n (len (fargs (aref1 dag-array-name dag-array nodenum))))
;;                 (pseudo-dag-arrayp-aux dag-array-name dag-array nodenum2) ;nodenum2 is a free var
;;                 ;; the whole expr is not a function call:
;;                 (not (equal 'quote (car (aref1 dag-array-name dag-array nodenum))))
;;                 ;; the whole expr is not a variable:
;;                 (consp (aref1 dag-array-name dag-array nodenum))
;;                 (<= nodenum nodenum2)
;;                 (natp nodenum)
;;                 (natp nodenum2))
;;            (equal (myquotep (nth n (aref1 dag-array-name dag-array nodenum)))
;;                   (not (natp (nth n (aref1 dag-array-name dag-array nodenum))))))
;;   :hints (("Goal" ;:expand (pseudo-dag-arrayp-aux dag-array-name dag-array nodenum)
;;            :use (:instance bounded-dag-exprp-of-aref1-when-pseudo-dag-arrayp-aux (m nodenum)
;;                            (n nodenum2))
;;            :in-theory (e/d ( ;pseudo-dag-arrayp-aux nth
;;                             myquotep
;;                             )
;;                            (nth-of-cdr
;;                             NONNEG-OF-NTH-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP-AUX
;;                             BOUNDED-DARG-LISTP-OF-DARGS-OF-AREF1
;;                             BOUNDED-DAG-EXPRP-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP-AUX-HELPER
;;                             QUOTE-LEMMA-FOR-BOUNDED-DARG-LISTP-GEN-ALT
;;                             BOUNDED-DAG-EXPRP-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP-AUX)))))

(defund bool-fix-constant (x)
  (declare (xargs :guard (myquotep x)))
  (if (or (equal x *t*)
          (equal x *nil*))
      x
    (if (unquote x)
        *t*
      *nil*)))

(defthmd booleanp-of-unquote-of-bool-fix-constant
  (booleanp (unquote (bool-fix-constant x)))
  :hints (("Goal" :in-theory (enable bool-fix-constant))))

(defthmd quotep-of-bool-fix-constant
  (quotep (bool-fix-constant x))
  :hints (("Goal" :in-theory (enable bool-fix-constant))))

(local
 (defthm axe-disjunctionp-of-bool-fix-constant
   (axe-disjunctionp (bool-fix-constant x))
   :hints (("Goal" :in-theory (enable bool-fix-constant)))))

(local
 (defthm axe-conjunctionp-of-bool-fix-constant
   (axe-conjunctionp (bool-fix-constant x))
   :hints (("Goal" :in-theory (enable bool-fix-constant)))))

(local
 (defthm bounded-axe-disjunctionp-of-bool-fix-constant
   (bounded-axe-disjunctionp (bool-fix-constant x) bound)
   :hints (("Goal" :in-theory (enable bool-fix-constant)))))

(local
 (defthm bounded-axe-conjunctionp-of-bool-fix-constant
   (bounded-axe-conjunctionp (bool-fix-constant x) bound)
   :hints (("Goal" :in-theory (enable bool-fix-constant)))))

;; These only preserve boolean-equivalence (that is, equivalence under iff).
;; TODO: Can we avoid checking the arities?
;; TODO: Handle (if x x y).
(mutual-recursion
 ;; Returns an axe-disjunctionp that is boolean-equivalent to NODENUM-OR-QUOTEP.
 (defun get-axe-disjunction-from-dag-item (nodenum-or-quotep dag-array-name dag-array dag-len)
   (declare (xargs :guard (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                               (dargp-less-than nodenum-or-quotep dag-len))
                   :ruler-extenders :all
                   :verify-guards nil ;done below
                   :measure (dag-item-measure nodenum-or-quotep)))
   (if (consp nodenum-or-quotep) ;checks for quotep
       (bool-fix-constant nodenum-or-quotep)
     ;;it's a nodenum:
     (let ((expr (aref1 dag-array-name dag-array nodenum-or-quotep)))
       (if (variablep expr)
           (list nodenum-or-quotep)
         (let ((fn (ffn-symb expr)))
           (if (eq 'quote fn)
               (bool-fix-constant expr)
             (if (and (eq 'boolor fn)
                      (= 2 (len (dargs expr))) ;(consp (cdr (dargs expr))) ;todo: here and elsewhere, put back these potentially faster tests
                      )
                 (and (mbt (< (dag-item-measure (darg1 expr)) (dag-item-measure nodenum-or-quotep)))
                      (mbt (< (dag-item-measure (darg2 expr)) (dag-item-measure nodenum-or-quotep)))
                      (combine-axe-disjunctions (get-axe-disjunction-from-dag-item (darg1 expr) dag-array-name dag-array dag-len)
                                                (get-axe-disjunction-from-dag-item (darg2 expr) dag-array-name dag-array dag-len)))
               (if (and (or (eq 'boolif fn)
                            (eq 'myif fn)
                            (eq 'if fn))
                        (= 3 (len (dargs expr))) ;(consp (cdr (cdr (dargs expr))))
                        )
                   ;; (if <x> 't <y>) is like (or <x> <y>)
                   (if (equal *t* (darg2 expr)) ;can it ever be the nodenum of a constant?  maybe not if this is all done on the second rewrite..
                       (and (mbt (< (dag-item-measure (darg1 expr)) (dag-item-measure nodenum-or-quotep)))
                            (mbt (< (dag-item-measure (darg3 expr)) (dag-item-measure nodenum-or-quotep)))
                            (combine-axe-disjunctions (get-axe-disjunction-from-dag-item (darg1 expr) dag-array-name dag-array dag-len)
                                                      (get-axe-disjunction-from-dag-item (darg3 expr) dag-array-name dag-array dag-len)))
                     ;; (if <x> <y> 't) is like (or (not <x>) <y>)
                     (if (equal *t* (darg3 expr)) ;can it ever be the nodenum of a constant?  maybe not if this is all done on the second rewrite..
                         (and (mbt (< (dag-item-measure (darg1 expr)) (dag-item-measure nodenum-or-quotep)))
                              (mbt (< (dag-item-measure (darg2 expr)) (dag-item-measure nodenum-or-quotep)))
                              (combine-axe-disjunctions (negate-axe-conjunction (get-axe-conjunction-from-dag-item (darg1 expr) dag-array-name dag-array dag-len))
                                                        (get-axe-disjunction-from-dag-item (darg2 expr) dag-array-name dag-array dag-len)))
                       (list nodenum-or-quotep)))
                 (if (and (eq 'not fn)
                          (= 1 (len (dargs expr))))
                     (and (mbt (< (dag-item-measure (darg1 expr)) (dag-item-measure nodenum-or-quotep)))
                          (negate-axe-conjunction (get-axe-conjunction-from-dag-item (darg1 expr) dag-array-name dag-array dag-len)))
                   (list nodenum-or-quotep))))))))))

 ;; Returns an axe-conjunctionp that is boolean-equivalent to NODENUM-OR-QUOTEP.
 (defun get-axe-conjunction-from-dag-item (nodenum-or-quotep dag-array-name dag-array dag-len)
   (declare (xargs :guard (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                               (dargp-less-than nodenum-or-quotep dag-len))
                   :ruler-extenders :all
                   :measure (dag-item-measure nodenum-or-quotep)))
   (if (consp nodenum-or-quotep) ;checks for quotep
       (bool-fix-constant nodenum-or-quotep)
     ;;it's a nodenum:
     (let ((expr (aref1 dag-array-name dag-array nodenum-or-quotep)))
       (if (variablep expr)
           (list nodenum-or-quotep)
         (let ((fn (ffn-symb expr)))
           (if (eq 'quote fn)
               (bool-fix-constant expr)
             (if (and (eq 'booland fn)
                      (equal 2 (len (dargs expr))) ;(consp (cdr (dargs expr)))
                      )
                 (and (mbt (< (dag-item-measure (darg1 expr)) (dag-item-measure nodenum-or-quotep)))
                      (mbt (< (dag-item-measure (darg2 expr)) (dag-item-measure nodenum-or-quotep)))
                      (combine-axe-conjunctions (get-axe-conjunction-from-dag-item (darg1 expr) dag-array-name dag-array dag-len)
                                                (get-axe-conjunction-from-dag-item (darg2 expr) dag-array-name dag-array dag-len)))
               (if (and (or (eq 'boolif fn)
                            (eq 'myif fn)
                            (eq 'if fn))
                        (equal 3 (len (dargs expr))) ;(consp (cdr (cdr (dargs expr))))
                        )
                   ;; (if <x> <y> 'nil) is like (and <x> <y>)
                   (if (equal *nil* (darg3 expr)) ;can it ever be the nodenum of a constant?  maybe not if this is all done on the second rewrite..
                       (and (mbt (< (dag-item-measure (darg1 expr)) (dag-item-measure nodenum-or-quotep)))
                            (mbt (< (dag-item-measure (darg2 expr)) (dag-item-measure nodenum-or-quotep)))
                            (combine-axe-conjunctions (get-axe-conjunction-from-dag-item (darg1 expr) dag-array-name dag-array dag-len)
                                                      (get-axe-conjunction-from-dag-item (darg2 expr) dag-array-name dag-array dag-len)))
                     ;; (if <x> 'nil <y>) is like (and (not <x>) <y>)
                     (if (equal *nil* (darg2 expr)) ;can it ever be the nodenum of a constant?  maybe not if this is all done on the second rewrite..
                         (and (mbt (< (dag-item-measure (darg1 expr)) (dag-item-measure nodenum-or-quotep)))
                              (mbt (< (dag-item-measure (darg3 expr)) (dag-item-measure nodenum-or-quotep)))
                              (combine-axe-conjunctions (negate-axe-disjunction (get-axe-disjunction-from-dag-item (darg1 expr) dag-array-name dag-array dag-len))
                                                        (get-axe-conjunction-from-dag-item (darg3 expr) dag-array-name dag-array dag-len)))
                       (list nodenum-or-quotep)))
                 (if (and (eq 'not fn)
                          (= 1 (len (dargs expr))))
                     (and (mbt (< (dag-item-measure (darg1 expr)) (dag-item-measure nodenum-or-quotep)))
                          (negate-axe-disjunction (get-axe-disjunction-from-dag-item (darg1 expr) dag-array-name dag-array dag-len)))
                   (list nodenum-or-quotep)))))))))))

(make-flag get-axe-disjunction-from-dag-item)

(defthm-flag-get-axe-disjunction-from-dag-item
  (defthm axe-disjunctionp-of-get-axe-disjunction-from-dag-item
    (implies (and (dargp-less-than nodenum-or-quotep dag-len)
                  (pseudo-dag-arrayp dag-array-name dag-array dag-len))
             (axe-disjunctionp (get-axe-disjunction-from-dag-item nodenum-or-quotep dag-array-name dag-array dag-len)))
    :flag get-axe-disjunction-from-dag-item)
  (defthm axe-conjunctionp-of-get-axe-conjunction-from-dag-item
    (implies (and (dargp-less-than nodenum-or-quotep dag-len)
                  (pseudo-dag-arrayp dag-array-name dag-array dag-len))
             (axe-conjunctionp (get-axe-conjunction-from-dag-item nodenum-or-quotep dag-array-name dag-array dag-len)))
    :flag get-axe-conjunction-from-dag-item)
  :hints (("Goal" :in-theory (enable car-becomes-nth-of-0))))

(defthm true-listp-of-get-axe-disjunction-from-dag-item
  (implies (and (dargp-less-than nodenum-or-quotep dag-len)
                (pseudo-dag-arrayp dag-array-name dag-array dag-len))
           (true-listp (get-axe-disjunction-from-dag-item nodenum-or-quotep dag-array-name dag-array dag-len)))
  :hints (("Goal" :use (:instance axe-disjunctionp-of-get-axe-disjunction-from-dag-item)
           :in-theory (disable axe-disjunctionp-of-get-axe-disjunction-from-dag-item))))

(verify-guards get-axe-disjunction-from-dag-item
  :hints (("Goal" :in-theory (enable car-becomes-nth-of-0))))

(defthm-flag-get-axe-disjunction-from-dag-item
  (defthm bounded-axe-disjunctionp-of-get-axe-disjunction-from-dag-item
    (implies (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                  (dargp-less-than nodenum-or-quotep dag-len)
                  (dargp-less-than nodenum-or-quotep bound)
                  (natp bound))
             (bounded-axe-disjunctionp (get-axe-disjunction-from-dag-item nodenum-or-quotep dag-array-name dag-array dag-len) bound))
    :flag get-axe-disjunction-from-dag-item)
  (defthm bounded-axe-conjunctionp-of-get-axe-conjunction-from-dag-item
    (implies (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                  (dargp-less-than nodenum-or-quotep dag-len)
                  (dargp-less-than nodenum-or-quotep bound)
                  (natp bound))
             (bounded-axe-conjunctionp (get-axe-conjunction-from-dag-item nodenum-or-quotep dag-array-name dag-array dag-len) bound))
    :flag get-axe-conjunction-from-dag-item)
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (car-becomes-nth-of-0
                            NATP-OF-+-OF-1)
                           (myquotep quotep DARGP-LESS-THAN)))))

(defthm consp-of-get-axe-disjunction-from-dag-item
  (implies (and (dargp-less-than nodenum-or-quotep dag-len)
                (pseudo-dag-arrayp dag-array-name dag-array dag-len))
           (consp (get-axe-disjunction-from-dag-item nodenum-or-quotep dag-array-name dag-array dag-len)))
  :hints (("Goal" :use (:instance axe-disjunctionp-of-get-axe-disjunction-from-dag-item)
           :in-theory (disable axe-disjunctionp-of-get-axe-disjunction-from-dag-item))))

(defthm consp-of-get-axe-conjunction-from-dag-item
  (implies (and (dargp-less-than nodenum-or-quotep dag-len)
                (pseudo-dag-arrayp dag-array-name dag-array dag-len))
           (consp (get-axe-conjunction-from-dag-item nodenum-or-quotep dag-array-name dag-array dag-len)))
  :hints (("Goal" :use (:instance axe-conjunctionp-of-get-axe-conjunction-from-dag-item)
           :in-theory (disable axe-conjunctionp-of-get-axe-conjunction-from-dag-item))))

;; (defthm all-<-of-strip-nots-from-possibly-negated-nodenums-of-get-axe-conjunction-from-dag-item
;;   (implies (and (not (equal (car (get-axe-conjunction-from-dag-item nodenum 'dag-array dag-array dag-len))
;;                             'quote))
;;                 (< nodenum dag-len)
;;                 (natp nodenum)
;;                 (pseudo-dag-arrayp 'dag-array dag-array dag-len))
;;            (all-< (strip-nots-from-possibly-negated-nodenums (get-axe-conjunction-from-dag-item nodenum 'dag-array dag-array dag-len))
;;                   dag-len))
;;   :hints (("goal" :use (:instance bounded-axe-conjunctionp-of-get-axe-conjunction-from-dag-item
;;                                   (nodenum-or-quotep nodenum)
;;                                   (dag-array-name 'dag-array))
;;            :in-theory (e/d (bounded-axe-conjunctionp) (bounded-axe-conjunctionp-of-get-axe-conjunction-from-dag-item)))))

(defthm bounded-possibly-negated-nodenumsp-of-get-axe-conjunction-from-dag-item
  (implies (and (not (equal (car (get-axe-conjunction-from-dag-item nodenum 'dag-array dag-array dag-len))
                            'quote))
                (< nodenum dag-len)
                (natp nodenum)
                (pseudo-dag-arrayp 'dag-array dag-array dag-len))
           (bounded-possibly-negated-nodenumsp (get-axe-conjunction-from-dag-item nodenum 'dag-array dag-array dag-len) dag-len))
  :hints (("goal" :use (:instance bounded-axe-conjunctionp-of-get-axe-conjunction-from-dag-item
                                  (nodenum-or-quotep nodenum)
                                  (dag-array-name 'dag-array)
                                  (bound dag-len))
           :in-theory (e/d (bounded-axe-conjunctionp) (bounded-axe-conjunctionp-of-get-axe-conjunction-from-dag-item)))))

;; (defthm all-<-of-strip-nots-from-possibly-negated-nodenums-of-get-axe-disjunction-from-dag-item
;;   (implies (and (not (equal (car (get-axe-disjunction-from-dag-item nodenum 'dag-array dag-array dag-len))
;;                             'quote))
;;                 (< nodenum dag-len)
;;                 (natp nodenum)
;;                 (pseudo-dag-arrayp 'dag-array dag-array dag-len))
;;            (all-< (strip-nots-from-possibly-negated-nodenums (get-axe-disjunction-from-dag-item nodenum 'dag-array dag-array dag-len))
;;                   dag-len))
;;   :hints (("goal" :use (:instance bounded-axe-disjunctionp-of-get-axe-disjunction-from-dag-item
;;                                   (nodenum-or-quotep nodenum)
;;                                   (dag-array-name 'dag-array))
;;            :in-theory (e/d (bounded-axe-disjunctionp) (bounded-axe-disjunctionp-of-get-axe-disjunction-from-dag-item)))))

(defthm bounded-possibly-negated-nodenumsp-of-get-axe-disjunction-from-dag-item
  (implies (and (not (equal (car (get-axe-disjunction-from-dag-item nodenum 'dag-array dag-array dag-len))
                            'quote))
                (< nodenum dag-len)
                (natp nodenum)
                (pseudo-dag-arrayp 'dag-array dag-array dag-len))
           (bounded-possibly-negated-nodenumsp (get-axe-disjunction-from-dag-item nodenum 'dag-array dag-array dag-len) dag-len))
  :hints (("goal" :use (:instance bounded-axe-disjunctionp-of-get-axe-disjunction-from-dag-item
                                  (nodenum-or-quotep nodenum)
                                  (dag-array-name 'dag-array)
                                  (bound dag-len))
           :in-theory (e/d (bounded-axe-disjunctionp) (bounded-axe-disjunctionp-of-get-axe-disjunction-from-dag-item)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;move
(defthmd dargp-less-than-of-cadr-of-car-when-bounded-possibly-negated-nodenumsp
  (implies (bounded-possibly-negated-nodenumsp items dag-len)
           (equal (dargp-less-than (car (cdr (car items))) dag-len)
                  (consp (car items))))
  :hints (("Goal" :in-theory (enable bounded-possibly-negated-nodenumsp
                                     bounded-possibly-negated-nodenump))))

;; Returns an axe-disjunction that is boolean-equivalent to the disjunction of the ITEMS.
(defund get-axe-disjunction-from-dag-items (items dag-array-name dag-array dag-len)
  (declare (xargs :guard (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (bounded-possibly-negated-nodenumsp items dag-len))
                  :verify-guards nil ;done below
                  ))
  (if (endp items)
      (false-disjunction) ;; the disjunction of no things is false
    (let* ((item (first items))
           (disjunction (if (consp item) ; item is (not <nodenum>):
                            (negate-axe-conjunction (get-axe-conjunction-from-dag-item (farg1 item) dag-array-name dag-array dag-len))
                          ;; item is a nodenum:
                          (get-axe-disjunction-from-dag-item item dag-array-name dag-array dag-len))))
      (if (and (quotep disjunction)
               (unquote disjunction))
          (true-disjunction)                  ; true or x = true
        (combine-axe-disjunctions disjunction ; might be 'nil
                                  (get-axe-disjunction-from-dag-items (rest items)
                                                                      dag-array-name dag-array dag-len))))))

(defthm axe-disjunctionp-of-get-axe-disjunction-from-dag-items
  (implies (and (bounded-possibly-negated-nodenumsp items dag-len)
                (pseudo-dag-arrayp dag-array-name dag-array dag-len))
           (axe-disjunctionp (get-axe-disjunction-from-dag-items items dag-array-name dag-array dag-len)))
  :hints (("Goal" :in-theory (enable get-axe-disjunction-from-dag-items
                                     dargp-less-than-of-cadr-of-car-when-bounded-possibly-negated-nodenumsp))))

;; Since an axe-disjunction is always a cons
(defthm consp-of-get-axe-disjunction-from-dag-items
  (implies (and (bounded-possibly-negated-nodenumsp items dag-len)
                (pseudo-dag-arrayp dag-array-name dag-array dag-len))
           (consp (get-axe-disjunction-from-dag-items items dag-array-name dag-array dag-len)))
  :hints (("Goal" :use (:instance axe-disjunctionp-of-get-axe-disjunction-from-dag-items)
           :in-theory (disable axe-disjunctionp-of-get-axe-disjunction-from-dag-items))))

(verify-guards get-axe-disjunction-from-dag-items
  :hints (("Goal" :in-theory (enable consp-of-cdr-when-axe-disjunctionp-lemma
                                     dargp-less-than-of-cadr-of-car-when-bounded-possibly-negated-nodenumsp
                                     bounded-possibly-negated-nodenumsp
                                     bounded-possibly-negated-nodenump))))

(defthm bounded-axe-disjunctionp-of-get-axe-disjunction-from-dag-items
  (implies (and (bounded-possibly-negated-nodenumsp items dag-len)
                (pseudo-dag-arrayp dag-array-name dag-array dag-len))
           (bounded-axe-disjunctionp (get-axe-disjunction-from-dag-items items dag-array-name dag-array dag-len)
                                     dag-len))
  :hints (("Goal" :in-theory (e/d (get-axe-disjunction-from-dag-items
                                   dargp-less-than-of-cadr-of-car-when-bounded-possibly-negated-nodenumsp)
                                  (disjunction-is-falsep
                                   disjunction-is-truep
                                   dargp-less-than)))))
