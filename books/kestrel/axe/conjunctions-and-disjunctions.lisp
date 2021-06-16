; Conjunctions and disjunctions in Axe
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

(include-book "kestrel/utilities/forms" :dir :system) ;for call-of
(include-book "dag-arrays")
(include-book "kestrel/booleans/boolif" :dir :system) ; since we handle boolif specially
(include-book "kestrel/booleans/booland" :dir :system) ; since we handle booland specially
(include-book "kestrel/booleans/boolor" :dir :system) ; since we handle boolor specially
(include-book "tools/flag" :dir :system)
(include-book "kestrel/utilities/polarity" :dir :system) ;for want-to-weaken
(local (include-book "kestrel/booleans/booleans" :dir :system))
(local (include-book "kestrel/lists-light/nth" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))
(local (include-book "kestrel/lists-light/cdr" :dir :system))

;(local (in-theory (disable list::nth-with-large-index-2))) ;for speed

(local (in-theory (enable ;NOT-CDDR-OF-NTH-WHEN-ALL-DARGP
;                   not-cddr-when-dag-exprp0-and-quotep
                   )))

;(local (in-theory (disable myquotep))) ;todo

; an item of the form <nodenum> or (not <nodenum>).
(defund possibly-negated-nodenump (item)
  (declare (xargs :guard t))
  (or (natp item)
      (and (call-of 'not item)
           (true-listp item)
           (eql 1 (len (fargs item))) ;(consp (cdr item))
           (natp (farg1 item)))))

(defund strip-not-from-possibly-negated-nodenum (item)
  (declare (xargs :guard (possibly-negated-nodenump item)
                  :guard-hints (("Goal" :in-theory (enable possibly-negated-nodenump)))))
  (if (consp item)
      (farg1 item)
    item))

(defthm natp-of-strip-not-from-possibly-negated-nodenum
  (implies (possibly-negated-nodenump item)
           (natp (strip-not-from-possibly-negated-nodenum item)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable strip-not-from-possibly-negated-nodenum
                                     possibly-negated-nodenump))))

(defthm rationalp-of-strip-not-from-possibly-negated-nodenum
  (implies (possibly-negated-nodenump item)
           (rationalp (strip-not-from-possibly-negated-nodenum item)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable strip-not-from-possibly-negated-nodenum))))

(defthm strip-not-from-possibly-negated-nodenum-when-not-consp
  (implies (not (consp item))
           (equal (strip-not-from-possibly-negated-nodenum item)
                  item))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable strip-not-from-possibly-negated-nodenum))))

(defund possibly-negated-nodenumsp (lst)
  (declare (xargs :guard t))
  (if (atom lst)
      (null lst) ;new
    (and (possibly-negated-nodenump (first lst))
         (possibly-negated-nodenumsp (rest lst)))))

(defthm possibly-negated-nodenumsp-of-cons
  (equal (possibly-negated-nodenumsp (cons item list))
         (and (possibly-negated-nodenump item)
              (possibly-negated-nodenumsp list)))
  :hints (("Goal" :in-theory (enable possibly-negated-nodenumsp))))

(defthm possibly-negated-nodenumsp-of-cdr-2
  (implies (possibly-negated-nodenump (car predicates-or-negations))
           (equal (possibly-negated-nodenumsp (cdr predicates-or-negations))
                  (possibly-negated-nodenumsp predicates-or-negations))))

(defthm true-listp-when-possibly-negated-nodenumsp
  (implies (possibly-negated-nodenumsp context)
           (true-listp context))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable possibly-negated-nodenumsp))))

;should we use a defforall?
(defthm possibly-negated-nodenumsp-forward-to-true-listp
  (implies (possibly-negated-nodenumsp items)
           (true-listp items))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable possibly-negated-nodenumsp))))

;; Shows that the representation of disjunctions/conjunctions is not ambiguous.
(defthm possibly-negated-nodenumsp-cannot-be-quotep
  (not (and (possibly-negated-nodenumsp x)
            (quotep x)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable possibly-negated-nodenumsp))))

(defthm possibly-negated-nodenumsp-of-add-to-set-equal
  (implies (and (possibly-negated-nodenump item)
                (possibly-negated-nodenumsp context))
           (possibly-negated-nodenumsp (add-to-set-equal item context)))
  :hints (("Goal" :in-theory (enable add-to-set-equal possibly-negated-nodenumsp))))

(defthm possibly-negated-nodenumsp-of-singleton
  (implies (natp nodenum)
           (possibly-negated-nodenumsp (list nodenum)))
  :hints (("Goal" :in-theory (enable possibly-negated-nodenumsp
                                     possibly-negated-nodenump))))


(defthm possibly-negated-nodenumsp-of-cdr
  (implies (possibly-negated-nodenumsp items)
           (possibly-negated-nodenumsp (cdr items)))
  :hints (("Goal" :in-theory (enable possibly-negated-nodenumsp))))

(defthm integerp-of-car-when-possibly-negated-nodenumsp-weaken-cheap
  (implies (and (syntaxp (want-to-weaken (integerp (car items))))
                (possibly-negated-nodenumsp items)
                (consp items))
           (equal (integerp (car items))
                  (or (not (consp (car items)))
                      (not (eq 'not (car (car items))))
                      (not (natp (farg1 (car items))))
                      (cdr (fargs (car items))))))
  :rule-classes ((:rewrite :backchain-limit-lst (nil 0 nil)))
  :hints (("Goal" :in-theory (enable possibly-negated-nodenumsp
                                     possibly-negated-nodenump))))

(defthm consp-of-car-when-possibly-negated-nodenumsp-weaken-cheap
  (implies (and (syntaxp (want-to-weaken (consp (car items))))
                (possibly-negated-nodenumsp items)
                (consp items))
           (equal (consp (car items))
                  (not (natp (car items)))))
  :rule-classes ((:rewrite :backchain-limit-lst (nil 0 nil)))
  :hints (("Goal" :in-theory (enable possibly-negated-nodenumsp
                                     possibly-negated-nodenump))))

;;;
;;; strip-nots-from-possibly-negated-nodenums
;;;

(defund strip-nots-from-possibly-negated-nodenums (items)
  (declare (xargs :guard (possibly-negated-nodenumsp items)
                  :guard-hints (("Goal" :expand (possibly-negated-nodenumsp items)))))
  (if (endp items)
      nil
    (cons (strip-not-from-possibly-negated-nodenum (first items))
          (strip-nots-from-possibly-negated-nodenums (rest items)))))

(defthm rational-listp-of-strip-nots-from-possibly-negated-nodenums
  (implies (possibly-negated-nodenumsp items)
           (rational-listp (strip-nots-from-possibly-negated-nodenums items)))
  :hints (("Goal" :in-theory (enable strip-nots-from-possibly-negated-nodenums
                                     possibly-negated-nodenumsp))))

(defthm nat-listp-of-strip-nots-from-possibly-negated-nodenums
  (implies (possibly-negated-nodenumsp items)
           (nat-listp (strip-nots-from-possibly-negated-nodenums items)))
  :hints (("Goal" :in-theory (enable strip-nots-from-possibly-negated-nodenums
                                     possibly-negated-nodenumsp))))

(defthm consp-of-strip-nots-from-possibly-negated-nodenums
  (equal (consp (strip-nots-from-possibly-negated-nodenums items))
         (consp items))
  :hints (("Goal" :in-theory (enable strip-nots-from-possibly-negated-nodenums))))

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

(defthm all-<-of-strip-nots-from-possibly-negated-nodenums-of-negate-possibly-negated-nodenums
  (implies (and (possibly-negated-nodenumsp items)
                (all-< (strip-nots-from-possibly-negated-nodenums items) dag-len)
                )
           (all-< (strip-nots-from-possibly-negated-nodenums (negate-possibly-negated-nodenums items)) dag-len))
  :hints (("Goal" :in-theory (enable negate-possibly-negated-nodenums strip-nots-from-possibly-negated-nodenums
                                     strip-not-from-possibly-negated-nodenum
                                     possibly-negated-nodenump))))

;;;
;;; axe-conjunctionp
;;;

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

;;;
;;; axe-disjunctionp
;;;

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

;;TODO: Add 'axe' to some of these names:

;; These are unique (except non-nil constants may differ) because we disallow empty lists of conjuncts/disjuncts:
(defun false-disjunction () (declare (xargs :guard t)) *nil*)
(defun true-disjunction () (declare (xargs :guard t)) *t*)
(defun false-conjunction () (declare (xargs :guard t)) *nil*)
(defun true-conjunction () (declare (xargs :guard t)) *t*)

;; The quotation of a something other than nil
;; todo: restruct to the quotation of t?
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

(defund bounded-axe-conjunctionp (item dag-len)
  (declare (xargs :guard (and (axe-conjunctionp item)
                              (natp dag-len))))
  (if (quotep item)
      t
    (all-< (strip-nots-from-possibly-negated-nodenums item) dag-len)))

(defthm bounded-axe-conjunctionp-of-quote-nil
  (bounded-axe-conjunctionp ''nil dag-len)
  :hints (("Goal" :in-theory (enable bounded-axe-conjunctionp))))

(defthm bounded-axe-conjunctionp-of-nil
  (bounded-axe-conjunctionp nil dag-len)
  :hints (("Goal" :in-theory (enable bounded-axe-conjunctionp))))

(defthm bounded-axe-conjunctionp-of-quote-t
  (bounded-axe-conjunctionp ''t dag-len)
  :hints (("Goal" :in-theory (enable bounded-axe-conjunctionp))))

(defthm bounded-axe-conjunctionp-of-singleton-when-natp
  (implies (natp item)
           (equal (bounded-axe-conjunctionp (list item) dag-len)
                  (< item dag-len)))
  :hints (("Goal" :in-theory (enable bounded-axe-conjunctionp
                                     strip-nots-from-possibly-negated-nodenums))))

(defund bounded-axe-disjunctionp (item dag-len)
  (declare (xargs :guard (and (axe-disjunctionp item)
                              (natp dag-len))))
  (if (quotep item)
      t
    (all-< (strip-nots-from-possibly-negated-nodenums item) dag-len)))

(defthm bounded-axe-disjunctionp-of-quote-t
  (bounded-axe-disjunctionp ''t dag-len)
  :hints (("Goal" :in-theory (enable bounded-axe-disjunctionp))))

(defthm bounded-axe-disjunctionp-of-quote-nil
  (bounded-axe-disjunctionp ''nil dag-len)
  :hints (("Goal" :in-theory (enable bounded-axe-disjunctionp))))

(defthm bounded-axe-disjunctionp-of-singleton-when-natp
  (implies (natp item)
           (equal (bounded-axe-disjunctionp (list item) dag-len)
                  (< item dag-len)))
  :hints (("Goal" :in-theory (enable bounded-axe-disjunctionp
                                     strip-nots-from-possibly-negated-nodenums))))

(defthm bounded-axe-conjunctionp-of-negate-axe-disjunction
  (implies (and (axe-disjunctionp item)
                (natp dag-len)
                (bounded-axe-disjunctionp item dag-len)
                )
           (bounded-axe-conjunctionp (negate-axe-disjunction item) dag-len))
  :hints (("Goal" :in-theory (enable negate-axe-disjunction
                                     bounded-axe-conjunctionp
                                     bounded-axe-disjunctionp))))

(defthm bounded-axe-disjunctionp-of-negate-axe-conjunction
  (implies (and (axe-conjunctionp item)
                (natp dag-len)
                (bounded-axe-conjunctionp item dag-len)
                )
           (bounded-axe-disjunctionp (negate-axe-conjunction item) dag-len))
  :hints (("Goal" :in-theory (enable negate-axe-conjunction
                                     bounded-axe-disjunctionp
                                     bounded-axe-conjunctionp))))

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
                (bounded-axe-disjunctionp x dag-len)
                (bounded-axe-disjunctionp y dag-len))
           (bounded-axe-disjunctionp (combine-axe-disjunctions-aux x y) dag-len))
  :hints (("Goal" :in-theory (enable combine-axe-disjunctions-aux strip-nots-from-possibly-negated-nodenums bounded-axe-disjunctionp))))

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
                (bounded-axe-disjunctionp x dag-len)
                (bounded-axe-disjunctionp y dag-len))
           (bounded-axe-disjunctionp (combine-axe-disjunctions x y)
                                     dag-len))
  :hints (("Goal" :in-theory (enable combine-axe-disjunctions))))


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
                (bounded-axe-conjunctionp x dag-len)
                (bounded-axe-conjunctionp y dag-len))
           (bounded-axe-conjunctionp (combine-axe-conjunctions-aux x y)
                                     dag-len))
  :hints (("Goal" :in-theory (enable combine-axe-conjunctions-aux strip-nots-from-possibly-negated-nodenums bounded-axe-conjunctionp))))


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
                (bounded-axe-conjunctionp x dag-len)
                (bounded-axe-conjunctionp y dag-len))
           (bounded-axe-conjunctionp (combine-axe-conjunctions x y)
                                     dag-len))
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
;;                             all-dargp-less-than-of-dargs-of-aref1
;;                             bounded-dag-exprp-of-aref1-when-pseudo-dag-arrayp-aux-helper
;;                             quote-lemma-for-all-dargp-less-than-gen-alt
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
;;                             ALL-DARGP-LESS-THAN-OF-DARGS-OF-AREF1
;;                             BOUNDED-DAG-EXPRP-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP-AUX-HELPER
;;                             QUOTE-LEMMA-FOR-ALL-DARGP-LESS-THAN-GEN-ALT
;;                             BOUNDED-DAG-EXPRP-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP-AUX)))))

(defun bool-fix-constant (x)
  (declare (xargs :guard (myquotep x)))
  (if (or (equal x *t*)
          (equal x *nil*))
      x
    (if (unquote x)
        *t*
      *nil*)))

(defthm booleanp-of-unquote-of-bool-fix-constant
  (booleanp (unquote (bool-fix-constant x))))

;; These only preserve boolean-equivalence (that is, equivalence under iff).
;; TODO: Can we avoid checking the arities?
;; TODO: Handle (if x x y).
(mutual-recursion
 ;; Returns an axe-disjunctionp that is boolean-equivalent to NODENUM-OR-QUOTEP.
 (defun get-axe-disjunction-from-dag-item (nodenum-or-quotep dag-array-name dag-array dag-len)
   (declare (xargs :ruler-extenders :all
                   :verify-guards nil ;done below
                   :guard (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                               (dargp-less-than nodenum-or-quotep dag-len))
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
   (declare (xargs :ruler-extenders :all
                   :guard (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                               (dargp-less-than nodenum-or-quotep dag-len))
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

;; (PSEUDO-DAG-ARRAYP DAG-ARRAY-NAME DAG-ARRAY
;;                                       (NTH 3
;;                                            (AREF1 DAG-ARRAY-NAME
;;                                                   DAG-ARRAY NODENUM-OR-QUOTEP)))

(defthm arith-hack-cheap
  (implies (< x y)
           (not (< y x)))
  :rule-classes ((:rewrite :backchain-limit-lst (0))))

;slow!
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
  :hints (("Goal" :expand ((AXE-CONJUNCTIONP NODENUM-OR-QUOTEP)
                           (AXE-DISJUNCTIONP NODENUM-OR-QUOTEP)
                           (AXE-CONJUNCTIONP (AREF1 DAG-ARRAY-NAME
                                                    DAG-ARRAY NODENUM-OR-QUOTEP))
                           (AXE-DISJUNCTIONP (AREF1 DAG-ARRAY-NAME
                                                    DAG-ARRAY NODENUM-OR-QUOTEP)))
           :in-theory (e/d (CAR-BECOMES-NTH-OF-0
                            ;cadr-becomes-nth-of-1
                            ;CONSP-FROM-LEN
                            ;CONSP-CDR
                            ;;consp-to-len-bound
;                            LIST::LEN-OF-CDR-BETTER
                            ;DAG-ITEM-MEASURE ;todo
                            )
                           (;LIST::NTH-WITH-LARGE-INDEX
                            ;len LIST::LEN-POS-REWRITE LIST::LEN-WHEN-AT-MOST-1
                                                       ;;LIST::LEN-EQUAL-0-REWRITE
;try me: pseudo-dag-arrayp
                                                       ;CONS-EQUAL-REWRITE-CONSTANT-VERSION
                            )))))

(defthm true-listp-of-get-axe-disjunction-from-dag-item
  (implies (and (dargp-less-than nodenum-or-quotep dag-len)
                (pseudo-dag-arrayp dag-array-name dag-array dag-len))
           (true-listp (get-axe-disjunction-from-dag-item nodenum-or-quotep dag-array-name dag-array dag-len)))
  :hints (("Goal" :use (:instance axe-disjunctionp-of-get-axe-disjunction-from-dag-item)
           :in-theory (disable axe-disjunctionp-of-get-axe-disjunction-from-dag-item))))

;; restrict to nth of aref1?
(defthmd axe-disjunctionp-when-myquotep
  (implies (myquotep x)
           (equal (axe-disjunctionp x)
                  (booleanp (unquote x))))
  :hints (("Goal" :in-theory (enable axe-disjunctionp))))

(defthmd axe-conjunctionp-when-myquotep
  (implies (myquotep x)
           (equal (axe-conjunctionp x)
                  (booleanp (unquote x))))
  :hints (("Goal" :in-theory (enable axe-conjunctionp))))

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

(defthm axe-conjunctionp-of-nth-of-dargs-of-aref1
  (implies  (and (consp (nth n (dargs (aref1 dag-array-name dag-array nodenum)))) ;means it's a constant
                 (pseudo-dag-arrayp-aux dag-array-name dag-array nodenum)
                 (< n (len (dargs (aref1 dag-array-name dag-array nodenum))))
                 (natp n)
                 (not (equal 'quote (nth 0 (aref1 dag-array-name dag-array nodenum))))
                 (natp nodenum)
                 (not (consp (nth n (dargs (aref1 dag-array-name dag-array nodenum))))) ;todo?
                 )
            (axe-conjunctionp (nth n (dargs (aref1 dag-array-name dag-array nodenum)))))
  :hints (("Goal" :in-theory (e/d (axe-conjunctionp car-of-nth-of-dargs-of-aref1 nth) (nth-of-cdr)))))

(defthm axe-disjunctionp-of-nth-of-dargs-of-aref1
  (implies  (and (consp (nth n (dargs (aref1 dag-array-name dag-array nodenum)))) ;means it's a constant
                 (pseudo-dag-arrayp-aux dag-array-name dag-array nodenum)
                 (< n (len (dargs (aref1 dag-array-name dag-array nodenum))))
                 (natp n)
                 (not (equal 'quote (nth 0 (aref1 dag-array-name dag-array nodenum))))
                 (natp nodenum)
                 (not (consp (nth n (dargs (aref1 dag-array-name dag-array nodenum))))) ;todo?
                 )
            (axe-disjunctionp (nth n (dargs (aref1 dag-array-name dag-array nodenum)))))
  :hints (("Goal" :in-theory (e/d (axe-disjunctionp car-of-nth-of-dargs-of-aref1 nth) (nth-of-cdr
                                                                              )))))

(verify-guards get-axe-disjunction-from-dag-item
  :hints (("Goal" :in-theory (e/d (CAR-BECOMES-NTH-OF-0 ;CONSP-FROM-LEN
                                                ;CONSP-CDR
                                                ;;consp-to-len-bound
                                   ;;LIST::LEN-OF-CDR-BETTER
                                                ;DAG-ITEM-MEASURE
                                                )
                                  (;LIST::NTH-WITH-LARGE-INDEX
                                   len ;LIST::LEN-POS-REWRITE LIST::LEN-WHEN-AT-MOST-1
                                       ;;LIST::LEN-EQUAL-0-REWRITE
                                   )))))

(defthm dargp-less-than-when-not-consp-cheap
  (implies (not (consp item))
           (equal (dargp-less-than item len)
                  (and (natp item)
                       (< item len))))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable dargp-less-than))))

(local
 (defthm <-of-+-of-1-when-integerp
   (implies (and (integerp x)
                 (integerp y))
            (equal (< x (+ 1 y))
                   (<= x y)))))

(defthm-flag-get-axe-disjunction-from-dag-item
  (defthm bounded-axe-disjunctionp-of-get-axe-disjunction-from-dag-item
    (implies (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                  (dargp-less-than nodenum-or-quotep dag-len))
             (bounded-axe-disjunctionp (get-axe-disjunction-from-dag-item nodenum-or-quotep dag-array-name dag-array dag-len) dag-len))
    :flag get-axe-disjunction-from-dag-item)
  (defthm bounded-axe-conjunctionp-of-get-axe-conjunction-from-dag-item
    (implies (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                  (dargp-less-than nodenum-or-quotep dag-len))
             (bounded-axe-conjunctionp (get-axe-conjunction-from-dag-item nodenum-or-quotep dag-array-name dag-array dag-len) dag-len))
    :flag get-axe-conjunction-from-dag-item)
  :hints (("Goal" :expand ((axe-conjunctionp nodenum-or-quotep)
                           (axe-disjunctionp nodenum-or-quotep)
                           (axe-conjunctionp (aref1 dag-array-name
                                                    dag-array nodenum-or-quotep))
                           (axe-disjunctionp (aref1 dag-array-name
                                                    dag-array nodenum-or-quotep)))
           :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (car-becomes-nth-of-0
                            NATP-OF-+-OF-1
                            STRIP-NOTS-FROM-POSSIBLY-NEGATED-NODENUMS)
                           (myquotep quotep DARGP-LESS-THAN)))))

; need a flag proof?
;; (thm
;;  (implies (or (myquotep nodenum-or-quotep)
;;               (and (natp nodenum-or-quotep)
;;                    (pseudo-dag-arrayp dag-array-name dag-array (+ 1 nodenum-or-quotep))))
;;           (ALL-< (STRIP-NOTS-FROM-POSSIBLY-NEGATED-NODENUMS (GET-AXE-DISJUNCTION-FROM-DAG-ITEM nodenum-or-quotep dag-array-name dag-array))
;;                  DAG-LEN))
;;  :hints (("Goal" :in-theory (enable STRIP-NOTS-FROM-POSSIBLY-NEGATED-NODENUMS))))

;;returns an axe-disjunctionp equivalent in the sense of IFF to the disjunction of nodenums-or-quoteps.
;; todo: use this instead of handle-constant-disjuncts?
(defund get-axe-disjunction-from-dag-items (nodenums-or-quoteps dag-array-name dag-array dag-len)
  (declare (xargs :guard (and (true-listp nodenums-or-quoteps)
                              (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (all-dargp-less-than nodenums-or-quoteps dag-len)
                              )
                  :verify-guards nil ;done below
                  ))
  (if (endp nodenums-or-quoteps)
      (false-disjunction) ;; the disjunction of no things is false
    (let ((nodenum-or-quotep (first nodenums-or-quoteps)))
      (if (consp nodenum-or-quotep)
          ;; it's a quotep:
          (if (unquote nodenum-or-quotep)
              (true-disjunction) ;; "true or something" is true
            ;;skip the nil: "false or x" is equivalent to x
            (get-axe-disjunction-from-dag-items (rest nodenums-or-quoteps) dag-array-name dag-array dag-len))
        ;; it's a nodenum:
        (let ((disjunction (get-axe-disjunction-from-dag-item nodenum-or-quotep dag-array-name dag-array dag-len)))
          (if (and (quotep disjunction)
                   (unquote disjunction))
              (true-disjunction)
            (combine-axe-disjunctions disjunction ;might be 'nil
                                      (get-axe-disjunction-from-dag-items (rest nodenums-or-quoteps)
                                                                          dag-array-name dag-array dag-len))))))))


(local
 (defthm <-of-+-of-1-when-integers
   (implies (and (syntaxp (not (quotep y)))
                 (integerp x)
                 (integerp y))
            (equal (< x (+ 1 y))
                   (<= x y)))))

(defthm axe-disjunctionp-forward-to-consp
  (implies (axe-disjunctionp x)
           (consp x))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable axe-disjunctionp))))

(defthm consp-of-combine-axe-disjunctions
  (implies (and (axe-disjunctionp x)
                (axe-disjunctionp y)
                )
           (consp (combine-axe-disjunctions x y)))
  :hints (("Goal" :in-theory (enable combine-axe-disjunctions AXE-DISJUNCTIONP POSSIBLY-NEGATED-NODENUMSP))))

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

(defthm axe-disjunctionp-of-get-axe-disjunction-from-dag-items
  (implies (and (all-dargp-less-than nodenum-or-quoteps dag-len)
                (pseudo-dag-arrayp dag-array-name dag-array dag-len))
           (axe-disjunctionp (get-axe-disjunction-from-dag-items nodenum-or-quoteps dag-array-name dag-array dag-len)))
  :hints (("Goal" :in-theory (enable get-axe-disjunction-from-dag-item ;AXE-DISJUNCTIONP
                                     get-axe-disjunction-from-dag-items
                                     ))))

(defthmd consp-of-cdr-when-axe-disjunctionp-lemma
  (implies (and (axe-disjunctionp d)
                (equal (car d) 'quote))
           (consp (cdr d)))
  :hints (("Goal" :in-theory (enable axe-disjunctionp POSSIBLY-NEGATED-NODENUMSP))))

(verify-guards get-axe-disjunction-from-dag-items
  :hints (("Goal" :in-theory (enable consp-of-cdr-when-axe-disjunctionp-lemma))))

(defthm bounded-axe-disjunctionp-of-get-axe-disjunction-from-dag-items
  (implies (and (all-dargp-less-than disjuncts dag-len)
                (pseudo-dag-arrayp dag-array-name dag-array dag-len))
           (bounded-axe-disjunctionp (get-axe-disjunction-from-dag-items disjuncts dag-array-name dag-array dag-len)
                                     dag-len))
  :hints (("Goal" :in-theory (e/d (get-axe-disjunction-from-dag-items)
                                  (disjunction-is-falsep
                                   disjunction-is-truep
                                   dargp-less-than)))))

(defthmd all-<-of-strip-nots-from-possibly-negated-nodenums-when-bounded-axe-disjunctionp
 (implies (and (axe-disjunctionp d)
               (bounded-axe-disjunctionp d dag-len)
               (not (disjunction-is-truep d))
               (not (disjunction-is-falsep d)))
          (all-< (strip-nots-from-possibly-negated-nodenums d) dag-len))
 :hints (("Goal" :in-theory (enable bounded-axe-disjunctionp AXE-DISJUNCTIONP ))))
