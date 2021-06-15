; Computing contexts from overarching DAG nodes
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "conjunctions-and-disjunctions")
(include-book "dag-parent-array-with-name")
(include-book "kestrel/acl2-arrays/typed-acl2-arrays" :dir :system)
(include-book "rational-lists")
(include-book "kestrel/bv/bvif" :dir :system) ;since this book deals with bvif specially
(local (include-book "kestrel/lists-light/nth" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "numeric-lists"))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))

;for speed:
(local (in-theory (disable nth-when-<=-len-cheap
                           ;;nth-with-large-index-cheap
                           ;list::nth-when-l-is-not-a-consp
                           nth-when-zp-cheap
                           nth-when-not-consp-cheap
                           nth-when-not-cddr
                           not-consp-of-nth-of-dargs-of-aref1
                           ;;consp-when-len-equal
                           ;;list::nth-when-n-is-not-an-integerp
                           )))

(local (in-theory (disable possibly-negated-nodenump)))

(defthm possibly-negated-nodenump-of-list-of-not
  (equal (possibly-negated-nodenump (list 'not nodenum))
         (natp nodenum))
  :hints (("Goal" :in-theory (enable possibly-negated-nodenump))))

(defthm possibly-negated-nodenump-when-natp
  (implies (natp nodenum)
           (possibly-negated-nodenump nodenum))
  :hints (("Goal" :in-theory (enable possibly-negated-nodenump))))

;we'll use consp as the normal form
(defthmd cdr-iff-when-possibly-negated-nodenump
  (implies (possibly-negated-nodenump item)
           (iff (cdr item)
                (consp item)))
  :hints (("Goal" :in-theory (enable possibly-negated-nodenump))))

;we'll use consp as the normal form
(defthmd consp-of-cdr-when-possibly-negated-nodenump
  (implies (possibly-negated-nodenump item)
           (equal (consp (cdr item))
                  (consp item)))
  :hints (("Goal" :in-theory (enable possibly-negated-nodenump))))

(defthm possibly-negated-nodenump-of-car
  (implies (possibly-negated-nodenumsp items)
           (equal (possibly-negated-nodenump (car items))
                  (consp items)))
  :hints (("Goal" :in-theory (enable possibly-negated-nodenumsp))))

;;
;; contexts
;;

;use these more!
(defmacro true-context () nil) ;a conjunction of no things is taken to be true
(defmacro false-context () :false)

(defmacro false-contextp (item)
  `(eq (false-context) ,item))

(defund contextp (context)
  (declare (xargs :guard t))
  (or (eq (false-context) context)
      ;;a non-false context is a list of conjuncts of the form <nodenum> or (not <nodenum>)
      ;;the meaning of a context is the conjunction of its items
      ;;a context of nil represents "true" (the conjunction of no things)
      ;;fixme, for efficiency, we could separate the lists of true and false things...
      (possibly-negated-nodenumsp context)))

;requires 0 <= nodenum < bound for all the nodenums in the context:
(defun possibly-negated-nodenumsp-with-bound (lst bound)
  (declare (type rational bound))
  (if (atom lst)
      (null lst) ;new
    (let ((item (first lst)))
      (and (or (and (natp item)
                    (< item bound))
               (and (call-of 'not item)
                    (consp (cdr item))
                    (null (cddr item))
                    (natp (farg1 item))
                    (< (farg1 item) bound)))
           (possibly-negated-nodenumsp-with-bound (rest lst) bound)))))

(defthm possibly-negated-nodenumsp-when-possibly-negated-nodenumsp-with-bound
  (implies (possibly-negated-nodenumsp-with-bound lst bound)
           (possibly-negated-nodenumsp lst))
  :hints (("Goal" :in-theory (enable possibly-negated-nodenumsp
                                     possibly-negated-nodenumsp-with-bound))))


(defund contextp-with-bound (context bound)
  (declare (type rational bound))
  (or (eq (false-context) context)
      (possibly-negated-nodenumsp-with-bound context bound)))

(defthm contextp-with-bound-monotone
  (implies (and (contextp-with-bound context bound1)
                (<= bound1 bound)
                (natp bound1)
                (natp bound))
           (contextp-with-bound context bound))
  :hints (("Goal" :in-theory (enable contextp-with-bound))))

(defthm contextp-when-contextp-with-bound
  (implies (contextp-with-bound context bound)
           (contextp context))
  :hints (("Goal" :in-theory (enable contextp-with-bound contextp))))

(defthm contextp-with-bound-forward-to-context
  (implies (contextp-with-bound context bound)
           (contextp context))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable contextp-with-bound contextp))))

;;;
;;; max-nodenum-in-possibly-negated-nodenums-aux
;;;

(defund max-nodenum-in-possibly-negated-nodenums-aux (items acc)
  (declare (xargs :guard (and (rationalp acc)
                              (possibly-negated-nodenumsp items))
                  :guard-hints (("Goal" :in-theory (enable possibly-negated-nodenumsp
                                                           possibly-negated-nodenump)))))
  (if (endp items)
      acc
    (let ((item (first items)))
      (max-nodenum-in-possibly-negated-nodenums-aux (rest items)
                                                    (max acc
                                                         (if (consp item) ;tests for not
                                                             (farg1 item)
                                                           item))))))

(defthm integerp-of-max-nodenum-in-possibly-negated-nodenums-aux
  (implies (and (possibly-negated-nodenumsp items)
                (integerp acc))
           (integerp (max-nodenum-in-possibly-negated-nodenums-aux items acc)))
  :hints (("Goal" :in-theory (enable max-nodenum-in-possibly-negated-nodenums-aux
                                     possibly-negated-nodenumsp
                                     possibly-negated-nodenump))))

(defthm <=-of-max-nodenum-in-possibly-negated-nodenums-aux-linear
  (implies (and (possibly-negated-nodenumsp items)
                (integerp acc))
           (<= acc (max-nodenum-in-possibly-negated-nodenums-aux items acc)))
  :rule-classes :linear
  :hints (("Goal" :expand ((possibly-negated-nodenump (car items))
                           (possibly-negated-nodenumsp items))
           :do-not '(generalize eliminate-destructors)
           :in-theory (enable max-nodenum-in-possibly-negated-nodenums-aux))))

(defthm <-of-max-nodenum-in-possibly-negated-nodenums-aux-when-possibly-negated-nodenumsp-with-bound
  (implies (and (possibly-negated-nodenumsp-with-bound context bound)
                (natp bound)
                (< acc bound))
           (< (max-nodenum-in-possibly-negated-nodenums-aux context acc) bound))
  :hints (("Goal" :in-theory (enable max-nodenum-in-possibly-negated-nodenums-aux
                                     possibly-negated-nodenumsp-with-bound))))

;;;
;;; max-nodenum-in-possibly-negated-nodenums
;;;

;returns -1 if there are no nodenums
(defund max-nodenum-in-possibly-negated-nodenums (items)
  (declare (xargs :guard (possibly-negated-nodenumsp items)
                  :guard-hints (("Goal" :in-theory (enable possibly-negated-nodenumsp)))))
  (max-nodenum-in-possibly-negated-nodenums-aux items -1))

(defthm integerp-of-max-nodenum-in-possibly-negated-nodenums
  (implies (possibly-negated-nodenumsp items)
           (integerp (max-nodenum-in-possibly-negated-nodenums items)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable max-nodenum-in-possibly-negated-nodenums))))

(defthm <=-of-max-nodenum-in-possibly-negated-nodenums-linear
  (implies (possibly-negated-nodenumsp items)
           (<= -1 (max-nodenum-in-possibly-negated-nodenums items)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable max-nodenum-in-possibly-negated-nodenums))))

(defthm <-of-max-nodenum-in-possibly-negated-nodenums-when-possibly-negated-nodenumsp-with-bound
  (implies (and (possibly-negated-nodenumsp-with-bound context bound)
                (natp bound))
           (< (max-nodenum-in-possibly-negated-nodenums context) bound))
  :hints (("Goal" :in-theory (enable max-nodenum-in-possibly-negated-nodenums))))

;;;
;;; max-nodenum-in-context
;;;

;returns -1 if no nodenums are mentioned
(defund max-nodenum-in-context (context)
  (declare (xargs :guard (contextp context)))
  (if (false-contextp context)
      -1
    (max-nodenum-in-possibly-negated-nodenums context)))

(defthm integerp-of-max-nodenum-in-context
  (implies (contextp context)
           (integerp (max-nodenum-in-context context)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable max-nodenum-in-context))))

(defthm <-of-max-nodenum-in-context-linear
  (implies (contextp context)
           (<= -1 (max-nodenum-in-context context)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable max-nodenum-in-context))))

(defthm <-of-max-nodenum-in-context-when-possibly-negated-nodenumsp-with-bound
  (implies (and (contextp-with-bound context bound)
                (natp bound))
           (< (max-nodenum-in-context context) bound))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable max-nodenum-in-context
                                     contextp-with-bound))))

;; (thm
;;  (implies (contextp context)
;;           (equal (equal -1 (MAX-NODENUM-IN-CONTEXT context))
;;                  (false-contextp context)))
;;  :hints (("Goal" :in-theory (enable MAX-NODENUM-IN-CONTEXT))))

;strips off the nots
;each element of CONTEXT is <integer> or (not <integer>)
;could make tail rec
(defun get-nodenums-mentioned-in-possibly-negated-nodenums (context)
  (declare (xargs :guard (and ;(true-listp context)
                          (possibly-negated-nodenumsp context))
                  :guard-hints (("Goal" :in-theory (enable possibly-negated-nodenumsp
                                                           possibly-negated-nodenump)))))
  (if (endp context)
      nil
    (cons (let ((item (first context)))
            (if (consp item) ;checks for a call of not
                (farg1 item)
              item))
          (get-nodenums-mentioned-in-possibly-negated-nodenums (rest context)))))

(defun get-nodenums-mentioned-in-context (context)
  (if (false-contextp context)
      nil
    (get-nodenums-mentioned-in-possibly-negated-nodenums context)))

(local (in-theory (enable possibly-negated-nodenumsp))) ;todo

;checks for contradictions:
(defun conjoin-contexts-aux (context1 context2)
  (declare (xargs :guard (and (possibly-negated-nodenumsp context1)
                              (possibly-negated-nodenumsp context2))
                  :guard-hints (("Goal" :in-theory (enable possibly-negated-nodenump)))))
  (if (endp context1)
      context2
    (let ((item (first context1)))
      (if (consp item) ;item is (not <nodenum>):
          (if (member (farg1 item) context2)
              (false-context)
            (conjoin-contexts-aux (rest context1) (add-to-set-equal item context2)))
        ;item is <nodenum>:
        (if (member-equal `(not ,item) context2) ;fixme save this cons?
            (false-context)
          (conjoin-contexts-aux (rest context1) (add-to-set-equal item context2)))))))

(defthm contextp-of-conjoin-contexts-aux
  (implies (and (possibly-negated-nodenumsp context1)
                (possibly-negated-nodenumsp context2))
           (contextp (conjoin-contexts-aux context1 context2)))
  :hints (("Goal" :in-theory (enable conjoin-contexts-aux))))

;this is inexact (doesn't look inside the nodenums in the context)
(defund conjoin-contexts (context1 context2)
  (declare (xargs :guard (and (contextp context1)
                              (contextp context2))))
  (if (or (eq (false-context) context1) ;use *false-context* for speed? ;fixme actually use false-contextp here and below?
          (eq (false-context) context2))
      (false-context)
    ;;both are lists of nodenums and negated nodenums:
    (conjoin-contexts-aux context1 context2)
    ;;    (union-equal context1 context2)
    ))

(defthm contextp-of-conjoin-contexts
  (implies (and (contextp context1)
                (contextp context2))
           (contextp (conjoin-contexts context1 context2)))
  :hints (("Goal" :in-theory (enable conjoin-contexts))))

;inline?
;this is inexact in two ways (doesn't look inside the nodenums in the context, also can't express the disjunction of two conjunctions as a single conjunction)
;the second type of loss of information has the flavor of the convex hull operations done when generating polyhedral invariants using the abstract interpretation framework.

(defund disjoin-contexts (context1 context2)
  (declare (xargs :guard (and (contextp context1)
                              (contextp context2))))
  (if (eq (false-context) context1)
      context2
    (if (eq (false-context) context2)
        context1
      (intersection-equal context1 context2))))

(defthm possibly-negated-nodenumsp-of-intersection-equal
  (implies (and (possibly-negated-nodenumsp context1)
                (possibly-negated-nodenumsp context2))
           (possibly-negated-nodenumsp (intersection-equal context1 context2))))

(defthm contextp-of-disjoin-contexts
  (implies (and (contextp context1)
                (contextp context2))
           (contextp (disjoin-contexts context1 context2)))
  :hints (("Goal" :in-theory (enable disjoin-contexts CONTEXTP))))


;; ;allow us to pass in a quotep?
;; ;fixme what if the expr at nodenum-to-negate is a not?  should have a rule to just reverse the if (but will rules have been applied? what if substitution put in the not?)
;; (defund negate-and-conjoin-to-context (nodenum-to-negate context dag-array-name dag-array)
;;   (declare (xargs :guard (and (natp nodenum-to-negate)
;;                               (true-listp context)
;;                               (array1p dag-array-name dag-array)
;;                               (< nodenum-to-negate
;;                                  (alen1 dag-array-name dag-array)))))
;;   (if (eq (false-context) context)
;;       (false-context)
;;     (if (member nodenum-to-negate context)
;;         (false-context)
;;       (let ((expr (aref1 dag-array-name dag-array nodenum-to-negate)))
;;         (if (myquotep expr)
;;             (if (unquote expr)
;;                 ;;we are negating a non-nil constant and conjoining it in (that is, we are anding with nil):
;;                 (false-context)
;;               ;; we are negating the constant nil and conjoining it in:
;;               context)
;;           ;;ffffffixme extract disjuncts from the nodenum-to-negate and add their negations...
;;           (add-to-set-equal `(not ,nodenum-to-negate) context))))))

;; (defthm contextp-of-negate-and-conjoin-to-context
;;   (implies (and (integerp nodenum-to-negate)
;;                 (contextp context))
;;            (contextp (negate-and-conjoin-to-context nodenum-to-negate context dag-array-name dag-array)))
;;   :hints (("Goal" :in-theory (enable negate-and-conjoin-to-context))))



;; ;combine the functions using a flag argument before proving this?
;; (thm
;;  (and (conjunction-or-disjunctionp (get-conjunction nodenum-or-quotep dag-array-name dag-array))
;;       (conjunction-or-disjunctionp (get-disjunction nodenum-or-quotep2 dag-array-name2 dag-array2)))
;;  :hints (("Goal" :induct t)))


(defthm contextp-of-cons-of-nil
  (implies (natp nodenum)
           (contextp (list nodenum)))
  :hints (("Goal" :in-theory (enable contextp))))

(defthm contextp-of-cons-of-cons
  (implies (natp nodenum)
           (contextp (list (list 'not nodenum))))
  :hints (("Goal" :in-theory (enable contextp))))

(defthm contextp-singleton
  (equal (contextp (list item))
         (possibly-negated-nodenump item))
  :hints (("Goal" :in-theory (enable contextp))))

(defthm contextp-of-combine-axe-conjunctions-aux
  (implies (and (not (equal 'quote (car (combine-axe-conjunctions-aux x y))))
                (possibly-negated-nodenumsp x)
                (possibly-negated-nodenumsp y))
           (contextp (combine-axe-conjunctions-aux x y)))
  :hints (("Goal" :in-theory (enable combine-axe-conjunctions-aux))))

(defthm true-listp-of-combine-axe-conjunctions-aux
  (implies (and (not (equal 'quote (car (combine-axe-conjunctions-aux x y))))
                (possibly-negated-nodenumsp x)
                (possibly-negated-nodenumsp y))
           (true-listp (combine-axe-conjunctions-aux x y)))
  :hints (("Goal" :in-theory (enable combine-axe-conjunctions-aux))))

(defthm contextp-of-combine-axe-disjunctions-aux
  (implies (and (not (equal 'quote (car (combine-axe-disjunctions-aux x y))))
                (possibly-negated-nodenumsp x)
                (possibly-negated-nodenumsp y))
           (contextp (combine-axe-disjunctions-aux x y)))
  :hints (("Goal" :in-theory (enable combine-axe-disjunctions-aux))))

(defthm true-listp-of-combine-axe-disjunctions-aux
  (implies (and (not (equal 'quote (car (combine-axe-disjunctions-aux x y))))
                (possibly-negated-nodenumsp x)
                (possibly-negated-nodenumsp y))
           (true-listp (combine-axe-disjunctions-aux x y)))
  :hints (("Goal" :in-theory (enable combine-axe-disjunctions-aux))))

(defthm contextp-of-combine-axe-conjunctions
  (implies (and (not (equal 'quote (car (combine-axe-conjunctions x y))))
                (force (axe-conjunctionp x))
                (force (axe-conjunctionp y)))
           (contextp (combine-axe-conjunctions x y)))
  :hints (("Goal" :in-theory (enable combine-axe-conjunctions axe-conjunctionp))))

(defthm true-listp-of-combine-axe-conjunctions
  (implies (and (not (equal 'quote (car (combine-axe-conjunctions x y))))
                (force (axe-conjunctionp x))
                (force (axe-conjunctionp y)))
           (true-listp (combine-axe-conjunctions x y)))
  :hints (("Goal" :in-theory (enable combine-axe-conjunctions axe-conjunctionp))))

;why needed?
(defthm possibly-negated-nodenumsp-of-combine-axe-conjunctions
  (implies (and (not (equal 'quote (car (combine-axe-conjunctions x y))))
                (force (axe-conjunctionp x))
                (force (axe-conjunctionp y)))
           (possibly-negated-nodenumsp (combine-axe-conjunctions x y)))
  :hints (("Goal" :in-theory (enable combine-axe-conjunctions axe-conjunctionp))))

(defthm contextp-of-combine-axe-disjunctions
  (implies (and (not (equal 'quote (car (combine-axe-disjunctions x y))))
                (force (axe-disjunctionp x))
                (force (axe-disjunctionp y)))
           (contextp (combine-axe-disjunctions x y)))
  :hints (("Goal" :in-theory (enable combine-axe-disjunctions axe-disjunctionp))))

(defthm true-listp-of-combine-axe-disjunctions
  (implies (and (not (equal 'quote (car (combine-axe-disjunctions x y))))
                (force (axe-disjunctionp x))
                (force (axe-disjunctionp y)))
           (true-listp (combine-axe-disjunctions x y)))
  :hints (("Goal" :in-theory (enable combine-axe-disjunctions axe-disjunctionp))))

;why needed?
(defthm possibly-negated-nodenumsp-of-combine-axe-disjunctions
  (implies (and (not (equal 'quote (car (combine-axe-disjunctions x y))))
                (force (axe-disjunctionp x))
                (force (axe-disjunctionp y)))
           (possibly-negated-nodenumsp (combine-axe-disjunctions x y)))
  :hints (("Goal" :in-theory (enable combine-axe-disjunctions axe-disjunctionp))))

(defthm contextp-of-negate-axe-disjunction
  (implies (and (not (equal 'quote (car (negate-axe-disjunction item))))
                (force (axe-disjunctionp item)))
           (contextp (negate-axe-disjunction item)))
  :hints (("Goal" :in-theory (enable negate-axe-disjunction contextp))))

;why needed?
(defthm possibly-negated-nodenumsp-of-negate-axe-disjunction
  (implies (and (not (equal 'quote (car (negate-axe-disjunction item))))
                (force (axe-disjunctionp item)))
           (possibly-negated-nodenumsp (negate-axe-disjunction item)))
  :hints (("Goal" :in-theory (enable negate-axe-disjunction contextp))))

(defthm contextp-of-negate-axe-conjunction
  (implies (and (not (equal 'quote (car (negate-axe-conjunction item))))
                (force (axe-conjunctionp item)))
           (contextp (negate-axe-conjunction item)))
  :hints (("Goal" :in-theory (enable negate-axe-conjunction contextp))))

;why needed?
(defthm possibly-negated-nodenumsp-of-negate-axe-conjunction
  (implies (and (not (equal 'quote (car (negate-axe-conjunction item))))
                (force (axe-conjunctionp item)))
           (possibly-negated-nodenumsp (negate-axe-conjunction item)))
  :hints (("Goal" :in-theory (enable negate-axe-conjunction contextp))))

;todo: always go from car/cadr of dargs to nth?

;; ;;move
;; (DEFTHM AXE-CONJUNCTIONP-OF-GET-AXE-CONJUNCTION-FROM-DAG-ITEM-forced
;;   (IMPLIES (force (OR (MYQUOTEP NODENUM-OR-QUOTEP)
;;                       (AND (NATP NODENUM-OR-QUOTEP)
;;                            (PSEUDO-DAG-ARRAYP DAG-ARRAY-NAME
;;                                               DAG-ARRAY (+ 1 NODENUM-OR-QUOTEP)))))
;;            (AXE-CONJUNCTIONP (GET-AXE-CONJUNCTION-FROM-DAG-ITEM
;;                               NODENUM-OR-QUOTEP
;;                               DAG-ARRAY-NAME DAG-ARRAY)))
;;   :hints (("Goal" :use (:instance AXE-CONJUNCTIONP-OF-GET-AXE-CONJUNCTION-FROM-DAG-ITEM)
;;            :in-theory (disable AXE-CONJUNCTIONP-OF-GET-AXE-CONJUNCTION-FROM-DAG-ITEM))))

;; ;;move
;; (DEFTHM AXE-DISJUNCTIONP-OF-GET-AXE-DISJUNCTION-FROM-DAG-ITEM-forced
;;   (IMPLIES (force (OR (MYQUOTEP NODENUM-OR-QUOTEP)
;;                       (AND (NATP NODENUM-OR-QUOTEP)
;;                            (PSEUDO-DAG-ARRAYP DAG-ARRAY-NAME
;;                                               DAG-ARRAY (+ 1 NODENUM-OR-QUOTEP)))))
;;            (AXE-DISJUNCTIONP (GET-AXE-DISJUNCTION-FROM-DAG-ITEM
;;                               NODENUM-OR-QUOTEP
;;                               DAG-ARRAY-NAME DAG-ARRAY)))
;;   :hints (("Goal" :use (:instance AXE-DISJUNCTIONP-OF-GET-AXE-DISJUNCTION-FROM-DAG-ITEM)
;;            :in-theory (disable AXE-DISJUNCTIONP-OF-GET-AXE-DISJUNCTION-FROM-DAG-ITEM))))

;; ;;move
;; (DEFTHM CONSP-OF-GET-AXE-DISJUNCTION-FROM-DAG-ITEM-forced
;;   (IMPLIES (force (OR
;;                    (MYQUOTEP NODENUM-OR-QUOTEP)
;;                    (AND
;;                     (NATP NODENUM-OR-QUOTEP)
;;                     (PSEUDO-DAG-ARRAYP DAG-ARRAY-NAME
;;                                        DAG-ARRAY (+ 1 NODENUM-OR-QUOTEP)))))
;;            (CONSP (GET-AXE-DISJUNCTION-FROM-DAG-ITEM
;;                    NODENUM-OR-QUOTEP
;;                    DAG-ARRAY-NAME DAG-ARRAY)))
;;   :hints (("Goal" :use (:instance CONSP-OF-GET-AXE-DISJUNCTION-FROM-DAG-ITEM)
;;            :in-theory (disable CONSP-OF-GET-AXE-DISJUNCTION-FROM-DAG-ITEM))))

;; ;;move
;; (DEFTHM CONSP-OF-GET-AXE-CONJUNCTION-FROM-DAG-ITEM-forced
;;   (IMPLIES (force (OR
;;                    (MYQUOTEP NODENUM-OR-QUOTEP)
;;                    (AND
;;                     (NATP NODENUM-OR-QUOTEP)
;;                     (PSEUDO-DAG-ARRAYP DAG-ARRAY-NAME
;;                                        DAG-ARRAY (+ 1 NODENUM-OR-QUOTEP)))))
;;            (CONSP (GET-AXE-CONJUNCTION-FROM-DAG-ITEM
;;                    NODENUM-OR-QUOTEP
;;                    DAG-ARRAY-NAME DAG-ARRAY)))
;;   :hints (("Goal" :use (:instance CONSP-OF-GET-AXE-CONJUNCTION-FROM-DAG-ITEM)
;;            :in-theory (disable CONSP-OF-GET-AXE-CONJUNCTION-FROM-DAG-ITEM))))

(local (in-theory (disable array1p-forward))) ;let to a lot of assumptions in the forcing rounds?

(defthm not-complex-rationalp-of-nth-when-all-dargp
  (implies (and (all-dargp args)
                ;(natp n)
                ;(< n (len args))
                )
           (not (complex-rationalp (nth n args))))
  :hints (("Goal" :in-theory (e/d (all-dargp-less-than nth) (NTH-OF-CDR)))))

(defthm not-complex-rationalp-of-nth-of-dargs
  (implies (and (dag-exprp0 expr)
                (< n (len (dargs expr)))
                (natp n)
                (not (equal 'quote (nth 0 expr))))
           (not (complex-rationalp (nth n (dargs expr)))))
  :hints (("Goal" :in-theory (enable integerp-of-nth-when-all-dargp
                                     not-<-of-0-and-nth-when-all-dargp
                                     dag-exprp0))))

(defthm contextp-of-get-axe-disjunction-from-dag-item
  (implies (and (natp nodenum-or-quotep)
                (< nodenum-or-quotep dag-len)
                (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (not (equal 'quote (car (get-axe-disjunction-from-dag-item nodenum-or-quotep dag-array-name dag-array dag-len)))))
           (contextp (get-axe-disjunction-from-dag-item nodenum-or-quotep dag-array-name dag-array dag-len)))
  :hints (("Goal" :use (:instance axe-disjunctionp-of-get-axe-disjunction-from-dag-item)
           :in-theory (e/d (axe-disjunctionp)
                           (axe-disjunctionp-of-get-axe-disjunction-from-dag-item
                            possibly-negated-nodenumsp-when-axe-disjunctionp)))))

(defthm contextp-of-get-axe-conjunction-from-dag-item
  (implies (and (natp nodenum-or-quotep)
                (< nodenum-or-quotep dag-len)
                (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (not (equal 'quote (car (get-axe-conjunction-from-dag-item nodenum-or-quotep dag-array-name dag-array dag-len)))))
           (contextp (get-axe-conjunction-from-dag-item nodenum-or-quotep dag-array-name dag-array dag-len)))
  :hints (("Goal" :use (:instance axe-conjunctionp-of-get-axe-conjunction-from-dag-item)
           :in-theory (e/d (axe-conjunctionp)
                           (axe-conjunctionp-of-get-axe-conjunction-from-dag-item
                            possibly-negated-nodenumsp-when-axe-conjunctionp)))))

;; ;;slow
;; (defthm-flag-get-axe-disjunction-from-dag-item
;;   (defthm true-listp-of-get-axe-disjunction-from-dag-item
;;     (implies (and (natp nodenum-or-quotep)
;;                   (pseudo-dag-arrayp dag-array-name dag-array (+ 1 nodenum-or-quotep))
;;                   (not (equal 'quote (car (get-axe-disjunction-from-dag-item nodenum-or-quotep dag-array-name dag-array)))))
;;              (true-listp (get-axe-disjunction-from-dag-item nodenum-or-quotep dag-array-name dag-array)))
;;     :flag get-axe-disjunction-from-dag-item)
;;   (defthm true-listp-of-get-axe-conjunction-from-dag-item
;;     (implies (and (natp nodenum-or-quotep)
;;                   (pseudo-dag-arrayp dag-array-name dag-array (+ 1 nodenum-or-quotep))
;;                   (not (equal 'quote (car (get-axe-conjunction-from-dag-item nodenum-or-quotep dag-array-name dag-array)))))
;;              (true-listp (get-axe-conjunction-from-dag-item nodenum-or-quotep dag-array-name dag-array)))
;;     :flag get-axe-conjunction-from-dag-item)
;;   :hints (("Goal" :in-theory (e/d (cadr-becomes-nth-of-1 car-becomes-nth-of-0) (alistp
;;                                                                                 ;;pseudo-dag-arrayp ;todo?
;;                                                                                 )))))

;returns a contextp that is boolean-equivalent to NODENUM
(defund get-context-from-node (nodenum ;allow a quotep? might just work (then the caller could do less checking?)
                               dag-array-name
                               dag-array
                               dag-len)
  (declare (xargs :guard (and (natp nodenum)
                              (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (< nodenum dag-len))
                  :guard-hints (("Goal" :use (:instance axe-conjunctionp-of-get-axe-conjunction-from-dag-item (nodenum-or-quotep nodenum))
                                 :in-theory (e/d (axe-conjunctionp GET-AXE-CONJUNCTION-FROM-DAG-ITEM)
                                                 (axe-conjunctionp-of-get-axe-conjunction-from-dag-item
                                                  ;axe-conjunctionp-of-get-axe-conjunction-from-dag-item-forced
                                                  ))))))
  (let ((conjunction (get-axe-conjunction-from-dag-item nodenum dag-array-name dag-array dag-len)))
    (if (quotep conjunction)
        (if (unquote conjunction)
            (true-context)
          (false-context))
      conjunction)))

(defthm contextp-of-get-context-from-node
  (implies (and (natp nodenum)
                (< nodenum dag-len)
                (pseudo-dag-arrayp dag-array-name dag-array dag-len))
           (contextp (get-context-from-node nodenum dag-array-name dag-array dag-len)))
  :hints (("Goal" :in-theory (enable get-context-from-node))))

;returns a contextp that is boolean-equivalent to the negation of NODENUM
(defund get-context-from-negation-of-node (nodenum ;allow a quotep? might just work (then the caller could do less checking?)
                                           dag-array-name
                                           dag-array
                                           dag-len)
  (declare (xargs :guard (and (natp nodenum)
                              (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (< nodenum dag-len))
                  :guard-hints (("Goal" :use (:instance axe-disjunctionp-of-get-axe-disjunction-from-dag-item (nodenum-or-quotep nodenum))
                                 :in-theory (e/d (axe-disjunctionp)
                                                 (axe-disjunctionp-of-get-axe-disjunction-from-dag-item
;axe-disjunctionp-of-get-axe-disjunction-from-dag-item-forced
                                                  ))))))
  (let ((disjunction (get-axe-disjunction-from-dag-item nodenum dag-array-name dag-array dag-len)))
    (if (quotep disjunction) ;negate it:
        (if (unquote disjunction)
            (false-context)
          (true-context))
      ;;it's a list of nodenums and negations of nodenums:
      (negate-possibly-negated-nodenums disjunction))))

(defthm contextp-of-get-context-from-negation-of-node
  (implies (and (natp nodenum)
                (< nodenum dag-len)
                (pseudo-dag-arrayp dag-array-name dag-array dag-len))
           (contextp (get-context-from-negation-of-node nodenum dag-array-name dag-array dag-len)))
  :hints (("Goal" :in-theory (enable contextp get-context-from-negation-of-node))))

;; ;returns a contextp equivalent to nodenum (flattens nested ANDs)
;; ;;fixme what about a negation of a boolor?
;; (skip- proofs
;;  (defun get-context-equivalent-to-node (nodenum dag-array-name dag-array)
;;    (let* ((expr (aref1 dag-array-name dag-array nodenum)))
;;      (if (variablep expr)
;;          (list nodenum) ;always safe to do this
;;        (let ((fn (ffn-symb expr)))
;;          (if (eq 'quote fn)
;;              (if (unquote expr)
;;                  ;;non-nil constant:
;;                  (true-context)
;;                (false-context) ;false context
;;                )
;;            (if (and (eq 'booland fn)
;;                     (integerp (farg1 expr)) ;what if not?
;;                     (integerp (farg2 expr)) ;what if not?
;;                     )
;;                (conjoin-contexts (get-context-equivalent-to-node (farg1 expr) dag-array-name dag-array)
;;                                  (get-context-equivalent-to-node (farg2 expr) dag-array-name dag-array))
;;              (if (and (eq 'not fn)
;;                       (integerp (farg1 expr)) ;what if not?
;;                       )
;;                  (list `(not ,(farg1 expr)))
;;                ;;always safe to do this:
;;                (list nodenum)))))))))

;;(skip- proofs (verify-guards get-context-equivalent-to-node))

;; (defthm contextp-of-get-context-equivalent-to-node
;;   (implies (integerp nodenum)
;;            (contextp (get-context-equivalent-to-node nodenum dag-array-name dag-array)))
;;   :hints (("Goal" :in-theory (disable contextp))))

(local (in-theory (disable contextp))) ;make non-local?

;todo: this failed when contextp was enabled
(def-typed-acl2-array context-arrayp (contextp val))

(defthmd acl2-numberp-of-nth-when-all-dargp
  (implies (and (all-dargp args)
                (natp n)
                (< n (len args))
                )
           (equal (acl2-numberp (nth n args))
                  (not (consp (nth n args)))))
  :hints (("Goal" :in-theory (e/d (all-dargp-less-than nth) (NTH-OF-CDR)))))

;compute the context of nodenum coming in via the given parent (this is just the parent's context unless the parent is an ITE)
;ffixme handle parents that are boolands and boolors - careful! -- must order the nodes: for (booland a b) we can't both assume a for b and assume b for a..
(defthm acl2-numberp-of-nth-of-dargs
  (implies (and (dag-exprp0 expr)
                (< n (len (dargs expr)))
                (natp n)
                (not (equal 'quote (car expr)))
;               (not (consp (nth n (aref1 dag-array-name dag-array nodenum)))) ;rules out a quotep
                )
           (equal (acl2-numberp (nth n (dargs expr)))
                  (not (consp (nth n (dargs expr))))))
  :hints (("Goal" :in-theory (enable acl2-numberp-of-nth-when-all-dargp))))

(defund get-context-via-parent (nodenum parent-nodenum dag-array-name dag-array dag-len context-array)
  (declare (xargs :guard (and (natp nodenum)
                              (natp parent-nodenum)
                              (< nodenum parent-nodenum)
                              (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (context-arrayp 'context-array context-array dag-len)
                              (< parent-nodenum dag-len))
                  :guard-hints (("Goal" :in-theory (enable cadr-becomes-nth-of-1 car-becomes-nth-of-0 context-arrayp)))))
  (let* ((parent-context (aref1 'context-array context-array parent-nodenum))
         (parent-expr (aref1 dag-array-name dag-array parent-nodenum)))
    (if (variablep parent-expr)
        (hard-error 'get-context-via-parent "parent should not be a variable" nil)
      (let ((parent-fn (ffn-symb parent-expr)))
        (if (and (or (eq 'if parent-fn) ;;(if/myif/boolif test thenpart elsepart)
                     (eq 'myif parent-fn)
                     (eq 'boolif parent-fn))
                 (= 3 (len (dargs parent-expr)))
                 (atom (darg1 parent-expr))) ;makes sure the test is a nodenum ;ffixme should we handle constants?  no, because we should never build an if with a constant test?  what if such a term arises from putting in a constant when merging? ;drop this now?
            (if (and (eql nodenum (darg2 parent-expr))
                     (not (eql nodenum (darg1 parent-expr)))
                     (not (eql nodenum (darg3 parent-expr))))
                ;;nodenum is the then-branch (but not the else-branch or the test), so add the test to the context for nodenum:
                (conjoin-contexts (get-context-from-node (darg1 parent-expr) dag-array-name dag-array dag-len) ;(get-context-equivalent-to-node (darg1 parent-expr) dag-array-name dag-array)
                                  parent-context)
              (if (and (eql nodenum (darg3 parent-expr))
                       (not (eql nodenum (darg1 parent-expr)))
                       (not (eql nodenum (darg2 parent-expr))))
                  ;;nodenum is the else-branch (but not the then-branch or the test), so add the negation of the test to the context for nodenum:
                  ;(negate-and-conjoin-to-context (darg1 parent-expr) parent-context dag-array-name dag-array)
                  (conjoin-contexts (get-context-from-negation-of-node (darg1 parent-expr) dag-array-name dag-array dag-len)
                                    parent-context)
                ;;nodenum is the test or appears in more than one argument (should be rare), so we don't add anything to the context:
                parent-context))
          (if (and (eq 'bvif parent-fn) ;(bvif size test thenpart elsepart)
                   (= 4 (len (dargs parent-expr)))
                   (atom (darg2 parent-expr))) ;makes sure the test is a nodenum ;drop?
              (if (and (eql nodenum (darg3 parent-expr))
                       (not (eql nodenum (darg1 parent-expr)))
                       (not (eql nodenum (darg2 parent-expr)))
                       (not (eql nodenum (darg4 parent-expr))))
                  ;;nodenum is the then-branch but not the else-branch (or the test or the size), so add the test to the context:
                  (conjoin-contexts (get-context-from-node (darg2 parent-expr) dag-array-name dag-array dag-len) ;(get-context-equivalent-to-node (darg2 parent-expr) dag-array-name dag-array)
                                    parent-context)
                (if (and (eql nodenum (darg4 parent-expr))
                         (not (eql nodenum (darg1 parent-expr)))
                         (not (eql nodenum (darg2 parent-expr)))
                         (not (eql nodenum (darg3 parent-expr))))
                    ;;nodenum is the else-branch but not the then-branch (or the test or the size), so add the negation of test to the context:
                    ;(negate-and-conjoin-to-context (darg2 parent-expr) parent-context dag-array-name dag-array)
                    (conjoin-contexts (get-context-from-negation-of-node (darg2 parent-expr) dag-array-name dag-array dag-len)
                                      parent-context)
                  ;;otherwise (nodenum is the test or size or appears more than once), we don't add anything to the context:
                  parent-context))
            ;;it's not an ITE:
            parent-context))))))

(defthm contextp-of-get-context-via-parent
  (implies (and (natp nodenum)
                (natp parent-nodenum)
                (< nodenum parent-nodenum)
                (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (context-arrayp 'context-array context-array dag-len)
                (< parent-nodenum dag-len))
           (contextp (get-context-via-parent nodenum parent-nodenum dag-array-name dag-array dag-len context-array)))
  :hints (("Goal" :in-theory (enable get-context-via-parent
                                     cadr-becomes-nth-of-1 car-becomes-nth-of-0))))

;; (defthm rational-listp-when-all-natp
;;   (implies (all-natp nodenums)
;;            (equal (RATIONAL-LISTP NODENUMS)
;;                   (true-listp nodenums))))

(defthm acl2-numberp-of-maxelem-forced
  (implies (and (consp items)
                (force (rational-listp items)))
           (acl2-numberp (maxelem items)))
  :hints (("Goal" :in-theory (enable maxelem))))

(defthm natp-of-maxelem-forced
  (implies (and (consp items)
                (all-natp items))
           (natp (maxelem items)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable maxelem))))

;;todo: pull out lemmas proved by induction (about all-> ?)
(defun disjoin-contexts-of-parents (parent-nodenums nodenum dag-array-name dag-array dag-len context-array context-so-far)
  (declare (xargs :guard (and (natp nodenum)
                              (all-natp parent-nodenums)
                              (true-listp parent-nodenums)
                              (all-> parent-nodenums nodenum)
                              (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (all-< parent-nodenums dag-len)
                              (context-arrayp 'context-array context-array dag-len)
                              (contextp context-so-far))
                  :guard-hints (("Goal" :in-theory (enable all-> cadr-becomes-nth-of-1 car-becomes-nth-of-0 context-arrayp)))))
  (if (endp parent-nodenums)
      context-so-far
    (let* ((context-via-next-parent (get-context-via-parent nodenum (first parent-nodenums) dag-array-name dag-array dag-len context-array))
           (context-so-far (disjoin-contexts context-so-far context-via-next-parent)))
      (disjoin-contexts-of-parents (rest parent-nodenums) nodenum dag-array-name dag-array dag-len context-array context-so-far))))

(defthm contextp-of-disjoin-contexts-of-parents
  (implies (and (natp nodenum)
                (all-natp parent-nodenums)
                (true-listp parent-nodenums)
                (all-> parent-nodenums nodenum)
                (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (all-< parent-nodenums dag-len)
                (context-arrayp 'context-array context-array dag-len)
                (contextp context-so-far))
           (contextp (disjoin-contexts-of-parents parent-nodenums nodenum dag-array-name dag-array dag-len context-array context-so-far)))
  :hints (("Goal" :in-theory (e/d (disjoin-contexts-of-parents) (pseudo-dag-arrayp)))))

;;move the aset out of this function?
;;todo: pull out lemmas proved by induction
(defund set-context-of-nodenum (nodenum parent-nodenums dag-array-name dag-array dag-len context-array)
  (declare (xargs :guard (and (natp nodenum)
                              (all-natp parent-nodenums)
                              (true-listp parent-nodenums)
                              (all-> parent-nodenums nodenum)
                              (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (< nodenum dag-len)
                              (all-< parent-nodenums dag-len)
                              (context-arrayp 'context-array context-array dag-len))
                  :guard-hints (("Goal" :in-theory (enable all-> cadr-becomes-nth-of-1 car-becomes-nth-of-0 context-arrayp)))))
  (if (endp parent-nodenums)
      (prog2$ (cw "!! nodenum ~x0 is an orphan" nodenum)
              (aset1 'context-array context-array nodenum (false-context)))
    (let* ((context-via-first-parent (get-context-via-parent nodenum (first parent-nodenums) dag-array-name dag-array dag-len context-array)) ;could start here with a context of (false-context)? and eliminate the check above
           (context (disjoin-contexts-of-parents (rest parent-nodenums) nodenum dag-array-name dag-array dag-len context-array context-via-first-parent)))
      (aset1 'context-array context-array nodenum context))))

(defthm context-arrayp-of-set-context-of-nodenum
  (implies (and (context-arrayp 'context-array context-array len)
                (natp nodenum)
                ;(< nodenum len)
                (all-natp parent-nodenums)
                (true-listp parent-nodenums)
                (all-> parent-nodenums nodenum)
                (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (< nodenum dag-len)
                (all-< parent-nodenums dag-len)
                (context-arrayp 'context-array context-array dag-len))
           (context-arrayp 'context-array (set-context-of-nodenum nodenum parent-nodenums dag-array-name dag-array dag-len context-array) len))
  :hints (("Goal" :in-theory (enable set-context-of-nodenum))))

(defthm array1p-of-set-context-of-nodenum
  (implies (and (natp nodenum)
                (< nodenum (alen1 'context-array context-array))
                (array1p 'context-array context-array))
           (array1p 'context-array (set-context-of-nodenum nodenum parent-nodenums dag-array-name dag-array dag-len context-array)))
  :hints (("Goal" :in-theory (enable set-context-of-nodenum))))

(defthm alen1-of-set-context-of-nodenum
  (implies (and (natp nodenum)
                (< nodenum (alen1 'context-array context-array))
                (array1p 'context-array context-array))
           (equal (alen1 'context-array (set-context-of-nodenum nodenum parent-nodenums dag-array-name dag-array dag-len context-array))
                  (alen1 'context-array context-array)))
  :hints (("Goal" :in-theory (enable set-context-of-nodenum))))

;would it be faster to just take a non-array and cdr down it?
;nodenum counts down
;returns 'context-array, which associates nodenums with their contextps
(defun make-full-context-array-aux (nodenum dag-array-name dag-array dag-len dag-parent-array context-array)
  (declare (xargs :guard (and (integerp nodenum)
                              (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (dag-parent-arrayp 'dag-parent-array dag-parent-array)
                              (context-arrayp 'context-array context-array dag-len)
                              ;; not necesarly equal:
                              (<= dag-len (alen1 'dag-parent-array dag-parent-array))
                              (bounded-dag-parent-entriesp (+ -1 dag-len) 'dag-parent-array dag-parent-array dag-len)
                              (< nodenum dag-len))
                  :guard-hints (("Goal" :in-theory (e/d (<-of-+-of-1-strengthen-2 DAG-PARENT-ARRAYP) (PSEUDO-DAG-ARRAYP))))
                  :measure (nfix (+ 1 nodenum))))
  (if (not (natp nodenum))
      context-array
    (let* ((parents (aref1 'dag-parent-array dag-parent-array nodenum))
           (context-array (set-context-of-nodenum nodenum parents dag-array-name dag-array dag-len context-array)))
      (make-full-context-array-aux (+ -1 nodenum) dag-array-name dag-array dag-len dag-parent-array context-array))))

(defthm array1p-of-make-full-context-array-aux
  (implies (and (array1p 'context-array context-array)
                (< nodenum (alen1 'context-array context-array)))
           (array1p 'context-array (make-full-context-array-aux nodenum dag-array-name dag-array dag-len dag-parent-array context-array))))

(defthm alen1-of-make-full-context-array-aux
  (implies (and (array1p 'context-array context-array)
                (< nodenum (alen1 'context-array context-array)))
           (equal (alen1 'context-array (make-full-context-array-aux nodenum dag-array-name dag-array dag-len dag-parent-array context-array))
                  (alen1 'context-array context-array))))

;returns 'context-array, which associates nodenums with their contextps
;; Use make-full-context-array instead if you don't already have the parent array.
(defun make-full-context-array-with-parents (dag-array-name dag-array dag-len dag-parent-array)
  (declare (xargs :guard (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (posp dag-len)
                              (<= dag-len 2147483646)
                              (dag-parent-arrayp 'dag-parent-array dag-parent-array)
                              ;; not necesarly equal:
                              (<= dag-len (alen1 'dag-parent-array dag-parent-array))
                              (bounded-dag-parent-entriesp (+ -1 dag-len) 'dag-parent-array dag-parent-array dag-len))
                  :guard-hints (("Goal" :in-theory (enable dag-parent-arrayp)))))
  (let* ((context-array (make-empty-array 'context-array dag-len))
         (top-nodenum (+ -1 dag-len))
         (context-array (aset1 'context-array context-array top-nodenum (true-context))) ;top node has no context
         (context-array (make-full-context-array-aux (+ -1 top-nodenum) ; skip the top node
                                                     dag-array-name
                                                     dag-array
                                                     dag-len
                                                     dag-parent-array
                                                     context-array)))
    context-array))

;new version! deprecate the old way of doing things (already done?)?
;returns 'context-array, which associates nodenums with their contextps
;smashes 'dag-parent-array
;; Use make-full-context-array-with-parents instead if you already have the parent array.
(defun make-full-context-array (dag-array-name dag-array dag-len)
  (declare (xargs :guard (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (posp dag-len)
                              (<= dag-len 2147483646))))
  (make-full-context-array-with-parents dag-array-name
                                        dag-array
                                        dag-len
                                        (make-dag-parent-array-with-name dag-len ; somewhat unusual not to use (alen1 dag-array-name dag-array) here, but this array doesn't need to grow after creation
                                                                         dag-array-name
                                                                         dag-array
                                                                         'dag-parent-array)))

;returns t, nil, or :unknown, depending on whether the context tells us anything about nodenum (fixme what if nodenum is the nodenum of a booland, a not, etc.?)
;fixme what if the context is (false-context)?
(defun look-up-in-context-aux (nodenum context)
  (declare (xargs :guard (and (possibly-negated-nodenumsp context)
                              (integerp nodenum))
                  :guard-hints (("Goal" :in-theory (enable cdr-iff-when-possibly-negated-nodenump
                                                           consp-of-cdr-when-possibly-negated-nodenump)))))
  (if (endp context)
      :unknown
    (let ((context-item (first context)))
      (if (eql nodenum context-item)
          t
        (if (and (consp context-item) ;it must be a not
                 (eql nodenum (farg1 context-item)))
            nil
          (look-up-in-context-aux nodenum (rest context)))))))

;can take a quotep, so the caller doesn't have to check
;returns t (meaning can assume non-nil), nil (meaning can assume nil), or :unknown
(defun look-up-in-context (nodenum-or-quotep context)
  (declare (xargs :guard (and (contextp context)
                              (or (and (quotep nodenum-or-quotep)
                                       (consp (cdr nodenum-or-quotep)))
                                  (integerp nodenum-or-quotep)))))
  (if (eq (false-context) context)
      :unknown ;fffffixme think about what to do here (just pick one of t or nil?)
    (if (consp nodenum-or-quotep)
        ;;it's a quotep (should be rare?)
        (if (unquote nodenum-or-quotep)
            t
          nil)
      (look-up-in-context-aux nodenum-or-quotep context))))

;returns a function call expression whose args are nodenums/quoteps, or nil to
;indicate that this item should be skipped.  The function call will often be
;NOT.
(defun context-item-to-maybe-expr (context-item dag-array)
  (if (atom context-item)
      ;; it's a nodenum, so look it up:
      (let ((expr (aref1 'dag-array dag-array context-item)))
        (if (or (symbolp expr)
                (quotep expr))
            nil ;not a suitable function call expr, so drop it
          expr))
    ;; it's of the form (not <nodenum>), so it is already a suitable expr
    context-item))

;;Turns a context into exprs that are function calls applied to nodenums /
;;quoteps.  Items in the context that map to variables or constants are dropped.
(defun context-to-exprs (context ; a possibly-negated-nodenumsp
                         dag-array)
  (if (endp context)
      nil
    (let* ((context-item (first context))
           (maybe-expr (context-item-to-maybe-expr context-item dag-array)))
      (if maybe-expr
          (cons maybe-expr (context-to-exprs (rest context) dag-array))
        (context-to-exprs (rest context) dag-array)))))

;returns nil
(defun print-contexts (dag-lst)
  (declare (xargs :guard (and (pseudo-dagp dag-lst)
                              (< (len dag-lst) 2147483645))
                  :guard-hints (("Goal" :in-theory (e/d (pseudo-dagp) (pseudo-dag-arrayp))))))
  (prog2$ (cw "(Computing contexts:~%")
          (let* ((dag-len (len dag-lst))
                 (dag-array (make-into-array 'dag-array dag-lst))
                 (context-array (make-full-context-array 'dag-array dag-array dag-len)))
            (prog2$ (cw ")~%")
                    (print-array2 'context-array context-array dag-len)))))
