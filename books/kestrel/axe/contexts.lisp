; Computing contexts from overarching DAG nodes
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

(include-book "conjunctions-and-disjunctions")
(include-book "dag-parent-array-with-name")
(include-book "kestrel/acl2-arrays/typed-acl2-arrays" :dir :system)
(include-book "rational-lists")
(include-book "kestrel/bv/bvif" :dir :system) ;since this book deals with bvif specially (do not remove)
(include-book "kestrel/booleans/boolif" :dir :system) ;since this book deals with boolif specially (do not remove)
(include-book "kestrel/utilities/myif" :dir :system) ;since this book deals with myif specially (do not remove)
(include-book "refine-assumptions") ; todo.  for all-dag-function-call-exprp
(local (include-book "kestrel/acl2-arrays/acl2-arrays" :dir :system))
(local (include-book "kestrel/lists-light/nth" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "numeric-lists"))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))

;; (defthm rational-listp-when-all-natp
;;   (implies (all-natp nodenums)
;;            (equal (RATIONAL-LISTP NODENUMS)
;;                   (true-listp nodenums))))

(defthm acl2-numberp-of-maxelem-forced
  (implies (and (consp items)
                (force (rational-listp items)))
           (acl2-numberp (maxelem items)))
  :hints (("Goal" :in-theory (enable maxelem))))

(defthm natp-of-maxelem-forced ; todo: rename
  (implies (and (consp items)
                (all-natp items))
           (natp (maxelem items)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable maxelem))))

;compute the context of nodenum coming in via the given parent (this is just the parent's context unless the parent is an ITE)
;ffixme handle parents that are boolands and boolors - careful! -- must order the nodes: for (booland a b) we can't both assume a for b and assume b for a..

;for speed:
(local (in-theory (disable nth-when-<=-len-cheap
                           ;;nth-with-large-index-cheap
                           nth-when-zp-cheap
                           nth-when-not-consp-cheap
                           not-consp-of-nth-of-dargs-of-aref1
                           ;;consp-when-len-equal
                           )))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;
;; contexts
;;

;use these more!
(defmacro true-context () nil) ;a conjunction of no things is taken to be true
(defmacro false-context () :false)

(defmacro false-contextp (item)
  `(eq (false-context) ,item))

;; enabled for now
(defun-inline non-false-contextp (context)
  (declare (xargs :guard t))
  (possibly-negated-nodenumsp context))

(defund contextp (context)
  (declare (xargs :guard t))
  (or (eq (false-context) context)
      ;;a non-false context is a list of conjuncts of the form <nodenum> or (not <nodenum>)
      ;;the meaning of a context is the conjunction of its items
      ;;a context of nil represents "true" (the conjunction of no things)
      ;; TODO: for efficiency, consider separating the lists of true and false things...
      ;; TODO: Consider requiring no dups, consider requiring no obvious contradictions (x and (not x) both present):
      (non-false-contextp context)))

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

(defthm contextp-when-nat-listp-cheap
  (implies (nat-listp context)
           (contextp context))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable contextp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund bounded-contextp (context bound)
  (declare (xargs :guard (natp bound)
                  :split-types t)
           (type (integer 0 *) bound))
  (or (eq (false-context) context)
      (bounded-possibly-negated-nodenumsp context bound)))

(defthm bounded-contextp-of-nil
  (bounded-contextp nil bound)
  :hints (("Goal" :in-theory (enable bounded-contextp))))

(defthm bounded-contextp-of-false
  (bounded-contextp :false bound)
  :hints (("Goal" :in-theory (enable bounded-contextp))))

(defthm contextp-when-bounded-contextp
  (implies (bounded-contextp context bound)
           (contextp context))
  :hints (("Goal" :in-theory (enable bounded-contextp contextp))))

(defthm bounded-contextp-forward-to-context
  (implies (bounded-contextp context bound)
           (contextp context))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable bounded-contextp contextp))))

;; limit?
(defthm bounded-possibly-negated-nodenumsp-when-bounded-contextp
  (implies (bounded-contextp context bound)
           (equal (bounded-possibly-negated-nodenumsp context bound)
                  (not (equal (false-context) context))))
  :hints (("Goal" :in-theory (enable bounded-contextp))))

(defthm bounded-contextp-monotone
  (implies (and (bounded-contextp context bound1)
                (<= bound1 bound)
                (natp bound1)
                (natp bound))
           (bounded-contextp context bound))
  :hints (("Goal" :in-theory (enable bounded-contextp))))

(defthm bounded-contextp-of-negate-possibly-negated-nodenums
  (implies (bounded-possibly-negated-nodenumsp possibly-negated-nodenums bound)
           (bounded-contextp (negate-possibly-negated-nodenums possibly-negated-nodenums) bound))
  :hints (("Goal" :in-theory (enable bounded-contextp negate-possibly-negated-nodenums))))

(defthm bounded-contextp-when-bounded-axe-disjunctionp
  (implies (and (bounded-axe-disjunctionp item bound)
                (not (quotep item)))
           (bounded-contextp item bound))
  :hints (("Goal" :in-theory (enable bounded-contextp bounded-axe-disjunctionp))))

(defthm bounded-contextp-when-bounded-axe-conjunctionp
  (implies (and (bounded-axe-conjunctionp item bound)
                (not (quotep item)))
           (bounded-contextp item bound))
  :hints (("Goal" :in-theory (enable bounded-contextp bounded-axe-conjunctionp))))

(defthm bounded-possibly-negated-nodenumsp-when-bounded-contextp
  (implies (bounded-contextp context bound)
           (equal (bounded-possibly-negated-nodenumsp context bound)
                  (not (equal (false-context) context))))
  :hints (("Goal" :in-theory (enable bounded-contextp bounded-possibly-negated-nodenumsp))))

(defthm bounded-contextp-of-if
  (equal (bounded-contextp (if test then else) bound)
         (if test (bounded-contextp then bound) (bounded-contextp else bound))))

(defthm bounded-contextp-when-nat-listp
  (implies (nat-listp context)
           (equal (bounded-contextp context bound)
                  (all-< context bound)))
  :hints (("Goal" :in-theory (enable bounded-contextp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

(defthm <=-of-0-and-max-nodenum-in-possibly-negated-nodenums-aux
  (implies (and (possibly-negated-nodenumsp items)
                (consp items)
                )
           (<= 0 (max-nodenum-in-possibly-negated-nodenums-aux items acc)))
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

(defthm <-of-max-nodenum-in-possibly-negated-nodenums-aux-when-bounded-possibly-negated-nodenumsp
  (implies (and (bounded-possibly-negated-nodenumsp context bound)
                (natp bound)
                (< acc bound))
           (< (max-nodenum-in-possibly-negated-nodenums-aux context acc) bound))
  :hints (("Goal" :in-theory (enable max-nodenum-in-possibly-negated-nodenums-aux
                                     bounded-possibly-negated-nodenumsp
                                     bounded-possibly-negated-nodenump))))

(local
 (defthm max-nodenum-in-possibly-negated-nodenums-aux-monotone-same-items
   (implies (<= acc1 acc2)
            (<= (max-nodenum-in-possibly-negated-nodenums-aux items acc1)
                (max-nodenum-in-possibly-negated-nodenums-aux items acc2)))
   :hints (("Goal" :in-theory (enable max-nodenum-in-possibly-negated-nodenums-aux)))))

(local
 (defthm max-nodenum-in-possibly-negated-nodenums-aux-monotone-helper
   (implies (<= acc1 acc2)
            (<= (max-nodenum-in-possibly-negated-nodenums-aux (cdr items) acc1)
                (max-nodenum-in-possibly-negated-nodenums-aux items acc2)))
   :hints (("Goal" :expand ((max-nodenum-in-possibly-negated-nodenums-aux nil acc1)
                            (max-nodenum-in-possibly-negated-nodenums-aux items acc2))))))

(defthm max-nodenum-in-possibly-negated-nodenums-aux-cdr-monotone
  (<= (max-nodenum-in-possibly-negated-nodenums-aux (cdr items) acc)
      (max-nodenum-in-possibly-negated-nodenums-aux items acc))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable max-nodenum-in-possibly-negated-nodenums-aux))))

(defthm all-<-of-strip-nots-from-possibly-negated-nodenums-and-+1-of-max-nodenum-in-possibly-negated-nodenums-aux
  (implies (and (possibly-negated-nodenumsp items)
                (integerp acc)
                )
           (all-< (strip-nots-from-possibly-negated-nodenums items) (+ 1 (max-nodenum-in-possibly-negated-nodenums-aux items acc))))
  :hints (("Goal" :in-theory (enable strip-nots-from-possibly-negated-nodenums max-nodenum-in-possibly-negated-nodenums-aux
                                     strip-not-from-possibly-negated-nodenum
                                     possibly-negated-nodenumsp
                                     possibly-negated-nodenump))))

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

(defthm natp-of-max-nodenum-in-possibly-negated-nodenums
  (implies (and (possibly-negated-nodenumsp items)
                (consp items))
           (natp (max-nodenum-in-possibly-negated-nodenums items)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable max-nodenum-in-possibly-negated-nodenums))))

(defthm <=-of-max-nodenum-in-possibly-negated-nodenums-linear
  (implies (possibly-negated-nodenumsp items)
           (<= -1 (max-nodenum-in-possibly-negated-nodenums items)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable max-nodenum-in-possibly-negated-nodenums))))

(defthm <-of-max-nodenum-in-possibly-negated-nodenums-when-bounded-possibly-negated-nodenumsp
  (implies (and (bounded-possibly-negated-nodenumsp context bound)
                (natp bound))
           (< (max-nodenum-in-possibly-negated-nodenums context) bound))
  :hints (("Goal" :in-theory (enable max-nodenum-in-possibly-negated-nodenums))))

(defthm all-<-of-strip-nots-from-possibly-negated-nodenums-and-+1-of-max-nodenum-in-possibly-negated-nodenums
  (implies (possibly-negated-nodenumsp items)
           (all-< (strip-nots-from-possibly-negated-nodenums items) (+ 1 (max-nodenum-in-possibly-negated-nodenums items))))
  :hints (("Goal" :in-theory (enable max-nodenum-in-possibly-negated-nodenums strip-nots-from-possibly-negated-nodenums
                                     strip-not-from-possibly-negated-nodenum))))

;;;
;;; max-nodenum-in-context
;;;

;returns -1 if no nodenums are mentioned (true or false context)
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

(defthm <-of-max-nodenum-in-context-when-bounded-contextp
  (implies (and (bounded-contextp context bound)
                (natp bound))
           (< (max-nodenum-in-context context) bound))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable max-nodenum-in-context
                                     bounded-contextp))))

;; (thm
;;  (implies (contextp context)
;;           (equal (equal -1 (MAX-NODENUM-IN-CONTEXT context))
;;                  (false-contextp context)))
;;  :hints (("Goal" :in-theory (enable MAX-NODENUM-IN-CONTEXT))))

;strips off any nots
(defun get-nodenums-mentioned-in-non-false-context (context)
  (declare (xargs :guard (and (contextp context)
                              (not (false-contextp context)))))
  (strip-nots-from-possibly-negated-nodenums context))

;; see how contexts are used in the equivalence checker
(thm
 (implies (and (contextp context)
               (not (false-contextp context)))
          (iff (get-nodenums-mentioned-in-non-false-context context)
               context))
 :hints (("Goal" :in-theory (enable strip-nots-from-possibly-negated-nodenums contextp))))

;strips off any nots
;; todo: can we get rid of this?  usually, if we have a false context we can do better
(defun get-nodenums-mentioned-in-context (context)
  (declare (xargs :guard (contextp context)))
  (if (false-contextp context)
      nil
    (get-nodenums-mentioned-in-non-false-context context)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;checks for contradictions:
;; TODO: Avoid comparing later items in CONTEXT1 to earlier items already copied from CONTEXT1 to CONTEXT2?
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
        (if (member-equal `(not ,item) context2) ; TODO: save this cons?
            (false-context)
          (conjoin-contexts-aux (rest context1) (add-to-set-equal item context2)))))))

(defthm contextp-of-conjoin-contexts-aux
  (implies (and (possibly-negated-nodenumsp context1)
                (possibly-negated-nodenumsp context2))
           (contextp (conjoin-contexts-aux context1 context2)))
  :hints (("Goal" :in-theory (enable conjoin-contexts-aux))))

(defthm bounded-contextp-of-conjoin-contexts-aux
  (implies (and (bounded-possibly-negated-nodenumsp context1 bound)
                (bounded-possibly-negated-nodenumsp context2 bound))
           (bounded-contextp (conjoin-contexts-aux context1 context2) bound))
  :hints (("Goal" :in-theory (enable bounded-contextp conjoin-contexts-aux))))

;; Computes a context equivalent to the conjunction of CONTEXT1 and CONTEXT2.
;; This doesn't look up the nodenums in the contexts and so may miss some
;; simplifications (e.g., if we know (or x y) and then learn (not x)).
(defund conjoin-contexts (context1 context2)
  (declare (xargs :guard (and (contextp context1)
                              (contextp context2))))
  (if (or (eq (false-context) context1)
          (eq (false-context) context2))
      (false-context)
    ;;both are lists of nodenums and negated nodenums:
    (conjoin-contexts-aux context1 context2)))

(defthm contextp-of-conjoin-contexts
  (implies (and (contextp context1)
                (contextp context2))
           (contextp (conjoin-contexts context1 context2)))
  :hints (("Goal" :in-theory (enable conjoin-contexts))))

(defthm bounded-contextp-of-conjoin-contexts
  (implies (and (bounded-contextp context1 bound)
                (bounded-contextp context2 bound))
           (bounded-contextp (conjoin-contexts context1 context2) bound))
  :hints (("Goal" :in-theory (enable bounded-contextp conjoin-contexts))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Computes a context implied by the disjunction of CONTEXT1 and CONTEXT2.
;this is inexact in two ways (doesn't look inside the nodenums in the context, also can't express the disjunction of two conjunctions as a single conjunction)
;the second type of loss of information has the flavor of the convex hull operations done when generating polyhedral invariants using the abstract interpretation framework.
(defund disjoin-contexts (context1 context2)
  (declare (xargs :guard (and (contextp context1)
                              (contextp context2))))
  (if (eq (false-context) context1)
      context2
    (if (eq (false-context) context2)
        context1
      ;; Keep only facts known in both contexts (giving true-context if there is nothing in common):
      (intersection-equal context1 context2))))

(defthm contextp-of-disjoin-contexts
  (implies (and (contextp context1)
                (contextp context2))
           (contextp (disjoin-contexts context1 context2)))
  :hints (("Goal" :in-theory (enable disjoin-contexts CONTEXTP))))

(defthm bounded-contextp-of-disjoin-contexts
  (implies (and (bounded-contextp context1 bound)
                (bounded-contextp context2 bound))
           (bounded-contextp (disjoin-contexts context1 context2) bound))
  :hints (("Goal" :in-theory (enable disjoin-contexts bounded-contextp))))

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

;; (defthmd not-complex-rationalp-of-nth-when-darg-listp
;;   (implies (and (darg-listp args)
;;                 ;(natp n)
;;                 ;(< n (len args))
;;                 )
;;            (not (complex-rationalp (nth n args))))
;;   :hints (("Goal" :in-theory (e/d (bounded-darg-listp nth) (NTH-OF-CDR)))))

;; ;drop?
;; (defthmd not-complex-rationalp-of-nth-of-dargs
;;   (implies (and (dag-exprp expr)
;;                 (< n (len (dargs expr)))
;;                 (natp n)
;;                 (not (equal 'quote (nth 0 expr))))
;;            (not (complex-rationalp (nth n (dargs expr)))))
;;   :hints (("Goal" :in-theory (enable integerp-of-nth-when-darg-listp
;;                                      not-<-of-0-and-nth-when-darg-listp
;;                                      dag-exprp))))

;; while true, this seems bad, because a contextp is a conjunction, not a disjunction
;; (defthm contextp-of-get-axe-disjunction-from-dag-item
;;   (implies (and (not (equal 'quote (car (get-axe-disjunction-from-dag-item nodenum-or-quotep dag-array-name dag-array dag-len))))
;;                 (natp nodenum-or-quotep)
;;                 (< nodenum-or-quotep dag-len)
;;                 (pseudo-dag-arrayp dag-array-name dag-array dag-len))
;;            (contextp (get-axe-disjunction-from-dag-item nodenum-or-quotep dag-array-name dag-array dag-len)))
;;   :hints (("Goal" :use (:instance axe-disjunctionp-of-get-axe-disjunction-from-dag-item)
;;            :in-theory (e/d (axe-disjunctionp)
;;                            (axe-disjunctionp-of-get-axe-disjunction-from-dag-item
;;                             possibly-negated-nodenumsp-when-axe-disjunctionp)))))

(defthm contextp-of-get-axe-conjunction-from-dag-item
  (implies (and (not (equal 'quote (car (get-axe-conjunction-from-dag-item nodenum-or-quotep dag-array-name dag-array dag-len))))
                (natp nodenum-or-quotep)
                (< nodenum-or-quotep dag-len)
                (pseudo-dag-arrayp dag-array-name dag-array dag-len))
           (contextp (get-axe-conjunction-from-dag-item nodenum-or-quotep dag-array-name dag-array dag-len)))
  :hints (("Goal" :use (:instance axe-conjunctionp-of-get-axe-conjunction-from-dag-item)
           :in-theory (e/d (axe-conjunctionp)
                           (axe-conjunctionp-of-get-axe-conjunction-from-dag-item
                            possibly-negated-nodenumsp-when-axe-conjunctionp)))))

;; Returns a contextp that is boolean-equivalent to NODENUM.
(defund context-representing-node (nodenum dag-array-name dag-array dag-len)
  (declare (xargs :guard (and (natp nodenum)
                              (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (< nodenum dag-len))
                  :guard-hints (("Goal" :use (:instance axe-conjunctionp-of-get-axe-conjunction-from-dag-item (nodenum-or-quotep nodenum))
                                 :in-theory (e/d (axe-conjunctionp get-axe-conjunction-from-dag-item)
                                                 (axe-conjunctionp-of-get-axe-conjunction-from-dag-item))))))
  (let ((conjunction (get-axe-conjunction-from-dag-item nodenum dag-array-name dag-array dag-len)))
    (if (quotep conjunction)
        (if (unquote conjunction)
            (true-context)
          (false-context))
      conjunction)))

(defthm contextp-of-context-representing-node
  (implies (and (natp nodenum)
                (< nodenum dag-len)
                (pseudo-dag-arrayp dag-array-name dag-array dag-len))
           (contextp (context-representing-node nodenum dag-array-name dag-array dag-len)))
  :hints (("Goal" :in-theory (enable context-representing-node))))

(defthm bounded-contextp-of-context-representing-node
  (implies (and (natp nodenum)
                (< nodenum dag-len)
                (< nodenum bound)
                (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (natp bound))
           (bounded-contextp (context-representing-node nodenum dag-array-name dag-array dag-len) bound))
  :hints (("Goal" :in-theory (enable contextp context-representing-node))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns a contextp that is boolean-equivalent to the negation of NODENUM.
(defund context-representing-negation-of-node (nodenum dag-array-name dag-array dag-len)
  (declare (xargs :guard (and (natp nodenum)
                              (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (< nodenum dag-len))
                  :guard-hints (("Goal" :use (:instance axe-disjunctionp-of-get-axe-disjunction-from-dag-item (nodenum-or-quotep nodenum))
                                 :in-theory (e/d (axe-disjunctionp)
                                                 (axe-disjunctionp-of-get-axe-disjunction-from-dag-item))))))
  (let ((disjunction (get-axe-disjunction-from-dag-item nodenum dag-array-name dag-array dag-len)))
    (if (quotep disjunction) ;negate it:
        (if (unquote disjunction)
            (false-context)
          (true-context))
      ;;it's a list of nodenums and negations of nodenums:
      (negate-possibly-negated-nodenums disjunction))))

(defthm contextp-of-context-representing-negation-of-node
  (implies (and (natp nodenum)
                (< nodenum dag-len)
                (pseudo-dag-arrayp dag-array-name dag-array dag-len))
           (contextp (context-representing-negation-of-node nodenum dag-array-name dag-array dag-len)))
  :hints (("Goal" :in-theory (enable contextp context-representing-negation-of-node))))

(defthm bounded-contextp-of-context-representing-negation-of-node
  (implies (and (natp nodenum)
                (< nodenum dag-len)
                (< nodenum bound)
                (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (natp bound))
           (bounded-contextp (context-representing-negation-of-node nodenum dag-array-name dag-array dag-len) bound))
  :hints (("Goal" :in-theory (enable contextp context-representing-negation-of-node))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; A context-array maps nodenums to their contexts.
;todo: this failed when contextp was enabled
(def-typed-acl2-array context-arrayp (contextp val) :default (true-context))

;; Recognizes an array whose values are bounded contexts (contexts contaning nodenums less than BOUND).
(def-typed-acl2-array bounded-context-arrayp (bounded-contextp val bound) :default (true-context) :extra-vars (bound) :extra-guards ((natp bound)))

;; this one allows the bound to differ
(defthm bounded-context-arrayp-aux-monotone-gen
  (implies (and (bounded-context-arrayp-aux array-name array n bound2)
                (<= bound2 bound)
                (<= m n)
                (integerp m)
                (integerp n)
                (natp bound)
                (natp bound2))
           (bounded-context-arrayp-aux array-name array m bound))
  :hints (("subgoal *1/3" :use (:instance type-of-aref1-when-bounded-context-arrayp-aux
                                          (index m)
                                          (top-index n)
                                          (bound bound2))
           :in-theory (disable type-of-aref1-when-bounded-context-arrayp-aux))
          ("Goal" :induct (bounded-context-arrayp-aux array-name array m bound)
           :in-theory (enable  bounded-context-arrayp-aux))))

;; this one allows the bound to differ
(defthm bounded-context-arrayp-monotone-gen
  (implies (and (bounded-context-arrayp array-name array n bound2)
                (<= bound2 bound)
                (<= m n)
                (natp m)
                (integerp n)
                (natp bound)
                (natp bound2))
           (bounded-context-arrayp array-name array m bound))
  :hints (("Goal" :in-theory (enable bounded-context-arrayp))))

(defthm context-arrayp-aux-when-bounded-context-arrayp-aux
  (implies (and (bounded-context-arrayp-aux array-name array index2 bound) ; bound is a free var
                (<= index index2)
                (integerp index2))
           (context-arrayp-aux array-name array index))
  :hints (("Goal" :expand (context-arrayp-aux array-name array index)
           :in-theory (enable bounded-context-arrayp-aux
                                     context-arrayp-aux))))

(defthm context-arrayp-when-bounded-context-arrayp
  (implies (and (bounded-context-arrayp array-name array num-valid-indices2 bound) ; bound is a free var
                (<= num-valid-indices num-valid-indices2)
                (natp num-valid-indices))
           (context-arrayp array-name array num-valid-indices))
  :hints (("Goal" :in-theory (enable context-arrayp
                                     bounded-context-arrayp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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
        (if (and (or (eq 'if parent-fn) ; (if/myif/boolif test thenpart elsepart)
                     (eq 'myif parent-fn)
                     (eq 'boolif parent-fn))
                 (= 3 (len (dargs parent-expr)))
                 (atom (darg1 parent-expr))) ;makes sure the test is a nodenum (constants are rare and give no real contextual information)
            (if (and (eql nodenum (darg2 parent-expr))
                     (not (eql nodenum (darg1 parent-expr)))
                     (not (eql nodenum (darg3 parent-expr))))
                ;;nodenum is the then-branch (but not the else-branch or the test), so add the test to the context for nodenum:
                (conjoin-contexts (context-representing-node (darg1 parent-expr) dag-array-name dag-array dag-len)
                                  parent-context)
              (if (and (eql nodenum (darg3 parent-expr))
                       (not (eql nodenum (darg1 parent-expr)))
                       (not (eql nodenum (darg2 parent-expr))))
                  ;;nodenum is the else-branch (but not the then-branch or the test), so add the negation of the test to the context for nodenum:
                  ;;(negate-and-conjoin-to-context (darg1 parent-expr) parent-context dag-array-name dag-array)
                  (conjoin-contexts (context-representing-negation-of-node (darg1 parent-expr) dag-array-name dag-array dag-len)
                                    parent-context)
                ;;nodenum is the test or appears in more than one argument (should be rare), so we don't add anything to the context:
                parent-context))
          (if (and (eq 'bvif parent-fn) ; (bvif size test thenpart elsepart)
                   (= 4 (len (dargs parent-expr)))
                   (atom (darg2 parent-expr))) ;makes sure the test is a nodenum (constants are rare and give no real contextual information)
              (if (and (eql nodenum (darg3 parent-expr))
                       (not (eql nodenum (darg1 parent-expr)))
                       (not (eql nodenum (darg2 parent-expr)))
                       (not (eql nodenum (darg4 parent-expr))))
                  ;;nodenum is the then-branch but not the else-branch (or the test or the size), so add the test to the context:
                  (conjoin-contexts (context-representing-node (darg2 parent-expr) dag-array-name dag-array dag-len)
                                    parent-context)
                (if (and (eql nodenum (darg4 parent-expr))
                         (not (eql nodenum (darg1 parent-expr)))
                         (not (eql nodenum (darg2 parent-expr)))
                         (not (eql nodenum (darg3 parent-expr))))
                    ;;nodenum is the else-branch but not the then-branch (or the test or the size), so add the negation of test to the context:
                    ;;(negate-and-conjoin-to-context (darg2 parent-expr) parent-context dag-array-name dag-array)
                    (conjoin-contexts (context-representing-negation-of-node (darg2 parent-expr) dag-array-name dag-array dag-len)
                                      parent-context)
                  ;; nodenum is the test or size or appears more than once, so we don't add anything to the context:
                  parent-context))
            ;;it's not any kind of IF:
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

(defthm bounded-contextp-of-get-context-via-parent
  (implies (and (natp nodenum)
                (natp parent-nodenum)
                (< nodenum parent-nodenum)
                (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (bounded-context-arrayp 'context-array context-array dag-len bound)
                (< parent-nodenum dag-len)
                (natp bound)
                (< parent-nodenum bound))
           (bounded-contextp (get-context-via-parent nodenum parent-nodenum dag-array-name dag-array dag-len context-array) bound))
  :hints (("Goal" :in-theory (enable get-context-via-parent))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;todo: pull out lemmas proved by induction (about all-> ?)
(defund disjoin-contexts-of-parents (parent-nodenums nodenum dag-array-name dag-array dag-len context-array context-so-far)
  (declare (xargs :guard (and (natp nodenum)
                              (nat-listp parent-nodenums)
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
                (nat-listp parent-nodenums)
                (all-> parent-nodenums nodenum)
                (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (all-< parent-nodenums dag-len)
                (context-arrayp 'context-array context-array dag-len)
                (contextp context-so-far))
           (contextp (disjoin-contexts-of-parents parent-nodenums nodenum dag-array-name dag-array dag-len context-array context-so-far)))
  :hints (("Goal" :in-theory (e/d (disjoin-contexts-of-parents) (pseudo-dag-arrayp)))))

(defthm bounded-contextp-of-disjoin-contexts-of-parents
  (implies (and (natp nodenum)
                (nat-listp parent-nodenums)
                (all-> parent-nodenums nodenum)
                (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (all-< parent-nodenums dag-len)
                (all-< parent-nodenums bound)
                (bounded-context-arrayp 'context-array context-array dag-len bound)
                (bounded-contextp context-so-far bound)
                (natp bound))
           (bounded-contextp (disjoin-contexts-of-parents parent-nodenums nodenum dag-array-name dag-array dag-len context-array context-so-far) bound))
  :hints (("Goal" :in-theory (e/d (disjoin-contexts-of-parents) (pseudo-dag-arrayp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;move the aset out of this function?
;;todo: pull out lemmas proved by induction
(defund set-context-of-nodenum (nodenum parent-nodenums dag-array-name dag-array dag-len context-array)
  (declare (xargs :guard (and (natp nodenum)
                              (nat-listp parent-nodenums)
                              (all-> parent-nodenums nodenum)
                              (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (< nodenum dag-len)
                              (all-< parent-nodenums dag-len)
                              (context-arrayp 'context-array context-array dag-len))
                  :guard-hints (("Goal" :in-theory (enable all-> cadr-becomes-nth-of-1 car-becomes-nth-of-0 context-arrayp)))))
  (if (endp parent-nodenums)
      (prog2$ (cw "!! nodenum ~x0 is an orphan !!~%" nodenum)
              (aset1 'context-array context-array nodenum (false-context)))
    (let* ((context-via-first-parent (get-context-via-parent nodenum (first parent-nodenums) dag-array-name dag-array dag-len context-array)) ;could start here with a context of (false-context)? and eliminate the check above
           (context (disjoin-contexts-of-parents (rest parent-nodenums) nodenum dag-array-name dag-array dag-len context-array context-via-first-parent)))
      (aset1 'context-array context-array nodenum context))))

;; (defthmd <-of-car-when-all->
;;   (implies (and (all-> parent-nodenums nodenum)
;;                 (consp parent-nodenums))
;;            (< nodenum (car parent-nodenums))))

(defthm context-arrayp-of-set-context-of-nodenum
  (implies (and (context-arrayp 'context-array context-array len)
                (natp nodenum)
                ;(< nodenum len)
                (nat-listp parent-nodenums)
                (all-> parent-nodenums nodenum)
                (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (< nodenum dag-len)
                (all-< parent-nodenums dag-len)
                (context-arrayp 'context-array context-array dag-len))
           (context-arrayp 'context-array (set-context-of-nodenum nodenum parent-nodenums dag-array-name dag-array dag-len context-array) len))
  :hints (("Goal" :in-theory (enable set-context-of-nodenum))))

(defthm bounded-context-arrayp-of-set-context-of-nodenum
  (implies (and (bounded-context-arrayp 'context-array context-array dag-len bound)
                (natp nodenum)
                ;(< nodenum len)
                (nat-listp parent-nodenums)
                (all-> parent-nodenums nodenum)
                (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (< nodenum dag-len)
                (all-< parent-nodenums dag-len)
                (all-< parent-nodenums bound)
                ;(context-arrayp 'context-array context-array dag-len)
                (natp bound))
           (bounded-context-arrayp 'context-array (set-context-of-nodenum nodenum parent-nodenums dag-array-name dag-array dag-len context-array) dag-len bound))
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Go top-down from NODENUM, filling in the CONTEXT-ARRAY.  Assumes we started at the top node and so will cover all ways a node can be reached from the top.
;; Returns the context-array, named 'context-array, which associates nodenums with their contextps.
;; It might seem faster to just take the dag as a list and cdr down it, but we need the dag to be an array so we can quickly dig conjuncts out of dag nodes.
(defund make-full-context-array-aux (nodenum dag-array-name dag-array dag-len dag-parent-array context-array)
  (declare (xargs :guard (and (integerp nodenum)
                              (<= -1 nodenum)
                              (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (dag-parent-arrayp 'dag-parent-array dag-parent-array)
                              (context-arrayp 'context-array context-array dag-len)
                              ;; not necesarly equal:
                              (<= dag-len (alen1 'dag-parent-array dag-parent-array))
                              (bounded-dag-parent-entriesp (+ -1 dag-len) 'dag-parent-array dag-parent-array dag-len)
                              (< nodenum dag-len))
                  :guard-hints (("Goal" :in-theory (e/d (<-of-+-of-1-strengthen-2 DAG-PARENT-ARRAYP) (PSEUDO-DAG-ARRAYP))))
                  :measure (nfix (+ 1 nodenum))
                  :split-types t)
           (type (integer -1 1152921504606846973) nodenum))
  (if (mbe :logic (not (natp nodenum))
           :exec (equal -1 nodenum))
      context-array
    (let* ((parents (aref1 'dag-parent-array dag-parent-array nodenum))
           (context-array (set-context-of-nodenum nodenum parents dag-array-name dag-array dag-len context-array)))
      (make-full-context-array-aux (+ -1 nodenum) dag-array-name dag-array dag-len dag-parent-array context-array))))

(defthm array1p-of-make-full-context-array-aux
  (implies (and (array1p 'context-array context-array)
                (< nodenum (alen1 'context-array context-array)))
           (array1p 'context-array (make-full-context-array-aux nodenum dag-array-name dag-array dag-len dag-parent-array context-array)))
  :hints (("Goal" :in-theory (enable make-full-context-array-aux))))

(defthm alen1-of-make-full-context-array-aux
  (implies (and (array1p 'context-array context-array)
                (< nodenum (alen1 'context-array context-array)))
           (equal (alen1 'context-array (make-full-context-array-aux nodenum dag-array-name dag-array dag-len dag-parent-array context-array))
                  (alen1 'context-array context-array)))
    :hints (("Goal" :in-theory (enable make-full-context-array-aux))))

(defthm context-arrayp-of-make-full-context-array-aux
  (implies (and (integerp nodenum)
                (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (dag-parent-arrayp 'dag-parent-array dag-parent-array)
                (context-arrayp 'context-array context-array dag-len)
                ;; not necesarly equal:
                (<= dag-len (alen1 'dag-parent-array dag-parent-array))
                (bounded-dag-parent-entriesp (+ -1 dag-len) 'dag-parent-array dag-parent-array dag-len)
                (< nodenum dag-len))
           (context-arrayp 'context-array (make-full-context-array-aux nodenum dag-array-name dag-array dag-len dag-parent-array context-array) dag-len))
  :hints (("Goal" :in-theory (enable make-full-context-array-aux len-when-pseudo-dagp))))

(defthm bounded-context-arrayp-of-make-full-context-array-aux
  (implies (and (integerp nodenum)
                (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (dag-parent-arrayp 'dag-parent-array dag-parent-array)
                (bounded-context-arrayp 'context-array context-array dag-len bound)
                ;; not necesarly equal:
                (<= dag-len (alen1 'dag-parent-array dag-parent-array))
                (bounded-dag-parent-arrayp 'dag-parent-array dag-parent-array dag-len)
                (<= dag-len bound)
                (< nodenum dag-len)
                (natp bound))
           (bounded-context-arrayp 'context-array
                                   (make-full-context-array-aux nodenum dag-array-name dag-array dag-len dag-parent-array context-array)
                                   dag-len
                                   bound))
  :hints (("Goal" :in-theory (enable make-full-context-array-aux
                                     len-when-pseudo-dagp
                                     ))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns an array, named 'context-array, which associates nodenums with their contextps.
;; Note that we need the dag to be an array so we can quickly dig conjuncts out of dag nodes.
;; Use make-full-context-array instead if you don't already have the dag-parent-array.
(defun make-full-context-array-with-parents (dag-array-name dag-array dag-len dag-parent-array)
  (declare (xargs :guard (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (posp dag-len)
                              (<= dag-len *max-1d-array-length*)
                              (dag-parent-arrayp 'dag-parent-array dag-parent-array)
                              ;; not necesarly equal:
                              (<= dag-len (alen1 'dag-parent-array dag-parent-array))
                              (bounded-dag-parent-entriesp (+ -1 dag-len) 'dag-parent-array dag-parent-array dag-len))
                  :guard-hints (("Goal" :in-theory (enable dag-parent-arrayp)))))
  (let* (;; All nodes initially have a context of "true" but all contexts except that of the top node get overwritten as we go:
         (context-array (make-empty-array-with-default 'context-array dag-len (true-context)))
         (top-nodenum (+ -1 dag-len))
         ;; (context-array (aset1 'context-array context-array top-nodenum (true-context))) ;top node has no context
         (context-array (make-full-context-array-aux (+ -1 top-nodenum) ; skip the top node
                                                     dag-array-name
                                                     dag-array
                                                     dag-len
                                                     dag-parent-array
                                                     context-array)))
    context-array))

(defthm context-arrayp-of-make-full-context-array-with-parents
  (implies (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (posp dag-len)
                (dag-parent-arrayp 'dag-parent-array dag-parent-array)
                ;; not necesarly equal:
                (<= dag-len (alen1 'dag-parent-array dag-parent-array))
                (bounded-dag-parent-entriesp (+ -1 dag-len) 'dag-parent-array dag-parent-array dag-len))
           (context-arrayp 'context-array (make-full-context-array-with-parents dag-array-name dag-array dag-len dag-parent-array) dag-len))
  :hints (("Goal" :in-theory (enable make-full-context-array-with-parents))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;new version! deprecate the old way of doing things (already done?)?
; Returns 'context-array, which associates nodenums with their contextps ("full" means all nodes have a valid entry in this array).
; Smashes 'dag-parent-array.
;; Use make-full-context-array-with-parents instead if you already have the parent array.
(defun make-full-context-array (dag-array-name dag-array dag-len)
  (declare (xargs :guard (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (posp dag-len))))
  (make-full-context-array-with-parents dag-array-name
                                        dag-array
                                        dag-len
                                        (make-minimal-dag-parent-array-with-name dag-len ; somewhat unusual not to use (alen1 dag-array-name dag-array) here, but this array doesn't need to grow after creation
                                                                                 dag-array-name
                                                                                 dag-array
                                                                                 'dag-parent-array)))

(defthm context-arrayp-of-make-full-context-array
  (implies (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (posp dag-len))
           (context-arrayp 'context-array (make-full-context-array dag-array-name dag-array dag-len) dag-len))
  :hints (("Goal" :in-theory (enable make-full-context-array))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns an array named 'context-array which associates nodenums with their
;; contexts ("full" means all nodes have a valid entry in this array).  Can
;; help with debugging.
(defund make-full-context-array-for-dag (dag)
  (declare (xargs :guard (and (pseudo-dagp dag)
                              (<= (len dag) *max-1d-array-length*))
                  :guard-hints (("Goal" :in-theory (enable len-when-pseudo-dagp)))))
  (let* ((dag-array-name 'temp-dag-array)
         (dag-array (make-into-array 'temp-dag-array dag)))
    (make-full-context-array dag-array-name dag-array (+ 1 (top-nodenum-of-dag dag)))))

;; TODO: Improve to match better
(defthm context-arrayp-of-make-full-context-array-for-dag
  (implies (and (pseudo-dagp dag)
                (<= (len dag) *max-1d-array-length*))
           (context-arrayp 'context-array (make-full-context-array-for-dag dag) (+ 1 (top-nodenum-of-dag dag))))
  :hints (("Goal" :in-theory (enable make-full-context-array-for-dag))))

(defthm bounded-context-arrayp-of-make-full-context-array-for-dag
  (implies (and (pseudo-dagp dag)
                (<= (len dag) *max-1d-array-length*)
                (<= (len dag) bound)
                (natp bound))
           (bounded-context-arrayp 'context-array (make-full-context-array-for-dag dag) (len dag) bound))
  :hints (("Goal" :in-theory (enable make-full-context-array-for-dag))))

(defthm bounded-context-arrayp-of-make-full-context-array-for-dag-gen
  (implies (and (pseudo-dagp dag)
                (<= (len dag) *max-1d-array-length*)
                (<= (len dag) bound)
                (natp bound)
                (<= num-valid-indices (len dag))
                (natp num-valid-indices))
           (bounded-context-arrayp 'context-array (make-full-context-array-for-dag dag) num-valid-indices bound))
  :hints (("Goal" :use (:instance bounded-context-arrayp-of-make-full-context-array-for-dag)
           :in-theory (disable bounded-context-arrayp-of-make-full-context-array-for-dag))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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
(defund context-item-to-maybe-expr (context-item dag-array dag-len)
  (declare (xargs :guard (and (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                              (bounded-possibly-negated-nodenump context-item dag-len)))
           (ignore dag-len) ; only use in the guard
           )
  (if (atom context-item)
      ;; it's a nodenum, so look it up:
      (let ((expr (aref1 'dag-array dag-array context-item)))
        (if (or (symbolp expr)
                (quotep expr))
            nil ;not a suitable function call expr, so drop it
          expr))
    ;; it's of the form (not <nodenum>), so it is already a suitable expr
    context-item))

(defthm dag-function-call-exprp-of-context-item-to-maybe-expr
  (implies (and (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (bounded-possibly-negated-nodenump context-item dag-len)
                (context-item-to-maybe-expr context-item dag-array dag-len) ; since it is a maybe-...
                )
           (dag-function-call-exprp (context-item-to-maybe-expr context-item dag-array dag-len)))
  :hints (("Goal" :in-theory (enable context-item-to-maybe-expr bounded-possibly-negated-nodenump))))

;;Turns a context into exprs that are function calls applied to nodenums /
;;quoteps.  Items in the context that map to variables or constants are dropped (todo: so rename this).
(defund context-to-exprs (context ; a possibly-negated-nodenumsp
                          dag-array
                          dag-len)
  (declare (xargs :guard (and (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                              (bounded-possibly-negated-nodenumsp context dag-len))))
  (if (endp context)
      nil
    (let* ((context-item (first context))
           (maybe-expr (context-item-to-maybe-expr context-item dag-array dag-len)))
      (if maybe-expr
          (cons maybe-expr (context-to-exprs (rest context) dag-array dag-len))
        (context-to-exprs (rest context) dag-array dag-len)))))

(defthm context-to-exprs-of-nil
  (equal (context-to-exprs nil dag-array dag-len)
         nil)
  :hints (("Goal" :in-theory (enable context-to-exprs))))

(defthm all-dag-function-call-exprp-of-context-to-exprs
  (implies (and (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (bounded-possibly-negated-nodenumsp context dag-len))
           (all-dag-function-call-exprp (context-to-exprs context dag-array dag-len)))
  :hints (("Goal" :in-theory (e/d (context-to-exprs) (dag-function-call-exprp-redef)))))

(local
  (defthm bounded-dag-exprp-when-bounded-possibly-negated-nodenump
    (implies (and (bounded-possibly-negated-nodenump item dag-len)
                  (consp item))
             (bounded-dag-exprp dag-len item))
    :hints (("Goal" :in-theory (enable bounded-possibly-negated-nodenump
                                       bounded-dag-exprp)))))

(defthm bounded-dag-expr-listp-of-context-to-exprs
  (implies (and (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (bounded-possibly-negated-nodenumsp context dag-len))
           (bounded-dag-expr-listp dag-len (context-to-exprs context dag-array dag-len)))
  :hints (("Goal" :in-theory (enable context-to-exprs bounded-contextp
                                     bounded-possibly-negated-nodenumsp
                                     context-item-to-maybe-expr))))

;; ;; Returns nil but prints.
;; (defun print-contexts (dag-lst)
;;   (declare (xargs :guard (and (pseudo-dagp dag-lst)
;;                               (< (len dag-lst) 1152921504606846973))
;;                   :guard-hints (("Goal" :in-theory (e/d (pseudo-dagp) (pseudo-dag-arrayp))))))
;;   (prog2$ (cw "(Computing contexts:~%")
;;           (let* ((dag-len (len dag-lst))
;;                  (dag-array (make-into-array 'dag-array dag-lst))
;;                  (context-array (make-full-context-array 'dag-array dag-array dag-len)))
;;             (prog2$ (cw ")~%")
;;                     (print-array 'context-array context-array dag-len)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
  (defthm eqlablep-when-natp
    (implies (natp x)
             (eqlablep x))))

(local (include-book "kestrel/lists-light/cdr" :dir :system))

(defund dag-expr-gives-rise-to-contextp (expr)
  (declare (xargs :guard (dag-exprp expr)
                  :guard-hints (("Goal" :in-theory (enable CONSP-OF-CDR)))
                  ))
  (and (consp expr) ; not a var
       (let ((fn (ffn-symb expr)))
         (case fn
           ((if myif boolif) ; (if/myif/boolif test thenpart elsepart)
            (and (consp (rest (rest (dargs expr))))
                 (let ((test (darg1 expr))
                       (then (darg2 expr))
                       (else (darg3 expr)))
                   (and (atom test) ; test must not be constant
                        (or (and (atom then)
                                 (not (eql then test))
                                 (not (eql then else)))
                            (and (atom else)
                                 (not (eql else test))
                                 (not (eql else then))
                                 ))))))
           (bvif ; (bvif size test thenpart elsepart)
             (and (consp (rest (rest (rest (dargs expr)))))
                  (let ((size (darg1 expr))
                        (test (darg2 expr))
                        (then (darg3 expr))
                        (else (darg4 expr)))
                    (and (atom test) ; test must not be constant
                         (or (and (atom then)
                                  (not (eql then test))
                                  (not (eql then size))
                                  (not (eql then else)))
                             (and (atom else)
                                  (not (eql else test))
                                  (not (eql else size))
                                  (not (eql else then))
                                  ))))))
           (otherwise nil)))))

;; Checks whether an internal-context array built for DAG will have anything non-trivial in it
;; If this is false, we can skip building a context array.
(defund dag-has-internal-contextsp (dag)
  (declare (xargs :guard (weak-dagp-aux dag)))
  (if (endp dag)
      nil
    (or (dag-expr-gives-rise-to-contextp (cdr (first dag)))
        (dag-has-internal-contextsp (rest dag)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund non-negated-nodenums-in-context (context)
  (declare (xargs :guard (non-false-contextp context)))
  (if (endp context)
      nil
    (let ((item (first context)))
      (if (consp item) ; checks if item is negated
          (non-negated-nodenums-in-context (rest context))
        (cons item (non-negated-nodenums-in-context (rest context)))))))

(defund negated-nodenums-in-context (context)
  (declare (xargs :guard (non-false-contextp context)))
  (if (endp context)
      nil
    (let ((item (first context)))
      (if (consp item) ; checks if item is negated
          (cons item (negated-nodenums-in-context (rest context)))
        (negated-nodenums-in-context (rest context))))))
