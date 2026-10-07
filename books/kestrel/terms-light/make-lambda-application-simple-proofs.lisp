; Proofs of properties of make-lambda-application-simple
;
; Copyright (C) 2013-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/evaluators/empty-eval" :dir :system)
(include-book "make-lambda-application-simple")
(include-book "no-nils-in-termp")
(include-book "lambdas-closed-in-termp")
(include-book "no-duplicate-lambda-formals-in-termp")
(include-book "kestrel/alists-light/map-lookup-equal" :dir :system) ; make local?
(include-book "kestrel/alists-light/alists-equiv-on" :dir :system)
(local (include-book "filter-formals-and-actuals-proofs"))
(local (include-book "empty-eval-helpers"))
(local (include-book "helpers"))
(local (include-book "kestrel/evaluators/empty-eval-theorems" :dir :system))
(local (include-book "kestrel/alists-light/pairlis-dollar" :dir :system))
(local (include-book "kestrel/alists-light/assoc-equal" :dir :system))
(local (include-book "kestrel/alists-light/strip-cars" :dir :system))
(local (include-book "kestrel/typed-lists-light/symbol-listp" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/nthcdr" :dir :system))
(local (include-book "kestrel/lists-light/subsetp-equal" :dir :system))
(local (include-book "kestrel/lists-light/intersection-equal" :dir :system))
(local (include-book "kestrel/lists-light/member-equal" :dir :system))
(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))
(local (include-book "kestrel/lists-light/take" :dir :system))
(local (include-book "kestrel/lists-light/set-difference-equal" :dir :system))
(local (include-book "kestrel/lists-light/no-duplicatesp-equal" :dir :system))
(local (include-book "kestrel/lists-light/list-sets" :dir :system))
(local (include-book "kestrel/utilities/equal-of-booleans" :dir :system))

;; TODO: Clean up and harvest this file


;todo: nested induction
;; (thm
;;  (equal (INTERSECTION-EQUAL (SET-DIFFERENCE-EQUAL vars FORMALS)
;;                             (MV-NTH 0 (FILTER-FORMALS-AND-ACTUALS FORMALS ACTUALS var)))
;;         nil)
;;  :hints (("Goal" :in-theory (enable FILTER-FORMALS-AND-ACTUALS))))

(defthm equal-of-cons-of-cdr-of-assoc-equal-and-assoc-equal-iff
  (implies (alistp a)
           (iff (equal (cons key (cdr (assoc-equal key a)))
                       (assoc-equal key a))
                (assoc-equal key a)))
  :hints (("Goal" :in-theory (enable assoc-equal alistp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm empty-eval-of-append-of-pairlis$-of-EMPTY-EVAL-LIST-when-relevant-actuals-are-formals
  (implies (and ;; the relevant actuals are all vars (unusual!):
            (equal (mv-nth 0 (filter-formals-and-actuals formals actuals (free-vars-in-term body)))
                   (mv-nth 1 (filter-formals-and-actuals formals actuals (free-vars-in-term body))))
            (pseudo-termp body)
            (no-nils-in-termp body)
            (symbol-listp formals)
            (no-duplicatesp-equal formals)
            (pseudo-term-listp actuals)
            (equal (len formals)
                   (len actuals)))
           (equal (empty-eval body (append (pairlis$ formals (empty-eval-list actuals a)) a))
                  (empty-eval body a)))
  :hints (("Goal" :in-theory (enable filter-formals-and-actuals
                                     pairlis$
                                     symbolp-when-member-equal-and-symbol-listp))))



;; (thm
;;  (implies (and (alistp a)
;;                (subsetp-equal keys (strip-cars a)))
;;           (alists-equiv-on keys (pairlis$ keys (map-lookup-equal keys a)) a))
;;  :hints (("Goal"  :induct (map-lookup-equal keys a)
;;           :in-theory (enable alists-equiv-on pairlis$ lookup-equal))))

(defthm assoc-equal-of-car-when-subsetp-equal-of-strip-cars
  (implies (and (subsetp-equal keys (strip-cars a))
                (consp keys)
                (alistp a))
           (assoc-equal (car keys) a))
  :hints (("Goal" :in-theory (enable assoc-equal-iff-member-equal-of-strip-cars))))

(defthm alists-equiv-on-of-pairlis$-of-map-lookup-equal
  (implies (and (alistp a)
;                (subsetp-equal keys keys2)
                ;(subsetp-equal keys (strip-cars a))
                )
           (alists-equiv-on keys (pairlis$ keys (map-lookup-equal keys a)) a))
  :hints (("Goal"  :induct (map-lookup-equal keys a)
           :in-theory (enable alists-equiv-on pairlis$
                              map-lookup-equal lookup-equal))))

(defthm alists-equiv-on-of-pairlis$-of-map-lookup-equal-gen
  (implies (and (alistp a)
                (subsetp-equal keys keys2)
                ;(subsetp-equal keys (strip-cars a))
                )
           (alists-equiv-on keys (pairlis$ keys2 (map-lookup-equal keys2 a)) a))
  :hints (("Goal"  :induct (map-lookup-equal keys a)
           :in-theory (enable alists-equiv-on pairlis$
                              map-lookup-equal lookup-equal))))

(defthm intersection-equal-of-set-difference-equal-arg1-when-subsetp-equal
  (implies (subsetp-equal z y)
           (equal (intersection-equal (set-difference-equal x y)
                                      z)
                  nil))
  :hints (("Goal" :in-theory (enable subsetp-equal intersection-equal))))

;; (thm
;;  (equal (INTERSECTION-EQUAL (SET-DIFFERENCE-EQUAL x y)
;;                             (INTERSECTION-EQUAL y z))
;;         nil))

;; Correctness theorem for make-lambda-application-simple
(defthm empty-eval-of-make-lambda-application-simple-correct-1
  (implies (and (pseudo-termp body)
                (no-nils-in-termp body)
                (symbol-listp formals)
                (no-duplicatesp-equal formals)
                (pseudo-term-listp actuals)
                (equal (len formals)
                       (len actuals))
                (alistp a))
           (equal (empty-eval (make-lambda-application-simple formals actuals body) a)
                  (empty-eval body (append (pairlis$ formals (empty-eval-list actuals a))
                                           a))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable alists-equiv-on
                              make-lambda-application-simple
                              intersection-equal-of-set-difference-equal-when-subsetp-equal))))

;true of any evaluator
;move or drop?
(defthm equal-of-empty-eval-and-empty-eval-when-not-consp-of-free-vars-in-term
  (implies (and (not (consp (free-vars-in-term body)))
                (pseudo-termp body))
           (equal (equal (empty-eval body a2)
                         (empty-eval body a1))
                  t))
  :hints (("Goal" :in-theory (enable alists-equiv-on))))

;; (thm
;;  (IMPLIES (and (SUBSETP-EQUAL (FREE-VARS-IN-TERM BODY)
;;                               (strip-cars a1))
;;                (pseudo-termp body) ;drop?
;;                (alistp a1)
;;                (alistp a2)
;;                )
;;           (EQUAL (EMPTY-EVAL BODY (APPEND a1 a2))
;;                  (EMPTY-EVAL BODY a1)))
;; ; :hints (("Goal" :in-theory (enable strip-cars SUBSETP-EQUAL append)))
;;  )

;; Special case for when the formals include all the free vars in the body,
;; as often will be the case (e.g., when processing an existing [closed] lambda).
(defthm empty-eval-of-make-lambda-application-simple-correct-2
  (implies (and (subsetp-equal (free-vars-in-term body) formals) ; this case
                (pseudo-termp body)
                (no-nils-in-termp body)
                (symbol-listp formals)
                (no-duplicatesp-equal formals)
                (pseudo-term-listp actuals)
                (equal (len formals)
                       (len actuals))
                (alistp a))
           (equal (empty-eval (make-lambda-application-simple formals actuals body) a)
                  (empty-eval body (pairlis$ formals (empty-eval-list actuals a)))))
  :hints (("Goal" :in-theory (enable ;alists-equiv-on ;why?
                                     ))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm lambdas-closed-in-termp-of-make-lambda-application-simple
  (implies (and (pseudo-termp body)
                (symbol-listp formals)
                (pseudo-term-listp actuals))
           (equal (lambdas-closed-in-termp (make-lambda-application-simple formals actuals body))
                  (and (lambdas-closed-in-termsp (mv-nth 1 (filter-formals-and-actuals formals actuals (free-vars-in-term body))))
                       (lambdas-closed-in-termp body))))
  :hints (("Goal" :do-not-induct t
           :in-theory (enable make-lambda-application-simple))))

(defthm no-nils-in-termp-of-make-lambda-application-simple
  (implies (and (pseudo-termp body)
                (symbol-listp formals)
                (pseudo-term-listp actuals))
           (equal (no-nils-in-termp (make-lambda-application-simple formals actuals body))
                  (and (no-nils-in-termsp (mv-nth 1 (filter-formals-and-actuals formals actuals (free-vars-in-term body))))
                       (no-nils-in-termp body))))
  :hints (("Goal" :do-not-induct t
           :in-theory (enable make-lambda-application-simple))))

(defthm no-duplicate-lambda-formals-in-termp-of-make-lambda-application-simple
  (implies (and (pseudo-termp body)
                (no-duplicate-lambda-formals-in-termp body)
                (symbol-listp formals)
                (no-duplicatesp-equal formals)
                (pseudo-term-listp actuals)
                (no-duplicate-lambda-formals-in-termsp actuals)
                (equal (len formals) (len actuals)))
           (no-duplicate-lambda-formals-in-termp (make-lambda-application-simple formals actuals body)))
  :hints (("Goal" :in-theory (e/d (make-lambda-application-simple
                                   no-duplicate-lambda-formals-in-termp)
                                  (mv-nth-0-of-filter-formals-and-actuals len)))))
