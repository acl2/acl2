; Proofs of properties of make-lambda-application-simple
;
; Copyright (C) 2013-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/evaluators/empty-eval" :dir :system)
(include-book "make-lambda-application-simple")
(include-book "no-nils-in-termp")
(include-book "kestrel/alists-light/map-lookup-equal" :dir :system) ; make local?
(include-book "kestrel/alists-light/alists-equiv-on" :dir :system)
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
(local (include-book "kestrel/utilities/equal-of-booleans" :dir :system))

;; TODO: Clean up and harvest this file

(local (in-theory (disable alistp no-duplicatesp-equal)))

;move to library
(defthmd intersection-equal-of-set-difference-equal-when-subsetp-equal
  (implies (subsetp-equal z y)
           (equal (intersection-equal (set-difference-equal x y) z)
                  nil))
  :hints (("Goal" :in-theory (enable intersection-equal set-difference-equal))))

;; todo: move, dup in letify
(defthm subsetp-equal-of-append-of-intersection-equal-and-set-difference-equal-swapped
  (subsetp-equal x
                 (append (intersection-equal y x)
                         (set-difference-equal x y)))
  :hints (("Goal" :in-theory (enable subsetp-equal intersection-equal set-difference-equal))))


;todo: nested induction
;; (thm
;;  (equal (INTERSECTION-EQUAL (SET-DIFFERENCE-EQUAL vars FORMALS)
;;                             (MV-NTH 0 (FILTER-FORMALS-AND-ACTUALS FORMALS ACTUALS var)))
;;         nil)
;;  :hints (("Goal" :in-theory (enable FILTER-FORMALS-AND-ACTUALS))))

;move or gen to a subsetp fact, or gen the second x to z
(defthm intersection-equal-of-intersection-equal-and-intersection-equal-swapped
  (equal (intersection-equal (intersection-equal x y)
                             (intersection-equal y x))
         (intersection-equal x y))
  :hints (("Goal" ;:induct (intersection-equal y x)
           :in-theory (enable intersection-equal))))

(defthm equal-of-cons-of-cdr-of-assoc-equal-and-assoc-equal-iff
  (implies (alistp a)
           (iff (equal (cons key (cdr (assoc-equal key a)))
                       (assoc-equal key a))
                (assoc-equal key a)))
  :hints (("Goal" :in-theory (enable assoc-equal alistp))))

(defthm cdr-of-assoc-equal-of-pairlis$-of-map-lookup-equal
  (implies (and (member-equal key keys)
                ;(assoc-equal key a)
                (alistp a))
           (equal (cdr (assoc-equal key (pairlis$ keys (map-lookup-equal keys a))))
                  (cdr (assoc-equal key a))))
  :hints (("Goal" :in-theory (enable pairlis$
                                     map-lookup-equal
                                     LOOKUP-EQUAL ;todo
                                     ))))

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

(defthm-flag-free-vars-in-term
  ;; If the alists agree on some set of keys that includes all the free vars in the term,
  ;; the the evaluations give the same result.
  (defthm equal-of-empty-eval-and-empty-eval-when-alists-equiv-on-alt ; todo: similar to one in the proof of expand-lambdas
    (implies (and (alists-equiv-on keys alist1 alist2)
                  (subsetp-equal (free-vars-in-term term) keys)
                  (pseudo-termp term))
             (equal (equal (empty-eval term alist1)
                           (empty-eval term alist2))
                    t))
    :flag free-vars-in-term)
  (defthm equal-of-empty-eval-list-and-empty-eval-list-when-alists-equiv-on-alt
    (implies (and (alists-equiv-on keys alist1 alist2)
                  (subsetp-equal (free-vars-in-terms terms) keys)
                  (pseudo-term-listp terms))
             (equal (equal (empty-eval-list terms alist1)
                           (empty-eval-list terms alist2))
                    t))
    :flag free-vars-in-terms)
  :hints (("Goal" :expand (free-vars-in-terms term)
           :in-theory (e/d (empty-eval-of-fncall-args)
                           (empty-eval-of-fncall-args-back)))))

(defthm equal-of-empty-eval-and-empty-eval-when-alists-equiv-on-special
  (implies (and (alists-equiv-on (free-vars-in-term term) alist1 alist2)
                (pseudo-termp term))
           (equal (equal (empty-eval term alist1)
                         (empty-eval term alist2))
                  t)))

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

(defthm mv-nth-1-of-FILTER-FORMALS-AND-ACTUALS
  (implies (no-duplicatesp-equal formals)
           (equal (mv-nth 1 (filter-formals-and-actuals formals actuals vars))
                  (map-lookup-equal (intersection-equal formals vars)
                                    (pairlis$ formals actuals))))
  :hints (("Goal" :in-theory (enable FILTER-FORMALS-AND-ACTUALS
                                     INTERSECTION-EQUAL
                                     map-lookup-equal
                                     PAIRLIS$) )))


(defthm EMPTY-EVAL-of-LOOKUP-EQUAL-of-pairlis$
  (EQUAL (EMPTY-EVAL (LOOKUP-EQUAL key (PAIRLIS$ FORMALS ACTUALS)) A)
         (LOOKUP-EQUAL key (PAIRLIS$ FORMALS (EMPTY-EVAL-LIST ACTUALS A))))
  :hints (("Goal" :in-theory (enable map-lookup-equal lookup-equal assoc-equal pairlis$))))

(defthm empty-eval-list-of-map-LOOKUP-EQUAL-of-pairlis$
  (equal (EMPTY-EVAL-LIST (MAP-LOOKUP-EQUAL keys (PAIRLIS$ FORMALS ACTUALS)) A)
         (MAP-LOOKUP-EQUAL keys (PAIRLIS$ FORMALS (EMPTY-EVAL-LIST ACTUALS a))))
  :hints (("Goal" :in-theory (enable map-lookup-equal))))

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

(include-book "lambdas-closed-in-termp")

(defthm lambdas-closed-in-termp-of-make-lambda-application-simple
  (implies (and (pseudo-termp body)
                (symbol-listp formals)
                (pseudo-term-listp actuals))
           (equal (lambdas-closed-in-termp (make-lambda-application-simple formals actuals body))
                  (and (lambdas-closed-in-termsp (mv-nth 1 (filter-formals-and-actuals formals actuals (free-vars-in-term body))))
                       (lambdas-closed-in-termp body))))
  :hints (("Goal" :do-not-induct t
           :in-theory (enable make-lambda-application-simple
                              lambdas-closed-in-termp ;todo
                              ))))

(defthm no-nils-in-termp-of-make-lambda-application-simple
  (implies (and (pseudo-termp body)
                (symbol-listp formals)
                (pseudo-term-listp actuals))
           (equal (no-nils-in-termp (make-lambda-application-simple formals actuals body))
                  (and (no-nils-in-termsp (mv-nth 1 (filter-formals-and-actuals formals actuals (free-vars-in-term body))))
                       (no-nils-in-termp body))))
  :hints (("Goal" :do-not-induct t
           :in-theory (enable make-lambda-application-simple
                              no-nils-in-termp ;todo
                              ))))
