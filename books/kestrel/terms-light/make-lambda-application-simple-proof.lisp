; A lightweight book about TODO.
;
; Copyright (C) 2013-2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/evaluators/empty-eval" :dir :system)
(include-book "make-lambda-application-simple")
(include-book "no-nils-in-termp")
(include-book "kestrel/alists-light/lookup-equal" :dir :system) ; make local?
(include-book "kestrel/alists-light/alists-equiv-on" :dir :system)
(local (include-book "kestrel/alists-light/pairlis-dollar" :dir :system))
(local (include-book "kestrel/alists-light/assoc-equal" :dir :system))
(local (include-book "kestrel/alists-light/strip-cars" :dir :system))
(local (include-book "kestrel/typed-lists-light/symbol-listp" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/nthcdr" :dir :system))
(local (include-book "kestrel/lists-light/subsetp-equal" :dir :system))
(local (include-book "kestrel/lists-light/intersection-equal" :dir :system))
(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))
(local (include-book "kestrel/lists-light/take" :dir :system))
(local (include-book "kestrel/lists-light/set-difference-equal" :dir :system))
(local (include-book "kestrel/lists-light/no-duplicatesp-equal" :dir :system))
(local (include-book "kestrel/utilities/equal-of-booleans" :dir :system))

;; TODO: Clean up and harvest this file

(local (in-theory (disable alistp)))

;; todo: add this to defevaluator+
(defthm-flag-free-vars-in-term
  ;; Bind a variable in the alist has no effect if it is not one of the free vars in the term.
  (defthm empty-eval-of-cons-irrel
    (implies (and (not (member-equal var (free-vars-in-term term)))
                  (pseudo-termp term))
             (equal (empty-eval term (cons (cons var val) a))
                    (empty-eval term a)))
    :flag free-vars-in-term)
  (defthm empty-eval-list-of-cons-irrel
    (implies (and (not (member-equal var (free-vars-in-terms terms)))
                  (pseudo-term-listp terms))
             (equal (empty-eval-list terms (cons (cons var val) a))
                    (empty-eval-list terms a)))
    :flag free-vars-in-terms)
  :hints (("Goal" :in-theory (e/d (empty-eval-of-fncall-args)
                                  (empty-eval-of-fncall-args-back)))))

;; todo: add this to defevaluator+
(defthm-flag-free-vars-in-term
  ;; Binds a var to the value it already has in the alist has no effect
  (defthm empty-eval-of-cons-irrel2
    (implies (and (equal val (cdr (assoc-equal var a))) ; so binding var to val has no effect
                  (pseudo-termp term))
             (equal (empty-eval term (cons (cons var val) a))
                    (empty-eval term a)))
    :flag free-vars-in-term)
  (defthm empty-eval-list-of-cons-irrel2
    (implies (and (equal val (cdr (assoc-equal var a))) ; so binding var to val has no effect
                  (pseudo-term-listp terms))
             (equal (empty-eval-list terms (cons (cons var val) a))
                    (empty-eval-list terms a)))
    :flag free-vars-in-terms)
  :hints (("Goal" :in-theory (e/d (empty-eval-of-fncall-args)
                                  (empty-eval-of-fncall-args-back)))))

(defthm empty-eval-of-append-of-pairlis$-of-EMPTY-EVAL-LIST-when-relevant-actuals-are-formals
  (IMPLIES  (and (pseudo-termp body)
                 (no-nils-in-termp body)
                 (symbol-listp formals)
                 (no-duplicatesp-equal formals)
                 (pseudo-term-listp actuals)
                 (equal (len formals)
                        (len actuals))
                 ;; the relevant actuals are all vars (unusual!):
                 (EQUAL
                  (MV-NTH 0
                          (FILTER-FORMALS-AND-ACTUALS FORMALS
                                                      ACTUALS (FREE-VARS-IN-TERM BODY)))
                  (MV-NTH 1
                          (FILTER-FORMALS-AND-ACTUALS FORMALS
                                                      ACTUALS (FREE-VARS-IN-TERM BODY)))))

            (EQUAL (EMPTY-EVAL BODY
                               (APPEND (PAIRLIS$ FORMALS (EMPTY-EVAL-LIST ACTUALS A))
                                       A))
                   (EMPTY-EVAL BODY A)))
  :hints (("Goal" :in-theory (enable FILTER-FORMALS-AND-ACTUALS
                                     PAIRLIS$
                                     symbolp-when-member-equal-and-symbol-listp))))

(local (in-theory (disable no-duplicatesp-equal))) ;move up

(defthm-flag-free-vars-in-term
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
  :hints (("Goal" :expand (FREE-VARS-IN-TERMS TERM)
           :in-theory (e/d (empty-eval-of-fncall-args)
                           (empty-eval-of-fncall-args-back)))))

(defthm empty-eval-when-alists-equiv-on-special
  (implies (and (alists-equiv-on (free-vars-in-term term) alist1 alist2)
                (pseudo-termp term))
           (equal (equal (empty-eval term alist1)
                         (empty-eval term alist2))
                  t)))

;move
(defthm alists-equiv-on-of-append-arg1
  (implies (alistp x)
           (equal (alists-equiv-on keys (binary-append x y) z)
                  (and (alists-equiv-on (intersection-equal keys (strip-cars x))
                                             x
                                             z)
                       (alists-equiv-on (set-difference-equal keys (strip-cars x))
                                             y
                                             z))))
  :hints (("Goal" :in-theory (enable (:d SET-DIFFERENCE-EQUAL)
                                     intersection-equal
                                     MEMBER-EQUAL-OF-STRIP-CARS-IFF
                                     ))))

;move
(defthm alists-equiv-on-of-append-arg2
  (implies (and (alistp x)
                )
           (equal (alists-equiv-on keys z (binary-append x y))
                  (and (alists-equiv-on (intersection-equal keys (strip-cars x))
                                             z
                                             x)
                       (alists-equiv-on (set-difference-equal keys (strip-cars x))
                                             z
                                             y))))
  :hints (("Goal" :in-theory (enable (:d SET-DIFFERENCE-EQUAL)
                                     intersection-equal
                                     MEMBER-EQUAL-OF-STRIP-CARS-IFF))))



;todo: nested induction
;; (thm
;;  (equal (INTERSECTION-EQUAL (SET-DIFFERENCE-EQUAL vars FORMALS)
;;                             (MV-NTH 0 (FILTER-FORMALS-AND-ACTUALS FORMALS ACTUALS var)))
;;         nil)
;;  :hints (("Goal" :in-theory (enable FILTER-FORMALS-AND-ACTUALS))))

(defthm subsetp-equal-of-mv-nth-0-of-FILTER-FORMALS-AND-ACTUALS
  (subsetp-equal (MV-NTH 0 (FILTER-FORMALS-AND-ACTUALS FORMALS ACTUALS vars)) formals)
  :hints (("Goal" :in-theory (enable FILTER-FORMALS-AND-ACTUALS) )))

(defthmd INTERSECTION-EQUAL-of-SET-DIFFERENCE-EQUAL-when-subsetp-equal
  (implies (subsetp-equal vars2 formals)
           (equal (INTERSECTION-EQUAL (SET-DIFFERENCE-EQUAL vars FORMALS)
                                      vars2)
                  nil))
  :hints (("Goal" :in-theory (enable INTERSECTION-EQUAL SET-DIFFERENCE-EQUAL))))

;nice!  use more above
(defthm mv-nth-0-of-FILTER-FORMALS-AND-ACTUALS
  (equal (MV-NTH 0 (FILTER-FORMALS-AND-ACTUALS FORMALS ACTUALS vars))
         (intersection-equal formals vars))
  :hints (("Goal" :in-theory (enable FILTER-FORMALS-AND-ACTUALS) )))



(defthm set-difference-equal-of-intersection-equal-and-intersection-equal-swapped
  (equal (set-difference-equal (intersection-equal x y)
                               (intersection-equal y x))
         nil))

(defthm intersection-equal-when-subsetp-equal
  (implies (subsetp-equal x y)
           (equal (intersection-equal x y)
                  (true-list-fix x)))
  :hints (("Goal" ;:induct (intersection-equal y x)
           :in-theory (enable intersection-equal))))

(defthm intersection-equal-of-intersection-equal-and-intersection-equal-swapped
  (equal (intersection-equal (intersection-equal x y)
                             (intersection-equal y x))
         (intersection-equal x y))
  :hints (("Goal" ;:induct (intersection-equal y x)
           :in-theory (enable intersection-equal))))

(defthm SET-DIFFERENCE-EQUAL-of-SET-DIFFERENCE-EQUAL-when-subsetp-equal
  (implies (subsetp-equal z formals)
           (equal (SET-DIFFERENCE-EQUAL (SET-DIFFERENCE-EQUAL x FORMALS)
                                        z)
                  (SET-DIFFERENCE-EQUAL x FORMALS)))
  :hints (("Goal" :in-theory (enable SET-DIFFERENCE-EQUAL))))

(defthm SET-DIFFERENCE-EQUAL-helper
  (equal (SET-DIFFERENCE-EQUAL (SET-DIFFERENCE-EQUAL x FORMALS)
                               (INTERSECTION-EQUAL FORMALS x))
         (SET-DIFFERENCE-EQUAL x FORMALS)))

(defund map-lookup-equal (terms a)
  (if (endp terms)
      nil
    (cons (lookup-equal (first terms) a)
          (map-lookup-equal (rest terms) a))))

(defthm len-of-map-lookup-equal
  (equal (len (map-lookup-equal terms a))
         (len terms))
  :hints (("Goal" :in-theory (enable map-lookup-equal))))


;true for any evaluator
(defthm empty-eval-list-when-symbol-listp
  (implies (and (symbol-listp terms)
                (no-nils-in-termsp terms))
           (equal (empty-eval-list terms a)
                  (map-lookup-equal terms a)))
  :hints (("Goal" :in-theory (enable map-lookup-equal
                                     lookup-equal))))

(defthm no-nils-in-termsp-of-set-difference-equal
  (implies (no-nils-in-termsp x)
           (no-nils-in-termsp (set-difference-equal x y)))
  :hints (("Goal" :in-theory (enable set-difference-equal))))

(make-flag NO-NILS-IN-TERMP)

(defthm-flag-no-nils-in-termp
  (defthm no-nils-in-termp-of-free-vars-in-term
    (implies (no-nils-in-termp term)
             (no-nils-in-termsp (free-vars-in-term term)))
    :flag no-nils-in-termp)
  (defthm no-nils-in-termsp-of-free-vars-in-terms
    (implies (no-nils-in-termsp terms)
             (no-nils-in-termsp (free-vars-in-terms terms)))
    :flag no-nils-in-termsp)
  :hints (("Goal" :expand (free-vars-in-terms terms)
           :in-theory (enable free-vars-in-term no-nils-in-termsp))))

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
  :hints (("Goal" :in-theory (enable ASSOC-EQUAL-IFF))))

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

(defthm MAP-LOOKUP-EQUAL-of-cons-of-cons-irrel
  (implies (not (member-equal key keys))
           (equal (MAP-LOOKUP-EQUAL keys (CONS (cons key val) alist))
                  (MAP-LOOKUP-EQUAL keys alist)))
  :hints (("Goal" :in-theory (enable MAP-LOOKUP-EQUAL))))


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

(defthm map-EMPTY-EVAL-of-map-LOOKUP-EQUAL-of-pairlis$
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
                                           a ; todo: show that this is irrelevant
                                           ))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (make-lambda-application-simple
                            intersection-equal-of-set-difference-equal-when-subsetp-equal)
                           ()))))

(defthm equal-of-empty-eval-and-empty-eval-when-not-consp-of-free-vars-in-term
  (implies (and (not (consp (free-vars-in-term body)))
                (pseudo-termp body) ;drop?
                )
           (equal (equal (empty-eval body a2)
                         (empty-eval body a1))
                  t)))

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
                  (empty-eval body (pairlis$ formals (empty-eval-list actuals a))))))
