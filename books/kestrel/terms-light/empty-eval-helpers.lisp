; Rules about the empty evaluator (which we use a lot in this dir)
;
; Copyright (C) 2023-2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/evaluators/empty-eval" :dir :system)
(include-book "non-trivial-formals")
(include-book "trivial-formals")
(include-book "free-vars-in-term")
(include-book "kestrel/alists-light/alists-equiv-on" :dir :system)
(local (include-book "helpers"))
(local (include-book "kestrel/lists-light/no-duplicatesp-equal" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))
(local (include-book "kestrel/lists-light/subsetp-equal" :dir :system))
(local (include-book "kestrel/alists-light/alistp" :dir :system))
(local (include-book "kestrel/alists-light/pairlis-dollar" :dir :system))
(local (include-book "kestrel/alists-light/strip-cars" :dir :system))

(defthm cdr-of-assoc-equal-of-pairlis$-of-empty-eval-list-when-member-equal-of-trivial-formals
  (implies (and (member-equal var (trivial-formals formals args))
     ;               (member-equal var formals)  ;drop?
     ;              (symbol-listp formals)
                (no-duplicatesp-equal formals)
                var
                (symbolp var))
           (equal (cdr (assoc-equal var (pairlis$ formals (empty-eval-list args a))))
                  (cdr (assoc-equal var a)) ; (empty-eval var a)
                  ))
  :hints (("Goal" :in-theory (enable trivial-formals pairlis$))))

;; slight rephrasing of the above
(defthm cdr-of-assoc-equal-of-pairlis$-of-empty-eval-list-when-not-member-equal-of-non-trivial-formals
  (implies (and (not (member-equal var (non-trivial-formals formals args)))
                (member-equal var formals)
     ;              (symbol-listp formals)
                (no-duplicatesp-equal formals)
                var
                (symbolp var))
           (equal (cdr (assoc-equal var (pairlis$ formals (empty-eval-list args a))))
                  (cdr (assoc-equal var a)) ; (empty-eval var a)
                  ))
  :hints (("Goal" :in-theory (enable trivial-formals pairlis$))))

(defthm helper1
  (implies (and (not (intersection-equal vars (non-trivial-formals formals args)))
                (no-duplicatesp-equal formals)
                (symbol-listp formals)
                (symbol-listp vars)
                (not (member-equal nil vars)))
           (alists-equiv-on vars
                            (append (pairlis$ formals (empty-eval-list args a)) a)
                            a))
  :hints (("Goal" :in-theory (enable alists-equiv-on symbol-listp intersection-equal))))

;(local (in-theory (disable symbol-listp no-duplicatesp-equal)))

;dup!
;change var names
(defthmd lookup-equal-of-pairlis$-of-empty-eval-list
  (equal (lookup-equal b (pairlis$ formals (empty-eval-list args a)))
         (empty-eval (lookup-equal b (pairlis$ formals args)) a))
  :hints (("Goal" :in-theory (enable pairlis$))))

(defthm empty-eval-of-lookup-equal-of-pairlis$
  (equal (empty-eval (lookup-equal key (pairlis$ formals actuals)) a)
         (lookup-equal key (pairlis$ formals (empty-eval-list actuals a))))
  :hints (("Goal" :in-theory (enable map-lookup-equal lookup-equal assoc-equal pairlis$))))

(theory-invariant (incompatible (:rewrite lookup-equal-of-pairlis$-of-empty-eval-list)
                                (:rewrite empty-eval-of-lookup-equal-of-pairlis$)))

(defthm empty-eval-list-of-map-lookup-equal-of-pairlis$
  (equal (empty-eval-list (map-lookup-equal keys (pairlis$ formals actuals)) a)
         (map-lookup-equal keys (pairlis$ formals (empty-eval-list actuals a))))
  :hints (("Goal" :in-theory (enable map-lookup-equal))))

(defthmd map-lookup-equal-of-pairlis$-of-empty-eval-list
  (equal (map-lookup-equal keys (pairlis$ keys2 (empty-eval-list terms alist)))
         (empty-eval-list (map-lookup-equal keys (pairlis$ keys2 terms)) alist))
  :hints (("Goal" :in-theory (enable map-lookup-equal))))

(theory-invariant (incompatible (:rewrite empty-eval-list-of-map-lookup-equal-of-pairlis$)
                                (:rewrite map-lookup-equal-of-pairlis$-of-empty-eval-list)))

(defthm-flag-free-vars-in-term
  ;; If the alists agree on some set of keys that includes all the free vars in the term,
  ;; then the evaluations give the same result.
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
