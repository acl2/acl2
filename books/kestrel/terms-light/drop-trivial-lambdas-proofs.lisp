; Proofs about substitute-constants-in-lambdas
;
; Copyright (C) 2024-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "drop-trivial-lambdas")
(include-book "kestrel/evaluators/empty-eval" :dir :system)
(include-book "lambdas-closed-in-termp")
(include-book "no-duplicate-lambda-formals-in-termp")
(include-book "no-nils-in-termp")
(local (include-book "helpers"))
(local (include-book "empty-eval-helpers"))
(local (include-book "kestrel/alists-light/symbol-alistp" :dir :system))
(local (include-book "kestrel/alists-light/pairlis-dollar" :dir :system))
(local (include-book "kestrel/typed-lists-light/symbol-listp" :dir :system))
(local (include-book "kestrel/typed-lists-light/pseudo-term-listp" :dir :system))
(local (include-book "kestrel/lists-light/subsetp-equal" :dir :system))
(local (include-book "kestrel/lists-light/set-difference-equal" :dir :system))
(local (include-book "kestrel/lists-light/take" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/lists-light/nthcdr" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))
(local (include-book "kestrel/lists-light/remove-equal" :dir :system))
(local (include-book "kestrel/lists-light/remove-duplicates-equal" :dir :system))

(local (in-theory (enable make-lambda-with-hint)))

;; (local (make-flag drop-trivial-lambdas))

;; The point here is to recur on a different alist.
;; todo: can we use this less below and move this down?
(local
 (mutual-recursion
  (defund drop-trivial-lambdas-induct (term alist)
    (declare (irrelevant alist))
    (if (variablep term)
        term
      (let ((fn (ffn-symb term)))
        (if (eq 'quote fn)
            term
          (let ((args (drop-trivial-lambdas-induct-lst (fargs term) alist)))
            (if (consp fn)
               ;; it's a lambda:
                (let* ((body (lambda-body fn))
                       (body (drop-trivial-lambdas-induct body (pairlis$ (lambda-formals fn) (empty-eval-list args alist))))
                       (formals (lambda-formals fn)))
                  (if (equal formals args)
                     ;; If the remaining formals are the same as the args, we
                     ;; don't need a lambda at all:
                      body
                   ;; no change:
                    `((lambda ,formals ,body) ,@args)))
             ;; not a lambda:
              (cons-with-hint fn args term)))))))
  (defund drop-trivial-lambdas-induct-lst (terms alist)
    (declare (irrelevant alist))
    (if (endp terms)
        nil
      (cons-with-hint (drop-trivial-lambdas-induct (first terms) alist)
                      (drop-trivial-lambdas-induct-lst (rest terms) alist)
                      terms)))))

(local (make-flag drop-trivial-lambdas-induct))

;; The induct function is the same as the original
(local
 (defthm-flag-drop-trivial-lambdas-induct
   (defthm drop-trivial-lambdas-induct-removal
     (equal (drop-trivial-lambdas-induct term alist)
            (drop-trivial-lambdas term))
     :flag drop-trivial-lambdas-induct)
   (defthm drop-trivial-lambdas-induct-lst-removal
     (equal (drop-trivial-lambdas-induct-lst terms alist)
            (drop-trivial-lambdas-lst terms))
     :flag drop-trivial-lambdas-induct-lst)
   :hints (("Goal" :in-theory (enable drop-trivial-lambdas
                                      drop-trivial-lambdas-lst
                                      drop-trivial-lambdas-induct
                                      drop-trivial-lambdas-induct-lst)))))

;!!do we even know whether there are nils among the lambda formals?

;; (thm
;;  (implies (and (consp (car term))
;;                (lambdas-closed-in-termp term)
;;                (no-nils-in-termp term))
;;           (not (member-equal 'nil (car (cdr (car term))))))
;;  :hints (("Goal" :expand (no-nils-in-termp term)
;;           :in-theory (enable no-nils-in-termp lambdas-closed-in-termp))))

;(local (in-theory (enable not-member-equal-of-nil-when-no-nils-in-termsp)))

;;todo: do we need the special induct for these?
(defthm-flag-drop-trivial-lambdas-induct
  (defthm no-nils-in-termp-of-drop-trivial-lambdas
    (implies (and (pseudo-termp term)
                  (no-nils-in-termp term)
                  ;; (no-duplicate-lambda-formals-in-termp term)
                  (lambdas-closed-in-termp term))
             (no-nils-in-termp (drop-trivial-lambdas term)))
    :flag drop-trivial-lambdas-induct)
  (defthm no-nils-in-termp-of-drop-trivial-lambdas-lst
    (implies (and (pseudo-term-listp terms)
                  (no-nils-in-termsp terms)
                  ;; (no-duplicate-lambda-formals-in-termsp terms)
                  (lambdas-closed-in-termsp terms))
             (no-nils-in-termsp (drop-trivial-lambdas-lst terms)))
    :flag drop-trivial-lambdas-induct-lst)
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (drop-trivial-lambdas
                                   drop-trivial-lambdas-lst
                                   empty-eval-of-fncall-args
                                   true-listp-when-symbol-alistp
                                   ;map-lookup-equal-of-pairlis$-of-empty-eval-list
                                   )
                                  (empty-eval-of-fncall-args-back
                                   ;empty-eval-list-of-map-lookup-equal-of-pairlis$
                                   )))))

(defthm-flag-drop-trivial-lambdas-induct
  (defthm subsetp-equal-of-free-vars-in-term-of-drop-trivial-lambdas
    (implies (and (pseudo-termp term)
                  ;; (no-nils-in-termp term)
                  (no-duplicate-lambda-formals-in-termp term)
                  (lambdas-closed-in-termp term)
                  )
             (subsetp-equal (free-vars-in-term (drop-trivial-lambdas term))
                            (free-vars-in-term term)))
    :flag drop-trivial-lambdas-induct)
  (defthm subsetp-equal-of-free-vars-in-terms-of-drop-trivial-lambdas-lst
    (implies (and (pseudo-term-listp terms)
                  ;; (no-nils-in-termsp terms)
                  (no-duplicate-lambda-formals-in-termsp terms)
                  (lambdas-closed-in-termsp terms)
                  )
             (subsetp-equal (free-vars-in-terms (drop-trivial-lambdas-lst terms))
                            (free-vars-in-terms terms)))
    :flag drop-trivial-lambdas-induct-lst)
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :expand ((free-vars-in-term term)
                    (no-duplicate-lambda-formals-in-termp term))
           :in-theory (e/d (drop-trivial-lambdas
                            drop-trivial-lambdas-lst
                            empty-eval-of-fncall-args
                            true-listp-when-symbol-alistp
;                            lambdas-closed-in-termp
                            free-vars-in-terms-when-symbol-listp)
                           (empty-eval-of-fncall-args-back)))))

(defthm subsetp-equal-of-free-vars-in-term-of-drop-trivial-lambdas-gen
  (implies (and (subsetp-equal (free-vars-in-term term) x)
                (pseudo-termp term)
                  ;; (no-nils-in-termp term)
                (no-duplicate-lambda-formals-in-termp term)
                (lambdas-closed-in-termp term))
           (subsetp-equal (free-vars-in-term (drop-trivial-lambdas term))
                          x)))

(defthm-flag-drop-trivial-lambdas-induct
  (defthm lambdas-closed-in-termp-of-drop-trivial-lambdas
    (implies (and (pseudo-termp term)
                  (lambdas-closed-in-termp term)
                  (no-duplicate-lambda-formals-in-termp term))
             (lambdas-closed-in-termp (drop-trivial-lambdas term)))
    :flag drop-trivial-lambdas-induct)
  (defthm lambdas-closed-in-termp-of-drop-trivial-lambdas-lst
    (implies (and (pseudo-term-listp terms)
                  (lambdas-closed-in-termsp terms)
                  (no-duplicate-lambda-formals-in-termsp terms))
             (lambdas-closed-in-termsp (drop-trivial-lambdas-lst terms)))
    :flag drop-trivial-lambdas-induct-lst)
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (drop-trivial-lambdas
                                   drop-trivial-lambdas-lst
                                   empty-eval-of-fncall-args
                                   true-listp-when-symbol-alistp
;                                   lambdas-closed-in-termp
                                   ;map-lookup-equal-of-pairlis$-of-empty-eval-list
                                   )
                                  (empty-eval-of-fncall-args-back
                                   ;empty-eval-list-of-map-lookup-equal-of-pairlis$
                                   )))))

(defthm-flag-drop-trivial-lambdas-induct
  (defthm no-duplicate-lambda-formals-in-termp-of-drop-trivial-lambdas
    (implies (and (pseudo-termp term)
                  (no-duplicate-lambda-formals-in-termp term))
             (no-duplicate-lambda-formals-in-termp (drop-trivial-lambdas term)))
    :flag drop-trivial-lambdas-induct)
  (defthm no-duplicate-lambda-formals-in-termp-of-drop-trivial-lambdas-lst
    (implies (and (pseudo-term-listp terms)
                  (no-duplicate-lambda-formals-in-termsp terms))
             (no-duplicate-lambda-formals-in-termsp (drop-trivial-lambdas-lst terms)))
    :flag drop-trivial-lambdas-induct-lst)
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (drop-trivial-lambdas
                                   drop-trivial-lambdas-lst
                                   empty-eval-of-fncall-args
                                   true-listp-when-symbol-alistp
                                   ;map-lookup-equal-of-pairlis$-of-empty-eval-list
                                   )
                                  (empty-eval-of-fncall-args-back
                                   ;empty-eval-list-of-map-lookup-equal-of-pairlis$
                                   )))))

;; Proof that drop-trivial-lambdas preserves the meaning of terms.
(defthm-flag-drop-trivial-lambdas-induct
  (defthm drop-trivial-lambdas-correct
    (implies (and (pseudo-termp term)
                  (no-nils-in-termp term)
                  (no-duplicate-lambda-formals-in-termp term)
                  (lambdas-closed-in-termp term))
             (equal (empty-eval (drop-trivial-lambdas term) alist)
                    (empty-eval term alist)))
    :flag drop-trivial-lambdas-induct)
  (defthm drop-trivial-lambdas-lst-correct
    (implies (and (pseudo-term-listp terms)
                  (no-nils-in-termsp terms)
                  (no-duplicate-lambda-formals-in-termsp terms)
                  (lambdas-closed-in-termsp terms))
             (equal (empty-eval-list (drop-trivial-lambdas-lst terms) alist)
                    (empty-eval-list terms alist)))
    :flag drop-trivial-lambdas-induct-lst)
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :expand (no-duplicate-lambda-formals-in-termp term)
           :in-theory (e/d (drop-trivial-lambdas
                            drop-trivial-lambdas-lst
                            empty-eval-of-fncall-args
                            true-listp-when-symbol-alistp
                            lambdas-closed-in-termp ; todo
                            ;; no-duplicate-lambda-formals-in-termp
                            ;; map-lookup-equal-of-pairlis$-of-empty-eval-list
                            alists-equiv-on-redef
                            not-member-equal-of-nil-when-no-nils-in-termsp)
                           (empty-eval-of-fncall-args-back
                            ;; empty-eval-list-of-map-lookup-equal-of-pairlis$
                            )))))

;; (defthm-flag-drop-trivial-lambdas
;;   (defthm drop-trivial-lambdas-correct
;;     (implies (and (pseudo-termp term)
;;                   (no-nils-in-termp term)
;;                   (no-duplicate-lambda-formals-in-termp term)
;;                   (lambdas-closed-in-termp term)
;;                   )
;;              (equal (empty-eval (drop-trivial-lambdas term) alist)
;;                     (empty-eval term alist)))
;;     :flag drop-trivial-lambdas)
;;   (defthm drop-trivial-lambdas-lst-correct
;;     (implies (and (pseudo-term-listp terms)
;;                   (no-nils-in-termsp terms)
;;                   (no-duplicate-lambda-formals-in-termsp terms)
;;                   (lambdas-closed-in-termsp terms)
;;                   )
;;              (equal (empty-eval-list (drop-trivial-lambdas-lst terms) alist)
;;                     (empty-eval-list terms alist)))
;;     :flag drop-trivial-lambdas-lst)
;;   :hints (("Goal" :do-not '(generalize eliminate-destructors)
;;            :expand (no-duplicate-lambda-formals-in-termp term)
;;            :in-theory (e/d (drop-trivial-lambdas
;;                                    drop-trivial-lambdas-lst
;;                                    empty-eval-of-fncall-args
;;                                    true-listp-when-symbol-alistp
;;                                    lambdas-closed-in-termp
;; ;                                   no-duplicate-lambda-formals-in-termp
;;  ;                                  no-duplicate-lambda-formals-in-termsp
;;                                    ;map-lookup-equal-of-pairlis$-of-empty-eval-list
;;                                    alists-equiv-on-redef
;;                                    not-member-equal-of-nil-when-no-nils-in-termsp)
;;                                   (empty-eval-of-fncall-args-back
;;                                    ;empty-eval-list-of-map-lookup-equal-of-pairlis$
;;                                    )))))
