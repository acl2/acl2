; Proofs about simplify-ors
;
; Copyright (C) 2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "simplify-ors")
(include-book "kestrel/evaluators/if-and-not-eval" :dir :system)
(include-book "no-nils-in-termp")
(include-book "lambdas-closed-in-termp")
(include-book "no-duplicate-lambda-formals-in-termp")
(local (include-book "kestrel/lists-light/subsetp-equal" :dir :system))
(local (include-book "termp-simple")) ; nicer definition of termp
(local (include-book "arglistp1"))

(local (in-theory (disable all-vars termp)))

(local (make-flag simplify-ors))

(defthm-flag-simplify-ors
  (defthm no-nils-in-termp-of-simplify-ors
    (implies (and (pseudo-termp term)
                  (no-nils-in-termp term))
             (no-nils-in-termp (simplify-ors term iffp)))
    :flag simplify-ors)
  (defthm no-nils-in-termp-of-simplify-ors-lst
    (implies (and (pseudo-term-listp terms)
                  (no-nils-in-termsp terms))
             (no-nils-in-termsp (simplify-ors-lst terms)))
    :flag simplify-ors-lst)
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable no-nils-in-termp no-nils-in-termsp simplify-ors simplify-ors-lst))))

(defthm-flag-simplify-ors
  (defthm no-duplicate-lambda-formals-in-termp-of-simplify-ors
    (implies (and (pseudo-termp term)
                  (no-duplicate-lambda-formals-in-termp term))
             (no-duplicate-lambda-formals-in-termp (simplify-ors term iffp)))
    :flag simplify-ors)
  (defthm no-duplicate-lambda-formals-in-termp-of-simplify-ors-lst
    (implies (and (pseudo-term-listp terms)
                  (no-duplicate-lambda-formals-in-termsp terms))
             (no-duplicate-lambda-formals-in-termsp (simplify-ors-lst terms)))
    :flag simplify-ors-lst)
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable simplify-ors simplify-ors-lst
                              no-duplicate-lambda-formals-in-termp ; todo
                              ))))

(defthm-flag-simplify-ors
  (defthm subsetp-equal-of-free-vars-in-term-of-simplify-ors
    (implies (pseudo-termp term)
             (subsetp-equal (free-vars-in-term (simplify-ors term iffp))
                            (free-vars-in-term term)))
    :flag simplify-ors)
  (defthm subsetp-equal-of-free-vars-in-terms-of-simplify-ors-lst
    (implies (pseudo-term-listp terms)
             (subsetp-equal (free-vars-in-terms (simplify-ors-lst terms))
                            (free-vars-in-terms terms)))
    :flag simplify-ors-lst)
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :expand ((free-vars-in-term term))
           :in-theory (enable simplify-ors
                              simplify-ors-lst
                              free-vars-in-terms-when-symbol-listp))))

(defthm subsetp-equal-of-free-vars-in-term-of-simplify-ors-gen
  (implies (and (subsetp-equal (free-vars-in-term term) x)
                (pseudo-termp term))
           (subsetp-equal (free-vars-in-term (simplify-ors term iffp))
                          x))
  :hints (("Goal" :use subsetp-equal-of-free-vars-in-term-of-simplify-ors
           :in-theory (disable subsetp-equal-of-free-vars-in-term-of-simplify-ors))))

(defthm-flag-simplify-ors
  (defthm lambdas-closed-in-termp-of-simplify-ors
    (implies (and (pseudo-termp term)
                  (lambdas-closed-in-termp term))
             (lambdas-closed-in-termp (simplify-ors term iffp)))
    :flag simplify-ors)
  (defthm lambdas-closed-in-termp-of-simplify-ors-lst
    (implies (and (pseudo-term-listp terms)
                  (lambdas-closed-in-termsp terms))
             (lambdas-closed-in-termsp (simplify-ors-lst terms)))
    :flag simplify-ors-lst)
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable simplify-ors simplify-ors-lst
                              lambdas-closed-in-termp))))

(defthm-flag-simplify-ors
  (defthm termp-of-simplify-ors
    (implies (and (termp term w)
                  (arities-okp '((if . 3)(not . 1)) w))
             (termp (simplify-ors term iffp) w))
    :flag simplify-ors)
  (defthm termp-of-simplify-ors-lst
    (implies (and (term-listp terms w)
                  (arities-okp '((if . 3)(not . 1)) w))
             (term-listp (simplify-ors-lst terms) w))
    :flag simplify-ors-lst)
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable termp-becomes-termp-simple
                              term-listp-becomes-term-listp-simple
                              simplify-ors
                              simplify-ors-lst))))

(defthm-flag-simplify-ors
  (defthm logic-fnsp-of-simplify-ors
    (implies (logic-fnsp term w)
             (logic-fnsp (simplify-ors term iffp) w))
    :flag simplify-ors)
  (defthm logic-fns-listp-of-simplify-ors-lst
    (implies (logic-fns-listp terms w)
             (logic-fns-listp (simplify-ors-lst terms) w))
    :flag simplify-ors-lst)
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable termp-becomes-termp-simple
                              term-listp-becomes-term-listp-simple
                              simplify-ors
                              simplify-ors-lst))))

;; Follows easily from termp and logic-fnsp proofs.
(defthm logic-termp-of-simplify-ors
  (implies (and (logic-termp term w)
                (arities-okp '((if . 3)(not . 1)) w))
           (logic-termp (simplify-ors term iffp) w)))

;; Follows easily from term-listp and logic-fns-listp proofs.
(defthm logic-term-listp-of-simplify-ors
  (implies (and (logic-term-listp terms w)
                (arities-okp '((if . 3)(not . 1)) w))
           (logic-term-listp (simplify-ors-lst terms) w)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The point here is to recur on a different alist for lambdas.
(local
 (mutual-recursion
  (defund simplify-ors-induct (term iffp alist)
    (declare (irrelevant alist))
    (if (variablep term)
       term
     (let ((fn (ffn-symb term)))
       (case fn
         (quote term)
         ;; (if test then else):
         (if (if (not (consp (cddr (fargs term)))) ; for guard proof
                 (prog2$ (er hard? 'simplify-ors "Bad term: ~x0." term)
                         term)
               (let* ((test (fargn term 1))
                      (then (fargn term 2))
                      (else (fargn term 3))
                      (test (simplify-ors-induct test t alist)) ; use a boolean context for the test
                      (then (simplify-ors-induct then iffp alist)) ; propagate boolean context to branches
                      (else (simplify-ors-induct else iffp alist)))
                 (if (and iffp
                          (equal test then))
                     ;; replace (if x x y) with (if x 't y):
                     `(if ,test 't ,else)
                   ;; todo: cons-with-hint:
                   `(if ,test ,then ,else)))))
         ;; (not arg):
         (not (if (not (consp (fargs term))) ; for guard proof
                  (prog2$ (er hard? 'simplify-ors "Bad term: ~x0." term)
                          term)
                (let* ((arg (fargn term 1))
                       (arg (simplify-ors-induct arg t alist))) ; use a boolean context for the arg
                  `(not ,arg))))
         ;; todo: build in any other functions?  myif/boolif
         (t ;; normal function call or lambda application:
          (let ((args (simplify-ors-lst-induct (fargs term) alist))) ; can't use boolean context for args
            (if (consp fn)
                ;; it's a lambda:
                (let* ((formals (lambda-formals fn))
                       (body (lambda-body fn))
                       ;; propagate boolean context:
                       (body (simplify-ors-induct body iffp (pairlis$ (lambda-formals fn) (if-and-not-eval-list args alist)))))
                  ;; todo: use cons-with-hint
                  `(,(make-lambda-with-hint formals body fn) ;(lambda ,formals ,body)
                    ,@args))
              ;; non-lambda:
              (cons-with-hint fn args term))))))))
  (defund simplify-ors-lst-induct (terms alist)
    (declare (irrelevant alist))
    (if (endp terms)
        nil
      (cons-with-hint (simplify-ors-induct (first terms) nil alist)
                      (simplify-ors-lst-induct (rest terms) alist)
                      terms)))))

(local (make-flag simplify-ors-induct))

;; The induct function is the equivalent to the original function
(local
 (defthm-flag-simplify-ors-induct
   (defthm simplify-ors-induct-removal
     (equal (simplify-ors-induct term iffp alist)
            (simplify-ors term iffp))
     :flag simplify-ors-induct)
   (defthm simplify-ors-lst-induct-removal
     (equal (simplify-ors-lst-induct terms alist)
            (simplify-ors-lst terms))
     :flag simplify-ors-lst-induct)
   :hints (("Goal" :in-theory (enable simplify-ors
                                      simplify-ors-lst
                                      simplify-ors-induct
                                      simplify-ors-lst-induct)))))

;; Proof that simplify-ors preserves the meaning of terms.
(defthm-flag-simplify-ors-induct
  (defthm simplify-ors-correct
    (implies (pseudo-termp term)
             (if iffp
                 (iff (if-and-not-eval (simplify-ors term iffp) alist)
                      (if-and-not-eval term alist))
               (equal (if-and-not-eval (simplify-ors term iffp) alist)
                      (if-and-not-eval term alist))))
    :flag simplify-ors-induct)
  (defthm simplify-ors-lst-induct-correct
    (implies (pseudo-term-listp terms)
             (equal (if-and-not-eval-list (simplify-ors-lst terms) alist)
                    (if-and-not-eval-list terms alist)))
    :flag simplify-ors-lst-induct)
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (simplify-ors
                            simplify-ors-lst
                            if-and-not-eval-of-fncall-args
                            not-member-equal-of-nil-when-no-nils-in-termsp)
                           (if-and-not-eval-of-fncall-args-back)))))

;; If iffp is true, we only get IFF, not EQUAL.
(defthm simplify-ors-of-nil-correct-iff
  (implies (pseudo-termp term)
           (iff (if-and-not-eval (simplify-ors term iffp) alist)
                (if-and-not-eval term alist)))
  :hints (("Goal" :use simplify-ors-correct
           :in-theory (disable simplify-ors-correct))))

;; If iffp is false, we get true equality:
(defthm simplify-ors-of-nil-correct
  (implies (pseudo-termp term)
           (equal (if-and-not-eval (simplify-ors term nil) alist)
                  (if-and-not-eval term alist)))
  :hints (("Goal" :use (:instance simplify-ors-correct (iffp nil))
           :in-theory (disable simplify-ors-correct))))

;; (simplify-ors '(if (if x x y) tp ep) nil) = (if (if x 't y) tp ep)
