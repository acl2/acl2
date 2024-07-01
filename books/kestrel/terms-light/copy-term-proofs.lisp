; Proofs about copy-term
;
; Copyright (C) 2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "copy-term")
(include-book "kestrel/evaluators/empty-eval" :dir :system)
;(include-book "lambdas-closed-in-termp")
;(include-book "no-duplicate-lambda-formals-in-termp")
(include-book "no-nils-in-termp")
(local (include-book "kestrel/lists-light/subsetp-equal" :dir :system))
(local (include-book "termp-simple")) ; nicer definition of termp
(local (include-book "arglistp1"))

(local (in-theory (disable all-vars termp)))

(local (make-flag copy-term))

(defthm-flag-copy-term
  (defthm no-nils-in-termp-of-copy-term
    (implies (and (pseudo-termp term)
                  (no-nils-in-termp term)
                  ;; (no-duplicate-lambda-formals-in-termp term)
                  ;; (lambdas-closed-in-termp term)
                  )
             (no-nils-in-termp (copy-term term)))
    :flag copy-term)
  (defthm no-nils-in-termp-of-copy-terms
    (implies (and (pseudo-term-listp terms)
                  (no-nils-in-termsp terms)
                  ;; (no-duplicate-lambda-formals-in-termsp terms)
                  ;; (lambdas-closed-in-termsp terms)
                  )
             (no-nils-in-termsp (copy-terms terms)))
    :flag copy-terms)
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (copy-term
                            copy-terms
                            ;; lambdas-closed-in-termp
                            )
                           ()))))

(defthm-flag-copy-term
  (defthm subsetp-equal-of-free-vars-in-term-of-copy-term
    (implies (and (pseudo-termp term)
                  ;; (no-nils-in-termp term)
                  ;; (no-duplicate-lambda-formals-in-termp term)
                  ;; (lambdas-closed-in-termp term)
                  )
             (subsetp-equal (free-vars-in-term (copy-term term))
                            (free-vars-in-term term)))
    :flag copy-term)
  (defthm subsetp-equal-of-free-vars-in-terms-of-copy-terms
    (implies (and (pseudo-term-listp terms)
                  ;; (no-nils-in-termsp terms)
                  ;; (no-duplicate-lambda-formals-in-termsp terms)
                  ;; (lambdas-closed-in-termsp terms)
                  )
             (subsetp-equal (free-vars-in-terms (copy-terms terms))
                            (free-vars-in-terms terms)))
    :flag copy-terms)
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :expand ((free-vars-in-term term)
                    ;; (no-duplicate-lambda-formals-in-termp term)
                    )
           :in-theory (e/d (copy-term
                            copy-terms
                            ;; lambdas-closed-in-termp
                            free-vars-in-terms-when-symbol-listp)
                           ()))))

(defthm-flag-copy-term
  (defthm termp-of-copy-term
    (implies (and ;; (pseudo-termp term)
                  (termp term w)
                  ;; (no-duplicate-lambda-formals-in-termp term)
                  ;; (lambdas-closed-in-termp term)
                  ;; (arities-okp ... w)
                  )
             (termp (copy-term term) w))
    :flag copy-term)
  (defthm termp-of-copy-terms
    (implies (and ;; (pseudo-term-listp terms)
                  (term-listp terms w)
                  ;; (no-duplicate-lambda-formals-in-termsp terms)
                  ;; (lambdas-closed-in-termsp terms)
                  ;; (arities-okp ... w)
                  )
             (term-listp (copy-terms terms) w))
    :flag copy-terms)
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (termp-becomes-termp-simple
                            term-listp-becomes-term-listp-simple
                            copy-term
                            copy-terms
                            ;; lambdas-closed-in-termp
                            )
                           ()))))

(defthm-flag-copy-term
  (defthm logic-fnsp-of-copy-term
    (implies (and (logic-fnsp term w)
                  ;; (pseudo-termp term)
                  ;; (no-duplicate-lambda-formals-in-termp term)
                  ;; (lambdas-closed-in-termp term)
                  )
             (logic-fnsp (copy-term term) w))
    :flag copy-term)
  (defthm logic-fns-listp-of-copy-terms
    (implies (and (logic-fns-listp terms w)
                  ;; (pseudo-term-listp terms)
                  ;; (no-duplicate-lambda-formals-in-termsp terms)
                  ;; (lambdas-closed-in-termsp terms)
                  )
             (logic-fns-listp (copy-terms terms) w))
    :flag copy-terms)
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (termp-becomes-termp-simple
                            term-listp-becomes-term-listp-simple
                            copy-term
                            copy-terms
                            ;; lambdas-closed-in-termp
                            )
                           ()))))

;; Follows easily from termp and logic-fnsp proofs.
;; In general, an arities-okp hyp may be needed.
(defthm logic-termp-of-copy-term
  (implies (logic-termp term w)
           (logic-termp (copy-term term) w)))

;; Follows easily from term-listp and logic-fns-listp proofs.
;; In general, an arities-okp hyp may be needed.
(defthm logic-term-listp-of-copy-term
  (implies (logic-term-listp terms w)
           (logic-term-listp (copy-terms terms) w)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The point here is to recur on a different alist for lambdas.
(local
 (mutual-recursion
  (defund copy-term-induct (term alist)
    (declare (irrelevant alist))
    (if (variablep term)
        term
      (let ((fn (ffn-symb term)))
        (case fn
          (quote term)
         ;; special handling for other functions would go here...
          (t ;; normal function call or lambda application:
           (let ((args (copy-terms-induct (fargs term) alist)))
             (if (consp fn)
             ;; it's a lambda:
                 (let* ((formals (lambda-formals fn))
                        (body (lambda-body fn))
                        (body (copy-term-induct body (pairlis$ (lambda-formals fn) (empty-eval-list args alist)))))
                  ;; todo: use cons-with-hint
                   `((lambda ,formals ,body) ,@args))
              ;; non-lambda:
               (cons-with-hint fn args term))))))))
  (defund copy-terms-induct (terms alist)
    (declare (irrelevant alist))
    (if (endp terms)
        nil
      (cons-with-hint (copy-term-induct (first terms) alist)
                      (copy-terms-induct (rest terms) alist)
                      terms)))))

(local (make-flag copy-term-induct))

;; The induct function is the equivalent to the original function
(local
 (defthm-flag-copy-term-induct
   (defthm copy-term-induct-removal
     (equal (copy-term-induct term alist)
            (copy-term term))
     :flag copy-term-induct)
   (defthm copy-terms-induct-removal
     (equal (copy-terms-induct terms alist)
            (copy-terms terms))
     :flag copy-terms-induct)
   :hints (("Goal" :in-theory (enable copy-term
                                      copy-terms
                                      copy-term-induct
                                      copy-terms-induct)))))

;; Proof that copy-term preserves the meaning of terms.
(defthm-flag-copy-term-induct
  (defthm copy-term-correct
    (implies (and (pseudo-termp term)
                  ;; (no-nils-in-termp term)
                  ;; (no-duplicate-lambda-formals-in-termp term)
                  ;; (lambdas-closed-in-termp term)
                  )
             (equal (empty-eval (copy-term term) alist)
                    (empty-eval term alist)))
    :flag copy-term-induct)
  (defthm copy-terms-induct-correct
    (implies (and (pseudo-term-listp terms)
                  ;; (no-nils-in-termsp terms)
                  ;; (no-duplicate-lambda-formals-in-termsp terms)
                  ;; (lambdas-closed-in-termsp terms)
                  )
             (equal (empty-eval-list (copy-terms terms) alist)
                    (empty-eval-list terms alist)))
    :flag copy-terms-induct)
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (copy-term
                            copy-terms
                            empty-eval-of-fncall-args
                            ;; lambdas-closed-in-termp
                            ;; no-duplicate-lambda-formals-in-termp
                            not-member-equal-of-nil-when-no-nils-in-termsp)
                           (empty-eval-of-fncall-args-back)))))
