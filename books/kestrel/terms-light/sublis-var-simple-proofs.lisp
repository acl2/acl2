; Proofs about sublis-var-simple
;
; Copyright (C) 2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "sublis-var-simple")
(include-book "make-lambda-terms-simple")
(include-book "lambdas-closed-in-termp")
(include-book "kestrel/evaluators/empty-eval" :dir :system)
(local (include-book "kestrel/evaluators/empty-eval-theorems" :dir :system))
(local (include-book "../lists-light/subsetp-equal"))
(local (include-book "kestrel/alists-light/assoc-equal" :dir :system))
(local (include-book "kestrel/alists-light/alists-equiv-on" :dir :system))
(local (include-book "kestrel/alists-light/strip-cars" :dir :system))
(local (include-book "kestrel/alists-light/strip-cdrs" :dir :system))
(local (include-book "kestrel/alists-light/pairlis-dollar" :dir :system))
(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/lists-light/nthcdr" :dir :system))
(local (include-book "kestrel/lists-light/take" :dir :system))
(local (include-book "kestrel/lists-light/member-equal" :dir :system))
;(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/set-difference-equal" :dir :system))
(local (include-book "kestrel/lists-light/subsetp-equal" :dir :system))
(local (include-book "kestrel/typed-lists-light/symbol-listp" :dir :system))
(local (include-book "kestrel/typed-lists-light/pseudo-term-listp" :dir :system))

;move?
(local
 (defthm lambdas-closed-in-termp-of-cdr-of-assoc-equal
   (implies (lambdas-closed-in-termsp (strip-cdrs alist))
            (lambdas-closed-in-termp (cdr (assoc-equal term alist))))
   :hints (("Goal" :in-theory (enable assoc-equal)))))

(defthm-flag-sublis-var-simple
  (defthm lambdas-closed-in-termp-of-sublis-var-simple
    (implies (and (pseudo-termp term)
                  (lambdas-closed-in-termp term)
                  (lambdas-closed-in-termsp (strip-cdrs alist)))
             (lambdas-closed-in-termp (sublis-var-simple alist term)))
    :flag sublis-var-simple)
  (defthm lambdas-closed-in-termp-of-sublis-var-lst-simple
    (implies (and (pseudo-term-listp terms)
                  (lambdas-closed-in-termsp terms)
                  (lambdas-closed-in-termsp (strip-cdrs alist)))
             (lambdas-closed-in-termsp (sublis-var-simple-lst alist terms)))
    :flag sublis-var-simple-lst)
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable sublis-var-simple
                              sublis-var-simple-lst
                              lambdas-closed-in-termp))))

(local
 (defthm subsetp-equal-of-free-vars-in-term-of-assoc-equal-and-free-vars-in-terms-of-strip-cdrs
   (implies (and (member-equal term (strip-cars alist))
                 (assoc-equal term alist))
            (subsetp-equal (free-vars-in-term (cdr (assoc-equal term alist)))
                           (free-vars-in-terms (strip-cdrs alist))))
   :hints (("Goal" :in-theory (enable subsetp-equal assoc-equal free-vars-in-terms)))))

(defthm-flag-free-vars-in-term
  ;; If we substitute all variables in the term, then the new free vars are limited to the free vars in the terms put in by substitution.
  (defthm subsetp-equal-of-free-vars-in-term-of-sublis-var-simple-and-free-vars-in-terms-of-strip-cdrs
    (implies (subsetp-equal (free-vars-in-term term)
                            (strip-cars alist))
             (subsetp-equal (free-vars-in-term (sublis-var-simple alist term))
                            (free-vars-in-terms (strip-cdrs alist))))
    :flag free-vars-in-term)
  (defthm subsetp-equal-of-free-vars-in-term-of-sublis-var-simple-lst-and-free-vars-in-terms-of-strip-cdrs
    (implies (subsetp-equal (free-vars-in-terms terms)
                            (strip-cars alist))
             (subsetp-equal (free-vars-in-terms (sublis-var-simple-lst alist terms))
                            (free-vars-in-terms (strip-cdrs alist))))
    :flag free-vars-in-terms)
  :hints (("Goal" :in-theory (enable sublis-var-simple
                                     sublis-var-simple-lst
                                     free-vars-in-term
                                     free-vars-in-terms
                                     assoc-equal))))

;; Simple consequence of the above.
(defthm subsetp-equal-of-free-vars-in-term-of-sublis-var-simple-and-free-vars-in-terms-of-strip-cdrs-gen
  (implies (and (subsetp-equal (free-vars-in-term term) ; the alist binds all the vars, so any free vars in the result come from the alist
                               (strip-cars alist))
                (subsetp-equal (free-vars-in-terms (strip-cdrs alist)) free))
           (subsetp-equal (free-vars-in-term (sublis-var-simple alist term))
                          free)))




;; (thm
;;  (implies (and (consp term)
;;                (not (equal 'quote (car term)))
;;                (symbolp (car term))
;;                (symbol-alistp alist)
;;                (pseudo-term-listp (strip-cdrs alist))
;;                (pseudo-term-listp (cdr term))
;;                (equal (len lambda-formals) (len args))
;;                )
;;           (equal (empty-eval (make-lambda-term-simple lambda-formals args term) a)
;;                  (empty-eval (cons
;;                                (car term) (KWOTE-LST (empty-eval-list (MAKE-LAMBDA-TERMS-SIMPLE lambda-formals args (cdr term)) a)))
;;                               nil)))
;;  :hints (("Goal" :in-theory (enable make-lambda-term-simple
;;                                     EMPTY-EVAL-OF-FNCALL-ARGS))))

;; The result of sublis-var-simple evaluates the same as if we had made a lambda.
(defthm-flag-sublis-var-simple
  (defthm sublis-var-simple-correct
    (implies (and (symbol-alistp alist) ; usually a symbol-term-alistp
                  (pseudo-term-listp (strip-cdrs alist))
                  (pseudo-termp term)
                  ;; since defevaluator has gross behavior on nil:
                  (not (member-equal nil (free-vars-in-term term))))
             (equal (empty-eval (sublis-var-simple alist term) a)
                    (empty-eval (make-lambda-term-simple (strip-cars alist) (strip-cdrs alist) term) a)))
    :flag sublis-var-simple)
  (defthm sublis-var-simple-lst-correct
    (implies (and (symbol-alistp alist) ; usually a symbol-term-alistp
                  (pseudo-term-listp (strip-cdrs alist))
                  (pseudo-term-listp terms)
                  (not (member-equal nil (free-vars-in-terms terms))))
             (equal (empty-eval-list (sublis-var-simple-lst alist terms) a)
                    (empty-eval-list (make-lambda-terms-simple (strip-cars alist) (strip-cdrs alist) terms) a)))
    :flag sublis-var-simple-lst)
  :hints (("Goal" :expand (PSEUDO-TERMP TERM)
           :in-theory (e/d (sublis-var-simple
                            sublis-var-simple-lst
                            MEMBER-EQUAL-OF-STRIP-CARS-IFF
                            make-lambda-terms-simple
                            ;;make-lambda-term-simple
                            empty-eval-of-fncall-args
                            empty-eval-of-cdr-of-assoc-equal)
                           (pairlis$
                            set-difference-equal
                            empty-eval-of-fncall-args-back)))))

(defthm-flag-sublis-var-simple
  (defthm sublis-var-simple-correct2
    (implies (and (symbol-alistp alist) ; usually a symbol-term-alistp
                  (pseudo-term-listp (strip-cdrs alist))
                  (pseudo-termp term)
                  (not (member-equal nil (free-vars-in-term term)))
                  (subsetp-equal (free-vars-in-term term) (strip-cars alist))
                  )
             (equal (empty-eval (sublis-var-simple alist term) a)
                    (empty-eval term (pairlis$ (strip-cars alist)
                                                (empty-eval-list (strip-cdrs alist) a)))))
    :flag sublis-var-simple)
  (defthm sublis-var-simple-lst-correct2
    (implies (and (symbol-alistp alist) ; usually a symbol-term-alistp
                  (pseudo-term-listp (strip-cdrs alist))
                  (pseudo-term-listp terms)
                  (not (member-equal nil (free-vars-in-terms terms)))
                  (subsetp-equal (free-vars-in-terms terms) (strip-cars alist)))
             (equal (empty-eval-list (sublis-var-simple-lst alist terms) a)
                    (empty-eval-list terms
                                      (pairlis$ (strip-cars alist)
                                                (empty-eval-list (strip-cdrs alist) a)))))
    :flag sublis-var-simple-lst)
  :hints (("Goal" :expand (PSEUDO-TERMP TERM)
           :in-theory (e/d (sublis-var-simple
                            sublis-var-simple-lst
                            MEMBER-EQUAL-OF-STRIP-CARS-IFF
                            make-lambda-terms-simple
                            ;;make-lambda-term-simple
                            empty-eval-of-fncall-args
                            empty-eval-of-cdr-of-assoc-equal)
                           (pairlis$
                            set-difference-equal
                            empty-eval-of-fncall-args-back)))))
