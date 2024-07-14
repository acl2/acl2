; Proofs about sublis-var-simple
;
; Copyright (C) 2023-2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "tools/flag" :dir :system)
(include-book "kestrel/utilities/symbol-term-alistp" :dir :system)
(include-book "sublis-var-simple")
(include-book "make-lambda-terms-simple")
(include-book "lambdas-closed-in-termp")
(include-book "kestrel/evaluators/empty-eval" :dir :system)
(include-book "no-duplicate-lambda-formals-in-termp")
(include-book "no-nils-in-termp")
(local (include-book "kestrel/evaluators/empty-eval-theorems" :dir :system))
(local (include-book "../lists-light/subsetp-equal"))
(local (include-book "kestrel/alists-light/assoc-equal" :dir :system))
(local (include-book "kestrel/alists-light/alists-equiv-on" :dir :system))
(local (include-book "kestrel/alists-light/strip-cars" :dir :system))
(local (include-book "kestrel/alists-light/strip-cdrs" :dir :system))
(local (include-book "kestrel/alists-light/pairlis-dollar" :dir :system))

(make-flag sublis-var-simple)

(defthm-flag-sublis-var-simple
  (defthm sublis-var-simple-of-nil
    (implies (pseudo-termp term)
             (equal (sublis-var-simple nil term)
                    term))
    :flag sublis-var-simple)
  (defthm sublis-var-simple-lst-of-nil
    (implies (pseudo-term-listp terms)
             (equal (sublis-var-simple-lst nil terms)
                    terms))
    :flag sublis-var-simple-lst)
  :hints (("Goal" :in-theory (enable sublis-var-simple
                                     sublis-var-simple-lst))))

(defthm true-listp-of-sublis-var-simple-lst
  (true-listp (sublis-var-simple-lst alist terms)))

(defthm len-of-sublis-var-simple-lst
  (equal (len (sublis-var-simple-lst alist terms))
         (len terms))
  :hints (("Goal" :in-theory (enable sublis-var-simple-lst))))

;;sublis-var-simple preserves pseudo-termp.
(defthm-flag-sublis-var-simple
  (defthm pseudo-termp-of-sublis-var-simple
    (implies (and (pseudo-termp term)
                  (symbol-term-alistp alist))
             (pseudo-termp (sublis-var-simple alist term)))
    :flag sublis-var-simple)
  (defthm pseudo-term-listp-of-sublis-var-simple-lst
    (implies (and (pseudo-term-listp terms)
                  (symbol-term-alistp alist))
             (pseudo-term-listp (sublis-var-simple-lst alist terms)))
    :flag sublis-var-simple-lst)
  :hints (("Goal" :in-theory (enable sublis-var-simple
                                     sublis-var-simple-lst)
           :expand ((pseudo-termp (cons (car term) (sublis-var-simple-lst alist (cdr term))))))))

(defthm car-of-sublis-var-simple
  (equal (car (sublis-var-simple alist term))
         (if (variablep term)
             (if (assoc-eq term alist)
                 (cadr (assoc-eq term alist))
               nil)
           (car term)))
  :hints (("Goal" :in-theory (enable sublis-var-simple))))

(defthm consp-of-sublis-var-simple
  (implies (consp term)
           (consp (sublis-var-simple alist term)))
  :hints (("Goal" :expand ((sublis-var-simple alist term)))))

(defthm cdr-of-sublis-var-simple
  (equal (cdr (sublis-var-simple alist term))
         (if (variablep term)
             (if (assoc-eq term alist)
                 (cddr (assoc-eq term alist))
               nil)
           (if (equal 'quote (car term))
               (cdr term)
             (sublis-var-simple-lst alist (cdr term)))))
  :hints (("Goal" :in-theory (enable sublis-var-simple))))

(defthm car-of-sublis-var-simple-lst
  (implies (consp terms)
           (equal (car (sublis-var-simple-lst alist terms))
                  (sublis-var-simple alist (car terms))))
  :hints (("Goal" :expand (sublis-var-simple-lst alist terms)
           :in-theory (enable sublis-var-simple-lst))))

(local
 (defthm symbolp-of-cdr-of-assoc-equal-when-symbol-listp-of-strip-cdrs
   (implies (symbol-listp (strip-cdrs alist))
            (symbolp (cdr (assoc-equal term alist))))
   :hints (("Goal" :in-theory (enable assoc-equal strip-cdrs)))))

(defthm-flag-sublis-var-simple
  ;; If we apply a variable renaming to a variable, we get a variable back.
  (defthm symbolp-of-sublis-var-simple-when-symbolp
    (implies (and (symbol-listp (strip-cdrs alist))
                  (symbolp term))
             (symbolp (sublis-var-simple alist term)))
    :flag sublis-var-simple)
  (defthm symbol-listp-of-sublis-var-simple-lst-when-symbol-listp
    (implies (and (symbol-listp (strip-cdrs alist))
                  (symbol-listp terms))
             (symbol-listp (sublis-var-simple-lst alist terms)))
    :flag sublis-var-simple-lst)
  :hints (("Goal" :in-theory (enable sublis-var-simple
                                     sublis-var-simple-lst))))

(defthm-flag-sublis-var-simple
  (defthm no-nils-in-termp-of-sublis-var-simple
    (implies (and (no-nils-in-termsp (strip-cdrs alist))
                  (no-nils-in-termp term))
             (no-nils-in-termp (sublis-var-simple alist term)))
    :flag sublis-var-simple)
  (defthm no-nils-in-termsp-of-sublis-var-simple-lst
    (implies (and (no-nils-in-termsp (strip-cdrs alist))
                  (no-nils-in-termsp terms))
             (no-nils-in-termsp (sublis-var-simple-lst alist terms)))
    :flag sublis-var-simple-lst)
  :hints (("Goal" :expand (no-nils-in-termp (cons (car term) (sublis-var-simple-lst alist (cdr term)))) ; todo
           :in-theory (enable sublis-var-simple
                                     sublis-var-simple-lst
                                     ;no-nils-in-termp ; todo
                                     ))))

(defthm sublis-var-simple-when-not-consp
  (implies (not (consp term))
           (equal (sublis-var-simple alist term)
                  (let ((res (assoc-eq term alist)))
                    (if res (cdr res) term))))
  :hints (("Goal" :in-theory (enable sublis-var-simple))))

(defthm-flag-sublis-var-simple
  (defthm lambdas-closed-in-termp-of-sublis-var-simple
    (implies (and ;;(pseudo-termp term)
                  (lambdas-closed-in-termp term)
                  (lambdas-closed-in-termsp (strip-cdrs alist)))
             (lambdas-closed-in-termp (sublis-var-simple alist term)))
    :flag sublis-var-simple)
  (defthm lambdas-closed-in-termp-of-sublis-var-lst-simple
    (implies (and ;;(pseudo-term-listp terms)
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
  (defthm subsetp-equal-of-free-vars-in-terms-of-sublis-var-simple-lst-and-free-vars-in-terms-of-strip-cdrs
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


(defthm-flag-free-vars-in-term
  (defthm subsetp-equal-of-free-vars-in-term
    (implies (alistp alist)
             (subsetp-equal (free-vars-in-term (sublis-var-simple alist term))
                            (union-equal (set-difference-equal (free-vars-in-term term)
                                                               (strip-cars alist))
                                         (free-vars-in-terms (strip-cdrs alist)))))
    :flag free-vars-in-term)
  (defthm subsetp-equal-of-free-vars-in-terms
    (implies (alistp alist)
             (subsetp-equal (free-vars-in-terms (sublis-var-simple-lst alist terms))
                            (union-equal (set-difference-equal (free-vars-in-terms terms)
                                                               (strip-cars alist))
                                         (free-vars-in-terms (strip-cdrs alist)))))
    :flag free-vars-in-terms)
  :hints (("Goal" :in-theory (enable sublis-var-simple
                                     sublis-var-simple-lst
                                     free-vars-in-term
                                     free-vars-in-terms
                                     assoc-equal
                                     member-equal-of-strip-cars-iff))))

(defthm subsetp-equal-of-free-vars-in-term-of-sublis-var-simple-gen
  (implies (and (alistp alist)
                (subsetp-equal (union-equal (set-difference-equal (free-vars-in-term term)
                                                               (strip-cars alist))
                                            (free-vars-in-terms (strip-cdrs alist)))
                               x))
           (subsetp-equal (free-vars-in-term (sublis-var-simple alist term))
                          x))
  :hints (("Goal" :use subsetp-equal-of-free-vars-in-term
           :in-theory (disable subsetp-equal-of-free-vars-in-term))))


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

;; Requires the alist to cover all the free vars
(defthm-flag-sublis-var-simple
  (defthm sublis-var-simple-correct2
    (implies (and (subsetp-equal (free-vars-in-term term) (strip-cars alist)) ; this case
                  (symbol-alistp alist) ; usually a symbol-term-alistp
                  (pseudo-term-listp (strip-cdrs alist))
                  (pseudo-termp term)
                  (not (member-equal nil (free-vars-in-term term))))
             (equal (empty-eval (sublis-var-simple alist term) a)
                    (empty-eval term (pairlis$ (strip-cars alist)
                                                (empty-eval-list (strip-cdrs alist) a)))))
    :flag sublis-var-simple)
  (defthm sublis-var-simple-lst-correct2
    (implies (and (subsetp-equal (free-vars-in-terms terms) (strip-cars alist)) ; this case
                  (symbol-alistp alist) ; usually a symbol-term-alistp
                  (pseudo-term-listp (strip-cdrs alist))
                  (pseudo-term-listp terms)
                  (not (member-equal nil (free-vars-in-terms terms))))
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

(defthm-flag-sublis-var-simple
  (defthmd sublis-var-simple-correct-3
    (implies (and (symbol-alistp alist) ; usually a symbol-term-alistp
                  (pseudo-term-listp (strip-cdrs alist))
                  (pseudo-termp term)
                  ;; since defevaluator has gross behavior on nil:
                  (not (member-equal nil (free-vars-in-term term))))
             (equal (empty-eval (sublis-var-simple alist term) a)
                    (empty-eval term (append (pairlis$ (strip-cars alist)
                                                       (empty-eval-list (strip-cdrs alist) a))
                                             a))))
    :flag sublis-var-simple)
  (defthmd sublis-var-simple-lst-correct-3
    (implies (and (symbol-alistp alist) ; usually a symbol-term-alistp
                  (pseudo-term-listp (strip-cdrs alist))
                  (pseudo-term-listp terms)
                  (not (member-equal nil (free-vars-in-terms terms))))
             (equal (empty-eval-list (sublis-var-simple-lst alist terms) a)
                    (empty-eval-list terms (append (pairlis$ (strip-cars alist)
                                                             (empty-eval-list (strip-cdrs alist) a))
                                                   a))))
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


;move
(defthm no-duplicate-lambda-formals-in-termp-of-cdr-of-assoc-equal
  (implies (no-duplicate-lambda-formals-in-termsp (strip-cdrs alist))
           (no-duplicate-lambda-formals-in-termp (cdr (assoc-equal key alist))))
  :hints (("Goal" :in-theory (enable assoc-equal))))

;move up
(defthm-flag-sublis-var-simple
  (defthm no-duplicate-lambda-formals-in-termp-of-sublis-var-simple
    (implies (and ;;(pseudo-termp term)
                  (no-duplicate-lambda-formals-in-termp term)
                  (no-duplicate-lambda-formals-in-termsp (strip-cdrs alist)))
             (no-duplicate-lambda-formals-in-termp (sublis-var-simple alist term)))
    :flag sublis-var-simple)
  (defthm no-duplicate-lambda-formals-in-termp-of-sublis-var-lst-simple
    (implies (and ;;(pseudo-term-listp terms)
                  (no-duplicate-lambda-formals-in-termsp terms)
                  (no-duplicate-lambda-formals-in-termsp (strip-cdrs alist)))
             (no-duplicate-lambda-formals-in-termsp (sublis-var-simple-lst alist terms)))
    :flag sublis-var-simple-lst)
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable sublis-var-simple
                              sublis-var-simple-lst
                              no-duplicate-lambda-formals-in-termp))))
