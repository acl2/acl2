; Proof of correctness of expand-lambdas-in-term
;
; Copyright (C) 2021-2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This book proves that the meaning of terms (expressed wrt an evaluator) is
;; preserved by expand-lambdas-in-term.

;; TODO: Prove that the result is lambda-free.

(include-book "expand-lambdas-in-term")
(include-book "make-lambda-term-simple")
(include-book "no-nils-in-termp")
(include-book "kestrel/evaluators/empty-eval" :dir :system)
(include-book "kestrel/alists-light/alists-equiv-on" :dir :system)
(local (include-book "kestrel/alists-light/assoc-equal" :dir :system))
(local (include-book "kestrel/alists-light/strip-cars" :dir :system))
(local (include-book "kestrel/alists-light/strip-cdrs" :dir :system))
(local (include-book "kestrel/alists-light/pairlis-dollar" :dir :system))
(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/lists-light/nthcdr" :dir :system))
(local (include-book "kestrel/lists-light/take" :dir :system))
(local (include-book "kestrel/lists-light/member-equal" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/set-difference-equal" :dir :system))
(local (include-book "kestrel/lists-light/no-duplicatesp-equal" :dir :system))
(local (include-book "kestrel/lists-light/cons" :dir :system))
(local (include-book "kestrel/lists-light/subsetp-equal" :dir :system))
(local (include-book "kestrel/arithmetic-light/less-than" :dir :system))
(local (include-book "kestrel/typed-lists-light/symbol-listp" :dir :system))
(local (include-book "kestrel/typed-lists-light/pseudo-term-listp" :dir :system))
(local (include-book "kestrel/alists-light/lookup-equal-lst" :dir :system))

(local (in-theory (disable member-equal symbol-listp set-difference-equal pseudo-term-listp len strip-cadrs strip-cdrs)))

;todo: automate some of this?

(defthm cdr-of-expand-lambdas-in-terms
  (equal (cdr (expand-lambdas-in-terms terms))
         (expand-lambdas-in-terms (cdr terms)))
  :hints (("Goal" :induct (len terms)
           :in-theory (enable (:i len) expand-lambdas-in-terms))))

(defthm subsetp-equal-of-free-vars-in-term-of-sublis-var-simple-and-free-vars-in-terms-of-strip-cdrs-gen
  (implies (and (subsetp-equal (free-vars-in-term term) ; the alist binds all the vars, so any fee vars in the result come from the alist
                               (strip-cars alist))
                (subsetp-equal (free-vars-in-terms (strip-cdrs alist)) free))
           (subsetp-equal (free-vars-in-term (sublis-var-simple alist term))
                          free)))

;this holds for any evaluator?
;term may often be a var
(defthmd empty-eval-of-cdr-of-assoc-equal
  (equal (empty-eval (cdr (assoc-equal term alist)) a)
         ;; evaluates all the terms in the alist wrt a and then looks up the term:
         (cdr (assoc-equal term (pairlis$ (strip-cars alist)
                                          (empty-eval-list (strip-cdrs alist)
                                                           a)))))
  :hints (("Goal" :in-theory (enable pairlis$ assoc-equal))))

(local
 (mutual-recursion
  ;; The whole point of this is to recur on a different alist in the lambda case
  (defund expand-lambdas-in-term-induct (term a)
    (declare (xargs :measure (acl2-count term))
             (irrelevant a))
    (if (or (variablep term)
            (fquotep term))
        term
      (let* ((args (fargs term))
             (args (expand-lambdas-in-terms-induct args a))
             (fn (ffn-symb term)))
        (if (flambdap fn)
            (let* ((lambda-body (expand-lambdas-in-term-induct (lambda-body fn)
                                                               (pairlis$ (lambda-formals fn) (empty-eval-list args a)) ;note this!
                                                               )))
              (sublis-var-simple (pairlis$ (lambda-formals fn) args) lambda-body))
          `(,fn ,@args)))))

  (defund expand-lambdas-in-terms-induct (terms a)
    (declare (xargs :measure (acl2-count terms))
             (irrelevant a))
    (if (endp terms)
        nil
      (cons (expand-lambdas-in-term-induct (first terms) a)
            (expand-lambdas-in-terms-induct (rest terms) a))))))

(defthm empty-eval-of-make-lambda-term-simple-when-symbolp
  (implies (and (symbolp var)
;                (symbol-listp lambda-formals)
;                (pseudo-term-listp args)
                (equal (len lambda-formals) (len args)))
           (equal (empty-eval (make-lambda-term-simple lambda-formals args var) a)
                  (if (equal var nil) ; gross exception in defevaluator
                      nil
                    (if (member-equal var lambda-formals)
                        (empty-eval (cdr (assoc-equal var (pairlis$ lambda-formals args)))
                                     a)
                      (empty-eval var a)))))
  :hints (("Goal" :in-theory (enable make-lambda-term-simple
                                     ;;assoc-equal-iff
                                     empty-eval-of-cdr-of-assoc-equal
                                     ))))


;this holds for any evaluator?
(local
 (defthm empty-eval-list-when-symbol-listp
  (implies (and (symbol-listp vars)
                (not (member-equal nil vars)) ;evaluating nil just gives nil
                )
           (equal (empty-eval-list vars a)
                  (lookup-equal-lst vars a)))
  :hints (("Goal" :in-theory (enable ;empty-eval-list
                              (:i len)
                              LOOKUP-EQUAL)
           :induct (len vars)))))

;; empty-eval gives the same result if the alist is changed to one that equivalent for the free vars of the term
(defthm-flag-free-vars-in-term
  (defthm equal-of-empty-eval-and-empty-eval-when-alists-equiv-on
    (implies (and (alists-equiv-on (free-vars-in-term term) alist1 alist2)
                  (pseudo-termp term))
             (equal (equal (empty-eval term alist1)
                           (empty-eval term alist2))
                    t))
    :flag free-vars-in-term)
  (defthm equal-of-empty-eval-list-and-empty-eval-list-when-alists-equiv-on
    (implies (and (alists-equiv-on (free-vars-in-terms terms) alist1 alist2)
                  (pseudo-term-listp terms))
             (equal (equal (empty-eval-list terms alist1)
                           (empty-eval-list terms alist2))
                    t))
    :flag free-vars-in-terms)
  :hints (("Goal" :expand (PSEUDO-TERMP TERM)
           :in-theory (e/d (free-vars-in-terms
                            empty-eval-of-fncall-args)
                           (empty-eval-of-fncall-args-back)))))

(defthm equal-of-car-of-assoc-equal-same
  (implies (alistp alist)
           (iff (equal key (car (assoc-equal key alist)))
                (or (equal key nil)
                    (assoc-equal key alist)))))

;; (defun cdr-remove-caar-induct-2 (x y)
;;   (if (or (endp x)
;;           (endp y))
;;       (list x y)
;;     (cdr-remove-caar-induct-2 (cdr x) (remove-equal (caar x) y))))

(defthm assoc-equal-of-pairlis$-when-not-member-equal
  (implies (not (member-equal key keys))
           (equal (assoc-equal key (pairlis$ keys vals))
                  nil)))

(local
 (defthm assoc-equal-of-pairlis$-of-lookup-equal-lst-same
  (implies (alistp alist)
           (equal (assoc-equal key (pairlis$ keys (lookup-equal-lst keys alist)))
                  (if (member-equal key keys)
                      (cons key (cdr (assoc-equal key alist)))
                    nil)))
  :hints (("Goal" :in-theory (enable assoc-equal lookup-equal-lst pairlis$ LOOKUP-EQUAL)))))

(local
 (defthm alists-equiv-on-of-pairlis$-of-lookup-equal-lst-same
  (alists-equiv-on keys
                   (pairlis$ keys (lookup-equal-lst keys a))
                   a)
  :hints (("Goal" :expand (ALISTS-EQUIV-ON KEYS
                                           (PAIRLIS$ KEYS (LOOKUP-EQUAL-LST KEYS A))
                                           A)
;:induct (ALISTS-EQUIV-ON KEYS a a)
           :in-theory (enable pairlis$ lookup-equal
                              assoc-equal-iff
                              (:I len))))))

;; term may have free vars not among the lambda formals
(defthm empty-eval-of-make-lambda-term-simple
  (implies (and (pseudo-termp term)
                (not (member-equal nil (free-vars-in-term term))) ;drop? may need the notion of alists agreeing on a set of keys not involving nil
                (equal (len lambda-formals) (len args)))
           (equal (empty-eval (make-lambda-term-simple lambda-formals args term) a)
                  (empty-eval term
                               (append (pairlis$ lambda-formals (empty-eval-list args a)) ; these pairs may shadow pairs in a
                                       a))))
  :hints (("Goal" :in-theory (enable make-lambda-term-simple))))

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

(defund make-lambda-terms-simple (lambda-formals args terms)
  (if (endp terms)
      nil
    (cons (make-lambda-term-simple lambda-formals args (first terms))
          (make-lambda-terms-simple lambda-formals args (rest terms)))))

(defthm make-lambda-terms-simple-of-nil
  (equal (make-lambda-terms-simple lambda-formals args nil)
         nil)
  :hints (("Goal" :in-theory (enable make-lambda-terms-simple))))

(defthm empty-eval-list-of-make-lambda-terms-simple
  (implies (and (pseudo-term-listp terms)
                (not (member-equal nil (free-vars-in-terms terms))) ;drop?
                (equal (len lambda-formals) (len args)))
           (equal (empty-eval-list (make-lambda-terms-simple lambda-formals args terms) a)
                  (empty-eval-list terms
                                    (append (pairlis$ lambda-formals (empty-eval-list args a)) ; these pairs may shadow pairs in a
                                            a))))
  :hints (("Goal" :in-theory (enable make-lambda-terms-simple))))

;; The result of sublis-var-simple evaluates the same as if we had made a lambda.
;move
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

;; Expanding lambdas does not introduce any new free vars.
(defthm-flag-expand-lambdas-in-term
  (defthm subsetp-equal-of-free-vars-in-term-of-expand-lambdas-in-term
    (implies (and (pseudo-termp term)
                  (lambdas-closed-in-termp term))
             (subsetp-equal (free-vars-in-term (expand-lambdas-in-term term))
                            (free-vars-in-term term)))
    :flag expand-lambdas-in-term)
  (defthm subsetp-equal-of-free-vars-in-terms-of-expand-lambdas-in-terms
    (implies (and (pseudo-term-listp terms)
                  (lambdas-closed-in-termsp terms))
             (subsetp-equal (free-vars-in-terms (expand-lambdas-in-terms terms))
                            (free-vars-in-terms terms)))
    :flag expand-lambdas-in-terms)
  :hints (("Goal" :expand ((expand-lambdas-in-term terms)
                           (free-vars-in-term term))
           :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (expand-lambdas-in-term
                            empty-eval-of-fncall-args
                            free-vars-in-terms
                            lambdas-closed-in-termp)
                           (empty-eval-of-fncall-args-back)))))

(defthm subsetp-equal-of-free-vars-in-term-of-expand-lambdas-in-term-gen
  (implies (and (pseudo-termp term)
                (lambdas-closed-in-termp term)
                (subsetp-equal (free-vars-in-term term) free))
           (subsetp-equal (free-vars-in-term (expand-lambdas-in-term term))
                          free)))

(defthm not-member-equal-of-free-var-in-term-of-expand-lambdas-in-term
  (implies (and (not (member-equal var (free-vars-in-term term)))
                (pseudo-termp term)
                (lambdas-closed-in-termp term))
           (not (member-equal var (free-vars-in-term (expand-lambdas-in-term term))))))


(local
 (make-flag expand-lambdas-in-term-induct))

(local
 (defthm-flag-expand-lambdas-in-term-induct
   (defthm expand-lambdas-in-term-induct-removal
     (equal (expand-lambdas-in-term-induct term a)
            (expand-lambdas-in-term term))
     :flag expand-lambdas-in-term-induct)
   (defthm expand-lambdas-in-terms-induct-removal
     (equal (expand-lambdas-in-terms-induct terms a)
            (expand-lambdas-in-terms terms))
     :flag expand-lambdas-in-terms-induct)
   :hints (("Goal" :in-theory (enable EXPAND-LAMBDAS-IN-TERM
                                      EXPAND-LAMBDAS-IN-TERMs
                                      EXPAND-LAMBDAS-IN-TERM-induct
                                      EXPAND-LAMBDAS-IN-TERMs-induct)))))

;; Correctness of expand-lambdas-in-term: The meaning of terms is preserved.
;; TODO: Can some assumptions be dropped?
(defthm-flag-expand-lambdas-in-term-induct
  (defthm expand-lambdas-in-term-correct
    (implies (and (pseudo-termp term)
                  (no-nils-in-termp term)
                  (lambdas-closed-in-termp term))
             (equal (empty-eval (expand-lambdas-in-term term) a)
                    (empty-eval term a)))
    :flag expand-lambdas-in-term-induct)
  (defthm expand-lambdas-in-terms-correct
    (implies (and (pseudo-term-listp terms)
                  (no-nils-in-termsp terms)
                  (lambdas-closed-in-termsp terms))
             (equal (empty-eval-list (expand-lambdas-in-terms terms) a)
                    (empty-eval-list terms a)))
    :flag expand-lambdas-in-terms-induct)
  :hints (("Goal" :expand ((expand-lambdas-in-term terms)
                           (free-vars-in-term term)
                           (lambdas-closed-in-termp term))
           :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (expand-lambdas-in-term
                            empty-eval-of-fncall-args
                            free-vars-in-terms)
                           (empty-eval-of-fncall-args-back)))))
