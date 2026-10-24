; Correctness of the ACL2 system function remove-guard-holders1
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

; cert_param: (non-acl2r)

;; REMOVE-GUARD-HOLDERS1 (in translate.lisp) does the work of
;; remove-guard-holders-weak and remove-guard-holders, which the prover applies
;; to the terms it gets from events and hints: goals, rules generated from
;; theorems, induction and termination machines, constraints, and more.  It
;; removes "guard holders" and other constructs that matter for guards or
;; execution but not for the logical meaning of a term:
;;
;; - a call of RETURN-LAST, MV-LIST, or THE-CHECK becomes its last argument;
;; - CONS-WITH-HINT becomes CONS;
;; - FROM-DF, and TO-DF of a df constant, are dropped, and DF0 and DF1 become
;;   '0 and '1;
;; - a non-nil quoted 6th argument of DO$ (which is logically irrelevant)
;;   becomes 'NIL;
;; - ((lambda (var) (the-check g y var)) val) becomes val;
;; - ((lambda formals (return-last 'mbe1-raw exec logic)) . args), which
;;   arises from let-mbe in the definitions of equality variants, becomes logic
;;   with the args substituted for the formals (using subcor-var);
;; - when LAMP is true, a lambda with one formal whose body is that formal is
;;   removed, and so is a lambda whose arguments are just its formals;
;; - calls of other functions are rebuilt with cons-term, which may evaluate
;;   calls of primitives on constant arguments.
;;
;; As the source comments say, "The minimal requirement on this function is
;; that it return a term that is provably equal to term."  This book proves
;; that requirement, in terms of an evaluator that knows the functions treated
;; specially and the primitives that cons-term may evaluate.  The result holds
;; whatever the attachment to remove-guard-holders-blocked-by-hide-p (which
;; decides whether calls of HIDE are left alone), since HIDE calls are either
;; left alone or treated like calls of any other function.

;; The correctness theorems require TERMP and the usual arities of
;; RETURN-LAST, MV-LIST, THE-CHECK, CONS-WITH-HINT, TO-DF, and FROM-DF.  The
;; guard (PSEUDO-TERMP) is not enough: see the counterexample in
;; remove-guard-holders1-tests.lisp, which involves a call of THE-CHECK with
;; two arguments.  This
;; doesn't indicate a bug, since ACL2 only applies remove-guard-holders1 to
;; translated terms.  (Not all of the arity hypotheses may be necessary, but
;; the proof uses them.)

(include-book "kestrel/evaluators/defevaluator-plus" :dir :system)
(include-book "system/remove-guard-holders-weak" :dir :system)
(local (include-book "clause-processors/sublis-var-meaning" :dir :system))
(local (include-book "subcor-var"))
(local (include-book "helpers"))
(local (include-book "system/remove-guard-holders1" :dir :system))
(local (include-book "kestrel/terms-light/termp" :dir :system))
(local (include-book "kestrel/lists-light/subsetp-equal" :dir :system))
(local (include-book "kestrel/alists-light/strip-cars" :dir :system))
(local (include-book "kestrel/lists-light/take" :dir :system))
(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "tools/flag" :dir :system))
(local (include-book "system/pseudo-termp-lemmas" :dir :system))
(local (include-book "kestrel/terms-light/empty-eval-helpers" :dir :system))
(local (include-book "system/legal-variablep" :dir :system)) ; speeds up some proofs

(defevaluator+ remove-guard-holders-eval
  ;; the primitives that cons-term may evaluate:
  acl2-numberp binary-* binary-+ unary-- unary-/ < car cdr char-code characterp code-char
  complex complex-rationalp coerce cons consp denominator equal imagpart integerp
  intern-in-package-of-symbol numerator rationalp realpart stringp symbol-name
  symbol-package-name symbolp if not
  ;; the functions treated specially by remove-guard-holders1:
  return-last mv-list the-check cons-with-hint to-df from-df df0 df1 do$)

;; Remove-guard-holders1 builds terms using cons-term and subcor-var.  We
;; transfer their correctness theorems (from
;; clause-processors/sublis-var-meaning.lisp and subcor-var.lisp) to our
;; evaluator:
(local
 (defthm remove-guard-holders-eval-of-cons-term
   (equal (remove-guard-holders-eval (cons-term fn args) a)
          (remove-guard-holders-eval (cons fn args) a))
   :hints (("Goal" :in-theory (e/d (remove-guard-holders-eval-of-fncall-args) (remove-guard-holders-eval-of-fncall-args-back))
            :use (:functional-instance cterm-ev-cons-term-correct
                                       (cterm-ev remove-guard-holders-eval)
                                       (cterm-ev-lst remove-guard-holders-eval-list))))))

(local
 (defthm remove-guard-holders-eval-of-subcor-var
   (implies (and (not (member-equal nil (free-vars-in-term form)))
                 (pseudo-termp form))
            (equal (remove-guard-holders-eval (subcor-var vars terms form) a)
                   (remove-guard-holders-eval form (append (pairlis$ vars (remove-guard-holders-eval-list terms a)) a))))
   :hints (("Goal" :in-theory (e/d (remove-guard-holders-eval-of-fncall-args) (remove-guard-holders-eval-of-fncall-args-back))
            :use (:functional-instance subcor-var-correct
                                       (cterm-ev remove-guard-holders-eval)
                                       (cterm-ev-lst remove-guard-holders-eval-list))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Facts about remove-guard-holders1

;; The term returned doesn't depend on changedp0 (for a pseudo-term, whose
;; lambda applications have true lists of arguments: when changedp0 is true,
;; the lambda case rebuilds the term from the arguments returned by
;; remove-guard-holders1-lst, which are the original arguments if nothing
;; changed).
(local
 (make-flag remove-guard-holders1))

(local
 (defthm cons-term-when-consp
   (implies (consp fn)
            (equal (cons-term fn args)
                   (cons fn args)))
   :hints (("Goal" :in-theory (enable cons-term cons-term1)))))

(local
 (defthm mv-nth-1-of-remove-guard-holders1-lst-when-unchanged-simple
   (implies (and (not (mv-nth 0 (remove-guard-holders1-lst lst lamp)))
                 (true-listp lst))
            (equal (mv-nth 1 (remove-guard-holders1-lst lst lamp))
                   lst))
   :hints (("Goal" :expand ((remove-guard-holders1-lst lst lamp))))))

(local
 (defthm-flag-remove-guard-holders1
   (defthm mv-nth-1-of-remove-guard-holders1-normalize-changedp0-helper
     (implies (pseudo-termp term)
              (equal (mv-nth 1 (remove-guard-holders1 changedp0 term lamp))
                     (mv-nth 1 (remove-guard-holders1 nil term lamp))))
     :rule-classes nil
     :flag remove-guard-holders1)
   (defthm remove-guard-holders1-lst-dummy
     t
     :rule-classes nil
     :flag remove-guard-holders1-lst)
   :hints (("Goal" :expand ((remove-guard-holders1 changedp0 term lamp)
                            (remove-guard-holders1 nil term lamp))))))

(local
 (defthm mv-nth-1-of-remove-guard-holders1-normalize-changedp0
   (implies (and (syntaxp (not (equal changedp0 ''nil)))
                 (pseudo-termp term))
            (equal (mv-nth 1 (remove-guard-holders1 changedp0 term lamp))
                   (mv-nth 1 (remove-guard-holders1 nil term lamp))))
   :hints (("Goal" :use mv-nth-1-of-remove-guard-holders1-normalize-changedp0-helper))))

(local
 (defthm do$-hard-er-dolia-irrelevant
   (implies (syntaxp (not (equal dolia ''nil)))
            (equal (do$-hard-er measure-fn alist values dolia stobj-values-p old-measure-value new-alist)
                   (do$-hard-er measure-fn alist values nil stobj-values-p old-measure-value new-alist)))))

(local
 (defthm do$-dolia-irrelevant
   (implies (syntaxp (not (equal dolia ''nil)))
            (equal (do$ measure-fn alist do-fn finally-fn values dolia)
                   (do$ measure-fn alist do-fn finally-fn values nil)))))

(local
 (defthm consp-of-mv-nth-1-of-remove-guard-holders1-lst
   (equal (consp (mv-nth 1 (remove-guard-holders1-lst lst lamp)))
          (consp lst))
   :hints (("Goal" :expand ((remove-guard-holders1-lst lst lamp))))))

;; The arities of the functions that remove-guard-holders1 treats specially, as
;; in any world that ACL2 actually uses.
(local
 (defund remove-guard-holders1-arities-okp (w)
   (and (equal (arity 'return-last w) 3)
        (equal (arity 'mv-list w) 2)
        (equal (arity 'the-check w) 3)
        (equal (arity 'cons-with-hint w) 3)
        (equal (arity 'to-df w) 1)
        (equal (arity 'from-df w) 1))))

(local
 (defthm arities-when-remove-guard-holders1-arities-okp
   (implies (remove-guard-holders1-arities-okp w)
            (and (equal (arity 'return-last w) 3)
                 (equal (arity 'mv-list w) 2)
                 (equal (arity 'the-check w) 3)
                 (equal (arity 'cons-with-hint w) 3)
                 (equal (arity 'to-df w) 1)
                 (equal (arity 'from-df w) 1)))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable remove-guard-holders1-arities-okp)))))

(local
 (defthm termp-of-car-of-last-of-cdr-when-termp-special
   (implies (and (termp term w)
                 (member-equal (car term) '(return-last mv-list the-check))
                 (remove-guard-holders1-arities-okp w))
            (termp (car (last (cdr term))) w))
   :hints (("Goal" :use termp-of-car-of-last-of-cdr-when-termp
            :in-theory (disable termp-of-car-of-last-of-cdr-when-termp last termp)))))

(local
 (defthm-flag-remove-guard-holders1
   (defthm no-nils-in-termp-of-mv-nth-1-of-remove-guard-holders1
     (implies (and (termp term w)
                   (remove-guard-holders1-arities-okp w))
              (no-nils-in-termp (mv-nth 1 (remove-guard-holders1 changedp0 term lamp))))
     :flag remove-guard-holders1)
   (defthm no-nils-in-termsp-of-mv-nth-1-of-remove-guard-holders1-lst
     (implies (and (term-listp lst w)
                   (remove-guard-holders1-arities-okp w))
              (no-nils-in-termsp (mv-nth 1 (remove-guard-holders1-lst lst lamp))))
     :flag remove-guard-holders1-lst)
   :hints (("Goal" :in-theory (e/d (termp) (member-equal
                                            pseudo-termp-lambda-lemma
                                            take
                                            quote-listp
                                            subcor-var-is-sublis-var1 subcor-var-lst-is-sublis-var1-lst))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Facts about the evaluator

;; Evaluation only depends on the free vars
(local
 (defthm equal-of-remove-guard-holders-eval-and-remove-guard-holders-eval-when-alists-equiv-on
   (implies (and (alists-equiv-on keys alist1 alist2)
                 (subsetp-equal (free-vars-in-term term) keys)
                 (pseudo-termp term))
            (equal (equal (remove-guard-holders-eval term alist1)
                          (remove-guard-holders-eval term alist2))
                   t))
   :hints (("Goal" :in-theory (e/d (remove-guard-holders-eval-of-fncall-args) (remove-guard-holders-eval-of-fncall-args-back))
            :use (:functional-instance equal-of-empty-eval-and-empty-eval-when-alists-equiv-on-alt
                                       (empty-eval remove-guard-holders-eval)
                                       (empty-eval-list remove-guard-holders-eval-list))))))

(local
 (defthm remove-guard-holders-eval-of-append-of-pairlis$-when-closed
   (implies (and (subsetp-equal (free-vars-in-term body) formals)
                 (pseudo-termp body))
            (equal (remove-guard-holders-eval body (append (pairlis$ formals vals) a))
                   (remove-guard-holders-eval body (pairlis$ formals vals))))
   :hints (("Goal" :use (:instance equal-of-remove-guard-holders-eval-and-remove-guard-holders-eval-when-alists-equiv-on
                                   (term body)
                                   (keys formals)
                                   (alist1 (append (pairlis$ formals vals) a))
                                   (alist2 (pairlis$ formals vals)))
            :in-theory (disable equal-of-remove-guard-holders-eval-and-remove-guard-holders-eval-when-alists-equiv-on)))))

(local
 (defthm cdr-of-assoc-equal-of-pairlis$-of-remove-guard-holders-eval-list-same
   (implies (and (member-equal key keys)
                 (symbolp key)
                 key)
            (equal (cdr (assoc-equal key (pairlis$ keys (remove-guard-holders-eval-list keys a))))
                   (cdr (assoc-equal key a))))
   :hints (("Goal" :in-theory (enable pairlis$ assoc-equal)))))

(local
 (defthm alists-equiv-on-of-pairlis$-of-remove-guard-holders-eval-list-same
   (implies (and (subsetp-equal keys formals)
                 (symbol-listp keys)
                 (not (member-equal nil keys)))
            (alists-equiv-on keys
                             (pairlis$ formals (remove-guard-holders-eval-list formals a))
                             a))
   :hints (("Goal" :in-theory (enable alists-equiv-on subsetp-equal)))))

;; Evaluating a closed lambda body after binding the formals to themselves
(local
 (defthm remove-guard-holders-eval-of-pairlis$-of-remove-guard-holders-eval-list-same
   (implies (and (subsetp-equal (free-vars-in-term body) formals)
                 (not (member-equal nil (free-vars-in-term body)))
                 (pseudo-termp body))
            (equal (remove-guard-holders-eval body (pairlis$ formals (remove-guard-holders-eval-list formals a)))
                   (remove-guard-holders-eval body a)))
   :hints (("Goal" :use (:instance equal-of-remove-guard-holders-eval-and-remove-guard-holders-eval-when-alists-equiv-on
                                   (term body)
                                   (keys (free-vars-in-term body))
                                   (alist1 (pairlis$ formals (remove-guard-holders-eval-list formals a)))
                                   (alist2 a))
            :in-theory (disable equal-of-remove-guard-holders-eval-and-remove-guard-holders-eval-when-alists-equiv-on)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Correctness for each case of remove-guard-holders1, assuming correctness for
;; the recursive calls.  Each conclusion has the same left-hand side, so these
;; rules do the work in the main induction below, where remove-guard-holders1
;; is disabled.

(local
 (in-theory (disable remove-guard-holders1 remove-guard-holders1-lst)))

(local
 (defthm car-of-last-when-len-3
   (implies (equal (len x) 3)
            (equal (car (last x)) (caddr x)))))

(local
 (defthm car-of-last-when-len-2
   (implies (equal (len x) 2)
            (equal (car (last x)) (cadr x)))))

(local
 (defthm remove-guard-holders1-correct-case-return-last-mv-list-the-check
   (implies (and (member-equal (car term) '(return-last mv-list the-check))
                 (consp term)
                 (equal (remove-guard-holders-eval (mv-nth 1 (remove-guard-holders1 nil (car (last (cdr term))) lamp)) a)
                        (remove-guard-holders-eval (car (last (cdr term))) a))
                 (termp term w)
                 (remove-guard-holders1-arities-okp w))
            (equal (remove-guard-holders-eval (mv-nth 1 (remove-guard-holders1 nil term lamp)) a)
                   (remove-guard-holders-eval term a)))
   :hints (("Goal" :expand ((remove-guard-holders1 nil term lamp))
            :use len-of-cdr-when-termp
            :in-theory (e/d (member-equal) (len-of-cdr-when-termp last))))))

(local
 (defthm remove-guard-holders1-correct-case-cons-with-hint
   (implies (and (equal (car term) 'cons-with-hint)
                 (equal (remove-guard-holders-eval (mv-nth 1 (remove-guard-holders1 nil (cadr term) lamp)) a)
                        (remove-guard-holders-eval (cadr term) a))
                 (equal (remove-guard-holders-eval (mv-nth 1 (remove-guard-holders1 nil (caddr term) lamp)) a)
                        (remove-guard-holders-eval (caddr term) a)))
            (equal (remove-guard-holders-eval (mv-nth 1 (remove-guard-holders1 nil term lamp)) a)
                   (remove-guard-holders-eval term a)))
   :hints (("Goal" :expand ((remove-guard-holders1 nil term lamp))))))

(local
 (defthm remove-guard-holders1-correct-case-to-df
   (implies (and (equal (car term) 'to-df)
                 (equal (remove-guard-holders-eval (mv-nth 1 (remove-guard-holders1 nil (cadr term) lamp)) a)
                        (remove-guard-holders-eval (cadr term) a)))
            (equal (remove-guard-holders-eval (mv-nth 1 (remove-guard-holders1 nil term lamp)) a)
                   (remove-guard-holders-eval term a)))
   :hints (("Goal" :expand ((remove-guard-holders1 nil term lamp))))))

(local
 (defthm remove-guard-holders1-correct-case-from-df
   (implies (and (equal (car term) 'from-df)
                 (equal (remove-guard-holders-eval (mv-nth 1 (remove-guard-holders1 nil (cadr term) lamp)) a)
                        (remove-guard-holders-eval (cadr term) a)))
            (equal (remove-guard-holders-eval (mv-nth 1 (remove-guard-holders1 nil term lamp)) a)
                   (remove-guard-holders-eval term a)))
   :hints (("Goal" :expand ((remove-guard-holders1 nil term lamp))))))

(local
 (defthm remove-guard-holders1-correct-case-df0
   (implies (equal (car term) 'df0)
            (equal (remove-guard-holders-eval (mv-nth 1 (remove-guard-holders1 nil term lamp)) a)
                   (remove-guard-holders-eval term a)))
   :hints (("Goal" :expand ((remove-guard-holders1 nil term lamp))))))

(local
 (defthm remove-guard-holders1-correct-case-df1
   (implies (equal (car term) 'df1)
            (equal (remove-guard-holders-eval (mv-nth 1 (remove-guard-holders1 nil term lamp)) a)
                   (remove-guard-holders-eval term a)))
   :hints (("Goal" :expand ((remove-guard-holders1 nil term lamp))))))

(local
 (defthm remove-guard-holders1-correct-case-other-fn
   (implies (and (consp term)
                 (symbolp (car term))
                 (not (member-equal (car term) '(quote return-last mv-list the-check cons-with-hint
                                                    to-df from-df df0 df1 do$)))
                 (equal (remove-guard-holders-eval-list (mv-nth 1 (remove-guard-holders1-lst (cdr term) lamp)) a)
                        (remove-guard-holders-eval-list (cdr term) a)))
            (equal (remove-guard-holders-eval (mv-nth 1 (remove-guard-holders1 nil term lamp)) a)
                   (remove-guard-holders-eval term a)))
   :hints (("Goal" :expand ((remove-guard-holders1 nil term lamp))
            :in-theory (e/d (remove-guard-holders-eval-of-fncall-args) (remove-guard-holders-eval-of-fncall-args-back))))))

(local
 (defthm remove-guard-holders-eval-list-of-take
   (equal (remove-guard-holders-eval-list (take n l) a)
          (take n (remove-guard-holders-eval-list l a)))
   :hints (("Goal" :in-theory (enable take)))))

(local
 (defthm remove-guard-holders-eval-of-do$-call-alt
   (implies (and (equal (car term) 'do$)
                 (consp term))
            (equal (remove-guard-holders-eval term a)
                   (let ((vals (remove-guard-holders-eval-list (cdr term) a)))
                     (do$ (nth 0 vals) (nth 1 vals) (nth 2 vals) (nth 3 vals) (nth 4 vals) (nth 5 vals)))))))

(local
 (defthm remove-guard-holders1-correct-case-do$
   (implies (and (equal (car term) 'do$)
                 (equal (remove-guard-holders-eval-list (mv-nth 1 (remove-guard-holders1-lst (cdr term) lamp)) a)
                        (remove-guard-holders-eval-list (cdr term) a)))
            (equal (remove-guard-holders-eval (mv-nth 1 (remove-guard-holders1 nil term lamp)) a)
                   (remove-guard-holders-eval term a)))
   :hints (("Goal" :expand ((remove-guard-holders1 nil term lamp))
            :in-theory (e/d (remove-guard-holders-eval-of-do$-call-alt) (remove-guard-holders-eval-of-do$-call))))))

;; The lambda case needs more facts, about the formals, body, and arguments of
;; the lambda:

(local
 (defthm termp-of-cadddr-when-return-last
   (implies (and (termp term w)
                 (equal (car term) 'return-last)
                 (remove-guard-holders1-arities-okp w))
            (termp (cadddr term) w))
   :hints (("Goal" :expand ((termp term w) (term-listp (cdr term) w) (term-listp (cddr term) w)
                            (term-listp (cdddr term) w))))))

(local
 (defthm subsetp-equal-of-free-vars-in-term-of-cadddr
   (implies (and (consp term)
                 (not (equal 'quote (car term)))
                 (consp (cdddr term)))
            (subsetp-equal (free-vars-in-term (cadddr term))
                           (free-vars-in-term term)))
   :hints (("Goal" :expand ((free-vars-in-term term)
                            (free-vars-in-terms (cdr term))
                            (free-vars-in-terms (cddr term))
                            (free-vars-in-terms (cdddr term)))))))

(local
 (defthm remove-guard-holders-eval-when-no-free-vars
   (implies (and (syntaxp (not (equal a ''nil)))
                 (not (consp (free-vars-in-term term)))
                 (pseudo-termp term))
            (equal (remove-guard-holders-eval term a)
                   (remove-guard-holders-eval term nil)))
   :hints (("Goal" :use (:instance equal-of-remove-guard-holders-eval-and-remove-guard-holders-eval-when-alists-equiv-on
                                   (keys nil) (alist1 a) (alist2 nil))
            :in-theory (disable equal-of-remove-guard-holders-eval-and-remove-guard-holders-eval-when-alists-equiv-on)))))

(local
 (defthm remove-guard-holders-eval-of-pairlis$-when-values-are-own
   (implies (and (equal (remove-guard-holders-eval-list formals a) vals) ; binds a
                 (subsetp-equal (free-vars-in-term body) formals)
                 (not (member-equal nil (free-vars-in-term body)))
                 (pseudo-termp body))
            (equal (remove-guard-holders-eval body (pairlis$ formals vals))
                   (remove-guard-holders-eval body a)))))

(local
 (defthm remove-guard-holders-eval-of-singleton-alist-when-closed
   (implies (and (subsetp-equal (free-vars-in-term body) formals) ; formals is a free var
                 (equal (car formals) v)
                 (not (consp (cdr formals)))
                 (pseudo-termp body))
            (equal (remove-guard-holders-eval body (list (cons v (cdr (assoc-equal v a)))))
                   (remove-guard-holders-eval body a)))
   :hints (("Goal" :use (:instance equal-of-remove-guard-holders-eval-and-remove-guard-holders-eval-when-alists-equiv-on
                                   (term body)
                                   (keys formals)
                                   (alist1 (list (cons v (cdr (assoc-equal v a)))))
                                   (alist2 a))
            :expand ((alists-equiv-on formals (list (cons (car formals) (cdr (assoc-equal (car formals) a)))) a))
            :in-theory (e/d (alists-equiv-on) (equal-of-remove-guard-holders-eval-and-remove-guard-holders-eval-when-alists-equiv-on))))))

(local
 (defthm remove-guard-holders-eval-of-lambda-body-singleton-alist
   (implies (and (termp term w)
                 (consp (car term))
                 (equal (car (cadr (car term))) v)
                 (not (consp (cdr (cadr (car term))))))
            (equal (remove-guard-holders-eval (caddr (car term)) (list (cons v (cdr (assoc-equal v a)))))
                   (remove-guard-holders-eval (caddr (car term)) a)))
   :hints (("Goal" :use (subsetp-equal-of-free-vars-in-term-of-lambda-body-of-car-when-termp
                         (:instance remove-guard-holders-eval-of-singleton-alist-when-closed
                                    (body (caddr (car term)))
                                    (formals (cadr (car term)))))
            :in-theory (disable subsetp-equal-of-free-vars-in-term-of-lambda-body-of-car-when-termp
                                remove-guard-holders-eval-of-singleton-alist-when-closed)))))

(local
 (defthm remove-guard-holders-eval-of-car-of-mv-nth-1-of-remove-guard-holders1-lst
   (implies (equal (remove-guard-holders-eval-list (mv-nth 1 (remove-guard-holders1-lst lst lamp)) a)
                   (remove-guard-holders-eval-list lst a))
            (equal (remove-guard-holders-eval (car (mv-nth 1 (remove-guard-holders1-lst lst lamp))) a)
                   (remove-guard-holders-eval (car lst) a)))
   :hints (("Goal" :use ((:instance car-of-remove-guard-holders-eval-list (terms (mv-nth 1 (remove-guard-holders1-lst lst lamp))))
                         (:instance car-of-remove-guard-holders-eval-list (terms lst)))
            :in-theory (disable car-of-remove-guard-holders-eval-list)))))

(local
 (defthm remove-guard-holders-eval-of-lambda-body-when-formals-eval-like-args
   (implies (and (equal (remove-guard-holders-eval-list (cadr (car term)) a) (remove-guard-holders-eval-list (cdr term) a))
                 (termp term w)
                 (consp (car term)))
            (equal (remove-guard-holders-eval (caddr (car term)) (pairlis$ (cadr (car term)) (remove-guard-holders-eval-list (cdr term) a)))
                   (remove-guard-holders-eval (caddr (car term)) a)))
   :hints (("Goal" :use ((:instance remove-guard-holders-eval-of-pairlis$-when-values-are-own
                                    (body (caddr (car term)))
                                    (formals (cadr (car term)))
                                    (vals (remove-guard-holders-eval-list (cdr term) a)))
                         subsetp-equal-of-free-vars-in-term-of-lambda-body-of-car-when-termp)
            :in-theory (disable remove-guard-holders-eval-of-pairlis$-when-values-are-own)))))

;; Facts about the "logic" part of a lambda body of the form
;; (return-last 'mbe1-raw exec logic), which arises from let-mbe:
(local
 (defthm termp-of-mbe1-raw-logic-when-termp
   (implies (and (termp term w)
                 (consp (car term))
                 (equal (car (caddr (car term))) 'return-last)
                 (remove-guard-holders1-arities-okp w))
            (termp (cadddr (caddr (car term))) w))))

(local
 (defthm pseudo-termp-of-mbe1-raw-logic-when-termp
   (implies (and (termp term w)
                 (consp (car term))
                 (equal (car (caddr (car term))) 'return-last)
                 (remove-guard-holders1-arities-okp w))
            (pseudo-termp (cadddr (caddr (car term)))))))

(local
 (defthm no-nils-in-termp-of-remove-guard-holders1-of-mbe1-raw-logic
   (implies (and (termp term w)
                 (consp (car term))
                 (equal (car (caddr (car term))) 'return-last)
                 (remove-guard-holders1-arities-okp w))
            (no-nils-in-termp (mv-nth 1 (remove-guard-holders1 changedp0 (cadddr (caddr (car term))) lamp))))))

(local
 (defthm subsetp-equal-of-free-vars-in-term-of-mbe1-raw-logic
   (implies (and (termp term w)
                 (consp (car term))
                 (equal (car (caddr (car term))) 'return-last)
                 (remove-guard-holders1-arities-okp w))
            (subsetp-equal (free-vars-in-term (cadddr (caddr (car term))))
                           (cadr (car term))))
   :hints (("Goal" :use (subsetp-equal-of-free-vars-in-term-of-lambda-body-of-car-when-termp
                         (:instance subsetp-equal-of-free-vars-in-term-of-cadddr (term (caddr (car term)))))
            :in-theory (disable subsetp-equal-of-free-vars-in-term-of-lambda-body-of-car-when-termp
                                subsetp-equal-of-free-vars-in-term-of-cadddr)))))

(local
 (defthm not-consp-of-free-vars-in-term-of-mbe1-raw-logic-when-no-formals
   (implies (and (termp term w)
                 (consp (car term))
                 (equal (car (caddr (car term))) 'return-last)
                 (remove-guard-holders1-arities-okp w)
                 (not (consp (cadr (car term)))))
            (not (consp (free-vars-in-term (cadddr (caddr (car term)))))))
   :hints (("Goal" :use subsetp-equal-of-free-vars-in-term-of-mbe1-raw-logic
            :in-theory (e/d (subsetp-equal) (subsetp-equal-of-free-vars-in-term-of-mbe1-raw-logic))))))

(local
 (defthm remove-guard-holders1-correct-case-lambda
   (implies (and (consp (car term))
                 (equal (remove-guard-holders-eval-list (mv-nth 1 (remove-guard-holders1-lst (cdr term) lamp)) a)
                        (remove-guard-holders-eval-list (cdr term) a))
                 (implies (consp (cadr (car term)))
                          (equal (remove-guard-holders-eval (mv-nth 1 (remove-guard-holders1 nil (cadr term) lamp)) a)
                                 (remove-guard-holders-eval (cadr term) a)))
                 (equal (remove-guard-holders-eval (mv-nth 1 (remove-guard-holders1 nil (caddr (car term)) lamp)) a)
                        (remove-guard-holders-eval (caddr (car term)) a))
                 (equal (remove-guard-holders-eval (mv-nth 1 (remove-guard-holders1 nil (caddr (car term)) lamp))
                                  (pairlis$ (cadr (car term)) (remove-guard-holders-eval-list (cdr term) a)))
                        (remove-guard-holders-eval (caddr (car term))
                                  (pairlis$ (cadr (car term)) (remove-guard-holders-eval-list (cdr term) a))))
                 (implies (and (consp (caddr (car term)))
                               (equal (car (caddr (car term))) 'return-last))
                          (equal (remove-guard-holders-eval (mv-nth 1 (remove-guard-holders1 nil (cadddr (caddr (car term))) lamp))
                                           (append (pairlis$ (cadr (car term)) (remove-guard-holders-eval-list (cdr term) a)) a))
                                 (remove-guard-holders-eval (cadddr (caddr (car term)))
                                           (append (pairlis$ (cadr (car term)) (remove-guard-holders-eval-list (cdr term) a)) a))))
                 (termp term w)
                 (remove-guard-holders1-arities-okp w))
            (equal (remove-guard-holders-eval (mv-nth 1 (remove-guard-holders1 nil term lamp)) a)
                   (remove-guard-holders-eval term a)))
   :hints (("Goal" :expand ((remove-guard-holders1 nil term lamp))
            :use subsetp-equal-of-free-vars-in-term-of-lambda-body-of-car-when-termp
            :in-theory (e/d (remove-guard-holders-eval-of-fncall-args)
                            (remove-guard-holders-eval-of-fncall-args-back
                             remove-guard-holders-eval-list-when-symbol-listp
                             take quote-listp
                             subcor-var-is-sublis-var1 subcor-var-lst-is-sublis-var1-lst))))))

(local
 (defthm remove-guard-holders1-correct-case-variable
   (implies (variablep term)
            (equal (remove-guard-holders-eval (mv-nth 1 (remove-guard-holders1 nil term lamp)) a)
                   (remove-guard-holders-eval term a)))
   :hints (("Goal" :expand ((remove-guard-holders1 nil term lamp))))))

(local
 (defthm remove-guard-holders1-correct-case-quote
   (implies (fquotep term)
            (equal (remove-guard-holders-eval (mv-nth 1 (remove-guard-holders1 nil term lamp)) a)
                   (remove-guard-holders-eval term a)))
   :hints (("Goal" :expand ((remove-guard-holders1 nil term lamp))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The main induction

;; An induction scheme that follows the case structure of remove-guard-holders1.
;; For lambdas, it evaluates the body under the alist that binds the formals to
;; the values of the arguments.
(local
 (defun induct-remove-guard-holders1 (flg x a)
   (declare (xargs :measure (acl2-count x)
                   :ruler-extenders :all
                   :verify-guards nil))
   (if flg
       (cond ((or (variablep x) (fquotep x)) a)
             ((flambdap (ffn-symb x))
              (list (induct-remove-guard-holders1 nil (fargs x) a)
                    (if (consp (lambda-formals (ffn-symb x)))
                        (induct-remove-guard-holders1 t (car (fargs x)) a)
                      a)
                    (induct-remove-guard-holders1 t (lambda-body (ffn-symb x)) a)
                    (induct-remove-guard-holders1 t (lambda-body (ffn-symb x))
                                (pairlis$ (lambda-formals (ffn-symb x)) (remove-guard-holders-eval-list (fargs x) a)))
                    (if (and (consp (lambda-body (ffn-symb x)))
                             (eq (car (lambda-body (ffn-symb x))) 'return-last))
                        (induct-remove-guard-holders1 t (car (cdr (cdr (cdr (lambda-body (ffn-symb x))))))
                                    (append (pairlis$ (lambda-formals (ffn-symb x)) (remove-guard-holders-eval-list (fargs x) a)) a))
                      a)))
             ((member-eq (ffn-symb x) '(return-last mv-list the-check))
              (induct-remove-guard-holders1 t (car (last (fargs x))) a))
             ((eq (ffn-symb x) 'cons-with-hint)
              (list (induct-remove-guard-holders1 t (cadr x) a)
                    (induct-remove-guard-holders1 t (caddr x) a)))
             ((member-eq (ffn-symb x) '(to-df from-df))
              (induct-remove-guard-holders1 t (cadr x) a))
             ((member-eq (ffn-symb x) '(df0 df1)) a)
             ;; Separate from the last case, so that the induction cases
             ;; match the hypotheses of the case lemmas:
             ((eq (ffn-symb x) 'do$) (induct-remove-guard-holders1 nil (fargs x) a))
             (t (induct-remove-guard-holders1 nil (fargs x) a)))
     (if (consp x)
         (list (induct-remove-guard-holders1 t (car x) a)
               (induct-remove-guard-holders1 nil (cdr x) a))
       a))))

(local
 (defthm remove-guard-holders1-correct-flag
   (if flg
       (implies (and (termp x w)
                     (remove-guard-holders1-arities-okp w))
                (equal (remove-guard-holders-eval (mv-nth 1 (remove-guard-holders1 nil x lamp)) a)
                       (remove-guard-holders-eval x a)))
     (implies (and (term-listp x w)
                   (remove-guard-holders1-arities-okp w))
              (equal (remove-guard-holders-eval-list (mv-nth 1 (remove-guard-holders1-lst x lamp)) a)
                     (remove-guard-holders-eval-list x a))))
   :rule-classes nil
   :hints (("Goal" :induct (induct-remove-guard-holders1 flg x a)
            :in-theory (disable last)
            :expand ((remove-guard-holders1-lst x lamp))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Remove-guard-holders1 preserves the meaning of terms (for any value of
;; CHANGEDP0, which only affects the first return value).
(defthm remove-guard-holders1-correct
  (implies (and (termp term w)
                (equal (arity 'return-last w) 3)
                (equal (arity 'mv-list w) 2)
                (equal (arity 'the-check w) 3)
                (equal (arity 'cons-with-hint w) 3)
                (equal (arity 'to-df w) 1)
                (equal (arity 'from-df w) 1))
           (equal (remove-guard-holders-eval (mv-nth 1 (remove-guard-holders1 changedp0 term lamp)) a)
                  (remove-guard-holders-eval term a)))
  :hints (("Goal" :use (:instance remove-guard-holders1-correct-flag (flg t) (x term))
           :in-theory (enable remove-guard-holders1-arities-okp))))

(defthm remove-guard-holders1-lst-correct
  (implies (and (term-listp lst w)
                (equal (arity 'return-last w) 3)
                (equal (arity 'mv-list w) 2)
                (equal (arity 'the-check w) 3)
                (equal (arity 'cons-with-hint w) 3)
                (equal (arity 'to-df w) 1)
                (equal (arity 'from-df w) 1))
           (equal (remove-guard-holders-eval-list (mv-nth 1 (remove-guard-holders1-lst lst lamp)) a)
                  (remove-guard-holders-eval-list lst a)))
  :hints (("Goal" :use (:instance remove-guard-holders1-correct-flag (flg nil) (x lst))
           :in-theory (enable remove-guard-holders1-arities-okp))))

(defthm remove-guard-holders-weak-correct
  (implies (and (termp term w)
                (equal (arity 'return-last w) 3)
                (equal (arity 'mv-list w) 2)
                (equal (arity 'the-check w) 3)
                (equal (arity 'cons-with-hint w) 3)
                (equal (arity 'to-df w) 1)
                (equal (arity 'from-df w) 1))
           (equal (remove-guard-holders-eval (remove-guard-holders-weak term lamp) a)
                  (remove-guard-holders-eval term a)))
  :hints (("Goal" :in-theory (enable remove-guard-holders-weak))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; A counterexample showing that pseudo-termp is not enough, and examples of
;; the CHANGEDP flag in the TO-DF case, are in remove-guard-holders1-tests.lisp.
