; A nicer interface to defevaluator
;
; Copyright (C) 2014-2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; See tests in defevaluator-plus-tests.lisp

(include-book "kestrel/utilities/pack" :dir :system) ; reduce?
(include-book "kestrel/utilities/make-function-calls-on-formals" :dir :system)

;; A nicer interface to defevaluator.  Improvements include:
;; 1. looks up the arities of the functions in the world.
;; 2. auto-generates the name of the -list function that will be mutually recursive with the term evaluator.
;; 3. always uses the :namedp t option to defevaluator, for nicer constraint names
;; 4. automatically generates various theorems
;; 5. generates improved versions of some constraints (currently, just one)

(defun defevaluator+-fn (eval-name fns state)
  (declare (xargs :guard (and (symbolp eval-name)
                              (symbol-listp fns))
                  :stobjs state))
  (let* ((eval-list-name (add-suffix-to-fn eval-name "-LIST"))
         (all-true-name (pack$ 'all-eval-to-true-with- eval-name))
         (all-false-name (pack$ 'all-eval-to-false-with- eval-name)))
    `(progn
       ;; The main defevaluator call generated:
       (defevaluator ,eval-name ,eval-list-name
         ,(make-function-calls-on-formals fns (w state))
         :namedp t)

       ;; Improved constraint(s):

       (defthm ,(pack$ eval-name '-of-lambda-better)
         (implies (consp (car x)) ;; no need to assume (consp x) since it's implied by this
                  (equal (,eval-name x a)
                         (,eval-name (caddr (car x))
                                (pairlis$ (cadr (car x))
                                          (,eval-list-name (cdr x) a))))))

       ;; Ours is better:
       (in-theory (disable ,(pack$ eval-name '-of-lambda)))

       ;; Extra theorems:

       (defthm ,(add-suffix-to-fn eval-list-name "-OF-APPEND")
         (equal (,eval-list-name (append terms1 terms2) a)
                (append (,eval-list-name terms1 a)
                        (,eval-list-name terms2 a)))
         :hints (("Goal" :in-theory (enable append))))

       (defthm ,(pack$ 'len-of- eval-list-name)
         (equal (len (,eval-list-name terms a))
                (len terms))
         :hints (("Goal" :in-theory (enable append (:I len)))))

       (defthm ,(add-suffix-to-fn eval-list-name "-OF-TRUE-LIST_FIX")
         (equal (,eval-list-name (true-list-fix terms) a)
                (,eval-list-name terms a))
         :hints (("Goal" :in-theory (enable append (:I len)))))

       ;; Helps prove the :functional-instance used to switch a theorem to a richer evaluator.
       ;; TODO: Consider disabling by default and instead providing a tool to lift a rule to a richer evaluator.
       (defthm ,(pack$ eval-name '-of-fncall-args-back)
         (implies (and (consp x)
                       (not (equal (car x) 'quote)))
                  (equal (,eval-name (cons (car x) (kwote-lst (,eval-list-name (cdr x) a))) nil)
                         (,eval-name x a)))
         :hints (("Goal" :use (:instance ,(pack$ eval-name '-of-fncall-args))
                  :in-theory nil)))

       (theory-invariant (incompatible (:rewrite ,(pack$ eval-name '-of-fncall-args))
                                       (:rewrite ,(pack$ eval-name '-of-fncall-args-back))))

       ;; These help with clause-processors.  We only generate them if the
       ;; evaluator knows about IF:
       ,@(and (member-eq 'if fns)
              `((defthm ,(add-suffix-to-fn eval-list-name "-OF-DISJOIN2-IFF")
                  (iff (,eval-name (disjoin2 term1 term2) a)
                       (or (,eval-name term1 a)
                           (,eval-name term2 a)))
                  :hints (("Goal" :in-theory (enable disjoin2))))

                (defthm ,(add-suffix-to-fn eval-list-name "-OF-DISJOIN-OF-CONS-IFF")
                  (iff (,eval-name (disjoin (cons term terms)) a)
                       (or (,eval-name term a)
                           (,eval-name (disjoin terms) a)))
                  :hints (("Goal" :in-theory (enable disjoin))))


                ;;
                ;; "all eval to true"
                ;;

                (defund ,all-true-name (terms a)
                  (declare (xargs :guard (and (pseudo-term-listp terms)
                                              (alistp a))))
                  (if (endp terms)
                      t
                    (and (,eval-name (first terms) a)
                         (,all-true-name (rest terms) a))))

                (defthm ,(pack$ all-true-name '-when-not-consp)
                  (implies (not (consp terms))
                           (,all-true-name terms a))
                  :hints (("Goal" :in-theory (enable ,all-true-name))))

                (defthm ,(pack$ all-true-name '-of-cons)
                  (equal (,all-true-name (cons term terms) a)
                         (and (,eval-name term a)
                              (,all-true-name terms a)))
                  :hints (("Goal" :in-theory (enable ,all-true-name))))

                (defthm ,(pack$ all-true-name '-of-append)
                  (equal (,all-true-name (append terms1 terms2) a)
                         (and (,all-true-name terms1 a)
                              (,all-true-name terms2 a)))
                  :hints (("Goal" :in-theory (enable ,all-true-name))))

                (defthm ,(pack$ eval-name '-of-conjoin)
                  (iff (,eval-name (conjoin terms) a)
                       (,all-true-name terms a))
                  :hints (("Goal" :in-theory (enable ,all-true-name))))

                (defthm ,(pack$ eval-name '-when- all-true-name '-and-member-equal)
                  (implies (and (,all-true-name terms a)
                                (member-equal term terms))
                           (,eval-name term a))
                  :hints (("Goal" :in-theory (enable ,all-true-name))))

                ;;
                ;; "all eval to false"
                ;;

                (defund ,all-false-name (terms a)
                  (declare (xargs :guard (and (pseudo-term-listp terms)
                                              (alistp a))))
                  (if (endp terms)
                      t
                    (and (not (,eval-name (first terms) a))
                         (,all-false-name (rest terms) a))))

                (defthm ,(pack$ all-false-name '-when-not-consp)
                  (implies (not (consp terms))
                           (,all-false-name terms a))
                  :hints (("Goal" :in-theory (enable ,all-false-name))))

                (defthm ,(pack$ all-false-name '-of-cons)
                  (equal (,all-false-name (cons term terms) a)
                         (and (not (,eval-name term a))
                              (,all-false-name terms a)))
                  :hints (("Goal" :in-theory (enable ,all-false-name))))

                (defthm ,(pack$ all-false-name '-of-append)
                  (equal (,all-false-name (append terms1 terms2) a)
                         (and (,all-false-name terms1 a)
                              (,all-false-name terms2 a)))
                  :hints (("Goal" :in-theory (enable ,all-false-name))))

                (defthm ,(pack$ eval-name '-of-disjoin)
                  (iff (,eval-name (disjoin terms) a)
                       (not (,all-false-name terms a)))
                  :hints (("Goal" :in-theory (enable ,ALL-FALSE-NAME))))

                (defthm ,(pack$ 'not- eval-name '-when- all-false-name '-and-member-equal)
                  (implies (and (,all-false-name terms a)
                                (member-equal term terms))
                           (not (,eval-name term a)))
                  :hints (("Goal" :in-theory (enable ,all-false-name))))

                (defthm ,(pack$ all-false-name '-when-equal-of-disjoin-and-quote-nil)
                  (implies (equal (disjoin terms) *nil*)
                           (,all-false-name terms a))
                  :hints (("Goal" :in-theory (enable ,all-false-name
                                                     disjoin))))

                (defthm ,(pack$ 'not- all-false-name '-when-equal-of-disjoin-and-quote-t)
                  (implies (equal (disjoin terms) *t*)
                           (not (,all-false-name terms a)))
                  :hints (("Goal" :in-theory (enable ,all-false-name
                                                     disjoin)))))))))

;; Example call (defevaluator+ math-and-if-ev binary-+ binary-* if).
;; Takes the name of the evaluator to create, followed by the names of all the
;; functions it should "know" about.
(defmacro defevaluator+ (eval-name &rest fns)
  `(make-event (defevaluator+-fn ',eval-name ',fns state)))
