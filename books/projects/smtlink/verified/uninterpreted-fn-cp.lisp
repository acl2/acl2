;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (July 6th 2018)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

(in-package "SMT")
(include-book "std/util/bstar" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "pseudo-lambda-lemmas")
(include-book "hint-please")
(include-book "hint-interface")
(include-book "computed-hints")

(defsection uninterpreted-fn-cp
  :parents (verified)
  :short "Verified clause-processor for proving return types of uninterpreted
  functions."

;; -----------------------------------------------------------------
;;       Define evaluators

(defevaluator ev-uninterpreted ev-lst-uninterpreted
  ((not x) (if x y z) (hint-please hint)))

(def-join-thms ev-uninterpreted)

;; -----------------------------------------------------------------

(define lambda->actuals-fix ((formals symbol-listp)
                             (actuals pseudo-term-listp))
  :returns (new-actuals pseudo-term-listp)
  (b* ((formals (symbol-list-fix formals))
       (actuals (pseudo-term-list-fix actuals))
       (len-formals (len formals))
       (len-actuals (len actuals))
       ((if (equal len-formals len-actuals)) actuals))
    nil))

(define lambda->formals-fix ((formals symbol-listp)
                             (actuals pseudo-term-listp))
  :returns (new-formals symbol-listp)
  (b* ((formals (symbol-list-fix formals))
       (actuals (pseudo-term-list-fix actuals))
       (len-formals (len formals))
       (len-actuals (len actuals))
       ((if (equal len-formals len-actuals)) formals))
    nil))

(local (in-theory (enable lambda->formals-fix lambda->actuals-fix)))
(defprod lambda-binding
  :parents (uninterpreted-fn-cp)
  ((formals symbol-listp
            :default nil
            :reqfix (lambda->formals-fix formals actuals))
   (actuals pseudo-term-listp
            :default nil
            :reqfix (lambda->actuals-fix formals actuals)))
  :require (equal (len formals) (len actuals)))

(deflist lambda-binding-list
  :parents (lambda-binding)
  :elt-type lambda-binding
  :pred lambda-binding-listp
  :true-listp t)

(defprod fhg-single-args
  :parents (uninterpreted-fn-cp)
  ((fn func-p :default nil)
   (actuals pseudo-term-listp :default nil)
   (fn-returns-hint-acc hint-pair-listp :default nil)
   (fn-more-returns-hint-acc hint-pair-listp :default nil)
   (lambda-acc lambda-binding-listp :default nil)))

(local
(defthm symbol-listp-of-append-of-symbol-listp
  (implies (and (symbol-listp x) (symbol-listp y))
           (symbol-listp (append x y))))
)

(local
 (defthm crock0
   (implies (and (fhg-single-args-p args)
                 (not (equal (func->name (fhg-single-args->fn args)) 'quote)))
            (pseudo-term-listp
             (list
              (cons (func->name (fhg-single-args->fn args))
                    (fhg-single-args->actuals args))))))
 )

(local
 (defthm crock1
   (implies (and (pseudo-term-listp x)
                 (pseudo-term-listp y))
            (pseudo-term-listp (append x y))))
 )

;; Precondition:
;; 1. formals are in the right sequence as the functions are first defined
;; 2. all free vars in the thm of hypo must either be the formals or returns
;; These precondition should be satisfied when generating
;;   Smtlink-hint.
(define generate-fn-hint-pair ((hypo hint-pair-p) (args fhg-single-args-p)
                               (flag symbolp))
  :returns (fn-hint-pair hint-pair-p)
  :guard-debug t
  (b* ((hypo (hint-pair-fix hypo))
       (args (fhg-single-args-fix args))
       (flag (symbol-fix flag))
       ((hint-pair h) hypo)
       ((fhg-single-args a) args)
       ((func f) a.fn)
       (formals f.flattened-formals)
       (returns f.flattened-returns)
       ((unless (equal (len returns) 1))
        (prog2$ (er hard? 'SMT-goal-generator=>generate-fn-hint-pair "User ~
                defined function with more than one returns is not supported ~
                currently. ~%The function ~q0 has returns ~q1." f.name returns)
                (make-hint-pair)))
       ((unless (equal (len formals) (len a.actuals)))
        (prog2$ (er hard? 'SMT-goal-generator=>generate-fn-hint-pair "Number ~
                of formals and actuals don't match. ~%Formals: ~q0, actuals: ~q1."
                    formals a.actuals)
                (make-hint-pair)))
       ((if (equal f.name 'quote))
        (prog2$ (er hard? 'SMT-goal-generator=>generate-fn-hint-pair
                    "Function name can't be 'quote.")
                (make-hint-pair)))
       ((unless (or (equal flag 'more-returns)
                    (and (consp h.thm)
                         (symbolp (car h.thm)))))
        (prog2$ (er hard? 'SMT-goal-generator=>generate-fn-hint-pair
                    "Returns should have consp h.thm.~%")
                (make-hint-pair)))
       (thm (if (equal flag 'more-returns)
                `((lambda (,@formals ,@returns) ,h.thm)
                  ,@a.actuals (,f.name ,@a.actuals))
              `(,(car h.thm) (,f.name ,@a.actuals)))))
    (change-hint-pair h
                      :thm thm)))

(define generate-fn-returns-hint ((returns decl-listp)
                                  (args fhg-single-args-p))
  :returns (fn-hint-lst hint-pair-listp)
  :measure (len returns)
  (b* ((returns (decl-list-fix returns))
       (args (fhg-single-args-fix args))
       ((fhg-single-args a) args)
       ((unless (consp returns)) a.fn-returns-hint-acc)
       ((cons first rest) returns)
       ((decl d) first)
       ((hint-pair h) d.type)
       (hypo (change-hint-pair h :thm `(,h.thm ,d.name)))
       (first-hint-pair (generate-fn-hint-pair hypo args 'returns)))
    (generate-fn-returns-hint
     rest
     (change-fhg-single-args
      a
      :fn-returns-hint-acc
      (cons first-hint-pair a.fn-returns-hint-acc)))))

(define generate-fn-more-returns-hint ((more-returns hint-pair-listp)
                                       (args fhg-single-args-p))
  :returns (fn-hint-lst hint-pair-listp)
  :measure (len more-returns)
  (b* ((more-returns (hint-pair-list-fix more-returns))
       (args (fhg-single-args-fix args))
       ((fhg-single-args a) args)
       ((unless (consp more-returns)) a.fn-more-returns-hint-acc)
       ((cons first rest) more-returns)
       (first-hint-pair (generate-fn-hint-pair first args 'more-returns)))
    (generate-fn-more-returns-hint
     rest
     (change-fhg-single-args
      a
      :fn-more-returns-hint-acc
      (cons first-hint-pair a.fn-more-returns-hint-acc)))))

(define generate-fn-hint ((args fhg-single-args-p))
  :returns (fn-hint-lst fhg-single-args-p)
  (b* ((args (fhg-single-args-fix args))
       ((fhg-single-args a) args)
       ((func f) a.fn))
    (change-fhg-single-args
     a
     :fn-returns-hint-acc (generate-fn-returns-hint f.returns a)
     :fn-more-returns-hint-acc (generate-fn-more-returns-hint f.more-returns a))))


;; function hypotheses generation arguments
(defprod fhg-args
  :parents (uninterpreted-fn-cp)
  ((term-lst pseudo-term-listp :default nil)
   (fn-lst func-alistp :default nil)
   (fn-returns-hint-acc hint-pair-listp :default nil)
   (fn-more-returns-hint-acc hint-pair-listp :default nil)
   (lambda-acc lambda-binding-listp :default nil)))

(encapsulate ()

  (local (defthm lemma-1
           (implies (fhg-args-p x)
                    (pseudo-term-listp (fhg-args->term-lst x)))))

  (local (defthm lemma-2
           (implies (and (pseudo-term-listp y) (consp y))
                    (pseudo-termp (car y)))))

  (local (defthm lemma-3
           (implies (and (pseudo-termp z) (consp z) (not (equal (car z) 'quote)))
                    (pseudo-term-listp (cdr z)))))

  (local (defthm not-symbolp-then-consp-of-pseudo-termp
           (implies (and (pseudo-termp x)
                         (not (symbolp x)))
                    (consp x))))

  (defthm not-symbolp-then-consp-of-car-of-fhg-args->term-lst
    (implies (and (fhg-args-p args)
                  (consp (fhg-args->term-lst args))
                  (not (symbolp (car (fhg-args->term-lst args)))))
             (consp (car (fhg-args->term-lst args)))))

  (local (defthm lemma-4
           (implies (and (pseudo-term-listp y) (consp y))
                    (pseudo-term-listp (cdr y)))))

  (defthm pseudo-term-listp-of-cdr-of-fhg-args->term-lst
    (implies (and (fhg-args-p args)
                  (consp (fhg-args->term-lst args)))
             (pseudo-term-listp (cdr (fhg-args->term-lst args)))))

  (defthm pseudo-term-listp-of-cdar-of-fhg-args->term-lst
    (implies (and (fhg-args-p args)
                  (consp (fhg-args->term-lst args))
                  (not (symbolp (car (fhg-args->term-lst args))))
                  (not (equal (car (car (fhg-args->term-lst args)))
                              'quote)))
             (pseudo-term-listp (cdr (car (fhg-args->term-lst args))))))

  (local (defthm lemma-5
           (implies (and (pseudo-termp z)
                         (not (symbolp z)) (not (pseudo-lambdap (car z))))
                    (symbolp (car z)))
           :hints (("Goal" :in-theory (enable pseudo-termp pseudo-lambdap)))))

  (defthm symbolp-of-caar-of-fhg-args->term-lst
    (implies (and (fhg-args-p args)
                  (consp (fhg-args->term-lst args))
                  (not (symbolp (car (fhg-args->term-lst args))))
                  (not (pseudo-lambdap (car (car (fhg-args->term-lst args))))))
             (symbolp (car (car (fhg-args->term-lst args))))))

  (local (defthm lemma-6
           (implies (and (pseudo-termp x) (pseudo-lambdap (car x)))
                    (equal (len (cadar x)) (len (cdr x))))
           :hints (("Goal" :in-theory (enable pseudo-lambdap pseudo-termp)))))

  (defthm len-equal-of-formals-of-pseudo-lambdap-and-actuals
    (implies (and (fhg-args-p args)
                  (consp (fhg-args->term-lst args))
                  (pseudo-lambdap (car (car (fhg-args->term-lst args)))))
             (equal (len (cadr (car (car (fhg-args->term-lst args)))))
                    (len (cdr (car (fhg-args->term-lst args)))))))

  (local (defthm lemma-7
           (implies (and (func-alistp x)
                         (assoc-equal key x))
                    (func-p (cdr (assoc-equal key x))))
           ))

  (defthm lemma-8
    (implies (and (fhg-args-p args)
                  (consp (fhg-args->term-lst args))
                  (assoc-equal (car (car (fhg-args->term-lst args)))
                               (fhg-args->fn-lst args)))
             (func-p (cdr (assoc-equal (car (car (fhg-args->term-lst args)))
                                       (fhg-args->fn-lst args)))))
    :hints (("Goal" :in-theory (disable lemma-7)
             :use ((:instance lemma-7
                              (key (car (car (fhg-args->term-lst args))))
                              (x (fhg-args->fn-lst args))))))
    )

  (local (defthm lemma-9
           (implies (and (func-alistp x)
                         (assoc-equal key x))
                    (consp (assoc-equal key x)))
           ))

  (defthm lemma-10
    (implies (and (fhg-args-p args)
                  (consp (fhg-args->term-lst args))
                  (assoc-equal (car (car (fhg-args->term-lst args)))
                               (fhg-args->fn-lst args)))
             (consp (assoc-equal (car (car (fhg-args->term-lst args)))
                                 (fhg-args->fn-lst args))))
    :hints (("Goal" :in-theory (disable lemma-9)
             :use ((:instance lemma-9
                              (key (car (car (fhg-args->term-lst args))))
                              (x (fhg-args->fn-lst args))))))
    )
  )

;;
;; The hypotheses each function is going to generate:
;;
;; If it is a non-recursive function:
;; No hypotheses needed because the function doesn't exist anymore.
;; If there's a case where one needs hypotheses for non-recursive functions,
;;   I will be interested to know.
;;
;; If it is a recursive function, but not declared as uninterpreted:
;;   An error will be produced when Smtlink gets to the translator.
;;   The expander doesn't know enough information.
;;
;; If it is a uninterpreted function:
;;   Generate hypotheses for return type theorems and more return
;;     theorems.
;;
(define generate-fn-hint-lst ((args fhg-args-p))
  :parents (uninterpreted-fn-cp)
  :short "@(call generate-fn-hint-lst) generate auxiliary hypotheses from ~
           function expansion"
  :returns (fn-hint-lst fhg-args-p)
  :measure (acl2-count (fhg-args->term-lst args))
  :verify-guards nil
  (b* ((args (fhg-args-fix args))
       ;; Syntactic sugar for easy field access, e.g. a.term-lst
       ((fhg-args a) args)
       ((unless (consp a.term-lst)) a)
       ((cons term rest) a.term-lst)
       ;; If first term is an symbolp, return the symbol
       ;; then recurse on the rest of the list
       ((if (symbolp term))
        (generate-fn-hint-lst (change-fhg-args a :term-lst rest)))
       ((if (equal (car term) 'quote))
        (generate-fn-hint-lst (change-fhg-args a :term-lst rest)))
       ;; The first term is now a function call:
       ;; Cons the function call and function actuals out of term
       ((cons fn-call fn-actuals) term)

       ;; If fn-call is a pseudo-lambdap, update lambda-binding-lst
       ((if (pseudo-lambdap fn-call))
        (b* ((lambda-formals (lambda-formals fn-call))
             (lambda-body (lambda-body fn-call))
             (lambda-actuals fn-actuals)
             (lambda-bd (make-lambda-binding :formals lambda-formals
                                             :actuals lambda-actuals))
             ((unless (mbt (lambda-binding-p lambda-bd))) a)
             (a-1
              (generate-fn-hint-lst
               (change-fhg-args a
                                :term-lst (list lambda-body)
                                :lambda-acc (cons lambda-bd a.lambda-acc))))
             (a-2
              (generate-fn-hint-lst
               (change-fhg-args a-1
                                :term-lst lambda-actuals))))
          (generate-fn-hint-lst (change-fhg-args a-2
                                                 :term-lst rest))))

       ;; If fn-call is neither a lambda expression nor a function call
       ((unless (mbt (symbolp fn-call))) a)
       ;; Try finding function call from fn-lst
       (fn (assoc-equal fn-call a.fn-lst))
       ;; If fn-call doesn't exist in fn-lst, it can be a basic function,
       ;; in that case we don't do anything with it.
       ;; Otherwise it can be a function that's forgotten to be added to fn-lst.
       ;; The translator will fail to translate it and report an error.
       ((unless fn)
        (b* ((a-1 (generate-fn-hint-lst
                   (change-fhg-args a :term-lst fn-actuals))))
          (generate-fn-hint-lst (change-fhg-args a-1 :term-lst rest))))

       ;; Now fn is a function in fn-lst,
       ;;   we need to generate returns and more-returns hypotheses for them
       (f (cdr fn))
       (as-1 (generate-fn-hint
              (make-fhg-single-args :fn f
                                    :actuals fn-actuals
                                    :fn-returns-hint-acc a.fn-returns-hint-acc
                                    :fn-more-returns-hint-acc
                                    a.fn-more-returns-hint-acc
                                    :lambda-acc
                                    a.lambda-acc)))
       ((fhg-single-args as-1) as-1)
       (a-1 (change-fhg-args
             a
             :fn-returns-hint-acc as-1.fn-returns-hint-acc
             :fn-more-returns-hint-acc as-1.fn-more-returns-hint-acc))
       (a-2
        (generate-fn-hint-lst (change-fhg-args a-1
                                               :term-lst fn-actuals)))
       )
    (generate-fn-hint-lst (change-fhg-args a-2
                                           :term-lst rest))))

(verify-guards generate-fn-hint-lst)

;; -----------------------------------------------------------------
;; Defines the clause-processor for extracting type declarations
;; (type-hyp T1) and (type-hyp T2) ... => G
;; (type-hyp T1) or G
;; (type-hyp T2) or G
;; ...

(defprod uninterpreted
  ((returns hint-pair-listp)
   (more-returns hint-pair-listp)))

(define uninterpreted-fn-helper ((cl pseudo-term-listp)
                                 (smtlink-hint smtlink-hint-p))
  :returns (uninterpreted uninterpreted-p)
  (b* ((cl (pseudo-term-list-fix cl))
       (smtlink-hint (smtlink-hint-fix smtlink-hint))
       ((smtlink-hint h) smtlink-hint)
       (fn-lst (make-alist-fn-lst h.functions))
       (G (disjoin cl))
       (args (generate-fn-hint-lst (make-fhg-args
                                    :term-lst (list G)
                                    :fn-lst fn-lst
                                    :fn-returns-hint-acc nil
                                    :fn-more-returns-hint-acc nil
                                    :lambda-acc nil)))
       ((fhg-args a) args)
       (fn-returns-hint-lst a.fn-returns-hint-acc)
       (fn-more-returns-hint-lst a.fn-more-returns-hint-acc))
    (make-uninterpreted :returns fn-returns-hint-lst
                        :more-returns fn-more-returns-hint-lst)))

(define uninterpreted-subgoals ((hint-pair-lst hint-pair-listp)
                                (G pseudo-termp)
                                (tag symbolp))
  :returns (mv (list-of-H-thm pseudo-term-list-listp)
               (list-of-not-Hs pseudo-term-listp))
  :measure (len hint-pair-lst)
  (b* ((hint-pair-lst (hint-pair-list-fix hint-pair-lst))
       (G (pseudo-term-fix G))
       ((unless (or (equal tag :return)
                    (equal tag :more-return)))
        (prog2$ (er hard? 'uninterpreted-fn-cp=>uninterpreted-subgoals
                    "Tag not supported: ~q0" tag)
                (mv nil nil)))
       ((unless (consp hint-pair-lst)) (mv nil nil))
       ((cons first-hinted-H rest-hinted-Hs) hint-pair-lst)
       (H (hint-pair->thm first-hinted-H))
       (H-hint (hint-pair->hints first-hinted-H))
       (merged-hint-please-in-theory
        (treat-in-theory-hint '(hint-please) H-hint))
       (merged-type-hyp-in-theory
        (treat-in-theory-hint '(type-hyp)
                              merged-hint-please-in-theory))
       (merged-expand (treat-expand-hint '((:free (x) (hide x)))
                                         merged-type-hyp-in-theory))
       (first-H-thm (if (equal tag :return)
                        `((hint-please ',merged-expand)
                          (type-hyp (hide (cons ,H 'nil)) ',tag)
                          ,G)
                      `((hint-please ',merged-hint-please-in-theory)
                        ,H ,G)))
       (first-not-H-clause (if (equal tag :return)
                               `(not (type-hyp (hide (cons ,H 'nil)) ',tag))
                             `(not ,H)))
       ((mv rest-H-thms rest-not-H-clauses)
        (uninterpreted-subgoals rest-hinted-Hs G tag)))
    (mv (cons first-H-thm rest-H-thms)
        (cons first-not-H-clause rest-not-H-clauses)))
  ///
  (defthm uninterpreted-subgoals-correctness
    (implies (and (pseudo-termp G)
                  (alistp b)
                  (hint-pair-listp hint-pair-lst)
                  (ev-uninterpreted
                   (disjoin
                    (mv-nth 1 (uninterpreted-subgoals hint-pair-lst G tag)))
                   b)
                  (ev-uninterpreted
                   (conjoin-clauses
                    (mv-nth 0 (uninterpreted-subgoals hint-pair-lst G tag)))
                   b))
             (ev-uninterpreted G b))
    :hints (("Goal"
             :induct (uninterpreted-subgoals hint-pair-lst G tag)))))

(local (defthm crock3 (implies (pseudo-term-list-listp x) (true-listp x))))
(local (defthm crock4 (implies (and (pseudo-term-list-listp x)
                                    (pseudo-term-list-listp y))
                               (pseudo-term-list-listp (append x y)))))
(local (defthm crock5 (implies (and (pseudo-term-listp x)
                                    (pseudo-term-listp y))
                               (pseudo-term-listp (append x y)))))

(define uninterpreted-fn-cp ((cl pseudo-term-listp)
                             (smtlink-hint t))
  :returns (subgoal-lst pseudo-term-list-listp)
  :guard-debug t
  (b* (((unless (pseudo-term-listp cl)) nil)
       ((unless (smtlink-hint-p smtlink-hint))
        (list cl))
       (G (disjoin cl))
       ((smtlink-hint h) smtlink-hint)
       (uninterpreted (uninterpreted-fn-helper cl h))
       (hinted-Ts-returns (uninterpreted->returns uninterpreted))
       (hinted-Ts-more-returns (uninterpreted->more-returns uninterpreted))
       ((mv list-of-returns-T-thm list-of-returns-not-Ts)
        (uninterpreted-subgoals hinted-Ts-returns G :return))
       ((mv list-of-more-returns-T-thm list-of-more-returns-not-Ts)
        (uninterpreted-subgoals hinted-Ts-more-returns G :more-return))
       (list-of-T-thm (append list-of-returns-T-thm
                              list-of-more-returns-T-thm))
       (list-of-not-Ts (append list-of-returns-not-Ts
                               list-of-more-returns-not-Ts))
       (next-cp (if h.custom-p
                    (cdr (assoc-equal 'uninterpreted-custom *SMT-architecture*))
                  (cdr (assoc-equal 'uninterpreted *SMT-architecture*))))
       ((if (null next-cp)) (list cl))
       (the-hint
        `(:clause-processor (,next-cp clause ',h state)))
       (cl0 `((hint-please ',the-hint) ,@list-of-not-Ts ,G))
       )
    `(,cl0 ,@list-of-T-thm)))

;; proving correctness of the uninterpreted-fn-cp clause processor
(local (in-theory (enable uninterpreted-fn-cp)))

(defthm correctness-of-uninterpreted-fn-cp
  (implies (and (pseudo-term-listp cl)
                (alistp b)
                (ev-uninterpreted
                 (conjoin-clauses (uninterpreted-fn-cp cl smtlink-hint))
                 b))
           (ev-uninterpreted (disjoin cl) b))
  :hints (("Goal"
           :in-theory (disable uninterpreted-subgoals-correctness)
           :use ((:instance uninterpreted-subgoals-correctness
                            (g (disjoin cl))
                            (hint-pair-lst
                             (uninterpreted->returns
                              (uninterpreted-fn-helper cl smtlink-hint)))
                            (tag :return)
                            (b b))
                 (:instance uninterpreted-subgoals-correctness
                            (g (disjoin cl))
                            (hint-pair-lst
                             (uninterpreted->more-returns
                              (uninterpreted-fn-helper cl smtlink-hint)))
                            (tag :more-return)
                            (b b)))))
  :rule-classes :clause-processor)
)
