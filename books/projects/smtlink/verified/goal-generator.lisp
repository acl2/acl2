;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (August 2nd 2016)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

(in-package "SMT")
(include-book "std/util/bstar" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "std/util/define" :dir :system)
;; for lambda expression
(include-book "kestrel/utilities/terms" :dir :system)
;; for symbol-fix
(include-book "centaur/fty/basetypes" :dir :system)
;; for symbol-list-fix
(include-book "centaur/fty/baselists" :dir :system)

;; Include SMT books
(include-book "expand")

;; To be compatible with Arithmetic books
(include-book "ordinals/lexicographic-ordering-without-arithmetic" :dir :system)

(defsection SMT-goal-generate
  :parents (verified)
  :short "SMT-goal-generator generates the three type of goals for the verified
  clause processor"

  (define initialize-fn-lvls ((fn-lst func-alistp))
    :returns (fn-lvls sym-nat-alistp)
    :measure (len fn-lst)
    :hints (("Goal" :in-theory (enable func-alist-fix)))
    (b* ((fn-lst (func-alist-fix fn-lst))
         ((unless (consp fn-lst)) nil)
         ((cons first rest) fn-lst)
         ((func f) (cdr first)))
      (cons (cons f.name f.expansion-depth) (initialize-fn-lvls rest))))

  ;; Generate auxiliary hypotheses from the user given hypotheses
  (define generate-hyp-hint-lst ((hyp-lst hint-pair-listp)
                                 (fn-lst func-alistp) (fn-lvls sym-nat-alistp)
                                 (wrld-fn-len natp)
                                 (fty-info fty-info-alist-p)
                                 state)
    :returns (hyp-hint-lst hint-pair-listp)
    (b* (((if (endp hyp-lst)) nil)
         ((cons (hint-pair hyp) rest) hyp-lst)
         (expand-result
          (expand (make-ex-args :term-lst (list hyp.thm)
                                :fn-lst fn-lst
                                :fn-lvls fn-lvls
                                :wrld-fn-len wrld-fn-len)
                  fty-info state))
         ((ex-outs e) expand-result)
         (G-prim (car e.expanded-term-lst)))
      (cons (make-hint-pair :thm G-prim
                            :hints hyp.hints)
            (generate-hyp-hint-lst rest fn-lst fn-lvls wrld-fn-len
                                   fty-info state))))

  (define lambda->actuals-fix ((formals symbol-listp) (actuals pseudo-term-listp))
    :returns (new-actuals pseudo-term-listp)
    (b* ((formals (symbol-list-fix formals))
         (actuals (pseudo-term-list-fix actuals))
         (len-formals (len formals))
         (len-actuals (len actuals))
         ((if (equal len-formals len-actuals)) actuals))
      nil))

  (define lambda->formals-fix ((formals symbol-listp) (actuals pseudo-term-listp))
    :returns (new-formals symbol-listp)
    (b* ((formals (symbol-list-fix formals))
         (actuals (pseudo-term-list-fix actuals))
         (len-formals (len formals))
         (len-actuals (len actuals))
         ((if (equal len-formals len-actuals)) formals))
      nil))

  (local (in-theory (enable lambda->formals-fix lambda->actuals-fix)))
  (defprod lambda-binding
    :parents (SMT-goal-generate)
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

  ;; (define generate-lambda-bindings ((lambda-bd-lst lambda-binding-listp) (term pseudo-termp))
  ;;   :returns (new-term pseudo-termp)
  ;;   :measure (len lambda-bd-lst)
  ;;   (b* ((lambda-bd-lst (lambda-binding-list-fix lambda-bd-lst))
  ;;        (term (pseudo-term-fix term))
  ;;        ((unless (consp lambda-bd-lst)) term)
  ;;        ((cons first-bd rest-bd) lambda-bd-lst)
  ;;        ((lambda-binding b) first-bd))
  ;;     (generate-lambda-bindings rest-bd
  ;;                               `((lambda ,b.formals ,term) ,@b.actuals))))

  (defprod fhg-single-args
    :parents (SMT-goal-generate)
    ((fn func-p :default nil)
     (actuals pseudo-term-listp :default nil)
     (fn-returns-hint-acc hint-pair-listp :default nil)
     (fn-more-returns-hint-acc hint-pair-listp :default nil)
     (lambda-acc lambda-binding-listp :default nil)))

  (defthm symbol-listp-of-append-of-symbol-listp
    (implies (and (symbol-listp x) (symbol-listp y))
             (symbol-listp (append x y))))

  ;; Precondition:
  ;; 1. formals are in the right sequence as the functions are first defined
  ;; 2. all free vars in the thm of hypo must either be the formals or returns
  ;; These precondition should be satisfied when generating
  ;;   Smtlink-hint.
  (define generate-fn-hint-pair ((hypo hint-pair-p) (args fhg-single-args-p))
    :returns (fn-hint-pair hint-pair-p)
    (b* ((hypo (hint-pair-fix hypo))
         (args (fhg-single-args-fix args))
         ((hint-pair h) hypo)
         ((fhg-single-args a) args)
         ((func f) a.fn)

         (formals f.flattened-formals)
         (returns f.flattened-returns)
         ((unless (equal (len returns) 1))
          (prog2$ (er hard? 'SMT-goal-generator=>generate-fn-hint-pair "User defined function with more than one returns is not supported currently. ~%The function ~q0 has returns ~q1." f.name returns)
                  (make-hint-pair)))
         ((unless (equal (len formals) (len a.actuals)))
          (prog2$ (er hard? 'SMT-goal-generator=>generate-fn-hint-pair "Number of formals and actuals don't match. ~%Formals: ~q0, actuals: ~q1." formals a.actuals)
                  (make-hint-pair)))
         ((if (equal f.name 'quote))
          (prog2$ (er hard? 'SMT-goal-generator=>generate-fn-hint-pair "Function name can't be 'quote.")
                  (make-hint-pair)))

         ;; (lambdaed-fn-call-instance (generate-lambda-bindings a.lambda-acc
         ;;                                                      `(,f.name
         ;;                                                        ,@a.actuals)))
         )
      (change-hint-pair h
                        :thm `((lambda (,@formals ,@returns) ,h.thm)
                               ,@a.actuals (,f.name ,@a.actuals)))))


  (define generate-fn-returns-hint ((returns decl-listp) (args fhg-single-args-p))
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
         (first-hint-pair (generate-fn-hint-pair hypo args)))
      (generate-fn-returns-hint rest
                                (change-fhg-single-args a :fn-returns-hint-acc (cons first-hint-pair a.fn-returns-hint-acc)))))

  (define generate-fn-more-returns-hint ((more-returns hint-pair-listp) (args fhg-single-args-p))
    :returns (fn-hint-lst hint-pair-listp)
    :measure (len more-returns)
    (b* ((more-returns (hint-pair-list-fix more-returns))
         (args (fhg-single-args-fix args))
         ((fhg-single-args a) args)
         ((unless (consp more-returns)) a.fn-more-returns-hint-acc)
         ((cons first rest) more-returns)
         (first-hint-pair (generate-fn-hint-pair first args)))
      (generate-fn-more-returns-hint rest
                                     (change-fhg-single-args a
                                                             :fn-more-returns-hint-acc
                                                             (cons first-hint-pair a.fn-more-returns-hint-acc)))))

  (define generate-fn-hint ((args fhg-single-args-p))
    :returns (fn-hint-lst fhg-single-args-p)
    (b* ((args (fhg-single-args-fix args))
         ((fhg-single-args a) args)
         ((func f) a.fn)
         ;; ((unless f.uninterpreted)
         ;;  (prog2$ (er hard? 'SMT-goal-generator=>generate-fn-hint "Function call ~q0 still exists in term but it's not declared as an uninterpreted function." f.name)
         ;;          a))
         )
      (change-fhg-single-args a
                              :fn-returns-hint-acc (generate-fn-returns-hint f.returns a)
                              :fn-more-returns-hint-acc (generate-fn-more-returns-hint f.more-returns a))))


  ;; function hypotheses generation arguments
  (defprod fhg-args
    :parents (SMT-goal-generate)
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

    (defthm len-equal-of-formals-of-pseudo-lambdap-and-actuals-of-pseudo-termp-of-car-of-fhg-args->term-lst
      (implies (and (fhg-args-p args)
                    (consp (fhg-args->term-lst args))
                    (pseudo-lambdap (car (car (fhg-args->term-lst args)))))
               (equal (len (cadr (car (car (fhg-args->term-lst args)))))
                      (len (cdr (car (fhg-args->term-lst args)))))))
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
    :parents (SMT-goal-generate)
    :short "@(call generate-fn-hint-lst) generate auxiliary hypotheses from function expansion"
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
               (lambda-bd (make-lambda-binding :formals lambda-formals :actuals lambda-actuals))
               ((unless (mbt (lambda-binding-p lambda-bd))) a)
               (a-1
                (generate-fn-hint-lst (change-fhg-args a
                                                       :term-lst (list lambda-body)
                                                       :lambda-acc (cons lambda-bd a.lambda-acc))))
               (a-2
                (generate-fn-hint-lst (change-fhg-args a-1
                                                       :term-lst lambda-actuals))))
            (generate-fn-hint-lst (change-fhg-args a-2
                                                   :term-lst rest))))

         ;; If fn-call is neither a lambda expression nor a function call
         ((unless (mbt (symbolp fn-call))) a)
         ;; Try finding function call from fn-lst
         (fn (hons-get fn-call a.fn-lst))
         ;; If fn-call doesn't exist in fn-lst, it can be a basic function,
         ;; in that case we don't do anything with it.
         ;; Otherwise it can be a function that's forgotten to be added to fn-lst.
         ;; The translator will fail to translate it and report an error.
         ((unless fn)
          (b* ((a-1 (generate-fn-hint-lst (change-fhg-args a :term-lst fn-actuals))))
            (generate-fn-hint-lst (change-fhg-args a-1 :term-lst rest))))

         ;; Now fn is a function in fn-lst,
         ;;   we need to generate returns and more-returns hypotheses for them
         (f (cdr fn))
         (as-1 (generate-fn-hint (make-fhg-single-args :fn f
                                                       :actuals fn-actuals
                                                       :fn-returns-hint-acc a.fn-returns-hint-acc
                                                       :fn-more-returns-hint-acc
                                                       a.fn-more-returns-hint-acc
                                                       :lambda-acc
                                                       a.lambda-acc)))
         ((fhg-single-args as-1) as-1)
         (a-1 (change-fhg-args a
                               :fn-returns-hint-acc as-1.fn-returns-hint-acc
                               :fn-more-returns-hint-acc as-1.fn-more-returns-hint-acc))
         (a-2
          (generate-fn-hint-lst (change-fhg-args a-1
                                                 :term-lst fn-actuals)))
         )
      (generate-fn-hint-lst (change-fhg-args a-2
                                             :term-lst rest))))

  (verify-guards generate-fn-hint-lst)


  ;; ---------------------------------------------------------------------
  ;; TODO
  ;; Should this function be in this file?
  (define is-type-decl ((type pseudo-termp))
    :returns (is? booleanp)
    (b* ((type (pseudo-term-fix type))
         ((unless (consp type)) nil))
      (and (equal (len type) 2)
           (symbolp (car type))
           (symbolp (cadr type)))))

  ;; --------------------------------------------------------------------

  (local (in-theory (enable is-type-decl)))
  (define structurize-type-decl-list ((type-decl-list pseudo-term-listp))
    :returns (structured-decl-list decl-listp)
    (b* ((type-decl-list (pseudo-term-list-fix type-decl-list))
         ((unless (consp type-decl-list)) nil)
         ((cons first rest) type-decl-list)
         ((unless (is-type-decl first))
          (er hard? 'SMT-goal-generator=>structurize-type-decl-list "Non type declaration found: ~q0" first))
         ((list type name) first))
      (cons (make-decl :name name :type (make-hint-pair :thm type))
            (structurize-type-decl-list rest))))

  (define add-expansion-hint ((expanded-fn-lst pseudo-term-alistp))
    :returns (hint-with-fn-expand listp)
    (b* (((unless (consp expanded-fn-lst)) nil)
         ((cons first rest) expanded-fn-lst)
         ((cons fn &) first)
         ((unless (true-listp fn))
          (er hard? 'SMT-goal-generator=>add-expansion-hint "function call should be a true-listp: ~q0" fn)))
      (cons (car fn) (add-expansion-hint rest))))

  (define generate-fty-info-alist ((hints smtlink-hint-p)
                                   (flextypes-table alistp))
    :returns (updated-hints smtlink-hint-p)
    (b* ((hints (smtlink-hint-fix hints))
         ((smtlink-hint h) hints)
         ((unless (alistp flextypes-table)) h)
         (fty-info (generate-fty-info-alist-rec h.fty nil flextypes-table)))
      (change-smtlink-hint h :fty-info fty-info)))

  (local
   (defthm crock-for-generate-fty-types-top
     (implies (fty-types-p x)
              (fty-types-p (reverse x)))))

  (define generate-fty-types-top ((hints smtlink-hint-p)
                                  (flextypes-table alistp))
    :returns (updated-hints smtlink-hint-p)
    :guard-debug t
    (b* ((hints (smtlink-hint-fix hints))
         ((smtlink-hint h) hints)
         ((unless (alistp flextypes-table)) h)
         ((mv & ordered-acc)
          (generate-fty-type-list h.fty flextypes-table
                                  h.fty-info nil nil))
         (fty-types (reverse ordered-acc)))
      (change-smtlink-hint h :fty-types fty-types)))

  (encapsulate ()
    (local (in-theory (enable pseudo-term-listp-of-expand
                              hint-pair-listp-of-fhg-args->fn-more-returns-hint-acc
                              hint-pair-listp-of-fhg-args->fn-returns-hint-acc
                              hint-pair-listp-of-generate-hyp-hint-lst)))

    (local (defthm pseudo-termp-of-disjoin-of-pseudo-term-listp
             (implies (pseudo-term-listp cl)
                      (pseudo-termp (disjoin cl)))))

    (local (defthm alistp-of-pseudo-term-alistp
             (implies (pseudo-term-alistp x)
                      (alistp x))))

    ;; The top level function for generating SMT goals: G-prim and A's
    (define SMT-goal-generator ((cl pseudo-term-listp) (hints smtlink-hint-p) state)
      :parents (SMT-goal-generate)
      :returns (new-hints smtlink-hint-p)
      :short "@(call SMT-goal-generator) is the top level function for generating SMT goals: G-prim and A's"
      :verify-guards nil
      (b* ((cl (pseudo-term-list-fix cl))
           (hints (smtlink-hint-fix hints))
           ;; generate all fty related stuff
           (flextypes-table (table-alist 'fty::flextypes-table (w state)))
           ((unless (alistp flextypes-table)) hints)
           (hints (generate-fty-info-alist hints flextypes-table))
           (hints (generate-fty-types-top hints flextypes-table))

           ((smtlink-hint h) hints)
           ;; Make an alist version of fn-lst
           (fn-lst (make-alist-fn-lst h.functions))
           (fn-lvls (initialize-fn-lvls fn-lst))

           ;; Generate user given hypotheses and their hints from hyp-lst
           (wrld-fn-len h.wrld-fn-len)
           (hyp-hint-lst (with-fast-alist fn-lst (generate-hyp-hint-lst
                                                  h.hypotheses fn-lst fn-lvls
                                                  wrld-fn-len h.fty-info state)))

           ;; Expand main clause using fn-lst
           ;; Generate function hypotheses and their hints from fn-lst
           (expand-result
            (with-fast-alist fn-lst (expand (make-ex-args
                                             :term-lst (list (disjoin cl))
                                             :fn-lst fn-lst
                                             :fn-lvls fn-lvls
                                             :wrld-fn-len wrld-fn-len)
                                            h.fty-info state)))
           ((ex-outs e) expand-result)
           (G-prim (car e.expanded-term-lst))

           ;; Generate auxiliary hypotheses from function expansion
           (args (with-fast-alist fn-lst (generate-fn-hint-lst (make-fhg-args
                                                                :term-lst (list G-prim)
                                                                :fn-lst fn-lst
                                                                :fn-returns-hint-acc
                                                                nil
                                                                :fn-more-returns-hint-acc nil
                                                                :lambda-acc
                                                                nil))))
           ((fhg-args a) args)
           (fn-returns-hint-lst a.fn-returns-hint-acc)
           (fn-more-returns-hint-lst a.fn-more-returns-hint-acc)

           ;; Generate auxiliary hypotheses for type extraction
           ((mv type-decl-list G-prim-without-type) (SMT-extract G-prim h.fty-info))
           (structured-decl-list (structurize-type-decl-list type-decl-list))

           ;; Combine all auxiliary hypotheses
           (total-aux-hint-lst `(,@hyp-hint-lst ,@fn-more-returns-hint-lst))

           ;; Combine expanded main clause and its hint
           (fncall-lst (strip-cars e.expanded-fn-lst))
           ((unless (alistp fncall-lst))
            (prog2$
             (er hard? 'SMT-goal-generator=>SMT-goal-generator "Function call list should be an alistp: ~q0" fncall-lst)
             hints))
           (expand-hint (remove-duplicates-equal (strip-cars fncall-lst)))
           (hint-with-fn-expand (treat-in-theory-hint expand-hint h.main-hint))
           (expanded-clause-w/-hint (make-hint-pair :thm G-prim-without-type
                                                    :hints hint-with-fn-expand))

           ;; Update smtlink-hint
           (new-hints
            (change-smtlink-hint hints
                                 :fast-functions fn-lst
                                 :aux-hint-list total-aux-hint-lst
                                 ;; These aux theorems needs to be proved, but
                                 ;; donot belong to hypothesis.
                                 :aux-thm-list fn-returns-hint-lst
                                 ;; These type-decl theorems needs to be
                                 ;; proved, too, but also, donot belong to hypothesis
                                 :type-decl-list structured-decl-list
                                 :expanded-clause-w/-hint expanded-clause-w/-hint
                                 )))
        new-hints))
    (verify-guards SMT-goal-generator)
    )

  (in-theory (disable consp-when-member-equal-of-sym-nat-alistp
                      pseudo-term-list-of-cdar-of-ex-args->term-lst
                      pseudo-term-listp-of-cdr-of-ex-args->term-lst
                      symbolp-of-car-of-ex-args->term-lst
                      pseudo-termp-of-car-of-ex-args->term-lst
                      len-equal-of-formals-of-pseudo-lambdap-and-actuals-of-pseudo-termp
                      symbolp-of-caar-of-ex-args->term-lst
                      symbol-listp-of-formals-of-pseudo-lambdap
                      not-cddr-of-car-of-pseudo-term-list-fix-of-expand-args->term-lst
                      consp-cdr-of-car-of-pseudo-term-list-fix-of-expand-args->term-lst
                      pseudo-term-listp-of-pseudo-lambdap-of-cdar-ex-args->term-lst
                      pseudo-termp-of-body-of-pseudo-lambdap
                      consp-of-cdr-of-pseudo-lambdap
                      consp-of-pseudo-lambdap
                      consp-of-cddr-of-pseudo-lambdap
                      not-stringp-of-cadr-of-pseudo-lambdap
                      integerp-of-cdr-of-assoc-equal-of-ex-args->fn-lvls-of-ex-args-p
                      non-neg-of-cdr-of-assoc-equal-of-ex-args->fn-lvls-of-ex-args-p
                      consp-of-assoc-equal-of-ex-args->fn-lvls-of-ex-args-p
                      not-symbolp-then-consp-of-car-of-fhg-args->term-lst
                      pseudo-term-listp-of-cdr-of-fhg-args->term-lst
                      pseudo-term-listp-of-cdar-of-fhg-args->term-lst
                      symbolp-of-caar-of-fhg-args->term-lst
                      len-equal-of-formals-of-pseudo-lambdap-and-actuals-of-pseudo-termp-of-car-of-fhg-args->term-lst))
  )
