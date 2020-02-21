;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (June 18th 2018)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

(in-package "SMT")
(include-book "std/util/bstar" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "std/util/define" :dir :system)
;; for symbol-fix
(include-book "centaur/fty/basetypes" :dir :system)
;; for symbol-list-fix
(include-book "centaur/fty/baselists" :dir :system)

;; Include SMT books
(include-book "pseudo-lambda-lemmas")
(include-book "hint-interface")
(include-book "extractor")
(include-book "basics")
(include-book "hint-please")
(include-book "computed-hints")

;; To be compatible with Arithmetic books
(include-book "ordinals/lexicographic-ordering-without-arithmetic" :dir :system)

(include-book "clause-processors/just-expand" :dir :system)

(defsection function-expansion
  :parents (verified)
  :short "Function expansion"

  (defalist sym-nat-alist
    :key-type symbol
    :val-type natp
    :pred sym-nat-alistp
    :true-listp t)

  (local
   (defthm consp-of-sym-nat-alist-fix
     (implies (consp (sym-nat-alist-fix x)) (consp x))
     :hints (("Goal" :in-theory (enable sym-nat-alist-fix))))
   )

  (local
   (defthm len-of-sym-nat-alist-fix-<
     (> (1+ (len x)) (len (sym-nat-alist-fix x)))
     :hints (("Goal" :in-theory (enable sym-nat-alist-fix))))
   )

  (local
   (defthm natp-of-cdar-sym-nat-alist-fix
     (implies (consp (sym-nat-alist-fix x))
              (natp (cdar (sym-nat-alist-fix x))))
     :hints (("Goal" :in-theory (enable sym-nat-alist-fix))))
   )

  (define update-fn-lvls ((fn symbolp) (fn-lvls sym-nat-alistp))
    :returns (updated-fn-lvls sym-nat-alistp)
    :measure (len fn-lvls)
    :hints (("Goal" :in-theory (enable sym-nat-alist-fix)))
    (b* ((fn (symbol-fix fn))
         (fn-lvls (sym-nat-alist-fix fn-lvls))
         ((unless (consp fn-lvls)) nil)
         ((cons first rest) fn-lvls)
         ((cons this-fn this-lvl) first)
         ((unless (equal fn this-fn))
          (cons (cons this-fn this-lvl)
                (update-fn-lvls fn rest))))
      (if (zp this-lvl)
          (cons (cons this-fn 0) rest)
        (cons (cons this-fn (1- this-lvl)) rest)))
    ///
    (more-returns
     (updated-fn-lvls
      (implies (and (symbolp fn)
                    (sym-nat-alistp fn-lvls)
                    (consp fn-lvls)
                    (assoc-equal fn fn-lvls)
                    (not (equal (cdr (assoc-equal fn fn-lvls)) 0)))
               (< (cdr (assoc fn updated-fn-lvls))
                  (cdr (assoc fn fn-lvls))))
      :name updated-fn-lvls-decrease))
    )


  (defprod ex-args
    :parents (function-expansion)
    :short "Argument list for function expand"
    :long "<p>@('Ex-args') stores the list of arguments passed into the
    function @(see expand). We design this product type so that we don't have a
    long list of arguments to write down every time there's a recursive call.
    This document describes what each argument is about and more specifically,
    why they exist necessarily. This document comes out because every time when
    I read the @(see expand) function, I get confused and lost track about why I
    designed such a argument in the first place.</p>

    <p>@('Term-lst') is easy, it stores the list of terms to be expanded.
    Recursively generated new terms are stored in this argument and gets used
    in recursive calls. Using a list of terms allows us to use a single
    recursive function instead of @(see mutual-recursion), even though every
    time we call this function, we really just have one term to expand.</p>

    <p>@('Fn-lst') stores a list of function definitions for use of expansion.
    This list comes from the @(see smtlink-hint) stored in function stub @(see
    smt-hint). Such a list initially comes from user inputs to @(see Smtlink).
    So it can be, for example, some functions that the user wants to get
    expanded specially.</p>

    <p>@('Fn-lvls') stores a list of maximum number of times each function
    needs to be expanded. This list doesn't take into account of functions that
    are not specified by the user, which should oftenly be the case. In that
    case, those functions will be expanded just once and a pair will be stored
    into @('fn-lvls') indicating this function has already been expanded. This
    is done by storing a level of 0 for such a function.</p>

    <p>@('Wrld-fn-len') is the hardest to explain. But given some thought, I
    found it to be necessary to have this argument. @('wrld-fn-len') represents
    the length of current ACL2 @(see world), meaning the number of definitions
    in total (might be more than that, I'm not completely sure about what the
    @(see world) is composed of). This argument helps prove termination of
    function @(see expand). See @(see expand-measure) for a discussion about
    the measure function for proving termimation.</p>

    <p>@('Expand-lst') stores all functions that are expanded in @(see expand).
    This list gets used later for generating the @(':in-theory') hint for
    proving that the expanded term implies the original unexpanded term.</p>"

    ((term-lst pseudo-term-listp "List of terms to be expanded. The function
    finishes when all of them are expanded to given level."
               :default nil)
     (fn-lst func-alistp "List of function definitions to use for
      function expansion." :default nil)
     (fn-lvls sym-nat-alistp "Levels to expand each functions to." :default
              nil)
     (wrld-fn-len natp "Number of function definitions in curent world."
                  :default 0)
     (expand-lst pseudo-term-alistp "An alist of expanded function symbols
    associated with their function call" :default nil)))

  (defprod ex-outs
    :parents (function-expansion)
    :short "Outputs for function expand"
    ((expanded-term-lst pseudo-term-listp "List of expanded terms." :default nil)
     (expanded-fn-lst pseudo-term-alistp "List of expanded function calls,
    needed for expand hint for proving G' implies G theorem." :default nil)))

  (local
   (defthm natp-of-sum-lvls-lemma
     (implies (and (consp (sym-nat-alist-fix fn-lvls)) (natp x))
              (natp (+ (cdr (car (sym-nat-alist-fix fn-lvls))) x)))
     :hints (("Goal"
              :in-theory (enable sym-nat-alist-fix)
              :use ((:instance natp-of-cdar-sym-nat-alist-fix)))))
   )

  (define sum-lvls ((fn-lvls sym-nat-alistp))
    :returns (sum natp :hints (("Goal"
                                :use ((:instance natp-of-sum-lvls-lemma
                                                 (x (sum-lvls (cdr (sym-nat-alist-fix fn-lvls)))))))))
    :measure (len fn-lvls)
    :hints (("Goal" :in-theory (enable sym-nat-alist-fix)))
    (b* ((fn-lvls (sym-nat-alist-fix fn-lvls))
         ((unless (consp fn-lvls)) 0)
         ((cons first rest) fn-lvls)
         ((cons & lvl) first))
      (+ lvl (sum-lvls rest)))
    ///
    (defthm sum-lvls-decrease-after-update
      (implies (and (symbolp fn)
                    (sym-nat-alistp fn-lvls)
                    (consp fn-lvls)
                    (assoc-equal fn fn-lvls)
                    (not (equal (cdr (assoc-equal fn fn-lvls)) 0)))
               (< (sum-lvls (update-fn-lvls fn fn-lvls))
                  (sum-lvls fn-lvls)))
      :hints (("Goal" :in-theory (enable update-fn-lvls)))))

  (define expand-measure ((expand-args ex-args-p))
    :returns (m nat-listp)
    :parents (function-expansion)
    :short "@(see acl2::Measure) function for proving termination of function
    @(see expand)."

    :long "<p>The measure is using the lexicographical order (see @(see
    mutual-recursion)), using a list of three arguments, where the priority
    goes from the first argument to the second, and then to the third.</p>

    <p>The first argument is @('wrld-fn-len') which appears in @(see ex-args).
    It is necessary for decreasing the measure when we are expanding a function
    that is not in @('fn-lst') (see @(see ex-args)). The second argument is a
    summation of @('fn-lvls') which also appears in @(see ex-args). This list
    remembers how many levels are left for each function. Since functions not
    in @('fn-lst') are added to @('fn-lvls') with 0 level, this argument
    doesn't decrease in that case. This is why it's necessary to have the first
    argument @('wrld-fn-len'). The third argument is the @(see acl2-count) of
    current @('term-lst') (also see @(see ex-args)). This argument decreases
    every time the recursive function @('expand') goes into expand the @(see
    cdr) of @('term-lst').</p>"

    (b* ((expand-args (ex-args-fix expand-args))
         ((ex-args a) expand-args)
         (lvl-sum (sum-lvls a.fn-lvls)))
      (list a.wrld-fn-len lvl-sum (acl2-count a.term-lst))))

  (encapsulate ()
    (local (defthm lemma-1
             (implies (ex-args-p x)
                      (pseudo-term-listp (ex-args->term-lst x)))))

    (local (defthm lemma-2
             (implies (and (pseudo-term-listp y) (consp y))
                      (pseudo-termp (car y)))))

    (local (defthm lemma-3
             (implies (and (pseudo-termp z) (consp z) (not (equal (car z) 'quote)))
                      (pseudo-term-listp (cdr z)))))

    (defthm pseudo-term-list-of-cdar-of-ex-args->term-lst
      (implies (and (ex-args-p expand-args)
                    (consp (ex-args->term-lst expand-args))
                    (consp (car (ex-args->term-lst expand-args)))
                    (not (equal (caar (ex-args->term-lst expand-args)) 'quote)))
               (pseudo-term-listp (cdar (ex-args->term-lst expand-args)))))

    (local (defthm lemma-4
             (implies (and (pseudo-term-listp y) (consp y))
                      (pseudo-term-listp (cdr y)))))

    (defthm pseudo-term-listp-of-cdr-of-ex-args->term-lst
      (implies (and (ex-args-p expand-args)
                    (consp (ex-args->term-lst expand-args)))
               (pseudo-term-listp (cdr (ex-args->term-lst expand-args)))))

    (local (defthm lemma-5
             (implies (and (pseudo-term-listp y) (consp y) (not (consp (car y))))
                      (symbolp (car y)))))

    (defthm symbolp-of-car-of-ex-args->term-lst
      (implies (and (ex-args-p expand-args)
                    (consp (ex-args->term-lst expand-args))
                    (not (consp (car (ex-args->term-lst expand-args)))))
               (symbolp (car (ex-args->term-lst expand-args)))))

    (defthm pseudo-termp-of-car-of-ex-args->term-lst
      (implies (and (ex-args-p expand-args)
                    (consp (ex-args->term-lst expand-args)))
               (pseudo-termp (car (ex-args->term-lst expand-args))))
      :hints (("Goal" :in-theory (enable pseudo-termp))))

    (defthm len-equal-of-formals-of-pseudo-lambdap-and-actuals-of-pseudo-termp
      (implies (and (ex-args-p expand-args)
                    (pseudo-termp (car (ex-args->term-lst expand-args)))
                    (pseudo-lambdap (car (car (ex-args->term-lst expand-args)))))
               (equal (len (cadr (car (car (ex-args->term-lst expand-args)))))
                      (len (cdr (car (ex-args->term-lst expand-args))))))
      :hints (("Goal" :in-theory (e/d (pseudo-termp pseudo-lambdap)
                                      (ACL2::FOLD-CONSTS-IN-+
                                       ACL2::PSEUDO-TERMP-CAR)))))

    (local (defthm lemma-6
             (implies (and (pseudo-termp x) (not (symbolp x)) (not (pseudo-lambdap (car x))))
                      (symbolp (car x)))
             :hints (("Goal" :in-theory (enable pseudo-termp pseudo-lambdap)))))

    (defthm symbolp-of-caar-of-ex-args->term-lst
      (implies (and (ex-args-p expand-args)
                    (consp (ex-args->term-lst expand-args))
                    (not (symbolp (car (ex-args->term-lst expand-args))))
                    (not (pseudo-lambdap (car (car (ex-args->term-lst expand-args))))))
               (symbolp (car (car (ex-args->term-lst expand-args))))))

    (local (defthm lemma-7
             (implies (and (pseudo-termp x) (consp x) (equal (car x) 'quote))
                      (and (not (cddr x)) (consp (cdr x))))))

    (defthm not-cddr-of-car-of-pseudo-term-list-fix-of-expand-args->term-lst
      (implies (and (consp (ex-args->term-lst expand-args))
                    (consp (car (ex-args->term-lst expand-args)))
                    (not (symbolp (car (ex-args->term-lst expand-args))))
                    (equal (car (car (ex-args->term-lst expand-args))) 'quote))
               (not (cddr (car (ex-args->term-lst expand-args))))))

    (defthm consp-cdr-of-car-of-pseudo-term-list-fix-of-expand-args->term-lst
      (implies (and (consp (ex-args->term-lst expand-args))
                    (consp (car (ex-args->term-lst expand-args)))
                    (not (symbolp (car (ex-args->term-lst expand-args))))
                    (equal (car (car (ex-args->term-lst expand-args))) 'quote))
               (consp (cdr (car (ex-args->term-lst expand-args))))))

    (defthm pseudo-term-listp-of-pseudo-lambdap-of-cdar-ex-args->term-lst
      (implies (and (ex-args-p expand-args)
                    (consp (ex-args->term-lst expand-args))
                    (consp (car (ex-args->term-lst expand-args)))
                    (not (equal (caar (ex-args->term-lst expand-args)) 'quote)))
               (pseudo-term-listp (cdar (ex-args->term-lst expand-args)))))
    )

  (encapsulate ()
    (local (in-theory (enable pseudo-lambdap)))

    (defthm symbol-listp-of-formals-of-pseudo-lambdap
      (implies (pseudo-lambdap x) (symbol-listp (cadr x))))

    (defthm pseudo-termp-of-body-of-pseudo-lambdap
      (implies (pseudo-lambdap x) (pseudo-termp (caddr x))))

    (defthm consp-of-pseudo-lambdap
      (implies (pseudo-lambdap x) (consp x)))

    (defthm consp-of-cdr-of-pseudo-lambdap
      (implies (pseudo-lambdap x) (consp (cdr x))))

    (defthm consp-of-cddr-of-pseudo-lambdap
      (implies (pseudo-lambdap x) (consp (cddr x))))

    (defthm not-stringp-of-cadr-of-pseudo-lambdap
      (implies (pseudo-lambdap x) (not (stringp (cadr x)))))
    )

  (encapsulate ()
    (local (defthm lemma-1
             (implies (ex-args-p x) (sym-nat-alistp (ex-args->fn-lvls x)))))

    (local (defthm lemma-2
             (implies (and (sym-nat-alistp y) (assoc-equal foo y))
                      (natp (cdr (assoc-equal foo y))))))

    (local (defthm lemma-3
             (implies (and (sym-nat-alistp y) (assoc-equal foo y))
                      (consp (assoc-equal foo y)))))

    (local (defthm natp-of-cdr-of-assoc-equal-of-ex-args->fn-lvls-of-ex-args-p
             (implies (and (ex-args-p x) (assoc-equal foo (ex-args->fn-lvls x)))
                      (natp (cdr (assoc-equal foo (ex-args->fn-lvls x)))))))

    (defthm integerp-of-cdr-of-assoc-equal-of-ex-args->fn-lvls-of-ex-args-p
      (implies (and (ex-args-p x) (assoc-equal foo (ex-args->fn-lvls x)))
               (integerp (cdr (assoc-equal foo (ex-args->fn-lvls x)))))
      :hints(("Goal" :use ((:instance
                            natp-of-cdr-of-assoc-equal-of-ex-args->fn-lvls-of-ex-args-p (x x))))))

    (defthm non-neg-of-cdr-of-assoc-equal-of-ex-args->fn-lvls-of-ex-args-p
      (implies (and (ex-args-p x) (assoc-equal foo (ex-args->fn-lvls x)))
               (<= 0 (cdr (assoc-equal foo (ex-args->fn-lvls x)))))
      :hints(("Goal" :use ((:instance
                            natp-of-cdr-of-assoc-equal-of-ex-args->fn-lvls-of-ex-args-p (x x))))))

    (defthm consp-of-assoc-equal-of-ex-args->fn-lvls-of-ex-args-p
      (implies (and (ex-args-p x) (assoc-equal foo (ex-args->fn-lvls x)))
               (consp (assoc-equal foo (ex-args->fn-lvls x)))))

    (defthm last-<=
      (<= (acl2-count (last x))
          (acl2-count x)))

    (defthm last-pseudo-term-list-is-pseudo-term-list
      (implies (pseudo-term-listp x)
               (pseudo-term-listp (last x))))
    )

  (local (in-theory (enable expand-measure)))
  (encapsulate
    ()
    (set-well-founded-relation l<)
    (local (in-theory (e/d
                       ()
                       (ACL2::PSEUDO-LAMBDAP-OF-CAR-WHEN-PSEUDO-TERMP
                        ACL2::SUBSETP-CONS-2
                        CONSP-OF-SYM-NAT-ALIST-FIX
                        DEFAULT-CDR
                        SYM-NAT-ALISTP-OF-CDR-WHEN-SYM-NAT-ALISTP
                        NTH
                        TRUE-LISTP
                        ACL2::PSEUDO-LAMBDAP-OF-CAR-WHEN-PSEUDO-LAMBDA-LISTP
                        ACL2::PSEUDO-LAMBDA-LISTP-OF-CDR-WHEN-PSEUDO-LAMBDA-LISTP
                        ACL2::PSEUDO-TERMP-CDR-ASSOC-EQUAL
                        SYM-NAT-ALISTP-WHEN-NOT-CONSP
                        ACL2::SUBSETP-CAR-MEMBER
                        STRIP-CDRS
                        (:TYPE-PRESCRIPTION SYM-NAT-ALIST-FIX$INLINE)
                        ACL2::SUBSETP-WHEN-ATOM-RIGHT
                        RATIONAL-LISTP
                        INTEGER-LISTP
                        ATOM
                        ACL2::SYMBOL-LISTP-WHEN-NOT-CONSP
                        ACL2::PSEUDO-LAMBDAP-WHEN-MEMBER-EQUAL-OF-PSEUDO-LAMBDA-LISTP
                        ACL2::SYMBOL-LISTP-CDR-ASSOC-EQUAL
                        ACL2::SYMBOL-LIST-LISTP
                        ACL2::RATIONALP-OF-CAR-WHEN-RATIONAL-LISTP
                        ACL2::INTEGERP-OF-CAR-WHEN-INTEGER-LISTP
                        CONSP-WHEN-MEMBER-EQUAL-OF-SYM-NAT-ALISTP
                        ACL2::CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
                        ACL2::PSEUDO-LAMBDAP-OF-NTH-WHEN-PSEUDO-LAMBDA-LISTP
                        ACL2::PSEUDO-LAMBDA-LISTP-WHEN-NOT-CONSP
                        ACL2::SUBSETP-WHEN-ATOM-LEFT))))

    ;; Q FOR YAN:
    ;; 1. merge expand-args->fn-lst and expand-args->fn-lvls
    ;; 2. change update-fn-lvls function so that old items are not deleted and update the measure function
    ;; 3. clean the code in a more structured way - treat lambdas in another function
    ;; 4. clean up the above encapsulated theorems, maybe in another file
    (define expand ((expand-args ex-args-p) (fty-info fty-info-alist-p)
                    (abs symbol-listp) state)
      :parents (function-expansion)
      :returns (expanded-result ex-outs-p)
      :measure (expand-measure expand-args)
      :verify-guards nil
      :hints
      (("Goal"
        :in-theory (e/d ()
                        (last-<=
                         sum-lvls-decrease-after-update))
        :use ((:instance last-<=
                         (x (cdr (car (ex-args->term-lst expand-args)))))
              (:instance sum-lvls-decrease-after-update
                         (fn (car (car (ex-args->term-lst expand-args))))
                         (fn-lvls (ex-args->fn-lvls expand-args))))))
      (b* ((expand-args (ex-args-fix expand-args))
           (fty-info (fty-info-alist-fix fty-info))
           ;; This binds expand-args to a, so that we can call a.term-lst ...
           ((ex-args a) expand-args)
           ((unless (consp a.term-lst))
            (make-ex-outs :expanded-term-lst nil :expanded-fn-lst a.expand-lst))
           ((cons term rest) a.term-lst)
           ;; If first term is a symbolp, return the symbol
           ;; then recurse on the rest of the list
           ((if (symbolp term))
            (b* ((rest-res (expand (change-ex-args a :term-lst rest) fty-info
                                   abs state))
                 ((ex-outs o) rest-res))
              (make-ex-outs :expanded-term-lst (cons term o.expanded-term-lst)
                            :expanded-fn-lst o.expanded-fn-lst)))
           ((if (equal (car term) 'quote))
            (b* ((rest-res (expand (change-ex-args a :term-lst rest) fty-info
                                   abs state))
                 ((ex-outs o) rest-res))
              (make-ex-outs :expanded-term-lst (cons term o.expanded-term-lst)
                            :expanded-fn-lst o.expanded-fn-lst)))
           ;; The first term is now a function call:
           ;; Cons the function call and function actuals out of term
           ((cons fn-call fn-actuals) term)

           ;; If fn-call is a pseudo-lambdap
           ((if (pseudo-lambdap fn-call))
            (b* ((lambda-formals (lambda-formals fn-call))
                 (body-res
                  (expand (change-ex-args a
                                          :term-lst (list (lambda-body
                                                           fn-call)))
                          fty-info abs state))
                 ((ex-outs b) body-res)
                 (lambda-body (car b.expanded-term-lst))
                 (actuals-res
                  (expand (change-ex-args a
                                          :term-lst fn-actuals
                                          :expand-lst b.expanded-fn-lst)
                          fty-info abs state))
                 ((ex-outs ac) actuals-res)
                 (lambda-actuals ac.expanded-term-lst)
                 ((unless (mbt (equal (len lambda-formals) (len lambda-actuals))))
                  (make-ex-outs :expanded-term-lst a.term-lst :expanded-fn-lst a.expand-lst))
                 (lambda-fn `((lambda ,lambda-formals ,lambda-body) ,@lambda-actuals))
                 (rest-res
                  (expand (change-ex-args a
                                          :term-lst rest
                                          :expand-lst ac.expanded-fn-lst)
                          fty-info abs state))
                 ((ex-outs r) rest-res))
              (make-ex-outs :expanded-term-lst (cons lambda-fn r.expanded-term-lst)
                            :expanded-fn-lst r.expanded-fn-lst)))

           ;; If fn-call is neither a lambda expression nor a function call
           ((unless (mbt (symbolp fn-call)))
            (make-ex-outs :expanded-term-lst a.term-lst :expanded-fn-lst a.expand-lst))
           ;; Try finding function call from fn-lst
           (fn (hons-get fn-call a.fn-lst))
           ;; If fn-call doesn't exist in fn-lst, it can be a basic function,
           ;; in that case we don't do anything with it.
           ;; Otherwise it can be a function that's forgotten to be added to fn-lst.
           ;; We are going to expand all function like this for one level.
           ;; If the function is basic or has already been expanded once.
           ((unless fn)
            (b* (((unless (function-symbolp fn-call (w state)))
                  (prog2$
                   (er hard? 'SMT-goal-generator=>expand "Should be a function call: ~q0" fn-call)
                   (make-ex-outs :expanded-term-lst a.term-lst :expanded-fn-lst a.expand-lst)))
                 (basic-function (member-equal fn-call *SMT-basics*))
                 (flex? (fncall-of-flextype fn-call fty-info))
                 (abs? (member-equal fn-call abs))
                 (lvl-item (assoc-equal fn-call a.fn-lvls))
                 (extract-res (meta-extract-formula fn-call state))
                 ((if (equal fn-call 'return-last))
                  (b* ((actuals-res
                        (expand (change-ex-args a :term-lst (last fn-actuals))
                                fty-info abs state))
                       ((ex-outs ac) actuals-res)
                       (rest-res
                        (expand (change-ex-args a :term-lst rest
                                                :expand-lst ac.expanded-fn-lst)
                                fty-info abs state))
                       ((ex-outs r) rest-res))
                    (make-ex-outs
                     :expanded-term-lst (cons
                                         (car ac.expanded-term-lst)
                                         r.expanded-term-lst)
                     :expanded-fn-lst r.expanded-fn-lst)))
                 ((if (or basic-function flex? abs?
                          (<= a.wrld-fn-len 0) (and lvl-item (zp (cdr lvl-item)))
                          (equal extract-res ''t)))
                  (b* ((actuals-res
                        (expand (change-ex-args a :term-lst fn-actuals)
                                fty-info abs state))
                       ((ex-outs ac) actuals-res)
                       (rest-res
                        (expand (change-ex-args a :term-lst rest
                                                :expand-lst ac.expanded-fn-lst)
                                fty-info abs state))
                       ((ex-outs r) rest-res))
                    (make-ex-outs :expanded-term-lst (cons (cons fn-call ac.expanded-term-lst) r.expanded-term-lst)

                                  :expanded-fn-lst r.expanded-fn-lst)))
                 (formals (formals fn-call (w state)))
                 ((unless (symbol-listp formals))
                  (prog2$
                   (er hard? 'SMT-goal-generator=>expand "formals get a list that's not a symbol-listp for ~q0, the formals are ~q1" fn-call formals)
                   (make-ex-outs :expanded-term-lst a.term-lst :expanded-fn-lst a.expand-lst)))
                 ((unless (true-listp extract-res))
                  (prog2$
                   (er hard? 'SMT-goal-generator=>expand "meta-extract-formula returning a non-true-listp for ~q0The extracted result is ~q1" fn-call extract-res)
                   (make-ex-outs :expanded-term-lst a.term-lst :expanded-fn-lst a.expand-lst)))
                 (body (nth 2 extract-res))
                 ((unless (pseudo-termp body))
                  (prog2$
                   (er hard? 'SMT-goal-generator=>expand "meta-extract-formula returning a non-pseudo-term for ~q0The body is ~q1" fn-call body)
                   (make-ex-outs :expanded-term-lst a.term-lst :expanded-fn-lst a.expand-lst)))
                 ;; (- (cw "SMT-goal-generator=>Expanding ... ~q0" fn-call))
                 ;; Adding function symbol into expand-lst
                 (updated-expand-lst
                  (if (assoc-equal term a.expand-lst)
                      a.expand-lst (cons `(,term . ,term) a.expand-lst)))
                 (body-res
                  (expand (change-ex-args a
                                          :term-lst (list body)
                                          :fn-lvls (cons `(,fn-call . 0) a.fn-lvls)
                                          :wrld-fn-len (1- a.wrld-fn-len)
                                          :expand-lst updated-expand-lst)
                          fty-info abs state))
                 ((ex-outs b) body-res)
                 ;; Expand function
                 (expanded-lambda-body (car b.expanded-term-lst))
                 (expanded-lambda `(lambda ,formals ,expanded-lambda-body))
                 (actuals-res
                  (expand (change-ex-args a :term-lst fn-actuals
                                          :expand-lst b.expanded-fn-lst)
                          fty-info abs state))
                 ((ex-outs ac) actuals-res)
                 (expanded-term-list ac.expanded-term-lst)
                 ((unless (equal (len formals) (len expanded-term-list)))
                  (prog2$
                   (er hard? 'SMT-goal-generator=>expand "You called your function with the wrong number of actuals: ~q0" term)
                   (make-ex-outs :expanded-term-lst a.term-lst :expanded-fn-lst ac.expanded-fn-lst)) )
                 (rest-res
                  (expand (change-ex-args a :term-lst rest
                                          :expand-lst ac.expanded-fn-lst)
                          fty-info abs state))
                 ((ex-outs r) rest-res))
              (make-ex-outs :expanded-term-lst (cons `(,expanded-lambda ,@expanded-term-list) r.expanded-term-lst)
                            :expanded-fn-lst r.expanded-fn-lst)))

           ;; Now fn is a function in fn-lst
           ;; If fn-call is already expanded to level 0, don't expand.
           (lvl-item (assoc-equal fn-call a.fn-lvls))
           ((unless lvl-item)
            (prog2$
             (er hard? 'SMT-goal-generator=>expand "Function ~q0 exists in the definition list but not in the levels list?" fn-call)
             (make-ex-outs :expanded-term-lst a.term-lst :expanded-fn-lst a.expand-lst)) )
           ((if (zp (cdr lvl-item)))
            (b* ((actuals-res
                  (expand (change-ex-args a :term-lst fn-actuals)
                          fty-info abs state))
                 ((ex-outs ac) actuals-res)
                 (rest-res
                  (expand (change-ex-args a :term-lst rest
                                          :expand-lst ac.expanded-fn-lst)
                          fty-info abs state))
                 ((ex-outs r) rest-res))
              (make-ex-outs :expanded-term-lst (cons (cons fn-call ac.expanded-term-lst) r.expanded-term-lst)

                            :expanded-fn-lst r.expanded-fn-lst)))

           ;; If fn-call is not expanded to level 0, still can expand.
           (new-fn-lvls (update-fn-lvls fn-call a.fn-lvls))
           ((func f) (cdr fn))
           (extract-res (meta-extract-formula fn-call state))
           ((unless (true-listp extract-res))
            (prog2$
             (er hard? 'SMT-goal-generator=>expand "meta-extract-formula returning a non-true-listp for ~q0The extracted result is ~q1" fn-call extract-res)
             (make-ex-outs :expanded-term-lst a.term-lst :expanded-fn-lst a.expand-lst)))
           (body (nth 2 extract-res))
           ((unless (pseudo-termp body))
            (prog2$
             (er hard? 'SMT-goal-generator=>expand "meta-extract-formula returning a non-pseudo-term for ~q0The body is ~q1" fn-call body)
             (make-ex-outs :expanded-term-lst a.term-lst :expanded-fn-lst a.expand-lst)))
           ;; (- (cw "SMT-goal-generator=>Expanding ... ~q0" fn-call))
           (updated-expand-lst
            (if (assoc-equal term a.expand-lst)
                a.expand-lst (cons `(,term . ,term) a.expand-lst)))
           (formals f.flattened-formals)
           (body-res
            (expand (change-ex-args a :term-lst (list body)
                                    :fn-lvls new-fn-lvls
                                    :expand-lst updated-expand-lst)
                    fty-info abs state))
           ((ex-outs b) body-res)
           (expanded-lambda-body (car b.expanded-term-lst))
           (expanded-lambda `(lambda ,formals ,expanded-lambda-body))
           (actuals-res
            (expand (change-ex-args a :term-lst fn-actuals
                                    :expand-lst b.expanded-fn-lst)
                    fty-info abs state))
           ((ex-outs ac) actuals-res)
           (expanded-term-list ac.expanded-term-lst)
           ((unless (equal (len formals) (len expanded-term-list)))
            (prog2$
             (er hard? 'SMT-goal-generator=>expand "You called your function with the wrong number of actuals: ~q0" term)
             (make-ex-outs :expanded-term-lst a.term-lst :expanded-fn-lst ac.expanded-fn-lst)))
           (rest-res
            (expand (change-ex-args a :term-lst rest
                                    :expand-lst ac.expanded-fn-lst)
                    fty-info abs state))
           ((ex-outs r) rest-res))
        (make-ex-outs :expanded-term-lst (cons `(,expanded-lambda ,@expanded-term-list) r.expanded-term-lst)
                      :expanded-fn-lst r.expanded-fn-lst))
      ///
      (more-returns
       (expanded-result (implies (ex-args-p expand-args)
                                 (pseudo-term-alistp
                                  (ex-outs->expanded-fn-lst expanded-result)))
                        :name pseudo-term-alistp-of-expand)
       (expanded-result (implies (ex-args-p expand-args)
                                 (pseudo-term-listp
                                  (ex-outs->expanded-term-lst expanded-result)))
                        :name pseudo-term-listp-of-expand)
       (expanded-result (implies (ex-args-p expand-args)
                                 (pseudo-termp
                                  (car (ex-outs->expanded-term-lst expanded-result))))
                        :name pseudo-termp-of-car-of-expand)
       (expanded-result (implies (ex-args-p expand-args)
                                 (equal (len (ex-outs->expanded-term-lst expanded-result))
                                        (len (ex-args->term-lst expand-args))))
                        :name len-of-expand)
       )
      )
    )

  (verify-guards expand
    :hints (("Goal"
             :in-theory (e/d
                         ()
                         (NTH
                          FGETPROP
                          TRUE-LISTP
                          DEFAULT-CDR
                          ASSOC-EQUAL
                          ACL2::SUBSETP-CONS-2
                          ACL2::O-P-O-INFP-CAR
                          CONSP-OF-SYM-NAT-ALIST-FIX
                          ACL2::SYMBOL-LISTP-WHEN-NOT-CONSP
                          ACL2::PSEUDO-LAMBDA-LISTP-WHEN-NOT-CONSP
                          ACL2::PSEUDO-LAMBDAP-OF-CAR-WHEN-PSEUDO-TERMP
                          CONSP-WHEN-MEMBER-EQUAL-OF-SYM-NAT-ALISTP
                          SYM-NAT-ALISTP-OF-CDR-WHEN-SYM-NAT-ALISTP
                          ACL2::PSEUDO-LAMBDAP-OF-NTH-WHEN-PSEUDO-LAMBDA-LISTP
                          ACL2::PSEUDO-LAMBDA-LISTP-OF-CDR-WHEN-PSEUDO-LAMBDA-LISTP
                          ACL2::PSEUDO-LAMBDAP-OF-CAR-WHEN-PSEUDO-LAMBDA-LISTP
                          ACL2::CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
                          ACL2::PSEUDO-LAMBDAP-WHEN-MEMBER-EQUAL-OF-PSEUDO-LAMBDA-LISTP))
             :use ((:instance pseudo-term-listp-of-pseudo-lambdap-of-cdar-ex-args->term-lst)
                   (:instance symbolp-of-caar-of-ex-args->term-lst)))))

  )

(define initialize-fn-lvls ((fn-lst func-alistp))
  :returns (fn-lvls sym-nat-alistp)
  :measure (len fn-lst)
  :hints (("Goal" :in-theory (enable func-alist-fix)))
  (b* ((fn-lst (func-alist-fix fn-lst))
       ((unless (consp fn-lst)) nil)
       ((cons first rest) fn-lst)
       ((func f) (cdr first)))
    (cons (cons f.name f.expansion-depth) (initialize-fn-lvls rest))))

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
  (b* ((hints (smtlink-hint-fix hints))
       ((smtlink-hint h) hints)
       ((unless (alistp flextypes-table)) h)
       ((mv & ordered-acc)
        (generate-fty-type-list h.fty flextypes-table
                                h.fty-info nil nil))
       (fty-types (reverse ordered-acc)))
    (change-smtlink-hint h :fty-types fty-types)))

;; -----------------------------------------------------------------
;;       Define evaluators

(defevaluator ev-expand-cp ev-lst-expand-cp
  ((not x) (if x y z) (hint-please hint)))

(def-join-thms ev-expand-cp)

;; -----------------------------------------------------------------

;; Define the function expansion clause processor
;; Expanded-G
;; Expanded-G => G

(define expand-cp-helper ((cl pseudo-term-listp)
                          (smtlink-hint smtlink-hint-p)
                          state)
  :returns (new-hint smtlink-hint-p)
  :guard-debug t
  (b* ((cl (pseudo-term-list-fix cl))
       (smtlink-hint (smtlink-hint-fix smtlink-hint))
       ;; generate all fty related stuff
       (flextypes-table (table-alist 'fty::flextypes-table (w state)))
       ((unless (alistp flextypes-table)) smtlink-hint)
       (h1 (generate-fty-info-alist smtlink-hint flextypes-table))
       (h2 (generate-fty-types-top h1 flextypes-table))
       ((smtlink-hint h) h2)
       ;; Make an alist version of fn-lst
       (fn-lst (make-alist-fn-lst h.functions))
       (fn-lvls (initialize-fn-lvls fn-lst))
       (wrld-fn-len h.wrld-fn-len)
       (G (disjoin cl))
       ;; Do function expansion
       (expand-result
        (with-fast-alist fn-lst (expand (make-ex-args
                                         :term-lst (list G)
                                         :fn-lst fn-lst
                                         :fn-lvls fn-lvls
                                         :wrld-fn-len wrld-fn-len)
                                        h.fty-info h.abs state)))
       ((ex-outs e) expand-result)
       (expanded-G (car e.expanded-term-lst))
       ;; generate expand hint
       (fncall-lst (strip-cars e.expanded-fn-lst))
       ((unless (alistp fncall-lst))
        (prog2$
         (er hard? 'expand=>expand-cp "Function call list should be an alistp: ~
                   ~q0" fncall-lst)
         h))
       (expand-hint (remove-duplicates-equal (strip-cars fncall-lst)))
       (hint-with-fn-expand (treat-in-theory-hint expand-hint h.main-hint))
       (expanded-clause-w/-hint (make-hint-pair :thm expanded-G
                                                :hints hint-with-fn-expand)))
    (change-smtlink-hint h
                         :expanded-clause-w/-hint expanded-clause-w/-hint)))

(define expand-cp-fn ((cl pseudo-term-listp)
                      (smtlink-hint t))
  :returns (subgoal-lst pseudo-term-list-listp)
  (b* (((unless (pseudo-term-listp cl)) nil)
       ((unless (smtlink-hint-p smtlink-hint))
        (list cl))
       (G (disjoin cl))
       (hinted-expanded-G
        (smtlink-hint->expanded-clause-w/-hint smtlink-hint))
       (expanded-G (hint-pair->thm hinted-expanded-G))
       (main-hint (hint-pair->hints hinted-expanded-G))
       ;; generate first clause
       (next-cp (cdr (assoc-equal 'expand *SMT-architecture*)))
       ((if (null next-cp)) (list cl))
       (the-hint
        `(:clause-processor (,next-cp clause ',smtlink-hint)))
       (cl0 `((hint-please ',the-hint) ,expanded-G))
       ;; generate-second clause
       (cl1 `((hint-please ',main-hint) (not ,expanded-G) ,G))
       )
    `(,cl0 ,cl1)))

(defmacro expand-cp (clause hint)
  `(expand-cp-fn clause (expand-cp-helper ,clause ,hint state)))

;; proving correctness of the expansion clause processor
(local (in-theory (enable expand-cp-fn)))

(defthm correctness-of-expand-cp
  (implies (and (pseudo-term-listp cl)
                (alistp b)
                (ev-expand-cp
                 (conjoin-clauses (expand-cp-fn cl smtlink-hint))
                 b))
           (ev-expand-cp (disjoin cl) b))
  :rule-classes :clause-processor)
