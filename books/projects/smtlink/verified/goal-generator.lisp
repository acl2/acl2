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
(include-book "hint-interface")
(include-book "extractor")
(include-book "basics")

;; To be compatible with Arithmetic books
(include-book "ordinals/lexicographic-ordering-without-arithmetic" :dir :system)

(defsection SMT-goal-generate
  :parents (verified)
  :short "SMT-goal-generator generates the three type of goals for the verified clause processor"

  (defalist sym-nat-alist
    :key-type symbol
    :val-type natp
    :pred sym-nat-alistp
    :true-listp t)

  (defthm consp-of-sym-nat-alist-fix
    (implies (consp (sym-nat-alist-fix x)) (consp x))
    :hints (("Goal" :in-theory (enable sym-nat-alist-fix))))

  (defthm len-of-sym-nat-alist-fix-<
    (> (1+ (len x)) (len (sym-nat-alist-fix x)))
    :hints (("Goal" :in-theory (enable sym-nat-alist-fix))))

  (defthm natp-of-cdar-sym-nat-alist-fix
    (implies (consp (sym-nat-alist-fix x))
             (natp (cdar (sym-nat-alist-fix x))))
    :hints (("Goal" :in-theory (enable sym-nat-alist-fix))))

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
    :parents (expand)
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
    :parents (expand)
    :short "Outputs for function expand"
    ((expanded-term-lst pseudo-term-listp "List of expanded terms." :default nil)
     (expanded-fn-lst pseudo-term-alistp "List of expanded function calls,
    needed for expand hint for proving G' implies G theorem." :default nil)))

  (defthm natp-of-sum-lvls-lemma
    (implies (and (consp (sym-nat-alist-fix fn-lvls)) (natp x))
             (natp (+ (cdr (car (sym-nat-alist-fix fn-lvls))) x)))
    :hints (("Goal"
             :in-theory (enable sym-nat-alist-fix)
             :use ((:instance natp-of-cdar-sym-nat-alist-fix)))))

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
    :parents (expand)
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
      :hints (("Goal" :in-theory (enable pseudo-termp pseudo-lambdap))))

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
      :hints(("Goal" :use ((:instance natp-of-cdr-of-assoc-equal-of-ex-args->fn-lvls-of-ex-args-p (x x))))))

    (defthm non-neg-of-cdr-of-assoc-equal-of-ex-args->fn-lvls-of-ex-args-p
      (implies (and (ex-args-p x) (assoc-equal foo (ex-args->fn-lvls x)))
               (<= 0 (cdr (assoc-equal foo (ex-args->fn-lvls x)))))
      :hints(("Goal" :use ((:instance natp-of-cdr-of-assoc-equal-of-ex-args->fn-lvls-of-ex-args-p (x x))))))

    (defthm consp-of-assoc-equal-of-ex-args->fn-lvls-of-ex-args-p
      (implies (and (ex-args-p x) (assoc-equal foo (ex-args->fn-lvls x)))
               (consp (assoc-equal foo (ex-args->fn-lvls x)))))
    )

  (local (in-theory (enable expand-measure)))
  (encapsulate
    ()
    (set-well-founded-relation l<)

    ;; Q FOR YAN:
    ;; 1. merge expand-args->fn-lst and expand-args->fn-lvls
    ;; 2. change update-fn-lvls function so that old items are not deleted and update the measure function
    ;; 3. clean the code in a more structured way - treat lambdas in another function
    ;; 4. clean up the above encapsulated theorems, maybe in another file
    (define expand ((expand-args ex-args-p) (fty-info fty-info-alist-p) state)
      :parents (SMT-goal-generate)
      :returns (expanded-result ex-outs-p)
      :measure (expand-measure expand-args)
      :verify-guards nil
      :hints
      (("Goal"
        :use ((:instance sum-lvls-decrease-after-update
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
                                   state))
                 ((ex-outs o) rest-res))
              (make-ex-outs :expanded-term-lst (cons term o.expanded-term-lst)
                            :expanded-fn-lst o.expanded-fn-lst)))
           ((if (equal (car term) 'quote))
            (b* ((rest-res (expand (change-ex-args a :term-lst rest) fty-info
                                   state))
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
                          fty-info state))
                 ((ex-outs b) body-res)
                 (lambda-body (car b.expanded-term-lst))
                 (actuals-res
                  (expand (change-ex-args a
                                          :term-lst fn-actuals
                                          :expand-lst b.expanded-fn-lst)
                          fty-info state))
                 ((ex-outs ac) actuals-res)
                 (lambda-actuals ac.expanded-term-lst)
                 ((unless (mbt (equal (len lambda-formals) (len lambda-actuals))))
                  (make-ex-outs :expanded-term-lst a.term-lst :expanded-fn-lst a.expand-lst))
                 (lambda-fn `((lambda ,lambda-formals ,lambda-body) ,@lambda-actuals))
                 (rest-res
                  (expand (change-ex-args a
                                          :term-lst rest
                                          :expand-lst ac.expanded-fn-lst)
                          fty-info state))
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
                 (- (cw "fn-call: ~p0, flex?: ~p1~%" fn-call flex?))
                 (lvl-item (assoc-equal fn-call a.fn-lvls))
                 (extract-res (meta-extract-formula fn-call state))
                 ((if (or basic-function flex?
                          (<= a.wrld-fn-len 0) (and lvl-item (zp (cdr lvl-item)))
                          (equal extract-res ''t)))
                  (b* ((actuals-res
                        (expand (change-ex-args a :term-lst fn-actuals)
                                fty-info state))
                       ((ex-outs ac) actuals-res)
                       (rest-res
                        (expand (change-ex-args a :term-lst rest
                                                :expand-lst ac.expanded-fn-lst)
                                fty-info state))
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
                 (- (cw "SMT-goal-generator=>Expanding ... ~q0" fn-call))
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
                          fty-info state))
                 ((ex-outs b) body-res)
                 ;; Expand function
                 (expanded-lambda-body (car b.expanded-term-lst))
                 (expanded-lambda `(lambda ,formals ,expanded-lambda-body))
                 (actuals-res
                  (expand (change-ex-args a :term-lst fn-actuals
                                          :expand-lst b.expanded-fn-lst)
                          fty-info state))
                 ((ex-outs ac) actuals-res)
                 (expanded-term-list ac.expanded-term-lst)
                 ((unless (equal (len formals) (len expanded-term-list)))
                  (prog2$
                   (er hard? 'SMT-goal-generator=>expand "You called your function with the wrong number of actuals: ~q0" term)
                   (make-ex-outs :expanded-term-lst a.term-lst :expanded-fn-lst ac.expanded-fn-lst)) )
                 (rest-res
                  (expand (change-ex-args a :term-lst rest
                                          :expand-lst ac.expanded-fn-lst)
                          fty-info state))
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
                          fty-info state))
                 ((ex-outs ac) actuals-res)
                 (rest-res
                  (expand (change-ex-args a :term-lst rest
                                          :expand-lst ac.expanded-fn-lst)
                          fty-info state))
                 ((ex-outs r) rest-res))
              (make-ex-outs :expanded-term-lst (cons (cons fn-call ac.expanded-term-lst) r.expanded-term-lst)

                            :expanded-fn-lst r.expanded-fn-lst)))

           ;; If fn-call is not expanded to level 0, still can expand.
           (new-fn-lvls (update-fn-lvls fn-call a.fn-lvls))
           ((func f) (cdr fn))
           (formals f.flattened-formals)
           (body-res
            (expand (change-ex-args a :term-lst (list f.body)
                                    :fn-lvls new-fn-lvls)
                    fty-info state))
           ((ex-outs b) body-res)
           (expanded-lambda-body (car b.expanded-term-lst))
           (expanded-lambda `(lambda ,formals ,expanded-lambda-body))
           (actuals-res
            (expand (change-ex-args a :term-lst fn-actuals
                                    :expand-lst b.expanded-fn-lst)
                    fty-info state))
           ((ex-outs ac) actuals-res)
           (expanded-term-list ac.expanded-term-lst)
           ((unless (equal (len formals) (len expanded-term-list)))
            (prog2$
             (er hard? 'SMT-goal-generator=>expand "You called your function with the wrong number of actuals: ~q0" term)
             (make-ex-outs :expanded-term-lst a.term-lst :expanded-fn-lst ac.expanded-fn-lst)))
           (rest-res
            (expand (change-ex-args a :term-lst rest
                                    :expand-lst ac.expanded-fn-lst)
                    fty-info state))
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
             :use ((:instance pseudo-term-listp-of-pseudo-lambdap-of-cdar-ex-args->term-lst)
                   (:instance  symbolp-of-caar-of-ex-args->term-lst)))))

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

  (define generate-fty-types-top ((hints smtlink-hint-p)
                                  (flextypes-table alistp))
    :returns (updated-hints smtlink-hint-p)
    (b* ((hints (smtlink-hint-fix hints))
         ((smtlink-hint h) hints)
         ((unless (alistp flextypes-table)) h)
         (fty-types (generate-fty-type-list h.fty flextypes-table
                                            h.fty-info nil)))
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
           (- (cw "fty-info: ~q0" (smtlink-hint->fty-info hints)))
           (hints (generate-fty-types-top hints flextypes-table))
           (- (cw "fty-types: ~q0" (smtlink-hint->fty-types hints)))

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
           (hint-with-fn-expand
            (if (equal nil expand-hint)
                h.main-hint
              (append `(:in-theory (enable ,@expand-hint)) h.main-hint)))
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

  )
