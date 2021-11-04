; A transformation to perform incrementalization
;
; Copyright (C) 2015-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; STATUS: IN-PROGRESS

;(include-book "rewriter")
(include-book "simplify")
;(include-book "expand-lets")
(include-book "utilities/extract-non-local-events")
(include-book "utilities/names") ; for INCREMENT-NAME-SUFFIX-SAFE
(include-book "utilities/defun-variant")
(include-book "kestrel/utilities/world" :dir :system) ; for fn-definedp
(include-book "kestrel/utilities/reconstruct-macros" :dir :system)
(include-book "kestrel/utilities/declares" :dir :system) ; for fixup-ignores
(include-book "kestrel/utilities/defining-forms" :dir :system)
(include-book "kestrel/terms-light/add-param-to-calls-in-term" :dir :system)
(include-book "kestrel/utilities/submit-events" :dir :system)
(include-book "kestrel/utilities/my-get-event" :dir :system)
(include-book "kestrel/utilities/fresh-names" :dir :system)
(include-book "kestrel/utilities/verify-guards-dollar" :dir :system)
(include-book "kestrel/utilities/directed-untranslate-dollar" :dir :system)
(include-book "kestrel/untranslated-terms-old/untranslated-terms" :dir :system)
(include-book "kestrel/std/system/install-not-normalized-event" :dir :system)
(include-book "kestrel/utilities/er-soft-plus" :dir :system)

(defxdoc finite-difference
  :parents (transformations)
  :short "This transformation performs finite-differencing, aka
incrementalization."

  :long "<h3>Usage</h3>

@({
     (finite-difference fn
                        term-to-replace
                        rules
                        [:skip-termination bool]     ;; Default: nil
                        [:verify-guards t/nil/auto]  ;; Default: :auto
                        [:guard-hints hints/:auto]   ;; Default: :auto
                        [:new-param-name name]       ;; Default: nil
                        [:expand-lets bool]          ;; Default: t
                        [:extra-rules rules]         ;; Default: nil
                        [:theorem-name name]         ;; Default: nil
                        [:build-wrapper bool]        ;; Default: t
                        [:theorem-disabled bool]     ;; Default: nil
                        [:function-disabled bool]    ;; Default: nil
                        [:new-name sym]              ;; New name to use for the function (if :auto, the transformation generates a name), Default: :auto
                        [:check-guard bool]          ;; Default: nil, whether to check the claimed relationship in the body of the function (may be needed for termination)
                        [:show-only bool]            ;; Default: nil
                        )
})


<h3>Detailed Description</h3>

<p>Consider a function, F(x) [assume F is unary for this discussion], whose
body includes some term, T(x), over the parameter x.  It may be the case that T
could be calculated incrementally (that is, we can use the current value of
T(X) to compute the value of T(x) that will be needed on the next iteration,
after x is updated).  This may be cheaper than calculating T(x) each time.</p>

<p>The transformation does the following:</p>

<ol>

<li>Build a function version of F(x), call it F$1-pre(x,v), that has an
additional parameter (call it v) which is always equal to T(x).  All recursive
calls must be changed pass the updated value of the new V parameter.  F$1-pre
will compute this for each call by replacing x in T(x) with the actual value of
x passed to the recursive call.  This establishes the invariant v=T(x) on the
recursive calls.</li>

<li>Prove that F$1-pre(x) is equivalent to F$1(x,v).  Note that F$1-pre ignores
its v parameter (but F$1, built below, will not).</li>

<li>Build F$1 by simplifying the body of F$1-pre, in two ways: 1) Simply use
the new v parameter instead of computing T(x). 2) Simplify the update of v
passed to each recursive call, using distributed laws provided by the user, to
express it in terms of T(x) = v.  This is the key incrementalization step.</li>

<li>Prove that F$1(x,v) is equivalent to F$1-pre(x,v) assuming v = T(x).</li>

<li>Build a wrapper function that calls F$1 with thv V parameter initialized to
T(x), thus establishing the invariant.</li>

<li>Prove that the wrapper function is equal to the original F.</li>

</ol>")


;; TODO: try on fibonacci-list (like factorial list)

;; TODO: add option to letify body

;; TODO: Add support for using the ambient theory?

;; TODO Add support for mutual recursion

;; General Schema (non-tail recursive version): TODO: Old comment?!

;; (defun loop (p1 p2 ...)
;;   (if (<term> p1 p2 ...)
;;       (<base> p1 p2 ...)
;;     (<combine> (<compute1> p1 p2 ...)
;;                (<compute2> p1 p2 ...)
;;                ...
;;                (<computeN> p1 p2 ...)
;;                ...
;;                (loop (<update1> p1)
;;                      (<update2> p2)
;;                      ...))))

;; where for one of the computeN's

;; (<computeN> (<update1> p1) (<update2> p2) ...)

;; can be efficiently computed from (<computeN> p1 p2 ...)
;;   and (<update1> p1) (<update2> p2) ...
;;   and p1 p2 ...

;; Then, add a new parameter v, which will for each call, always be equal to (<computeN> p1 p2 ...).

;; Then, from the above, first just add v, giving

;; (defun loop2 (p1 p2 ... v)
;;   (if (<term> p1 p2 ...)
;;       (<base> p1 p2 ...)
;;     (<combine> (<compute1> p1 p2 ...)
;;                (<compute2> p1 p2 ...)
;;                ...
;;                (<computeN> p1 p2 ...)
;;                ...
;;                (loop2 (<update1> p1)
;;                       (<update2> p2)
;;                       ...
;;                       (<computeN> (<update1> p1) (<update1> p2) ...)))))  ;this re-establishes the invariant about v

;; Then prove equivalence of this with the original (trivial induction, since v is not yet used).

;; Now (step 2), simplify the body of the function using:
;; 1. The directed equality (<computeN> p1 p2 ...) = v, and
;; 2. Other simplification rules that can simplify the update of v, (<computeN> (<update1> p1) (<update1> p2) ...)

;;Let s be the simplified version of (<computeN> (<update1> p1) (<update1> p2) ...) after applying rewrite rules.  The simplified version
;; of s should include v.

;; Then the result is:

;; (defun loop3 (p1 p2 ... v)
;;   (if (<term> p1 p2 ...)
;;       (<base> p1 p2 ...)
;;     (<combine> (<compute1> p1 p2 ...)
;;                (<compute2> p1 p2 ...)
;;                ...
;;                v  ;;the computeN has been replaced by v, using the invariant about v
;;                ...
;;                (loop3 (<update1> p1)
;;                       (<update2> p2)
;;                       ...
;;                       s)))) ;; s is simpler and should be phrased in terms of (the old value of) v

;; Then prove the equivalence of loop2 and loop3, again by induction.

;(in-theory (disable CAR-BECOMES-NTH-OF-0))

;; ;making this a separate function so we can trace it:
;; (defun untranslate-term (term w)
;;   (declare (xargs :mode :program))
;;   (untranslate term nil w))

;; A nice abbreviation when no rules are to be used (clearer than nil).
(defun no-rules () nil)

;; Returns (mv erp result state), where result is usually an event but in the erp case might contain useful info.
;TODO: pass back an error flag instead of calling hard-error.
;TODO: term-to-replace is a bad name
;TODO: check that term-to-replace is over the params of the function (what about let-bound vars?)...
(defun finite-difference-event (fn
                                term-to-replace ; gets translated
                                rules
                                extra-rules
                                skip-terminationp
                                verify-guards
                                guard-hints
                                new-param-name
                                expand-letsp
                                theorem-name
                                build-wrapper
                                theorem-disabled
                                function-disabled
                                new-name
                                check-guard
                                error-value
                                verbose
                                state)
  (declare (xargs :stobjs state
                  :guard (and (symbolp fn)
                              (symbol-listp rules)       ;todo improve
                              (symbol-listp extra-rules) ;todo improve
;                              (defun-formp fn-event)     ;for now
                              (booleanp skip-terminationp)
                              (member-eq verify-guards '(t nil :auto))
                              (booleanp expand-letsp)
                              (symbolp new-param-name)
                              (booleanp verbose)
                              (booleanp check-guard)
                              (member-eq function-disabled '(t nil :auto)))
                  :verify-guards nil
                  :mode :program ;;because we call translate-term
                  ))
  (b* (((when (not (symbol-listp rules)))
        (er-soft+ 'finite-difference :bad-input nil
                  "The :rules must be a list of symbols, but it is ~x0."
                  rules))
       ((when (not (symbol-listp extra-rules)))
        (er-soft+ 'finite-difference :bad-input nil
                  "The :extra-rules must be a list of symbols, but it is ~x0."
                  extra-rules))
       ((when (not (fn-definedp fn (w state))))
        (er-soft+ 'finite-difference :bad-input nil
                  "~x0 is not a defined function."
                  fn))
       (wrld (w state))
       (fn-event (my-get-event fn wrld))
       (body (fn-body fn nil wrld))
       (formals (fn-formals fn wrld))
       (rec (fn-recursivep fn state))
       (non-executable (non-executablep fn wrld))
       (term-to-replace (translate-term term-to-replace 'finite-difference-event wrld))
       ((when (member-eq fn (get-fns-in-term term-to-replace)))
        (mv t
            (hard-error 'finite-difference-event
                        "We do not allow the term passed to finite-difference to include a recursive call." nil)
            state))
       ((when (not (subsetp-eq (free-vars-in-term term-to-replace) formals))) ;todo: what about lets?
        (mv t
            (er hard? 'finite-difference-event "Term to replace, ~x0, has vars not among the formals, ~x1." term-to-replace formals)
            state))
       ;; TODO: Handle this better?:
       (body (if expand-letsp (expand-lambdas-in-term body) body))

       (declares (get-declares-from-event fn fn-event)) ;copy all of the old declares (TODO: Think about each kind of declare)
;         (guard-verifiedp (event-demands-guard-verificationp fn-event))
       (verify-guards ;(decide-whether-to-verify-guards verify-guards fn-event state)
         (if (eq :auto verify-guards)
             (guard-verified-p fn wrld)
           verify-guards))
       ;; We transform things in this order:  fn -> new-fn-pre -> new-fn-pre2 -> new-fn
       (new-fn (if (eq new-name :auto) (increment-name-suffix-safe fn state) new-name)) ;TODO think about name clashes
       (new-fn-pre-name (pack$ new-fn "-PRE"))
       (new-fn-pre2-name (pack$ new-fn "-PRE2"))
       (wrapper-fn (pack$ new-fn '-wrapper))

       (old-becomes-pre-theorem (pack$ fn '-becomes- new-fn-pre-name))
       (pre2-becomes-new-theorem (pack$ new-fn-pre2-name '-becomes- new-fn))
       (old-becomes-new-theorem-name (or theorem-name (pack$ fn '-becomes- new-fn)))
       (old-becomes-new-wrapper-theorem-name (or theorem-name (pack$ fn '-becomes- wrapper-fn)))

;todo: maybe pass previously generated names as names-to-avoid in these calls:
       ((mv fn-not-normalized-event fn-not-normalized &) (install-not-normalized-event fn nil nil wrld))
       ((mv new-fn-pre-not-normalized-event new-fn-pre-not-normalized &) (install-not-normalized-event new-fn-pre-name nil nil wrld))
       ((mv new-fn-pre2-not-normalized-event new-fn-pre2-not-normalized &) (install-not-normalized-event new-fn-pre2-name nil nil wrld))
       ((mv new-fn-not-normalized-event     new-fn-not-normalized &)     (install-not-normalized-event new-fn     nil nil wrld))
       ((mv wrapper-fn-not-normalized-event wrapper-fn-not-normalized &) (install-not-normalized-event wrapper-fn nil nil wrld))

       ;; the new param:
       (v (or new-param-name (make-fresh-name 'v formals))) ;TODO: also avoid any lambda-bound vars (if any)
       ;; build the body of the -pre function:
       (new-fn-pre-body (add-param-to-calls-in-term body fn formals term-to-replace))
       (new-fn-pre-body (rename-fn fn new-fn-pre-name new-fn-pre-body))
       ;; (measure-declares (if (not (fn-has-measurep fn state))
       ;;                       nil
       ;;                     `((xargs :measure ,(fn-measure fn state)))))
       (new-fn-pre-formals (append formals (list v)))
       (new-fn-pre-declares (fixup-ignores declares new-fn-pre-formals new-fn-pre-body))
       (new-fn-pre-declares (set-verify-guards-in-declares nil new-fn-pre-declares)) ; guard-verification may be done separately below
       (new-fn-pre-declares (replace-xarg-in-declares
                             :hints
                             `(("Goal" :in-theory '()
                                ;; ACL2 automatically replaces the old functions with the new ones in this:
                                :use (:instance (:termination-theorem ,fn))))
                             new-fn-pre-declares))
       (new-fn-pre `(defun ,new-fn-pre-name (,@new-fn-pre-formals)
                      ,@new-fn-pre-declares
                      ,(reconstruct-macros-in-term new-fn-pre-body) ;  (untranslate-term new-fn-pre-body wrld) ;;todo: or just use the untranslated body to build new-fn-pre
                      ))
       (- (and verbose (cw "(New-fn-pre: ~X01)~%" new-fn-pre nil)))
       (new-fn-pre-events `((local ,fn-not-normalized-event) ;todo: transformation prologue?
                            ;; The defun, etc:
                            (local (progn ,new-fn-pre))
                            (local ,new-fn-pre-not-normalized-event)
                            (local (defthmd ,old-becomes-pre-theorem
                                     (equal (,fn ,@formals)
                                            (,new-fn-pre-name ,@formals ,v))
                                     ;; :hints ,(if use-flagp ;weird format for make-flag hints:
                                     ;;             `('(:in-theory (append '(,fn ,new-fn-pre-name ,@enables) (theory 'minimal-theory))))
                                     ;;           `(("Goal" :induct t
                                     ;;              :in-theory (append '(,fn ,new-fn-pre-name ,@enables) (theory 'minimal-theory))
                                     ;;              )))
;              ,@(and use-flagp (list :flag fn))
                                     :hints (("Goal" :in-theory (append '(,fn-not-normalized ,new-fn-pre-not-normalized (:i ,new-fn-pre-name)) (theory 'minimal-theory))
                                              ,@(and rec `(:induct (,new-fn-pre-name ,@formals ,v)))
                                              :expand ((,fn ,@formals)
                                                       (,new-fn-pre-name ,@formals ,v)) ;TODO: equalities could mess this up? maybe use a computed hint?
                                              :do-not '(preprocess)))))
                            ,@(and verify-guards
                                   ;; This proof is not fully automatic,
                                   ;; because the term we put in to update the
                                   ;; new param may itself cause guard
                                   ;; obligations (TODO: Separate that out as
                                   ;; an applicability condition):
                                   `((local (verify-guards$ ,new-fn-pre-name
                                                            :hints
                                                            ,(if (eq :auto guard-hints)
                                                                 `(("Goal"
                                                                    ;; This should handle the bulk of the proof:
                                                                    :use (:instance (:guard-theorem ,fn))
                                                                    :do-not '(generalize eliminate-destructors) ;;TODO; Turn off more stuff:
                                                                    ;; we use the becomes lemma(s):
                                                                    :in-theory (enable ,old-becomes-pre-theorem)
                                                                    ))
                                                               guard-hints)))))))
       ;; must submit the defun now, so that it is there for simplify-defun to see:
       (state (submit-events-quiet new-fn-pre-events state))
       ;;step 2:

       ;; Now use simplify-defun to simplify the update of v in the rec. call, yielding the new-fn-pre2 and pre-becomes-pre2-theorem:
       (pre-becomes-pre2-theorem (pack$ new-fn-pre-name '-becomes- new-fn-pre2-name))
       (formal-patterns (append (repeat (len formals) '_) (list '@))) ;the last param of recursive calls is where we want to simplify (TODO: What if there is more than 1 call?)
       ;; todo: separate out the various uses of guard-hints?  these are separate 'applicability conditions':
       ;; (simplify-defun-guard-hints (if (eq :auto guard-hints)
       ;;                                 nil ;default for simplify-defun
       ;;                               guard-hints))
       (simplify-print-arg (if verbose :all :error))
       ((er result) ;passes back the erp and result from simplify-defun
        (simplify-defun-programmatic new-fn-pre-name
                                     :new-name new-fn-pre2-name ;:normalize nil
                                     ;;:untranslate nil ;because we need to preserve the exact term that v replaces below (for now, we work around it)
                                     :theory `',rules
                                     ;; just simplify the recursive call(s):
                                     :simplify-body (cons new-fn-pre-name formal-patterns)
                                     :must-simplify nil
                                     :guard-hints guard-hints
                                     :print simplify-print-arg
                                     ))
       ;;TODO: Keep arguments in sync with the above:
       (simplify-defun-event
        `(simplify-defun ,new-fn-pre-name
                         :new-name ,new-fn-pre2-name
                         :theory ',rules
                         :simplify-body ,(cons new-fn-pre-name formal-patterns)
                         :must-simplify nil
                         :guard-hints ,guard-hints
                         :print ,simplify-print-arg))
       ;; (new-fn-pre2-defun (cdr result))
       (new-fn-pre2-defun (extract-single-non-local-defun result))
;       (- (cw "new-fn-pre2: ~x0" new-fn-pre2-name))
       ;; Now put in v where possible for its corresponding expression:
       (new-fn-pre2-body (car (last new-fn-pre2-defun))) ;untranslated!
       ;; replace both the translated and untranslated forms of the term (TODO: Think about this -- really want to replace any term that translates the same as the given term):
       (untranslated-term-to-replace (untranslate term-to-replace nil (w state)))
       (new-fn-body (replace-in-untranslated-term new-fn-pre2-body (acons untranslated-term-to-replace v nil))) ;untranslated! ;;TODO: Think about how this might work with lets now...
       (new-fn-body (replace-in-untranslated-term new-fn-body (acons term-to-replace v nil)))
       (new-fn-body (rename-fns-in-untranslated-term new-fn-body (acons new-fn-pre2-name new-fn nil))) ;untranslated!
       (guard `(equal ,v ,term-to-replace))
       (new-fn-body (if check-guard
                        `(if (not (mbt ,guard))
                             ,error-value ;;todo: support :auto, which means try to find a good base case (by looking at ifs and mbts) -- maybe even combine this test into an existing test
                           ,new-fn-body)
                      new-fn-body))

;       (new-fn-body (if expand-letsp (expand-lambdas-in-term new-fn-body) new-fn-body))
;       (new-fn-body (rewrite-term2 new-fn-body rules state))
;       (new-fn-body (replace-in-term new-fn-body (acons term-to-replace v nil))) ;;TODO may need to ignore v and print a warning if v doesn't appear!
;(reconstruct-macros-in-term new-fn-body) ; (untranslate-term new-fn-body (w state))
       ;; (directed-untranslate$ new-fn-body
       ;;                        body ;not sure which body to use here, so let's try the original function's body
       ;;                        (w state))

       (guard (reconstruct-macros-in-term guard)) ;(untranslate-term guard (w state))
       (declares (add-guard-conjunct guard declares)) ;;TODO: The guard hints should be exactly the RULES, plus the old guard hints?
;         (declares (if guard-verifiedp declares (add-verify-guards-nil declares)))  ;keeps the guard about v from triggering guard verification
       (wrapper-guard (fn-guard fn (w state))) ;TODO: what about other declares?
       (new-fn-declares (fixup-ignores declares (cons v formals) new-fn-body))
       (new-fn-declares (replace-xarg-in-declares
                         :hints
                         `(("Goal" :in-theory '()
                            ;; ACL2 automatically replaces the old functions with the new ones in this:
                            :use (:instance (:termination-theorem ,new-fn-pre2-name))))
                         new-fn-declares))
       (new-fn-declares (set-verify-guards-in-declares nil new-fn-declares)) ; may be done separately, below
       (defun-variant (defun-variant fn non-executable function-disabled state))
       (new-fn-defun `(,defun-variant ,new-fn (,@formals ,v)
                       ,@new-fn-declares
                       ,new-fn-body)))
    (mv
     nil
     `(encapsulate
        ()
        ;; The -pre function takes and updates the new parameter but doesn't
        ;; really use it yet.  Everything mentioning the -pre function is local
        ;; to the encapsulate (no need to export it, it's just a way to get to
        ;; the final function).
        ,@new-fn-pre-events

        ;; The -pre2 function has a simplified version of the update of the new
        ;; param (often, the simplified expression will mention the expression
        ;; represented by the new param).  It is also local to the encapsulate.
        (local ,simplify-defun-event) ; this gives us pre-becomes-pre2-theorem
        (local ,new-fn-pre2-defun) ; this is just a check; it will be redundant since simplify-defun introduces this (todo: include the theorem here too)
        (local ,new-fn-pre2-not-normalized-event)

        ;; This is NEW-FN, the main new function being created.  It has the new-param
        ;; put in for all mentions of its corresponding expression:
        ,(if skip-terminationp `(skip-proofs ,new-fn-defun) new-fn-defun) ; guard proof not skipped since :verify-guards is nil

        (local ,new-fn-not-normalized-event)

        ;;TODO: prove the base and inductive cases explicitly
        ;;TODO: Applicability condition to show that the assumption about v is preserved on recursive calls (does simplify-defun also have to prove that?)...
        (local (defthmd ,pre2-becomes-new-theorem
                 (implies (equal ,v ,term-to-replace)
                          (equal (,new-fn-pre2-name ,@formals ,v)
                                 (,new-fn ,@formals ,v)))
                 :hints (("Goal" :induct (,new-fn ,@formals ,v)
                          :expand (,new-fn-pre2-name ,@formals ,term-to-replace) ;sometimes needed because of acl2's heuristics (TODO: what if substitution changes this term?)
                          :in-theory (append '( ;,new-fn-pre-not-normalized
                                               ,new-fn-pre2-name
                                               ,new-fn-not-normalized
                                               ,new-fn-pre2-not-normalized
                                               (:i ,new-fn) ,@rules ,@extra-rules)
                                             (theory 'minimal-theory))
                          :do-not '(generalize eliminate-destructors fertilize))) ;todo: or use the old function, or the joint scheme?
                 ;; :hints ,(if use-flagp ;weird format for make-flag hints:
                 ;;             `('(:in-theory (append '(,fn ,new-fn-pre-name ,@enables) (theory 'minimal-theory))))
                 ;;           `(("Goal" :induct t
                 ;;              :in-theory (append '(,fn ,new-fn-pre-name ,@enables) (theory 'minimal-theory))
                 ;;              )))
;              ,@(and use-flagp (list :flag fn))
                 ))
        ,@(and verify-guards
               `((verify-guards$ ,new-fn
                                 ;; The guard obligations should be the same or strictly
                                 ;;less than for the -pre2 function, except with the expr
                                 ;;substituted for v, but the guard says the expr is the
                                 ;;same as v -- except that guard obligations from the expr itself
                                 ;;may arise, because now it is in the guard (todo: carve that out
                                 ;; as an applicability condition) -- yes, usually the the expr
                                 ;; also appears in the body of pre2, meaning we already have that obligation,
                                 ;; but it may be guarded by an IF, so it may have conditions from that IF in
                                 ;; the guard obligation of -pre2.
                                 :hints
                                 ,(if (eq :auto guard-hints)
                                      `(("Goal"
                                         :use (:instance (:guard-theorem ,new-fn-pre2-name))
                                         :do-not '(generalize eliminate-destructors) ;;TODO; Turn off more stuff:
                                         ;; we use the becomes lemma(s):
                                         ;;:in-theory (enable ,pre2-becomes-new-theorem)
                                         :in-theory (enable ,pre2-becomes-new-theorem)
                                         ))
                                    guard-hints))))

        ;; The wrapper function initializes v and then calls the main loop function
        ;; The wrapper function will typically be left enabled:
        ,@(and build-wrapper ;; suppress the wrapper if build-wrapper is nil
               `((,defun-variant ,wrapper-fn (,@formals)
                  ,@(if (defun-has-a-guardp fn-event)
                        `((declare (xargs :guard ,wrapper-guard
                                          :verify-guards ,verify-guards ;todo
                                          ;; Shouldn't need any
                                          ;; hints (guard of new fun
                                          ;; is the same as for the
                                          ;; wrapper [and the old
                                          ;; fn] except it required
                                          ;; that v = its expression, which the wrapper establishes:
                                          :guard-hints ,(if (eq :auto guard-hints)
                                                            `(("Goal" :do-not '(generalize eliminate-destructors)
                                                               :do-not-induct t
                                                               :in-theory nil))
                                                          guard-hints))))
                      nil)
                  (declare (xargs :normalize nil)) ;new (todo: drop)
                  ;; ,@declares ;TODO: think about the declares!
                  (,new-fn ,@formals ,term-to-replace))))
        ,@(and build-wrapper `((local ,wrapper-fn-not-normalized-event)))

        ,(if build-wrapper
             ;; The main theorem that rewrites the old function to the wrapper:
             `(,(if theorem-disabled 'defthmd 'defthm) ,old-becomes-new-wrapper-theorem-name
               (equal (,fn ,@formals)
                      (,wrapper-fn ,@formals))
               :hints (("Goal"
                        :use (:instance ,old-becomes-pre-theorem (,v ,term-to-replace))
                        :in-theory (append '(,pre-becomes-pre2-theorem ,pre2-becomes-new-theorem ,wrapper-fn-not-normalized)
                                           (theory 'minimal-theory))))
               ;; :hints ,(if use-flagp ;weird format for make-flag hints:
               ;;             `('(:in-theory (append '(,fn ,new-fn-pre-name ,@enables) (theory 'minimal-theory))))
               ;;           `(("Goal" :induct t
               ;;              :in-theory (append '(,fn ,new-fn-pre-name ,@enables) (theory 'minimal-theory))
               ;;              )))
;              ,@(and use-flagp (list :flag fn))
               )
           ;; We are not generating the wrapper:
           `(,(if theorem-disabled 'defthmd 'defthm) ,old-becomes-new-theorem-name
             (equal (,fn ,@formals)
                    (,new-fn ,@formals ,term-to-replace))
             :hints (("Goal"
                      :use (:instance ,old-becomes-pre-theorem (,v ,term-to-replace))
                      :in-theory (append '(,pre-becomes-pre2-theorem ,pre2-becomes-new-theorem)
                                         (theory 'minimal-theory))))
             ;; :hints ,(if use-flagp ;weird format for make-flag hints:
             ;;             `('(:in-theory (append '(,fn ,new-fn-pre-name ,@enables) (theory 'minimal-theory))))
             ;;           `(("Goal" :induct t
             ;;              :in-theory (append '(,fn ,new-fn-pre-name ,@enables) (theory 'minimal-theory))
             ;;              )))
;              ,@(and use-flagp (list :flag fn))
             )))
     state)))

;; ;assumes the base case is the then-branch (maybe not??)
;; ;TODO: handle when the combine is the then-branch (maybe done?)
;; ;;fn should be a recursive but not tail-recursive function (for now)
;; ;the :extra-rules may be needed in the ACL2 proof (in case the RULES given are not confluent and the ACL2 rewriter takes a different path)
;; ; The :extra-rules may also help to resolve conditions of conditional rewrite rules?

(deftransformation finite-difference
  (fn
   term-to-replace
   rules  ;TODO: Make this a keyword argument (defailt nil?)? or allow :enable, etc and pass through to simplify-defun
   )
  ((extra-rules 'nil)
   (skip-termination 'nil)
   (verify-guards ':auto)
   (guard-hints ':auto)
   (new-param-name 'nil)
   (expand-lets 't)
   (theorem-name 'nil)
   (build-wrapper 't)
   (theorem-disabled 'nil)
   (function-disabled 'nil) ; todo: make :auto the default?
   (new-name ':auto)
   (check-guard 'nil) ;; whether to check the claimed relationship in the body of the function (may be needed for termination)
   (error-value ':error)
   )
  :pass-print t ;must be passed in to finite-difference-event because it's passed to simplify-defun
  )

;; See tests in finite-difference-tests.lisp
