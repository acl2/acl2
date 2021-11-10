; A transformation to transform the output of a function using a wrapper
;
; Copyright (C) 2014-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Main Author: Eric Smith (eric.smith@kestrel.edu)
; Supporting Authors: Nathan Guermond and Jared Davis

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; STATUS: IN-PROGRESS

;;TODO: Restrict the hints to these transforms to keep them from going off the rails.

;;TODO: We may be able to better handle non-tail calls as follows: Say my
;;function f(x) makes a non-tail call in some branch.  Say that call is:

;; TODO: Improve this to operate on untranslated terms

;; TODO: Applicability guard conditions for calling the wrapper on each branch.

;; (g (f (update x))).
;;
;; Now I want to wrap the output of f in w.  So I would get:
;;
;; (w (g (f (update x))).  I can't replace the call to f with a call to f'
;; because of g.  But if I can somehow commute w and g, giving
;;
;; (g' (w (f (update x))))
;;
;; then I can replace the (w (f (update x))) with (f' (update x)).

(include-book "tools/flag" :dir :system)
(include-book "misc/records" :dir :system)
(include-book "misc/install-not-normalized" :dir :system)
(include-book "utilities/deftransformation")
(include-book "utilities/defun-variant")
(include-book "utilities/option-parsing")
(include-book "utilities/function-renamingp")
(include-book "utilities/transformation-prologue")
(include-book "utilities/names")
(include-book "kestrel/utilities/dont-remove-trivial-equivalences" :dir :system)
(include-book "kestrel/utilities/translate" :dir :system)
(include-book "kestrel/utilities/defining-forms" :dir :system)
(include-book "kestrel/utilities/world" :dir :system)
(include-book "kestrel/utilities/my-get-event" :dir :system)
(include-book "kestrel/utilities/fixup-ignores" :dir :system)
(include-book "kestrel/utilities/fixup-irrelevants" :dir :system)
(include-book "kestrel/utilities/system/world-queries" :dir :system)
(include-book "kestrel/apt/utilities/verify-guards-for-defun" :dir :system)
(include-book "kestrel/terms-light/wrap-pattern-around-term" :dir :system)
(include-book "kestrel/alists-light/lookup-eq-safe" :dir :system)
(include-book "kestrel/untranslated-terms-old/untranslated-terms" :dir :system)

(defxdoc wrap-output
  :parents (transformations)
  :short "Push an external computation into a function (by pushing it
through the top-level if-branches of the function)."

  :long "<p>Given a function @('f') and a (unary) wrapper function @('wrapper'), the
transformation acts on the top level @(see if) branches as follows:</p>

<p>If the branch contains no recursive call then @('wrapper') is simply wrapped around the branch.
Otherwise, if the branch contains a tail-recursive call then the recursive call is replaced by a recursive call of the transformed
function @('f$1'), and if the recursive call is not a tail call then @('wrapper') is wrapped
around the original call of @('f'). In particular this means that
the resulting function may no longer be recursive. The same rules apply if @('f')
lies in a mutual-recursion nest, so that the new functions may no longer be
mutually recursive.</p>

<p>If a top-level term is a lambda then the body of the lambda is treated as a branch <b>unless</b> free variables in @('wrapper') become bound in the body (TODO: treat this case).</p>

<p> Note furthermore that this transformation is applied to the untranslated (see @(see trans)) form of the body, so macros are not expanded. The only macros treated separately are @(see and), @(see or) (TODO!), @(see let), @(see let*), @(see b*), (TODO? @(see mv-let)) and @(see cond).</p>

<p>The transformation produces the equivalence theorem</p>
@({(defthm f-f$1-connection
    (equal (w (f arg-1 ... arg-n))
           (f$1 arg-1 ... arg-n free-1 ... free-k)))
   })

<p>where @('free-1'), ..., @('free-k') are free variables possibly introduced in @('wrapper') if it is a lambda term.</p>

<p>This transformation is in some sense the dual of @(see wrap-input).</p>

<h3>Example Scenarios</h3>

<ul>
<li>Suppose @('foo') is defined as follows
@({(defun foo (x)
     (cond ((<test-1>)
            (bar x))          ;; non-recursive
           ((<test-2>)
            (foo (bar x)))    ;; tail-recursive
           ((<test-3>)
            (bar (foo x)))    ;; recursive but not tail-recursive
           ((<test-4>)
            ((lambda (y) (foo y)) (foo x)))) ;; lambda
   })
then if @('wrapper') is a wrapper function then @('foo') is transformed to the function
@({(defun foo$1 (x)
     (cond ((<test-1>)
            (wrapper (bar x)))
           ((<test-2>)
            (foo$1 (bar x)))
           ((<test-3>)
            (wrapper (bar (foo x))))
           ((<test-4>)
            ((lambda (y) (foo$1 y)) (foo x))))) ;; the argument is unchanged
   })</li>

<li>If the term @('(lambda (x) (nth '2 x))') is wrapped around a function that returns @('(list x y z)'), then the new functions simply returns @('z').  (This is useful for
functions that axe has lifted).</li>
</ul>



<h3>Usage</h3>

@({
    (wrap-output fn                        ;; Function to refine
                 wrapper                   ;; A unary function or unary lambda, where free variables are added as arguments
;; TODO: add check that free variables are not function parameters! (or that they don't do bad things)
                 [:theorem-disabled bool]  ;; Whether to disable the theorem(s) that replace the old function with the new, Default: nil
                 [:function-disabled bool] ;; Whether to disable the new function, Default: nil
                                           ;; In a mutual-recursion nest this applies to all functions
                 [:new-name map]           ;; New name to use for the function (if :auto, the transformation generates a name)
                 [:guard map]              ;; Apply a guard to the generated function
                 [:guard-hints hints]      ;; Hints for the guard proof, Default: nil
                 [:show-only bool]         ;; Show event without execution
                 [:print print-specifier]  ;; Specifies how output is printed (see @(see print-specifier))
                 )
    ;; If a function is in a mutual-recursion nest then the parameters :new-name and :guard
    ;; can be applied separately through a list of doublets of the form
    (:map (name-1 val-1) ... (name-k val-k))
})


<p>TODO: Add check: For now, the wrapper should only be over one variable.</p>")

(defun untranslated-lambdap (x)
  (declare (xargs :guard t))
  (and (true-listp x)
       (= (len x) 3)
       (eq (first x) 'lambda)
       (symbol-listp (second x))
       (untranslated-termp (third x))))

(defun untranslated-unary-lambdap (x)
  (declare (xargs :guard t
                  :guard-hints (("Goal" :in-theory (enable pseudo-lambdap)))))
  (and (untranslated-lambdap x)
       (eql 1 (len (second x))) ;exactly one argument
  ))

(defun wrap-pattern-around-untranslated-term (term pattern)
  (declare (xargs :guard (and (untranslated-TERMP TERM)
                              (untranslated-unary-lambdap pattern))
                  :guard-hints (("Goal" :in-theory (enable untranslated-LAMBDAP))))) ;todo
  (let* ((lambda-formals (second pattern))
         (lambda-body (third pattern))
         (var (first lambda-formals)) ;the only formal
         )
    (sublis-var-UNTRANSLATED-TERM (acons var term nil) lambda-body)))


;;TODO: Or maybe the extra vars can be names of params of the function (that are passed around unchanged??)?

;; ;; Tests for and:

;; ;; ;many args:
;; (defstub f (x) t)
;; (thm
;;  (equal (f (and x y z))
;;         (if (and x y)
;;             (f z)
;;           (f nil))))

;; WRAPPER mentions the single variable x
;; for each if-branch B of term, replace it with the result of substituting B for x in WRAPPER
;; except: if the branch is a recursive call of the old function, just call the new function (adding any new formals).
;; TERM is an untranslated term.
(mutual-recursion
 (defun wrap-output-in-term (term wrapper fn-renaming new-formals)
   (declare (xargs :guard (and (untranslated-termp term) ;(pseudo-termp term)
                               (untranslated-unary-lambdap wrapper)
;                              (pseudo-termp (third wrapper))
                               (function-renamingp fn-renaming)
                               (symbol-listp new-formals))
                   :guard-hints (("Goal" :expand (UNTRANSLATED-TERMP TERM)))))
   (if (atom term)
       (wrap-pattern-around-untranslated-term term wrapper)
     (let ((fn (ffn-symb term)))
       (if (eq 'quote fn)
           (wrap-pattern-around-untranslated-term term wrapper)
         (if (eq 'if fn)
             ;;If it's an IF, apply to both branches:
             `(if ,(farg1 term)
                  ,(wrap-output-in-term (farg2 term) wrapper fn-renaming new-formals)
                ,(wrap-output-in-term (farg3 term) wrapper fn-renaming new-formals))
           (if (eq fn 'and)
               (if (eql 0 (len (fargs term))) ;; (and) = t, so we wrap t:
                   (wrap-pattern-around-untranslated-term t wrapper)
                 (if (eql 1 (len (fargs term))) ;; (and x) = x, so we wrap x:
                     (wrap-pattern-around-untranslated-term (farg1 term) wrapper)
                   (if (eql 2 (len (fargs term)))
                       `(if ,(farg1 term)
                            ,(wrap-output-in-term (farg2 term) wrapper fn-renaming new-formals)
                          ,(wrap-pattern-around-untranslated-term nil wrapper))
                     ;; If all the args except the first are true, then the AND
                     ;; is equal to the last arg, so wrap that.  Otherwise, the
                     ;; AND is nil, so wrap nil:
                     `(if (and ,@(butlast (fargs term) 1))
                          ,(wrap-pattern-around-untranslated-term (car (last (fargs term))) wrapper)
                        ,(wrap-pattern-around-untranslated-term nil wrapper)))))
             ;;fixme: handle nary OR as we do for AND above
             (if (eq fn 'or) ;; (or x y) = (if x t y)
                 `(if ,(farg1 term)
                      ,(wrap-pattern-around-untranslated-term t wrapper)
                    ,(wrap-output-in-term (farg2 term) wrapper fn-renaming new-formals))
               (if (consp fn) ;test for lambda application: ((lambda (vars) body) ... args ...)
                   ;; If it's a lambda, wrap the lambda body (TODO: think about free vars in the wrapper)
                   ;; TODO: Think about this case
                   (let* ((args (fargs term))
                          (lambda-formals (ulambda-formals fn))
                          (lambda-declares (ulambda-declares fn))
                          (lambda-body (ulambda-body fn)))
                     `(,(make-ulambda lambda-formals lambda-declares (wrap-output-in-term lambda-body wrapper fn-renaming new-formals)) ,@args))
                 (if (member-eq fn '(let let*))
                     (let ((bindings (farg1 term))
                           (declares (let-declares term))
                           (body (car (last (fargs term)))))
                       `(,fn ;the let, etc.
                         ,bindings
                         ,@declares
                         ,(wrap-output-in-term body wrapper fn-renaming new-formals)))
                   (if (eq 'b* fn)      ;no declare allowed for b*
                       `(b* ,(farg1 term) ;the bindings
                          ,(wrap-output-in-term (farg2 term) wrapper fn-renaming new-formals))
                     (if (eq 'cond fn)
                         `(cond ,@(make-doublets
                                   (strip-cars (rest term))
                                   (wrap-output-in-terms (strip-cadrs (rest term)) wrapper fn-renaming new-formals)))
                       ;; TODO: Handle case!
                       (if (assoc-eq fn fn-renaming)
                           ;; It's a tail call, so
                           ;;put in a call of the new function: (TODO: Do this in a separate step?)
                           `(,(lookup-eq fn fn-renaming) ;inefficient, use the assoc-eq above
                             ,@(fargs term)
                             ,@new-formals)
                         ;;anything other than an IF or lambda or call of the old function is just a branch to be wrapped:
                         ;; There may be calls of functions in the nest below this, so they just remain.
                         (wrap-pattern-around-untranslated-term term wrapper)))))))))))))

 (defun wrap-output-in-terms (terms wrapper fn-renaming new-formals)
   (declare (xargs :guard (and (untranslated-term-listp terms)
                               (untranslated-unary-lambdap wrapper)
;                              (pseudo-termp (third wrapper))
                               (function-renamingp fn-renaming)
                               (symbol-listp new-formals))))
   (if (endp terms)
       nil
     (cons (wrap-output-in-term (first terms) wrapper fn-renaming new-formals)
           (wrap-output-in-terms (rest terms) wrapper fn-renaming new-formals)))))

;; ;move
;; (in-theory (disable wrap-pattern-around-untranslated-term))
;; (in-theory (disable sublis-var))

;; ;; It would be nice if this worked... (my-make-flag SUBLIS-VAR1)

;; (thm
;;  (IMPLIES (AND (PSEUDO-TERMP TERM)
;;                (PSEUDO-TERMP PATTERN)
;;                )
;;           (PSEUDO-TERMP (WRAP-PATTERN-AROUND-UNTRANSLATED-TERM TERM PATTERN)))
;;  :hints (("Goal" :in-theory (enable wrap-pattern-around-untranslated-term))))

;; (thm
;;  (implies (and (PSEUDO-TERMP term)
;;                (PSEUDO-TERMP pattern)
;;                (function-renamingp fn-renaming))
;;           (PSEUDO-TERMP (wrap-output-in-term term pattern fn-renaming))))

(defun wrap-output-in-defun (fn
                             new-fn
                             fn-event wrapper fn-renaming rec options guard new-formals state)
  (declare (xargs :stobjs state :guard (and (symbolp fn)
                                            (symbolp new-fn)
                                            (untranslated-UNARY-LAMBDAP WRAPPER)
                                            (defun-or-mutual-recursion-formp fn-event)
;                                            (PSEUDO-TERMP (THIRD WRAPPER))
                                            (function-renamingp fn-renaming)
                                            (symbol-listp new-formals))
                  :verify-guards nil ;TODO
                  ))
  (let* ((body (get-body-from-event fn fn-event)) ; untranslated
         (wrld (w state))
         ;(body (fn-body fn t wrld))
         (formals (fn-formals fn wrld))
         (non-executable (non-executablep fn wrld))
         (function-disabled (g :function-disabled options))
         ;; Chose between defun, defund, defun-nx, etc.:
         (defun-variant (defun-variant fn non-executable function-disabled state))

         (new-body (wrap-output-in-term body wrapper fn-renaming new-formals))
         ;;(new-body (fix-up-lambda-ignores new-body))
         ;;(called-fns (get-fns-in-term new-body))
         (called-fns (get-called-fns-in-untranslated-term new-body)) ;todo: improve get-called-fns-in-untranslated-term?
         ;;(new-body (reconstruct-macros-in-term new-body))
         ;; Check whether
         (new-fn-recursivep (if (intersection-eq (strip-cdrs fn-renaming) called-fns) t nil)) ;TODO: what about mutual recursion becoming non-recursive?  we really should transform all the function bodies first and then see what we've got in terms of things bring recursive / mutually recursive
;         (has-measurep (fn-has-measurep fn state))

         (declares (get-declares-from-event fn fn-event)) ;TODO: Think about all the kinds of declares that get passed through.

         ;; Deal with the :verify-guards xarg.  We always do :verify-guards nil and then perhaps
         ;; do verify-guards later, in case the function appears in its own guard-theorem (meaning the guard proof needs the becomes-theorem)
         (declares (set-verify-guards-in-declares nil declares))
         (declares (remove-xarg-in-declares :guard-hints declares)) ; verify-guards is done separately
         (declares (remove-xarg-in-declares :guard-debug declares)) ; verify-guards is done separately
         (declares (remove-xarg-in-declares :guard-simplify declares)) ; verify-guards is done separately
         ;; Deal with the :guard xarg:
;         (guard-alist (g :guard-alist options))
;         (guard (lookup-eq-safe fn guard-alist))
         (declares (if (not (eq :auto guard))
                       (replace-xarg-in-declares :guard guard declares)
                     declares))
         (declares (if (not new-fn-recursivep)
                       ;; Nuke :the measure if needed:
                       (remove-xarg-in-declares :measure declares) ;todo: think about mut rec
                     declares))
         (declares (remove-xarg-in-declares :hints declares)) ;in case it becomes non-recursive (pretty common?)
         (declares (if (or new-fn-recursivep
                           (eq :mutual rec))
                       (replace-xarg-in-declares
                        :hints
                        `(("Goal" :in-theory '()
                           :use (:instance (:termination-theorem ,fn))))
                        declares)
                     declares)))
    `(,defun-variant ,new-fn (,@formals ,@new-formals)
       ,@declares
       ;; ,@(if has-measurep
       ;;       ;; use the same measure as the old fn:
       ;;       (list `(declare (xargs :measure ,(fn-measure fn state))))
       ;;     nil)
       ;;todo: pass through all the declares?
       ,new-body)))

;returns the new defuns
(defun wrap-output-in-defuns (fns fn-event wrapper fn-renaming options guard-alist new-formals state)
  (declare (xargs :stobjs state
                  :verify-guards nil
                  :guard (and (symbol-listp fns)
                              (untranslated-UNARY-LAMBDAP WRAPPER)
                              (defun-or-mutual-recursion-formp fn-event)
;                              (PSEUDO-TERMP (THIRD WRAPPER))
                              (function-renamingp fn-renaming)
                              (symbol-listp new-formals))))
  (if (endp fns)
      nil
    (let ((fn (first fns)))
      (cons (wrap-output-in-defun fn
                                  (lookup-eq-safe fn fn-renaming) ;new name for this fn
                                  fn-event
                                  wrapper fn-renaming :mutual options
                                  (lookup-eq-safe fn guard-alist)
                                  new-formals
                                  state)
            (wrap-output-in-defuns (rest fns) fn-event wrapper fn-renaming options guard-alist new-formals state)))))

(defun make-wrap-output-defthm (fn new-fn wrapper use-flagp options recursivep new-formals state)
  (declare (xargs :stobjs state :guard (and (symbolp fn)
                                            (not (eq 'quote fn))
                                            (not (member-eq fn *supported-untranslated-term-macros*))
                                            (symbolp new-fn)
                                            (untranslated-UNARY-LAMBDAP WRAPPER)
;                                            (PSEUDO-TERMP (THIRD WRAPPER))
                                            )))
  (let ((formals (fn-formals fn (w state)))
        (theorem-disabled (g :theorem-disabled options))
        (fn-not-normalized (install-not-normalized-name fn))
        (new-fn-not-normalized (install-not-normalized-name new-fn))
        )
    `(,(if theorem-disabled 'defthmd 'defthm)
       ,(pack$ fn '- new-fn '-connection)
       (equal ,(wrap-pattern-around-untranslated-term `(,fn ,@formals) wrapper) ;want to re-order but it causes loops.
              (,new-fn ,@formals ,@new-formals))
       ,@(and (not use-flagp) (list :hints `(("Goal"
                                              ;; Induct on the old function, since the new one may be non-recursive:
                                              ;; I think the induction will use the non-normalized body.
                                              ,@(if recursivep `(:induct (,fn ,@formals))
                                                  nil)
                                              :in-theory '(,@(if recursivep `((:induction ,fn)) nil) ;todo: think about this
                                                           ,fn-not-normalized ,new-fn-not-normalized)
                                              ;; todo: what if an equality causes a formal to be substituted?:
                                              ;; :expand ((,fn ,@formals)
                                              ;;          (,new-fn ,@formals))

                                              :do-not '(generalize eliminate-destructors))
                                             ;; In every inductive subgoal,
                                             ;; instantiate the bodies of both
                                             ;; functions applied to their
                                             ;; params.  Note that we have
                                             ;; called
                                             ;; dont-remove-trivial-equivalences,
                                             ;; since that can interfere with
                                             ;; this approach.  TODO: Maybe don't wait until stable.
                                             (if stable-under-simplificationp
                                                 '(:in-theory (theory 'minimal-theory)
                                                              :use (,fn-not-normalized ,new-fn-not-normalized))
                                               nil))))
       ,@(and use-flagp (list :flag fn)))))

(defun make-wrap-output-defthms (fns new-fns wrapper use-flagp options recursivep new-formals state)
  (declare (xargs :stobjs state :guard (and (symbol-listp fns)
                                            (not (member-eq 'quote fns))
                                            (not (intersection-eq fns *supported-untranslated-term-macros*))
                                            (symbol-listp new-fns)
                                            (untranslated-unary-lambdap wrapper)
;                                            (pseudo-termp (third wrapper))
                                            )))
  (if (endp fns)
      nil
    (cons (make-wrap-output-defthm (first fns) (first new-fns) wrapper use-flagp options recursivep
                                   new-formals
                                   state)
          (make-wrap-output-defthms (rest fns) (rest new-fns) wrapper use-flagp options recursivep new-formals state))))

(defun wrap-output-event (fn wrapper guard guard-hints theorem-disabled function-disabled new-name verify-guards state)
  (declare (xargs :stobjs state
                  :verify-guards nil ;TODO!
                  :guard (and (symbolp fn)
                              ;(symbolp new-name)
                              (not (eq 'quote fn))
                              (or (symbolp wrapper)
                                  (untranslated-unary-lambdap wrapper))
                              (t/nil/auto-p function-disabled))
                  :mode :program))
  (b* ((wrld (w state))
       (fn-event (my-get-event fn wrld))
       (options nil)
;         (options (s :guard-hints guard-hints options))
;         (options (s :guard guard options))
       (options (s :theorem-disabled theorem-disabled options))
       (options (s :function-disabled function-disabled options))
       (wrapper (if (symbolp wrapper) `(lambda (x) (,wrapper x)) wrapper)) ;convert a symbol into a unary lambda
       (lambda-formals (lambda-formals wrapper))
       (wrapper-body (lambda-body wrapper))
       (wrapper-body-vars (all-vars (translate-term wrapper-body 'wrap-output wrld)))
       (extra-wrapper-vars (set-difference-eq wrapper-body-vars lambda-formals))
       ;; ((when extra-wrapper-vars)
       ;;  (mv t
       ;;      (er hard 'wrap-output-event "Extra wrapper vars detected: ~x0." extra-wrapper-vars)
       ;;      state))
       ;; TODO: Check that any formals among the wrapper vars are passed through unchanged to all recursive calls
       (formals (fn-formals fn wrld))
       (new-formals (set-difference-eq extra-wrapper-vars formals))
       ;; (- (cw "Adding formals: ~x0.~%" new-formals)) ;;todo: optionally print this
       (recursivep (fn-recursivep fn state))
       (prologue (transformation-prologue fn wrld))
       (verify-guards (if (eq :auto verify-guards) (guard-verified-p fn wrld) verify-guards))
       (guard-hints (if (eq :auto guard-hints)
                        `(("Goal" :use (:instance (:guard-theorem ,fn))
                           ;; TODO: Restrict the theory here (but allow guard hints to be passed in)
                           ))
                      guard-hints)))
    (if (not recursivep)
        (let* ((new-fn (if (eq new-name :auto) (increment-name-suffix-safe fn state) new-name))
               ;; (function-renaming (acons fn new-fn nil))
               (new-defun (wrap-output-in-defun fn new-fn fn-event wrapper (acons fn new-fn nil) nil options guard new-formals state))
               ;; Drop the :verify-guards nil if needed, and add :verify-guards t if appropriate:
               (new-defun-to-export (if verify-guards (ensure-defun-demands-guard-verification new-defun) new-defun))
               (becomes-theorem (make-wrap-output-defthm fn new-fn wrapper nil options recursivep new-formals state)) ;unusual form (requires the wrapper to be present)
               ;; Remove :hints from the theorem before exporting it:
               (becomes-theorem-to-export (clean-up-defthm becomes-theorem)))
          (mv nil
              `(encapsulate ()
                 ,@prologue
                 (local ,new-defun) ; has :verify-guards nil
                 (local (install-not-normalized ,new-fn))
                 (local ,becomes-theorem)
                 ,@(and verify-guards `((local (verify-guards$ ,new-fn :hints ,guard-hints))))
                 ,new-defun-to-export
                 ,becomes-theorem-to-export)
              state))
      (if (fn-singly-recursivep fn state)
          (let* ((new-fn (if (eq new-name :auto) (increment-name-suffix-safe fn state) new-name))
                 ;; (function-renaming (acons fn new-fn nil))
                 (new-defun (wrap-output-in-defun fn new-fn fn-event wrapper (acons fn new-fn nil) :single options guard new-formals state))
                 (new-defun-to-export (if verify-guards (ensure-defun-demands-guard-verification new-defun) new-defun))
                 (new-defun-to-export (remove-hints-from-defun new-defun-to-export))
                 (becomes-theorem (make-wrap-output-defthm fn new-fn wrapper nil options recursivep new-formals state))
                 ;; Remove :hints from the theorem before exporting it:
                 (becomes-theorem-to-export (clean-up-defthm becomes-theorem)))
            (mv nil
                `(encapsulate ()
                   ,@prologue
                   (dont-remove-trivial-equivalences) ; is this still needed?
                   (local ,new-defun)
                   (local (install-not-normalized ,new-fn))
                   (local ,becomes-theorem)
                   ,@(and verify-guards `((local (verify-guards$ ,new-fn :hints ,guard-hints))))
                   ;; export the new defun and the becomes theorem:
                   ,new-defun-to-export
                   ,becomes-theorem-to-export)
                state))
        ;; FN is a member of a mutual-recursion:
        (b* ((ctx (cons 'wrap-output fn))
               (fns (get-clique fn wrld))
               ;; Handle the :new-name arg:
               (new-name-alist ;this is an alist, but some values may be :auto
                (elaborate-mut-rec-option2 new-name :new-name fns ctx))
               (function-renaming (pick-new-names new-name-alist state))
               (new-fn (lookup-eq-safe fn function-renaming))
               ;; Handle the :guard arg:
               (guard-alist ;this is an alist, but some values may be :auto
                (elaborate-mut-rec-option2 guard :guard fns ctx))
               (new-defuns (wrap-output-in-defuns fns fn-event wrapper function-renaming options guard-alist new-formals state))
               (mutual-recursion `(mutual-recursion ,@new-defuns))
               (mutual-recursion (fixup-ignores-in-mutual-recursion-form mutual-recursion wrld))
               (mutual-recursion (fixup-irrelevants-in-mutual-recursion-form mutual-recursion state))
               (mutual-recursion-to-export (if verify-guards
                                               (ensure-mutual-recursion-demands-guard-verification mutual-recursion)
                                             mutual-recursion))
               (mutual-recursion-to-export (remove-hints-from-mutual-recursion mutual-recursion-to-export))
               (first-fn (first fns))
               (make-flag-form `(make-flag ,(pack$ 'flag- first-fn) ,first-fn :hints (("Goal" :use (:instance (:termination-theorem ,fn))))))
               (becomes-theorems (make-wrap-output-defthms fns (strip-cdrs function-renaming) wrapper t options recursivep new-formals state))
               (becomes-defthm-flag `(,(pack$ 'defthm-flag- first-fn) ;; this is a custom kind of defthm when using the make-flag trick
                                      ,@becomes-theorems))
               (becomes-theorems-to-export (clean-up-defthms becomes-theorems)))
          (mv nil
              `(encapsulate nil
                 ,@prologue
                 (dont-remove-trivial-equivalences) ; drop?
                 (local ,mutual-recursion)
                 (local (install-not-normalized ,(lookup-eq-safe fn function-renaming)))
                 ;; This helps with the proof about mutually recursive functions:
                 (local ,make-flag-form)
                 (local ,becomes-defthm-flag)
                 ,@(and verify-guards `((local (verify-guards$ ,new-fn :hints ,guard-hints))))
                 ;; Export the new mutual-recursion:
                 ,mutual-recursion-to-export
                 ;; Export the 'becomes' theorems:
                 ,@becomes-theorems-to-export)
              state))))))

(deftransformation wrap-output
  (fn      ;must be a defined function
   wrapper
   )
  ((guard ':auto) ;TODO: Document
   (guard-hints ':auto) ;TODO: Document
   (theorem-disabled 'nil)
   (function-disabled ':auto)
   (new-name ':auto)
   (verify-guards ':auto)
   ))

;; See tests in wrap-output-tests.lisp.
