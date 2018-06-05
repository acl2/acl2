#|$ACL2s-Preamble$;
;; Author - Harsh Raju Chamarthi (harshrc)
(include-book ;; Newline to fool ACL2/cert.pl dependency scanner
 "../portcullis")
(begin-book t :ttags :all);$ACL2s-Preamble$|#


(in-package "CGEN")

(include-book "type")

(include-book "topological-sort")
(include-book "cgen-search" :ttags :all)
(include-book "acl2s-parameter")



;; The following 2 functions need to be revisited and rewritten if necessary
(defun let-binding->dep-graph-alst (vt-lst ans)
  "Walk down the var-term list vt-lst and add edges. 
   Build graph alist in ans"
  (if (endp vt-lst)
      ans
    (b* (((list var term) (car vt-lst))
         (fvars (all-vars term)));only non-buggy for terms
   
      (let-binding->dep-graph-alst 
       (cdr vt-lst)
       (cgen::union-entry-in-adj-list var fvars ans)))))

(defun get-ordered-alst (keys alst ans)
  (declare (xargs :guard (and (true-listp keys) (alistp ans) (alistp alst))))
  "accumulate entries of alist in ans in the order of keys"
  (if (endp keys)
    ans
    (let ((at (assoc-equal (car keys) alst)))
      (if at
        (get-ordered-alst (cdr keys) alst (append ans (list at)))
        (get-ordered-alst (cdr keys) alst ans)))))

(defun do-let*-ordering (vt-lst)
  (declare (xargs :guard (symbol-alistp vt-lst)
                  :mode :program))
  (b* ((vars (union-eq (all-vars1-lst (strip-cars vt-lst) nil)
                       (all-vars1-lst (strip-cdrs vt-lst) nil)))
       (dep-g (let-binding->dep-graph-alst vt-lst 
                                           (cgen::make-empty-adj-list vars)))
       (sorted-vars (cgen::topological-sort dep-g)))
    (get-ordered-alst (reverse sorted-vars) vt-lst nil)))
#||
(do-let*-ordering '((X3 '+)
                    (W1 (CONS W W2))
                    (X (CONS X1 X2))
                    (X2 (CONS X3 X4))
                    (W2 (CONS W4 X3))
                    (Z (CONS Y X3))
                    (Y (CONS X X3))
                    (W (CONS Z Y))) 
                  )
||#




(set-state-ok t)
(program)


;-- 2 utility functions by Matt, to get elided variable replaced term information --
(defun get-dest-elim-replaced-terms (elim-sequence)
  (if (endp elim-sequence)
    nil
    (let* ((elt (car elim-sequence))
           (rhs (nth 1 elt))
           (lhs (nth 2 elt)))
      (cons (list rhs lhs)
            (get-dest-elim-replaced-terms (cdr elim-sequence))))))


(defun collect-replaced-terms (hist ans)
  (declare (xargs :mode :program))
  (if (endp hist)
    ans
    (b* ((H (car hist))
         (ttree (acl2::access acl2::history-entry H :ttree))
         (proc (acl2::access acl2::history-entry H :processor))
         ;(- (cw "DEBUG: proc is ~x0~%" proc))
         )
      (cond ((eq proc 'acl2::generalize-clause)
;Generalize
             (let ((ans1 
                    (list-up-lists
                     (acl2::tagged-object 'acl2::terms ttree)
                     (acl2::tagged-object 'acl2::variables ttree))))
               (collect-replaced-terms 
                (cdr hist) (append ans1 ans))))
            ((eq proc 'acl2::eliminate-destructors-clause)
;Destructor elimination
             (let* ((elim-sequence 
                     (acl2::tagged-object 'acl2::elim-sequence ttree))
                    (ans1 (get-dest-elim-replaced-terms elim-sequence)))
               (collect-replaced-terms
                (cdr hist) (append ans1 ans))))
;Else (simplification and etc etc)
            (t (let* ((binding-lst 
                       (acl2::tagged-object 'acl2::binding-lst ttree))
;TODO: Modified! Show (convert-conspairs-to-listpairs binding-lst) = (listlis (strip-cars binding-lst) (strip-cdrs binding-lst))
                      (ans1 (list-up-lists (strip-cars binding-lst) (strip-cdrs binding-lst))))
                 (collect-replaced-terms
                  (cdr hist) (append ans1 ans))))))))




(defun cgen-search-clause (cl name 
                              ens hist 
                              elim-elided-var-map
                              cgen-state
                              vl ctx state)
   "helper function for test-checkpoint. It basically sets up 
   everything for the call to csearch."
  (declare (xargs :stobjs (state) :mode :program))
  (b* ((type-alist (get-acl2-type-alist-fn cl ens state))
       (vars (all-vars1-lst cl '()))
       
       ((mv hyps concl) (clause-mv-hyps-concl cl))
       ((mv hyps concl state) (if (and (consp cl) (null (cdr cl))
                                       (consp (car cl))
                                       (eq (caar cl) 'ACL2::IMPLIES))
; [2016-02-29 Mon] For the Preprocess/Goal cl, explicitly take care of the implies and lambda/let
                                  (partition-into-hyps-concl-and-preprocess (car cl) "cgen-search-clause" state)
                                (mv hyps concl state)))
;       (wrld (w state))
       (elided-var-map (append (collect-replaced-terms hist nil)
                               elim-elided-var-map))
       (- (cw? (verbose-stats-flag vl)
               "~|CEgen/Verbose: Search clause with elide-map ~x0. ~|" 
               elided-var-map))

       ;; Ordering is necessary to avoid errors in printing top-level cts

       (ord-elide-map (do-let*-ordering elided-var-map))
       (tau-interval-alist (tau-interval-alist-clause cl vars ens))
       ((mv erp cgen-state state)  (cgen-search-fn name hyps concl 
                                                   type-alist tau-interval-alist
                                                   ord-elide-map 
                                                   (eq (default-defun-mode (w state)) :program)
                                                   cgen-state
                                                   ctx state)))
    (mv erp cgen-state state)))


(defun all-functions-definedp-lst (fns wrld)
  "are all the functions used in fns executable?"
  (declare (xargs :verify-guards nil
                  :guard (and (symbol-listp fns)
                              (plist-worldp wrld))))
  (if (endp fns)
      T
    (and (acl2::logical-namep (car fns) wrld)
         (all-functions-definedp-lst (cdr fns) wrld))))


;; 21th March 2013
;; CHeck for multiple valued functions and functions having
;; stobjs in their arguments and return values.

(defun unsupported-fns (fns wrld)
  "gather functions that 
1. take stobjs as args
2. constrained (encapsulate) and no attachment"
  (if (endp fns)
      nil
    (let* ((fn (car fns))
           (constrainedp (acl2-getprop fn 'acl2::constrainedp wrld :default nil))
           (att (acl2-getprop fn 'acl2::attachment wrld :default nil)))
          
      (if (or (or-list (acl2::stobjs-in fn wrld))
              (and constrainedp
                   (null att)))
          (cons fn (unsupported-fns (cdr fns) wrld))
        (unsupported-fns (cdr fns) wrld)))))
  



; Catch restrictions, warn : skip cgen/testing
(defun cgen-exceptional-functions (terms vl wrld) ;clause is a list of terms
  "return (mv all-execp unsupportedp)"
  (declare (xargs :verify-guards nil
                  :guard (pseudo-term-listp terms)))
  (b* ((fns (all-functions-lst terms))
       (all-execp (all-functions-definedp-lst fns wrld))
       (- (cw? (and (not all-execp) (verbose-flag vl))
"~|CEgen/Note: Skipping testing completely, since not all functions in this conjecture are defined.~%"))
       (unsupportedp (consp (unsupported-fns fns wrld)))
       (- (cw? (and unsupportedp (verbose-flag vl))
"~|CEgen/Note: Skipping testing completely, since some functions in this conjecture either take stobj arguments or are constrained without an attachment.~%")))
    (mv all-execp unsupportedp)))
       
     

(defun not-equivalid-p (processor-hist)
  "proof has wandered into non-equi-valid path"
  (intersection-eq processor-hist
                   '(acl2::fertilize-clause
                     acl2::generalize-clause
                     acl2::eliminate-irrelevance-clause)))

(defun update-cgen-state-givens/callback (term ctx vl state)
  "update cgen-state fields user-supplied-term,top-vt-alist etc from test-checkpoint"
  (b* ((cgen-state (@ cgen-state))
       (cgen-state (cput top-ctx ctx))
       (cgen-state (cput user-supplied-term term))
       (cgen-state (cput displayed-goal term)) ;ASK: shud I prettify it?
; ACHTUNG - get-hyps only looks at outermost implies.
       ((mv hyp concl) (mv (get-hyp term) (get-concl term)))
       (hyps (if (eq hyp 't) '() (acl2::expand-assumptions-1 hyp)))
       (vars (vars-in-dependency-order hyps concl (w state)))
       (d-typ-al (dumb-type-alist-infer
                   (cons (cgen-dumb-negate-lit concl) hyps) vars 
                   vl (w state)))
       (cgen-state (cput top-vt-alist d-typ-al))
       (- (cw? (system-debug-flag vl)
               "~|CEgen/Sysdebug: update-gcs%-top-level : ~x0 dumb top vt-alist: ~x1 ~|"
               term d-typ-al)))
;   in 
    cgen-state))

(defconst *check-bad-generalizations-and-backtrack* nil)
        
;; The following function implements a callback function (computed hint)
;; which calls the counterexample generation testing code. Thus the
;; the so called "automated" combination of testing and theorem proving
;; is enabled naturally by the computed hints feature in the
;; engineering design of ACL2 theorem prover.
;; If somebody reads this comment, I would be very interested in any other
;; theorem-provers having a call-back mechanism in their implementation.
(defun acl2::test-checkpoint (id cl cl-list processor pspv hist ctx state)
  "?: This function is a callback called via an override hint +
backtrack no-op hint combination.  On SUBGOALS that are not
checkpoints it is a no-op. On checkpoints it calls the main
cgen/testing procedure. 

Note that this (observer) hint combination means that when this
callback function is called, that particular processor had a HIT and
resulted in one or more subgoals, each of which will fall on top of
the waterfall like in a Escher drawing.

RETURN either (mv t nil state) or (mv nil nil state) i.e as a hint it
is a no-op with the following exception.  If the processor is
generalize and a counterexample was found to the generalized subgoal,
then it returns (value '(:do-not '(acl2::generalize)
                                :no-thanks t))

"
;;  :sig ((symbol clause clause-list symbol pspv hist ctx state) -> (mv erp boolean state))


; PRECONDITION -
; INVARIANT - no new prove call is made during the computation of this
; function (this is very important, but now I can relax this invariant,
; with the introduction of post and pre functions at event level)
  ;; (acl2::with-timeout1 
  ;;  (acl2s-defaults :get subgoal-timeout)
   (b* (
;TODObug: test? defaults should be the one to be used
       (vl (acl2s-defaults :get verbosity-level))
       
       ((unless (and (f-boundp-global 'cgen-state state)
                     (cgen-state-p (@ cgen-state)))) 
        ;; Ignore contexts where cgen-state is not well-formed. TODO SHouldnt we give a message here at least for regression/testing?
        (prog2$
         (cw? (debug-flag vl)
              "~|CEgen/Debug: test-checkpoint -- cgen-state malformed; skip cgen/testing...~%")
         (value nil)))
       

       ((mv all-execp unsupportedp) 
        (cgen-exceptional-functions cl vl (w state)))
;27 June 2012 - Fixed bug, in CCG, some lemmas are non-executable, since they
;involve calling the very function being defined. We should avoid testing
;anything that is not executable.
       ((unless all-execp) (value nil))
; 21st March 2013 - catch stobj taking and constrained functions, skip testing.
       ((when unsupportedp) (value nil))
       (hist-len (len hist))
       (- (cw? (debug-flag vl)
               "test-checkpoint : id = ~x0 processor = ~x1 ctx = ~x2 hist-len = ~x3~|" 
               id processor ctx ;(acl2::prettyify-clause cl nil (w state)) 
               hist-len))
 
       ((unless (member-eq processor
                           '(acl2::preprocess-clause
                             ;;acl2::simplify-clause
                             acl2::settled-down-clause 
                             acl2::eliminate-destructors-clause
                             acl2::fertilize-clause
                             acl2::generalize-clause
                             acl2::eliminate-irrelevance-clause
                             acl2::push-clause)))  
; NOTE: I can also use (f-get-global 'checkpoint-processors state)
        (value nil));no-op
       
       (name (acl2::string-for-tilde-@-clause-id-phrase id))
       ((when (and (eq processor 'acl2::preprocess-clause) ;;[2016-02-26 Fri]
                   ;;ignore all preprocess except the first
                   (not (equal name "Goal"))))             
        (value nil));no-op
       (wrld (w state))
       (cgen-state (@ cgen-state))
       (pspv-user-supplied-term (acl2::access acl2::prove-spec-var 
                                              pspv :user-supplied-term))
       (- (cw? (debug-flag vl) "~| pspv-ust: ~x0 curr ust: ~x1 ctx:~x2 cgen-state.ctx:~x3~%" pspv-user-supplied-term (cget user-supplied-term) ctx (cget top-ctx)))

       ((unless (implies (and (not (eq (cget user-supplied-term) :undefined))
                              (not (eq (car (cget top-ctx)) :user-defined))) ;allow test?/prove
                         (equal ctx (cget top-ctx))))
        (prog2$ ;Invariant 
         (cw? (verbose-flag vl)
              "~|Cgen/Note: We encountered a new goal ctx ~x0, in the course of testing ctx ~x1. ~ 
Nested testing not allowed! Skipping testing of new goal...~%" 
              ctx
              (cget top-ctx))
         (value nil)))
       (user-supplied-term (cget user-supplied-term))
       ((unless (implies (not (eq user-supplied-term :undefined)) ;already set
                         (equal user-supplied-term pspv-user-supplied-term)))
        (prog2$ ;Invariant [2016-04-04 Mon] TODO: this only works for test?, not for thm/defthm
         (cw? (verbose-flag vl)
              "~|Cgen/Note: We encountered a new goal ~x0, in the course of testing ~x1. ~ 
Nested testing not allowed! Skipping testing of new goal...~%" 
              (acl2::prettyify-clause (list pspv-user-supplied-term) nil wrld)
              (acl2::prettyify-clause (list user-supplied-term) nil wrld))
         (value nil)))

       (cgen-state (if (eq (cget user-supplied-term) :undefined)
                       (update-cgen-state-givens/callback pspv-user-supplied-term ctx vl state)
                     cgen-state))
       
       
        
       (- (cw? (verbose-stats-flag vl)
               "~%~%~|Cgen/Note: @Checkpoint Subgoal-name:~x0 Processor:~x1~|" name processor))
       (ens (acl2::access acl2::rewrite-constant
                          (acl2::access 
                           acl2::prove-spec-var pspv :rewrite-constant)
                          :current-enabled-structure))
       
  ;     (abo? (not-equi-valid-p (cget processor-hist))) ;all bets off
       ((mv & cgen-state state) (cgen-search-clause cl name
                                                    ens hist 
                                                    ;;abo? processor
                                                    '() ;deprecated arg for manual elim elided var map
                                                    cgen-state
                                                    vl ctx state))
       
; Assumption Jan 6th 2013 (check with Matt)
; We only arrive here with processor P, if it was a hit i.e if P
; is fertilize-clause then cross-fertilization was successful and
; potentially the generalization was unsound.
       (processor-hist (cons processor (cget processor-hist)))
       (cgen-state (cput processor-hist processor-hist))
       (abo? (not-equivalid-p processor-hist))
       (- (cw? (and (debug-flag vl) abo?)
               "~|Cgen/Debug: Top-level cts/wts cannot be constructed now ... ~x0 in ~x1~%" name ctx))

       (state (f-put-global 'cgen-state cgen-state state)) ;put it back in globals
       (gcs% (cget gcs))
       )
   
;  in  
   (if (or (cget stopping-condition-p)
           (and (> (access gcs% cts) 0)
                (or abo? (eq processor 'acl2::push-clause))))
; jan 6th 2013
; why bother continuing with a generalized (possibly unsound) subgoal
; or an induction when we already have found a counterexample.
; simply abort! (ASK: Pete)
       (mv t nil state)

; Check for false generalizations. TODO also do the same for
; cross-fertilization and eliminate-irrelevance if its worth the trouble
     (if (and *check-bad-generalizations-and-backtrack*
              (equal processor 'acl2::generalize-clause))
         ;NOTE: this pspv (and hist) is for the cl not for cl-list, so there
         ;might be some inconsistency or wierdness here
         (b* ((gen-cl (car cl-list))
              (type-alist (get-acl2-type-alist gen-cl))
              ((mv H C) (cgen::clause-mv-hyps-concl gen-cl))
              (vars (vars-in-dependency-order H C wrld))

              (vt-alist (make-weakest-type-alist vars))
              ;; (term (if (null H)
              ;;           C
              ;;           `(implies (and ,@H) ,C)))

; the above is not really a term, but almost, we can assume AND is a function.
; hopefully it will not affect any computation based on it, certainly will
; not affect all-vars. CHECK! 20th March 2013
              (tau-interval-alist (tau-interval-alist-clause gen-cl vars))
              (temp-cgen-state (list (cons 'PARAMS (cget params))
                                     (cons 'GCS *initial-gcs%*)
                                     (cons 'TOP-CTX ctx)
                                     (cons 'TOP-VT-ALIST vt-alist)))
              ((mv erp res state) (cgen-search-local name H C 
                                                     type-alist tau-interval-alist 
                                                     NIL 
                                                     *initial-test-outcomes%* 
; we dont care about witnesses and the start time and do no accumulation.
                                                     *initial-gcs%*
                                                     temp-cgen-state
                                                     ctx state))
              ((when erp) (value nil))
              ((list & test-outcomes% &) res)
              (num-cts-found (access test-outcomes% |#cts|)))
          (value (if (> num-cts-found 0)
                     (progn$ 
                      (cw? (verbose-stats-flag vl) "~| Generalized subgoal: ~x0~|" 
                           (acl2::prettyify-clause gen-cl nil (w state)))
                      (cw? (verbose-stats-flag vl)
                           "~| Counterexample found: ~x0 ~|"
                           (car (access test-outcomes% cts)))
                      (cw? (verbose-flag vl) "~| Bad generalization! Backtracking...~|")
                      '(:do-not '(acl2::generalize)
                                :no-thanks t))
                   nil)))
;ignore errors in cts search function
       (value nil))))
   ;; (prog2$
   ;;  (cw? (normal-output-flag (acl2s-defaults :get verbosity-level))
   ;;       "~| Subgoal counterexample search TIMED OUT!~%")
   ;;  (value nil))
   )




;;; add no-op override hints that test each checkpoint.  The reason
;;; why we need backtrack hint is not that we need clause-list
;;; (children goals of clause), but because we need to do testing only
;;; on checkpoints, and only backtrack hints have access to processor,
;;; if this were not the case, we could have used ":no-op
;;; '(test-each-goal ...)" as an override hint which has no effect but
;;; to test each goal.  Another reason is that because computed-hints
;;; with :COMPUTED-HINT-REPLACEMENT t is not additive like
;;; override-hints it can cause a hint to be not selected otherwise.
(defmacro acl2s::enable-acl2s-random-testing ()
;; this has to be a makevent because enable-acl2s-random-testing is the
;; expansion result of the make-event in set-acl2s-random-testing-enabled
`(make-event  
  '(progn 
     (acl2::add-override-hints!
      '((list* :backtrack 
;take parent pspv and hist, not the ones returned by clause-processor

               `(acl2::test-checkpoint acl2::id 
                                       acl2::clause
                                       acl2::clause-list
                                       acl2::processor
;TODO:ask Matt about sending parent pspv and hist
                                       ',acl2::pspv 
                                       ',acl2::hist
                                       acl2::ctx
                                       state
                                       )

             ;; `(mv-let (erp tval state)
             ;;          (trans-eval
             ;;           `(test-each-checkpoint ',acl2::id 
             ;;                                  ',acl2::clause 
             ;;                                  ',acl2::processor 
             ;;                                  ',',acl2::pspv 
             ;;                                  ',',acl2::hist state
             ;;                                  ts$)
             ;;           'acl2s-testing ; ctx
             ;;           state
             ;;           t ; aok
             ;;           )
             ;;          (declare (ignorable erp))
             ;;          (mv (cadr tval) (caddr tval) state))

;`(test-each-checkpoint acl2::id acl2::clause acl2::processor ',acl2::pspv ',acl2::hist state)
             acl2::keyword-alist)))
     )))

(defmacro acl2s::disable-acl2s-random-testing ()
`(make-event  
     '(progn
        (acl2::remove-override-hints!
         '((list* :backtrack 
                  `(acl2::test-checkpoint acl2::id 
                                          acl2::clause 
                                          acl2::clause-list
                                          acl2::processor 
                                          ',acl2::pspv 
                                          ',acl2::hist
                                          acl2::ctx
                                          state
                                          )
;take parent pspv and hist, not the ones returned by clause-processor
                 ;; `(mv-let (erp tval state)
                 ;;      (trans-eval
                 ;;       `(test-each-checkpoint ',acl2::id 
                 ;;                              ',acl2::clause 
                 ;;                              ',acl2::processor 
                 ;;                              ',',acl2::pspv 
                 ;;                              ',',acl2::hist state
                 ;;                              ts$)
                 ;;       'acl2s-testing ; ctx
                 ;;       state
                 ;;       t ; aok
                 ;;       )
                 ;;      (declare (ignorable erp))
                 ;;      (mv (cadr tval) (caddr tval) state))
;`(test-each-checkpoint acl2::id acl2::clause acl2::processor ',acl2::pspv ',acl2::hist state)
                acl2::keyword-alist)))
        )))


;Dont print the "Thanks" message:
(defmacro acl2::dont-print-thanks-message-override-hint ()
`(make-event  
  '(acl2::add-override-hints 
    '((cond ((or (null acl2::keyword-alist)
                 (assoc-keyword :no-thanks acl2::keyword-alist))
             acl2::keyword-alist)
            (t
             (append '(:no-thanks t) acl2::keyword-alist)))))))
   




;;; event pre and post functions
(logic)
(defun init-cgen-state/event (params start-time top-ctx)
  (declare (xargs :guard (and (cgen-params-p params)
                              (rationalp start-time)
                              (allowed-cgen-event-ctx-p top-ctx))))
  (list (cons 'PARAMS params)
        (cons 'USER-SUPPLIED-TERM :undefined)
        (cons 'DISPLAYED-GOAL :undefined)
        (cons 'START-TIME start-time)
        (cons 'GCS *initial-gcs%*)
        (cons 'TOP-CTX top-ctx)))

(defun compute-event-ctx (ctx-form)
  (cond ((atom ctx-form) ctx-form)
        ((mem-tree 'ACL2::THM ctx-form) 'ACL2::THM)
        ((mem-tree 'ACL2::DEFTHM ctx-form) 'ACL2::DEFTHM)
        ((mem-tree 'ACL2::VERIFY-GUARDS ctx-form) 'ACL2::VERIFY-GUARDS)
        ((mem-tree 'ACL2::DEFUN-CTX ctx-form) 'ACL2::DEFUNS)
        (t ctx-form)))



; The following functions are used to initialize and finalize
; cgen-state for cgen/testing support in forms (that are wrapped in
; with-ctx-summarized) such as thm, defthm, verify-guards, defun that
; call the prover. If testing-enabled is T, then the callback
; (computed hint) function test-checkpoint calls tests the conjecture
; clause at each checkpoint. For test-checkpoint to function sanely,
; we need to appropriately setup globals used by it (cgen-state) and
; appropriately communicate the result/summary of its computation
; back to the user and cleanup any globals.








; [2014-05-03 Sat] event-stack stores in its entries, either a keyword
; :ignore-cgen or the ctx of the current event/form. The former
; indicates that cgen has ignored this event, the latter that cgen is
; processing the event as its main top-level form which provides the
; conjecture under test. This is crucial to match the actions taken in
; initialize-event with actions in finalize-event. At the top-level,
; this stack better be empty (how to ensure this invariant?).
#|
(defun initialize-event-user-cgen/old (ctx-form body state)
  (declare (xargs :stobjs state
                  :mode :program
                  :verify-guards nil))
  (declare (ignorable body)) 

  (b* (((unless (and (f-boundp-global 'cgen-state state)
                     (f-boundp-global 'event-stack state)))
        state) ;ignore
       (vl (acl2s-defaults :get verbosity-level))
  
; Always push the event into the event-stack for matching with
; finalize. The default is to push :ignore-cgen, which is overriden
; later, if cgen takes this event to give the conjecture under test.
       (event-stack (@ event-stack))
       (event-stack~ (cons :ignore-cgen event-stack)) ;ensure this keyword is never a event ctx
       (state (f-put-global 'event-stack event-stack~ state))
       (ctx (compute-event-ctx ctx-form))
       ((unless (allowed-cgen-event-ctx-p ctx))
        (prog2$
         (cw? (> vl 8) 
              "~|CEgen/Warning: initialize-event -- ctx ~x0 ignored...~%" ctx)
         state))
       
       (cgen-state (@ cgen-state))
       ;TODO: Perhaps just flush cgen-state here. Reason: currently allowed ctx
       ; are not usually nested: i.e Why would someone call thm inside a
       ; thm?. But I am not convinced...
       ((unless (null cgen-state))
        (prog2$
         (cw? (debug-flag vl)
              "~|CEgen/Warning: initialize-event -- nested event ignored...~%")
         state))
       
       ((mv start state) (acl2::read-run-time state))
       (cgen-state (init-cgen-state/event (acl2s::acl2s-defaults-alist) start ctx))
       (- (cw? (debug-flag vl)
              "~|CEgen/Note: CGEN-STATE initialized for ctx ~x0~%" ctx))
       (state (f-put-global 'cgen-state cgen-state state))
       (event-stack~ (cons ctx event-stack)) ;overwrite/update 
       (state (f-put-global 'event-stack event-stack~ state)))
    state))
|#

(defstub print-testing-summary (* * state) => (mv * * state))

#|
(defun finalize-event-user-cgen/old (ctx-form body state)
  (declare (xargs :mode :program ;print-testing-summary is program-mode
                  :verify-guards nil :stobjs state))
  (declare (ignorable ctx-form body))
  (b* (((unless (and (f-boundp-global 'cgen-state state)
                     (f-boundp-global 'event-stack state)))
        state) ;ignore
       (vl (acl2s-defaults :get verbosity-level)) ;todo replace with the one from cgen-state
  
; Always pop the ctx from the event-stack (matching with initialize).
       (event-stack (@ event-stack))
       (event-stack~ (cdr event-stack))
       (state (f-put-global 'event-stack event-stack~ state))

       
       ((when (eq (car event-stack) :ignore-cgen))
        (prog2$
         (cw? (> vl 8)
              "~|CEgen/Warning: finalize-event -- matching ignore...~%")
         state))

       ;; symmetric to initialize-event-user-cgen, update end time
       ((mv end state) (acl2::read-run-time state))
       (cgen-state (@ cgen-state))
; removed assert here for valid cgen-state, as there are many events that occur that have nothing to do with testing!
       (cgen-state (cput end-time end))
       (state (f-put-global 'cgen-state cgen-state state))
       (gcs% (cget gcs))

       (ctx (compute-event-ctx ctx-form))
       (print-summary-p (and (cget print-cgen-summary) 
                             (> (access gcs% cts) 0)
; dont print at the end of defun/defuns events (any help to CCG by cgen is invisible) TODO
                             (member-eq ctx '(ACL2::THM ACL2::DEFTHM ACL2::VERIFY-GUARDS))))
       
       (- (cw? (system-debug-flag vl) "~|CEgen/SysDebug: Exiting event with gcs% : ~x0. ~ ctx: ~x1 print-cgen-summ : ~x2 ~%" gcs% ctx (cget print-cgen-summary)))
                        
       ((mv & & state) ;ignore error in print function
        (if print-summary-p
            (print-testing-summary cgen-state ctx state) ;state is important also because we call trans-eval inside this fun
          (value nil)))
       (- (cw? (debug-flag vl)
              "~|CEgen/Note: CGEN-STATE finalized for ctx ~x0~%" ctx))
       (state (f-put-global 'cgen-state nil state))) ;clean up cgen state
    state))
|#          
      

;; [2015-02-04 Wed] Simplify the pre/post event hooks used by Cgen.
;; Assume that no event of concern to use will be nested. i.e thm, defthm, verify-guards, test? will never be nested.
(defun initialize-event-user-cgen (ctx-form body state)
  (declare (xargs :stobjs state :mode :program :verify-guards nil))
  (declare (ignorable body)) 
; As soon as it sees a testable/cgen-able event it resets/inits the two globals:
; cgen-state using init-cgen-state/event and event-ctx with ctx-form
  (b* (((unless (and (f-boundp-global 'cgen-state state)
                     (f-boundp-global 'event-ctx state)))
        state) ;ignore
       (vl (acl2s-defaults :get verbosity-level))
       (ctx (compute-event-ctx ctx-form))
       ((unless (allowed-cgen-event-ctx-p ctx))
        (prog2$
         (cw? (> vl 8) "~|CEgen/Warning: initialize-event -- ctx ~x0 ignored...~%" ctx)
         state))
              
       ((mv start state) (acl2::read-run-time state))
       (cgen-state (init-cgen-state/event (acl2s::acl2s-defaults-alist) start ctx))
       (- (cw? (debug-flag vl) "~|CEgen/Note: CGEN-STATE initialized for ~x0~%" ctx-form))
       (state (f-put-global 'cgen-state cgen-state state))
       (state (f-put-global 'event-ctx ctx-form state)))
    state))
       
(defun finalize-event-user-cgen (ctx-form body state)
  (declare (xargs :mode :program ;print-testing-summary is program-mode
                  :verify-guards nil :stobjs state))
  (declare (ignorable body))
; If event-ctx global matches ctx-form, we know (sure??) this is the top cgen event and do the following. (if not matched, we ignore/skip).
; We reset event-ctx to nil.
; Finalize cgen-state with end-time, print-summary and reset cgen-state to nil.
  (b* (((unless (and (f-boundp-global 'cgen-state state)
                     (f-boundp-global 'event-ctx state)))
        state) ;ignore
       (vl (acl2s-defaults :get verbosity-level)) ;todo replace with the one from cgen-state
       (event-ctx (@ event-ctx))
       ((unless (equal event-ctx ctx-form)) ;check if it is the matching finalize
        (prog2$
         (cw? (> vl 8) "~|CEgen/Warning: finalize-event -- ignore non-top event...~%")
         state))
       
       (state (f-put-global 'event-ctx nil state)) ;reset/clean

       ;; symmetric to initialize-event-user-cgen, update end time
       ((mv end state) (acl2::read-run-time state))
       (cgen-state (@ cgen-state))
; removed assert here for valid cgen-state, as there are many events that occur that have nothing to do with testing!
       (cgen-state (cput end-time end))
       (state (f-put-global 'cgen-state cgen-state state))
       (gcs% (cget gcs))

       (ctx (compute-event-ctx ctx-form))
       (print-summary-p (and (cget print-cgen-summary) 
                             ;(> (access gcs% cts) 0) ;commented out to collect vacuous stats
; dont print at the end of defun/defuns events (any help to CCG by cgen is invisible) TODO
                             (allowed-cgen-event-ctx-p ctx)))

       
       (- (cw? (system-debug-flag vl) "~|CEgen/SysDebug: Exiting event with gcs% : ~x0. ~ ctx: ~x1 print-cgen-summ : ~x2 ~%" gcs% ctx (cget print-cgen-summary)))
                        
       ((mv & & state) ;ignore error in print function
        (if print-summary-p
            (print-testing-summary cgen-state ctx state) ;state is important also because we call trans-eval inside this fun
          (value nil)))
       (- (cw? (debug-flag vl)
              "~|CEgen/Note: CGEN-STATE finalized for ctx ~x0~%" ctx))
       (state (f-put-global 'cgen-state nil state))) ;clean up cgen state
    state))



(defun initialize-event-user-cgen-gv (ctx body state)
  (declare (xargs :mode :program
                  :stobjs state
                  :guard T))
  (ec-call (initialize-event-user-cgen ctx body state)))

(defun finalize-event-user-cgen-gv (ctx body state)
  (declare (xargs :mode :program
                  :guard T
                  :stobjs state))
  (ec-call (finalize-event-user-cgen ctx body state)))



;BEWARE/ACHTUNG: CGen only works through events and its API. Otherwise the
;state globals might be polluted and we are hosed. I saw this happen when using
;brr which does not end gracefully (no finalize-event is called).
; Actually even simple interrupts, leave the event-stack unfinalized, and hence
; we might need to manually flush these globals.

; [2015-02-04 Wed] After the above simplification (disallowing nested
; cgen-relevant events), the above note is mostly irrelevant.

(defmacro flush ()
;; ":Doc-Section cgen
  
;;   Flush/Reset the transient Cgen state globals to sane values.~/~/

;;   ~bv[]
;;    Usage (at the top-level):
;;      (cgen::flush)
;;    ~ev[]
;; "
;flush any transient/polluted globals due to interrupts
  `(er-progn 
    (assign cgen::cgen-state nil)
    (assign cgen::event-ctx nil)
    (value nil)))
