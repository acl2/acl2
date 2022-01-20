; A more compositional version of the unrolling lifter
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; A more compositional version of the unrolling lifter (instead of building a
;; complex symbolic state to start with, you constrain the variable S to be a
;; state that is poised to invoke the program).  See tests in
;; ../examples/axe/compositional-test.lisp.

;; Unlike in other variants of the lifter, here the state var represents the
;; state *before* the invoke instruction is executed (so arguments are on the
;; stack, not in locals).

;; Methods are inlined except those that have already been lifted separately.

;; This version takes no :output-indicator because the result of the lifting
;; process represents the effect of the code on the entire state.

;; TODO: Abstract out more state components (not just the return value)

;;TODO: Consider adding an :unroll option to lift-java-code instead of
;;having this separate tool?

;; TODO: Add support for :smart and :split branch handling, like unroll-java-code has.

;; TODO: Add support for chunked execution, like unroll-java-code has.


(include-book "lifter-utilities2")
(include-book "kestrel/typed-lists-light/map-strip-cars" :dir :system)
(include-book "kestrel/utilities/doc" :dir :system)
(include-book "kestrel/utilities/unify" :dir :system)
(include-book "unroll-java-code") ;for unroll-java-code-rules
(include-book "../dag-to-term-with-lets")

;; Used by Axe
(defthm natp-of-+
  (implies (and (natp x)
                (natp y))
           (natp (+ x y))))

(in-theory (disable jvm::typep))
;(defopeners FIRST-NON-MEMBER)

(defthm first-non-member-opener
  (implies (syntaxp (quotep items))
           (equal (FIRST-NON-MEMBER ITEMS ITEMS-TO-EXCLUDE)
                  (IF (ATOM ITEMS)
                      NIL
                      (IF (NOT (MEMBER-EQUAL (CAR ITEMS)
                                             ITEMS-TO-EXCLUDE))
                          (CAR ITEMS)
                          (FIRST-NON-MEMBER (CDR ITEMS)
                                            ITEMS-TO-EXCLUDE))))))

(defthm invoke-static-initializer-for-class-of-myif
  (equal (jvm::invoke-static-initializer-for-class initialized-classes th s (myif test class1 class2))
         (myif test
               (jvm::invoke-static-initializer-for-class initialized-classes th s class1)
               (jvm::invoke-static-initializer-for-class initialized-classes th s class2)))
  :hints (("Goal" :in-theory (enable myif))))

(defthm myif-of-member-equal
  (equal (myif (member-equal a x) tp ep)
         (myif (memberp a x) tp ep))
  :hints (("Goal" :in-theory (enable myif member-equal-becomes-memberp))))

(defthm not-equal-of-call-stack-size-impossible
  (implies (and (syntaxp (quotep k))
                (not (natp k)))
           (not (equal k (jvm::call-stack-size x)))))

;; This is a hack to make sure we track the fact that exceptions/errors were
;; ignored.  These get included as hyps in generated theorems and should be
;; contagious because there is no way to get rid of them.
(defstub no-exceptions-occur () t)
(defstub no-errors-occur () t)

;; (defun make-locals-term (th state-term)
;;   `(jvm::locals (jvm::thread-top-frame ,th ,state-term)))


;TODO: How to remove this skip-proofs?
(skip-proofs
 (defthm run-until-return-from-stack-height-lemma-for-invoke
   (implies (and (<= sh (stack-height s)) ;todo: prevent loops
                 (member-equal (jvm::op-code (jvm::current-inst (th) s)) *invoke-opcodes*)
                 (natp sh)
                 )
            (equal (run-until-return-from-stack-height sh (jvm::step (th) s))
                   ;; todo: consider using run-until-return here
                   ;; This needs to match the theorem proved for the called method when we (previously) lifted it:
                   (run-until-return-from-stack-height sh (run-until-return-from-stack-height (+ 1 (stack-height s)) (jvm::step (th) s)))))))

;fixme: the axe-rule for string-append looped!  now fixed since we expand return-last?
(defthm string-append-opener
  (equal (string-append str1 str2)
         (coerce (binary-append (coerce str1 'list)
                                (coerce str2 'list))
                 'string)))

;; To these rules we add one more, generated on the fly, allowing us to open
;; STEP when the instruction invokes a method that we have not yet lifted.
(defun compositional-symbolic-execution-rules ()
  (append '(jvm::step-always-open ; jvm::step is replaced by JVM::STEP-ALWAYS-OPEN when we decide to open it
            step-opener-for-non-invokes ;open step, but only for non-invoke instructions
            ;some of these are not inherently compositional:
            run-until-return
            run-until-return-from-stack-height-base-axe
            run-until-return-from-stack-height-opener-axe ;introduces a call of step (this is not the fast version)
            run-until-return-from-stack-height-lemma-for-invoke
            member-equal-of-nil
            )
          ;; Handle Ifs smartly (todo: make this an option?):
          (step-state-with-pc-and-call-stack-height-rules)
          '(run-until-return-from-stack-height-of-myif-alt-axe ;note the -alt
            )))

(defun unroll-java-code2-rules ()
  (set-difference-eq
   (append (unroll-java-code-rules) ;todo: contains step-opener (remove that?)
           ; todo: why are these not part of unroll-java-code-rules?
           '(myif-of-member-equal ;turns the member-equal into a memberp
             jvm::acl2-numberp-of-call-stack-size
             natp-of-call-stack-size
             equal-constant-+-alt
             natp-of-+
             not-equal-of-call-stack-size-impossible
             string-append-opener ;for method designators
             ))
   ;; Turn these rules off:
   '(jvm::step-opener
    ; jvm::step ;don't open step all the time
   ;  run-until-return-from-stack-height-opener-fast ;this bypasses step, which we use to trigger theorems, so we disable it
     ;run-until-return-from-stack-height-of-myif-axe ;todo think about this
;     run-until-return-from-stack-height-of-myif-axe-alt ;todo think about this
     ;; can't disable these because we need to execute the first invoke:
     ;; jvm::execute-invokestatic
     ;; jvm::execute-invokevirtual
     ;; jvm::execute-invokespecial
     ;; jvm::execute-invokeinterface
     )))

;;
;; extract out the state components into separate functions
;;

;; TODO: Use better names than x0, x1, etc for the formals of the extracted function here (e.g., param-names)

(mutual-recursion
 ;; Returns (mv new-term term-var-alist var-count)
 (defun abstract-state-components-in-term (term term-var-alist var-count)
   (declare (xargs :guard (and (pseudo-termp term)
                               (alistp term-var-alist)
                               (natp var-count))
                   :verify-guards nil ;done below
                   ))
   (if (variablep term)
       (mv term term-var-alist var-count)
     (let ((fn (ffn-symb term)))
       (if (eq 'quote fn)
           (mv term term-var-alist var-count)
         (if (member-eq fn '(get-field
                             jvm::top-operand
                             jvm::top-long
                             )) ;todo: what else?  get-static-field?
             ;; term is a state component
             (if (assoc-equal term term-var-alist)
                 ;;already bound, so just put in its variable:
                 (mv (lookup-equal term term-var-alist) term-var-alist var-count)
               ;; this state component has not yet been encountered:
               (let* ((new-var (pack$ 'x var-count)))
                 (mv new-var (acons term new-var term-var-alist) (+ 1 var-count))))
           ;; normal function:
           (b* (((mv new-args term-var-alist var-count)
                 (abstract-state-components-in-terms (fargs term) term-var-alist var-count)))
             (mv `(,fn ,@new-args) term-var-alist var-count)))))))

 ;; Returns (mv new-terms term-var-alist var-count)
 (defun abstract-state-components-in-terms (terms term-var-alist var-count)
   (declare (xargs :guard (and (pseudo-term-listp terms)
                               (alistp term-var-alist)
                               (natp var-count))))
   (if (endp terms)
       (mv nil term-var-alist var-count)
     (mv-let (new-term term-var-alist var-count)
       (abstract-state-components-in-term (first terms) term-var-alist var-count)
       (mv-let (new-terms term-var-alist var-count)
         (abstract-state-components-in-terms (rest terms) term-var-alist var-count)
         (mv (cons new-term new-terms) term-var-alist var-count))))))

(make-flag abstract-state-components-in-term)

(defthm-flag-abstract-state-components-in-term
  (defthm natp-of-mv-nth-2-of-abstract-state-components-in-term
    (implies (natp var-count)
             (natp (mv-nth 2 (abstract-state-components-in-term term term-var-alist var-count))))
    :flag abstract-state-components-in-term)
  (defthm natp-of-mv-nth-2-of-abstract-state-components-in-terms
    (implies (natp var-count)
             (natp (mv-nth 2 (abstract-state-components-in-terms terms term-var-alist var-count))))
    :flag abstract-state-components-in-terms)
  :hints (("Goal" :expand ((abstract-state-components-in-term term term-var-alist var-count)))))

(defthm-flag-abstract-state-components-in-term
  (defthm alist-of-mv-nth-1-of-abstract-state-components-in-term
    (implies (alistp term-var-alist)
             (alistp (mv-nth 1 (abstract-state-components-in-term term term-var-alist var-count))))
    :flag abstract-state-components-in-term)
  (defthm alist-of-mv-nth-1-of-abstract-state-components-in-terms
    (implies (alistp term-var-alist)
             (alistp (mv-nth 1 (abstract-state-components-in-terms terms term-var-alist var-count))))
    :flag abstract-state-components-in-terms)
  :hints (("Goal" :expand ((abstract-state-components-in-term term term-var-alist var-count)))))

(verify-guards abstract-state-components-in-terms)

;; Make a function whose body is TERM except that subterms of term that are JVM
;; state components have been abstracted into variables that are passed in as
;; arguments of the defun. Returns (mv new-defun call) where CALL is a call of
;; NEW-DEFUN that is equal to TERM.
;; TODO: We could actually have this prove the equality...
(defun make-defun-abstracting-state-components (fn term)
  (declare (xargs :guard (pseudo-termp term)))
  (b* (( ;; Walk through term identifying state components and binding them to vars
        (mv new-term term-var-alist &)
        (abstract-state-components-in-term term nil 0))
       (state-components (strip-cars term-var-alist))
       (vars (strip-cdrs term-var-alist)) ;todo: make the order here more predictable!
       ;; We probably want the function disabled, or what's the point of extracting it?
       (new-defun `(defund ,fn ,vars
                     (declare (xargs :normalize nil)) ;seems crucial in some cases
                     ,new-term))
       (call `(,fn ,@state-components)))
    (mv new-defun call)))

;; ; test:
;; (make-defun-abstracting-state-components
;;  'foo
;;  '(BVIF '1
;;         (BOOLOR (SBVLT '32
;;                        (JVM::TOP-OPERAND (JVM::STACK (JVM::thread-top-frame (th) S0)))
;;                        '48)
;;                 (SBVLT '32
;;                        '57
;;                        (JVM::TOP-OPERAND (JVM::STACK (JVM::thread-top-frame (th) S0)))))
;;         '0
;;         '1))

(defttag invariant-risk)
(set-register-invariant-risk nil) ;potentially dangerous but needed for execution speed

;; Converts a DAG to an equivalent term, where the meaning of non-built-in
;; functions mentioned in the dag comes from WRLD.  Avoids blowup if the term
;; would be huge.
;; TODO: Compare to dag-to-term-limited.
(defun dag-to-term-limited2 (dag
                             max-term-size     ;nil means no limit
                             use-lets-in-terms ;boolean
                             wrld)
  (declare (xargs :guard (and (or (and (pseudo-dagp dag)
                                       (< (len dag) 2147483647))
                                  (myquotep dag))
                              (or (null max-term-size)
                                  (natp max-term-size))
                              (booleanp use-lets-in-terms)
                              (plist-worldp wrld))
                  :guard-hints (("Goal" :in-theory (enable CAR-OF-CAR-WHEN-PSEUDO-DAGP-CHEAP)))))
  (if (quotep dag)
      dag
    (if (not max-term-size) ;no limit = always make a term
        ;; todo: only print the message if an embedded DAG would normally have been used?
        (if use-lets-in-terms
            (prog2$ (cw "Converting DAG to a term (without an embedded DAG) since max-term-size is nil.  Using lets for compactness.~%")
                    (dag-to-term-with-lets dag))
          (prog2$ (cw "Converting DAG to a term (without an embedded DAG) since max-term-size is nil.  Term size will be ~x0.~%" (dag-size-fast dag))
                  (dag-to-term dag)))
      ;; Max term size is a natural number:
      (if (dag-or-quotep-size-less-thanp dag max-term-size)
          (dag-to-term dag) ;todo: respect use-lets-in-terms here as well?
        ;; term would be too big, so use an embedded dag:
        (embed-dag-in-term dag wrld)))))

;; Returns (mv erp fn-body supporting-events state-component-defun-names)
(defun make-unroll-java-code2-fn-result (result-dag fn abstract-state-components wrld)
  (if (not abstract-state-components)
      (mv nil ;no error
          (dag-to-term-limited2 result-dag
                                    1000 ;todo: pass in
                                    nil  ;todo
                                    wrld)
          nil
          nil)
  ;; Result-term should be over the single variable S:
  (b* ((result-term (dag-to-term result-dag)) ;TODO: watch for explosion -- don't do this conversion
       ;; Try to extract interesting pieces of this into separate functions.
       ;; For now, we just do the return value. TODO: Add support for fields
       ;; and static fields that get changed. TODO: Suppress the rv abstraction for void functions.
       ;; TODO: Add support for pushing a :long result:
       ((mv matchp unify-subst)
        (unify-term result-term '(jvm::make-state
                                  (jvm::bind
                                   (th)
                                   (jvm::push-frame
                                     (jvm::make-frame :pc
                                                      :locals
                                                      :new-stack
                                                      :locked-object
                                                      :method-info
                                                      :method-designator)
                                     :stack)
                                   :thread-table)
                                  :heap
                                  :class-table
                                  :heapref-table
                                  :monitor-table
                                  :static-field-map
                                  :initialized-classes
                                  :uninitialized-classes
                                  :intern-table)))
       ((when (not matchp))
        ;; TODO: Handle ifs, perhaps by making a version of matching that can deal with IFs.
        (mv t (er hard? 'unroll-java-code2-fn "Result has an unexpected form: ~x0." result-term) nil nil))
       (stack-term (lookup-eq :new-stack unify-subst))
       ;; TODO: For these, look at the return type too:
       ;; Check whether a 1-slot value has been pushed:
       ((mv non-long-rv-presentp non-long-rv-unify-subst)
        (unify-term stack-term '(jvm::push-operand :rv :rest-stack)))
       ;; Check whether a 2-slot value has been pushed:
       ((mv long-rv-presentp long-rv-unify-subst)
        (unify-term stack-term '(jvm::push-long :rv :rest-stack)))
       (rv-presentp (or non-long-rv-presentp
                        long-rv-presentp))
       ;; may be nil:
       (rv-term (lookup-eq :rv (if non-long-rv-presentp
                                   non-long-rv-unify-subst
                                 long-rv-unify-subst))))
    (if (not rv-presentp)
        (mv nil ;no error
            result-term nil nil)
      ;; There is a return value subterm to abstract:
      (mv-let (new-defun call)
        (make-defun-abstracting-state-components (pack$ fn '-result) rv-term)
        (mv nil ;no error
            (replace-in-term result-term (acons rv-term ;; I guess this replaces any other matches of the RV term too.  okay?  would be better to use the fact that the state matched the pattern above...
                                                call
                                                nil))
            (list new-defun)
            (list (cadr new-defun))))))))

;; Returns (mv erp event state).
(defun unroll-java-code2-fn (fn
                             method-designator-string
                             array-length-alist ;TODO: perhaps we should also support an alist whose keys are local slots, in case the slots don't have names (no debugging info in the class file)
                             user-assumptions
                             classes-to-assume-initialized
                             classes-to-assume-uninitialized
                             ignore-exceptions
                             ignore-errors
                             extra-rules
                             remove-rules
                             rule-alists
                             monitor
                             prove-with-acl2
                             print
                             abstract-state-components
                             prune-branches
                             call-stp
                             param-names
                             extra-proof-rules ;for proving the result with acl2
                             print-interval
                             steps
                             whole-form
                             state
                            )
  (declare (xargs :stobjs (state)
                  :mode :program
                  :guard (and (symbolp fn)
                              (stringp method-designator-string)
                              ;;todo: check array-length-alist
                              (or (eq classes-to-assume-initialized :all)
                                  (jvm::all-class-namesp classes-to-assume-initialized))
                              (or (eq classes-to-assume-uninitialized :all)
                                  (jvm::all-class-namesp classes-to-assume-uninitialized))
                              (booleanp ignore-exceptions)
                              (booleanp ignore-errors)
                              (symbol-listp extra-rules)
                              (symbol-listp remove-rules)
                              (all-rule-alistp rule-alists)
                              (symbol-listp monitor)
                              (booleanp prove-with-acl2)
                              ;; print
                              (booleanp abstract-state-components)
                              (booleanp prune-branches)
                              (or (member-eq call-stp '(t nil))
                                  (natp call-stp))
                              (symbol-listp param-names)
                              (or (natp steps)
                                  (eq :auto steps)))))
  (b* (((when (command-is-redundantp whole-form state))
        (mv nil '(value-triple :invisible) state))
       (- (cw "(Unrolling ~x0:~%" method-designator-string))
       (state-var 's0)
       (method-class (extract-method-class method-designator-string))
       (method-name (extract-method-name method-designator-string))
       (method-descriptor (extract-method-descriptor method-designator-string)) ;todo: should this be called a descriptor?
       (class-alist (global-class-alist state))
       (all-class-names (strip-cars class-alist))
       ((when (not (assoc-equal method-class class-alist)))
        (mv t
            (hard-error 'unroll-java-code2 "Class ~x0 not found." (acons #\0 method-class nil))
            state))
       (class-info (lookup-equal method-class class-alist))
       (method-info-alist (jvm::class-decl-methods class-info))
       (method-id (cons method-name method-descriptor))
       ((when (not (assoc-equal method-id method-info-alist)))
        (mv t
            (hard-error 'unroll-java-code2 "Method ~x0 not found." (acons #\0 method-id nil))
            state))
       (method-info (lookup-equal method-id method-info-alist))
       ;; For every class currently loaded, we make an assumption about looking up that class in the class table:
       (class-table-assumptions (class-table-hyps2 state-var class-alist))
       (class-table-assumptions-translated (translate-terms class-table-assumptions 'unroll-java-code2 (w state)))
       (classes-to-assume-initialized (if (eq :all classes-to-assume-initialized)
                                          all-class-names
                                        classes-to-assume-initialized))
       (classes-to-assume-uninitialized (if (eq :all classes-to-assume-uninitialized)
                                            all-class-names
                                          classes-to-assume-uninitialized))
       ((when (intersection-equal classes-to-assume-initialized
                                  classes-to-assume-uninitialized))
        (mv t (er hard 'unroll-java-code2-fn "Some classes were assumed to be both initialized and uninitialized: ~x0"
                  (intersection-equal classes-to-assume-initialized
                                      classes-to-assume-uninitialized))
            state))
       (assumptions-that-classes-are-initialized (assumptions-that-classes-are-initialized classes-to-assume-initialized state-var))
       (assumptions-that-classes-are-uninitialized (assumptions-that-classes-are-uninitialized classes-to-assume-uninitialized state-var))
       ;; this implies that the list given is exhaustive:
       ;; (assumptions-that-classes-are-initialized `((equal (jvm::initialized-classes ,state-var)
       ;;                                         ',classes-to-assume-initialized)))
       ;; The thread:
       (th '(th)) ;todo what about (th) ?
       (parameter-types (lookup-eq :parameter-types method-info)) ;in order, does not include "this"

       ;; (formal-slot-count (jvm::count-slots-in-types parameter-types))
       (staticp (jvm::method-staticp method-info))
       (first-param-slot (if staticp 0 1)) ;skip a slot for "this" if it's an instance method
       (param-slot-to-name-alist (make-param-slot-to-name-alist method-info param-names))
       (param-name-to-slot-alist (reflect-alist param-slot-to-name-alist))

       ;(local-variable-table (lookup-eq :local-variable-table method-info)) ;may be nil
       ;(local-vars-at-pc-0 (merge-sort-local-vars-for-pc (local-vars-for-pc 0 local-variable-table))) ;may be nil if there is no local-variable-table

       ;; Translate and desugar user-supplied assumptions:
       (user-assumptions (translate-terms user-assumptions 'unroll-java-code2 (w state)))
       (user-assumption-vars (all-vars1-lst user-assumptions nil))
       ((when (not (subsetp-eq user-assumption-vars (list state-var))))
        (mv t (er hard 'unroll-java-code2-fn "Unsupported vars in assumptions: ~x0" (set-difference-eq user-assumption-vars (list state-var)))
            state))
       (param-slot-to-stack-item-alist (param-slot-to-stack-item-alist parameter-types first-param-slot th state-var))
       (user-assumptions (desugar-params-in-assumption-terms-to-stack-items user-assumptions param-name-to-slot-alist param-slot-to-stack-item-alist))
       (user-assumptions (desugar-calls-of-contents-in-terms user-assumptions `(jvm::heap ,state-var)))

       ;; If it's an instance method, the "this" object is below all the params on the stack, so we don't really need to worry about it.
       ;; Make assumptions for the parameters of the given method.  These will be
       ;; terms over STATE-VAR. ARRAY-LENGTH-ALIST is an alist from
       ;; parameter names (currently symbols) to naturals representing the lengths of the
       ;; corresponding arrays.
       ;; TODO: Should we use strings for parameter names?
       ;; TODO: What if two params of the method have names that differ only in case?
       ;; TODO: Add assumptions about 'this' ?

       (parameter-assumptions (assumptions-about-parameters-on-stack parameter-types first-param-slot param-slot-to-name-alist array-length-alist th state-var))
       (- (cw "(Parameter assumptions: ~x0)~%" parameter-assumptions))
       (structural-assumptions (append (standard-hyps-basic-before-invoke state-var)
                                       ;; anything else?
                                       ))
       (poised-assumptions (make-poised-assumptions staticp method-class method-name method-descriptor parameter-types state-var))
       (assumptions (append poised-assumptions ;these come first so the theorem fails fast when it doesn't apply
                            parameter-assumptions
                            structural-assumptions
                            assumptions-that-classes-are-initialized
                            assumptions-that-classes-are-uninitialized
                            user-assumptions
                            class-table-assumptions-translated
                            ))
       (all-lifted-methods (get-all-lifted-methods-from-table (w state)))
       (all-lifted-method-designator-strings (lookup-eq-in-all :method-designator-string all-lifted-methods))
       (all-lifted-method-functions (lookup-eq-in-all :function-name all-lifted-methods))
       (all-lifted-method-theorems (lookup-eq-in-all :theorem-name all-lifted-methods))
       (extra-rules (append all-lifted-method-functions
                            all-lifted-method-theorems
                            extra-rules))
       ;; Build a rule to inline methods not already lifted:
       (inlining-theorem (make-step-opener-for-non-already-lifted-methods all-lifted-method-designator-strings))
       ;; This gets rolled back after the make-event:
       (state (submit-event inlining-theorem state))
       ;; Set up the rule sets:
       (symbolic-execution-rules (if t ;(eq :auto steps) ;todo
                                     (compositional-symbolic-execution-rules)
                                   ;; for running a fixed number of steps:
                                   (append '(jvm::step-always-open ; jvm::step is replaced by JVM::STEP-ALWAYS-OPEN when we decide to open it
                                             step-opener-for-non-invokes)
                                           (symbolic-execution-rules-for-run-n-steps))))
       ((mv erp default-rule-alist) (make-rule-alist (append (unroll-java-code2-rules)
                                                             symbolic-execution-rules)
                                                     (w state)))
       ((when erp) (mv erp nil state))
       (rule-alists (or rule-alists ;use user-supplied rule-alists, if any
                        ;; by default, we use 1 rule-alist:
                        (list default-rule-alist)))
       ;; maybe add some rules (TODO: Print a warning):
       (rule-alists (extend-rule-alists2
                     (append (and ignore-exceptions *ignore-exception-axe-rule-set*)
                             (and ignore-errors *ignore-error-state-axe-rule-set*))
                     rule-alists
                     (w state)))
       ;; Include any :extra-rules given:
       ((mv erp rule-alists) (add-to-rule-alists extra-rules rule-alists (w state)))
       ((when erp) (mv erp nil state))
       ;; Include the inlining theorem introduced above:
       ((mv erp rule-alists) (add-to-rule-alists '(step-opener-for-non-already-lifted-methods) rule-alists (w state)))
       ((when erp) (mv erp nil state))
       ;;maybe remove some rules:
       (rule-alists (remove-from-rule-alists remove-rules rule-alists))
       ;; Do the symbolic execution.  We start with a state that is poised to do the invoke.  We always step the state once (using jvm::step-always-open).  Then we run until the stack frame created by the invoke gets popped off.
       ;;(term-to-simplify `(run-until-return (jvm::STEP-always-open (th) ,state-var)))
       (term-to-simplify (if t; (eq :auto steps)
                             `(run-until-return-from-stack-height (binary-+ '1 (stack-height ,state-var)) (jvm::step-always-open (th) ,state-var))
                           `(jvm::run-n-steps ',steps (jvm::step-always-open (th) ,state-var))))
       (limits (if (eq :auto steps)
                   nil
                 (progn$ (cw "(Adding limit of ~x0 steps.)~%" steps)
                         (acons 'run-until-return-from-stack-height-opener-axe steps nil))))
       (- (cw "(Assumptions: ~x0)~%" assumptions))
       (- (cw "(Simplifying term:~%"))
       ((mv erp result-dag state)
        (simp-term term-to-simplify
                        ;;TODO: I had this and it caused a crash! `(run-until-return ,(jvm::step (th) state-var))
                        :rule-alists rule-alists
                        :limits limits
                        :print print
                        :print-interval print-interval
                        :monitor monitor
                        :assumptions assumptions
                        :check-inputs nil))
       ((when erp)
        (er hard? 'unroll-java-code-fn "Error in unrolling.")
        (mv erp nil state))
       (- (cw "  Done simplifying term.)~%"))
       ;; todo: make optional and avoid this on huge terms by default
       ((mv erp result-dag state)
        (if prune-branches
            (prune-dag result-dag
                       assumptions
                       (set-difference-eq
                        ;; no actual symbolic execution is done here:
                        (union-eq (unroll-java-code2-rules)
                                  extra-rules)
                        remove-rules)
                       monitor
                       call-stp
                       state)
          (mv nil result-dag state)))
       ((when erp) (mv erp nil state))
       ;; Now simplify the pruned dag (TODO, repeatedly simplifying and pruning might help?)
       ;; TODO: Consider the rules to use here, especially if a limit was reached above
       ((mv erp result-dag state)
        (if prune-branches
            (simp-dag result-dag
                      :rule-alists (remove-from-rule-alists symbolic-execution-rules rule-alists) ;don't let any more execution happen (TODO: Or do we want it to?)
                      :print print
                      :print-interval print-interval
                      :monitor monitor
                      :assumptions assumptions
                      :check-inputs nil)
          (mv (erp-nil) result-dag state)))
       ((when erp) (mv erp nil state))
       ;; Result-dag should be over the single variable S0 and should represent
       ;; the change to S0 made by running the subroutine.
       (- (progn$ (cw "~|(Result DAG:~%")
                  (print-list result-dag)
                  (cw ")~%")))
       ((when (member-eq 'run-until-return-from-stack-height (dag-fns result-dag)))
        (and (dag-or-quotep-size-less-thanp result-dag 10000)
             (progn$ (cw "(Clarified term:~%")
                     (cw "~x0" (clarify-lifter-branches (dag-to-term result-dag)))
                     (cw ")~%")))
        (hard-error 'unroll-java-code2 "ERROR: Symbolic simulation did not seem to finish (see DAG above)." nil)
        (mv (erp-t) nil state))
       ;; Ensure that the single var in the DAG is state-var (s0):
       ((when (not (equal (dag-vars result-dag) (list state-var))))
        (mv t
            (er hard 'unroll-java-code2-fn "Unexpected vars in result DAG.  Vars are ~x0 but should be just ~x1." (dag-vars result-dag) state-var)
            state))
       ((mv erp fn-body supporting-events state-component-defun-names)
        (make-unroll-java-code2-fn-result result-dag fn abstract-state-components (w state)))
       ((when erp) (mv t ;todo: pass back the erp?
                       nil state))
       ;; for the theorem, use translated versions of the class-table-assumptions (much shorter)
       (nicer-assumptions (union-equal class-table-assumptions
                                       (set-difference-equal assumptions
                                                             class-table-assumptions-translated)))
       (main-theorem-name (pack$ fn '-correct))
       (helper-theorem-name (pack$ main-theorem-name '-helper))
       (helper-theorem
        `(defthmd ,helper-theorem-name
           (implies (and ,@nicer-assumptions)
                    (equal ,term-to-simplify
                           (,fn ,state-var)))
           :hints (("Goal" :in-theory (set-difference-eq
                                       '(,fn
                                         ,@state-component-defun-names
                                         ,@(rules-from-rule-alists rule-alists) ;the rules that axe used (todo: but think about phasing)
                                         ,@(wrap-all :executable-counterpart (flatten (map-strip-cars (strip-cdrs (axe-evaluator-function-info))))) ;must be able to evaluate
                                         myif-when-nil ;built into axe in a deep way
                                         myif-when-not-nil ;built into axe in a deep way
                                         ,@extra-proof-rules
                                         run-until-return-from-stack-height-of-myif-split ;todo: make and use a smart version, if appropriate
                                         run-until-return-from-stack-height-base
                                         run-until-return-from-stack-height-opener
                                         )
                                       ;; These are not legal ACL2 rules:
                                       '(run-until-return-from-stack-height-of-myif-alt-axe
                                         run-until-return-from-stack-height-opener-axe
                                         run-until-return-from-stack-height-base-axe
                                         step-state-with-pc-and-call-stack-height-becomes-step-axe
                                         step-state-with-pc-and-call-stack-height-does-nothing-1-axe
                                         step-state-with-pc-and-call-stack-height-does-nothing-2-axe))
                    ;; (e/d (,@state-component-defun-names
                    ;;                           ;; ,@extra-rules
                    ;;                           jvm::step ;todo: it would be nice to use an axe rule set here (should axe rule sets be acl2 rulesets? well, the axe-syntax rules would not work..)
                    ;;                           jvm::execute-invokestatic-helper
                    ;;                           jvm::get-superclass
                    ;;                           lookup-method-in-classes-peel-off-one-axe
                    ;;                           run-until-return
                    ;;                           run-until-return-from-stack-height-opener-fast
                    ;;                           jvm::cur-method-name
                    ;;                           stack-height
                    ;;                           ;jvm::cur-method
                    ;;                           )
                    ;;                        (RUN-UNTIL-RETURN-FROM-STACK-HEIGHT-OPENER-FAST
                    ;;                         RUN-UNTIL-RETURN-FROM-STACK-HEIGHT-BASE
                    ;;                         ))
                    ))))

       (main-theorem
        ;; Introduce the SH var for better matching in the LHS:
        `(defthm ,main-theorem-name
           (implies (and (equal sh (binary-+ '1 (stack-height ,state-var))) ;TODO: Think about this
                         ,@nicer-assumptions)
                    ;; this calls step (not the variant) and uses run-until-return-from-stack-height instead of run-until-return (why not run-until-return? must match run-until-return-from-stack-height-lemma-for-invoke)
                    (equal (run-until-return-from-stack-height sh (jvm::step (th) ,state-var))
                           (,fn ,state-var)))
           :hints ,(and prove-with-acl2
                        `(("Goal" :in-theory '(jvm::step jvm::step-always-open)
                           :use (:instance ,(pack$ fn '-correct-helper)))))))
       (new-all-lifted-methods (cons (acons :method-designator-string method-designator-string
                                            (acons :function-name fn
                                                   (acons :theorem-name main-theorem-name
                                                          nil)))
                                     all-lifted-methods))
       (event `(encapsulate ()
                 ,@supporting-events
                 ;; TODO: Abstract out the functionality to be over the inputs?
                 (defun ,fn (,state-var)
                   (declare (xargs :normalize nil)) ;todo: without this, things seemed to explode in MUSE/derivations/http/derivation-http-parsing.lisp
                   ;; (declare (ignorable ,state-var)) ;why?
                   ,fn-body)
                 ;;big cheat, just to check the theorem (TTODO: Prove this compositionally!)
                 ;;Really, simplify-term2 (or a variant) should produce this theorem!
                 ,@(and prove-with-acl2 (list `(local ,inlining-theorem))) ;needed by the helper lemma below
                 ,@(and prove-with-acl2
                        `((local ,helper-theorem)))
                 ,(if prove-with-acl2
                      main-theorem
                    `(skip-proofs ,main-theorem))
                 ;; Add this method to the list that will be stored in the table:
                 (table compositional-lifter-table
                        :all-lifted-methods
                        ',new-all-lifted-methods)))
       (- (cw "Done unrolling.)~%")))
    (mv (erp-nil)
        (extend-progn (extend-progn event `(table unroll-java-code2-table ',whole-form ',event))
                      `(value-triple ',fn) ;todo: use cw-event and then return invisible here?
                      )
        state
       )))

;;We need to supply:
;; - the name of the method to unroll
;; - the lengths of the array inputs
;; - extra rules to use
(defmacrodoc unroll-java-code2
  (&whole whole-form
          fn ;name of function to create  ;todo: reorder the first 2 args to match the main lifter (same for unroll-java-code)
          method-designator-string
          &key
          (array-length-alist 'nil)
          (assumptions 'nil) ;; These are over the state var S ;TODO: Allow these to mention vars that correspond to the inputs?
          (classes-to-assume-initialized ':all)
          (classes-to-assume-uninitialized 'nil)
          (ignore-exceptions 'nil)
          (ignore-errors 'nil)
          (extra-rules 'nil)   ; to add to the usual set of rules
          (remove-rules 'nil)  ;to remove from the usual set of rules
          (rule-alists 'nil) ;to completely replace the usual sets of rules
          (monitor 'nil)       ;rules to monitor
          (prove-with-acl2 't) ;todo: switch default to nil?
          (print ':brief)
          (abstract-state-components 'nil) ;todo: make t the default
          (prune-branches 't)
          (call-stp 'nil)
          (param-names 'nil)
          (extra-proof-rules 'nil)
          (print-interval '1000)
          (steps ':auto))
  (let ((form `(unroll-java-code2-fn ',fn
                                     ',method-designator-string
                                     ,array-length-alist
                                     ,assumptions
                                     ,classes-to-assume-initialized
                                     ,classes-to-assume-uninitialized
                                     ,ignore-exceptions
                                     ,ignore-errors
                                     ,extra-rules
                                     ,remove-rules
                                     ,rule-alists
                                     ,monitor
                                     ',prove-with-acl2
                                     ',print
                                     ',abstract-state-components
                                     ',prune-branches
                                     ',call-stp
                                     ',param-names
                                     ',extra-proof-rules
                                     ',print-interval
                                     ',steps
                                     ',whole-form
                                     state
                                    )))
    (if print
        `(make-event ,form)
      `(with-output
         :off :all
         :on error
         :gag-mode nil (make-event ,form))))
  :parents (lifter)
  :short "Given a Java method, define a function that represents
  the (unrolled) effect of the given method on the JVM state (under the given
  assumptions).  This uses symbolic execution including unrolling all loops."
  :args ((fn "The name of the function to create")
         (method-designator-string "The method designator of the method (a string like \"java.lang.Object.foo(IB)V\")")
         (array-length-alist "An alist pairing array parameters with their sizes")
         (classes-to-assume-initialized "Classes to assume the JVM has already initialized, or :all")
         (classes-to-assume-uninitialized "Classes to assume the JVM has not already initialized, or :all")
         (ignore-exceptions       "Whether to assume exceptions do not happen (e.g., out-of-bounds array accesses)")
         (ignore-errors           "Whether to assume JVM errors do not happen")
         (extra-rules             "Rules to add to the usual set of rules")
         (remove-rules            "Rules to remove from the usual set of rules")
         (rule-alists               "If non-nil, rule-sets to use to completely replace the usual rule sets")
         (monitor                 "Rules to monitor (to help debug failures)")
         (prove-with-acl2         "Attempt to sanity check the result by proving it with ACL2")
         (assumptions             "Assumptions about the initial state, S.")
         (print                   "Verbosity level (passed to the Axe rewriter)")
         (abstract-state-components "Whether to define functions abstracting how the state components are updated")
         (prune-branches "whether to aggressively prune unreachable branches in the result")
         (call-stp                 "whether to call STP when pruning (t, nil, or a number of conflicts before giving up)")
         (extra-proof-rules "Extra rules to support proving the result with ACL2")
         (print-interval "Number of DAG nodes to create before printing intermediate results (or nil for no limit).")
         (param-names "Names to use for the parameters (e.g., if no debugging information is available).")
         (steps "A number of steps to run.  A natural number (for debugging only), or :auto, meaning run until the method returns.")
         )
  :description "<p>This uses lifting theorems for subroutine calls that have already been lifted.  Otherwise, it effectively inlines the subroutine call.</p>
  <p>To inspect the resulting form, you can use @('print-list') on the generated defconst.</p>"
  )

;TODO: Add a wrapper that extracts just the indicated output, then replace the old unroll-java-code??
