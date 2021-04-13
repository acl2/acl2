; Making Axe rules and rule-alists from formulas
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

(include-book "kestrel/sequences/defforall" :dir :system)
(include-book "kestrel/alists-light/lookup-eq" :dir :system)
(include-book "kestrel/utilities/world" :dir :system)
(include-book "kestrel/utilities/terms" :dir :system)
;(include-book "../utilities/basic")
(include-book "kestrel/utilities/clean-up-lambdas" :dir :system) ; for drop-unused-lambda-bindings
(include-book "kestrel/utilities/conjunctions" :dir :system)
(include-book "kestrel/utilities/conjuncts-and-disjuncts" :dir :system)
(include-book "kestrel/utilities/quote" :dir :system)
(include-book "kestrel/utilities/acons-fast" :dir :system)
;(include-book "kestrel/typed-lists-light/all-consp" :dir :system)
(include-book "known-booleans")
(include-book "axe-rules")
(include-book "axe-syntax") ;since this book knows about axe-syntaxp and axe-bind-free
(include-book "kestrel/std/system/theorem-symbolp" :dir :system)
(include-book "kestrel/utilities/erp" :dir :system)
(local (include-book "kestrel/std/system/all-vars" :dir :system))
(local (include-book "kestrel/utilities/remove-guard-holders" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/union-equal" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))
(local (include-book "kestrel/lists-light/reverse" :dir :system))
(local (include-book "kestrel/utilities/equal-of-booleans" :dir :system))
(local (include-book "kestrel/lists-light/memberp" :dir :system))
;(local (include-book "kestrel/std/system/all-vars" :dir :system))
(local (include-book "kestrel/typed-lists-light/symbol-listp" :dir :system))
(local (include-book "kestrel/alists-light/symbol-alistp" :dir :system))
(local (include-book "kestrel/utilities/pseudo-termp" :dir :system))
(local (include-book "kestrel/typed-lists-light/pseudo-term-listp" :dir :system))

(in-theory (disable ilks-plist-worldp
                    plist-worldp)) ;move

(add-known-boolean memberp) ;move?

;move
(defthm pseudo-termp-of-caddr
  (implies (and (pseudo-termp x)
                ;(consp x)
;                (<= 2 (len x))
                )
           (pseudo-termp (caddr x)))
  :hints (("Goal" :expand ((pseudo-termp x)))))

;move
(defthm ilks-plist-worldp-forward-to-plist-worldp
  (implies (ilks-plist-worldp wrld)
           (plist-worldp wrld))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable ilks-plist-worldp))))

;move
;because they are symbols
(defthm lambda-free-termsp-of-fn-formals
  (lambda-free-termsp (fn-formals fun wrld))
  :hints (("Goal" :in-theory (enable lambda-free-termsp-when-symbol-listp))))

;move
;avoid name clash with the one in books/std/typed-lists/symbol-listp.lisp
(defthm symbol-listp-of-union-equal2
  (implies (and (symbol-listp x)
                (symbol-listp y))
           (symbol-listp (union-equal x y))))

;;;
;;; hyps-and-conc-for-axe-rule
;;;

;; Split an ACL2 theorem into hypotheses and a conclusion
;; Returns (mv erp hyps conc).
;todo: ACL2 must have something like this already
;; TODO: Add support for lambdas (here and in lhs-and-rhs-of-conc).
;; TODO: Handle a conjunction at the top level.
;; TODO: Document what kinds of ACL2 theorems can be made into Axe rules.
(defund hyps-and-conc-for-axe-rule (theorem-body rule-name)
  (declare (xargs :guard (pseudo-termp theorem-body)))
  (if (not (consp theorem-body))
      (mv `(:bad-rule ,rule-name)
          (er hard? 'hyps-and-conc-for-axe-rule "Unable to make an Axe rule from ~x0 (theorem body is a variable): ~x1" rule-name theorem-body)
          nil)
    (if (consp (car theorem-body))
        (mv `(:bad-rule ,rule-name)
            (er hard? 'hyps-and-conc-for-axe-rule "Unable to make an Axe rule from ~x0 (theorem body is a lambda application, which is not yet supported): ~x1" rule-name theorem-body)
            nil)
      (if (and (eq 'implies (car theorem-body))
               (= 2 (len (fargs theorem-body)))) ;for guards
          ;; TODO: Support nested implies?
          (mv (erp-nil)
              (get-conjuncts (second theorem-body))
              (third theorem-body))
        (mv (erp-nil)
            nil ;no hyps
            theorem-body)))))

(defthm pseudo-termp-of-mv-nth-2-of-hyps-and-conc-for-axe-rule
  (implies (pseudo-termp term)
           (pseudo-termp (mv-nth 2 (hyps-and-conc-for-axe-rule term sym))))
  :hints (("Goal" :in-theory (enable hyps-and-conc-for-axe-rule))))

(defthm pseudo-term-listp-of-mv-nth-1-of-hyps-and-conc-for-axe-rule
  (implies (pseudo-termp term)
           (pseudo-term-listp (mv-nth 1 (hyps-and-conc-for-axe-rule term sym))))
  :hints (("Goal" :in-theory (enable hyps-and-conc-for-axe-rule))))

;; ;; Recognize a pseudo-term that is neither a variable, quoted constant, or lambda application.
;; (defun regular-function-callp (term)
;;   (declare (xargs :guard (pseudo-termp term)))
;;   (and (consp term)
;;        (not (eq 'quote (ffn-symb term)))
;;        (not (consp (ffn-symb term))) ;test for a lambda application
;;        ))

;;ffixme think about what to do with force in rules..

;ffixme how are corollaries stored?  should we allow making them into axe-rules?

;;;
;;; Handle synp hyps:
;;;

;; ;currently, we only support quoteps (and turn them into axe-quoteps)
;; ;ffixme handle (not (quotep <x>)) as well? maybe any boolean combination of quotep hyps?
;; (defun process-syntaxp-conjuncts (conjuncts)
;;   (if (endp conjuncts)
;;       nil
;;     (let ((conjunct (car conjuncts)))
;;       (if (and (consp conjunct)
;;                (eq 'quotep (ffn-symb conjunct)))
;;           (cons `(AXE-SYNTAXP (axe-QUOTEP-FN ,(first (fargs conjunct))))
;;                 (process-syntaxp-conjuncts (cdr conjuncts)))
;;         (prog2$ (er hard? 'process-syntaxp-conjuncts "unrecognized argument to syntaxp: ~x0.  we only support quotep."
;;                             conjunct)
;;                 (cons ''nil ;so that it never matches..
;;                       (process-syntaxp-conjuncts (cdr conjuncts))))))))

;; (skip -proofs (verify-guards process-syntaxp-conjuncts))

;; Returns (mv erp processed-argument).
;;sample inputs: (QUOTEP SHIFT-AMOUNT), (NOT (QUOTEP X)), (IF (QUOTEP K) (QUOTEP SIZE) 'NIL)
;;handles a nest of IFs and NOTs with constants and calls to quotep at the leaves
(defund process-syntaxp-argument (term rule-symbol)
  (declare (xargs :guard (pseudo-termp term)))
  (if (not (consp term)) ;;maybe it's okay to allow a variable here?
      (prog2$ (er hard? 'process-syntaxp-argument "unexpected term, ~x0, in syntaxp hyp in rule ~x1." term rule-symbol)
              (mv (erp-t) nil))
    (if (myquotep term) ;quoted constant
        (mv (erp-nil) term)
      (let ((fn (ffn-symb term)))
        (if (and (eq 'quotep fn) ; (quotep <var>), convert to axe-quotep (why?)
                 (= 1 (len (fargs term)))
                 (symbolp (first (fargs term))))
            (mv (erp-nil) `(axe-quotep ,(first (fargs term))))
          (if (eq fn 'if)
              (b* (((mv erp processed-test) (process-syntaxp-argument (farg1 term) rule-symbol))
                   ((when erp) (mv erp nil))
                   ((mv erp processed-then) (process-syntaxp-argument (farg2 term) rule-symbol))
                   ((when erp) (mv erp nil))
                   ((mv erp processed-else) (process-syntaxp-argument (farg3 term) rule-symbol))
                   ((when erp) (mv erp nil)))
                (mv (erp-nil) `(if ,processed-test ,processed-then ,processed-else)))
            (if (eq fn 'not)
                (b* (((mv erp processed-arg) (process-syntaxp-argument (farg1 term) rule-symbol))
                     ((when erp) (mv erp nil)))
                  (mv (erp-nil) `(not ,processed-arg)))
              (prog2$ (er hard? 'process-syntaxp-argument "unexpected term, ~x0, in syntaxp hyp in rule ~x1." term rule-symbol)
                      (mv (erp-t) nil)))))))))

(defthm pseudo-termp-of-mv-nth-1-of-process-syntaxp-argument
  (implies (pseudo-termp term)
           (pseudo-termp (mv-nth 1 (process-syntaxp-argument term rule-symbol))))
  :hints (("Goal" :in-theory (enable process-syntaxp-argument))))

(defthm axe-syntaxp-exprp-of-mv-nth-1-of-process-syntaxp-argument
  (implies (and (pseudo-termp conjunct)
                (not (mv-nth 0 (process-syntaxp-argument conjunct rule-symbol))))
           (axe-syntaxp-exprp (mv-nth 1 (process-syntaxp-argument conjunct rule-symbol))))
  :hints (("Goal" :in-theory (enable process-syntaxp-argument axe-syntaxp-exprp axe-syntaxp-function-applicationp list-of-variables-and-constantsp))))

;; Returns a hyp.
;; process-syntaxp-argument helps catch errors if the rule has unsupported stuff in a syntaxp hyp
;; propagate errors back?
(defund make-axe-syntaxp-hyp-for-synp-conjunct (conjunct bound-vars rule-symbol hyp)
  (declare (xargs :guard (and (pseudo-termp conjunct)
                              (symbol-listp bound-vars)
                              (symbolp rule-symbol))))
  (b* ((mentioned-vars (all-vars conjunct))
       ;drop?:
       (allowed-vars (cons 'dag-array bound-vars))
       ((when (not (subsetp-eq mentioned-vars allowed-vars)))
        (er hard? 'make-axe-syntaxp-hyp-for-synp-conjunct "Hyp ~x0 in rule ~x1 mentions vars ~x2 that are not bound by the LHS or by preceding hyps."
            hyp rule-symbol (set-difference-eq mentioned-vars allowed-vars))
        *unrelievable-hyp*)
       ((mv erp processed-arg)
        (process-syntaxp-argument conjunct rule-symbol))
       ((when erp)
        (er hard? 'make-axe-syntaxp-hyp-for-synp-conjunct "Error processing synp hyp ~x0 in rule ~x1." hyp rule-symbol)
        *unrelievable-hyp*))
    `(axe-syntaxp ,processed-arg)))

(defthm axe-rule-hypp-of-make-axe-syntaxp-hyp-for-synp-conjunct
  (implies (pseudo-termp conjunct)
           (axe-rule-hypp (make-axe-syntaxp-hyp-for-synp-conjunct conjunct bound-vars rule-symbol hyp)))
  :hints (("Goal" :in-theory (enable make-axe-syntaxp-hyp-for-synp-conjunct axe-rule-hypp))))

;; Returns a list of hyps.
(defund make-axe-syntaxp-hyps-for-synp-conjuncts (conjuncts bound-vars rule-symbol hyp)
  (declare (xargs :guard (and (pseudo-term-listp conjuncts)
                              (symbol-listp bound-vars)
                              (symbolp rule-symbol))))
  (if (endp conjuncts)
      nil
    (cons (make-axe-syntaxp-hyp-for-synp-conjunct (first conjuncts) bound-vars rule-symbol hyp)
          (make-axe-syntaxp-hyps-for-synp-conjuncts (rest conjuncts) bound-vars rule-symbol hyp))))

(defthm axe-rule-hyp-listp-of-make-axe-syntaxp-hyps-for-synp-conjuncts
  (implies (pseudo-term-listp conjuncts)
           (axe-rule-hyp-listp (make-axe-syntaxp-hyps-for-synp-conjuncts conjuncts bound-vars rule-symbol hyp)))
  :hints (("Goal" :in-theory (enable make-axe-syntaxp-hyps-for-synp-conjuncts))))

;; Returns a list of hyps.  More than one hyp can be returned because we
;; extract conjuncts and make a separate hyp for each one
;; TODO: Don't flatten by calling get-conjuncts-of-term, now that axe-syntaxp hyps can be if/not nests
(defund make-axe-syntaxp-hyps-for-synp-hyp (term bound-vars rule-symbol hyp)
  (declare (xargs :guard (and (pseudo-termp term)
                              (symbol-listp bound-vars)
                              (symbolp rule-symbol))))
  (make-axe-syntaxp-hyps-for-synp-conjuncts (get-conjuncts-of-term term) bound-vars rule-symbol hyp))

(defthm axe-rule-hyp-listp-of-make-axe-syntaxp-hyps-for-synp-hyp
  (implies (pseudo-termp term)
           (axe-rule-hyp-listp (make-axe-syntaxp-hyps-for-synp-hyp term bound-vars rule-symbol hyp)))
  :hints (("Goal" :in-theory (enable make-axe-syntaxp-hyps-for-synp-hyp))))

;; If the function takes dag-array as its last formal, drop the corresponding arg.
;; TODO: Check that dag-array is passed as the arg to the dag-array-formal, if any.
(defund process-axe-syntaxp-function-application (expr wrld)
  (declare (xargs :guard (and (pseudo-termp expr)
                              (axe-syntaxp-function-applicationp expr)
                              (plist-worldp wrld))
                  :guard-hints (("Goal" :in-theory (enable axe-syntaxp-function-applicationp)))))
  (let* ((fn (ffn-symb expr))
         (args (fargs expr)))
    (if (eq fn 'axe-quotep) ;special case, we know dag-array isn't mentioned
        expr
      (let* ((formals (fn-formals fn wrld))
             (fn-uses-dagp (and (consp formals)
                                (eq 'dag-array (car (last formals)))))
             (args-to-store (if fn-uses-dagp
                                (butlast args 1)
                              args)))
        `(,fn ,@args-to-store)))))

;; Simpler than pseudo-term-listp-of-take.
(defthm pseudo-term-listp-of-take-simple
  (implies (pseudo-term-listp x)
           (pseudo-term-listp (take n x))))

(defthm pseudo-termp-of-process-axe-syntaxp-function-application
  (implies (and (pseudo-termp expr)
                (axe-syntaxp-function-applicationp expr)
                ;;(not (eq 'quote (ffn-symb expr)))
                )
           (pseudo-termp (process-axe-syntaxp-function-application expr wrld)))
  :hints (("Goal" :in-theory (enable process-axe-syntaxp-function-application axe-syntaxp-function-applicationp))))

(defthm axe-syntaxp-exprp-of-process-axe-syntaxp-function-application
  (implies (and (pseudo-termp expr)
                (axe-syntaxp-function-applicationp expr)
                ;; (not (eq 'quote (ffn-symb expr)))
                (not (eq 'if (ffn-symb expr)))
                (not (eq 'not (ffn-symb expr)))
        ;        (not (eq 'axe-quotep (ffn-symb expr))) ;ok?
                )
           (axe-syntaxp-exprp (process-axe-syntaxp-function-application expr wrld)))
  :hints (("Goal" :expand (axe-syntaxp-exprp expr)
           :in-theory (enable process-axe-syntaxp-function-application axe-syntaxp-function-applicationp axe-syntaxp-exprp))))

(defund process-axe-syntaxp-expr (expr wrld)
  (declare (xargs :guard (and (pseudo-termp expr)
                              (axe-syntaxp-exprp expr)
                              (plist-worldp wrld))
                  :guard-hints (("Goal" :in-theory (enable axe-syntaxp-exprp)))))
  (case (ffn-symb expr)
    (quote expr)
    (if `(if ,(process-axe-syntaxp-expr (farg1 expr) wrld)
             ,(process-axe-syntaxp-expr (farg2 expr) wrld)
           ,(process-axe-syntaxp-expr (farg3 expr) wrld)))
    (not `(not ,(process-axe-syntaxp-expr (farg1 expr) wrld)))
    (t (process-axe-syntaxp-function-application expr wrld))))

(defthm pseudo-termp-of-process-axe-syntaxp-expr
  (implies (and (pseudo-termp expr)
                (axe-syntaxp-exprp expr))
           (pseudo-termp (process-axe-syntaxp-expr expr wrld)))
  :hints (("Goal" :in-theory (enable process-axe-syntaxp-expr axe-syntaxp-exprp))))

(defthm axe-syntaxp-exprpp-of-process-axe-syntaxp-expr
  (implies (and (pseudo-termp expr)
                (axe-syntaxp-exprp expr))
           (axe-syntaxp-exprp (process-axe-syntaxp-expr expr wrld)))
  :hints (("Goal" :in-theory (enable process-axe-syntaxp-expr axe-syntaxp-exprp))))

;; If the function takes dag-array as its last formal, drop the corresponding arg.
;; TODO: Check that dag-array is passed as the arg to the dag-array-formal, if any.
(defund process-axe-bind-free-function-application (expr wrld)
  (declare (xargs :guard (and (pseudo-termp expr)
                              (axe-bind-free-function-applicationp expr)
                              (plist-worldp wrld))
                  :guard-hints (("Goal" :in-theory (enable axe-bind-free-function-applicationp)))))
  (let* ((fn (ffn-symb expr))
         (args (fargs expr)))
    (let* ((formals (fn-formals fn wrld))
           (fn-uses-dagp (and (consp formals)
                              (eq 'dag-array (car (last formals)))))
           (args-to-store (if fn-uses-dagp
                              (butlast args 1)
                            args)))
      `(,fn ,@args-to-store))))

(defthm pseudo-termp-of-process-axe-bind-free-function-application
  (implies (and (pseudo-termp expr)
                (axe-bind-free-function-applicationp expr)
                ;;(not (eq 'quote (ffn-symb expr)))
                )
           (pseudo-termp (process-axe-bind-free-function-application expr wrld)))
  :hints (("Goal" :in-theory (enable process-axe-bind-free-function-application axe-bind-free-function-applicationp))))

(defthm axe-bind-free-function-applicationp-of-process-axe-bind-free-function-application
  (implies (and (pseudo-termp expr)
                (axe-bind-free-function-applicationp expr)
                ;;(not (eq 'quote (ffn-symb expr)))
                )
           (axe-bind-free-function-applicationp (process-axe-bind-free-function-application expr wrld)))
  :hints (("Goal" :in-theory (enable process-axe-bind-free-function-application axe-bind-free-function-applicationp))))

;;;
;;; make-axe-rule-hyps-for-hyp
;;;

;; Returns (mv hyps bound-vars).  The HYPS returned may have more than one
;; element if we flatten a syntaxp or axe-syntaxp hyp.  The HYPS returned may
;; be empty if drop a hyp that is a non-nil constant. The BOUND-VARS returned
;; is the list of vars bound by the LHS, this hyp, and all previous hyps.
(defund make-axe-rule-hyps-for-hyp (hyp bound-vars rule-symbol wrld)
  (declare (xargs :guard (and (pseudo-termp hyp)
                              (symbol-listp bound-vars)
                              (symbolp rule-symbol)
                              (plist-worldp wrld))
                  :guard-hints (("Goal" :expand (AXE-SYNTAXP-EXPRP (CADR HYP))))
                  ))
  (if (atom hyp) ;; can only be a variable
      ;;turn a hyp of <var> into (not (equal 'nil <var>)) which is equivalent.  Axe relies on the fact that a hyp cannot be a variable.
      (mv `((not (equal 'nil ,hyp))) bound-vars)
    (if (fquotep hyp)
        (if (equal *nil* hyp)
            (prog2$ (er hard? 'make-axe-rule-hyps-for-hyp "Found a hyp of nil in rule ~x0!" rule-symbol)
                    (mv *unrelievable-hyps* bound-vars))
          (prog2$ (cw "Note: Skipping a constant, non-nil hyp of ~x0 in ~x1.~%" hyp rule-symbol)
                  (mv nil ;no hyps!
                      bound-vars)))
      (if (call-of 'synp hyp) ;; Example: (SYNP 'NIL '(SYNTAXP (QUOTEP X)) '(IF (QUOTEP X) 'T 'NIL)).
          ;; it's a call to SYNP, which represents both syntaxp and bind-free hyps in ACL2:
          (if (and (= 3 (len (fargs hyp)))
                   (true-listp hyp)
                   (equal *nil* (farg1 hyp))
                   ;; arg 2 is the untranslated form, which we ignore
                   (myquotep (farg3 hyp))
                   (pseudo-termp (unquote (farg3 hyp))))
              ;; We attempt to convert the syntaxp hyp into an axe-syntaxp hyp (this only works for very simple hyps)
              (mv (make-axe-syntaxp-hyps-for-synp-hyp (unquote (farg3 hyp)) bound-vars rule-symbol hyp)
                  bound-vars ;no extra vars get bound
                  )
            ;; TODO: Check whether it is a bind-free hyp and print a better message if so:
            (prog2$ (er hard? 'make-axe-rule-hyps-for-hyp "Hyp ~x0 in rule ~x1 is an unsupported call of SYNP.  If it is a (translated) bind-free hyp, considering using axe-bind-free instead, along with DAG-aware versions of the function(s) called inside the bind-free."
                        hyp rule-symbol)
                    (mv *unrelievable-hyps* bound-vars)))
        (if (call-of 'axe-syntaxp hyp)
            (b* (((when (not (and (true-listp (fargs hyp))
                                  (eql 1 (len (fargs hyp))))))
                  (er hard? 'make-axe-rule-hyps-for-hyp "Ill-formed axe-syntaxp hyp ~x0 in rule ~x1." hyp rule-symbol)
                  (mv *unrelievable-hyps* bound-vars))
                 ;; drop this?:
                 ;; ((when (member-eq 'dag-array bound-vars))
                 ;;  (er hard? 'make-axe-rule-hyps-for-hyp "The variable dag-array is bound in rule ~x0, but that variable has a special meaning in axe-syntaxp hyps and cannot appear in such rules."
                 ;;      rule-symbol)
                 ;;  (mv *unrelievable-hyps* bound-vars))
                 (axe-syntaxp-expr (farg1 hyp))
                 ((when (not (axe-syntaxp-exprp axe-syntaxp-expr)))
                  (er hard? 'make-axe-rule-hyps-for-hyp "Ill-formed axe-syntaxp argument ~x0 in rule ~x1." axe-syntaxp-expr rule-symbol)
                  (mv *unrelievable-hyps* bound-vars))
                 (processed-axe-syntaxp-expr (process-axe-syntaxp-expr axe-syntaxp-expr wrld))
                 (mentioned-vars (all-vars processed-axe-syntaxp-expr)) ;dag-array has been perhaps removed
                 (allowed-vars bound-vars ;(cons 'dag-array bound-vars)
                               )
                 ((when (not (subsetp-eq mentioned-vars allowed-vars)))
                  (er hard? 'make-axe-rule-hyps-for-hyp "Axe-syntaxp hyp ~x0 in rule ~x1 mentions vars ~x2 that are not bound by the LHS or by preceding hyps."
                      hyp rule-symbol (set-difference-eq mentioned-vars allowed-vars))
                  (mv *unrelievable-hyps* bound-vars))
                 ;; TODO: Should we convert any calls of quote to axe-quotep?
                 )
              (mv `((axe-syntaxp ,processed-axe-syntaxp-expr)) bound-vars))
          (if (call-of 'axe-bind-free hyp) ;; (axe-bind-free <term> '<vars-to-bind>)
              (b* (((when (not (and (true-listp hyp)
                                    (eql 2 (len (fargs hyp))))))
                    (er hard? 'make-axe-rule-hyps-for-hyp "The axe-bind-free hyp ~x0 is not well-formed (should be a call of axe-bind-free on exactly 2 arguments, a term and a quoted list of vars to bind)." hyp)
                    (mv *unrelievable-hyps* bound-vars))
                   ;; ((when (member-eq 'dag-array bound-vars))
                   ;;  (er hard? 'make-axe-rule-hyps-for-hyp "The variable DAG-ARRAY is bound in rule ~x0, but that variable has a special meaning in axe-bind-free hyps and cannot already be bound when an axe-bind-free hyp is encountered."
                   ;;      rule-symbol)
                   ;;  (mv *unrelievable-hyps* bound-vars))
                   (axe-bind-free-expr (farg1 hyp))
                   ((when (not (axe-bind-free-function-applicationp axe-bind-free-expr)))
                    (er hard? 'make-axe-rule-hyps-for-hyp "Ill-formed axe-bind-free argument ~x0 in rule ~x1." axe-bind-free-expr rule-symbol)
                    (mv *unrelievable-hyps* bound-vars))
                   (axe-bind-free-expr (process-axe-bind-free-function-application axe-bind-free-expr wrld))
                   (mentioned-vars (all-vars axe-bind-free-expr))
                   (allowed-vars bound-vars ;(cons 'dag-array bound-vars)
                                 )
                   ((when (not (subsetp-eq mentioned-vars allowed-vars)))
                    (er hard? 'make-axe-rule-hyps-for-hyp "Axe-bind-free hyp ~x0 in rule ~x1 mentions vars ~x2 that are not bound by the LHS or preceding hyps."
                        hyp rule-symbol (set-difference-eq mentioned-vars allowed-vars))
                    (mv *unrelievable-hyps* bound-vars))
                   (quoted-vars-to-bind (farg2 hyp))
                   ((when (not (quoted-symbol-listp quoted-vars-to-bind)))
                    (er hard? 'make-axe-rule-hyps-for-hyp "The second argument to an axe-bind-free hyp must be a quoted list of vars, but we got ~x0 in hyp ~x1." quoted-vars-to-bind hyp)
                    (mv *unrelievable-hyps* bound-vars))
                   (vars-to-bind (unquote quoted-vars-to-bind))
                   ((when (not (consp vars-to-bind)))
                    (er hard? 'make-axe-rule-hyps-for-hyp "The declared vars-to-bind of axe-bind-free hyp ~x0 in rule ~x1 is empty." hyp rule-symbol)
                    (mv *unrelievable-hyps* bound-vars))
                   ((when (intersection-eq vars-to-bind bound-vars))
                    ;; TODO: Improve message to just print the intersection
                    (er hard? 'make-axe-rule-hyps-for-hyp "The axe-bind-free hyp ~x0 in rule ~x1 is declared to bind the vars ~x2, but these are not disjoint from the set of vars already bound (~x3)" hyp rule-symbol vars-to-bind bound-vars)
                    (mv *unrelievable-hyps* bound-vars)))
                ;; axe-bind-free hyps include both the term and the variables:
                (mv `((axe-bind-free ,axe-bind-free-expr ,vars-to-bind))
                    (append vars-to-bind bound-vars)))
            ;; not a special hyp:
            (b* ((all-fns (fns-in-term hyp))
                 ((when (member-eq 'axe-syntaxp all-fns))
                  (er hard? 'make-axe-rule-hyps-for-hyp "Hyp ~x0 in rule ~x1 contains a call to axe-syntaxp that is not at the top level." hyp rule-symbol)
                  (mv *unrelievable-hyps* bound-vars))
                 ((when (member-eq 'axe-bind-free all-fns))
                  (er hard? 'make-axe-rule-hyps-for-hyp "Hyp ~x0 in rule ~x1 contains a call to axe-bind-free that is not at the top level." hyp rule-symbol)
                  (mv *unrelievable-hyps* bound-vars))
                 ;; todo: check for work-hards not at the top-level?
                 (hyp (expand-lambdas-in-term hyp)) ;could print a note here, if this does anything.  ;; TODO: What if we don't expand lambdas?  Maybe that's only needed for the free variable case?
                 ((when (not (consp hyp)))
                  (er hard? 'make-axe-rule-hyps-for-hyp "Hyp ~x0 in rule ~x1 is not a function call after expanding lambdas." hyp rule-symbol)
                  (mv *unrelievable-hyps* bound-vars))
                 ((when (fquotep hyp))
                  (er hard? 'make-axe-rule-hyps-for-hyp "Hyp ~x0 in rule ~x1 is a quoted constant after expanding lambdas." hyp rule-symbol)
                  (mv *unrelievable-hyps* bound-vars))
                 (hyp-vars (all-vars hyp))
                 (free-vars (set-difference-eq hyp-vars bound-vars)))
              (if free-vars
                  ;; Normal hyp with free vars that will get bound by matching with assumptions:
                  ;; TODO: Wrap the hyp in a marker that indicates that free vars are present?
                  (b* (;; (- (cw "NOTE: Free vars in rule ~x0.~%" rule-symbol))
                       ;; Strip and note the work-hard, if any:
                       ;; Previously, a work-hard with free vars was an error, but Axe generates some rules like that.
                       ((mv hyp work-hardp)
                        (if (and (call-of 'work-hard hyp)
                                 (= 1 (len (fargs hyp))))
                            (mv (farg1 hyp) t)
                          (mv hyp nil)))
                       (- (and work-hardp free-vars
                               (cw "NOTE: Hyp ~x0 in rule ~x1 is a call of work-hard but contains free-variables." hyp rule-symbol)))
                       ((when (not (consp hyp)))
                        (er hard? 'make-axe-rule-hyps-for-hyp "Hyp ~x0 in rule ~x1 is not a function call after expanding lambdas and possibly stripping a work-hard." hyp rule-symbol)
                        (mv *unrelievable-hyps* bound-vars))
                       ((when (fquotep hyp))
                        (er hard? 'make-axe-rule-hyps-for-hyp "Hyp ~x0 in rule ~x1 is a quoted constant after expanding lambdas and possibly stripping a work-hard." hyp rule-symbol)
                        (mv *unrelievable-hyps* bound-vars))
                       (fn (ffn-symb hyp)))
                    (prog2$ (and ;todo: drop this check, or use it:
                             (eq 'equal fn) ;; test for (equal <free-var> <term-with-no-free-vars>)
                             (eql 2 (len (fargs hyp))) ;for guard proofs
                             (atom (farg1 hyp))
                             (not (member-eq (farg1 hyp) bound-vars))
                             (subsetp-eq (all-vars (farg2 hyp))
                                         bound-vars)
                             ;;(cw "Note: Binding hyp ~x0 detected in rule ~x1.~%" hyp rule-symbol) ;todo: add a print option?
                             )
                            (mv (list hyp)
                                (append free-vars ;if the hyp is relieved by searching for matches in the context, any free vars in the hyp wil become bound
                                        bound-vars))))
                ;; Normal hyp with no free vars:
                ;; TODO: Wrap the hyp in a marker that indicates that no free vars are present?
                (mv (list hyp)
                    bound-vars)))))))))

(defthmd not-equal-of-car-when-not-memberp-of-fns-in-term
  (implies (and (not (memberp a (fns-in-term x)))
                (consp x)
                ;(pseudo-termp x)
                (not (equal 'quote a))
                (not (consp a))
                )
           (not (equal a (car x))))
  :hints (("Goal" :expand (fns-in-term x)
           :in-theory (enable fns-in-term))))

;memberp version
(defthm not-memberp-of-fns-in-term-of-expand-lambdas-in-term
  (implies (and (pseudo-termp term)
                (not (memberp fn (fns-in-term term))))
           (not (memberp fn (fns-in-term (expand-lambdas-in-term term)))))
  :hints (("Goal" :use (:instance not-member-equal-of-fns-in-term-of-expand-lambdas-in-term)
           :in-theory (disable not-member-equal-of-fns-in-term-of-expand-lambdas-in-term))))

(defthm not-memberp-of-fns-in-term-of-cadr
  (implies (and (not (memberp fn (fns-in-term x)))
                (not (equal 'quote (car x))))
           (not (memberp fn (fns-in-term (car (cdr x))))))
  :hints (("Goal" :expand (fns-in-term x)
           :in-theory (enable fns-in-term))))

(defthmd lambda-free-termp-when-equal-of-car-and-quote
  (implies (equal 'quote (car term))
           (lambda-free-termp term)))

;move
(defthm car-of-expand-lambdas-in-terms
  (equal (car (expand-lambdas-in-terms terms))
         (expand-lambdas-in-term (car terms)))
  :hints (("Goal" :in-theory (enable expand-lambdas-in-terms))))

;(local (in-theory (disable pairlis$))) ;prevent inductions

(defthm car-of-my-sublis-var-lst
  (implies (consp l)
           (equal (car (my-sublis-var-lst alist l))
                  (my-sublis-var alist (car l))))
  :hints (("Goal" :expand (my-sublis-var-lst alist l)
           :in-theory (enable my-sublis-var-lst))))

(defthm lambda-free-termp-of-cadr
  (implies (and (pseudo-termp term)
                (lambda-free-termp term)
                (not (equal 'quote (car term)))
                ;(not (consp (car term)))
                )
           (lambda-free-termp (cadr term)))
  :hints (("Goal" :in-theory (enable lambda-free-termp-when-equal-of-car-and-quote))))

(defthm axe-rule-hyp-listp-of-mv-nth-0-of-make-axe-rule-hyps-for-hyp
  (implies (pseudo-termp hyp)
           (axe-rule-hyp-listp (mv-nth 0 (make-axe-rule-hyps-for-hyp hyp bound-vars rule-symbol wrld))))
  :hints (("Goal" :use (;; (:instance not-member-equal-of-fns-in-term-of-expand-lambdas-in-term
                        ;;            (fn 'axe-bind-free)
                        ;;            (term hyp))
                        ;; (:instance not-member-equal-of-fns-in-term-of-expand-lambdas-in-term
                        ;;            (fn 'axe-bind-free)
                        ;;            (term (cadr hyp)))
                        ;; (:instance not-member-equal-of-fns-in-term-of-expand-lambdas-in-term
                        ;;            (fn 'axe-syntaxp)
                        ;;            (term hyp))
                        ;; (:instance not-member-equal-of-fns-in-term-of-expand-lambdas-in-term
                        ;;            (fn 'axe-syntaxp)
                        ;;            (term (cadr hyp)))
                        ;; (:instance not-member-equal-of-fns-in-term-of-expand-lambdas-in-term
                        ;;            (fn 'work-hard)
                        ;;            (term (cdr hyp)))
                        )
           :do-not '(generalize eliminate-destructors)
           :expand (;(FNS-IN-TERM HYP)
                    ;;(expand-lambdas-in-term hyp)
                    ;(fns-in-term (expand-lambdas-in-term hyp))
                    ;(pseudo-termp (cdr hyp))
                    ;(PSEUDO-TERMP (CADDR HYP))
                    ;(pseudo-term-listp (cddr hyp))
                    ;(PSEUDO-TERM-LISTP (CDR HYP))
                    ;;(PSEUDO-TERMP HYP)
                    (AXE-SYNTAXP-EXPRP (CADR HYP))
                    ;(EXPAND-LAMBDAS-IN-TERM HYP)
                    )
           :in-theory (e/d (axe-rule-hypp make-axe-rule-hyps-for-hyp symbolp-when-pseudo-termp
                                          not-equal-of-car-when-not-memberp-of-fns-in-term
                                          )
                           (not-member-equal-of-fns-in-term-of-expand-lambdas-in-term
                            MYQUOTEP
                            ;QUOTED-SYMBOL-LISTP
                            ;ALL-VAR-OR-MYQUOTEP
                            fns-in-term
                            add-to-set-equal
                            EXPAND-LAMBDAS-IN-TERM
                            )))))

;; (defthm axe-rule-hypp-of-mv-nth-0-of-make-axe-rule-hyp
;;   (implies (and (pseudo-termp hyp)
;;                 (not (equal :drop (mv-nth 0 (make-axe-rule-hyp hyp bound-vars rule-symbol))))
;;                 (not (equal :error (mv-nth 0 (make-axe-rule-hyp hyp bound-vars rule-symbol)))))
;;            (axe-rule-hypp (mv-nth 0 (make-axe-rule-hyp hyp bound-vars rule-symbol))))
;;   :hints (("Goal" :in-theory (enable axe-rule-hypp make-axe-rule-hyp))))

;; ;todo: actually we probably want everything to be lambda-free
;; (defun all-regular-function-callp (x)
;;   (declare (xargs :guard (pseudo-term-listp x)))
;;   (if (atom x)
;;       t
;;     (and (regular-function-callp (first x))
;;          (all-regular-function-callp (rest x)))))

;; (defthm all-consp-of-mv-nth-0-of-make-axe-rule-hyps-for-hyp
;;   (all-consp (mv-nth 0 (make-axe-rule-hyps-for-hyp hyp bound-vars rule-symbol)))
;;   :hints (("Goal" :in-theory (enable make-axe-rule-hyps-for-hyp))))

;todo: not true because of axe-bind-free hyps.  define a notion of an axe-hyp..
;; (defthm pseudo-termp-of-mv-nth-1-of-make-axe-rule-hyp
;;   (implies (and (not (mv-nth 0 (make-axe-rule-hyp hyp bound-vars rule-symbol)))
;;                 (pseudo-termp hyp))
;;            (pseudo-termp (mv-nth 1 (make-axe-rule-hyp hyp bound-vars rule-symbol))))
;;   :hints (("Goal" :in-theory (enable make-axe-rule-hyp))))

(defthm symbol-listp-of-mv-nth-1-of-make-axe-rule-hyps-for-hyp
  (implies (and (symbol-listp bound-vars)
                (pseudo-termp hyp))
           (symbol-listp (mv-nth 1 (make-axe-rule-hyps-for-hyp hyp bound-vars rule-symbol wrld))))
  :hints (("Goal" :in-theory (enable make-axe-rule-hyps-for-hyp))))

(defthm true-listp-of-mv-nth-0-of-make-axe-rule-hyps-for-hyp
  (true-listp (mv-nth 0 (make-axe-rule-hyps-for-hyp hyp bound-vars rule-symbol wrld)))
  :hints (("Goal" :in-theory (enable make-axe-rule-hyps-for-hyp))))

(defthm true-listp-of-mv-nth-1-of-make-axe-rule-hyps-for-hyp
  (implies (and (true-listp bound-vars)
                ;; (pseudo-termp hyp)
                )
           (true-listp (mv-nth 1 (make-axe-rule-hyps-for-hyp hyp bound-vars rule-symbol wrld))))
  :hints (("Goal" :in-theory (enable make-axe-rule-hyps-for-hyp))))

;TODO: prove
;; (defthm all-regular-function-callp-of-make-axe-rule-hyps-for-hyp
;;   (all-regular-function-callp (make-axe-rule-hyps-for-hyp hyp rule-symbol)))

;; Returns (mv processed-hyps bound-vars) where bound-vars is all the vars
;; bound in the LHS or when relieving hyps
(defund make-axe-rule-hyps (hyps bound-vars rule-symbol wrld acc)
  (declare (xargs :guard (and (pseudo-term-listp hyps)
                              (symbol-listp bound-vars)
                              (symbolp rule-symbol)
                              (true-listp acc)
                              (plist-worldp wrld))))
  (if (endp hyps)
      (mv (reverse-list acc) bound-vars)
    (b* ((hyp (first hyps))
         ((mv axe-rule-hyps bound-vars) (make-axe-rule-hyps-for-hyp hyp bound-vars rule-symbol wrld))
         (acc (append axe-rule-hyps acc)))
      (make-axe-rule-hyps (rest hyps) bound-vars rule-symbol wrld acc))))

;; (defthm all-consp-of-reverse-list
;;   (implies (all-consp acc)
;;            (all-consp (reverse-list acc)))
;;   :hints (("Goal" :in-theory (enable all-consp reverse-list))))

;; (defthm all-consp-of-make-axe-rule-hyps
;;   (implies (all-consp acc)
;;            (all-consp (mv-nth 0 (make-axe-rule-hyps hyps bound-vars rule-symbol acc))))
;;   :hints (("Goal" :in-theory (enable make-axe-rule-hyps))))

(defthm axe-rule-hyp-listp-of-make-axe-rule-hyps
  (implies (and (pseudo-term-listp hyps)
                (axe-rule-hyp-listp acc))
           (axe-rule-hyp-listp (mv-nth 0 (make-axe-rule-hyps hyps bound-vars rule-symbol wrld acc))))
  :hints (("Goal" :in-theory (enable make-axe-rule-hyps))))

;;move
(defthm pseudo-term-listp-of-reverse-list
  (equal (pseudo-term-listp (reverse-list acc))
         (pseudo-term-listp (true-list-fix acc)))
  :hints (("Goal" :in-theory (enable pseudo-term-listp reverse-list))))

;not true because of axe-bind-free.
;; (defthm pseudo-term-listp-of-mv-nth-0-of-make-axe-rule-hyps
;;   (implies (and (pseudo-term-listp hyps)
;;                 (pseudo-term-listp acc)
;;                 (true-listp acc))
;;            (pseudo-term-listp (mv-nth 0 (make-axe-rule-hyps hyps bound-vars rule-symbol wrld acc))))
;;   :hints (("Goal" :in-theory (enable make-axe-rule-hyps))))

(defthm symbol-listp-of-mv-nth-1-of-make-axe-rule-hyps
  (implies (and (symbol-listp bound-vars)
                (pseudo-term-listp hyps))
           (symbol-listp (mv-nth 1 (make-axe-rule-hyps hyps bound-vars rule-symbol wrld acc))))
  :hints (("Goal" :in-theory (enable make-axe-rule-hyps))))

(defthm true-listp-of-mv-nth-1-of-make-axe-rule-hyps
  (implies (true-listp bound-vars)
           (true-listp (mv-nth 1 (make-axe-rule-hyps hyps bound-vars rule-symbol wrld acc))))
  :hints (("Goal" :in-theory (enable make-axe-rule-hyps))))

;; ;TODO: Prove:
;; (defthm all-regular-function-callp-of-make-axe-rule-hyps
;;   (implies (all-regular-function-callp acc)
;;            (all-regular-function-callp (mv-nth 0 (make-axe-rule-hyps hyps bound-vars rule-symbol acc)))))

;; Note: the format of the rule when stored in a rule-alist or rule-world is different (see stored-axe-rulep).
;; TODO: Consider deprecating this in favor of the stored-rule format.
;; TODO: Allow this to return an error (causing the caller to skip the rule)?
(defund make-axe-rule (lhs rhs rule-symbol hyps extra-hyps print wrld)
  (declare (xargs :guard (and (axe-rule-lhsp lhs)
                              (pseudo-termp rhs)
                              (pseudo-term-listp hyps) ;; from the theorem
                              (axe-rule-hyp-listp extra-hyps) ;; already processed, don't bind any vars, for stopping loops
                              (symbolp rule-symbol)
                              (plist-worldp wrld))))
  (b* ((- (and print (cw "(Making Axe rule: ~x0.)~%" rule-symbol)))
       (lhs-vars (all-vars lhs))
       ((mv processed-hyps bound-vars) (make-axe-rule-hyps hyps lhs-vars rule-symbol wrld nil))
       (rhs-vars (all-vars rhs))
       ((when (not (subsetp-eq rhs-vars bound-vars)))
        (prog2$ (er hard? 'make-axe-rule "The RHS, ~x0, of rule ~x1 has free vars (namely, ~x2) that are not bound by the LHS or the hyps (which together bind ~x3)."
                    ;; todo: maybe return the lhs as the rhs here so that it has no free vars?
                    rhs rule-symbol (set-difference-eq rhs-vars bound-vars) bound-vars)
                (list lhs rhs rule-symbol (append extra-hyps processed-hyps)))))
    (list lhs rhs rule-symbol (append extra-hyps processed-hyps))))

(defthm len-of-make-axe-rule
  (equal (len (make-axe-rule lhs rhs rule-symbol hyps extra-hyps print wrld))
         4)
  :hints (("Goal" :in-theory (enable make-axe-rule))))

(defthm rule-lhs-of-make-axe-rule
  (equal (rule-lhs (make-axe-rule lhs rhs rule-symbol hyps extra-hyps print wrld))
         lhs)
  :hints (("Goal" :in-theory (enable rule-lhs make-axe-rule))))

(defthm rule-rhs-of-make-axe-rule
  (equal (rule-rhs (make-axe-rule lhs rhs rule-symbol hyps extra-hyps print wrld))
         rhs)
  :hints (("Goal" :in-theory (enable rule-rhs make-axe-rule))))

(defthm rule-symbol-of-make-axe-rule
  (equal (rule-symbol (make-axe-rule lhs rhs rule-symbol hyps extra-hyps print wrld))
         rule-symbol)
  :hints (("Goal" :in-theory (enable rule-symbol make-axe-rule))))

;gross?
(defthm rule-hyps-of-make-axe-rule
  (equal (rule-hyps (make-axe-rule lhs rhs rule-symbol hyps extra-hyps print wrld))
         (append extra-hyps (mv-nth 0 (make-axe-rule-hyps hyps (all-vars lhs) rule-symbol wrld nil))))
  :hints (("Goal" :in-theory (enable rule-hyps make-axe-rule))))

(defthm axe-rulep-of-make-axe-rule
  (implies (and (axe-rule-lhsp lhs)
                (pseudo-termp rhs)
                (pseudo-term-listp hyps)
                (axe-rule-hyp-listp extra-hyps)
                (symbolp rule-symbol))
           (axe-rulep (make-axe-rule lhs rhs rule-symbol hyps extra-hyps print wrld)))
  :hints (("Goal" :in-theory (enable axe-rulep))))

;;Returns (mv erp lhs rhs).
(defund lhs-and-rhs-of-conc (conc rule-symbol known-boolean-fns)
  (declare (xargs :guard (and (pseudo-termp conc)
                              (symbolp rule-symbol)
                              (symbol-listp known-boolean-fns))))
  (if (atom conc)
      (prog2$ (er hard? 'lhs-and-rhs-of-conc "Unexpected form (atom) of conclusion ~x0 in rule ~x1" conc rule-symbol)
              (mv t nil nil))
    (b* ((fn (ffn-symb conc)))
      (if (eq 'equal fn)
          (if (not (consp (farg1 conc))) ;probably always true, since rewrite rules must have function calls on the lhs)
              (prog2$ (er hard? 'lhs-and-rhs-of-conc "Unexpected form (not a cons) of LHS ~x0 in rule ~x1" (farg1 conc) rule-symbol)
                      (mv t nil nil))
            (if (eq 'quote (ffn-symb (farg1 conc)))
                (prog2$ (er hard? 'lhs-and-rhs-of-conc "Unexpected form (quoted thing) of LHS ~x0 in rule ~x1" (farg1 conc) rule-symbol)
                        (mv t nil nil))
              (if (symbolp (ffn-symb (farg1 conc)))
                  ;;(equal (<function> ...) ...): ;fixme what about lambdas?
                  (mv nil (expand-lambdas-in-term (farg1 conc)) (farg2 conc))
                (prog2$ (er hard? 'lhs-and-rhs-of-conc "Unexpected form of conclusion ~x0 in rule ~x1" conc rule-symbol)
                        (mv t nil nil)))))
        (if (eq 'not fn)
            (if (and (consp (farg1 conc)) ;; (these are probably always true, since rewrite rules must have function calls on the lhs
                     (symbolp (ffn-symb (farg1 conc)))
                     (not (eq 'quote (ffn-symb (farg1 conc)))))
                ;; (not (<function> ..)):
                ;;(not x) is the same as (equal x 'nil):
                (mv nil (expand-lambdas-in-term (farg1 conc)) *nil*)
              (prog2$ (er hard? 'lhs-and-rhs-of-conc "Unexpected form of conclusion ~x0 in rule ~x1" conc rule-symbol)
                      (mv t nil nil)))
          (if (eq 'quote fn)
              (prog2$ (er hard? 'lhs-and-rhs-of-conc "Unexpected form (quoted constant) of conclusion ~x0 in rule ~x1" conc rule-symbol)
                      (mv t nil nil))
            (if (member-eq fn known-boolean-fns)
                ;; pred -> (equal pred 't)
                (mv nil (expand-lambdas-in-term conc) *t*)
              (prog2$ (er hard? 'lhs-and-rhs-of-conc "Unexpected form of conclusion (not an equality, a call of not, or a call of a known-boolean) ~x0 in rule ~x1" conc rule-symbol)
                      (mv t nil nil)))))))))

(defthm axe-rule-lhsp-of-mv-nth-1-of-lhs-and-rhs-of-conc
  (implies (and (not (mv-nth 0 (lhs-and-rhs-of-conc conc rule-symbol known-boolean-fns)))
                (symbol-listp known-boolean-fns) ;drop?
                (pseudo-termp conc))
           (axe-rule-lhsp (mv-nth 1 (lhs-and-rhs-of-conc conc rule-symbol known-boolean-fns))))
  :hints (("Goal"  :expand ((expand-lambdas-in-term conc))
           :in-theory (enable lhs-and-rhs-of-conc axe-rule-lhsp))))

;; (defthm lambda-free-termp-of-mv-nth-1-of-lhs-and-rhs-of-conc
;;   (implies (and (not (mv-nth 0 (lhs-and-rhs-of-conc conc rule-symbol known-boolean-fns)))
;;                 (pseudo-termp conc))
;;            (lambda-free-termp (mv-nth 1 (lhs-and-rhs-of-conc conc rule-symbol known-boolean-fns))))
;;   :hints (("Goal" :in-theory (enable lhs-and-rhs-of-conc))))

;; (defthm pseudo-termp-of-mv-nth-1-of-lhs-and-rhs-of-conc
;;   (implies (and (not (mv-nth 0 (lhs-and-rhs-of-conc conc rule-symbol known-boolean-fns)))
;;                 (pseudo-termp conc))
;;            (pseudo-termp (mv-nth 1 (lhs-and-rhs-of-conc conc rule-symbol known-boolean-fns))))
;;   :hints (("Goal" :in-theory (enable lhs-and-rhs-of-conc))))

;; (defthm symbolp-of-car-of-mv-nth-1-of-lhs-and-rhs-of-conc
;;   (implies (and (not (mv-nth 0 (lhs-and-rhs-of-conc conc rule-symbol known-boolean-fns)))
;;                 (symbol-listp known-boolean-fns)
;;                 (pseudo-termp conc))
;;            (symbolp (car (mv-nth 1 (lhs-and-rhs-of-conc conc rule-symbol known-boolean-fns)))))
;;   :hints (("Goal" :expand ((expand-lambdas-in-term conc))
;;            :in-theory (enable lhs-and-rhs-of-conc))))

;; (defthm consp-of-mv-nth-1-of-lhs-and-rhs-of-conc
;;   (implies (and (not (mv-nth 0 (lhs-and-rhs-of-conc conc rule-symbol known-boolean-fns)))
;;                 (symbol-listp known-boolean-fns)
;;                 (pseudo-termp conc))
;;            (consp (mv-nth 1 (lhs-and-rhs-of-conc conc rule-symbol known-boolean-fns))))
;;   :hints (("Goal" :expand ((expand-lambdas-in-term conc))
;;            :in-theory (enable lhs-and-rhs-of-conc))))

;; ;; (defthm not-equal-of-quote-and-car-of-mv-nth-1-of-lhs-and-rhs-of-conc
;; ;;   (implies (and (not (mv-nth 0 (lhs-and-rhs-of-conc conc rule-symbol known-boolean-fns)))
;; ;;                 (symbol-listp known-boolean-fns)
;; ;;                 (pseudo-termp conc))
;; ;;            (not (equal 'quote (car (mv-nth 1 (lhs-and-rhs-of-conc conc rule-symbol known-boolean-fns))))))
;; ;;   :hints (("Goal" :expand ((expand-lambdas-in-term conc))
;; ;;            :in-theory (enable lhs-and-rhs-of-conc))))

(defthm pseudo-termp-of-mv-nth-2-of-lhs-and-rhs-of-conc
  (implies (and (not (mv-nth 0 (lhs-and-rhs-of-conc conc rule-symbol known-boolean-fns)))
                (pseudo-termp conc))
           (pseudo-termp (mv-nth 2 (lhs-and-rhs-of-conc conc rule-symbol known-boolean-fns))))
  :hints (("Goal" :in-theory (enable lhs-and-rhs-of-conc))))



;;;
;;; axe-rule-listp
;;;

(defforall axe-rule-listp (items) (axe-rulep items) :true-listp t)
(verify-guards axe-rule-listp)

;fixme defforall should do this (but maybe disable it?)
(defthm axe-rulep-of-car-when-axe-rule-listp
  (implies (and (axe-rule-listp lst)
                (consp lst))
           (axe-rulep (car lst))))

(defund rule-symbol-list (rules)
  (declare (xargs :guard (axe-rule-listp rules)
                  :guard-hints (("Goal" :expand ((axe-rulep (car rules))) ;this is because rule-symbol is a macro?
                                 :in-theory (enable axe-rule-listp)))))
  (if (endp rules)
      nil
    (cons (rule-symbol (first rules))
          (rule-symbol-list (rest rules)))))

;possibly adds an axe-rule to acc
;fixme be more general?
(defund add-rule-for-conjunct (conc
                               hyps
                               extra-hyps
                               counter ;nil means this is the only conjunct of the rule
                               rule-symbol
                               known-boolean-fns
                               print
                               wrld
                               acc)
  (declare (xargs :guard (and (pseudo-termp conc)
                              (pseudo-term-listp hyps) ;from the theorem
                              (axe-rule-hyp-listp extra-hyps) ;already processed
                              (or (natp counter) (equal nil counter))
                              (symbolp rule-symbol)
                              (symbol-listp known-boolean-fns)
                              (plist-worldp wrld))))
  (b* (((mv erp lhs rhs) (lhs-and-rhs-of-conc conc rule-symbol known-boolean-fns)))
    (if erp
        acc ;don't extend acc
      (cons (make-axe-rule lhs rhs
                               (if counter
                                   ;; todo: make a pack-string and pass to add-suffix:
                                   (pack-in-package-of-symbol rule-symbol rule-symbol '-conjunct- (nat-to-string counter))
                                 rule-symbol)
                               hyps
                               extra-hyps
                               print
                               wrld)
            acc))))

(defthm symbolp-when-memberp
  (implies (and (memberp x free)
                (symbol-listp free))
           (symbolp x)))

(defthm axe-rule-listp-of-add-rule-for-conjunct
  (implies (and (symbolp rule-symbol)
                (pseudo-termp conc)
                (pseudo-term-listp hyps)
                (axe-rule-hyp-listp extra-hyps)
                (axe-rule-listp acc)
                (symbol-listp known-boolean-fns)
                )
           (axe-rule-listp (add-rule-for-conjunct conc hyps extra-hyps counter rule-symbol known-boolean-fns print wrld acc)))
  :hints (("Goal" :in-theory (e/d (;axe-rulep
                                   add-rule-for-conjunct) ()))))

(defthm true-listp-of-add-rule-for-conjunct
  (implies (true-listp acc)
           (true-listp (add-rule-for-conjunct conc hyps extra-hyps counter rule-symbol known-boolean-fns print wrld acc)))
  :hints (("Goal" :in-theory (e/d (add-rule-for-conjunct) (true-listp)))))

;; Returns an axe-rule-list.
(defund make-rules-from-conclusion-aux (conc hyps extra-hyps counter rule-symbol known-boolean-fns print wrld)
  (declare (xargs :guard (and (pseudo-termp conc)
                              (pseudo-term-listp hyps)
                              (axe-rule-hyp-listp extra-hyps) ;already processed
                              (natp counter)
                              (symbolp rule-symbol)
                              (symbol-listp known-boolean-fns)
                              (plist-worldp wrld))))
  (if (atom conc)
      (er hard? 'make-rules-from-conclusion-aux "Unexpected form (atom) of a conclusion for ~x0" conc)
    (if (eq 'if (ffn-symb conc))
        ;;it's an AND (represented as (if <x> <y> 'nil), of course):
        ;;fffixme handle booland??!
        (if (equal *nil* (farg3 conc))
            (add-rule-for-conjunct (farg1 conc) hyps extra-hyps counter rule-symbol known-boolean-fns print wrld
                                   (make-rules-from-conclusion-aux (farg2 conc) hyps extra-hyps (+ 1 counter) rule-symbol known-boolean-fns print wrld))
          ;;the guard on this is nil?
          ;;ffixme what about lambdas?
          (er hard? 'make-rules-from-conclusion-aux "Unexpected form of a conclusion: ~x0" conc))
      (add-rule-for-conjunct conc hyps extra-hyps counter rule-symbol known-boolean-fns print wrld nil))))

(defthm axe-rule-listp-of-make-rules-from-conclusion-aux
  (implies (and (symbolp rule-symbol)
                (pseudo-termp conc)
                (pseudo-term-listp hyps)
                (axe-rule-hyp-listp extra-hyps)
                (symbol-listp known-boolean-fns))
           (axe-rule-listp (make-rules-from-conclusion-aux conc hyps extra-hyps counter rule-symbol known-boolean-fns print wrld)))
  :hints (("Goal" :in-theory (enable axe-rulep make-rules-from-conclusion-aux))))

(defthm true-listp-of-make-rules-from-conclusion-aux
  (true-listp (make-rules-from-conclusion-aux conc hyps extra-hyps counter rule-symbol known-boolean-fns print wrld))
  :hints (("Goal" :in-theory (enable axe-rulep make-rules-from-conclusion-aux))))

;; Returns an axe-rule-list.
;fixme pass in a rule symbol only?
(defund make-rules-from-conclusion (conc hyps extra-hyps rule-symbol known-boolean-fns print wrld)
  (declare (xargs :guard (and (pseudo-termp conc)
                              (pseudo-term-listp hyps) ;from the theorem
                              (axe-rule-hyp-listp extra-hyps) ;already processed
                              (symbolp rule-symbol)
                              (symbol-listp known-boolean-fns)
                              (plist-worldp wrld))))
  (if (call-of 'if conc)
      ;;the rules will be tagged with the conjunct number:
      (make-rules-from-conclusion-aux conc hyps extra-hyps 1 rule-symbol known-boolean-fns print wrld)
    ;;there is only one conclusion:
    (add-rule-for-conjunct conc hyps extra-hyps nil rule-symbol known-boolean-fns print wrld nil)))

(defthm axe-rule-listp-of-make-rules-from-conclusion
  (implies (and (symbolp rule-symbol)
                (pseudo-termp conc)
                (pseudo-term-listp hyps)
                (axe-rule-hyp-listp extra-hyps)
                (symbol-listp known-boolean-fns))
           (axe-rule-listp (make-rules-from-conclusion conc hyps extra-hyps rule-symbol known-boolean-fns print wrld)))
  :hints (("Goal" :in-theory (enable make-rules-from-conclusion axe-rulep))))

(defthm true-listp-of-make-rules-from-conclusion
  (true-listp (make-rules-from-conclusion conc hyps extra-hyps rule-symbol known-boolean-fns print wrld))
  :hints (("Goal" :in-theory (e/d (make-rules-from-conclusion) (axe-rulep)))))

;;TTODO: How can we access the auto-generated loop stopper that ACL2 sometimes puts in?
(defund make-axe-rule-hyp-for-loop-stopper (loop-stopper rule-name)
  (declare (xargs :guard t)
           (ignore rule-name))
  (if (and (true-listp loop-stopper)
           (<= 2 (len loop-stopper))
           (symbolp (first loop-stopper))
           (symbolp (second loop-stopper)))
      ;;a loop-stopper of (x y) means y must be smaller than x for the rule to fire
      (let ((loop-stopper `(axe-syntaxp (heavier-dag-term ,(first loop-stopper) ,(second loop-stopper)))))
        (prog2$ nil ;(cw "Note: inserting loop stopper ~x0 for rule ~x1.~%" loop-stopper rule-name)
                loop-stopper)) ;TODO: get the invisible fns and have heavier-dag-term (or a variant of it) ignore them
    (prog2$ (er hard? 'make-axe-rule-hyp-for-loop-stopper "Unrecognized loop stopper: ~x0." loop-stopper)
            *unrelievable-hyp*)))

(defthm axe-rule-hypp-of-make-axe-rule-hyp-for-loop-stopper
  (axe-rule-hypp (make-axe-rule-hyp-for-loop-stopper loop-stopper rule-name))
  :hints (("Goal" :in-theory (enable axe-rule-hypp make-axe-rule-hyp-for-loop-stopper
                                     axe-syntaxp-exprp axe-syntaxp-function-applicationp
                                     list-of-variables-and-constantsp))))

(defund make-axe-rule-hyps-for-loop-stoppers (loop-stoppers rule-name)
  (declare (xargs :guard t))
  (if (atom loop-stoppers)
      nil
    (cons (make-axe-rule-hyp-for-loop-stopper (first loop-stoppers) rule-name)
          (make-axe-rule-hyps-for-loop-stoppers (rest loop-stoppers) rule-name))))

(defthm axe-rule-hyp-listp-of-make-axe-rule-hyps-for-loop-stoppers
  (axe-rule-hyp-listp (make-axe-rule-hyps-for-loop-stoppers loop-stoppers rule-name))
  :hints (("Goal" :in-theory (enable make-axe-rule-hyps-for-loop-stoppers))))

;; TODO: Should we get anything else from the :rule-classes in addition to the loop-stoppers?  Check for unknown things?
;; These do not bind any vars
(defund make-axe-rule-loop-stopping-hyps (rule-classes rule-name)
  (declare (xargs :guard t))
  (b* (((when (not (alistp rule-classes)))
        (er hard? 'make-axe-rule-loop-stopping-hyps "Bad rule-classes: ~x0" rule-classes))
       (rewrite-keyword-value-list (lookup-eq :rewrite rule-classes))
       ((when (not (keyword-value-listp rewrite-keyword-value-list)))
        (er hard? 'make-axe-rule-loop-stopping-hyps "Unexpected stuff in :rewrite rule class: ~x0." rewrite-keyword-value-list))
       (loop-stoppers (cadr (assoc-keyword :loop-stopper rewrite-keyword-value-list)))) ;we only look at :rewrite rules to get the loop-stoppers
    (make-axe-rule-hyps-for-loop-stoppers loop-stoppers rule-name)))

(defthm axe-rule-hyp-listp-of-make-axe-rule-loop-stopping-hyps
  (axe-rule-hyp-listp (make-axe-rule-loop-stopping-hyps rule-classes rule-symbol))
  :hints (("Goal" :in-theory (enable make-axe-rule-loop-stopping-hyps))))

;; Returns (mv erp axe-rules).
(defund make-rules-from-theorem (theorem-body rule-symbol rule-classes known-boolean-fns print wrld)
  (declare (xargs :guard (and (pseudo-termp theorem-body)
                              (symbolp rule-symbol)
                              (symbol-listp known-boolean-fns)
                              (plist-worldp wrld))))
  ;; Split the rule into conclusion and hyps
  (b* (((mv erp hyps conc)
        (hyps-and-conc-for-axe-rule theorem-body rule-symbol))
       ((when erp) (mv erp nil)))
    ;; We can't process the hyps yet because we don't know the LHS vars (there
    ;; may be several LHSes).  It's okay to ignore the loop-stopping-hyps when
    ;; processing other hyps because the loop-stopping-hyps do not bind any
    ;; vars.
    (let ((extra-hyps (make-axe-rule-loop-stopping-hyps rule-classes rule-symbol)))
      ;; the conclusion may have multiple conjuncts:
      (mv (erp-nil)
          (make-rules-from-conclusion conc hyps extra-hyps rule-symbol known-boolean-fns print wrld)))))

;; Returns the axe-rules.  Does not return erp.
(defund make-rules-from-theorem! (theorem-body rule-symbol rule-classes known-boolean-fns print wrld)
  (declare (xargs :guard (and (pseudo-termp theorem-body)
                              (symbolp rule-symbol)
                              (symbol-listp known-boolean-fns)
                              (plist-worldp wrld))))
  (mv-let (erp axe-rules)
    (make-rules-from-theorem theorem-body rule-symbol rule-classes known-boolean-fns print wrld)
    (if erp
        (er hard? 'make-rules-from-theorem! "Error making Axe rules.")
      axe-rules)))


(defthm axe-rule-listp-of-mv-nth-1-of-make-rules-from-theorem
  (implies (and (pseudo-termp theorem-body)
                (symbolp rule-symbol)
                (symbol-listp known-boolean-fns))
           (axe-rule-listp (mv-nth 1 (make-rules-from-theorem theorem-body rule-symbol rule-classes known-boolean-fns print wrld))))
  :hints (("Goal" :in-theory (enable make-rules-from-theorem
                                     axe-rulep ;fixme
                                     ))))

(defthm true-listp-of-mv-nth-1-of-make-rules-from-theorem
  (true-listp (mv-nth 1 (make-rules-from-theorem theorem-body rule-symbol rule-classes known-boolean-fns print wrld)))
  :hints (("Goal" :in-theory (e/d (make-rules-from-theorem) ()))))

(defthm plist-world-of-cdr-of-assoc-equal-etc
  (implies (state-p1 state)
           (plist-worldp (cdr (assoc-equal 'current-acl2-world
                                           (nth 2 state)))))
  :hints (("Goal" :in-theory (enable state-p1))))

;; (mutual-recursion
;;  (defun strip-return-last (term)
;;    (declare (xargs :guard (pseudo-termp term)))
;;    (if (atom term)
;;        term
;;      (let ((fn (ffn-symb term)))
;;        (if (eq 'quote fn)
;;            term
;;          (if (and (eq 'return-last fn) ;replace with the last arg (suitably fixed up)
;;                   (eql 3 (len (fargs term))))
;;              (strip-return-last (caddr (fargs term)))
;;            ;; first fixup the args
;;            (let ((args (strip-return-last-list (fargs term)))
;;                  (fn (if (consp fn)
;;                          (let* ((formals (cadr fn))
;;                                 (body (caddr fn))
;;                                 (body (strip-return-last body)))
;;                            `(lambda ,formals ,body))
;;                        fn)))
;;              `(,fn ,@args)))))))

;;  (defun strip-return-last-list (terms)
;;    (declare (xargs :guard (pseudo-term-listp terms)))
;;    (if (endp terms)
;;        nil
;;      (cons (strip-return-last (first terms))
;;            (strip-return-last-list (rest terms))))))


;; (my-make-flag strip-return-last)

;; (defthm len-of-strip-return-last-list
;;   (equal (len (strip-return-last-list terms))
;;          (len terms))
;;   :hints (("Goal" :in-theory (enable len))))

;; (DEFTHM-FLAG-STRIP-RETURN-LAST
;;   (DEFTHM pseudo-termp-of-STRIP-RETURN-LAST
;;     (IMPLIES (pseudo-termp term)
;;              (pseudo-termp (STRIP-RETURN-LAST TERM)))
;;     :FLAG STRIP-RETURN-LAST)
;;   (DEFTHM pseudo-term-listp-of-STRIP-RETURN-LAST-LIST
;;     (IMPLIES (pseudo-term-listp terms)
;;              (pseudo-term-listp (STRIP-RETURN-LAST-LIST TERMS)))
;;     :FLAG STRIP-RETURN-LAST-LIST))

;; Returns (mv erp new-acc) where new-acc extends acc.
;keep in sync with check-that-rule-is-known
(defund add-axe-rules-for-rule (rule-name known-boolean-fns print acc wrld)
  (declare (xargs :guard (and (symbolp rule-name)
                              (symbol-listp known-boolean-fns)
                              (ilks-plist-worldp wrld))))
  (b* (((when (eq 'quote rule-name))
        (er hard? 'add-axe-rules-for-rule "QUOTE is an illegal name for an Axe rule.")
        (mv :bad-rule-name acc))
       ;;(rule-class (first rule-name))
       ;;(name (second rule-name))
       (name rule-name)
       (theoremp (theorem-symbolp rule-name wrld))
       (functionp (function-symbolp rule-name wrld)))
    (cond ((and (not functionp)
                (not theoremp))
           (prog2$ (er hard? 'add-axe-rules-for-rule "~x0 does not seem to be a theorem or defun." rule-name)
                   (mv :rule-not-found acc)))
          ((and functionp theoremp)
           (prog2$ (er hard? 'add-axe-rules-for-rule "Rule-Name ~x0 appears to be both a function and a theorem (so which is it?!)" name)
                   (mv :confusing-rule-name acc)))
          (functionp
           ;;it's a defun:
           (let* ((formals (fn-formals rule-name wrld))
                  (body (fn-body rule-name t wrld))
                  ;; If we don't handle return-last, the axe rule for
                  ;; string-append causes a loop.  Also, this should make it
                  ;; faster to open functions defined using MBE:
                  (body (remove-guard-holders-weak body) ;(strip-return-last body)
                        )
                  (body (drop-unused-lambda-bindings body))
                  (lhs (cons name formals)))
             ;;ffixme for recursive functions, we could generate separate cases for the recursive case and the base case (really, defopeners should be used)...
             (mv (erp-nil)
                 (cons (make-axe-rule lhs body name nil nil print wrld)
                       acc))))
          (t ;;it's a theorem:
           (b* ((theorem-body (defthm-body rule-name wrld))
                (rule-classes (defthm-rule-classes name wrld))
                ;;otherwise, unrolling rules of functions using mbe can loop):
                (theorem-body ;(strip-return-last theorem-body)
                 (remove-guard-holders-weak theorem-body))
                (theorem-body (drop-unused-lambda-bindings theorem-body))
                ((mv erp rules)
                 (make-rules-from-theorem theorem-body name rule-classes known-boolean-fns print wrld))
                ((when erp) (mv erp acc)))
             (mv (erp-nil)
                 (append rules acc)))))))

(defthm axe-rule-listp-of-mv-nth-1-of-add-axe-rules-for-rule
  (implies (and (axe-rule-listp acc)
                (symbolp rule-name)
                (symbol-listp known-boolean-fns))
           (axe-rule-listp (mv-nth 1 (add-axe-rules-for-rule rule-name known-boolean-fns print acc wrld))))
  :hints (("Goal" :in-theory (enable ADD-AXE-RULES-FOR-RULE axe-rulep))))

(defthm true-listp-of-mv-nth-1-of-add-axe-rules-for-rule
  (implies (true-listp acc)
           (true-listp (mv-nth 1 (add-axe-rules-for-rule rule-name known-boolean-fns print acc wrld))))
  :hints (("Goal" :in-theory (enable add-axe-rules-for-rule))))

;; For each of the RULE-NAMES, look it up in the world and add one or more rules for it to ACC.
;; Returns (mv erp rules) where rules is a list of axe-rules.
(defund make-axe-rules-aux (rule-names known-boolean-fns print acc wrld)
  (declare (xargs :guard (and (symbol-listp rule-names)
                              (true-listp acc)
                              (symbol-listp known-boolean-fns)
                              (ilks-plist-worldp wrld))))
  (if (endp rule-names)
      (mv (erp-nil) (reverse acc)) ;skip this reverse! or call a better version of it that doesn't handle strings?
    (b* (((mv erp res)
          (add-axe-rules-for-rule (first rule-names) known-boolean-fns print acc wrld))
         ((when erp) (mv erp acc)))
      (make-axe-rules-aux (rest rule-names) known-boolean-fns print
                          res
                          wrld))))

(defthm true-listp-of-mv-nth-1-of-make-axe-rules-aux
  (implies (true-listp acc)
           (true-listp (mv-nth 1 (make-axe-rules-aux rule-names known-boolean-fns print acc wrld))))
  :hints (("Goal" :in-theory (enable make-axe-rules-aux))))

(defthm axe-rule-listp-of-mv-nth-1-of-make-axe-rules-aux
  (implies (and (axe-rule-listp acc)
                (true-listp acc)
                (symbol-listp rule-names)
                (symbol-listp known-boolean-fns))
           (axe-rule-listp (mv-nth 1 (make-axe-rules-aux rule-names known-boolean-fns print acc wrld))))
  :hints (("Goal" :in-theory (enable make-axe-rules-aux))))

;; Returns (mv erp rules) where rules is a list of axe-rules.
(defund make-axe-rules (rule-names wrld)
  (declare (xargs :guard (and (symbol-listp rule-names)
                              (ilks-plist-worldp wrld))))
  (make-axe-rules-aux rule-names (known-booleans wrld) nil nil wrld))

(defthm true-listp-of-mv-nth-1-of-make-axe-rules
  (true-listp (mv-nth 1 (make-axe-rules rules wrld)))
  :hints (("Goal" :in-theory (enable make-axe-rules))))

(defthm axe-rule-listp-of-mv-nth-1-of-make-axe-rules
  (implies (symbol-listp rule-names)
           (axe-rule-listp (mv-nth 1 (make-axe-rules rule-names wrld))))
  :hints (("Goal" :in-theory (enable make-axe-rules))))

;; This variant doesn't pass back an error
(defund make-axe-rules! (rule-names wrld)
  (declare (xargs :guard (and (symbol-listp rule-names)
                              (ilks-plist-worldp wrld))))
  (mv-let (erp axe-rules)
    (make-axe-rules rule-names wrld)
    (if erp
        (er hard? 'make-axe-rules! "Error making Axe rules.")
      axe-rules)))

;; Returns (mv erp rules) where rules is a list of axe-rules.
;; This version removes duplicate rules first.  (That may happen later anyway
;; when making the rule-alist...).
(defund make-axe-rules2 (rule-names wrld)
  (declare (xargs :guard (and (symbol-listp rule-names)
                              (ilks-plist-worldp wrld))))
  (make-axe-rules (remove-duplicates-eq rule-names) ;slow?  use property worlds to speed up?
                  wrld))

;; Returns (mv erp rules) where rules is a list of axe-rules.
(defun add-rules-to-rule-set (rules rule-set wrld)
  (declare (xargs :guard (and (symbol-listp rules)
                              (axe-rule-listp rule-set)
                              (ilks-plist-worldp wrld))))
  (b* (((mv erp rules) (make-axe-rules rules wrld))
       ((when erp) (mv erp rule-set)))
    (mv (erp-nil)
        (union-equal rules rule-set))))

(defforall-simple axe-rule-listp)
(verify-guards all-axe-rule-listp)

;; Recognize a true-list of axe-rule-sets.
(defun axe-rule-setsp (items)
  (declare (xargs :guard t))
  (and (all-axe-rule-listp items)
       (true-listp items)))

;; Returns (mv erp rule-sets).
;; Add the RULES to each rule set in RULE-SETS.
;todo: optimze?
(defun add-rules-to-rule-sets (rules rule-sets wrld)
  (declare (xargs :guard (and (symbol-listp rules)
                              (axe-rule-setsp rule-sets)
                              (ilks-plist-worldp wrld))))
  (if (endp rule-sets)
      (mv (erp-nil) nil)
    (b* (((mv erp first-rule-set)
          (add-rules-to-rule-set rules (first rule-sets) wrld))
         ((when erp) (mv erp nil))
         ((mv erp rest-rule-sets)
          (add-rules-to-rule-sets rules (rest rule-sets) wrld))
         ((when erp) (mv erp nil)))
      (mv (erp-nil)
          (cons first-rule-set
                rest-rule-sets)))))

;; Returns the new rule-sets.  Does not return erp.
(defun add-rules-to-rule-sets! (rules rule-sets wrld)
  (mv-let (erp rule-sets)
    (add-rules-to-rule-sets rules rule-sets wrld)
    (if erp
        (er hard? 'add-rules-to-rule-sets! "Error adding rules to rule-sets.")
      rule-sets)))

;; Add the RULES to each rule set in RULE-SETS.
;todo: optimze?
(defun add-axe-rules-to-rule-sets (axe-rules rule-sets)
  (declare (xargs :guard (and (axe-rule-listp axe-rules)
                              (axe-rule-setsp rule-sets))))
  (if (endp rule-sets)
      nil
    (cons (union-equal axe-rules (first rule-sets))
          (add-axe-rules-to-rule-sets axe-rules (rest rule-sets)))))

;; (defun remove-rule-from-rule-set (rule rule-set)
;;   (declare (xargs :guard (and (symbolp rule)
;;                               (axe-rule-listp rule-set))
;;                   :guard-hints (("Goal" :expand (axe-rule-listp rule-set)
;;                                  :in-theory (enable axe-rulep)))))
;;   (if (endp rule-set)
;;       nil
;;     (if (eq rule (rule-symbol (first rule-set)))
;;         (remove-rule-from-rule-set rule (rest rule-set)) ;could stop here if we know there are no dups
;;       (cons (first rule-set)
;;             (remove-rule-from-rule-set rule (rest rule-set))))))

;; (defun remove-rules-from-rule-set (rules rule-set)
;;   (declare (xargs :guard (and (symbol-listp rules)
;;                               (true-listp rules)
;;                               (axe-rule-listp rule-set))))
;;   (if (endp rules)
;;       rule-set
;;     (remove-rules-from-rule-set (rest rules)
;;                                 (remove-rule-from-rule-set (first rules) rule-set))))

;; ;; Remove the RULES from each rule set in RULE-SETS.
;; ;todo: optimze?
;; (defun remove-rules-from-rule-sets (rules rule-sets)
;;   (declare (xargs :guard (and (symbol-listp rules)
;;                               (true-listp rules)
;;                               (axe-rule-setsp rule-sets))))
;;   (if (endp rule-sets)
;;       nil
;;     (cons (remove-rules-from-rule-set rules (first rule-sets))
;;           (remove-rules-from-rule-sets rules (rest rule-sets)))))
