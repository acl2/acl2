; Making Axe rules and rule-alists from formulas
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2024 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/alists-light/lookup-eq" :dir :system)
(include-book "kestrel/utilities/world" :dir :system) ; reduce?
(include-book "kestrel/utilities/terms" :dir :system)
;(include-book "../utilities/basic")
;(include-book "kestrel/terms-light/drop-unused-lambda-bindings" :dir :system)
(include-book "kestrel/terms-light/pre-simplify-term" :dir :system)
(include-book "kestrel/utilities/conjunctions" :dir :system)
(include-book "kestrel/utilities/conjuncts-and-disjuncts2" :dir :system)
(include-book "kestrel/utilities/quote" :dir :system)
(include-book "kestrel/utilities/remove-guard-holders" :dir :system)
;(include-book "kestrel/typed-lists-light/all-consp" :dir :system)
(include-book "known-booleans")
(include-book "axe-rule-lists")
(include-book "axe-syntax") ;since this book knows about axe-syntaxp and axe-bind-free
(include-book "kestrel/world-light/defthm-or-defaxiom-symbolp" :dir :system)
(include-book "kestrel/utilities/erp" :dir :system)
(include-book "kestrel/sequences/defforall" :dir :system) ; todo: reduce
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/union-equal" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))
(local (include-book "kestrel/lists-light/reverse" :dir :system))
(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/lists-light/take" :dir :system))
(local (include-book "kestrel/lists-light/reverse-list" :dir :system))
(local (include-book "kestrel/utilities/equal-of-booleans" :dir :system))
(local (include-book "kestrel/lists-light/member-equal" :dir :system))
(local (include-book "kestrel/lists-light/set-difference-equal" :dir :system))
(local (include-book "kestrel/lists-light/subsetp-equal" :dir :system))
(local (include-book "kestrel/typed-lists-light/symbol-listp" :dir :system))
(local (include-book "kestrel/alists-light/symbol-alistp" :dir :system))
(local (include-book "kestrel/alists-light/strip-cdrs" :dir :system))
(local (include-book "kestrel/utilities/pseudo-termp" :dir :system))
(local (include-book "kestrel/typed-lists-light/pseudo-term-listp" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/terms-light/all-fnnames1" :dir :system))
;(local (include-book "kestrel/terms-light/pre-simplify-term-proofs" :dir :system))

(local
 (in-theory (disable ilks-plist-worldp
                     plist-worldp
                     set-difference-equal intersection-equal symbol-listp true-listp ;prevent inductions
                     )))

(local
 (defthmd not-equal-of-car-when-not-member-equal-of-fns-in-term
   (implies (and (not (member-equal a (fns-in-term x)))
                 (consp x)
                ;(pseudo-termp x)
                 (not (equal 'quote a))
                 (not (consp a))
                 )
            (not (equal a (car x))))
   :hints (("Goal" :expand (fns-in-term x)
            :in-theory (enable fns-in-term)))))

(local
 (defthm not-member-equal-of-fns-in-term-of-expand-lambdas-in-term
   (implies (and (pseudo-termp term)
                 (not (member-equal fn (fns-in-term term))))
            (not (member-equal fn (fns-in-term (expand-lambdas-in-term term)))))
   :hints (("Goal" :use (:instance not-member-equal-of-fns-in-term-of-expand-lambdas-in-term)
            :in-theory (disable not-member-equal-of-fns-in-term-of-expand-lambdas-in-term)))))

;; (local
;;  (defthm not-memberp-of-fns-in-term-of-cadr
;;    (implies (and (not (memberp fn (fns-in-term x)))
;;                  (not (equal 'quote (car x))))
;;             (not (memberp fn (fns-in-term (car (cdr x))))))
;;    :hints (("Goal" :expand (fns-in-term x)
;;             :in-theory (enable fns-in-term)))))

;(local (in-theory (disable pairlis$))) ;prevent inductions

(defthm plist-worldp-of-cdr-of-assoc-equal-etc
  (implies (state-p1 state)
           (plist-worldp (cdr (assoc-equal 'current-acl2-world
                                           (nth 2 state)))))
  :hints (("Goal" :in-theory (enable state-p1))))

;move
(defthm free-vars-in-terms-when-equal-of-0-and-len
  (implies (equal 0 (len terms))
           (equal (free-vars-in-terms terms)
                  nil))
  :hints (("Goal" :in-theory (enable free-vars-in-terms))))

;; (defthm all-vars-of-cons
;;   (equal (all-vars (cons fn args))
;;          (if (eq fn 'quote)
;;              nil
;;            (all-vars1-lst args nil)))
;;   :hints (("Goal" :in-theory (enable all-vars))))

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
;;           (cons `(:AXE-SYNTAXP (axe-QUOTEP-FN ,(first (fargs conjunct))))
;;                 (process-syntaxp-conjuncts (cdr conjuncts)))
;;         (prog2$ (er hard? 'process-syntaxp-conjuncts "unrecognized argument to syntaxp: ~x0.  we only support quotep."
;;                             conjunct)
;;                 (cons ''nil ;so that it never matches..
;;                       (process-syntaxp-conjuncts (cdr conjuncts))))))))

;; (skip -proofs (verify-guards process-syntaxp-conjuncts))

;; Returns (mv erp processed-argument).
;;sample inputs: (QUOTEP SHIFT-AMOUNT), (NOT (QUOTEP X)), (IF (QUOTEP K) (QUOTEP SIZE) 'NIL)
;;handles a nest of IFs and NOTs with constants and calls to quotep at the leaves
(defund convert-syntaxp-argument-for-axe (term rule-symbol)
  (declare (xargs :guard (pseudo-termp term)))
  (if (not (consp term)) ;;maybe it's okay to allow a variable here?
      (prog2$ (er hard? 'convert-syntaxp-argument-for-axe "unexpected term, ~x0, in syntaxp hyp in rule ~x1." term rule-symbol)
              (mv (erp-t) nil))
    (if (myquotep term) ;quoted constant (may arise from the translation of an IF)
        (mv (erp-nil) term)
      (let ((fn (ffn-symb term)))
        (if (and (eq 'quotep fn) ; (quotep <var>)
                 (= 1 (len (fargs term)))
                 (symbolp (first (fargs term)))
                 ;; (not (eq 'dag-array (first (fargs term)))) ;todo: think about this?
                 )
            ;; Converts quotep to axe-quotep (faster):
            (mv (erp-nil) `(axe-quotep ,(first (fargs term))))
          (if (eq fn 'if)
              (b* (((mv erp processed-test) (convert-syntaxp-argument-for-axe (farg1 term) rule-symbol))
                   ((when erp) (mv erp nil))
                   ((mv erp processed-then) (convert-syntaxp-argument-for-axe (farg2 term) rule-symbol))
                   ((when erp) (mv erp nil))
                   ((mv erp processed-else) (convert-syntaxp-argument-for-axe (farg3 term) rule-symbol))
                   ((when erp) (mv erp nil)))
                (mv (erp-nil) `(if ,processed-test ,processed-then ,processed-else)))
            (if (eq fn 'not)
                (b* (((mv erp processed-arg) (convert-syntaxp-argument-for-axe (farg1 term) rule-symbol))
                     ((when erp) (mv erp nil)))
                  (mv (erp-nil) `(not ,processed-arg)))
              (prog2$ (er hard? 'convert-syntaxp-argument-for-axe "unexpected term, ~x0, in syntaxp hyp in rule ~x1." term rule-symbol)
                      (mv (erp-t) nil)))))))))

(local
 (defthm pseudo-termp-of-mv-nth-1-of-convert-syntaxp-argument-for-axe
   (implies (pseudo-termp term)
            (pseudo-termp (mv-nth 1 (convert-syntaxp-argument-for-axe term rule-symbol))))
   :hints (("Goal" :in-theory (enable convert-syntaxp-argument-for-axe)))))

(local
 (defthm axe-syntaxp-exprp-of-mv-nth-1-of-convert-syntaxp-argument-for-axe
   (implies (and (pseudo-termp conjunct)
                 (not (mv-nth 0 (convert-syntaxp-argument-for-axe conjunct rule-symbol))))
            (axe-syntaxp-exprp (mv-nth 1 (convert-syntaxp-argument-for-axe conjunct rule-symbol))))
   :hints (("Goal" :in-theory (enable convert-syntaxp-argument-for-axe axe-syntaxp-exprp axe-syntaxp-function-applicationp list-of-variables-and-constantsp)))))

;; (defthm subsetp-equal-of-free-vars-in-term-of-mv-nth-1-of-convert-syntaxp-argument-for-axe
;;   (implies (and (not (mv-nth 0 (convert-syntaxp-argument-for-axe term rule-symbol)))
;;                 (subsetp-equal (free-vars-in-term term)
;;                                (cons 'dag-array bound-vars))
;;                 (pseudo-termp term))
;;            (subsetp-equal (free-vars-in-term (mv-nth 1 (convert-syntaxp-argument-for-axe term rule-symbol)))
;;                           bound-vars))
;;   :hints (("Goal" :expand (free-vars-in-terms (cdr term))
;;            :in-theory (enable convert-syntaxp-argument-for-axe
;;                               myquotep
;;                               free-vars-in-term))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv erp hyp).
;; convert-syntaxp-argument-for-axe helps catch errors if the rule has unsupported stuff in a syntaxp hyp
(defund make-axe-syntaxp-hyp-for-synp-expr (expr bound-vars rule-symbol hyp)
  (declare (xargs :guard (and (pseudo-termp expr)
                              (symbol-listp bound-vars)
                              (symbolp rule-symbol))))
  (b* (;; Remove dag-array args from axe-syntaxp functions ('dag-array might remain as an argument to quotep):
       ((mv erp expr)
        (convert-syntaxp-argument-for-axe expr rule-symbol))
       ((when erp)
        (er hard? 'make-axe-syntaxp-hyp-for-synp-expr "Error processing synp hyp ~x0 in rule ~x1." hyp rule-symbol)
        (mv erp nil))
       ;; Check that all vars that remain in EXPR are bound:
       (mentioned-vars (free-vars-in-term expr))
       ((when (not (subsetp-eq mentioned-vars bound-vars)))
        (er hard? 'make-axe-syntaxp-hyp-for-synp-expr "Hyp ~x0 in rule ~x1 mentions vars ~x2 that are not bound by the LHS or by preceding hyps."
            hyp rule-symbol (set-difference-eq mentioned-vars bound-vars))
        (mv :bad-vars nil)))
    (mv (erp-nil) `(:axe-syntaxp . ,expr))))

(local
 (defthm axe-rule-hypp-of-mv-nth-1-of-make-axe-syntaxp-hyp-for-synp-expr
   (implies (and (pseudo-termp conjunct)
                 (not (mv-nth 0 (make-axe-syntaxp-hyp-for-synp-expr conjunct bound-vars rule-symbol hyp))))
            (axe-rule-hypp (mv-nth 1 (make-axe-syntaxp-hyp-for-synp-expr conjunct bound-vars rule-symbol hyp))))
   :hints (("Goal" :in-theory (enable make-axe-syntaxp-hyp-for-synp-expr axe-rule-hypp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

(local
 (defthm pseudo-termp-of-process-axe-syntaxp-function-application
   (implies (and (pseudo-termp expr)
                 (axe-syntaxp-function-applicationp expr)
                ;;(not (eq 'quote (ffn-symb expr)))
                 )
            (pseudo-termp (process-axe-syntaxp-function-application expr wrld)))
   :hints (("Goal" :in-theory (enable process-axe-syntaxp-function-application axe-syntaxp-function-applicationp)))))

(local
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
            :in-theory (enable process-axe-syntaxp-function-application axe-syntaxp-function-applicationp axe-syntaxp-exprp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Drops dag-array formals passed as the last args to functions
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

(local
 (defthm pseudo-termp-of-process-axe-syntaxp-expr
   (implies (and (pseudo-termp expr)
                 (axe-syntaxp-exprp expr))
            (pseudo-termp (process-axe-syntaxp-expr expr wrld)))
   :hints (("Goal" :in-theory (enable process-axe-syntaxp-expr axe-syntaxp-exprp)))))

(local
 (defthm axe-syntaxp-exprpp-of-process-axe-syntaxp-expr
   (implies (and (pseudo-termp expr)
                 (axe-syntaxp-exprp expr))
            (axe-syntaxp-exprp (process-axe-syntaxp-expr expr wrld)))
   :hints (("Goal" :in-theory (enable process-axe-syntaxp-expr axe-syntaxp-exprp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

(local
 (defthm pseudo-termp-of-process-axe-bind-free-function-application
   (implies (and (pseudo-termp expr)
                 (axe-bind-free-function-applicationp expr)
                ;;(not (eq 'quote (ffn-symb expr)))
                 )
            (pseudo-termp (process-axe-bind-free-function-application expr wrld)))
   :hints (("Goal" :in-theory (enable process-axe-bind-free-function-application axe-bind-free-function-applicationp)))))

(local
 (defthm axe-bind-free-function-applicationp-of-process-axe-bind-free-function-application
   (implies (and (pseudo-termp expr)
                 (axe-bind-free-function-applicationp expr)
                ;;(not (eq 'quote (ffn-symb expr)))
                 )
            (axe-bind-free-function-applicationp (process-axe-bind-free-function-application expr wrld)))
   :hints (("Goal" :in-theory (enable process-axe-bind-free-function-application axe-bind-free-function-applicationp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv erp hyps bound-vars).  The HYPS returned may be empty if we drop a
;; hyp that is a non-nil constant. The BOUND-VARS returned is the list of vars
;; bound by the LHS, this hyp, and all previous hyps.
(defund make-axe-rule-hyps-for-hyp (hyp bound-vars rule-symbol wrld)
  (declare (xargs :guard (and (pseudo-termp hyp) ; todo: strengthen
                              (symbol-listp bound-vars)
                              (symbolp rule-symbol)
                              (plist-worldp wrld))
                  :guard-hints (("Goal" :expand (AXE-SYNTAXP-EXPRP (CADR HYP))
                                 :in-theory (enable
                                             ;; member-equal-of-pre-simplify-term-and-free-vars-in-term-when-not-consp-of-pre-simplify-term
                                             )))))
  (if (atom hyp) ;; can only be a variable
      ;;turn a hyp of <var> into (not (equal 'nil <var>)) which is equivalent.  Axe relies on the fact that a hyp cannot be a variable.
      (if (member-eq hyp bound-vars)
          (mv (erp-nil) `((not (equal 'nil ,hyp))) bound-vars)
        (prog2$ (er hard? 'make-axe-rule-hyps-for-hyp "Hyp ~x0 is a single free var in rule ~x1!" hyp rule-symbol)
                (mv :bad-hyp *unrelievable-hyps* bound-vars)))
    (if (fquotep hyp)
        (if (equal *nil* hyp)
            (prog2$ (er hard? 'make-axe-rule-hyps-for-hyp "Found a hyp of nil in rule ~x0!" rule-symbol)
                    (mv :nil-hyp *unrelievable-hyps* bound-vars))
          (prog2$ (cw "Note: Skipping a constant, non-nil hyp of ~x0 in ~x1.~%" hyp rule-symbol)
                  (mv (erp-nil)
                      nil ;no hyps!
                      bound-vars)))
      (if (call-of 'synp hyp) ;; Example: (SYNP 'NIL '(SYNTAXP (QUOTEP X)) '(IF (QUOTEP X) 'T 'NIL)).
          ;; it's a call to SYNP, which represents both syntaxp and bind-free hyps in ACL2:
          (if (and (= 3 (len (fargs hyp)))
                   (true-listp hyp)
                   (equal *nil* (farg1 hyp))
                   ;; arg 2 is the untranslated form, which we ignore
                   (myquotep (farg3 hyp))
                   (let ((core-term (unquote (farg3 hyp)))) ; example: (IF (QUOTEP X) 'T 'NIL)
                     (and (pseudo-termp core-term)
                          (call-of 'if core-term)
                          (equal *t* (farg2 core-term))
                          (equal *nil* (farg3 core-term)))))
              (b* ( ;; We attempt to convert the syntaxp hyp into an axe-syntaxp hyp (this only works for some hyps)
                   ((mv erp hyp)
                    (make-axe-syntaxp-hyp-for-synp-expr (farg1 (unquote (farg3 hyp))) bound-vars rule-symbol hyp))
                   ((when erp) (mv erp *unrelievable-hyps* bound-vars)))
                (mv (erp-nil)
                    (list hyp)
                    bound-vars ;no extra vars get bound
                    ))
            ;; TODO: Check whether it is a bind-free hyp and print a better message if so:
            (prog2$ (er hard? 'make-axe-rule-hyps-for-hyp "Hyp ~x0 in rule ~x1 is an unsupported call of SYNP.  If it is a (translated) bind-free hyp, considering using axe-bind-free instead, along with DAG-aware versions of the function(s) called inside the bind-free."
                        hyp rule-symbol)
                    (mv :unsupported-synp *unrelievable-hyps* bound-vars)))
        (if (call-of 'axe-syntaxp hyp) ; (axe-syntaxp <expr>)
            (b* ((args (fargs hyp))
                 ((when (not (and (consp args) ; must be exactly 1 arg
                                  (null (cdr args)))))
                  (er hard? 'make-axe-rule-hyps-for-hyp "Ill-formed axe-syntaxp hyp ~x0 in rule ~x1." hyp rule-symbol)
                  (mv :bad-syntaxp-hyp *unrelievable-hyps* bound-vars))
                 ;; drop this?:
                 ;; ((when (member-eq 'dag-array bound-vars))
                 ;;  (er hard? 'make-axe-rule-hyps-for-hyp "The variable dag-array is bound in rule ~x0, but that variable has a special meaning in axe-syntaxp hyps and cannot appear in such rules."
                 ;;      rule-symbol)
                 ;;  (mv *unrelievable-hyps* bound-vars))
                 (expr (first args))
                 ((when (not (axe-syntaxp-exprp expr)))
                  (er hard? 'make-axe-rule-hyps-for-hyp "Ill-formed axe-syntaxp argument ~x0 in rule ~x1." expr rule-symbol)
                  (mv :bad-syntaxp-argument *unrelievable-hyps* bound-vars))
                 ;; Drops dag-array formals passed as last args to functions:
                 (processed-expr (process-axe-syntaxp-expr expr wrld))
                 (mentioned-vars (free-vars-in-term processed-expr)) ;dag-array has been perhaps removed
                 (allowed-vars bound-vars ;(cons 'dag-array bound-vars)
                               )
                 ((when (not (subsetp-eq mentioned-vars allowed-vars)))
                  (er hard? 'make-axe-rule-hyps-for-hyp "Axe-syntaxp hyp ~x0 in rule ~x1 mentions vars ~x2 that are not bound by the LHS or by preceding hyps."
                      hyp rule-symbol (set-difference-eq mentioned-vars allowed-vars))
                  (mv :unallowed-vars *unrelievable-hyps* bound-vars))
                 ;; TODO: Should we convert any calls of quote to axe-quotep?
                 )
              (mv (erp-nil) `((:axe-syntaxp . ,processed-expr)) bound-vars))
          (if (call-of 'axe-bind-free hyp) ;; (axe-bind-free <term> '<vars-to-bind>)
              (b* ((args (fargs hyp))
                   ((when (not (and (consp args) ; must be exactly 2 args
                                    (consp (cdr args))
                                    (null (cddr args)))))
                    (er hard? 'make-axe-rule-hyps-for-hyp "The axe-bind-free hyp ~x0 is not well-formed (should be a call of axe-bind-free on exactly 2 arguments, a term and a quoted list of vars to bind)." hyp)
                    (mv :bad-bind-free-hyp *unrelievable-hyps* bound-vars))
                   ;; ((when (member-eq 'dag-array bound-vars))
                   ;;  (er hard? 'make-axe-rule-hyps-for-hyp "The variable DAG-ARRAY is bound in rule ~x0, but that variable has a special meaning in axe-bind-free hyps and cannot already be bound when an axe-bind-free hyp is encountered."
                   ;;      rule-symbol)
                   ;;  (mv *unrelievable-hyps* bound-vars))
                   (axe-bind-free-expr (first args))
                   ((when (not (axe-bind-free-function-applicationp axe-bind-free-expr)))
                    (er hard? 'make-axe-rule-hyps-for-hyp "Ill-formed axe-bind-free argument ~x0 in rule ~x1." axe-bind-free-expr rule-symbol)
                    (mv :bad-bind-free-argument *unrelievable-hyps* bound-vars))
                   (axe-bind-free-expr (process-axe-bind-free-function-application axe-bind-free-expr wrld))
                   (mentioned-vars (free-vars-in-term axe-bind-free-expr))
                   (allowed-vars bound-vars ;(cons 'dag-array bound-vars)
                                 )
                   ((when (not (subsetp-eq mentioned-vars allowed-vars)))
                    (er hard? 'make-axe-rule-hyps-for-hyp "Axe-bind-free hyp ~x0 in rule ~x1 mentions vars ~x2 that are not bound by the LHS or preceding hyps."
                        hyp rule-symbol (set-difference-eq mentioned-vars allowed-vars))
                    (mv :disallowed-vars-in-bind-free-hyp *unrelievable-hyps* bound-vars))
                   (quoted-vars-to-bind (second args))
                   ((when (not (quoted-symbol-listp quoted-vars-to-bind)))
                    (er hard? 'make-axe-rule-hyps-for-hyp "The second argument to an axe-bind-free hyp must be a quoted list of vars, but we got ~x0 in hyp ~x1." quoted-vars-to-bind hyp)
                    (mv :bad-bind-free-vars-arg *unrelievable-hyps* bound-vars))
                   (vars-to-bind (unquote quoted-vars-to-bind))
                   ((when (not (consp vars-to-bind)))
                    (er hard? 'make-axe-rule-hyps-for-hyp "The declared vars-to-bind of axe-bind-free hyp ~x0 in rule ~x1 is empty." hyp rule-symbol)
                    (mv :empty-bind-free-vars-arg *unrelievable-hyps* bound-vars))
                   ((when (intersection-eq vars-to-bind bound-vars))
                    ;; TODO: Improve message to just print the intersection
                    (er hard? 'make-axe-rule-hyps-for-hyp "The axe-bind-free hyp ~x0 in rule ~x1 is declared to bind the vars ~x2, but these are not disjoint from the set of vars already bound (~x3)" hyp rule-symbol vars-to-bind bound-vars)
                    (mv :already-bound-bind-free-vars *unrelievable-hyps* bound-vars)))
                ;; axe-bind-free hyps include both the term and the variables:
                (mv (erp-nil)
                    `((:axe-bind-free ,axe-bind-free-expr . ,vars-to-bind))
                    ;; the vars become bound:
                    (append vars-to-bind bound-vars)))
            (if (call-of 'axe-binding-hyp hyp) ; (axe-binding-hyp (equal <free-var> <expr-with-no-free-vars>))
                ;; Special treatment for a binding hyp (see "binding hypothesis" in :doc free-variables to see how ACL2 handles these):
                (b* ((args (fargs hyp))
                     ((when (not (and (consp args) ; must be exactly 1 arg
                                      (null (cdr args)))))
                      (er hard? 'make-axe-rule-hyps-for-hyp "Ill-formed axe-binding-hyp ~x0 in rule ~x1." hyp rule-symbol)
                      (mv :bad-axe-binding-hyp *unrelievable-hyps* bound-vars))
                     (equality (first args)) ; strip the call of axe-binding-hyp
                     ((when (not (and (consp equality)
                                      (eq 'equal (ffn-symb equality)) ; (equal <free-var> <expr-with-no-free-vars>)
                                      (= 2 (len (fargs equality))) ; for guards
                                      (variablep (farg1 equality))
                                      (not (member-equal (farg1 equality) bound-vars))
                                      ;; second arg should already be known to be a pseudo-term
                                      (subsetp-equal (free-vars-in-term (farg2 equality)) bound-vars))))
                      (er hard? 'make-axe-rule-hyps-for-hyp "Ill-formed axe-binding-hyp ~x0 in rule ~x1." hyp rule-symbol)
                      (mv :bad-axe-binding-hyp *unrelievable-hyps* bound-vars))
                     ;; (- (cw "Note: Binding hyp detected in rule ~x0.~%" rule-symbol))
                     (var (farg1 equality))
                     (expr (farg2 equality))
                     ;; We do not expand lambdas, but we do pre-simplify:
                     (expr (pre-simplify-term expr nil nil)) ; preserves equal, not iff
                     ((when (not (subsetp-equal (free-vars-in-term expr) bound-vars))) ; todo: prove this can't happen (but strengthen the guard)
                      (prog2$ (er hard? 'make-axe-rule-hyps-for-hyp "Hyp, ~x0 in ~x1 has free vars after pre-simplification!" hyp rule-symbol)
                              (mv :bad-axe-binding-hyp *unrelievable-hyps* bound-vars))))
                  (mv (erp-nil)
                      `((:axe-binding-hyp ,var . ,expr))
                      (cons var bound-vars) ;; the var becomes bound
                      ))
            ;; not a special hyp:
            (b* ((all-fns (fns-in-term hyp))
                 ;; These 2 checks catch common errors:
                 ((when (member-eq 'axe-syntaxp all-fns))
                  (er hard? 'make-axe-rule-hyps-for-hyp "Hyp ~x0 in rule ~x1 contains a call to axe-syntaxp that is not at the top level." hyp rule-symbol)
                  (mv :bad-hyp *unrelievable-hyps* bound-vars))
                 ((when (member-eq 'axe-bind-free all-fns))
                  (er hard? 'make-axe-rule-hyps-for-hyp "Hyp ~x0 in rule ~x1 contains a call to axe-bind-free that is not at the top level." hyp rule-symbol)
                  (mv :bad-hyp *unrelievable-hyps* bound-vars))
                 ;; todo: check for work-hards not at the top-level?
                 ;; These 3 checks ensure that expanding the lambdas in a normal hyp doesn't result in a special hyp:
                 ((when (member-eq :axe-syntaxp all-fns)) ;todo: prove that this never happens?
                  (er hard? 'make-axe-rule-hyps-for-hyp "Hyp ~x0 in rule ~x1 contains a call to :axe-syntaxp, which is not a legal function name." hyp rule-symbol)
                  (mv :bad-hyp *unrelievable-hyps* bound-vars))
                 ((when (member-eq :axe-bind-free all-fns)) ;todo: prove that this never happens?
                  (er hard? 'make-axe-rule-hyps-for-hyp "Hyp ~x0 in rule ~x1 contains a call to :axe-bind-free, which is not a legal function name." hyp rule-symbol)
                  (mv :bad-hyp *unrelievable-hyps* bound-vars))
                 ((when (member-eq :free-vars all-fns)) ;todo: prove that this never happens?
                  (er hard? 'make-axe-rule-hyps-for-hyp "Hyp ~x0 in rule ~x1 contains a call to :free-vars which is not a legal function name." hyp rule-symbol)
                  (mv :bad-hyp *unrelievable-hyps* bound-vars))
                 ((when (member-eq :axe-binding-hyp all-fns)) ;todo: prove that this never happens?
                  (er hard? 'make-axe-rule-hyps-for-hyp "Hyp ~x0 in rule ~x1 contains a call to :axe-binding-hyp which is not a legal function name." hyp rule-symbol)
                  (mv :bad-hyp *unrelievable-hyps* bound-vars))
                 ;; Check for free vars in the hyp:
                 (hyp-free-vars (set-difference-eq (free-vars-in-term hyp) bound-vars)))
              (if hyp-free-vars
                  ;; Free vars but not a binding-hyp.  Will be relieved by matching against assumptions:
                  (b* (;; Must expand lambdas to allow for matching:
                       (expanded-hyp (expand-lambdas-in-term hyp)) ; todo: print a note here, if this does anything.
                       (expanded-hyp-free-vars (set-difference-eq (free-vars-in-term expanded-hyp) bound-vars))
                       ((when (not expanded-hyp-free-vars)) ; unusual case: such a hyp doesn't really fit this case or the normal case
                        (er hard? 'make-axe-rule-hyps-for-hyp "Hyp ~x0 in rule ~x1 has free vars that disappear when lambdas are expanded." hyp rule-symbol)
                        (mv :bad-hyp *unrelievable-hyps* bound-vars))
                         ;; todo: consider cleaning up the hyp in other ways?
                       (hyp expanded-hyp)
                         ;; (- (cw "NOTE: Free vars in rule ~x0.~%" rule-symbol))
                         ;; Strip and note the work-hard, if any:
                         ;; Previously, a work-hard with free vars was an error, but Axe generates some rules like that.
                       ((mv hyp work-hardp)
                        (if (and (call-of 'work-hard hyp)
                                 (= 1 (len (fargs hyp))))
                            (mv (farg1 hyp) t)
                          (mv hyp nil)))
                       (- (and work-hardp
                               (cw "NOTE: Hyp ~x0 in rule ~x1 is a call of work-hard but contains free-variables." hyp rule-symbol)))
                       ((when (not (consp hyp)))
                        (er hard? 'make-axe-rule-hyps-for-hyp "Hyp ~x0 in rule ~x1 is not a function call after expanding lambdas and possibly stripping a work-hard." hyp rule-symbol)
                        (mv :bad-hyp *unrelievable-hyps* bound-vars))
                       ((when (fquotep hyp))
                        (er hard? 'make-axe-rule-hyps-for-hyp "Hyp ~x0 in rule ~x1 is a quoted constant after expanding lambdas and possibly stripping a work-hard." hyp rule-symbol)
                        (mv :bad-hyp *unrelievable-hyps* bound-vars))
                       (fn (ffn-symb hyp)))
                    (prog2$ (and ;todo: drop this check, or use it:
                             (eq 'equal fn) ;; test for (equal <free-var> <term-with-no-free-vars>)
                             (eql 2 (len (fargs hyp))) ;for guard proofs
                             (atom (farg1 hyp))
                             (not (member-eq (farg1 hyp) bound-vars))
                             (subsetp-eq (free-vars-in-term (farg2 hyp))
                                         bound-vars)
                             ;;(cw "Note: Binding hyp ~x0 detected in rule ~x1.~%" hyp rule-symbol) ;todo: add a print option?
                             )
                            (mv (erp-nil)
                                (list (cons :free-vars hyp)) ;tag the hyp to indicate it has free vars
                                ;; if the hyp is successfully relieved (by searching for matches in the context), all of the free-vars in the hyp wil become bound:
                                (append expanded-hyp-free-vars bound-vars))))
                ;; Normal hyp with no free vars:
                ;; Here we use hyp, not expanded-hyp, to make it cheaper to rewrite a hyp that contains lambdas:
                ;; Previously, we did use the expanded-hyp.
                (b* ((hyp (pre-simplify-term hyp t nil)) ; cleans up lambdas, improves translated ORs, etc. only preserves IFF (not EQUAL)
                     ((when (atom hyp)) ;; can only be a variable
                      ;;turn a hyp of <var> into (not (equal 'nil <var>)) which is equivalent.  Axe relies on the fact that a hyp cannot be a variable.
                      (if (not (member-equal hyp bound-vars)) ; todo: prove this can't happen (but strengthen the guard)
                          (prog2$ (er hard? 'make-axe-rule-hyps-for-hyp "Hyp, ~x0, is a free var in ~x1 after pre-simplification!" hyp rule-symbol)
                                  (mv :bad-hyp *unrelievable-hyps* bound-vars))
                        (mv (erp-nil) `((not (equal 'nil ,hyp))) bound-vars)))
                     ((when (fquotep hyp))
                      (if (equal *nil* hyp)
                          (prog2$ (er hard? 'make-axe-rule-hyps-for-hyp "Found a hyp of nil (after pre-simplification) in rule ~x0!" rule-symbol)
                                  (mv :nil-hyp *unrelievable-hyps* bound-vars))
                        (prog2$ (cw "Note: Skipping a constant, non-nil hyp of ~x0 in ~x1 (after pre-simplification).~%" hyp rule-symbol)
                                (mv (erp-nil)
                                    nil ;no hyps!
                                    bound-vars))))
                     ((when (or (eq :axe-syntaxp (ffn-symb hyp))
                                (eq :axe-bind-free (ffn-symb hyp))
                                (eq :free-vars (ffn-symb hyp))
                                (eq :axe-binding-hyp (ffn-symb hyp))
                                (not (subsetp-equal (free-vars-in-term hyp) bound-vars)))) ; todo: prove that this can't happen: pre-simplify can't introduce new functions
                      (prog2$ (er hard? 'make-axe-rule-hyps-for-hyp "Unexpected form of hyp, ~x0, in ~x1 after pre-simplification!" hyp rule-symbol)
                              (mv :bad-hyp *unrelievable-hyps* bound-vars))))
                  (mv (erp-nil)
                      (list hyp) ; hyp is not wrapped
                      bound-vars)))))))))))

(local
 (defthm axe-rule-hyp-listp-of-mv-nth-1-of-make-axe-rule-hyps-for-hyp
   (implies (pseudo-termp hyp)
            (axe-rule-hyp-listp (mv-nth 1 (make-axe-rule-hyps-for-hyp hyp bound-vars rule-symbol wrld))))
   :hints (("Goal" :in-theory (e/d (make-axe-rule-hyps-for-hyp
                                    axe-rule-hypp
                                    symbolp-when-pseudo-termp
                                    not-equal-of-car-when-not-member-equal-of-fns-in-term
                                    axe-rule-hyp-listp)
                                   (;not-member-equal-of-fns-in-term-of-expand-lambdas-in-term
                                    myquotep
                                    ;;QUOTED-SYMBOL-LISTP
                                    ;;ALL-VAR-OR-MYQUOTEP
                                    ;fns-in-term
                                    ;add-to-set-equal
                                    ;EXPAND-LAMBDAS-IN-TERM
                                    pseudo-termp
                                    AXE-RULE-HYPP
                                    ))))))

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

;; (defthm all-consp-of-mv-nth-1-of-make-axe-rule-hyps-for-hyp
;;   (all-consp (mv-nth 1 (make-axe-rule-hyps-for-hyp hyp bound-vars rule-symbol)))
;;   :hints (("Goal" :in-theory (enable make-axe-rule-hyps-for-hyp))))

;todo: not true because of axe-bind-free hyps.  define a notion of an axe-hyp..
;; (defthm pseudo-termp-of-mv-nth-1-of-make-axe-rule-hyp
;;   (implies (and (not (mv-nth 0 (make-axe-rule-hyp hyp bound-vars rule-symbol)))
;;                 (pseudo-termp hyp))
;;            (pseudo-termp (mv-nth 1 (make-axe-rule-hyp hyp bound-vars rule-symbol))))
;;   :hints (("Goal" :in-theory (enable make-axe-rule-hyp))))

(local
 (defthm symbol-listp-of-mv-nth-2-of-make-axe-rule-hyps-for-hyp
   (implies (and (symbol-listp bound-vars)
                 (pseudo-termp hyp))
            (symbol-listp (mv-nth 2 (make-axe-rule-hyps-for-hyp hyp bound-vars rule-symbol wrld))))
   :hints (("Goal" :in-theory (enable make-axe-rule-hyps-for-hyp)))))

(local
 (defthm true-listp-of-mv-nth-1-of-make-axe-rule-hyps-for-hyp
   (true-listp (mv-nth 1 (make-axe-rule-hyps-for-hyp hyp bound-vars rule-symbol wrld)))
   :hints (("Goal" :in-theory (enable make-axe-rule-hyps-for-hyp)))))

(local
 (defthm true-listp-of-mv-nth-2-of-make-axe-rule-hyps-for-hyp
   (implies (and (true-listp bound-vars)
                ;; (pseudo-termp hyp)
                 )
            (true-listp (mv-nth 2 (make-axe-rule-hyps-for-hyp hyp bound-vars rule-symbol wrld))))
   :hints (("Goal" :in-theory (enable make-axe-rule-hyps-for-hyp)))))

;TODO: prove
;; (defthm all-regular-function-callp-of-make-axe-rule-hyps-for-hyp
;;   (all-regular-function-callp (make-axe-rule-hyps-for-hyp hyp rule-symbol)))

;;because it returns no hyps or 1 hyp
(local
 (defthm reverse-list-of-mv-nth-1-of-make-axe-rule-hyps-for-hyp
   (equal (reverse-list (mv-nth 1 (make-axe-rule-hyps-for-hyp hyp bound-vars rule-symbol wrld)))
          (mv-nth 1 (make-axe-rule-hyps-for-hyp hyp bound-vars rule-symbol wrld)))
   :hints (("Goal" :in-theory (enable make-axe-rule-hyps-for-hyp)))))

;; We always get either a single hyp or no hyps.
;; Justifies not worrying about reversing the hyps added to the acc in make-axe-rule-hyps.
(thm
 (or (equal 0 (len (mv-nth 1 (make-axe-rule-hyps-for-hyp hyp bound-vars rule-symbol wrld))))
     (equal 1 (len (mv-nth 1 (make-axe-rule-hyps-for-hyp hyp bound-vars rule-symbol wrld)))))
 :hints (("Goal" :in-theory (enable make-axe-rule-hyps-for-hyp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv erp processed-hyps bound-vars) where bound-vars is all the vars
;; bound in the LHS or when relieving hyps
(defund make-axe-rule-hyps (hyps bound-vars rule-symbol wrld acc)
  (declare (xargs :guard (and (pseudo-term-listp hyps)
                              (symbol-listp bound-vars)
                              (symbolp rule-symbol)
                              (true-listp acc)
                              (plist-worldp wrld))))
  (if (endp hyps)
      (mv (erp-nil) (reverse-list acc) bound-vars)
    (b* ((hyp (first hyps))
         ((mv erp axe-rule-hyps bound-vars) (make-axe-rule-hyps-for-hyp hyp bound-vars rule-symbol wrld))
         ((when erp) (mv erp *unrelievable-hyps* bound-vars)))
      (make-axe-rule-hyps (rest hyps) bound-vars rule-symbol wrld (append axe-rule-hyps acc)))))

(local
 (defthm mv-nth-1-of-make-axe-rule-hyps-of-append
   (implies (not (mv-nth 0 (make-axe-rule-hyps hyps bvars rule-symbol wrld (append acc1 acc2))))
            (equal (mv-nth 1 (make-axe-rule-hyps hyps bvars rule-symbol wrld (append acc1 acc2)))
                   (append (reverse-list acc2)
                           (mv-nth 1 (make-axe-rule-hyps hyps bvars rule-symbol wrld acc1)))))
   :hints (("Goal" :in-theory (enable make-axe-rule-hyps)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; no accumulator, easier to reason about
;; Returns (mv erp processed-hyps bound-vars).
(local
  (defund make-axe-rule-hyps-simple (hyps bound-vars rule-symbol wrld)
    (declare (xargs :guard (and (pseudo-term-listp hyps)
                                (symbol-listp bound-vars)
                                (symbolp rule-symbol)
                                (plist-worldp wrld))))
    (if (endp hyps)
        (mv (erp-nil) nil bound-vars)
      (b* ((hyp (first hyps))
           ((mv erp axe-rule-hyps bound-vars) (make-axe-rule-hyps-for-hyp hyp bound-vars rule-symbol wrld))
           ((when erp) (mv erp *unrelievable-hyps* bound-vars))
           ((mv erp axe-rule-hyps2 bound-vars) (make-axe-rule-hyps-simple (rest hyps) bound-vars rule-symbol wrld))
           ((when erp) (mv erp *unrelievable-hyps* bound-vars)))
        (mv (erp-nil)
            (append axe-rule-hyps axe-rule-hyps2)
            bound-vars)))))

;; redefine in terms of the simpler function
(local
 (defthmd make-axe-rule-hyps-redef
   (implies (not (mv-nth 0 (make-axe-rule-hyps hyps bound-vars rule-symbol wrld acc)))
            (equal (make-axe-rule-hyps hyps bound-vars rule-symbol wrld acc)
                   (mv (mv-nth 0 (make-axe-rule-hyps-simple hyps bound-vars rule-symbol wrld))
                       (append (reverse-list acc)
                               (mv-nth 1 (make-axe-rule-hyps-simple hyps bound-vars rule-symbol wrld)))
                       (mv-nth 2 (make-axe-rule-hyps-simple hyps bound-vars rule-symbol wrld)))))
   :hints (("Goal" :in-theory (enable make-axe-rule-hyps make-axe-rule-hyps-simple
                                     ;make-axe-rule-hyps-for-hyp ;so we can see it r
                                      )))))

;; error case
(local
 (defthmd make-axe-rule-hyps-redef-0
   (equal (mv-nth 0 (make-axe-rule-hyps hyps bound-vars rule-symbol wrld acc))
          (mv-nth 0 (make-axe-rule-hyps-simple hyps bound-vars rule-symbol wrld)))
   :hints (("Goal" :in-theory (enable make-axe-rule-hyps make-axe-rule-hyps-simple)))))

(local
 (defthm axe-rule-hyp-listp-of-mv-nth-1-of-make-axe-rule-hyps-simple
   (implies (pseudo-term-listp hyps)
            (axe-rule-hyp-listp (mv-nth 1 (make-axe-rule-hyps-simple hyps bound-vars rule-symbol wrld))))
   :hints (("Goal" :in-theory (enable make-axe-rule-hyps-simple)))))

;; (defthm-flag-expand-lambdas-in-term
;;   (defthm not-member-equal-of-fns-in-term-of-expand-lambdas-in-term
;;     (implies (not (member-equal fn (fns-in-term term)))
;;              (not (member-equal fn (fns-in-term (expand-lambdas-in-term term)))))
;;     :flag expand-lambdas-in-term)
;;   (defthm not-member-equal-of-fns-in-terms-of-expand-lambdas-in-terms
;;     (implies (not (member-equal fn (fns-in-terms terms)))
;;              (not (member-equal fn (fns-in-terms (expand-lambdas-in-terms terms)))))
;;     :flag expand-lambdas-in-terms)
;;   :hints (("Goal" :in-theory (enable expand-lambdas-in-terms
;;                                      expand-lambdas-in-term))))

;move
(local
 (defthm not-member-equal-when-not-symbolp
   (implies (and (not (symbolp a))
                 (symbol-listp x))
            (not (member-equal a x)))
   :hints (("Goal" :in-theory (enable member-equal symbol-listp)))))

;move
(local
 (defthm not-member-equal-of-fns-in-term-when-consp
   (implies (and (consp x)
                 (pseudo-termp term))
            (not (member-equal x (fns-in-term term))))
   :hints (("Goal" :use ( symbol-listp-of-fns-in-term)
            :in-theory (disable symbol-listp-of-fns-in-term)))))

;move
(local
 (defthm member-equal-of-car-and-fns-in-term-same-iff
   (implies (and (pseudo-termp term)
                 (not (equal 'quote (car term)))
                 (consp term))
            (iff (member-equal (car term) (fns-in-term term))
                 (not (consp (car term)))))
   :hints (("Goal" :expand (fns-in-term term)
            :in-theory (enable fns-in-term)))))

(local
 (defthm not-equal-of-car-of-expand-lambdas-in-term-when-not-member-equal-of-fns-in-term
   (implies (and (not (member-equal fn (fns-in-term term)))
                 (consp (expand-lambdas-in-term term))
                 (pseudo-termp term)
                 (not (equal 'quote fn))
                 (consp term))
            (not (equal fn (car (expand-lambdas-in-term term)))))
   :hints (("Goal"
            :use ((:instance not-member-equal-of-fns-in-term-of-expand-lambdas-in-term
                             (fn (CAR (EXPAND-LAMBDAS-IN-TERM TERM))))
                  (:instance not-equal-of-car-when-not-member-equal-of-fns-in-term
                             (a fn) (x term)))
            :in-theory (disable not-equal-of-car-when-not-member-equal-of-fns-in-term
                                not-member-equal-of-fns-in-term-of-expand-lambdas-in-term)))))

(local (in-theory (disable FNS-IN-TERM MYQUOTEP QUOTED-SYMBOL-LISTP )))

;move up
(local
 (defthm bound-vars-suitable-for-hypsp-of-mv-nth-1-of-make-axe-rule-hyps-for-hyp
   (implies (and (not (mv-nth 0 (make-axe-rule-hyps-for-hyp hyp bound-vars rule-symbol wrld)))
                 (pseudo-termp hyp)
                ;(symbol-listp bound-vars)
                ;(symbolp rule-symbol)
                ;(plist-worldp wrld)
                 )
            (bound-vars-suitable-for-hypsp bound-vars (mv-nth 1 (make-axe-rule-hyps-for-hyp hyp bound-vars rule-symbol wrld))))
   :hints (("Goal" ;:expand (EXPAND-LAMBDAS-IN-TERM HYP)
            :expand ((FREE-VARS-IN-TERM (EXPAND-LAMBDAS-IN-TERM HYP))
                     (FREE-VARS-IN-TERMS (CDR (EXPAND-LAMBDAS-IN-TERM HYP)))
                    ;(FREE-VARS-IN-TERMS (CDDR (EXPAND-LAMBDAS-IN-TERM HYP)))
                     )
            :in-theory (enable make-axe-rule-hyps-for-hyp
                               bound-vars-suitable-for-hypp
                               make-axe-syntaxp-hyp-for-synp-expr
                               fns-in-term)))))

(local
 (defthm free-vars-in-term-when-unary
   (implies (and (equal 2 (len term))
                 (not (eq 'quote (car term))))
            (equal (FREE-VARS-IN-TERM term)
                   (FREE-VARS-IN-TERM (cadr term))))))

;; use rule about (free-vars-in-terms (expand-lambdas-in-terms terms))
(local
 (defthm mv-nth-2-of-make-axe-rule-hyps-for-hyp
   (implies (and (pseudo-termp hyp)
                 (not (mv-nth 0 (make-axe-rule-hyps-for-hyp hyp bound-vars rule-symbol wrld))))
            (equal (mv-nth 2 (make-axe-rule-hyps-for-hyp hyp bound-vars rule-symbol wrld))
                   (bound-vars-after-hyps bound-vars (mv-nth 1 (make-axe-rule-hyps-for-hyp hyp bound-vars rule-symbol wrld)))))
   :hints (("Goal" :expand ((FNS-IN-TERM HYP)
                           ;(FREE-VARS-IN-TERM (EXPAND-LAMBDAS-IN-TERM HYP))
                           ;(FREE-VARS-IN-TERMS (CDR (EXPAND-LAMBDAS-IN-TERM HYP)))
                           ;(FREE-VARS-IN-TERM (EXPAND-LAMBDAS-IN-TERM HYP))
                           ;(FREE-VARS-IN-TERMS (CDR (EXPAND-LAMBDAS-IN-TERM HYP)))
                            )
            :in-theory (enable bound-vars-after-hyps
                               bound-vars-after-hyp
                               make-axe-rule-hyps-for-hyp
                               MAKE-AXE-SYNTAXP-HYP-FOR-SYNP-EXPR)))))

(local
 (defthm mv-nth-2-of-make-axe-rule-hyps-simple
   (implies (and (pseudo-term-listp hyps)
                 (not (mv-nth 0 (make-axe-rule-hyps-simple hyps bound-vars rule-symbol wrld))))
            (equal (mv-nth 2 (make-axe-rule-hyps-simple hyps bound-vars rule-symbol wrld))
                   (bound-vars-after-hyps bound-vars (mv-nth 1 (make-axe-rule-hyps-simple hyps bound-vars rule-symbol wrld)))))
   :hints (("Goal" :in-theory (enable bound-vars-after-hyps
                                      make-axe-rule-hyps-simple)))))

(local
 (defthm bound-vars-suitable-for-hypsp-of-mv-nth-1-of-make-axe-rule-hyps-simple
   (implies (and (not (mv-nth 0 (make-axe-rule-hyps-simple hyps bound-vars rule-symbol wrld)))
                 (pseudo-term-listp hyps))
            (bound-vars-suitable-for-hypsp bound-vars (mv-nth 1 (make-axe-rule-hyps-simple hyps bound-vars rule-symbol wrld))))
   :hints (("Goal" ;:expand (EXPAND-LAMBDAS-IN-TERM HYP)
            :in-theory (enable make-axe-rule-hyps-simple
                                     ;;make-axe-rule-hyps-for-hyp
                               bound-vars-suitable-for-hypp
                               bound-vars-after-hyp)))))

;zz
;; (defthm bound-vars-suitable-for-hypsp-of-mv-nth-0-of-make-axe-rule-hyps-helper
;;   (implies (and (pseudo-term-listp hyps) ; these come from rules in the world..
;;                 (symbol-listp bound-vars0)
;;                 (symbolp rule-symbol)
;;                 (true-listp acc)
;;                 (plist-worldp wrld)
;;                 (bound-vars-suitable-for-hypsp bound-vars0 (reverse-list acc))
;;                 (equal bvars (bound-vars-after-hyps bound-vars0 (reverse-list acc)))
;;                 )
;;            (and (bound-vars-suitable-for-hypsp bound-vars0
;;                                                (mv-nth 0 (make-axe-rule-hyps hyps
;;                                                                              bvars
;;                                                                              rule-symbol
;;                                                                              wrld
;;                                                                              acc)))
;;                 (equal (mv-nth 1 (make-axe-rule-hyps hyps
;;                                                      bvars
;;                                                      rule-symbol
;;                                                      wrld
;;                                                      acc))
;;                        (bound-vars-after-hyps hyps
;;                                               bvars))))
;;   :hints (("Goal" :induct (make-axe-rule-hyps hyps
;;                                               bvars
;;                                               rule-symbol
;;                                               wrld
;;                                               acc)
;;            :in-theory (enable make-axe-rule-hyps
;;                               MAKE-AXE-RULE-HYPS-FOR-HYP))))

;; (defthm all-consp-of-reverse-list
;;   (implies (all-consp acc)
;;            (all-consp (reverse-list acc)))
;;   :hints (("Goal" :in-theory (enable all-consp reverse-list))))

;; (defthm all-consp-of-make-axe-rule-hyps
;;   (implies (all-consp acc)
;;            (all-consp (mv-nth 0 (make-axe-rule-hyps hyps bound-vars rule-symbol acc))))
;;   :hints (("Goal" :in-theory (enable make-axe-rule-hyps))))

(local
 (defthm axe-rule-hyp-listp-of-make-axe-rule-hyps
   (implies (and (pseudo-term-listp hyps)
                 (axe-rule-hyp-listp acc))
            (axe-rule-hyp-listp (mv-nth 1 (make-axe-rule-hyps hyps bound-vars rule-symbol wrld acc))))
   :hints (("Goal" :in-theory (enable make-axe-rule-hyps)))))

;;move
(local
 (defthm pseudo-term-listp-of-reverse-list
   (equal (pseudo-term-listp (reverse-list acc))
          (pseudo-term-listp (true-list-fix acc)))
   :hints (("Goal" :in-theory (enable pseudo-term-listp reverse-list)))))

;not true because of axe-bind-free.
;; (defthm pseudo-term-listp-of-mv-nth-1-of-make-axe-rule-hyps
;;   (implies (and (pseudo-term-listp hyps)
;;                 (pseudo-term-listp acc)
;;                 (true-listp acc))
;;            (pseudo-term-listp (mv-nth 1 (make-axe-rule-hyps hyps bound-vars rule-symbol wrld acc))))
;;   :hints (("Goal" :in-theory (enable make-axe-rule-hyps))))

(local
 (defthm symbol-listp-of-mv-nth-2-of-make-axe-rule-hyps
   (implies (and (symbol-listp bound-vars)
                 (pseudo-term-listp hyps))
            (symbol-listp (mv-nth 2 (make-axe-rule-hyps hyps bound-vars rule-symbol wrld acc))))
   :hints (("Goal" :in-theory (enable make-axe-rule-hyps)))))

(local
 (defthm true-listp-of-mv-nth-2-of-make-axe-rule-hyps
   (implies (true-listp bound-vars)
            (true-listp (mv-nth 2 (make-axe-rule-hyps hyps bound-vars rule-symbol wrld acc))))
   :hints (("Goal" :in-theory (enable make-axe-rule-hyps)))))

;; ;TODO: Prove:
;; (defthm all-regular-function-callp-of-make-axe-rule-hyps
;;   (implies (all-regular-function-callp acc)
;;            (all-regular-function-callp (mv-nth 1 (make-axe-rule-hyps hyps bound-vars rule-symbol acc)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Checks that all the HYPS are :axe-syntaxp hyps
(defund all-axe-syntaxp-hypsp (hyps)
  (declare (xargs :guard (axe-rule-hyp-listp hyps)
                  :guard-hints (("Goal" :in-theory (enable axe-rule-hyp-listp)))))
  (if (endp hyps)
      t
    (and (eq :axe-syntaxp (ffn-symb (first hyps)))
         (all-axe-syntaxp-hypsp (rest hyps)))))

(local
 (defthm bound-vars-after-hyps-when-all-axe-syntaxp-hypsp
   (implies (all-axe-syntaxp-hypsp hyps)
            (equal (bound-vars-after-hyps bound-vars hyps)
                   bound-vars))
   :hints (("Goal" :in-theory (enable all-axe-syntaxp-hypsp bound-vars-after-hyps BOUND-VARS-AFTER-HYP)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;Returns (mv erp hyp).
;;TTODO: How can we access the auto-generated loop stopper that ACL2 sometimes puts in?
(defund make-axe-rule-hyp-for-loop-stopper (loop-stopper rule-name)
  (declare (xargs :guard t)
           (ignore rule-name))
  (if (and (true-listp loop-stopper)
           (<= 2 (len loop-stopper))
           (symbolp (first loop-stopper))
           (symbolp (second loop-stopper)))
      ;;a loop-stopper of (x y) means y must be smaller than x for the rule to fire
      (let ((loop-stopper `(:axe-syntaxp . (heavier-dag-term ,(first loop-stopper) ,(second loop-stopper)))))
        (prog2$ nil ;(cw "Note: inserting loop stopper ~x0 for rule ~x1.~%" loop-stopper rule-name)
                (mv (erp-nil) loop-stopper))) ;TODO: get the invisible fns and have heavier-dag-term (or a variant of it) ignore them
    (prog2$ (er hard? 'make-axe-rule-hyp-for-loop-stopper "Unrecognized loop stopper: ~x0." loop-stopper)
            (mv :bad-loop-stopper *unrelievable-hyp*))))

(local
 (defthm axe-rule-hypp-of-mv-nth-1-of-make-axe-rule-hyp-for-loop-stopper
   (axe-rule-hypp (mv-nth 1 (make-axe-rule-hyp-for-loop-stopper loop-stopper rule-name)))
   :hints (("Goal" :in-theory (enable axe-rule-hypp make-axe-rule-hyp-for-loop-stopper
                                      axe-syntaxp-exprp axe-syntaxp-function-applicationp
                                      list-of-variables-and-constantsp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;Returns (mv erp hyps).
(defund make-axe-rule-hyps-for-loop-stoppers (loop-stoppers rule-name)
  (declare (xargs :guard t))
  (if (atom loop-stoppers)
      (mv (erp-nil) nil)
    (b* (((mv erp first-res)
          (make-axe-rule-hyp-for-loop-stopper (first loop-stoppers) rule-name))
         ((when erp) (mv erp nil))
         ((mv erp rest-res)
          (make-axe-rule-hyps-for-loop-stoppers (rest loop-stoppers) rule-name))
         ((when erp) (mv erp nil)))
      (mv (erp-nil)
          (cons first-res rest-res)))))

(local
 (defthm axe-rule-hyp-listp-of-mv-nth-1-io-make-axe-rule-hyps-for-loop-stoppers
   (axe-rule-hyp-listp (mv-nth 1 (make-axe-rule-hyps-for-loop-stoppers loop-stoppers rule-name)))
   :hints (("Goal" :in-theory (enable make-axe-rule-hyps-for-loop-stoppers
                                      axe-rule-hyp-listp)))))

(local
 (defthm all-axe-syntaxp-hypsp-of-mv-nth-1-io-make-axe-rule-hyps-for-loop-stoppers
   (all-axe-syntaxp-hypsp (mv-nth 1 (make-axe-rule-hyps-for-loop-stoppers loop-stoppers rule-name)))
   :hints (("Goal" :in-theory (enable make-axe-rule-hyps-for-loop-stoppers
                                      make-axe-rule-hyp-for-loop-stopper
                                      all-axe-syntaxp-hypsp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;Returns (mv erp hyps).
;; TODO: Should we get anything else from the :rule-classes in addition to the loop-stoppers?  Check for unknown things?
;; These do not bind any vars
(defund make-axe-rule-loop-stopping-hyps (rule-classes rule-name)
  (declare (xargs :guard (and (symbol-alistp rule-classes)
                              (symbolp rule-name))))
  (b* ((rewrite-keyword-value-list (lookup-eq :rewrite rule-classes))
       ((when (not (keyword-value-listp rewrite-keyword-value-list)))
        (er hard? 'make-axe-rule-loop-stopping-hyps "Unexpected stuff in :rewrite rule class: ~x0." rewrite-keyword-value-list)
        (mv :bad-rule-class nil))
       (loop-stoppers (cadr (assoc-keyword :loop-stopper rewrite-keyword-value-list)))) ;we only look at :rewrite rules to get the loop-stoppers
    (make-axe-rule-hyps-for-loop-stoppers loop-stoppers rule-name)))

(local
 (defthm axe-rule-hyp-listp-of-mv-nth-1-of-make-axe-rule-loop-stopping-hyps
   (axe-rule-hyp-listp (mv-nth 1 (make-axe-rule-loop-stopping-hyps rule-classes rule-symbol)))
   :hints (("Goal" :in-theory (enable make-axe-rule-loop-stopping-hyps)))))

(local
 (defthm all-axe-syntaxp-hypsp-of-mv-nth-1-of-make-axe-rule-loop-stopping-hyps
   (all-axe-syntaxp-hypsp (mv-nth 1 (make-axe-rule-loop-stopping-hyps rule-classes rule-symbol)))
   :hints (("Goal" :in-theory (enable make-axe-rule-loop-stopping-hyps)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv erp rule).
;; Note: the format of the rule when stored in a rule-alist or rule-world is different (see stored-axe-rulep).
;; TODO: Consider deprecating this in favor of the stored-rule format.
(defund make-axe-rule (lhs rhs rule-symbol hyps extra-hyps print wrld)
  (declare (xargs :guard (and (axe-rule-lhsp lhs)
                              (pseudo-termp rhs)
                              (symbolp rule-symbol)
                              (pseudo-term-listp hyps) ;; from the theorem, unprocessed
                              (axe-rule-hyp-listp extra-hyps) ;; already processed, don't bind any vars, for stopping loops
                              (all-axe-syntaxp-hypsp extra-hyps)
                              (plist-worldp wrld))))
  (b* ((- (and print (cw "(Making Axe rule: ~x0.)~%" rule-symbol)))
       (lhs-vars (free-vars-in-term lhs))
       ;; Process and check the HYPS:
       ((mv erp processed-hyps bound-vars) (make-axe-rule-hyps hyps lhs-vars rule-symbol wrld nil))
       ((when erp) (mv erp nil))
       ;; Check the extra-hyps (loop-stoppers):
       ((when (not (bound-vars-suitable-for-hypsp lhs-vars extra-hyps)))
        (er hard? 'make-axe-rule "Bad vars in loop-stoppers in rule ~x0." rule-symbol)
        (mv :bad-loop-stoppers nil))
       ;; Check the RHS:
       (rhs-vars (free-vars-in-term rhs))
       ((when (not (subsetp-eq rhs-vars bound-vars)))
        (er hard? 'make-axe-rule "The RHS, ~x0, of rule ~x1 has free vars (namely, ~x2) that are not bound by the LHS or the hyps (which together bind ~x3)."
            rhs rule-symbol (set-difference-eq rhs-vars bound-vars) bound-vars)
        (mv :free-vars-in-rhs nil)))
    (mv (erp-nil)
        ; Form the rule (note that stored-rules take a different form):
        (list lhs rhs rule-symbol (append extra-hyps processed-hyps)))))

;; (defthm len-of-mv-nth-1-of-make-axe-rule
;;   (implies (not (mv-nth 0 (make-axe-rule lhs rhs rule-symbol hyps extra-hyps print wrld)))
;;            (equal (len (mv-nth 1 (make-axe-rule lhs rhs rule-symbol hyps extra-hyps print wrld)))
;;                   4))
;;   :hints (("Goal" :in-theory (enable make-axe-rule))))

;; (defthm true-listp-of-mv-nth-1-of-make-axe-rule
;;   (implies (not (mv-nth 0 (make-axe-rule lhs rhs rule-symbol hyps extra-hyps print wrld)))
;;            (true-listp (mv-nth 1 (make-axe-rule lhs rhs rule-symbol hyps extra-hyps print wrld))))
;;   :hints (("Goal" :in-theory (enable make-axe-rule))))

(defthm rule-lhs-of-mv-nth-1-of-make-axe-rule
  (implies (not (mv-nth 0 (make-axe-rule lhs rhs rule-symbol hyps extra-hyps print wrld)))
           (equal (rule-lhs (mv-nth 1 (make-axe-rule lhs rhs rule-symbol hyps extra-hyps print wrld)))
                  lhs))
  :hints (("Goal" :in-theory (enable rule-lhs make-axe-rule))))

(defthm rule-rhs-of-mv-nth-1-of-make-axe-rule
  (implies (not (mv-nth 0 (make-axe-rule lhs rhs rule-symbol hyps extra-hyps print wrld)))
           (equal (rule-rhs (mv-nth 1 (make-axe-rule lhs rhs rule-symbol hyps extra-hyps print wrld)))
                  rhs))
  :hints (("Goal" :in-theory (enable rule-rhs make-axe-rule))))

(defthm rule-symbol-of-mv-nth-1-of-make-axe-rule
  (implies (not (mv-nth 0 (make-axe-rule lhs rhs rule-symbol hyps extra-hyps print wrld)))
           (equal (rule-symbol (mv-nth 1 (make-axe-rule lhs rhs rule-symbol hyps extra-hyps print wrld)))
                  rule-symbol))
  :hints (("Goal" :in-theory (enable rule-symbol make-axe-rule))))

;gross?
(defthm rule-hyps-of-mv-nth-1-of-make-axe-rule
  (implies (not (mv-nth 0 (make-axe-rule lhs rhs rule-symbol hyps extra-hyps print wrld)))
           (equal (rule-hyps (mv-nth 1 (make-axe-rule lhs rhs rule-symbol hyps extra-hyps print wrld)))
                  (append extra-hyps (mv-nth 1 (make-axe-rule-hyps hyps (free-vars-in-term lhs) rule-symbol wrld nil)))))
  :hints (("Goal" :in-theory (enable rule-hyps make-axe-rule))))

(defthm axe-rulep-of-mv-nth-1-of-make-axe-rule
  (implies (and (not (mv-nth 0 (make-axe-rule lhs rhs rule-symbol hyps extra-hyps print wrld)))
                (axe-rule-lhsp lhs)
                (pseudo-termp rhs)
                (pseudo-term-listp hyps)
                (axe-rule-hyp-listp extra-hyps)
                (all-axe-syntaxp-hypsp extra-hyps) ;so we know they don't bind any vars
                (symbolp rule-symbol))
           (axe-rulep (mv-nth 1 (make-axe-rule lhs rhs rule-symbol hyps extra-hyps print wrld))))
  :hints (("Goal" :in-theory (enable axe-rulep
                                     make-axe-rule
                                     make-axe-rule-hyps-redef
                                     make-axe-rule-hyps-redef-0
                                     rule-lhs
                                     rule-rhs
                                     rule-hyps
                                     rule-symbol))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Splits the rule conclusion, CONC, into a left-hand-side and a
;; right-hand-side.  Returns (mv erp lhs rhs).
(defund lhs-and-rhs-of-conc (conc rule-symbol known-boolean-fns)
  (declare (xargs :guard (and (pseudo-termp conc)
                              (symbolp rule-symbol)
                              (symbol-listp known-boolean-fns))))
  (if (atom conc)
      (prog2$ (er hard? 'lhs-and-rhs-of-conc "Unexpected form (atom) of conclusion ~x0 in rule ~x1" conc rule-symbol)
              (mv :bad-conclusion nil nil))
    (b* ((fn (ffn-symb conc)))
      (if (eq 'equal fn)
          (if (not (consp (farg1 conc))) ; probably always true, since rewrite rules must have function calls on the lhs
              (prog2$ (er hard? 'lhs-and-rhs-of-conc "Unexpected form (not a cons) of LHS ~x0 in rule ~x1" (farg1 conc) rule-symbol)
                      (mv :bad-lhs nil nil))
            (if (eq 'quote (ffn-symb (farg1 conc)))
                (prog2$ (er hard? 'lhs-and-rhs-of-conc "Unexpected form (quoted thing) of LHS ~x0 in rule ~x1" (farg1 conc) rule-symbol)
                        (mv :bad-lhs nil nil))
              (if (symbolp (ffn-symb (farg1 conc)))
                  ;;(equal (<function> ...) ...): ;fixme what about lambdas?
                  (mv nil (expand-lambdas-in-term (farg1 conc)) (farg2 conc))
                (prog2$ (er hard? 'lhs-and-rhs-of-conc "Unexpected form of conclusion ~x0 in rule ~x1" conc rule-symbol)
                        (mv :bad-conclusion nil nil)))))
        (if (eq 'not fn)
            (if (and (consp (farg1 conc)) ;; (these are probably always true, since rewrite rules must have function calls on the lhs
                     (symbolp (ffn-symb (farg1 conc)))
                     (not (eq 'quote (ffn-symb (farg1 conc)))))
                ;; (not (<function> ..)):
                ;;(not x) is the same as (equal x 'nil):
                (mv nil (expand-lambdas-in-term (farg1 conc)) *nil*)
              (prog2$ (er hard? 'lhs-and-rhs-of-conc "Unexpected form of conclusion ~x0 in rule ~x1" conc rule-symbol)
                      (mv :bad-conclusion nil nil)))
          (if (eq 'quote fn)
              (prog2$ (er hard? 'lhs-and-rhs-of-conc "Unexpected form (quoted constant) of conclusion ~x0 in rule ~x1" conc rule-symbol)
                      (mv :bad-conclusion nil nil))
            (if (consp fn)
                (prog2$ (er hard? 'lhs-and-rhs-of-conc "Unexpected form (lambda application) of conclusion ~x0 in rule ~x1" conc rule-symbol)
                        (mv :bad-conclusion nil nil))
              (if (member-eq fn known-boolean-fns)
                  ;; pred -> (equal pred 't)
                  (mv nil (expand-lambdas-in-term conc) *t*)
                (prog2$ (er hard? 'lhs-and-rhs-of-conc "Unexpected form of conclusion (not an equality, a call of not, or a call of a known-boolean) ~x0 in rule ~x1" conc rule-symbol)
                        (mv :bad-conclusion nil nil))))))))))

(local
 (defthm axe-rule-lhsp-of-mv-nth-1-of-lhs-and-rhs-of-conc
  (implies (and (not (mv-nth 0 (lhs-and-rhs-of-conc conc rule-symbol known-boolean-fns)))
                (pseudo-termp conc))
           (axe-rule-lhsp (mv-nth 1 (lhs-and-rhs-of-conc conc rule-symbol known-boolean-fns))))
  :hints (("Goal"  :expand ((expand-lambdas-in-term conc))
           :in-theory (enable lhs-and-rhs-of-conc axe-rule-lhsp
                              symbol-listp)))))

(local
 (defthm pseudo-termp-of-mv-nth-2-of-lhs-and-rhs-of-conc
  (implies (and (not (mv-nth 0 (lhs-and-rhs-of-conc conc rule-symbol known-boolean-fns)))
                (pseudo-termp conc))
           (pseudo-termp (mv-nth 2 (lhs-and-rhs-of-conc conc rule-symbol known-boolean-fns))))
  :hints (("Goal" :in-theory (enable lhs-and-rhs-of-conc)))))

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Possibly adds an axe-rule to ACC.
;;fixme be more general?
;; TODO: Return an error?
(defund add-axe-rule-for-conjunct (conc
                                   hyps
                                   extra-hyps
                                   counter ;nil means this is the only conjunct of the rule
                                   rule-symbol
                                   known-boolean-fns
                                   print
                                   wrld
                                   acc)
  (declare (xargs :guard (and (pseudo-termp conc)
                              (pseudo-term-listp hyps)        ;from the theorem
                              (axe-rule-hyp-listp extra-hyps) ;already processed
                              (all-axe-syntaxp-hypsp extra-hyps)
                              (or (natp counter) (equal nil counter))
                              (symbolp rule-symbol)
                              (symbol-listp known-boolean-fns)
                              (plist-worldp wrld))))
  (b* (((mv erp lhs rhs) (lhs-and-rhs-of-conc conc rule-symbol known-boolean-fns))
       ((when erp) acc) ;don't extend acc
       ;; Applies various simplifications:
       (rhs (pre-simplify-term rhs nil nil)) ; must preserve equal, not just iff
       ((mv erp rule) (make-axe-rule lhs rhs
                                     (if counter
                                         ;; todo: make a pack-string and pass to add-suffix:
                                         (pack-in-package-of-symbol rule-symbol rule-symbol '-conjunct- (nat-to-string counter))
                                       rule-symbol)
                                     hyps
                                     extra-hyps
                                     print
                                     wrld))
       ((when erp) acc) ;don't extend acc
       )
    (cons rule acc)))

;; (defthm symbolp-when-memberp
;;   (implies (and (memberp x free)
;;                 (symbol-listp free))
;;            (symbolp x))
;;   :hints (("Goal" :in-theory (enable symbol-listp))))

(local
 (defthm axe-rule-listp-of-add-axe-rule-for-conjunct
   (implies (and (symbolp rule-symbol)
                 (pseudo-termp conc)
                 (pseudo-term-listp hyps)
                 (axe-rule-hyp-listp extra-hyps)
                 (axe-rule-listp acc)
                 (all-axe-syntaxp-hypsp extra-hyps))
            (axe-rule-listp (add-axe-rule-for-conjunct conc hyps extra-hyps counter rule-symbol known-boolean-fns print wrld acc)))
   :hints (("Goal" :in-theory (enable ;axe-rulep
                              ;;symbol-listp
                               add-axe-rule-for-conjunct)))))

(local
 (defthm true-listp-of-add-axe-rule-for-conjunct
   (implies (true-listp acc)
            (true-listp (add-axe-rule-for-conjunct conc hyps extra-hyps counter rule-symbol known-boolean-fns print wrld acc)))
   :hints (("Goal" :in-theory (e/d (add-axe-rule-for-conjunct) (true-listp))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns an axe-rule-list.
;; Extracts conjuncts from CONC and makes a rule for each
;; TODO: What about lambdas that hide conjunctions?
(defund make-axe-rules-from-conclusion-aux (conc hyps extra-hyps counter rule-symbol known-boolean-fns print wrld)
  (declare (xargs :guard (and (pseudo-termp conc)
                              (pseudo-term-listp hyps)
                              (axe-rule-hyp-listp extra-hyps) ;already processed
                              (all-axe-syntaxp-hypsp extra-hyps)
                              (natp counter)
                              (symbolp rule-symbol)
                              (symbol-listp known-boolean-fns)
                              (plist-worldp wrld))))
  (if (atom conc)
      (er hard? 'make-axe-rules-from-conclusion-aux "Unexpected form (atom) of a conclusion for ~x0" conc)
    (if (eq 'if (ffn-symb conc))
        (if (equal *nil* (farg3 conc))
            ;;it's an AND, represented as (if <x> <y> 'nil):
            (add-axe-rule-for-conjunct (farg1 conc) hyps extra-hyps counter rule-symbol known-boolean-fns print wrld
                                   (make-axe-rules-from-conclusion-aux (farg2 conc) hyps extra-hyps (+ 1 counter) rule-symbol known-boolean-fns print wrld))
          ;; TODO: Perhaps we should support this (ACL2 can now rewrite an IF):
          (er hard? 'make-axe-rules-from-conclusion-aux "Unexpected form of a conclusion (an IF that does not represent a conjunction): ~x0" conc))
      (add-axe-rule-for-conjunct conc hyps extra-hyps counter rule-symbol known-boolean-fns print wrld nil))))

(local
 (defthm axe-rule-listp-of-make-axe-rules-from-conclusion-aux
   (implies (and (symbolp rule-symbol)
                 (pseudo-termp conc)
                 (pseudo-term-listp hyps)
                 (axe-rule-hyp-listp extra-hyps)
                 (all-axe-syntaxp-hypsp extra-hyps))
            (axe-rule-listp (make-axe-rules-from-conclusion-aux conc hyps extra-hyps counter rule-symbol known-boolean-fns print wrld)))
   :hints (("Goal" :in-theory (enable axe-rulep make-axe-rules-from-conclusion-aux)))))

(local
 (defthm true-listp-of-make-axe-rules-from-conclusion-aux
   (true-listp (make-axe-rules-from-conclusion-aux conc hyps extra-hyps counter rule-symbol known-boolean-fns print wrld))
   :hints (("Goal" :in-theory (enable axe-rulep make-axe-rules-from-conclusion-aux)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns an axe-rule-list.
;fixme pass in a rule symbol only?
(defund make-axe-rules-from-conclusion (conc hyps extra-hyps rule-symbol known-boolean-fns print wrld)
  (declare (xargs :guard (and (pseudo-termp conc)
                              (pseudo-term-listp hyps) ;from the theorem
                              (axe-rule-hyp-listp extra-hyps) ;already processed
                              (all-axe-syntaxp-hypsp extra-hyps)
                              (symbolp rule-symbol)
                              (symbol-listp known-boolean-fns)
                              (plist-worldp wrld))))
  (if (call-of 'if conc)
      ;;the rules will be tagged with the conjunct number:
      (make-axe-rules-from-conclusion-aux conc hyps extra-hyps 1 rule-symbol known-boolean-fns print wrld)
    ;;there is only one conclusion:
    (add-axe-rule-for-conjunct conc hyps extra-hyps nil rule-symbol known-boolean-fns print wrld nil)))

(local
 (defthm axe-rule-listp-of-make-axe-rules-from-conclusion
   (implies (and (symbolp rule-symbol)
                 (pseudo-termp conc)
                 (pseudo-term-listp hyps)
                 (axe-rule-hyp-listp extra-hyps)
                 (all-axe-syntaxp-hypsp extra-hyps))
            (axe-rule-listp (make-axe-rules-from-conclusion conc hyps extra-hyps rule-symbol known-boolean-fns print wrld)))
   :hints (("Goal" :in-theory (enable make-axe-rules-from-conclusion axe-rulep)))))

(local
 (defthm true-listp-of-make-axe-rules-from-conclusion
   (true-listp (make-axe-rules-from-conclusion conc hyps extra-hyps rule-symbol known-boolean-fns print wrld))
   :hints (("Goal" :in-theory (e/d (make-axe-rules-from-conclusion) (axe-rulep))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Splits an ACL2 theorem into hypotheses and a conclusion.
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
    (if (consp (car theorem-body)) ; check for lambda
        (mv `(:bad-rule ,rule-name)
            (er hard? 'hyps-and-conc-for-axe-rule "Unable to make an Axe rule from ~x0 (theorem body is a lambda application, which is not yet supported): ~x1" rule-name theorem-body)
            nil)
      (if (and (call-of 'implies theorem-body)
               (= 2 (len (fargs theorem-body)))) ;for guards
          ;; TODO: Support nested implies?
          (mv (erp-nil)
              (get-conjuncts (farg1 theorem-body)) ; multiple hyps
              (farg2 theorem-body) ; single conclusion (for now)
              )
        (mv (erp-nil)
            nil ;no hyps
            theorem-body)))))

(local
 (defthm pseudo-termp-of-mv-nth-2-of-hyps-and-conc-for-axe-rule
   (implies (pseudo-termp term)
            (pseudo-termp (mv-nth 2 (hyps-and-conc-for-axe-rule term sym))))
   :hints (("Goal" :in-theory (enable hyps-and-conc-for-axe-rule)))))

(local
 (defthm pseudo-term-listp-of-mv-nth-1-of-hyps-and-conc-for-axe-rule
   (implies (pseudo-termp term)
            (pseudo-term-listp (mv-nth 1 (hyps-and-conc-for-axe-rule term sym))))
   :hints (("Goal" :in-theory (enable hyps-and-conc-for-axe-rule)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv erp axe-rules).  If the conclusion is a conjunction, we get multiple rules.
(defund make-axe-rules-from-theorem (theorem-body rule-symbol rule-classes known-boolean-fns print wrld)
  (declare (xargs :guard (and (pseudo-termp theorem-body)
                              (symbolp rule-symbol)
                              (symbol-alistp rule-classes)
                              (symbol-listp known-boolean-fns)
                              (plist-worldp wrld))))
  (b* ( ;; Split the rule into conclusion and hyps:
       ((mv erp hyps conc)
        (hyps-and-conc-for-axe-rule theorem-body rule-symbol))
       ((when erp) (mv erp nil))
       ;; We can't process the hyps yet because we don't know the LHS vars
       ;; (there may be several LHSes).  But we can create the
       ;; loop-stopping-hyps here because they do not bind any vars:
       ((mv erp extra-hyps)
        (make-axe-rule-loop-stopping-hyps rule-classes rule-symbol))
       ((when erp) (mv erp nil)))
    ;; the conclusion may have multiple conjuncts:
    (mv (erp-nil)
        (make-axe-rules-from-conclusion conc hyps extra-hyps rule-symbol known-boolean-fns print wrld))))

(local
 (defthm axe-rule-listp-of-mv-nth-1-of-make-axe-rules-from-theorem
   (implies (and (pseudo-termp theorem-body)
                 (symbolp rule-symbol))
            (axe-rule-listp (mv-nth 1 (make-axe-rules-from-theorem theorem-body rule-symbol rule-classes known-boolean-fns print wrld))))
   :hints (("Goal" :in-theory (enable make-axe-rules-from-theorem
                                      axe-rulep ;fixme
                                      )))))

(local
 (defthm true-listp-of-mv-nth-1-of-make-axe-rules-from-theorem
   (true-listp (mv-nth 1 (make-axe-rules-from-theorem theorem-body rule-symbol rule-classes known-boolean-fns print wrld)))
   :hints (("Goal" :in-theory (enable make-axe-rules-from-theorem)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns the axe-rules.  Does not return erp.
(defund make-axe-rules-from-theorem! (theorem-body rule-symbol rule-classes known-boolean-fns print wrld)
  (declare (xargs :guard (and (pseudo-termp theorem-body)
                              (symbolp rule-symbol)
                              (symbol-alistp rule-classes)
                              (symbol-listp known-boolean-fns)
                              (plist-worldp wrld))))
  (mv-let (erp axe-rules)
    (make-axe-rules-from-theorem theorem-body rule-symbol rule-classes known-boolean-fns print wrld)
    (if erp
        (er hard? 'make-axe-rules-from-theorem! "Error making Axe rules.")
      axe-rules)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Extends ACC with one or more axe-rules for RULE-NAME.  Returns (mv erp new-acc) where new-acc is an axe-rule-listp.
;; Keep this in sync with ensure-rule-known?
(defund add-axe-rules-for-rule (rule-name known-boolean-fns print acc wrld)
  (declare (xargs :guard (and (symbolp rule-name)
                              (symbol-listp known-boolean-fns)
                              (axe-rule-listp acc)
                              (ilks-plist-worldp wrld))))
  (b* (((when (eq 'quote rule-name))
        (er hard? 'add-axe-rules-for-rule "QUOTE is an illegal name for an Axe rule.")
        (mv :bad-rule-name acc))
       ;; (- (cw "Making axe-rule for ~x0.~%" rule-name))
       (theoremp (defthm-or-defaxiom-symbolp rule-name wrld))
       (functionp (function-symbolp rule-name wrld)))
    (cond ((and (not functionp)
                (not theoremp))
           (prog2$ (er hard? 'add-axe-rules-for-rule "~x0 does not seem to be a theorem/axiom or defun." rule-name)
                   (mv :rule-not-found acc)))
          ((and functionp theoremp)
           (prog2$ (er hard? 'add-axe-rules-for-rule "~x0 appears to be both a function and a theorem/axiom (so which is it?!)" rule-name)
                   (mv :confusing-rule-name acc)))
          (functionp
           ;;it's a defun:
           (b* ((formals (fn-formals rule-name wrld))
                (body (fn-body rule-name t wrld))
                ;; If we don't handle return-last, the axe rule for
                ;; string-append causes a loop.  Also, this should make it
                ;; faster to open functions defined using MBE:
                (body (remove-guard-holders-and-clean-up-lambdas body) ;(strip-return-last body)
                      )
                (body (pre-simplify-term body nil nil)) ; must preserve equal, not just iff
                (clique (true-list-fix ; drop?
                          (recursivep rule-name nil wrld))) ; todo: consider :definition rules and the flg option here
                (body-fns (all-fnnames body))
                (- (if (member-eq rule-name body-fns)
                       (cw "Warning: Make safe openers for recursive function ~x0.~%" rule-name)
                     (if (intersection-eq clique body-fns)
                         (cw "Warning: Make safe openers for mut. rec. function ~x0.~%" rule-name)
                       nil)))
                (lhs (cons rule-name formals))
                ;; Make a rule equating a call of the function (on its formals)
                ;; with its body (note: for recursive functions, it may be
                ;; better to use defopeners to get separate cases for the
                ;; recursive case and the base case):
                ((mv erp rule) (make-axe-rule lhs body rule-name nil nil print wrld))
                ((when erp) (mv erp acc)))
             (mv (erp-nil) (cons rule acc))))
          (t ;;it's a theorem/axiom:
           (b* ((theorem-body (defthm-body rule-name wrld))
                (rule-classes (defthm-rule-classes rule-name wrld))
                ((when (not (symbol-alistp rule-classes)))
                 (er hard? 'make-add-axe-rules-for-rule "Bad rule-classes: ~x0" rule-classes)
                 (mv :bad-rule-classes nil))
                ;;otherwise, unrolling rules of functions using mbe can loop:
                (theorem-body ;(strip-return-last theorem-body)
                  (remove-guard-holders-and-clean-up-lambdas theorem-body))
                ;; we simplify the rhs elsewhere.  we should not call pre-simplify-term here, because it might affect the LHS as well (e.g., turning (equal (= x y) (equal x y))
                ;; into (equal (equal x y) (equal x y)), which would loop.
                ((mv erp rules)
                 (make-axe-rules-from-theorem theorem-body rule-name rule-classes known-boolean-fns print wrld))
                ((when erp) (mv erp acc)))
             (mv (erp-nil)
                 (append rules acc)))))))

(local
 (defthm axe-rule-listp-of-mv-nth-1-of-add-axe-rules-for-rule
   (implies (and (axe-rule-listp acc)
                 (symbolp rule-name))
            (axe-rule-listp (mv-nth 1 (add-axe-rules-for-rule rule-name known-boolean-fns print acc wrld))))
   :hints (("Goal" :in-theory (enable add-axe-rules-for-rule)))))

(local
 (defthm true-listp-of-mv-nth-1-of-add-axe-rules-for-rule
   (implies (true-listp acc)
            (true-listp (mv-nth 1 (add-axe-rules-for-rule rule-name known-boolean-fns print acc wrld))))
   :hints (("Goal" :in-theory (enable add-axe-rules-for-rule)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; For each of the RULE-NAMES, look it up in the world and add one or more rules for it to ACC.
;; Returns (mv erp rules) where rules is a list of axe-rules.
(defund make-axe-rules-aux (rule-names known-boolean-fns print acc wrld)
  (declare (xargs :guard (and (symbol-listp rule-names)
                              (symbol-listp known-boolean-fns)
                              (axe-rule-listp acc)
                              (ilks-plist-worldp wrld))))
  (if (endp rule-names)
      (mv (erp-nil) (reverse acc)) ;skip this reverse! or call a better version of it that doesn't handle strings?
    (b* (((mv erp res)
          (add-axe-rules-for-rule (first rule-names) known-boolean-fns print acc wrld))
         ((when erp) (mv erp acc)))
      (make-axe-rules-aux (rest rule-names) known-boolean-fns print
                          res
                          wrld))))

(local
 (defthm true-listp-of-mv-nth-1-of-make-axe-rules-aux
   (implies (true-listp acc)
            (true-listp (mv-nth 1 (make-axe-rules-aux rule-names known-boolean-fns print acc wrld))))
   :hints (("Goal" :in-theory (enable make-axe-rules-aux)))))

(local
 (defthm axe-rule-listp-of-mv-nth-1-of-make-axe-rules-aux
   (implies (and (axe-rule-listp acc)
                 (true-listp acc)
                 (symbol-listp rule-names))
            (axe-rule-listp (mv-nth 1 (make-axe-rules-aux rule-names known-boolean-fns print acc wrld))))
   :hints (("Goal" :in-theory (enable make-axe-rules-aux)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv erp rules) where rules is a list of axe-rules.
;; Does not remove duplicates (that should be done when making the rule-alist).
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; This variant doesn't pass back an error
(defund make-axe-rules! (rule-names wrld)
  (declare (xargs :guard (and (symbol-listp rule-names)
                              (ilks-plist-worldp wrld))))
  (mv-let (erp axe-rules)
    (make-axe-rules rule-names wrld)
    (if erp
        (er hard? 'make-axe-rules! "Error making Axe rules.")
      axe-rules)))

(defthm axe-rule-listp-of-make-axe-rules!
  (implies (symbol-listp rule-names)
           (axe-rule-listp (make-axe-rules! rule-names wrld)))
  :hints (("Goal" :in-theory (enable make-axe-rules!))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv erp rules) where rules is a list of axe-rules.
; rename extend-rule-list
(defun add-rules-to-rule-set (rule-names rule-set wrld)
  (declare (xargs :guard (and (symbol-listp rule-names)
                              (axe-rule-listp rule-set)
                              (ilks-plist-worldp wrld))))
  (b* (((mv erp rules) (make-axe-rules rule-names wrld))
       ((when erp) (mv erp rule-set)))
    (mv (erp-nil)
        ;; todo: append here would be fasters: think about duplicates and ordering
        (union-equal rules rule-set))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Introduces all-axe-rule-listp:
;; this is really axe-rule-setsp:
(defforall-simple axe-rule-listp)
(verify-guards all-axe-rule-listp)

;; Recognize a true-list of axe-rule-sets.
(defun axe-rule-setsp (items)
  (declare (xargs :guard t))
  (and (all-axe-rule-listp items)
       (true-listp items)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv erp rule-sets).
;; Add the given rules to each rule set in RULE-SETS.
;todo: optimze?
; rename extend-rule-lists
(defun add-rules-to-rule-sets (rule-names rule-sets wrld)
  (declare (xargs :guard (and (symbol-listp rule-names)
                              (axe-rule-setsp rule-sets)
                              (ilks-plist-worldp wrld))))
  (if (endp rule-sets)
      (mv (erp-nil) nil)
    (b* (((mv erp first-rule-set)
          (add-rules-to-rule-set rule-names (first rule-sets) wrld))
         ((when erp) (mv erp nil))
         ((mv erp rest-rule-sets)
          (add-rules-to-rule-sets rule-names (rest rule-sets) wrld))
         ((when erp) (mv erp nil)))
      (mv (erp-nil)
          (cons first-rule-set rest-rule-sets)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; rename extend-rule-lists!
;; Returns the new rule-sets.  Does not return erp.
(defun add-rules-to-rule-sets! (rule-names rule-sets wrld)
  (declare (xargs :guard (and (symbol-listp rule-names)
                              (axe-rule-setsp rule-sets)
                              (ilks-plist-worldp wrld))))
  (mv-let (erp rule-sets)
    (add-rules-to-rule-sets rule-names rule-sets wrld)
    (if erp
        (er hard? 'add-rules-to-rule-sets! "Error adding rules to rule-sets.")
      rule-sets)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Where should this stuff go?:

;; Can be used to determine which rules introduce a given function symbol
(defund filter-axe-rules-for-rhses-mentioning (fn axe-rules)
  (declare (xargs :guard (and (symbolp fn)
                              (axe-rule-listp axe-rules))
                  :guard-hints (("Goal" :in-theory (enable len-when-axe-rulep)))))
  (if (endp axe-rules)
      nil
    (let* ((axe-rule (first axe-rules))
           (rhs (rule-rhs axe-rule))
           (rhs-fns (get-fns-in-term rhs)))
      (if (member-eq fn rhs-fns)
          (cons (rule-symbol axe-rule)
                (filter-axe-rules-for-rhses-mentioning fn (rest axe-rules)))
        (filter-axe-rules-for-rhses-mentioning fn (rest axe-rules))))))

;; overkill to actually make the rules?
(defund axe-rules-that-introduce (fn rule-names wrld)
  (declare (xargs :guard (and (symbolp fn)
                              (symbol-listp rule-names)
                              (ilks-plist-worldp wrld))))
  (let ((axe-rules (make-axe-rules! rule-names wrld)))
    (filter-axe-rules-for-rhses-mentioning fn axe-rules)))
