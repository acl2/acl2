#|$ACL2s-Preamble$;
(include-book ;; Newline to fool ACL2/cert.pl dependency scanner
 "portcullis")
(begin-book t :ttags :all);$ACL2s-Preamble$|#

(in-package "ACL2S")
(include-book "cgen/top" :ttags :all)
(include-book "utilities")
(include-book "kestrel/utilities/symbols" :dir :system)
(include-book "kestrel/utilities/user-interface" :dir :system)
(include-book "kestrel/utilities/er-soft-plus" :dir :system)
(include-book "centaur/misc/outer-local" :dir :system)

#|
Here is the top-level defunc control flow:

Test phase:
  skip-proofs defun
  If test? function-contract fails
    return message; quit
  ;;skip-proofs (function-contract)
  ;;maybe function-contract fails
  If test? body-contracts fails
    return message; quit

Logic-mode or program-mode?
  If function terminates then logic-mode else program-mode

Program-mode
 defun/program-mode; fail /or :success

Logic-mode
  FC: Function-contract holds?
  If FC then
     defun-ng/static; FC;
      BC: body contracts hold?
      if BC then verify-guards
      else
       message+= check: defun-ng/static; FC; verify-guard. defun, FC should pass &
                 verify-guard should fail;
       fail /or :success
  else
    message+=check: defun-ng; FC, defun should pass, FC will fail;
    fail /or defun-ng/dynamic;
    BC: dynamic-body contracts hold?
    if BC then verify-guards; :success
    else
      message+= check: defun-ng/dynamic; FC, verify-guards. Only defun passes;
      fail /or :success


Here is one way of encoding the above flow using nested make-event with :OR
Let termination-strictp, function-contract-strictp and body-contracts-strictp be defined in a table (or globally).

(make-event
 (er-progn
   (test-phase ...)
   (cond ((and termination-strictp function-contract-strictp)
           `(:OR ,(static-defunc-events ...)
                 ,(make-show-failure-msg-ev ...)))
          (termination-strictp
           `(:OR ,(static-defunc-events ...)
                 ,(dynamic-defunc-events ...)
                 ,(make-show-failure-msg-ev ...)))
          (t `(:OR ,(static-defunc-events ...)
                   ,(dynamic-defunc-events ...)
                   ,(program-mode-defunc-events ...)
                   ,(make-show-failure-msg-ev ...))))))
||#


#!ACL2
(defun function-guard-obligation (fun-name state)
  (declare (xargs :mode :program
                  :stobjs (state)))
  (b* (((mv cl-set &) (guard-clauses-for-clique (list fun-name)
                                                T ;debug-p
                                                (ens state)
                                                (w state)
                                                (f-get-global 'safe-mode state)
                                                (gc-off state)
                                                nil))
       (guard-ob (prettyify-clause-set cl-set (let*-abstractionp state) (w state)))
       ;;(- (cw "fn: ~x0 and body-contract-obligation: ~x1~%" fun-name guard-ob))
       )
    (value guard-ob)))



(mutual-recursion
 (defun simple-termp (x)
   (declare (xargs :guard t))
   (cond ((atom x) t)
         ((eq (car x) 'quote)
          (and (consp (cdr x))
               (null (cdr (cdr x)))))
         ((not (true-listp x)) nil)
         ((not (simple-term-listp (cdr x))) nil)
         (t (or (symbolp (car x))
                (and (true-listp (car x))
                     (equal (length (car x)) 3)
                     (eq (car (car x)) 'lambda)
                     (symbol-listp (cadr (car x)))
                     (simple-termp (caddr (car x)))
                     (equal (length (cadr (car x)))
                            (length (cdr x))))))))

 (defun simple-term-listp (lst)
   (declare (xargs :guard t))
   (cond ((atom lst) (equal lst nil))
         (t (and (simple-termp (car lst))
                 (simple-term-listp (cdr lst)))))))

(defun replace-in-term (old new term)
  "replace all occurrences of old in term with new"
  (declare (xargs :guard t))
  (cond ((equal term old)
         new)
        ((atom term)
         term)
        (t (cons (replace-in-term old new (car term))
                 (replace-in-term old new (cdr term))))))

(defun in-termp (x term)
  ;; is x in term?
  (declare (xargs :guard t))
  (not (equal term (replace-in-term x (list x x) term))))


(defun xargs-kwd-alist1 (decls keywords ctx al)
  (if (atom decls)
      al
    (if (and (consp (car decls))
             (eq 'acl2::declare (caar decls))
             (consp (cdr (car decls)))
             (consp (cadr (car decls)))
             (eq 'acl2::xargs (first (cadr (car decls)))))
        (b* ((kwd-val-list (cdr (cadr (car decls))))
             ((mv al ?rest-args) (defdata::extract-keywords ctx keywords kwd-val-list al)))
          (xargs-kwd-alist1 (cdr decls) keywords ctx al))
      (xargs-kwd-alist1 (cdr decls) keywords ctx al))))

(defconst *our-xargs-keywords* (append '(:CONSIDER-CCMS :CONSIDER-ONLY-CCMS :TERMINATION-METHOD
                                                        :CCG-PRINT-PROOFS :TIME-LIMIT
                                                        :CCG-HIERARCHY)
                                       acl2::*xargs-keywords*))

(defun xargs-kwd-alist (decls ctx)
  "Parse a list of declare forms into a kwd-alist mapping xarg keywords to their values."
  (xargs-kwd-alist1 decls *our-xargs-keywords* ctx nil))

#!ACL2
(verify-termination find-runed-lemma (declare (xargs :measure (if (null lst) 0 (1+ (acl2-count lst))))))

;returns controller pocket
#!ACL2
(defun controller-alist (nm wrld)
  (if (and (not (symbolp nm))
           (not (function-symbolp nm wrld)))
      nil
    (let ((rl (find-runed-lemma `(:definition ,nm)
                                (getprop nm 'lemmas nil 'current-acl2-world wrld))))
      (if rl
          (let ((ctrl-pocket
                 (cdr (assoc-eq nm (cdr (access rewrite-rule rl :heuristic-info))))))

; PETE: I replaced this because in the degenerate case where
;       there is no 'T, then termination does not depend on any variable
;       and if we use nil in the definition rule defunc
;       generates, we get an error.
            ;; (if (member 'T ctrl-pocket)
            ;;     ctrl-pocket
            ;;     nil)
            ctrl-pocket
            )
        nil))))

(include-book "coi/util/pseudo-translate" :dir :system)

(defun c-is-t (c)
  (or (equal c 't) (equal c ''t)))

(defun type-of-pred (pred tbl)
  (cond ((endp tbl) nil)
        ((equal pred (get-alist :predicate (cdar tbl)))
         (caar tbl))
        (t (type-of-pred pred (cdr tbl)))))

; (type-of-pred 'integerp (table-alist 'defdata::type-metadata-table (w state)))
; (type-of-pred nil (table-alist 'defdata::type-metadata-table (w state)))

(defun enum-of-type (type tbl)
  (get-alist :enumerator (get-alist type tbl)))

; (enum-of-type 'integer (table-alist 'defdata::type-metadata-table (w state)))

(defun base-val-of-type (type tbl)
  (get-alist :default-base-value (get-alist type tbl)))

; (base-val-of-type 'integer (table-alist 'defdata::type-metadata-table (w state)))

(defun pred-of-oc (name formals oc)
  (and (consp oc) 
       (equal (cdr oc) `((,name ,@formals)))
       (car oc)))

(acl2::program)
(defun add-output-contract-check (body output-contract fun-name fun-args wrld)
  "To body, we insert a runtime check for output-contract."
  (b* (;(ctx 'add-output-contract-check)
       ((mv ?erp tbody) (acl2::pseudo-translate body (list (cons fun-name fun-args)) wrld))
       (vars (all-vars tbody))
       (avoid-lst (union-eq fun-args vars))
       (return-var (acl2::generate-variable '_ret avoid-lst nil nil wrld)))
    `(let ((,return-var ,body))
       (if ,(replace-in-term `(,fun-name ,@fun-args)
                             return-var
                             output-contract)
           ,return-var
         (er hard ',fun-name
             ;; harshrc-- Should we really give an hard
             ;; error here? Perhaps a warning is sufficient, atleast in the
             ;; case where the input-contract was violated in the first place.
             "**Output contract violation**: ~x0 with argument list ~x1 returned ~x2.~%"
             ',fun-name (list ,@fun-args) ,return-var)))))

(defun get-undef-name (pred w)
  (declare (xargs :mode :program :guard (symbolp pred)))
  (b* ((tbl (table-alist 'defdata::type-metadata-table w))
       (type (type-of-pred pred tbl))
       (undef-name (if type
                       (make-symbl `(acl2s::acl2s - ,type -undefined))
                     'acl2s::acl2s-undefined)))
      (if (acl2::arity undef-name w)
          undef-name
        'acl2s::acl2s-undefined)))

(defun make-defun-body/logic (name formals ic oc body wrld make-staticp)
  (b* ((with-ic-body
        (if (c-is-t ic)
            body
          `(if ,ic
               ,body
             (,(get-undef-name (pred-of-oc name formals oc) wrld)
              (quote ,name)
              (list ,@formals))))))
    (if make-staticp
        with-ic-body
      (add-output-contract-check with-ic-body oc name formals wrld))))

(defun make-defun-body/exec (name formals oc body wrld make-staticp)
  (if make-staticp
      body
    (add-output-contract-check body oc name formals wrld)))

(defun make-generic-typed-defunc-events
    (name formals ic oc decls body kwd-alist wrld make-staticp)
  "Generate events which simulate a typed ACL2s language."
  (b* ((recursivep (defdata::get1 :recursivep kwd-alist))
       (lbody (make-defun-body/logic name formals ic oc body wrld make-staticp))
       (ebody (make-defun-body/exec name formals oc body wrld make-staticp))
       (fun-ind-name (make-sym name 'induction-scheme-from-definition))
       (ind-scheme-name (make-sym name 'induction-scheme)))
    (append

; Submit a function to get an induction scheme?
; Would be good to reuse the termination proof we already did here,
; but the use of ccg make that hard
     (and recursivep
          `((defun ,fun-ind-name ,formals
              ,@decls
              ,(replace-in-term name fun-ind-name lbody))))

     ;; The above defun can take a long time to admit, but
     ;; since its termination argument is exactly the same
     ;; as the main defun, I should investigate how to make
     ;; it go throuh automatically (as we do with many of
     ;; the other forms).


; Induction scheme
     (and recursivep
          `((defthm ,ind-scheme-name
              t
              :rule-classes ((:induction :pattern ,(cons name formals)
                                         :condition ,ic
                                         :scheme ,(cons fun-ind-name formals))))))

; Definitional Rule
     `((with-output :stack :push :off :all
         (make-event
          (let ((controller-alist (acl2::controller-alist ',name (w state))))
            `(with-output :stack :pop
               (defthm ,(make-sym ',name 'definition-rule)
                 (implies ,',ic
                          (equal ,(cons ',name ',formals)
                                 ,',ebody))
                 :hints (("Goal" :use ,',name :in-theory nil))
                 :rule-classes ((:definition
                                 ,@(if ,recursivep
                                       `(:controller-alist
                                         ((,',name ,@controller-alist)))
                                     nil)))))))))
     ;; The controller-alist argument above is useful when
     ;; we use CCG analysis or an explicit measure. We
     ;; should use whatever controller-alist we used for the
     ;; original function definition.

     ;; Notice also that if defunc does not work with
     ;; mutually recursive definitions. If I wanted it to
     ;; work, I'd have to (in addition to other things), add
     ;; a :clique argument to the above definition rule.

; Disable some rules
     `((in-theory (disable (:definition ,name)
                           ,@(and recursivep
                                  `((:induction ,name)
                                    (:definition ,fun-ind-name))))))
     )))


(logic)

(defun map-force-list (l)
  (if (endp l)
      l
    (cons `(force ,(car l))
          (map-force-list (cdr l)))))

(defun map-force-ic (ic)
  (cond ((equal ic 't) 't)
        ((and (consp ic)
              (equal (car ic) 'acl2::and))
         (cons 'and (map-force-list (cdr ic))))
        (t `(force ,ic))))

(defun make-contract-body (name ic oc formals w)
  (declare (xargs :mode :program))
  (b* ((pred (pred-of-oc name formals oc))
       (undef-name (get-undef-name pred w)))
    (if (or (c-is-t ic)
            (not (equal undef-name 'acl2s::acl2s-undefined)))
        (mv oc t)
      (mv `(implies ,(map-force-ic ic) ,oc) nil))))

(defun make-contract-defthm (name ic oc kwd-alist formals w)
  (declare (xargs :mode :program))
  (b* ((instructions (defdata::get1 :instructions kwd-alist))
       (otf-flg (defdata::get1 :otf-flg kwd-alist))
       (hints (defdata::get1 :function-contract-hints kwd-alist))
       (rule-classes (defdata::get1 :rule-classes kwd-alist))
       ((mv body &) (make-contract-body name ic oc formals w)))
    `(DEFTHM ,(make-sym name 'CONTRACT)
       ,body
       ,@(and hints `(:HINTS ,hints))
       ,@(and rule-classes `(:RULE-CLASSES ,rule-classes))
       ,@(and otf-flg `(:OTF-FLG ,otf-flg))
       ,@(and instructions `(:INSTRUCTIONS ,instructions)))))

(defun make-contract-ev (name formals ic oc kwd-alist make-staticp w)
  (declare (xargs :mode :program))
  (b* (((when (c-is-t oc)) nil) ;trivially satisfied
       (function-contract-strictp
        (defdata::get1 :function-contract-strictp kwd-alist))
       (instructions (defdata::get1 :instructions kwd-alist))
       (otf-flg (defdata::get1 :otf-flg kwd-alist))
       (hints (defdata::get1 :function-contract-hints kwd-alist))
       (rule-classes (defdata::get1 :rule-classes kwd-alist))
       ((mv body no-hyps?) (make-contract-body name ic oc formals w))
       (contract-name (make-sym name 'CONTRACT))
       (contract-tpname (make-sym name 'CONTRACT-TP))
       (recursivep (defdata::get1 :recursivep kwd-alist))
       (ihints `(:hints ;; add induction hint, so user-provided
                 ;; hints are treated as extra
                 ,(append `(("Goal" :induct ,(cons name formals)))
                          hints)))
       (rhints (if recursivep
                   ihints
                 (and hints `(:hints ,hints))))
       (rewrite-class (if no-hyps?
                          '(:rewrite) ;; error if no hyps
                        '(:rewrite :backchain-limit-lst 3)))
       (rclass
        `(,rewrite-class
          (:forward-chaining :trigger-terms ((,name ,@formals)))))
       (rclass (or rule-classes rclass)) ; rule-classes overrides rclass
       (rewrite-fc ;; in case user wanted to completely override hints
        (if hints
            `(DEFTHM ,contract-name ,body
               ,@(and hints `(:hints ,hints))
               ,@(and rclass `(:rule-classes ,rclass))
               ,@(and otf-flg `(:otf-flg ,otf-flg))
               ,@(and instructions `(:instructions ,instructions)))
          '(acl2::fail-event :defunc t :fail-contract "No user-provided hints")))
       (induct-rewrite-fc
        `(DEFTHM ,contract-name ,body ,@rhints
           ,@(and rclass `(:rule-classes ,rclass))
           ,@(and otf-flg `(:otf-flg ,otf-flg))
           ,@(and instructions `(:instructions ,instructions))))
       (tp-rule
        `(DEFTHM ,contract-tpname ,body
           :rule-classes ((:type-prescription))
           :hints (("goal" :by ,contract-name)))))
    (if (or make-staticp function-contract-strictp)
        `(encapsulate
          ()
          (make-event '(:or ,induct-rewrite-fc ,rewrite-fc))
          (make-event '(:or ,tp-rule (value-triple :type-prescription-rule-failed))))
      `(encapsulate
        ()
        (make-event '(:OR ,induct-rewrite-fc
                          (value-triple :contract-failed)))
        (make-event '(:OR ,tp-rule
                          (value-triple :Type-prescription-rule-failed)))))))

(defun make-verify-guards-ev (name kwd-alist)
  (b* ((hints (defdata::get1 :body-contracts-hints kwd-alist)) ; (defdata::get1 :guard-hints xargs{})
       (body-contracts-strictp (defdata::get1 :body-contracts-strictp kwd-alist))
       (hints (or hints '(("Goal" :do-not-induct t :do-not '(acl2::generalize acl2::fertilize)))))
       )

    (if body-contracts-strictp
        `(verify-guards ,name :guard-debug t :hints ,hints)
      `(make-event
        '(:OR (verify-guards ,name :guard-debug t :hints ,hints)
              (value-triple :body-contracts-FAILED))))))


; Sometimes counterexample generation winds up trying to evaluate
; a defunc-defined function outside of it's domain. That should
; not happen, but things like generalization can lead to such
; behavior. It useful for debugging to print an error when this
; happens. By default, I turn it off (nil), but it should be on
; (t) when testing defunc.
(defconst *print-contract-violations* nil) ;IMP NOTE-- turn this ON when debugging.

(encapsulate
  ((acl2s-undefined (x y) t :guard (and (symbolp x) (true-listp y))))
  (local (defun acl2s-undefined (x y) (declare (ignorable x y)) nil)))

(defconst *defunc-keywords*
  '(:input-contract :output-contract :sig ;:sig unsupported now
    :verbose :debug
    :rule-classes :instructions :function-contract-hints :otf-flg ;for contract defthm
    :body-contracts-hints ;for verify-guards event
    :skip-tests
    :timeout :termination-strictp :function-contract-strictp :body-contracts-strictp
    ))

(defdata::deffilter filter-keywords (xs) keywordp)

(defun acl2s-undefined-attached (name args)
  (declare (xargs :guard (and (symbolp name)
                              (true-listp args))))
  (cw "~|**Input contract violation**: ~x0 ~%" `(,name ,@args)))

(defun acl2s-undefined-attached-base (name args)
  (declare (xargs :guard (and (symbolp name)
                              (true-listp args))))
  (declare (ignorable name args))
  nil)

; If you want to see contract violations printed in an ACL2s
; session, you can do that with the following event:
; (defattach acl2s-undefined acl2s-undefined-attached-base)

(make-event
 (if *print-contract-violations*
     '(defattach acl2s-undefined acl2s-undefined-attached)
   '(defattach acl2s-undefined acl2s-undefined-attached-base))
 :check-expansion t)

#!ACL2
(defun modify-xargs-decl (key val decl)
  (b* ((kwd-val-list (cdr (cadr decl)))
       (kwd-val-list (remove-keyword key kwd-val-list)))
    (list 'DECLARE (cons 'XARGS (list* key val kwd-val-list)))))


#!ACL2
(defun update-xargs-decls-fn (decls guard mode)
  "add guard and mode to decls, or create a decl if decls is empty."
  (b* ((xargs-decl (car (last decls)))) ;PRECONDITION: we know that the xargs declare is at the end
    (cond (mode (append (butlast decls 1)
                        (list (modify-xargs-decl :mode mode
                                                 (modify-xargs-decl :guard guard xargs-decl)))))

          (t (append (butlast decls 1)
                     (list (modify-xargs-decl :guard guard xargs-decl)))))))




(defmacro update-xargs-decls (decls &key guard mode)
  `(acl2::update-xargs-decls-fn ,decls ,guard ,mode))
;Note : Macro confusion, if I put ',decls or ',ic, it doesnt
;work. Macros are not that nice, one needs to know the context in
;which they are called, if I call from program context where decls,
;guard are variable names, you should not use quotes, but if you use
;them in a context where decls, guard are actual values, then you need
;to quote them.

(defun print-summary-ev (name oc kwd-alist)
  `(with-output :stack :push :off :all
     (make-event
      (b* ((symbol-class (acl2::symbol-class ',name (w state)))
           (contract-name (make-sym ',name 'contract))
           (function-contract-proven-p
            (or (c-is-t ',oc) (acl2::logical-namep contract-name (w state))))
           (print (defdata::get1 :print-summary ',kwd-alist))
           ((mv end state) (acl2::read-run-time state))
           ((er &) (if print (print-time-taken ,(defdata::get1 :start-time kwd-alist) end state) (value nil)))
           )
          (value
           `(with-output :stack :pop
              (value-triple
               (defdata::cw? ,print
                 "~%~|Function Name : ~s0 ~|Termination proven -------- [~s1] ~|Function Contract proven -- [~s2] ~|Body Contracts proven ----- [~s3]~%"
                 ',',name
                 (print-*-or-space (not (eq :PROGRAM ,symbol-class)))
                 (print-*-or-space ,function-contract-proven-p)
                 (print-*-or-space (eq :COMMON-LISP-COMPLIANT ,symbol-class))))))))))

(defun print-*-or-space (b)
  (if b "*" " "))

(defun make-defun-no-guard-ev (name formals ic oc decls body wrld make-staticp)
  (declare (xargs :mode :program))
  (b* ((lbody (make-defun-body/logic name formals ic oc body wrld make-staticp))
       (ebody (make-defun-body/exec name formals oc body wrld make-staticp))
       (decls (update-xargs-decls decls :guard ic)))
    (list* 'ACL2::DEFUN name formals (append decls (list (list 'ACL2::MBE :logic lbody :exec ebody))))))


(defun timeout-abort-fn (start-time timeout-secs debug state)
  (declare (xargs :mode :program :stobjs (state)))
  (b* (((mv end state) (acl2::read-run-time state))
       (time-elapsed (- end start-time))
       (- (defdata::cw? debug  "~| Elapsed Time is ~x0 and timeout-secs is ~x1 ~%" time-elapsed timeout-secs))
       (- (defdata::cw? (> time-elapsed timeout-secs) "~|Defunc timeout exceeded!!~%")))
    (if (> time-elapsed timeout-secs)
        (mv t nil state)
      (value '(value-triple :invisible)))))


(defmacro abort-this-event-sequence (start-time timeout-secs debug)
  "If timedout or reason was termiantion -- just raise error"
  `(with-output :off :all
     (make-event (er-progn
                  (if (and (acl2::boundp-global 'defunc-failure-reason state)
                           (eq (@ defunc-failure-reason) :termination))
                      (mv t nil state)
                    (value nil))
                  (assign defunc-failure-reason :timed-out)
                  (timeout-abort-fn ,start-time ,timeout-secs ,debug state)))))

(defun defunc-events-with-staticp-flag
    (name formals ic oc decls body kwd-alist wrld make-staticp)
  "Depending on flag make-staticp, we generate either events with static contract or with dynamic contract (run-time checking)."
  (declare (xargs :mode :program))
  (if (defdata::get1 :program-mode-p kwd-alist)
      '(mv t nil state) ;skip/abort
    (b* ((defun/ng
           (make-defun-no-guard-ev
            name formals ic oc decls body wrld make-staticp))
         (contract-defthm
          (make-contract-ev name formals ic oc kwd-alist make-staticp wrld))
         (verify-guards-ev (make-verify-guards-ev name kwd-alist))
         (timeout-secs (defdata::get1 :timeout kwd-alist))
         (test-subgoals-p (eq t (defdata::get1 :testing-enabled kwd-alist))))
      `(with-prover-time-limit
        ,timeout-secs
        (encapsulate
         nil
         (abort-this-event-sequence
          ,(defdata::get1 :start-time kwd-alist)
          ,timeout-secs
          ,(defdata::get1 :debug kwd-alist))
         ,@(and test-subgoals-p '((local (acl2s-defaults :set testing-enabled nil))))
         (local (acl2s-defaults :set print-cgen-summary nil))
         (with-output
          :off :all
          (make-event (er-progn
                       (assign defunc-failure-reason :termination)
                       (value '(value-triple :invisible)))))
         ;;(with-prover-time-limit ,timeout-secs ,defun/ng)
         (with-output :on (summary) :summary (acl2::form acl2::time)
                      (with-prover-time-limit ,(* 4/5 timeout-secs) ,defun/ng))

         (with-output
          :off :all
          (make-event (er-progn (assign defunc-failure-reason :contract)
                                (value '(value-triple :invisible)))))
         ,@(and test-subgoals-p
                '((local (acl2s-defaults :set testing-enabled t))))
         ;;helps defeat generalizations
         ,@(and contract-defthm ;(list contract-defthm))
                `((with-output
                   :on (summary) :summary (acl2::form acl2::time)
                   (with-prover-time-limit ,(* 1/3 timeout-secs) ,contract-defthm))))
         ,@(and test-subgoals-p '((local (acl2s-defaults :set testing-enabled nil))))

         (with-output
          :off :all
          (make-event (er-progn (assign defunc-failure-reason :guards)
                                (value '(value-triple :invisible)))))
         (with-output
          :on (summary) :summary (acl2::form acl2::time)
          (with-prover-time-limit ,(* 1/3 timeout-secs) ,verify-guards-ev))
         
         (with-output
          :off :all
          (make-event (er-progn (assign defunc-failure-reason
                                        :generic-ev)
                                (value '(value-triple :invisible)))))
         ,@(make-generic-typed-defunc-events
            name formals ic oc decls body kwd-alist wrld make-staticp)

         (with-output
          :off :all
          (make-event (er-progn (assign defunc-failure-reason :none)
                                (value '(value-triple :invisible)))))

         ,(print-summary-ev name oc kwd-alist))))))


(defun program-mode-defunc-events (name formals ic oc decls body kwd-alist wrld)
  (declare (xargs :mode :program))
  (b* ((dynamic-body (make-defun-body/logic name formals ic oc body wrld nil))
       (decls (update-xargs-decls decls :guard ic :mode :program))

       )

    `(with-output
       :on (summary) :summary (acl2::form)
       (PROGN
        (defun ,name ,formals
          ,@decls
          ,dynamic-body)
        ,(print-summary-ev name oc kwd-alist)))))



(defun print-guard-extra-info-hyps (hyps yesp)
  (if (endp hyps)
      nil
    (if (and (consp (car hyps))
             (eq (car (car hyps)) 'ACL2::EXTRA-INFO))
        (prog2$
         (cgen::cw? yesp "~| -- ~x0~%" (car hyps))
         (print-guard-extra-info-hyps (cdr hyps) yesp))
      (print-guard-extra-info-hyps (cdr hyps) yesp))))

;; ((acl2::fun (check-syntax form logicp state)) ;flet
;;          (acl2::state-global-let*
;;           ((acl2::inhibit-output-lst acl2::*valid-output-names*))
;;           (acl2::translate form T logicp T "test-guards" (w state) state)))

(defun test-guards1 (guards hints override-defaults state)
  (declare (xargs :mode :program :stobjs (state)))
  (if (endp guards)
      (value nil)
    (b* (((mv erp & state) (test?-fn (car guards) hints override-defaults state))
         (vl  (acl2s-defaults :get verbosity-level))
         (show-falsified-guards-p (and erp (cgen::normal-output-flag vl)))
         (- (cgen::cw? show-falsified-guards-p "~|Body contract falsified in: ~%"))

; [2015-02-04 Wed] Add extra support to blame the falsified body contract by looking through lambda/let/assumptions/etc


         ((mv & gterm state) (cgen::check-syntax (car guards) NIL state))
         ((mv hyps concl state) (cgen::partition-hyps-concl gterm "test-guards" state))
         ((mv & nconcl state) (cgen::simplify-term (list 'not concl) hyps nil state))
         (hyps1 (acl2::expand-assumptions-1 nconcl))

         (- (print-guard-extra-info-hyps (append hyps hyps1) show-falsified-guards-p))
         ((when erp) (mv t nil state)))
      (test-guards1 (cdr guards) hints override-defaults state))))


(defun test-guards (guard-obligation hints override-defaults state)
  "This is just a looping test?-fn over multiple guards, and on error, printing out the appropriate guard-info."
  (declare (xargs :mode :program :stobjs (state)))
  (b* ((guards (if (and (consp guard-obligation)
                        (eq 'ACL2::AND (car guard-obligation)))
                   (cdr guard-obligation)
                 (list guard-obligation))))
    (test-guards1 guards hints override-defaults state)))

;; If ld-error-action is :error, ld stops and returns, signalling an
;; error to its caller by returning an error triple with non-nil error
;; component, and reverting the logical world to its value just before
;; that call of ld.

(defun print-time-taken (start end state)
  (declare (xargs :mode :program :stobjs (state)))
  (b* ((- (cw "~|Elapsed Run Time: ")))
    (pprogn (acl2::print-rational-as-decimal (rfix (- end start)) (standard-co state) state)
            (princ$ " seconds" (standard-co state) state)
            (newline (standard-co state) state)
            (value :invisible))))


(defun test?-phase (parsed state)
  (declare (xargs :mode :program :stobjs (state)))
  (b* (((list name formals ic oc decls body kwd-alist) parsed)
       (skip-tests-p (or (defdata::get1 :skip-tests kwd-alist)
                         (eq nil (defdata::get1 :testing-enabled kwd-alist))))
       (testing-timeout (defdata::get1 :cgen-timeout kwd-alist))
       ((when skip-tests-p) (value nil))
       (mode (if (defdata::get1 :program-mode-p kwd-alist) :program :logic))
       (defun (list* 'ACL2::DEFUN name formals
                     (append (update-xargs-decls decls :guard ic :mode mode)
                             (list body))))
       (debug (defdata::get1 :debug kwd-alist))
       (- (defdata::cw? debug "~| defun : ~x0 ~| ic : ~x1 ~| oc: ~x2~%" defun ic oc))
       (hints (defdata::get1 :body-contracts-hints kwd-alist))
       ((mv start state) (acl2::read-run-time state))
       ((er trval)
        (acl2::trans-eval
         `(make-event
           (er-progn
            (with-output :on (error) (skip-proofs ,defun))
            (b* (((er guard-ob) (acl2::function-guard-obligation ',name state))
                 (- (defdata::cw? ,debug "~| guard-obligation: ~x0~%" guard-ob))
                 (- (cw "~|Query: Testing body contracts ... ~%"))
                 ((er &) (with-output :on (error)
                                      (with-prover-time-limit
                                       ,testing-timeout
                                       (test-guards guard-ob ',hints '(:print-cgen-summary nil :num-witnesses 0) state))))
                 )
              (value '(value-triple :invisible))))) 'test?-phase state t))
       ((when (eq T (cadr trval))) (mv t nil state)) ;abort with error
       (- (cw "~|Query: Testing function contract ... ~%"))
       ((er trval)
        (acl2::trans-eval
         `(make-event
           (er-progn
            (with-output :on (error) (skip-proofs ,defun))
            (with-output :on (error) (test? (implies ,ic ,oc) :print-cgen-summary nil :num-witnesses 0))
            (value '(value-triple :invisible))))
         'test?-phase state t))
       ((when (eq T (cadr trval))) (mv t nil state)) ;abort with error
       ((mv end state) (acl2::read-run-time state))
       ((er &) (print-time-taken start end state))
       )
    (value nil)))

;       (- (cw "~| ld erp: ~x0 defun-name logical-namep result: ~x1 ld-err-triple: ~x2~%" erp (logical-namep name (w state)) (ld-error-triples state))))
;; ;; THis is stupid. ACL2 should have a error-propagating mechanism where errors have names!!
;;     (if (eq :passed (@ _test?-phase__ld-result))
;;         (mv t :passed state)
;;       (mv t nil state))))

(defun make-show-failure-msg-ev (start-time kwd-alist events-seen)
  `(make-event
    (b* ((body-contracts-strictp (defdata::get1 :body-contracts-strictp ',kwd-alist))
         (function-contract-strictp (defdata::get1 :function-contract-strictp ',kwd-alist))
         (termination-strictp (defdata::get1 :termination-strictp ',kwd-alist))
         (timeout-secs (defdata::get1 :timeout ',kwd-alist))
         ((mv end state) (acl2::read-run-time state))
         ((er &) (print-time-taken ,start-time end state))
         (time-elapsed (- end ,start-time))
         (failure-reason (@ defunc-failure-reason))
         (blame-msg
          (or (and (or (> time-elapsed timeout-secs) (eq :timed-out failure-reason))
                   "Defunc has TIMED OUT!! You can change the timeout default using :timeout option (also see :doc set-defunc-timeout). If you want to bypass this failure, you can modify defunc's default strictness (see :doc defunc).")
              (and termination-strictp (eq :termination failure-reason)
                   "Termination FAILED!")
              (and function-contract-strictp (eq :contract failure-reason)
                   "Function Contract FAILED! You can provide :function-contract-hints to help.")
              (and body-contracts-strictp (eq :guards failure-reason)
                   "Body Contracts FAILED! You can provide :body-contracts-hints to help.")
              "Something that we could not assign blame to has FAILED! The failure might be due to the definition rule or the induction scheme associated with this function definition. Chances are that there is a problem with your definition. To debug this further, please consult an expert."))
         )

      (if (> time-elapsed timeout-secs)
          (value
           `(with-output
              :stack :pop
              (value-triple (er hard? 'defunc "~%~s0~%" ,blame-msg))))
        (value
         `(with-output
            :stack :pop
            (value-triple
             (progn$
              (fmt-to-comment-window "~%~%FAILED EVENTS: ~x0" (list (cons #\0 (list* 'ACL2::PROGN ',',events-seen))) 0 nil nil)
              (cw "~%~s0" ,blame-msg)
              (er hard? 'defunc "~|Submit the events shown above to replicate the failure.")))))))))


(defun events-seen-list (parsed wrld make-staticp)
  (declare (xargs :mode :program))
  (b* (((list name formals ic oc decls body kwd-alist) parsed)
       (defun/ng (make-defun-no-guard-ev name formals ic oc decls body wrld make-staticp))
       (contract-defthm (make-contract-defthm name ic oc kwd-alist formals wrld))
       (verify-guards-ev (make-verify-guards-ev name kwd-alist))
       (function-contract-strictp (defdata::get1 :function-contract-strictp kwd-alist))
       (body-contracts-strictp (defdata::get1 :body-contracts-strictp kwd-alist)))
    (append (list defun/ng)
            (and function-contract-strictp contract-defthm (list contract-defthm))
            (and body-contracts-strictp (list verify-guards-ev)))))

(defun defunc-events (parsed state)
  (declare (xargs :mode :program :stobjs (state)))
  (b* (((list name formals ic oc decls body kwd-alist) parsed)
       (wrld (w state))
       ;;some initialization
       ((mv start state) (acl2::read-run-time state))
       (kwd-alist (put-assoc :start-time start kwd-alist))
       ((er &) (assign defunc-failure-reason :none))
       (static-defunc-ev
        (defunc-events-with-staticp-flag
          name formals ic oc decls body kwd-alist wrld t))
       (dynamic-defunc-ev
        (defunc-events-with-staticp-flag
          name formals ic oc decls body kwd-alist wrld nil))
       (program-mode-defunc-ev
        (program-mode-defunc-events
         name formals ic oc decls body kwd-alist wrld))
       (termination-strictp
        (and (defdata::get1 :termination-strictp kwd-alist)
             (not (defdata::get1 :program-mode-p kwd-alist))))
       ;;program-mode overrides termination-strictp
       (function-contract-strictp
        (defdata::get1 :function-contract-strictp kwd-alist)))
    (value
     (cond
      ((and termination-strictp function-contract-strictp)
       `(:OR ,static-defunc-ev
             ,(make-show-failure-msg-ev start kwd-alist
                                        (events-seen-list parsed wrld t))))
      (termination-strictp
       `(:OR ,static-defunc-ev
             ,dynamic-defunc-ev
             ,(make-show-failure-msg-ev start kwd-alist
                                        (events-seen-list parsed wrld nil))))
      (t `(:OR ,static-defunc-ev
               ,dynamic-defunc-ev
               ,program-mode-defunc-ev
               ,(make-show-failure-msg-ev
                 start kwd-alist
                 (list (make-defun-no-guard-ev
                        name formals ic oc decls body wrld t)))))))))

(defun union-keyword-value-lists (kwd-val-lst1 kwd-val-lst2)
  (if (endp kwd-val-lst1)
      kwd-val-lst2
    (b* ((key (car kwd-val-lst1))
         (value (cadr kwd-val-lst1))
         (rest (cddr kwd-val-lst1)))
      (union-keyword-value-lists
       rest
       (list* key value (acl2::remove-keyword key kwd-val-lst2))))))

#!ACL2
(defun collect-xargs-into-single-declare (xargs-decls ans-kwd-val-lst)
  (if (endp xargs-decls)
      (list 'DECLARE (cons 'XARGS (list* :VERIFY-GUARDS NIL
                                         :NORMALIZE NIL ;o.w definition-rule fails in e.g defunc len
                                         (remove-keyword :normalize
                                                         (remove-keyword :verify-guards ans-kwd-val-lst)))))
    (b* ((curr-kwd-val-lst (cdr (cadr (car xargs-decls)))))

      (collect-xargs-into-single-declare (cdr xargs-decls) (acl2s::union-keyword-value-lists curr-kwd-val-lst ans-kwd-val-lst)))))

(defdata::deffilter filter-xargs-decls (decls)
  (lambda (x) (and (= 2 (len x))
                   (consp (cadr x))
                   (eq 'ACL2::XARGS (car (cadr x))))))


(defun squeeze-multiple-xarg-decls (decls)
  "collect all xargs decls, squeeze them into one decl and put that at the end."
  (b* ((xargs-decls (filter-xargs-decls decls))
       (xargs-decl (acl2::collect-xargs-into-single-declare xargs-decls '())))
    (append (set-difference-equal decls xargs-decls) (list xargs-decl))))




(defdata::deffilter filter-strings (xs) stringp)

;; (defmacro termination-strictp () `(cdr (assoc-eq :termination-strictp (table-alist 'defunc-defaults-table wrld))))
;; (defmacro function-contract-strictp () `(cdr (assoc-eq :function-contract-strictp (table-alist 'defunc-defaults-table wrld))))
;; (defmacro body-contracts-strictp () `(cdr (assoc-eq :body-contracts-strictp (table-alist 'defunc-defaults-table wrld))))



(table defunc-defaults-table nil
       '((:debug       .  nil)
         (:verbose     . nil)
         (:print-summary  . t)
         (:skip-tests . nil)
         (:timeout . 50)
         (:termination-strictp . t)
         (:function-contract-strictp . t)
         (:body-contracts-strictp . t)
         )
       :clear)

(verify-termination defdata::remove1-assoc-eq-lst)

(defloop thereis-programp (fns wrld)
  (for ((fn in fns)) (thereis (acl2::programp fn wrld))))

(defun program-mode-p (name formals body decls wrld)
  "Check if :mode :program is declared, or check if current mode is (program), or if body has a program-mode function call"
  (declare (xargs :mode :program))
  (b* ((xargs{} (xargs-kwd-alist decls 'program-mode-p))
       (pm? (eq (defdata::get1 :mode xargs{}) :program))
       ((mv ?erp tbody) (acl2::pseudo-translate body (list (cons name formals)) wrld))
       (sub-fns (set-difference-eq (cgen::all-functions tbody) (list name))))
    (or pm?
        (eq (cdr (assoc-eq :defun-mode (table-alist 'acl2::acl2-defaults-table wrld)))
            :program)
        (thereis-programp sub-fns wrld))))

(defun parse-defunc (name args wrld)
  ;; Returns (list nm formals ic oc doc decls body kwd-alist)
  (declare (xargs :mode :program))
  (declare (ignorable wrld))
  (b* ((ctx 'defunc)
       ((unless (or (proper-symbolp name)
                    (and (symbolp name) (equal "*" (symbol-name name))))) ;exception
        (er hard? ctx "~| Function name ~x0 expected to be a proper symbol.~%" name))

       (defaults-alst (table-alist 'defunc-defaults-table wrld))
       (defaults-alst (defdata::remove1-assoc-eq-lst (filter-keywords args) defaults-alst))
       (defaults-alst (put-assoc :testing-enabled (get-acl2s-defaults 'testing-enabled wrld) defaults-alst))
       (defaults-alst (put-assoc :cgen-timeout (get-acl2s-defaults 'cgen-timeout wrld) defaults-alst))
       ((mv kwd-alist defun-rest) (defdata::extract-keywords ctx *defunc-keywords* args defaults-alst))

       (formals (car defun-rest))
       (decls/docs (butlast (cdr defun-rest) 1))
       (body  (car (last defun-rest)))
       (full-input-contract (assoc-equal :input-contract kwd-alist))
       (full-output-contract (assoc-equal :output-contract kwd-alist))
       ((unless full-input-contract)
        (er hard ctx "~|Defunc is missing an input contract. ~%" ))
       ((unless full-output-contract)
        (er hard ctx "~|Defunc is missing an output contract. ~%" ))

       (input-contract (defdata::get1 :input-contract kwd-alist ))
       (output-contract (defdata::get1 :output-contract kwd-alist ))
       ((unless (simple-termp input-contract))
        (er hard ctx "~|The input contract has to be a term. ~x0 is not.~%" input-contract))
       ((unless (simple-termp output-contract))
        (er hard ctx "~|The output contract has to be a term. ~x0 is not.~%" output-contract))
;       (signature (defdata::get1 :sig kwd-alist))

       (recp (in-termp name body))
       (kwd-alist (put-assoc :recursivep recp kwd-alist))

       (docs (filter-strings decls/docs))
       ((when (consp (cdr docs)))
        (er hard ctx "~|Multiple doc strings unexpected!~%" docs))
       (doc-strings (and (consp docs) (list (car docs))))
       (decls (set-difference-equal decls/docs docs))
       (decls (squeeze-multiple-xarg-decls decls))
       (decls (append doc-strings decls)) ;put doc-string at the front of decls

       (program-mode-p (program-mode-p name formals body decls wrld))
       (kwd-alist (put-assoc :program-mode-p program-mode-p kwd-alist))
       )

    (list name formals input-contract output-contract decls body kwd-alist)))

(defun make-undefined (name args w)
  (declare (xargs :mode :program :guard (symbolp name)))
  (b* ((parsed (parse-defunc name args w))
       ((list name formals & oc & & kwd-alist) parsed)
       (pred (pred-of-oc name formals oc))
       (tbl (table-alist 'defdata::type-metadata-table w))
       (type (type-of-pred pred tbl))
       (undef-name (if type
                       (make-symbl `(acl2s::acl2s - ,type -undefined))
                     'acl2s::acl2s-undefined))
       (attch-name (make-symbl `(,undef-name -attached)))
       (attch-base-name (make-symbl `(,attch-name -base)))
       (thm-name (make-symbl `(,undef-name - ,pred)))
       (base-val (and type (base-val-of-type type tbl))))
    (cond
     ((defdata::get1 :program-mode-p kwd-alist)
      `(value-triple :program-mode))
     ((acl2::arity undef-name w)
      `(value-triple ',undef-name))
     (t `(encapsulate
          nil
          (encapsulate
           ((,undef-name (x y) t :guard (and (symbolp x) (true-listp y))))
           (local (defun ,undef-name (x y)
                    (declare (ignorable x y))
                    ',base-val))
           (defthm ,thm-name (,pred (,undef-name x y))
             :rule-classes ((:type-prescription) (:rewrite))))
          (defun ,attch-name (x y)
            (declare (xargs :guard (and (symbolp x) (true-listp y))))
            (cw "~|**Input contract violation**: ~x0 ~%" `(,x ,@y)))
          (defun ,attch-base-name (x y)
            (declare (xargs :guard (and (symbolp x) (true-listp y))))
            (declare (ignorable x y))
            ',base-val)
          ,(if *print-contract-violations*
               `(defattach ,undef-name ,attch-name)
             `(defattach ,undef-name ,attch-base-name)))))))

; (make-event (make-undefined 'foo '((x) :input-contract (natp x) :output-contract (booleanp (foo x)) nil)  (w state)))
; (make-event (make-undefined 'booleanp (w state)))
; (make-event (make-undefined 'boole (w state)))

(defmacro defunc (name &rest args)
  (b* ((verbosep (let ((lst (member :verbose args)))
                   (and lst (cadr lst))))
       (verbosep (or verbosep
                     (let ((lst (member :debug args)))
                       (and lst (cadr lst))))))
    `(encapsulate
      nil
      (make-event (make-undefined ',name ',args (w state)))
      (with-output
       ,@(and (not verbosep) '(:off :all))
       :gag-mode ,(not verbosep)
       :stack :push
       ;; Generate undef
       (make-event
        (er-progn
         ;; Test phase using trans-eval/make-event
         (test?-phase (parse-defunc ',name ',args (w state)) state)
         ;; Generate events
         (defunc-events (parse-defunc ',name ',args (w state)) state)))))))

(include-book "xdoc/top" :dir :system)

(defxdoc defunc
  :parents (acl2::acl2-sedan acl2::macro-libraries)
  :short "Function definitions with contracts @(see acl2::defun)"
  :long
  "
<h3>Examples</h3>

@({

  (defunc len (a)
    :input-contract t
    :output-contract (natp (len a))
    (if (atom a)
        0
      (+ 1 (len (rest a)))))

  (defunc app (x y)
    :input-contract (and (true-listp x) (true-listp y))
    :output-contract (and (true-listp (app x y))
                          (equal (len (app x y)) (+ (len x) (len y))))
    (if (endp x)
        y
      (cons (car x) (app (cdr x) y))))

  (defunc add-digits (x)
    :input-contract (natp x)
    :output-contract (natp (add-digits x))
    :function-contract-hints ((\"Goal\" :do-not '(acl2::generalize)))
    (if (< x 10)
        x
      (let* ((rem (rem x 10))
             (y   (/ (- x rem) 10)))
        (+ rem (add-digits y)))))

  (defunc square-list (l)
    :input-contract (nat-listp l)
    :output-contract (nat-listp (square-list l))
    (if (endp l)
        nil
      (app (list (* (car l) (car l)))
           (square-list (cdr l))))
    :verbose t
    :skip-tests t)

})

<h3>Purpose</h3>
<p>
The macro @('defunc') is an extension of @('acl2::defun') with <b>contracts</b>.
</p>

<p> Using @('defunc') one can specify input and output
contracts (pre and post conditions) for a function. The following
actions are performed when @('defunc') is used in the default
way. If any of the actions fail, then an informative error
message is printed. If all actions succeed, then the function has
been successfully admitted to ACL2s.  </p>

<ol>

<li> Test the function contract, i.e., whether the output
contract holds under the assumption that the function terminates
and the input contract holds.</li>

<li> Test the body contracts, i.e., whether the contracts of the
functions appearing in the body of the @('defunc') are violated.
</li>

<li>Construct a definition in the core ACL2 logic that respects
the input contracts, and prove that this definition is
terminating.</li>

<li> Prove the function contract, i.e., that the input
contract implies the output contract.</li>

<li> Prove the body contracts, i.e., that for each occurrence of
a function call inside the body of the function being defined,
all of the arguments to the function call satisfy the input
contracts of the function. In ACL2 parlance, this is guard
verification.</li>

<li> Replace the function definition and induction scheme with a
definition rule and an induction scheme for the function that
restricts definition expansion and inductions to contexts where
the input contract is satisfied. If @('defunc') is used in a
disciplined way, then all contexts should satisfy this
restriction.  Use @(':pcb fun-name') to check the names of the
above events.  </li>
</ol>


<h3>Syntax</h3>
<p>
The general form of @('defunc') is:
</p>

@({
 (defunc name (x1 x2 ...)
   [doc-string declare-form*]
   [:input-contract ic]
   [:output-contract oc]
   [:function-contract-hints hints :rule-classes ...] ;function contract hints
   [:body-contracts-hints hints]                      ;body contracts hints
   [Other :key value ...]
   body)
})

<p>
The form of @('defunc') is just like @(see acl2::defun) except that is allows
extra keyword options.  Note that the keyword options can go anywhere
between the formals (parameters) and the end of @('defunc') macro.
The supported keyword options with the syntax restrictions and actions are noted
below.
</p>

<h4>Keyword Options</h4>

<dl>
<dt>@(':input-contract ic')</dt>
  <dd>Required; @('ic') is a <see topic='@(url acl2::term)'>term</see>.</dd>
<dt>@(':output-contract oc')</dt>
  <dd>Required; @('oc') is a <see topic='@(url acl2::term)'>term</see>.</dd>
<dt>@(':function-contract-hints hints')</dt>
  <dd>Passed as <tt>:<see topic='@(url acl2::hints)'>hints</see></tt> to the
      function contract @(see defthm).</dd>
<dt>@(':rule-classes rcs')<br/>
    @(':instructions is')<br/>
    @(':otf-flg flg')</dt>
  <dd>These three keyword arguments are passed directly to the function
      contract @(see defthm).</dd>
<dt>@(':body-contracts-hints hints')</dt>
  <dd>Passed as <tt>:<see topic='@(url acl2::hints)'>hints</see></tt> to the
      body contracts @(see defthm).</dd>
</dl>

<p>The following keyword options are usually set at the
session-wide-level (see the <tt>set-defunc-*</tt> macros documented
below); when given as keyword arguments to @('defunc') they override
the session defaults.</p>

<dl>
<dt>@(':termination-strictp x')</dt>
  <dd>When @('x') is @('t') (default), abort if termination failed.</dd>
  <dd>When @('x') is @('nil'), then if termination fails, admit the function in
      :program mode.</dd>
<dt>@(':function-contract-strictp x')</dt>
  <dd>When @('x') is @('t') (default), abort if the contract proof failed.</dd>
  <dd>When @('x') is @('nil'), then if the proof fails, add a dynamic contract
      check.</dd>
<dt>@(':body-contracts-strictp x')</dt>
  <dd>When @('x') is @('t') (default), abort if the body contracts proof
      failed.</dd>
  <dd>When @('x') is @('nil'), body contracts are checked dynamically.</dd>
<dt>@(':timeout n')</dt>
  <dd>Limit the time spent in defunc events to @('n') seconds.</dd>
<dt>@(':skip-tests t')</dt>
  <dd>Skip the testing actions.</dd>
</dl>


<h3>Debugging</h3>
<p>
To debug a failed defunc form, you can proceed in multiple ways:
<ul>
<li> Submit the events shown above the failure message to replicate the error.</li>
<li> At the session editor (or emacs prompt), submit/evaluate
     @(':trans1 (defunc ...)')
     And from the output, evaluate the form that says <tt>(defunc-events ...)</tt>.</li>
<li>Use keyword options <tt>:verbose t</tt> (or <tt>:debug t</tt>) and examine the ACL2 output.</li>
</ul>
</p>
"
  )

(defmacro set-defunc-termination-strictp (b) `(table defunc-defaults-table :termination-strictp ,b :put))
(defmacro set-defunc-function-contract-strictp (b) `(table defunc-defaults-table :function-contract-strictp ,b :put))
(defmacro set-defunc-body-contracts-strictp (b) `(table defunc-defaults-table :body-contracts-strictp ,b :put))
(defmacro set-defunc-timeout (r) `(table defunc-defaults-table :timeout ,r :put))

(defmacro get-defunc-timeout () `(table defunc-defaults-table :timeout))
(defmacro get-defunc-termination-strictp () `(table defunc-defaults-table :termination-strictp))
(defmacro get-defunc-function-contract-strictp () `(table defunc-defaults-table :function-contract-strictp))
(defmacro get-defunc-body-contracts-strictp () `(table defunc-defaults-table :body-contracts-strictp))

(defxdoc set-defunc-timeout
  :parents (defunc)
  :short "Set timeout (in seconds) for defunc"
  :long
  "<p>Set timeout for the events generated by @('defunc').
  The default timeout limit is set to 50 seconds.</p>

  <p>Guard : Timeout value should be a rational.</p>
   ")

(defxdoc get-defunc-timeout
  :parents (defunc)
  :short "Get timeout default for defunc")

(defxdoc get-defunc-termination-strictp
  :parents (defunc)
  :short "Get termination-strictp default for defunc")

(defxdoc get-defunc-function-contract-strictp
  :parents (defunc)
  :short "Get function-contract-strictp default for defunc")

(defxdoc get-defunc-body-contracts-strictp
  :parents (defunc)
  :short "Get body-contracts-strictp default for defunc")


(defxdoc set-defunc-termination-strictp
  :parents (defunc)
  :short "Set termination-strictp for defunc"
  :long
  "<p>Set whether termination is strict for @('defunc'), i.e. whether
   @('defunc') should abort or continue on failure to prove termination.</p>
   <p>The default is set to @('t').</p>
   ")

(defxdoc set-defunc-function-contract-strictp
  :parents (defunc)
  :short "Set function-contract-strictp for defunc"
  :long
  "<p>Set whether @('defunc') should abort or continue on failure to prove function contract.</p>
   <p>The default is set to @('t').</p>
   ")

(defxdoc set-defunc-body-contracts-strictp
  :parents (defunc)
  :short "Set body-contracts-strictp for defunc"
  :long
  "<p>Set whether @('defunc') should abort or continue on failure to verify body contracts.</p>
   <p>The default is set to @('t').</p>
   ")

(defmacro defuncd (name &rest args)
  (let* ((defname (make-symbl `(,name -DEFINITION-RULE))))
    `(progn
      (defunc ,name ,@args)
      (in-theory (disable ,defname)))))

(defmacro set-defunc-skip-tests (r)
  `(table defunc-defaults-table :skip-tests ,r :put))

(defmacro defunc-no-test (name &rest args)
  `(acl2::with-outer-locals
    (local (acl2s-defaults :set testing-enabled nil))
    (defunc ,name ,@args)))

(defmacro defuncd-no-test (name &rest args)
  `(acl2::with-outer-locals
    (local (acl2s-defaults :set testing-enabled nil))
    (defuncd ,name ,@args)))

