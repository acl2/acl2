; SOFT (Second-Order Functions and Theorems) Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "SOFT")

(include-book "core")

(include-book "kestrel/event-macros/cw-event" :dir :system)
(include-book "kestrel/event-macros/make-event-terse" :dir :system)
(include-book "kestrel/event-macros/restore-output" :dir :system)
(include-book "kestrel/std/system/fundef-enabledp" :dir :system)
(include-book "kestrel/std/system/guard-verified-p" :dir :system)
(include-book "kestrel/utilities/er-soft-plus" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ defun-inst-implementation
  :parents (soft-implementation defun-inst)
  :short "Implementation of @(tsee defun-inst)."
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-qrewrite-rule-funvars ((fun symbolp) (wrld plist-worldp))
  :returns (err-msg? "A @(tsee maybe-msgp).")
  :mode :program
  :short "Check if the rewrite rule of a quantifier second-order function,
          or of an instance of it,
          depends exactly on the same function variables
          that the matrix of the function depends on."
  :long
  (xdoc::topstring
   (xdoc::p
    "When a quantifier second-order function, or an instance thereof,
     is introduced,
     the submitted event form first introduces the function,
     and then checks whether its rewrite rule depends
     exactly on the same function variables
     that the matrix of the function depends on.
     The following code performs this check.")
   (xdoc::p
    "If the check is satisfied, @('nil') is returned.
     Otherwise, an error message is returned.")
   (xdoc::p
    "This check is relevant when the rewrite rule is a custom one.
     Otherwise, it is a redundant check."))
  (let* ((rule-name (defun-sk-rewrite-name fun wrld))
         (rule-body (formula rule-name nil wrld))
         (fun-matrix (defun-sk-matrix fun wrld)))
    (if (set-equiv (funvars-of-term rule-body wrld)
                   (funvars-of-term fun-matrix wrld))
        nil
      (msg "The custom rewrite rule ~x0 must have ~
            the same function variables as the function's matrix ~x1.~%"
           rule-body fun-matrix))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-sofun-inst (sofun-inst (wrld plist-worldp))
  :returns (yes/no "A @(tsee booleanp).")
  :verify-guards nil
  :short "Recognize designations of instances of second-order functions."
  :long
  (xdoc::topstring-p
   "A designation of an instance of a second-order function has the form
    @('(sofun (f1 . g1) ... (fM . gM))'),
    where @('sofun') is a second-order function
    and @('((f1 . g1) ... (fM . gM))') is an instantiation.
    These designations are used in @(tsee defun-inst).")
  (and (true-listp sofun-inst)
       (>= (len sofun-inst) 2)
       (sofunp (car sofun-inst) wrld)
       (funvar-instp (cdr sofun-inst) wrld)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defun-inst-plain-events ((fun symbolp)
                                 (sofun (plain-sofunp sofun (w state)))
                                 inst
                                 (options keyword-value-listp)
                                 (ctx "Context for errors.")
                                 state)
  :returns (mv (erp "@(tsee booleanp) flag of the
                     <see topic='@(url acl2::error-triple)'>error
                     triple</see>.")
               (events+result+funvars
                "A tuple @('(events result funvars)') where
                 @('events') is a @(tsee pseudo-event-form-listp),
                 @('result') is a @(tsee maybe-pseudo-event-formp),
                 and @('funvars') is a @(tsee funvar-listp).")
               state)
  :mode :program
  :short "Generate a list of events to submit,
          when instantiating a plain second-order function."
  :long
  (xdoc::topstring
   (xdoc::p
    "Also return the @(tsee defun2) or @(tsee defun) event form,
     without the termination hints.
     This is printed when @(':print') is @(':result').")
   (xdoc::p
    "Also return the function variables that the new function depends on.")
   (xdoc::p
    "Only the @(':verify-guards'), @(':enable'), and @(':print') options
     may be present.")
   (xdoc::p
    "We add @('fun') to the table of second-order functions
     iff it is second-order.")
   (xdoc::p
    "If @('sofun') (and consequently @('fun')) is recursive,
     we extend the instantiation with @('(sofun . fun)'),
     to ensure that the recursive calls are properly transformed."))
  (b* ((wrld (w state))
       ((unless (subsetp (evens options)
                         '(:verify-guards :enable :print)))
        (er-soft+ ctx t nil
                  "Only the input keywords ~
                   :VERIFY-GUARDS, :ENABLE, and :PRINT are allowed, ~
                   because ~x0 is a plain second-order function."
                  sofun))
       (verify-guards (let ((verify-guards-option
                             (assoc-keyword :verify-guards options)))
                        (if verify-guards-option
                            (cadr verify-guards-option)
                          (guard-verified-p sofun wrld))))
       (enable (let ((enable-option (assoc-keyword :enable options)))
                 (if enable-option
                     (cadr enable-option)
                   (fundef-enabledp sofun state))))
       (sofun-body (ubody sofun wrld))
       (sofun-measure (if (recursivep sofun nil wrld)
                          (measure sofun wrld)
                        nil))
       (sofun-guard (uguard sofun wrld))
       (fsbs (if sofun-measure (acons sofun fun inst) inst))
       (fun-body (fun-subst-term fsbs sofun-body wrld))
       (fun-body-funvars (funvars-of-term fun-body wrld))
       (fun-body (untranslate fun-body nil wrld))
       (fun-measure (fun-subst-term inst sofun-measure wrld))
       (fun-measure-funvars (funvars-of-term fun-measure wrld))
       (fun-measure (untranslate fun-measure nil wrld))
       (fun-guard (fun-subst-term inst sofun-guard wrld))
       (fun-guard-funvars (funvars-of-term fun-guard wrld))
       (fun-guard (untranslate fun-guard t wrld))
       (sofun-tt-name `(:termination-theorem ,sofun))
       (sofun-tt-formula (and (recursivep sofun nil wrld)
                              (termination-theorem sofun wrld)))
       (fsbs (ext-fun-subst-term sofun-tt-formula inst wrld))
       (fun-tt-proof (sothm-inst-proof sofun-tt-name fsbs wrld))
       (hints (if fun-measure `(:hints (("Goal" ,@fun-tt-proof))) nil))
       (measure (if fun-measure `(:measure ,fun-measure) nil))
       (formals (formals sofun wrld))
       (funvars (remove-duplicates (append fun-body-funvars
                                           fun-measure-funvars
                                           fun-guard-funvars)))
       (defun-event `(defun ,fun ,formals
                       (declare (xargs :guard ,fun-guard
                                       :verify-guards ,verify-guards
                                  ,@measure
                                  ,@hints))
                       ,fun-body))
       (result `(,(if funvars 'defun2 'defun)
                 ,fun
                 ,formals
                 (declare (xargs :guard ,fun-guard
                                 :verify-guards ,verify-guards
                            ,@measure))
                 ,fun-body))
       (disable-event?
        (if enable
            nil
          `((in-theory (disable ,fun)))))
       (table-event?
        (if funvars
            `((table second-order-functions ',fun ',funvars))
          nil)))
    (value (list `(,defun-event ,@disable-event? ,@table-event?)
                 result
                 funvars))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defun-inst-choice-events ((fun symbolp)
                                  (sofun (choice-sofunp sofun (w state)))
                                  inst
                                  (options keyword-value-listp)
                                  (ctx "Context for errors.")
                                  state)
  :returns (mv (erp "@(tsee booleanp) flag of the
                     <see topic='@(url acl2::error-triple)'>error
                     triple</see>.")
               (events+result+funvars
                "A tuple @('(events result funvars)') where
                 @('events') is a @(tsee pseudo-event-form-listp),
                 @('result') is a @(tsee maybe-pseudo-event-formp),
                 and @('funvars') is a @(tsee funvar-listp).")
               state)
  :mode :program
  :short "Generate a list of events to submit,
          when instantiating a choice second-order function."
  :long
  (xdoc::topstring
   (xdoc::p
    "Also return the @(tsee defchoose2) or @(tsee defchoose) event form.
     This is printed when @(':print') is @(':result').")
   (xdoc::p
    "Also return the function variables that the new function depends on.")
   (xdoc::p
    "Only the @(':print') option may be present.")
   (xdoc::p
    "We add @('fun') to the table of second-order functions
     iff it is second-order."))
  (b* ((wrld (w state))
       ((unless (subsetp (evens options)
                         '(:print)))
        (er-soft+ ctx t nil
                  "Only the input keyword :PRINT is allowed, ~
                   because ~x0 is a choice second-order function."
                  sofun))
       (bound-vars (defchoose-bound-vars sofun wrld))
       (sofun-body (defchoose-body sofun wrld))
       (fun-body (fun-subst-term inst sofun-body wrld))
       (funvars (funvars-of-term fun-body wrld))
       (fun-body (untranslate fun-body nil wrld))
       (formals (formals sofun wrld))
       (strengthen (defchoose-strengthen sofun wrld))
       (funvars (remove-duplicates funvars))
       (defchoose-event `(defchoose ,fun ,bound-vars ,formals
                           ,fun-body
                           :strengthen ,strengthen))
       (result `(,(if funvars 'defchoose2 'defchoose)
                 ,fun
                 ,bound-vars
                 ,formals
                 ,fun-body
                 :strengthen ,strengthen))
       (table-event?
        (if funvars
            `((table second-order-functions ',fun ',funvars))
          nil)))
    (value (list `(,defchoose-event ,@table-event?)
                 result
                 funvars))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defun-inst-quant-events ((fun symbolp)
                                 (sofun (quant-sofunp sofun (w state)))
                                 inst
                                 (options keyword-value-listp)
                                 (ctx "Context for errors.")
                                 state)
  :returns (mv (erp "@(tsee booleanp) flag of the
                     <see topic='@(url acl2::error-triple)'>error
                     triple</see>.")
               (events+result+funvars
                "A tuple @('(events result funvars)') where
                 @('events') is a @(tsee pseudo-event-form-listp),
                 @('result') is a @(tsee maybe-pseudo-event-formp),
                 and @('funvars') is a @(tsee funvar-listp).")
               state)
  :mode :program
  :short "Generate a list of events to submit,
          when instantiating a quantifier second-order function."
  :long
  (xdoc::topstring
   (xdoc::p
    "Also return the @(tsee defun-sk2) or @(tsee defun-sk) event form.
     This is printed when @(':print') is @(':result').")
   (xdoc::p
    "Also return the function variables that the new function depends on.")
   (xdoc::p
    "Only the
     @(':verify-guards'),
     @(':enable'),
     @(':skolem-name'),
     @(':thm-name'),
     @(':rewrite'),
     @(':constrain'), and
     @(':print')
     options may be present.")
   (xdoc::p
    "We add @('fun') to the table of second-order functions
     iff it is second-order."))
  (b* ((wrld (w state))
       ((unless (subsetp (evens options)
                         '(:verify-guards
                           :enable
                           :skolem-name
                           :thm-name
                           :rewrite
                           :constrain
                           :print)))
        (er-soft+ ctx t nil
                  "Only the input keywords ~
                   :VERIFY-GUARDS, ~
                   :ENABLE, ~
                   :SKOLEM-NAME, ~
                   :THM-NAME,  ~
                   :REWRITE, ~
                   :CONSTRAIN and ~
                   :PRINT ~
                   are allowed, ~
                   because ~x0 is a quantifier second-order function."
                  sofun))
       (enable (let ((enable-option (assoc-keyword :enable options)))
                 (if enable-option
                     (cadr enable-option)
                   (fundef-enabledp sofun state))))
       (verify-guards (let ((verify-guards-option
                             (assoc-keyword :verify-guards options)))
                        (if verify-guards-option
                            (cadr verify-guards-option)
                          (guard-verified-p sofun wrld))))
       (bound-vars (defun-sk-bound-vars sofun wrld))
       (quant (defun-sk-quantifier sofun wrld))
       (sofun-matrix (defun-sk-matrix sofun wrld))
       (fun-matrix (fun-subst-term inst sofun-matrix wrld))
       (fun-matrix-funvars (funvars-of-term fun-matrix wrld))
       (fun-matrix (untranslate fun-matrix nil wrld))
       (rewrite-option (assoc-keyword :rewrite options))
       (rewrite
        (if rewrite-option
            (cadr rewrite-option)
          (let ((qrkind (defun-sk-rewrite-kind sofun wrld)))
            (case qrkind
              (:default :default)
              (:direct :direct)
              (:custom
               (let* ((fsbs (acons sofun fun inst))
                      (rule-name (defun-sk-rewrite-name sofun wrld))
                      (term (formula rule-name nil wrld)))
                 (fun-subst-term fsbs term wrld)))))))
       (skolem-name (let ((skolem-name-option
                           (assoc-keyword :skolem-name options)))
                      (if skolem-name-option
                          `(:skolem-name ,(cadr skolem-name-option))
                        nil)))
       (thm-name (let ((thm-name-option
                        (assoc-keyword :thm-name options)))
                   (if thm-name-option
                       `(:thm-name ,(cadr thm-name-option))
                     nil)))
       (constrain (let ((constrain-option
                         (assoc-keyword :constrain options)))
                    (if constrain-option
                        `(:constrain ,(cadr constrain-option))
                      nil)))
       (sofun-guard (uguard sofun wrld))
       (fun-guard (fun-subst-term inst sofun-guard wrld))
       (fun-guard-funvars (funvars-of-term fun-guard wrld))
       (fun-guard (untranslate fun-guard t wrld))
       (formals (formals sofun wrld))
       (strengthen (defun-sk-strengthen sofun wrld))
       (body (list quant bound-vars fun-matrix))
       (rest `(:strengthen ,strengthen
               :quant-ok t
               ,@(and (eq quant 'forall)
                      (list :rewrite rewrite))
               ,@skolem-name
               ,@thm-name
               ,@constrain))
       (funvars (remove-duplicates (append fun-matrix-funvars
                                           fun-guard-funvars)))
       (defun-sk-event `(defun-sk ,fun ,formals
                          (declare (xargs :guard ,fun-guard
                                          :verify-guards ,verify-guards))
                          ,body
                          ,@rest))
       (result `(,(if funvars 'defun-sk2 'defun-sk)
                 ,fun
                 ,formals
                 ,body
                 ,@rest))
       (disable-event?
        (if enable
            nil
          (let ((fn/defrule (cond ((eq constrain nil) fun)
                                  ((eq constrain t) (add-suffix fun
                                                                "-DEFINITION"))
                                  (t constrain)))
                (rwrule (if thm-name
                            (cadr thm-name)
                          (if (eq quant 'forall)
                              (add-suffix fun "-NECC")
                            (add-suffix fun "-SUFF")))))
            `((in-theory (disable ,fn/defrule ,rwrule))))))
       (table-event?
        (if funvars
            `((table second-order-functions ',fun ',funvars))
          nil))
       (check-event `(make-event-terse
                      (b* ((err-msg?
                            (check-qrewrite-rule-funvars ',sofun (w state))))
                        (if err-msg?
                            (er-soft+
                             (cons 'defun-inst ',fun) t nil "~@0" err-msg?)
                          (value '(value-triple :invisible)))))))
    (value (list `(,defun-sk-event ,@disable-event? ,@table-event? ,check-event)
                 result
                 funvars))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defun-inst-fn (fun
                       sofun-inst
                       options
                       (ctx "Context for errors.")
                       state)
  :returns (mv (erp "@(tsee booleanp) flag of the
                     <see topic='@(url acl2::error-triple)'>error
                     triple</see>.")
               (event "A @(tsee maybe-pseudo-event-formp).")
               state)
  :mode :program
  :short "Validate some of the inputs to @(tsee defun-inst)
          and generate the event form to submit."
  :long
  (xdoc::topstring
   (xdoc::p
    "We directly check the name and instance designation,
     we directly check the correct presence of keyed options
     (we do that in
     @(tsee defun-inst-plain-events),
     @(tsee defun-inst-choice-events), and
     @(tsee defun-inst-quant-events)), and
     we directly check the correct value of the @(':print') option (if present),
     but rely on @(tsee defun), @(tsee defchoose), and @(tsee defun-sk)
     to check the values of the other keyed options.")
   (xdoc::p
    "Prior to introducing @('fun'),
     we generate local events
     to avoid errors due to ignored or irrelevant formals in @('fun')
     (which may happen if @('sofun') has ignored or irrelevant formals).
     We add @('fun') to the table of instances of second-order functions."))
  (b* ((wrld (w state))
       ((unless (symbolp fun))
        (er-soft+ ctx t nil
                  "The first input must be a name, but ~x0 is not."
                  fun))
       ((unless (check-sofun-inst sofun-inst wrld))
        (er-soft+ ctx t nil
                  "The second input must be ~
                   the name of a second-order function ~
                   followed by the pairs of an instantiation, ~
                   but ~x0 is not."
                  sofun-inst))
       (sofun (car sofun-inst))
       (inst (cdr sofun-inst))
       ((unless (subsetp (alist-keys inst) (sofun-funvars sofun wrld)))
        (er-soft+ ctx t nil
                  "Each function variable key of ~x0 must be ~
                   among the function variables ~x1 ~
                   that ~x2 depends on."
                  inst (sofun-funvars sofun wrld) sofun))
       ((unless (keyword-value-listp options))
        (er-soft+ ctx t nil
                  "The inputs after the second input ~
                   must be a keyword-value list, ~
                   but ~x0 is not."
                  options))
       (keywords (evens options))
       ((unless (no-duplicatesp keywords))
        (er-soft+ ctx t nil
                  "The input keywords must be unique."))
       (print-pair (assoc-keyword :print options))
       (print (if print-pair
                  (cadr print-pair)
                :result))
       ((unless (member-eq print '(nil :all :result)))
        (er-soft+ ctx t nil
                  "The :PRINT input must be NIL, :ALL, or :RESULT, ~
                   but ~x0 is not."
                  print))
       ((er (list fun-intro-events result funvars))
        (case (sofun-kind sofun wrld)
          (plain
           (defun-inst-plain-events fun sofun inst options ctx state))
          (choice
           (defun-inst-choice-events fun sofun inst options ctx state))
          (quant
           (defun-inst-quant-events fun sofun inst options ctx state))
          (t (prog2$ (impossible) (value (list nil nil))))))
       (instmap (sof-instances sofun wrld))
       (new-instmap (put-sof-instance inst fun instmap wrld))
       (encapsulate
         `(encapsulate
            ()
            (set-ignore-ok t)
            (set-irrelevant-formals-ok t)
            ,@fun-intro-events
            (table sof-instances ',sofun ',new-instmap)))
       (result-event `(cw-event "~x0~|" ',result))
       (print-funvar-event
        (if funvars
            `(cw-event
              "The function ~x0 depends on the function variables ~x1.~%"
              ',fun ',funvars)
          `(cw-event "The function ~x0 depends on no function variables.~%"
                     ',fun)))
       (return-value-event `(value-triple ',fun))
       (event (cond ((eq print nil)
                     `(progn
                        ,encapsulate
                        ,print-funvar-event
                        ,return-value-event))
                    ((eq print :all)
                     (restore-output
                      `(progn
                         ,encapsulate
                         ,print-funvar-event
                         ,return-value-event)))
                    ((eq print :result)
                     `(progn
                        ,encapsulate
                        ,result-event
                        ,print-funvar-event
                        ,return-value-event))
                    (t (impossible)))))
    (value event)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection defun-inst-macro-definition
  :short "Definition of the @(tsee defun-inst) macro."
  :long
  "@(def defun-inst)
   @(def acl2::defun-inst)"

  (defmacro defun-inst (fun sofun-inst &rest rest)
    `(make-event-terse (defun-inst-fn
                         ',fun
                         ',sofun-inst
                         ',rest
                         (cons 'defun-inst ',fun)
                         state)))

  (defmacro acl2::defun-inst (&rest args)
    `(defun-inst ,@args)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection show-defun-inst
  :short "Show the event form generated by @(tsee defun-inst),
          without submitting them."
  :long
  "@(def show-defun-inst)
   @(def acl2::show-defun-inst)"

  (defmacro show-defun-inst (fun sofun-inst &rest rest)
    `(defun-inst-fn
       ',fun
       ',sofun-inst
       ',rest
       (cons 'defun-inst ',fun)
       state))

  (defmacro acl2::show-defun-inst (&rest args)
    `(show-defun-inst ,@args)))
