; Standard Utilities Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "centaur/fty/top" :dir :system)
(include-book "clause-processors/pseudo-term-fty" :dir :system)
(include-book "kestrel/fty/deffixequiv-sk" :dir :system)
(include-book "kestrel/fty/symbol-set" :dir :system)
(include-book "kestrel/utilities/er-soft-plus" :dir :system)
(include-book "kestrel/utilities/messages" :dir :system)
(include-book "std/system/check-user-term" :dir :system)
(include-book "std/system/fresh-namep" :dir :system)
(include-book "std/util/define-sk" :dir :system)
(include-book "std/util/defirrelevant" :dir :system)
(include-book "std/util/defprojection" :dir :system)
(include-book "std/util/error-value-tuples" :dir :system)
(include-book "system/pseudo-event-form-listp" :dir :system)

(local (include-book "kestrel/lists-light/no-duplicatesp-equal" :dir :system))
(local (include-book "kestrel/utilities/msgp" :dir :system))
(local (include-book "std/system/all-vars" :dir :system))
(local (include-book "std/system/pseudo-event-form-listp" :dir :system))
(local (include-book "std/system/w" :dir :system))
(local (include-book "std/alists/pairlis" :dir :system))
(local (include-book "std/typed-lists/atom-listp" :dir :system))
(local (include-book "std/typed-lists/pseudo-term-listp" :dir :system))
(local (include-book "std/typed-lists/string-listp" :dir :system))
(local (include-book "std/typed-lists/symbol-listp" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; move to Std/basic

(define symbol-lfix ((x symbolp))
  :returns (x-fixed symbolp)
  (mbe :logic (symbol-fix x)
       :exec x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; move to FTY

(defrule symbol-setp-of-mergesort
  (equal (symbol-setp (set::mergesort x))
         (symbol-listp (true-list-fix x)))
  :induct t
  :enable set::mergesort)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; move to Std/system

(define legal-variable-listp ((names true-listp))
  :returns (yes/no booleanp)
  (or (endp names)
      (and (legal-variablep (car names))
           (legal-variable-listp (cdr names)))))

(define check-user-term$ (x state)
  :returns (mv (term/message (or (pseudo-termp term/message)
                                 (msgp term/message)))
               (stobjs-out symbol-listp))
  (b* ((wrld (w state))
       ((mv erp val)
        (magic-ev-fncall 'check-user-term (list x wrld) state nil nil))
       ((when erp)
        (raise "Internal error: call of CHECK-USER-TERM failed.")
        (mv nil nil))
       ((unless (and (true-listp val)
                     (= (len val) 2)))
        (raise "Internal error: call of CHECK-USER-TERM returns ~x0." val)
        (mv nil nil))
       ((list term/message stobjs-out) val)
       ((unless (or (pseudo-termp term/message)
                    (msgp term/message)))
        (raise "Internal error: CHECK-USER-TERM returned ~x0." term/message)
        (mv nil nil))
       ((unless (symbol-listp stobjs-out))
        (raise "Internal error: CHECK-USER-TERM returned ~x0." stobjs-out)
        (mv nil nil)))
    (mv term/message stobjs-out))
  :no-function nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-implementation

 definductive

 :items

 ((xdoc::evmac-topic-implementation-item-input "name")

  (xdoc::evmac-topic-implementation-item-input "preds")

  "@('pred') is an element of @('preds')."

  "@('pred-name') is the name of
   one of the predicates specified in the @(':preds') input,
   i.e. a @('p[i]') in the user documentation."

  "@('pred-names') is the list of names @('p[1]'), ..., @('p[n]'),
   in that order."

  "@('pred-formals') is the list of the formals @('x[i,1]'), ..., @('x[i,m[i]]')
   of one of the predicates specified in the @(':preds') input,
   i.e. a @('p[i]') in the user documentation."

  (xdoc::evmac-topic-implementation-item-input "irules")

  "@('irule-name') is the name of
   one of the inference rules specified in the @(':irules') input,
   i.e. a @('rule[k]') in the user documentation."

  (xdoc::evmac-topic-implementation-item-input "parents")

  (xdoc::evmac-topic-implementation-item-input "short")

  (xdoc::evmac-topic-implementation-item-input "long")

  "@('xdocp') is a flag saying whether XDOC should be generated or not.")

 :additional

 ((xdoc::p
   "As also done above, the documentation of the implementation
    refers to the notation used in the user documentation,
    e.g. the names @('p[i]') of the predicates being defined.")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ definductive-info
  :parents (definductive-implementation)
  :short "Information about the predicates and inference rules."
  :long
  (xdoc::topstring
   (xdoc::p
    "We introduce data structures, and operations on them,
     for the information about the predicates and inference rules."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod defind-pred-info
  :short "Fixtype of information about a predicate being defined."
  :long
  (xdoc::topstring
   (xdoc::p
    "For each predicate, we have
     its name @('p[i]') and its formals @('x[i,j]')."))
  ((name symbol)
   (formals symbol-list))
  :pred defind-pred-infop)

;;;;;;;;;;

(defirrelevant irr-defind-pred-info
  :short "Irrelevant information about a predicate being defined."
  :type defind-pred-infop
  :body (defind-pred-info nil nil))

;;;;;;;;;;;;;;;;;;;;

(fty::defoption defind-pred-info-option
  defind-pred-info
  :short "Fixtype of optional information about a predicate being defined."
  :pred defind-pred-info-optionp)

;;;;;;;;;;;;;;;;;;;;

(fty::deflist defind-pred-info-list
  :short "Fixtype of lists of information about a predicate being defined."
  :elt-type defind-pred-info
  :true-listp t
  :elementp-of-nil nil
  :pred defind-pred-info-listp)

;;;;;;;;;;

(std::defprojection defind-pred-info-list->name ((x defind-pred-info-listp))
  :returns (names symbol-listp)
  :short "Lift @(tsee defind-pred-info->name) to lists."
  (defind-pred-info->name x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod defind-term-info
  :short "Fixtype of information about a term."
  :long
  (xdoc::topstring
   (xdoc::p
    "The terms that this information pertains to are
     (i) whole premises of inference rules
     that do not contain the @('p[i]') predicates,
     or (ii) arguments @('arg[j]') of premises and conclusions
     of the form @('(p[i] arg[1] ... arg[m[i]])').
     That is, these are the components of rules
     whose internal structure is not of concern
     for the workings of the @(tsee definductive) macro
     (aside from satisfying certain conditions).")
   (xdoc::p
    "The information about each of these terms consists of
     the term in untranslated form
     and the term in translated form.
     The former is used in generated events,
     while the latter is used for performing certain checks."))
  ((uterm "An untranslated term.")
   (tterm pseudo-termp))
  :pred defind-term-infop)

;;;;;;;;;;

(defirrelevant irr-defind-term-info
  :short "Irrelevant information about a term."
  :type defind-term-infop
  :body (defind-term-info nil nil))

;;;;;;;;;;;;;;;;;;;;

(fty::deflist defind-term-info-list
  :short "Fixtype of lists of information about a term."
  :elt-type defind-term-info
  :true-listp t
  :elementp-of-nil nil
  :pred defind-term-info-listp)

;;;;;;;;;;

(std::defprojection defind-term-info-list->uterm ((x defind-term-info-listp))
  :short "Lift @(tsee defind-term-info->uterm) to lists."
  (defind-term-info->uterm x))

;;;;;;;;;;

(std::defprojection defind-term-info-list->tterm ((x defind-term-info-listp))
  :returns (tterms pseudo-term-listp)
  :short "Lift @(tsee defind-term-info->tterm) to lists."
  (defind-term-info->tterm x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum defind-premise-info
  :short "Fixtype of information about a premise of a rule."
  :long
  (xdoc::topstring
   (xdoc::p
    "A premise has the form of
     (i) a call of a @('p[i]') predicate
     on some terms not containing the predicates being defined,
     or (ii) some term not containing the predicates being defined."))
  (:pred ((name symbol)
          (args defind-term-info-list)))
  (:other ((term defind-term-info)))
  :pred defind-premise-infop)

;;;;;;;;;;;;;;;;;;;;

(fty::deflist defind-premise-info-list
  :short "Fixtype of lists of information about a premise of a rule."
  :elt-type defind-premise-info
  :true-listp t
  :elementp-of-nil nil
  :pred defind-premise-info-listp)

;;;;;;;;;;

(defirrelevant irr-defind-premise-info
  :short "Irrelevant information about a premise of a rule."
  :type defind-premise-infop
  :body (defind-premise-info-pred nil nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod defind-conclusion-info
  :short "Fixtype of information about a conclusion of a rule."
  :long
  (xdoc::topstring
   (xdoc::p
    "Conclusions always have the form of
     a call of a @('p[i]') predicate
     on some terms not containing the predicates being defined.
     It is like the @(':pred') case of @(tsee defind-premise-info)."))
  ((name symbol)
   (args defind-term-info-list))
  :pred defind-conclusion-infop)

;;;;;;;;;;

(defirrelevant irr-defind-conclusion-info
  :short "Irrelevant information about a conclusion of a rule."
  :type defind-conclusion-infop
  :body (defind-conclusion-info nil nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod defind-irule-info
  :short "Fixtype of information about a rule."
  :long
  (xdoc::topstring
   (xdoc::p
    "This consists of a name,
     the information about zero or more premises,
     and the information about the conclusion."))
  ((name symbol)
   (premises defind-premise-info-list)
   (conclusion defind-conclusion-info))
  :pred defind-irule-infop)

;;;;;;;;;;

(defirrelevant irr-defind-irule-info
  :short "Irrelevant information about a rule."
  :type defind-irule-infop
  :body (defind-irule-info nil nil (irr-defind-conclusion-info)))

;;;;;;;;;;;;;;;;;;;;

(fty::deflist defind-irule-info-list
  :short "Fixtype of lists of information about a rule."
  :elt-type defind-irule-info
  :true-listp t
  :elementp-of-nil nil
  :pred defind-irule-info-listp)

;;;;;;;;;;

(std::defprojection defind-irule-info-list->name ((x defind-irule-info-listp))
  :returns (names symbol-listp)
  :short "Lift @(tsee defind-irule-info->name) to lists."
  (defind-irule-info->name x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-lookup-pred ((pred-name symbolp) (infos defind-pred-info-listp))
  :guard (no-duplicatesp-equal (defind-pred-info-list->name infos))
  :returns (info? defind-pred-info-optionp)
  :short "Look up the information about the predicate."
  :long
  (xdoc::topstring
   (xdoc::p
    "The first match is returned,
     but the list has no duplicate names (see guard),
     so if there is a match it is the only one."))
  (b* (((when (endp infos)) nil)
       ((defind-pred-info info) (car infos))
       ((when (eq (symbol-lfix pred-name) info.name))
        (defind-pred-info-fix info)))
    (defind-lookup-pred pred-name (cdr infos))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-term-info-free-vars ((info defind-term-infop))
  :returns (vars symbol-setp)
  :short "Free variables in the information about a term."
  :long
  (xdoc::topstring
   (xdoc::p
    "That is, the free variables obtained from
     the translated form of the term."))
  (set::mergesort (all-vars (defind-term-info->tterm info))))

;;;;;;;;;;;;;;;;;;;;

(define defind-term-info-list-free-vars ((infos defind-term-info-listp))
  :returns (vars symbol-setp)
  :short "Free variables in a list of information about terms."
  (cond ((endp infos) nil)
        (t (set::union (defind-term-info-free-vars (car infos))
                       (defind-term-info-list-free-vars (cdr infos)))))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;

(define defind-premise-info-free-vars ((info defind-premise-infop))
  :returns (vars symbol-setp)
  :short "Free variables in the information about a premise."
  (defind-premise-info-case
    info
    :pred (defind-term-info-list-free-vars info.args)
    :other (defind-term-info-free-vars info.term)))

;;;;;;;;;;;;;;;;;;;;

(define defind-premise-info-list-free-vars ((infos defind-premise-info-listp))
  :returns (vars symbol-setp)
  :short "Free variables in a list of information about premises."
  (cond ((endp infos) nil)
        (t (set::union (defind-premise-info-free-vars (car infos))
                       (defind-premise-info-list-free-vars (cdr infos)))))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;

(define defind-conclusion-info-free-vars ((info defind-conclusion-infop))
  :returns (vars symbol-setp)
  :short "Free variables in the information about a conclusion."
  (defind-term-info-list-free-vars (defind-conclusion-info->args info)))

;;;;;;;;;;;;;;;;;;;;

(define defind-irule-info-free-vars ((info defind-irule-infop))
  :returns (vars symbol-setp)
  :short "Free variables in the information about an inference rule."
  (b* (((defind-irule-info info)))
    (set::union (defind-premise-info-list-free-vars info.premises)
                (defind-conclusion-info-free-vars info.conclusion))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-input-processing definductive)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-process-name (name (wrld plist-worldp))
  :returns (mv erp (name symbolp))
  :short "Process the @('name') input."
  :long
  (xdoc::topstring
   (xdoc::p
    "Although currently we do not generate any event with this name
     (technically, XDOC topics are not ACL2 event names),
     we check that it is not an existing event name,
     to reduce possible confusion
     and the chance that it may shadow another XDOC topic.")
   (xdoc::p
    "We may also check directly that it does not shadow any topic.
     But all these checks only take the current world into consideration:
     shadowing may occur when putting different books together,
     and can be realiably detected only when building the whole manual.
     We could also omit these checks if no XDOC topic is in fact generated,
     but it seems conceptually best, even in that case,
     to ensure some separation between the name supplied here
     and any existing names in the world."))
  (b* (((reterr) nil)
       ((unless (symbolp name))
        (reterr (msg "The NAME input must be a symbol, ~
                      but it is ~x0 instead."
                     name)))
       ((when (keywordp name))
        (reterr (msg "The NAME input must not be a keyword, ~
                      but it is ~x0 instead."
                     name)))
       (msg/nil (fresh-namep-msg-weak name nil wrld))
       ((when msg/nil)
        ;; No period at the end of the following string
        ;; because MSG/NIL ends with period already.
        (reterr (msg "The NAME input must be a fresh name, but ~@0"
                     msg/nil))))
    (retok name)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-process-pred (pred (i posp) (wrld plist-worldp))
  :returns (mv erp (info defind-pred-infop))
  :short "Process an element of the @(':preds') input."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('i') input of this function is
     the index of the predicate @('p[i]')
     that must be described by the @('pred') of this function.")
   (xdoc::p
    "We ensure that the name is a valid fresh one for a function."))
  (b* (((reterr) (irr-defind-pred-info))
       ((unless (and (symbol-listp pred)
                     (consp pred)
                     (consp (cdr pred))))
        (reterr (msg "The ~n0 element of the :PREDS input ~
                      must be a list of at least two symbols, ~
                      but it is ~x1 instead."
                     (list (lposfix i)) pred)))
       (pred-name (car pred))
       (pred-formals (cdr pred))
       ((when (keywordp pred-name))
        (reterr (msg "The name of the predicate in ~
                      the ~n0 element of the :PREDS input ~
                      must not be a keyword, ~
                      but it is ~x1 instead."
                     (list (lposfix i)) pred-name)))
       (msg/nil (fresh-namep-msg-weak pred-name 'function wrld))
       ((when msg/nil)
        ;; No period at the end of the following string
        ;; because MSG/NIL ends with period already.
        (reterr (msg "The name of the predicate in ~
                      the ~n0 element of the :PREDS input ~
                      must be fresh, but ~@1"
                     (list (lposfix i)) msg/nil)))
       ((unless (legal-variable-listp pred-formals))
        (reterr (msg "The formals of the predicate in ~
                      the ~n0 element of the :PREDS input ~
                      must be legal variable names, ~
                      but at least one in ~&1 is not."
                     (list (lposfix i)) pred-formals)))
       ((unless (no-duplicatesp-eq pred-formals))
        (reterr (msg "The formals of the predicate in ~
                      the ~n0 element of the :PREDS input ~
                      must be all distinct, ~
                      but there are duplicates among ~&1."
                     (list (lposfix i)) pred-formals))))
    (retok (make-defind-pred-info :name pred-name
                                  :formals pred-formals))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-process-preds (preds
                              (preds-suppliedp booleanp)
                              (wrld plist-worldp))
  :returns (mv erp (infos defind-pred-info-listp))
  :short "Process the @(':preds') input."
  (b* (((reterr) nil)
       ((unless preds-suppliedp)
        (reterr (msg "The :PREDS input must be supplied.")))
       ((unless (and (true-listp preds)
                     (consp preds)))
        (reterr (msg "The :PREDS input must be a non-empty list, ~
                      but it is ~x0 instead."
                     preds)))
       ((when (consp (cdr preds)))
        (reterr (msg "The current implementation of DEFINDUCTIVE ~
                      only supports a single predicate, ~
                      but the :PREDS input has ~x0 elements."
                     (len preds))))
       ((erp infos) (defind-process-preds-loop preds 1 wrld))
       (pred-names (defind-pred-info-list->name infos))
       ((unless (no-duplicatesp-eq pred-names))
        (reterr (msg "The names of the predicates in the :PREDS input ~
                      must be all distinct, ~
                      but there are duplicates among ~&0."
                     pred-names))))
    (retok infos))

  :prepwork
  ((define defind-process-preds-loop ((preds true-listp)
                                      (i posp)
                                      (wrld plist-worldp))
     :returns (mv erp (infos defind-pred-info-listp))
     :parents nil
     (b* (((reterr) nil)
          ((when (endp preds)) (retok nil))
          ((erp info) (defind-process-pred (car preds) i wrld))
          ((erp infos)
           (defind-process-preds-loop (cdr preds) (1+ (lposfix i)) wrld)))
       (retok (cons info infos)))))

  ///

  (defret no-duplicatesp-equal-of-defind-process-preds
    (no-duplicatesp-equal (defind-pred-info-list->name infos))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-process-term (term (desc msgp) state)
  :returns (mv erp (info defind-term-infop))
  :short "Process a term in a rule."
  :long
  (xdoc::topstring
   (xdoc::p
    "The input to this function is
     either a whole premise that does not have the form @('(p[i] ...'))
     or an argument of a premise or conclusion that has that form.
     The @(tsee definductive) macro accepts any terms there,
     so long as they are well-formed,
     which is checked by this function.
     The term must be a valid untranslated term,
     which we attempt to translate here.
     If the translation is successful,
     we return both the untranslated and translated term,
     packaged in a @(tsee defind-term-info).")
   (xdoc::p
    "Note that, before we get here,
     we have checked, in @(tsee defind-process-pred),
     that the predicates being defined are new.
     Thus, the translation of the term here fails
     if the term mentions those predicates.
     So this automatically checks their absence from the term.")
   (xdoc::p
    "We ensure that the term is single-valued, not a stobj.")
   (xdoc::p
    "The @('desc') input of this function is
     a description of the term, for error messages."))
  (b* (((reterr) (irr-defind-term-info))
       ((mv term/msg stobjs-out) (check-user-term$ term state))
       ((unless (pseudo-termp term/msg))
        ;; No period at the end of the following string
        ;; because TERM/MSG ends with period already.
        (reterr (msg "~@0 must be a valid untranslated term, but: ~@1"
                     desc term/msg)))
       ((unless (equal stobjs-out (list nil)))
        (reterr (msg "~@0 must return a single non-stobj value, ~
                      but it returns ~x1 instead."
                     desc stobjs-out))))
    (retok (make-defind-term-info :uterm term :tterm term/msg))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-process-args ((args true-listp) (prem/concl-desc msgp) state)
  :returns (mv erp (infos defind-term-info-listp))
  :short "Process the arguments of a premise or conclusion of a rule
          that has the form of a call of a predicate being defined."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('prem/concl-desc') input of this function provides
     a description of the premise or conclusion
     that the purported arguments belong to;
     it is used for error messages."))
  (defind-process-args-loop args prem/concl-desc 1 state)

  :prepwork
  ((define defind-process-args-loop ((args true-listp)
                                     (prem/concl-desc msgp)
                                     (q posp)
                                     state)
     :returns (mv erp (infos defind-term-info-listp))
     :parents nil
     (b* (((reterr) nil)
          ((when (endp args)) (retok nil))
          (arg-desc (msg "the ~n0 argument of ~@1"
                         (list (lposfix q))
                         (msg-downcase-first prem/concl-desc)))
          ((erp info) (defind-process-term (car args) arg-desc state))
          ((erp infos) (defind-process-args-loop
                         (cdr args) prem/concl-desc (1+ (lposfix q)) state)))
       (retok (cons info infos)))
     :guard-hints (("Goal" :in-theory (enable character-alistp))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-process-conclusion (concl
                                   (desc msgp)
                                   (pred-infos defind-pred-info-listp)
                                   state)
  :guard (no-duplicatesp-equal (defind-pred-info-list->name pred-infos))
  :returns (mv erp (info defind-conclusion-infop))
  :short "Process the conclusion of a rule."
  :long
  (xdoc::topstring
   (xdoc::p
    "This must have the form of a call of a predicate @('p[i]').")
   (xdoc::p
    "The @('desc') input of this function is
     a description of the conclusion, for error messages."))
  (b* (((reterr) (irr-defind-conclusion-info))
       ((unless (and (true-listp concl)
                     (consp concl)))
        (reterr (msg "~@0 must be a non-empty list, ~
                      but it is ~x1 instead."
                     desc concl)))
       (pred-name (car concl))
       ((unless (symbolp pred-name))
        (reterr (msg "~@0 must start with a symbol, ~
                      but it starts with ~x1 instead."
                     desc pred-name)))
       (args (cdr concl))
       (pred-info (defind-lookup-pred pred-name pred-infos))
       ((unless pred-info)
        (reterr (msg "~@0 must have the form of ~
                      a call of one of the predicates among ~&1, ~
                      but ~x2 is not one of them."
                     desc (defind-pred-info-list->name pred-infos) pred-name)))
       (pred-formals (defind-pred-info->formals pred-info))
       ((unless (= (len args) (len pred-formals)))
        (reterr (msg "The number of arguments in ~@0 ~
                      must match the number ~x1 of formals ~
                      of the predicate ~x2, ~
                      but it is ~x3 instead."
                     (msg-downcase-first desc)
                     (len pred-formals)
                     pred-name
                     (len args))))
       (args-desc (msg "the arguments of ~@0" (msg-downcase-first desc)))
       ((erp arg-infos) (defind-process-args args args-desc state)))
    (retok (make-defind-conclusion-info :name pred-name :args arg-infos)))
  :guard-hints (("Goal" :in-theory (enable character-alistp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-process-premise (prem
                                (desc msgp)
                                (pred-infos defind-pred-info-listp)
                                state)
  :guard (no-duplicatesp-equal (defind-pred-info-list->name pred-infos))
  :returns (mv erp (info defind-premise-infop))
  :short "Process the premise of a rule."
  :long
  (xdoc::topstring
   (xdoc::p
    "This may have the form of a call of a @('p[i]') predicate,
     as in @(tsee defind-process-conclusion),
     or it may be some other term not involving
     the predicates being defined.")
   (xdoc::p
    "The @('desc') input of this function is
     a description of the premise, for error messages."))
  (b* (((reterr) (irr-defind-premise-info))
       (pred-names (defind-pred-info-list->name pred-infos)))
    (if (and (true-listp prem)
             (consp prem)
             (member-equal (car prem) pred-names))
        (b* ((pred-name (car prem))
             (args (cdr prem))
             ((unless (symbolp pred-name))
              (raise "Internal error: ~x0 is not a symbol." pred-name)
              (reterr "irrelevant"))
             (pred-info (defind-lookup-pred pred-name pred-infos))
             ((unless pred-info)
              (raise "Internal error: no information for ~x0." pred-name)
              (reterr "irrelevant"))
             (pred-formals (defind-pred-info->formals pred-info))
             ((unless (= (len args) (len pred-formals)))
              (reterr (msg "The number of arguments in ~@0 ~
                            must match the number ~x1 of formals ~
                            of the predicate ~x2, ~
                            but it is ~x3 instead."
                           (msg-downcase-first desc)
                           (len pred-formals)
                           pred-name
                           (len args))))
             (args-desc (msg "the arguments of ~@0" (msg-downcase-first desc)))
             ((erp arg-infos) (defind-process-args args args-desc state)))
          (retok (make-defind-premise-info-pred :name pred-name
                                                :args arg-infos)))
      (b* ((desc (msg "Since ~@0 does not have the form of ~
                       a call of one of the predicates among ~&1, ~
                       it "
                      (msg-downcase-first desc) pred-names))
           ((erp info) (defind-process-term prem desc state)))
        (retok (make-defind-premise-info-other :term info)))))
  :no-function nil
  :guard-hints (("Goal" :in-theory (enable character-alistp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-process-premises (prems
                                 (irule-desc msgp)
                                 (pred-infos defind-pred-info-listp)
                                 state)
  :guard (no-duplicatesp-equal (defind-pred-info-list->name pred-infos))
  :returns (mv erp (infos defind-premise-info-listp))
  :short "Process the premises of a rule."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('irule-desc') input of this function is
     a description of the rule that the premises belong to;
     it is used for error message."))
  (b* (((reterr) nil)
       ((unless (true-listp prems))
        (reterr (msg "The premises of ~@0 must be a list, ~
                      but they are ~x1 instead."
                     irule-desc prems))))
    (defind-process-premises-loop prems 1 irule-desc pred-infos state))

  :prepwork
  ((define defind-process-premises-loop ((prems true-listp)
                                         (q posp)
                                         (irule-desc msgp)
                                         (pred-infos defind-pred-info-listp)
                                         state)
     :guard (no-duplicatesp-equal (defind-pred-info-list->name pred-infos))
     :returns (mv erp (infos defind-premise-info-listp))
     :parents nil
     (b* (((reterr) nil)
          ((when (endp prems)) (retok nil))
          (prem (car prems))
          (prem-desc
           (msg "The ~n0 premise of ~@1"
                (list (lposfix q))
                (msg-downcase-first irule-desc)))
          ((erp info) (defind-process-premise prem prem-desc pred-infos state))
          ((erp infos) (defind-process-premises-loop
                         (cdr prems) (1+ (lposfix q))
                         irule-desc pred-infos state)))
       (retok (cons info infos)))
     :guard-hints (("Goal" :in-theory (enable character-alistp))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-process-irule (irule
                              (desc msgp)
                              (pred-infos defind-pred-info-listp)
                              state)
  :guard (no-duplicatesp-equal (defind-pred-info-list->name pred-infos))
  :returns (mv erp (info defind-irule-infop))
  :short "Process a rule."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('desc') input of this function is
     a description of the rule, for error messages."))
  (b* (((reterr) (irr-defind-irule-info))
       ((unless (and (true-listp irule)
                     (= (len irule) 3)))
        (reterr (msg "~@0 must be a list of three elements, ~
                       but it is ~x1 instead."
                     desc irule)))
       ((list name prems concl) irule)
       ((unless (symbolp name))
        (reterr (msg "The first element of ~@0 must be a symbol, ~
                      but it is ~x1 instead."
                     desc name)))
       ((erp prem-infos)
        (defind-process-premises prems desc pred-infos state))
       (concl-desc (msg "The conclusion of ~@0" (msg-downcase-first desc)))
       ((erp concl-info)
        (defind-process-conclusion concl concl-desc pred-infos state)))
    (retok (make-defind-irule-info :name name
                                   :premises prem-infos
                                   :conclusion concl-info)))
  :guard-hints (("Goal" :in-theory (enable character-alistp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-process-irules (irules
                               (irules-suppliedp booleanp)
                               (pred-infos defind-pred-info-listp)
                               state)
  :guard (no-duplicatesp-equal (defind-pred-info-list->name pred-infos))
  :returns (mv erp (infos defind-irule-info-listp))
  :short "Process the @(':irules') input."
  (b* (((reterr) nil)
       ((unless irules-suppliedp)
        (reterr (msg "The :IRULES input must be supplied.")))
       ((unless (and (true-listp irules)
                     (consp irules)))
        (reterr (msg "The :IRULES input must be a non-empty list, ~
                      but it is ~x0 instead."
                     irules)))
       ((erp infos) (defind-process-irules-loop irules 1 pred-infos state))
       (irule-names (defind-irule-info-list->name infos))
       ((unless (no-duplicatesp-eq irule-names))
        (reterr (msg "The names of the rules in the :IRULES input ~
                      must be all distinct, ~
                      but there are duplicates among ~&0."
                     irule-names))))
    (retok infos))

  :prepwork
  ((define defind-process-irules-loop ((irules true-listp)
                                       (k posp)
                                       (pred-infos defind-pred-info-listp)
                                       state)
     :guard (no-duplicatesp-equal (defind-pred-info-list->name pred-infos))
     :returns (mv erp (infos defind-irule-info-listp))
     :parents nil
     (b* (((reterr) nil)
          ((when (endp irules)) (retok nil))
          (desc (msg "The ~n0 element of the :IRULES input" (list (lposfix k))))
          ((erp info) (defind-process-irule (car irules) desc pred-infos state))
          ((erp infos) (defind-process-irules-loop
                         (cdr irules) (1+ (lposfix k)) pred-infos state)))
       (retok (cons info infos)))
     :guard-hints (("Goal" :in-theory (enable character-alistp)))))

  ///

  (defret no-duplicatesp-equal-of-defind-process-irules
    (no-duplicatesp-equal (defind-irule-info-list->name infos))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-process-parents/short/long (parents
                                           (parents-suppliedp booleanp)
                                           short
                                           (short-suppliedp booleanp)
                                           long
                                           (long-suppliedp booleanp))
  :returns (mv erp (parents symbol-listp) short long (xdocp booleanp))
  :short "Process the @(':parents'), @(':short'), and @(':long') inputs."
  :long
  (xdoc::topstring
   (xdoc::p
    "We do not perform any check on the @(':short') and @(':long') inputs,
     which in general may be terms consisting of XDOC constructors."))
  (b* (((reterr) nil nil nil nil)
       ((when (and (not parents-suppliedp)
                   (not short-suppliedp)
                   (not long-suppliedp)))
        (retok nil nil nil nil))
       ((when (and parents-suppliedp
                   (not (and (symbol-listp parents)
                             (consp parents)))))
        (reterr (msg "The :PARENTS input must be a non-empty list of symbols, ~
                      but it is ~x0 instead."
                     parents)))
       (parents (and parents-suppliedp parents))
       (short (and short-suppliedp short))
       (long (and long-suppliedp long)))
    (retok parents short long t)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-process-inputs (name
                               preds
                               (preds-suppliedp booleanp)
                               irules
                               (irules-suppliedp booleanp)
                               parents
                               (parents-suppliedp booleanp)
                               short
                               (short-suppliedp booleanp)
                               long
                               (long-suppliedp booleanp)
                               state)
  :returns (mv erp
               (name symbolp)
               (pred-infos defind-pred-info-listp)
               (irule-infos defind-irule-info-listp)
               (parents symbol-listp)
               short
               long
               (xdocp booleanp))
  :short "Process all the inputs."
  (b* (((reterr) nil nil nil nil nil nil nil)
       (wrld (w state))
       ((erp name) (defind-process-name name wrld))
       ((erp pred-infos)
        (defind-process-preds preds preds-suppliedp wrld))
       ((erp irule-infos)
        (defind-process-irules irules irules-suppliedp pred-infos state))
       ((erp parents short long xdocp)
        (defind-process-parents/short/long
          parents parents-suppliedp
          short short-suppliedp
          long long-suppliedp)))
    (retok name pred-infos irule-infos parents short long xdocp))

  ///

  (defret no-duplicatesp-equal-of-defind-process-inputs-preds
    (no-duplicatesp-equal (defind-pred-info-list->name pred-infos)))

  (defret no-duplicatesp-equal-of-defind-process-inputs-irules
    (no-duplicatesp-equal (defind-irule-info-list->name irule-infos))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-event-generation definductive)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-assert-type-name ((pred-name symbolp) (name symbolp))
  :returns (type-name symbolp)
  :short "Name of a @('p[i]-assertion') fixtype."
  (packn-pos (list (symbol-lfix pred-name) '-assertion) (symbol-lfix name)))

;;;;;;;;;;

(define defind-proof-type-name ((pred-name symbolp) (name symbolp))
  :returns (type-name symbolp)
  :short "Name of a @('p[i]-proof') fixtype."
  (packn-pos (list (symbol-lfix pred-name) '-proof) (symbol-lfix name)))

;;;;;;;;;;;;;;;;;;;;

(define defind-assert-recog-name ((pred-name symbolp) (name symbolp))
  :returns (recog-name symbolp)
  :short "Name of the recognizer of a @('p[i]-assertion') fixtype."
  (packn-pos (list (symbol-lfix pred-name) '-assertionp) (symbol-lfix name)))

;;;;;;;;;;

(define defind-proof-recog-name ((pred-name symbolp) (name symbolp))
  :returns (recog-name symbolp)
  :short "Name of the recognizer of a @('p[i]-proof') fixtype."
  (packn-pos (list (symbol-lfix pred-name) '-proofp) (symbol-lfix name)))

;;;;;;;;;;;;;;;;;;;;

(define defind-assert-fixer-name ((pred-name symbolp) (name symbolp))
  :returns (fixer-name symbolp)
  :short "Name of the fixer of a @('p[i]-assertion') fixtype."
  (packn-pos (list (symbol-lfix pred-name) '-assertion-fix) (symbol-lfix name)))

;;;;;;;;;;

(define defind-proof-fixer-name ((pred-name symbolp) (name symbolp))
  :returns (fixer-name symbolp)
  :short "Name of the fixer of a @('p[i]-proof') fixtype."
  (packn-pos (list (symbol-lfix pred-name) '-proof-fix) (symbol-lfix name)))

;;;;;;;;;;;;;;;;;;;;

(define defind-assert-equiv-name ((pred-name symbolp) (name symbolp))
  :returns (recog-name symbolp)
  :short "Name of the equivalence of a @('p[i]-assertion') fixtype."
  (packn-pos (list (defind-assert-type-name pred-name name)
                   '-equiv)
             (symbol-lfix name)))

;;;;;;;;;;

(define defind-proof-equiv-name ((pred-name symbolp) (name symbolp))
  :returns (fixer-name symbolp)
  :short "Name of the equivalence of a @('p[i]-proof') fixtype."
  (packn-pos (list (symbol-lfix pred-name) '-proof-equiv) (symbol-lfix name)))

;;;;;;;;;;;;;;;;;;;;

(define defind-proof-constr-name ((pred-name symbolp)
                                  (irule-name symbolp)
                                  (name symbolp))
  :returns (constr-name symbolp)
  :short "Name of a constructor of a @('p[i]-proof') fixtype."
  (packn-pos (list (defind-proof-type-name pred-name name)
                   '-
                   (symbol-lfix irule-name))
             (symbol-lfix name)))

;;;;;;;;;;;;;;;;;;;;

(define defind-concl-field-name ((name symbolp))
  :returns (field-name symbolp)
  :short "Name of the conclusion field of a @('p[i]-proof') fixtype."
  (packn-pos (list 'conclusion) (symbol-lfix name)))

;;;;;;;;;;

(define defind-prem-field-name ((num posp) (name symbolp))
  :returns (field-name symbolp)
  :short "Name of a premise field of a @('p[i]-proof') fixtype."
  (packn-pos (list 'premise (lposfix num) '-proof) (symbol-lfix name)))

;;;;;;;;;;;;;;;;;;;;

(define defind-assert-var-name ((name symbolp))
  :returns (var-name symbolp)
  :short "Name of the assertion variable."
  (packn-pos (list 'assertion) (symbol-lfix name)))

;;;;;;;;;;

(define defind-proof-var-name ((name symbolp))
  :returns (var-name symbolp)
  :short "Name of the proof variable."
  (packn-pos (list 'proof) (symbol-lfix name)))

;;;;;;;;;;

(define defind-prem-var-name ((num posp) (name symbolp))
  :returns (var-name symbolp)
  :short "Name of a premise variable."
  (packn-pos (list 'prem (lposfix num)) (symbol-lfix name)))

;;;;;;;;;;

(define defind-concl-var-name ((name symbolp))
  :returns (var-name symbolp)
  :short "Name of the conclusion variable."
  (packn-pos (list 'concl) (symbol-lfix name)))

;;;;;;;;;;

(define defind-proof-prem-var-name ((num posp) (name symbolp))
  :returns (var-name symbolp)
  :short "Name of the variable bound to a premise of a proof."
  (packn-pos (list (defind-proof-var-name name)
                   #\.
                   (defind-prem-field-name num name))
             (symbol-lfix name)))

;;;;;;;;;;

(define defind-proof-concl-var-name ((name symbolp))
  :returns (var-name symbolp)
  :short "Name of the variable bound to the conclusion of a proof."
  (packn-pos (list (defind-proof-var-name name)
                   #\.
                   (defind-concl-field-name name))
             (symbol-lfix name)))

;;;;;;;;;;

(define defind-prem-proof-var-name ((num posp) (name symbolp))
  :returns (var-name symbolp)
  :short "Name of a premise proof variable."
  (packn-pos (list (defind-prem-var-name num name) '-proof)
             (symbol-lfix name)))

;;;;;;;;;;

(define defind-concl-formal-var-name ((formal symbolp) (name symbolp))
  :returns (var-name symbolp)
  :short "Name of the variable bound to a formal of
          a conclusion variable for an assertion."
  (packn-pos (list (defind-concl-var-name name)
                   #\.
                   (symbol-lfix formal))
             (symbol-lfix name)))

;;;;;;;;;;

(define defind-concl-formal-var-names ((formals symbol-listp) (name symbolp))
  :returns (var-names symbol-listp)
  :short "Name of all the variables bound to the formals of
          a conclusion variable for an assertion."
  (cond ((endp formals) nil)
        (t (cons (defind-concl-formal-var-name (car formals) name)
                 (defind-concl-formal-var-names (cdr formals) name)))))

;;;;;;;;;;;;;;;;;;;;

(define defind-proof-case-name ((pred-name symbolp) (name symbolp))
  :returns (case-name symbolp)
  :short "Name of the case macro of a @('p[i]-proof') fixtype."
  (packn-pos (list (defind-proof-type-name pred-name name) '-case)
             (symbol-lfix name)))

;;;;;;;;;;;;;;;;;;;;

(define defind-assert-acc-name ((pred-name symbolp)
                                (field-name symbolp)
                                (name symbolp))
  :returns (acc-name symbolp)
  :short "Name of the accessor of a field of a @('p[i]-assert') type."
  (packn-pos (list (defind-assert-type-name pred-name name)
                   '->
                   (symbol-lfix field-name))
             (symbol-lfix name)))

;;;;;;;;;;

(define defind-proof-prem-acc-name ((pred-name symbolp)
                                    (irule-name symbolp)
                                    (num posp)
                                    (name symbolp))
  :returns (acc-name symbolp)
  :short "Name of a premise accessor of a @('p[i]-proof') summand."
  (packn-pos (list (defind-proof-constr-name pred-name irule-name name)
                   '->
                   (defind-prem-field-name num name))
             (symbol-lfix name)))

;;;;;;;;;;

(define defind-proof-concl-acc-name ((pred-name symbolp)
                                     (irule-name symbolp)
                                     (name symbolp))
  :returns (acc-name symbolp)
  :short "Name of the conclusion accessor of a @('p[i]-proof') summand."
  (packn-pos (list (defind-proof-constr-name pred-name irule-name name)
                   '->conclusion)
             (symbol-lfix name)))

;;;;;;;;;;;;;;;;;;;;

(define defind-proof-count-fn-name ((pred-name symbolp) (name symbolp))
  :returns (fn-name symbolp)
  :short "Name of the count function of a @('p[i]-proof') fixtype."
  (packn-pos (list (defind-proof-type-name pred-name name) '-count)
             (symbol-lfix name)))

;;;;;;;;;;

(define defind-proof-concl-fn-name ((pred-name symbolp)
                                    (name symbolp))
  :returns (fn-name symbolp)
  :short "Name of a @('p[i]-proof->conclusion') function."
  (packn-pos (list (defind-proof-type-name pred-name name) '->conclusion)
             (symbol-lfix name)))

;;;;;;;;;;

(define defind-irule-valid-fn-name ((pred-name symbolp)
                                    (irule-name symbolp)
                                    (name symbolp))
  :returns (fn-name symbolp)
  :short "Name of a @('p[l[1]]-rule[1]-validp') function."
  (packn-pos (list (symbol-lfix pred-name)
                   '-
                   (symbol-lfix irule-name)
                   '-validp)
             (symbol-lfix name)))

;;;;;;;;;;

(define defind-irule-witness-fn-name ((pred-name symbolp)
                                      (irule-name symbolp)
                                      (name symbolp))
  :returns (fn-name symbolp)
  :short "Name of the witness function of
          a @('p[l[1]]-rule[1]-validp') function."
  (packn-pos (list (defind-irule-valid-fn-name pred-name irule-name name)
                   '-witness)
             (symbol-lfix name)))

;;;;;;;;;;

(define defind-proof-valid-fn-name ((pred-name symbolp) (name symbolp))
  :returns (fn-name symbolp)
  :short "Name of a @('p[i]-proof-validp')."
  (packn-pos (list (defind-proof-type-name pred-name name) '-validp)
             (symbol-lfix name)))

;;;;;;;;;;

(define defind-proof-witness-fn-name ((pred-name symbolp) (name symbolp))
  :returns (fn-name symbolp)
  :short "Name of the witness function for a @('p[i]') predicate."
  (packn-pos (list (symbol-lfix pred-name) '-proof) (symbol-lfix name)))

;;;;;;;;;;

(define defind-proof-for-rule-fn-name ((pred-name symbolp)
                                       (irule-name symbolp)
                                       (name symbolp))
  :returns (fn-name symbolp)
  :short "Name of a @('p[l[k]]-proof-for-rule[k]') function."
  (packn-pos (list (symbol-lfix pred-name)
                   '-proof-for-
                   (symbol-lfix irule-name))
             (symbol-lfix name)))

;;;;;;;;;;

(define defind-pred-alt-fn-name ((pred-name symbolp) (name symbolp))
  :returns (fn-name symbolp)
  :short "Name of a @('p[i]-alt') function name."
  (packn-pos (list (symbol-lfix pred-name) '-alt) (symbol-lfix name)))

;;;;;;;;;;

(define defind-pred-alt-irule-fn-name ((pred-name symbolp)
                                       (irule-name symbolp)
                                       (name symbolp))
  :returns (fn-name symbolp)
  :short "Name of the proposition (nullary function) saying that
          a @('p[i]-alt') stub satisfies an inference rule."
  (packn-pos (list (defind-pred-alt-fn-name pred-name name)
                   '-
                   (symbol-lfix irule-name)
                   '-p)
             (symbol-lfix name)))

;;;;;;;;;;;;;;;;;;;;

(define defind-equal-of-assert-thm-name ((pred-name symbolp) (name symbolp))
  :returns (thm-name symbolp)
  :short "Name of the equality decomposition theorem
          of a @('p[i]-assertion') fixtype."
  (packn-pos (list 'equal-of- (defind-assert-type-name pred-name name))
             (symbol-lfix name)))

;;;;;;;;;;

(define defind-assert-fix-id-thm-name ((pred-name symbolp) (name symbolp))
  :returns (thm-name symbolp)
  :short "Name of the theorem that rewrites away
          the fixer of @('p[i]-assertion') when the recognizer holds."
  (packn-pos (list (defind-assert-fixer-name pred-name name)
                   '-when-
                   (defind-assert-recog-name pred-name name))
             (symbol-lfix name)))

;;;;;;;;;;

(define defind-assert-fix-return-thm-name ((pred-name symbolp) (name symbolp))
  :returns (thm-name symbolp)
  :short "Name of the theorem saying that
          the fixer of a @('p[i]-assertion') type
          satisfies the recognizer of the type."
  (packn-pos (list (defind-assert-recog-name pred-name name)
                   '-of-
                   (defind-assert-fixer-name pred-name name))
             (symbol-lfix name)))

;;;;;;;;;;

(define defind-assert-constr-return-thm-name ((pred-name symbolp)
                                              (name symbolp))
  :returns (thm-name symbolp)
  :short "Name of the return theorem of
          the constructor of a @('p[i]-assert') fixtype."
  (packn-pos (list (defind-assert-recog-name pred-name name)
                   '-of-
                   (defind-assert-type-name pred-name name))
             (symbol-lfix name)))

;;;;;;;;;;

(define defind-assert-acc-of-constr-thm-names ((pred-name symbolp)
                                               (field-names symbol-listp)
                                               (name symbolp))
  :returns (thm-names symbol-listp)
  :short "Names of the theorems about the application of
          the accessors of a @('p[i]-assertion') fixtype
          to the constructor of the fixtype."
  (cond ((endp field-names) nil)
        (t (cons (packn-pos (list (defind-assert-acc-name
                                    pred-name (car field-names) name)
                                  '-of-
                                  (defind-assert-type-name pred-name name))
                            (symbol-lfix name))
                 (defind-assert-acc-of-constr-thm-names
                   pred-name (cdr field-names) name)))))

;;;;;;;;;;

(define defind-assert-fix-equiv-thm-name ((pred-name symbolp) (name symbolp))
  :returns (thm-name symbolp)
  :short "Name of the equivalence theorem stating the equivalence between
          a fixed and non-fixed @('p[i]-assertion') value."
  (packn-pos (list (defind-assert-fixer-name pred-name name)
                   '-under-
                   (defind-assert-equiv-name pred-name name))
             (symbol-lfix name)))

;;;;;;;;;;

(define defind-assert-acc-equiv-cong-thm-names ((pred-name symbolp)
                                                (field-names symbol-listp)
                                                (name symbolp))
  :returns (thm-names symbol-listp)
  :short "Names of the congruence theorems for
          the accessors of a @('p[i]-assertion') fixtype."
  (cond ((endp field-names) nil)
        (t (cons (packn-pos
                  (list
                   (defind-assert-acc-name pred-name (car field-names) name)
                   '$inline-
                   (defind-assert-equiv-name pred-name name)
                   '-congruence-on-
                   (defind-assert-var-name name))
                  (symbol-lfix name))
                 (defind-assert-acc-equiv-cong-thm-names
                   pred-name (cdr field-names) name)))))

;;;;;;;;;;

(define defind-proof-kind-poss-thm-name ((pred-name symbolp) (name symbolp))
  :returns (thm-name symbolp)
  :short "Name of the kind possibilities theorem for a @('p[i]-proof') fixtype."
  (packn-pos (list (defind-proof-type-name pred-name name) '-kind-possibilities)
             (symbol-lfix name)))

;;;;;;;;;;

(define defind-proof-kind-fixing-thm-name ((pred-name symbolp) (name symbolp))
  :returns (thm-name symbolp)
  :short "Name of the kind fixing theorem for a @('p[i]-proof') fixtype."
  (packn-pos (list (defind-proof-type-name pred-name name)
                   '-kind$inline-of-
                   (defind-proof-fixer-name pred-name name)
                   '-x)
             (symbol-lfix name)))

;;;;;;;;;;

(define defind-proof-constr-return-thm ((pred-name symbolp)
                                        (irule-name symbolp)
                                        (name symbolp))
  :returns (thm-name symbolp)
  :short "Name of the return theorem of
          the constructor of a @('p[i]-proof') fixtype."
  (packn-pos (list 'return-type-of-
                   (defind-proof-constr-name pred-name irule-name name))
             (symbol-lfix name)))

;;;;;;;;;;

(define defind-proof-concl-acc-return-thm-name ((pred-name symbolp)
                                                (irule-name symbolp)
                                                (name symbolp))
  :returns (thm-name symbolp)
  :short "Name of the return theorem of the conclusion accessor of
          a @('p[i]-proof') fixtype."
  (packn-pos (list (defind-assert-recog-name pred-name name)
                   '-of-
                   (defind-proof-concl-acc-name pred-name irule-name name))
             (symbol-lfix name)))

;;;;;;;;;;

(define defind-proof-concl-return-thm-name ((pred-name symbolp)
                                            (name symbolp))
  :returns (thm-name symbolp)
  :short "Name of the return theorem of a @('p[i]-proof->conclusion') function."
  (packn-pos (list (defind-assert-recog-name pred-name name)
                   '-of-
                   (defind-proof-concl-fn-name pred-name name))
             (symbol-lfix name)))

;;;;;;;;;;

(define defind-proof-concl-fixing-thm-name ((pred-name symbolp) (name symbolp))
  :returns (thm-name symbolp)
  :short "Name of the fixing theorem of a @('p[i]-proof->conclusion') function."
  (packn-pos (list (defind-proof-concl-fn-name pred-name name)
                   '-of-
                   (defind-proof-fixer-name pred-name name)
                   '-
                   (defind-proof-var-name name))
             (symbol-lfix name)))

;;;;;;;;;;

(define defind-proof-fix-equiv-thm-name ((pred-name symbolp) (name symbolp))
  :returns (thm-name symbolp)
  :short "Name of the equivalence theorem stating the equivalence between
          a fixed and non-fixed @('p[i]-proof') value."
  (packn-pos (list (defind-proof-fixer-name pred-name name)
                   '-under-
                   (defind-proof-equiv-name pred-name name))
             (symbol-lfix name)))

;;;;;;;;;;

(define defind-proof-prem-count-thm-name ((pred-name symbolp)
                                          (irule-name symbolp)
                                          (num posp)
                                          (name symbolp))
  :returns (thm-name symbolp)
  :short "Name of the count theorem of a premise accessor of
          a @('p[i]-proof') fixtype."
  (packn-pos (list (defind-proof-count-fn-name pred-name name)
                   '-of-
                   (defind-proof-prem-acc-name
                     pred-name irule-name num name))
             (symbol-lfix name)))

;;;;;;;;;;

(define defind-proof-prem-fixing-thm-name ((pred-name symbolp)
                                           (irule-name symbolp)
                                           (num posp)
                                           (name symbolp))
  :returns (thm-name symbolp)
  :short "Name of the fixing theorem of a premise accessor of
          a @('p[i]-proof') fixtype."
  (packn-pos (list (defind-proof-prem-acc-name pred-name irule-name num name)
                   '$inline-of-
                   (defind-proof-fixer-name pred-name name)
                   '-x)
             (symbol-lfix name)))

;;;;;;;;;;

(define defind-proof-concl-acc-fixing-thm-name ((pred-name symbolp)
                                                (irule-name symbolp)
                                                (name symbolp))
  :returns (thm-name symbolp)
  :short "Name of the fixing theorem of the conclusion accessor of
          a @('p[i]-proof') fixtype."
  (packn-pos (list (defind-proof-type-name pred-name name)
                   '-
                   (symbol-lfix irule-name)
                   '->
                   (defind-concl-field-name name)
                   '$inline-of-
                   (defind-proof-fixer-name pred-name name)
                   '-x)
             (symbol-lfix name)))

;;;;;;;;;;

(define defind-proof-concl-of-constr-thm-name ((pred-name symbolp)
                                               (irule-name symbolp)
                                               (name symbolp))
  :returns (thm-name symbolp)
  :short "Name of the theorem about the application of
          the conclusion accessor of a @('p[i]-proof') fixtype
          to the constructor of the fixtype."
  (packn-pos (list (defind-proof-concl-acc-name pred-name irule-name name)
                   '-of-
                   (defind-proof-constr-name pred-name irule-name name))
             (symbol-lfix name)))

;;;;;;;;;;

(define defind-proof-prem-of-constr-thm-name ((pred-name symbolp)
                                              (irule-name symbolp)
                                              (num posp)
                                              (name symbolp))
  :returns (thm-name symbolp)
  :short "Name of the theorem about the application of
          a premise accessor of a @('p[i]-proof') fixtype
          to a constructor of the fixtype."
  (packn-pos (list (defind-proof-prem-acc-name pred-name irule-name num name)
                   '-of-
                   (defind-proof-constr-name pred-name irule-name name))
             (symbol-lfix name)))

;;;;;;;;;;

(define defind-valid-congruence-thm-name ((pred-name symbolp) (name symbolp))
  :returns (thm-name symbolp)
  :short "Name of the congruence theorem for a @('p[i]-proof-validp') function."
  (packn-pos (list (defind-proof-valid-fn-name pred-name name)
                   '-
                   (defind-proof-type-name pred-name name)
                   '-equiv-congruence-on-
                   (defind-proof-var-name name))
             (symbol-lfix name)))

;;;;;;;;;;

(define defind-valid-proof-for-rule-thm-name ((pred-name symbolp)
                                              (irule-name symbolp)
                                              (name symbolp))
  :returns (thm-name symbolp)
  :short "Name of the theorem saying that
          a @('p[l[k]]-proof-for-rule[k]') function
          returns a valid proof."
  (packn-pos (list (defind-proof-valid-fn-name pred-name name)
                   '-of-
                   (defind-proof-for-rule-fn-name pred-name irule-name name))
             (symbol-lfix name)))

;;;;;;;;;;

(define defind-irule-valid-return-thm-name ((pred-name symbolp)
                                            (irule-name symbolp)
                                            (name symbolp))
  :returns (thm-name)
  :short "Name fo the return theorem of
          a @('p[l[k]]-proof-for-rule[k]') function."
  (packn-pos (list 'booleanp-of-
                   (defind-irule-valid-fn-name pred-name irule-name name))
             (symbol-lfix name)))

;;;;;;;;;;

(define defind-irule-valid-suff-thm-name ((pred-name symbolp)
                                          (irule-name symbolp)
                                          (name symbolp))
  :returns (thm-name symbolp)
  :short "Name of the sufficiency theorem associated to
          a @('p[l[k]]-proof-for-rule[k]') function."
  (packn-pos (list (defind-irule-valid-fn-name pred-name irule-name name)
                   '-suff)
             (symbol-lfix name)))

;;;;;;;;;;

(define defind-concl-proof-for-rule-thm-name ((pred-name symbolp)
                                              (irule-name symbolp)
                                              (name symbolp))
  :returns (thm-name symbolp)
  :short "Name of the theorem saying that
          the conclusion of a @('p[l[k]]-proof-for-rule[k]') function
          is the expected assertion."
  (packn-pos (list (defind-proof-concl-fn-name pred-name name)
                   '-of-
                   (defind-proof-for-rule-fn-name pred-name irule-name name))
             (symbol-lfix name)))

;;;;;;;;;;

(define defind-pred-irule-thm-name ((pred-name symbolp)
                                    (irule-name symbolp)
                                    (name symbolp))
  :returns (thm-name symbolp)
  :short "Name of the @('p[l[k]]-rule[k]') theorem."
  (packn-pos (list (symbol-lfix pred-name)
                   '-
                   (symbol-lfix irule-name))
             (symbol-lfix name)))

;;;;;;;;;;

(define defind-pred-suff-thm-name ((pred-name symbolp) (name symbolp))
  :returns (thm-name symbolp)
  :short "Name of the theorem associated to a @('p[i]') function."
  (packn-pos (list (symbol-lfix pred-name) '-suff) (symbol-lfix name)))

;;;;;;;;;;

(define defind-irule-proof-return-thm-name ((pred-name symbolp)
                                            (irule-name symbolp)
                                            (name symbolp))
  :returns (thm-name symbolp)
  :short "Name of the return theorem of
          a @('p[l[k]]-proof-for-rule[k]') function."
  (packn-pos (list (defind-proof-recog-name pred-name name)
                   '-of-
                   (defind-proof-for-rule-fn-name pred-name irule-name name))
             (symbol-lfix name)))

;;;;;;;;;;

(define defind-pred-alt-irule-thm-name ((pred-name symbolp)
                                        (irule-name symbolp)
                                        (name symbolp))
  :returns (thm-name symbolp)
  :short "Name of the necessity theorem associated to
          a @('p[l[k]]-alt-rule[k]-p') function."
  (packn-pos (list (defind-pred-alt-irule-fn-name pred-name irule-name name)
                   '-necc)
             (symbol-lfix name)))

;;;;;;;;;;

(define defind-pred-alt-when-proof-valid-thm-name ((pred-name symbolp)
                                                   (name symbolp))
  :returns (thm-name symbolp)
  :short "Name of a @('p[i]-alt-when-proof-validp') theorem."
  (packn-pos (list (defind-pred-alt-fn-name pred-name name)
                   '-when-
                   (defind-proof-valid-fn-name pred-name name))
             (symbol-lfix name)))

;;;;;;;;;;

(define defind-pred-alt-when-pred-thm-name ((pred-name symbolp) (name symbolp))
  :returns (thm-name symbolp)
  :short "Name of a @('p[i]-alt-when-p[i]') theorem."
  (packn-pos (list (defind-pred-alt-fn-name pred-name name)
                   '-when-
                   (symbol-lfix pred-name))
             (symbol-lfix name)))

;;;;;;;;;;;;;;;;;;;;

(define defind-irule-tag ((irule-name symbolp))
  :returns (tag symbolp)
  :short "Keyword tag for a @('rule[k]') rule name."
  (packn-pos (list (symbol-lfix irule-name)) :keyword))

;;;;;;;;;;;;;;;;;;;;

(define defind-rule-thm-section-name ((name symbolp))
  :returns (topic symbolp)
  :short "Name of the @(tsee defsection) containing
          the @('p[l[k]]-rule[k]') theorems."
  (packn-pos (list (symbol-lfix name) '-rules) (symbol-lfix name)))

;;;;;;;;;;

(define defind-minimality-section-name ((name symbolp))
  :returns (topic symbolp)
  :short "Name of the @(tsee defsection) containing
          the stubs, propositions, and theorems
          for the minimality of the predicates."
  (packn-pos (list (symbol-lfix name) '-minimal) (symbol-lfix name)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-name-defxdoc+ ((name symbolp)
                                  (parents symbol-listp)
                                  short
                                  long
                                  (xdocp booleanp))
  :returns (event pseudo-event-formp)
  :short "Generate the @(tsee defxdoc+) for @('name'),
          or an empty @(tsee progn) if no XDOC must be generated."
  (if xdocp
      `(defxdoc+ ,(symbol-lfix name)
         ,@(and (consp parents)
                (list :parents (symbol-list-fix parents)))
         ,@(and short
                (list :short short))
         ,@(and long
                (list :long long))
         :order-subtopics t
         :default-parent ,(symbol-lfix name))
    '(progn)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-assertion-defprod ((info defind-pred-infop)
                                      (name symbolp)
                                      (xdocp booleanp))
  :returns (defprod pseudo-event-formp)
  :short "Generate a @('p[i]-assertion') fixtype."
  :long
  (xdoc::topstring
   (xdoc::p
    "Since the parameters are currently untyped,
     we can just list them as field names in the fixtype definition.")
   (xdoc::p
    "We use the @(':xvar') option to avoid possible collisions with @('x'),
     which could be a commonly chosen name for a predicate formal.
     Although @('assertion') seems unlikely to clash,
     at some point we should pick an @(':xvar') name
     that we establish to be distinct from the formals
     (maybe even leaving @('x') as is if it is not a formal)."))
  (b* (((defind-pred-info info)))
    `(fty::defprod ,(defind-assert-type-name info.name name)
       ,@(and xdocp
              `(:parents (,(symbol-lfix name))
                :short ,(str::cat
                         "Fixtype of assertions for predicate @('"
                         (str::downcase-string (symbol-name info.name))
                         "').")))
       ,info.formals
       :xvar ,(defind-assert-var-name name)
       :pred ,(defind-assert-recog-name info.name name))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-assertion-defprods ((infos defind-pred-info-listp)
                                       (name symbolp)
                                       (xdocp booleanp))
  :guard (no-duplicatesp-equal (defind-pred-info-list->name infos))
  :returns (defprods pseudo-event-form-listp)
  :short "Generate the @('p[i]-assertion') fixtypes."
  (b* (((when (endp infos)) nil)
       (event (defind-gen-assertion-defprod (car infos) name xdocp))
       (events (defind-gen-assertion-defprods (cdr infos) name xdocp)))
    (cons event events)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-prem-fields ((infos defind-premise-info-listp)
                                (num posp)
                                (name symbolp))
  :returns (fields true-list-listp)
  :short "Generate the premise fields of
          a summand of a @('p[i]-proof') fixtype."
  :long
  (xdoc::topstring
   (xdoc::p
    "The summand corresponds to an inference rule,
     which has zero or more premises.
     The summand has one field for each premise of the @(':pred') kind:
     the field has the form @('(premise[num]-proof p[j]-proof)'),
     where @('p[j]') is the name of the predicate of the premise.
     The index @('num') is passed to this function,
     and incremented at each recursive call after a @(':pred') premise
     (unchanged after a @(':other') premise),
     initially 1.
     The @('p[j]-proof') fixtype is the one of the proofs for @('p[j]')."))
  (b* (((when (endp infos)) nil)
       (info (car infos))
       ((when (defind-premise-info-case info :other))
        (defind-gen-prem-fields (cdr infos) (lposfix num) name))
       (pred-name (defind-premise-info-pred->name info))
       (field-name (defind-prem-field-name num name))
       (field-type (defind-proof-type-name pred-name name))
       (field `(,field-name ,field-type))
       (fields (defind-gen-prem-fields (cdr infos) (1+ (lposfix num)) name)))
    (cons field fields)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-proof-summand ((info defind-irule-infop) (name symbolp))
  :returns (summand true-listp)
  :short "Generate a summand of a @('p[i]-proof') fixtype."
  :long
  (xdoc::topstring
   (xdoc::p
    "There is a summand for each inference rule
     whose conclusion is the predicate @('p[i]')
     associated to the proof fixtype in question.
     We only call this function with the information about
     the inference rules with the appropriate conclusions."))
  (b* (((defind-irule-info info))
       (tag (defind-irule-tag info.name))
       ((defind-conclusion-info info.conclusion))
       (concl-field `(,(defind-concl-field-name name)
                      ,(defind-assert-type-name info.conclusion.name name)))
       (prem-fields (defind-gen-prem-fields info.premises 1 name)))
    `(,tag (,concl-field ,@prem-fields))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-proof-summands ((pred-name symbolp)
                                   (infos defind-irule-info-listp)
                                   (name symbolp))
  :guard (no-duplicatesp-equal (defind-irule-info-list->name infos))
  :returns (summands true-list-listp)
  :short "Generate the summands of a @('p[i]-proof') fixtype."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are for the proof fixtype associated to
     the predicate whose name is specified by the @('pred-name') input.
     We generate a summand for exactly the rules
     whose conclusion matches that predicate,
     skipping the other rules."))
  (b* (((when (endp infos)) nil)
       ((defind-irule-info info) (car infos))
       ((defind-conclusion-info info.conclusion))
       ((unless (equal info.conclusion.name (symbol-lfix pred-name)))
        (defind-gen-proof-summands pred-name (cdr infos) name))
       (summand (defind-gen-proof-summand info name))
       (summands (defind-gen-proof-summands pred-name (cdr infos) name)))
    (cons summand summands)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-proof-deftagsum ((pred-name symbolp)
                                    (infos defind-irule-info-listp)
                                    (name symbolp)
                                    (xdocp booleanp))
  :guard (no-duplicatesp-equal (defind-irule-info-list->name infos))
  :returns (deftagsum pseudo-event-formp)
  :short "Generate a @('p[i]-proof') fixtype."
  :long
  (xdoc::topstring
   (xdoc::p
    "The predicate is specified by its name, passed as input."))
  (b* ((summands (defind-gen-proof-summands pred-name infos name)))
    `(fty::deftagsum ,(defind-proof-type-name pred-name name)
       ,@(and xdocp
              `(:parents (,(symbol-lfix name))
                :short ,(str::cat
                         "Fixtype of proofs for predicate @('"
                         (str::downcase-string (symbol-name pred-name))
                         "').")))
       ,@summands
       :pred ,(defind-proof-recog-name pred-name name)
       :prepwork ((set-induction-depth-limit 1)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-proof-deftagsums ((pred-infos defind-pred-info-listp)
                                     (irule-infos defind-irule-info-listp)
                                     (name symbolp)
                                     (xdocp booleanp))
  :guard (and (no-duplicatesp-equal (defind-pred-info-list->name pred-infos))
              (no-duplicatesp-equal (defind-irule-info-list->name irule-infos)))
  :returns (deftagsums pseudo-event-form-listp)
  :short "Generate the @('p[i]-proof') fixtypes."
  (b* (((when (endp pred-infos)) nil)
       (pred-name (defind-pred-info->name (car pred-infos)))
       (event (defind-gen-proof-deftagsum pred-name irule-infos name xdocp))
       (events (defind-gen-proof-deftagsums
                 (cdr pred-infos) irule-infos name xdocp)))
    (cons event events)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-proof-concl-fn-cases+rules ((pred-name symbolp)
                                               (infos defind-irule-info-listp)
                                               (name symbolp))
  :guard (no-duplicatesp-equal (defind-irule-info-list->name infos))
  :returns (mv (cases true-listp)
               (return-rules symbol-listp)
               (fixing-rules symbol-listp))
  :short "Generate the cases of a @('p[i]-proof->conclusion') function,
          and the rules used in the generated proofs for the function."
  :long
  (xdoc::topstring
   (xdoc::p
    "There is one case and one pair of rules for each summand of that fixtype,
     so some of this code is similar to @(tsee defind-gen-proof-summands).
     Each aforementioned pair of rules is put into a different list:
     one is for the return proof and one is for the fixing proof."))
  (b* (((when (endp infos)) (mv nil nil nil))
       ((defind-irule-info info) (car infos))
       ((defind-conclusion-info info.conclusion))
       ((unless (equal info.conclusion.name (symbol-lfix pred-name)))
        (defind-gen-proof-concl-fn-cases+rules pred-name (cdr infos) name))
       (case `(,(defind-irule-tag info.name)
               ,(defind-proof-concl-var-name name)))
       (return-rule
        (defind-proof-concl-acc-return-thm-name pred-name info.name name))
       (fixing-rule
        (defind-proof-concl-acc-fixing-thm-name pred-name info.name name))
       ((mv cases return-rules fixing-rules)
        (defind-gen-proof-concl-fn-cases+rules pred-name (cdr infos) name)))
    (mv (cons case cases)
        (cons return-rule return-rules)
        (cons fixing-rule fixing-rules))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-proof-concl-fn ((pred-name symbolp)
                                   (infos defind-irule-info-listp)
                                   (name symbolp)
                                   (xdocp booleanp))
  :guard (no-duplicatesp-equal (defind-irule-info-list->name infos))
  :returns (fn pseudo-event-formp)
  :short "Generate a @('p[i]-proof->conclusion') function."
  (b* ((fn-name (defind-proof-concl-fn-name pred-name name))
       (fn-formal (defind-proof-var-name name))
       (proof-recog (defind-proof-recog-name pred-name name))
       (fn-result (defind-concl-var-name name))
       (assert-recog (defind-assert-recog-name pred-name name))
       ((mv cases return-rules fixing-rules)
        (defind-gen-proof-concl-fn-cases+rules pred-name infos name))
       (poss-rule (defind-proof-kind-poss-thm-name pred-name name))
       (fixing-rule (defind-proof-kind-fixing-thm-name pred-name name)))
    `(define ,fn-name ((,fn-formal ,proof-recog))
       :returns (,fn-result ,assert-recog
                            :hints
                            (("Goal" :in-theory '(,fn-name ,@return-rules))))
       ,@(and xdocp
              `(:parents (,(symbol-lfix name))
                :short ,(str::cat "Conclusion of a proof for @('"
                                  (str::downcase-string (symbol-name pred-name))
                                  "').")))
       (,(defind-proof-case-name pred-name name)
        ,fn-formal
        ,@cases)
       :guard-hints (("Goal" :in-theory '(,poss-rule)))
       :hooks ((:fix :hints (("Goal" :in-theory '(,fn-name
                                                  ,fixing-rule
                                                  ,@fixing-rules))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-proof-concl-fns ((pred-infos defind-pred-info-listp)
                                    (irule-infos defind-irule-info-listp)
                                    (name symbolp)
                                    (xdocp booleanp))
  :guard (and (no-duplicatesp-equal (defind-pred-info-list->name pred-infos))
              (no-duplicatesp-equal (defind-irule-info-list->name irule-infos)))
  :returns (fns pseudo-event-form-listp)
  :short "Generate the @('p[i]-proof->conclusion') functions."
  (b* (((when (endp pred-infos)) nil)
       (pred-name (defind-pred-info->name (car pred-infos)))
       (event (defind-gen-proof-concl-fn pred-name irule-infos name xdocp))
       (events (defind-gen-proof-concl-fns
                 (cdr pred-infos) irule-infos name xdocp)))
    (cons event events)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-irule-fn-prems+formals ((infos defind-premise-info-listp)
                                           (num posp)
                                           (name symbolp))
  :returns (mv (conjunct true-listp) (formals true-listp))
  :short "Generate the conjuncts for the premises of an inference rule
          in a @('p[l[k]]-rule[k]-validp') function,
          along with the extended formals of the function for the premises."
  :long
  (xdoc::topstring
   (xdoc::p
    "If a premise is a call of a @('p[i]') predicate,
     we generate an equality between the premise and the call.
     Otherwise, we just generate the premise itself.")
   (xdoc::p
    "The @('num') input keep track of the number in
     the variable names used, i.e. @('prem1'), @('prem2'), etc."))
  (b* (((when (endp infos)) (mv nil nil))
       (info (car infos)))
    (defind-premise-info-case
      info
      :pred (b* ((recog (defind-assert-recog-name info.name name))
                 (fixer (defind-assert-fixer-name info.name name))
                 (constr (defind-assert-type-name info.name name))
                 (var (defind-prem-var-name num name))
                 (args (defind-term-info-list->uterm info.args))
                 (conjunct `(equal (,fixer ,var)
                                   (,constr ,@args)))
                 (formal `(,var ,recog))
                 ((mv conjuncts formals)
                  (defind-gen-irule-fn-prems+formals
                    (cdr infos) (1+ (lposfix num)) name)))
              (mv (cons conjunct conjuncts) (cons formal formals)))
      :other (b* ((conjunct (defind-term-info->uterm info.term))
                  ((mv conjuncts formals)
                   (defind-gen-irule-fn-prems+formals (cdr infos) num name)))
               (mv (cons conjunct conjuncts) formals)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-irule-valid-fn ((info defind-irule-infop)
                                   (name symbolp)
                                   (xdocp booleanp))
  :returns (event pseudo-event-formp)
  :short "Generate a @('p[l[k]]-rule[k]-validp') function."
  (b* (((defind-irule-info info))
       ((defind-conclusion-info info.conclusion))
       (fn-name (defind-irule-valid-fn-name info.conclusion.name info.name name))
       (concl-var (defind-concl-var-name name))
       (concl-recog (defind-assert-recog-name info.conclusion.name name))
       (concl-formal `(,concl-var ,concl-recog))
       (concl-fixer (defind-assert-fixer-name info.conclusion.name name))
       (concl-args (defind-term-info-list->uterm info.conclusion.args))
       (assert (defind-assert-type-name info.conclusion.name name))
       (concl-conjunct `(equal (,concl-fixer ,concl-var)
                               (,assert ,@concl-args)))
       ((mv prem-conjuncts prem-formals)
        (defind-gen-irule-fn-prems+formals info.premises 1 name))
       (vars (defind-irule-info-free-vars info))
       (body/matrix `(and ,@prem-conjuncts
                          ,concl-conjunct))
       (fix-id-thm (defind-assert-fix-id-thm-name info.conclusion.name name))
       (fix-return-thm
        (defind-assert-fix-return-thm-name info.conclusion.name name))
       (equal-thm (defind-equal-of-assert-thm-name info.conclusion.name name))
       (xdoc?
        (and xdocp
             `(:parents (,(symbol-lfix name))
               :short ,(str::cat "Validity of an instance of the rule @('"
                                 (str::downcase-string (symbol-name info.name))
                                 "').")))))
    (if (set::emptyp vars)
        `(define ,fn-name (,concl-formal ,@prem-formals)
           :returns (yes/no booleanp
                            :hints (("Goal" :in-theory '(,fn-name
                                                         booleanp))))
           ,@xdoc?
           ,body/matrix
           :verify-guards nil
           :hooks ((:fix :hints (("Goal" :in-theory '(,fn-name
                                                      ,fix-id-thm
                                                      ,fix-return-thm
                                                      ,equal-thm))))))
      `(define-sk ,fn-name (,concl-formal ,@prem-formals)
         :returns (yes/no booleanp
                          :hints (("Goal" :in-theory '(,fn-name
                                                       booleanp))))
         ,@xdoc?
         (exists ,vars ,body/matrix)
         :verify-guards nil
         ///
         (local (in-theory '(,fix-id-thm
                             ,fix-return-thm
                             ,equal-thm)))
         (fty::deffixequiv-sk ,fn-name
           :args (,concl-formal ,@prem-formals))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-irule-valid-fns ((infos defind-irule-info-listp)
                                    (name symbolp)
                                    (xdocp booleanp))
  :guard (no-duplicatesp-equal (defind-irule-info-list->name infos))
  :returns (events pseudo-event-form-listp)
  :short "Generate the @('p[l[k]]-rule[k]-validp') functions."
  (b* (((when (endp infos)) nil)
       (event (defind-gen-irule-valid-fn (car infos) name xdocp))
       (events (defind-gen-irule-valid-fns (cdr infos) name xdocp)))
    (cons event events)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-proof-valid-fn-case-prems ((infos defind-premise-info-listp)
                                              (irule-name symbolp)
                                              (num posp)
                                              (name symbolp))
  :returns (mv (conjuncts true-listp)
               (concl-calls true-listp)
               (count-thms symbol-listp)
               (fixing-thms symbol-listp))
  :short "Generate the conjuncts for the proofs of the premises
          of an inference rule in a case of a @('p[i]-proof-validp') function,
          along with calls of the conclusion functions on those proofs,
          and along with the names of some relevant theorems."
  (b* (((when (endp infos)) (mv nil nil nil nil))
       (info (car infos)))
    (defind-premise-info-case
      info
      :pred (b* ((valid-fn (defind-proof-valid-fn-name info.name name))
                 (concl-fn (defind-proof-concl-fn-name info.name name))
                 (prem-proof-var (defind-proof-prem-var-name num name))
                 (conjunct `(,valid-fn ,prem-proof-var))
                 (concl-call `(,concl-fn ,prem-proof-var))
                 (count-thm (defind-proof-prem-count-thm-name
                              info.name irule-name num name))
                 (fixing-thm (defind-proof-prem-fixing-thm-name
                               info.name irule-name num name))
                 ((mv conjuncts concl-calls count-thms fixing-thms)
                  (defind-gen-proof-valid-fn-case-prems
                    (cdr infos) irule-name (1+ (lposfix num)) name)))
              (mv (cons conjunct conjuncts)
                  (cons concl-call concl-calls)
                  (cons count-thm count-thms)
                  (cons fixing-thm fixing-thms)))
      :other (defind-gen-proof-valid-fn-case-prems
               (cdr infos) irule-name num name))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-proof-valid-fn-case ((pred-name symbolp)
                                        (infos defind-premise-info-listp)
                                        (irule-name symbolp)
                                        (name symbolp))
  :returns (mv (keyword+term true-listp)
               (return-thm symbolp)
               (count-thms symbol-listp)
               (fixing-thms symbol-listp))
  :short "Generate a case of a @('p[i]-proof-validp') function,
          along with the names of some relevant theorems."
  (b* ((tag (defind-irule-tag irule-name))
       (valid-irule-fn (defind-irule-valid-fn-name pred-name irule-name name))
       ((mv prem-conjuncts
            concl-calls
            count-thms
            fixing-thms)
        (defind-gen-proof-valid-fn-case-prems infos irule-name 1 name))
       (concl-var (defind-proof-concl-var-name name))
       (return-thm
        (defind-irule-valid-return-thm-name pred-name irule-name name)))
    (mv `(,tag (and ,@prem-conjuncts
                    (,valid-irule-fn ,concl-var
                                     ,@concl-calls)))
        return-thm
        count-thms
        fixing-thms)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-proof-valid-fn-cases ((pred-name symbolp)
                                         (infos defind-irule-info-listp)
                                         (name symbolp))
  :guard (no-duplicatesp-equal (defind-irule-info-list->name infos))
  :returns (mv (keywords+terms true-listp)
               (return-thms symbol-listp)
               (count-thms symbol-listp)
               (prem-fixing-thms symbol-listp)
               (concl-fixing-thms symbol-listp))
  :short "Generate the cases of a @('p[i]-proof-validp') function,
          along with the names of some relevant theorems."
  :long
  (xdoc::topstring
   (xdoc::p
    "There is one case for each rule whose conclusion is @('p[i]')."))
  (b* (((when (endp infos)) (mv nil nil nil nil nil))
       ((defind-irule-info info) (car infos))
       ((unless (equal (defind-conclusion-info->name info.conclusion)
                       (symbol-lfix pred-name)))
        (defind-gen-proof-valid-fn-cases pred-name (cdr infos) name))
       ((mv keyword+term return-thm count-thms prem-fixing-thms)
        (defind-gen-proof-valid-fn-case pred-name info.premises info.name name))
       (concl-fixing-thm
        (defind-proof-concl-acc-fixing-thm-name pred-name info.name name))
       ((mv keywords+terms
            more-return-thms
            more-count-thms
            more-prem-fixing-thms
            more-concl-fixing-thms)
        (defind-gen-proof-valid-fn-cases pred-name (cdr infos) name)))
    (mv (cons keyword+term keywords+terms)
        (cons return-thm more-return-thms)
        (append count-thms more-count-thms)
        (append prem-fixing-thms more-prem-fixing-thms)
        (cons concl-fixing-thm more-concl-fixing-thms))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-proof-valid-fn ((pred-name symbolp)
                                   (infos defind-irule-info-listp)
                                   (name symbolp)
                                   (xdocp booleanp))
  :guard (no-duplicatesp-equal (defind-irule-info-list->name infos))
  :returns (event pseudo-event-formp)
  :short "Generate a @('p[i]-proof-validp') function."
  :long
  (xdoc::topstring
   (xdoc::p
    "This assumes that there is a single @('p[i]'),
     as documented as an initial restriction in @(tsee definductive).
     So we generate termination hints as part of this function,
     as well as fixing theorems and hints for this function.
     Once we generalize to multiple @('p[i]') predicates,
     this has to become part of a @(tsee defines),
     and some of these hints, and the fixing, must go under there."))
  (b* ((fn-name (defind-proof-valid-fn-name pred-name name))
       (fn-formal (defind-proof-var-name name))
       (proof-recog (defind-proof-recog-name pred-name name))
       (proof-case (defind-proof-case-name pred-name name))
       ((mv keywords+terms
            return-thms
            count-thms
            prem-fixing-thms
            concl-fixing-thms)
        (defind-gen-proof-valid-fn-cases pred-name infos name))
       (count-fn (defind-proof-count-fn-name pred-name name))
       (poss-thm (defind-proof-kind-poss-thm-name pred-name name))
       (kind-fixing-thm (defind-proof-kind-fixing-thm-name pred-name name)))
    `(define ,fn-name ((,fn-formal ,proof-recog))
       :returns (yes/no booleanp
                        :hints (("Goal" :in-theory '(,fn-name
                                                     ,@return-thms))))
       ,@(and xdocp
              `(:parents (,(symbol-lfix name))
                :short ,(str::cat "Validity of a proof for @('"
                                  (str::downcase-string (symbol-name pred-name))
                                  "').")))
       (,proof-case ,fn-formal ,@keywords+terms)
       :measure (,count-fn ,fn-formal)
       :hints (("Goal" :in-theory '(o-p
                                    o-finp
                                    o<
                                    (:t ,count-fn)
                                    (:e tau-system)
                                    ,poss-thm
                                    ,@count-thms)))
       :verify-guards nil
       :hooks ((:fix :hints (("Goal" :in-theory '(,fn-name
                                                  ,kind-fixing-thm
                                                  ,@prem-fixing-thms
                                                  ,@concl-fixing-thms))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-proof-valid-fns ((pred-infos defind-pred-info-listp)
                                    (irule-infos defind-irule-info-listp)
                                    (name symbolp)
                                    (xdocp booleanp))
  :guard (and (no-duplicatesp-equal (defind-pred-info-list->name pred-infos))
              (no-duplicatesp-equal (defind-irule-info-list->name irule-infos)))
  :returns (events pseudo-event-form-listp)
  :short "Generate all the @('p[i]-proof-validp') functions."
  (cond ((endp pred-infos) nil)
        (t (cons (defind-gen-proof-valid-fn
                   (defind-pred-info->name (car pred-infos))
                   irule-infos
                   name
                   xdocp)
                 (defind-gen-proof-valid-fns
                   (cdr pred-infos) irule-infos name xdocp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-pred ((pred-info defind-pred-infop)
                         (name symbolp)
                         (xdocp booleanp))
  :returns (event pseudo-event-formp)
  :short "Generate a @('p[i]') predicate."
  (b* (((defind-pred-info pred-info))
       (proof (defind-proof-var-name name))
       (proofp (defind-proof-recog-name pred-info.name name))
       (proof-validp (defind-proof-valid-fn-name pred-info.name name))
       (proof->concl (defind-proof-concl-fn-name pred-info.name name))
       (assert (defind-assert-type-name pred-info.name name))
       (witness (defind-proof-witness-fn-name pred-info.name name)))
    `(define-sk ,pred-info.name (,@pred-info.formals)
       :returns (yes/no booleanp
                        :hints (("Goal" :in-theory '(,pred-info.name
                                                     booleanp))))
       ,@(and xdocp
              `(:parents (,(symbol-lfix name))
                :short ,(str::cat "Definition of the predicate @('"
                                  (str::downcase-string
                                   (symbol-name pred-info.name))
                                  "') via proof existence.")))
       (exists (,proof)
               (and (,proofp ,proof)
                    (,proof-validp ,proof)
                    (equal (,proof->concl ,proof)
                           (,assert ,@pred-info.formals))))
       :skolem-name ,witness
       :verify-guards nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-preds ((pred-infos defind-pred-info-listp)
                          (name symbolp)
                          (xdocp booleanp))
  :returns (events pseudo-event-form-listp)
  :short "Generate all the @('p[i]') predicates."
  (cond ((endp pred-infos) nil)
        (t (cons (defind-gen-pred (car pred-infos) name xdocp)
                 (defind-gen-preds (cdr pred-infos) name xdocp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-irule-proof-fn ((info defind-irule-infop)
                                   (pred-infos defind-pred-info-listp)
                                   (name symbolp)
                                   (xdocp booleanp))
  :guard (no-duplicatesp-equal (defind-pred-info-list->name pred-infos))
  :returns (event pseudo-event-formp)
  :short "Generate a @('p[l[k]]-proof-for-rule[k]') function."
  (b* (((defind-irule-info info))
       ((defind-conclusion-info cinfo) info.conclusion)
       (fn-name (defind-proof-for-rule-fn-name cinfo.name info.name name))
       (concl-vars (defind-conclusion-info-free-vars cinfo))
       ((mv subproof-vars
            subproof-formals
            subproof-hyps
            subproof-eqs
            prem-insts
            prem-of-constr-thms
            other-prems)
        (defind-gen-irule-proof-fn-loop info.name info.premises 1 name))
       (proof-var (defind-proof-var-name name))
       (proof-recog (defind-proof-recog-name cinfo.name name))
       (proof-return (defind-proof-constr-return-thm cinfo.name info.name name))
       (proof-constr (defind-proof-constr-name cinfo.name info.name name))
       (assert (defind-assert-type-name cinfo.name name))
       (concl-args (defind-term-info-list->uterm cinfo.args))
       (proof-valid-fn (defind-proof-valid-fn-name cinfo.name name))
       (valid-thm
        (defind-valid-proof-for-rule-thm-name cinfo.name info.name name))
       (suff/def-thm
        (if (set::emptyp (defind-irule-info-free-vars info))
            (defind-irule-valid-fn-name cinfo.name info.name name)
          (defind-irule-valid-suff-thm-name cinfo.name info.name name)))
       (concl (defind-concl-var-name name))
       (cong-thm (defind-valid-congruence-thm-name cinfo.name name))
       (fix-id-thm (defind-assert-fix-id-thm-name cinfo.name name))
       (assert-return-thm
        (defind-assert-constr-return-thm-name cinfo.name name))
       (concl-fix-thm (defind-proof-concl-fixing-thm-name cinfo.name name))
       (proof-fix-equiv-thm (defind-proof-fix-equiv-thm-name cinfo.name name))
       (concl-of-constr-thm
        (defind-proof-concl-of-constr-thm-name cinfo.name info.name name))
       (pred-info (defind-lookup-pred cinfo.name pred-infos))
       (concl-thm
        (defind-concl-proof-for-rule-thm-name cinfo.name info.name name))
       (concl-fn (defind-proof-concl-fn-name cinfo.name name))
       ((unless pred-info)
        (raise "Internal error: predicate ~x0 not found." cinfo.name)
        '(_))
       (pred-formals (defind-pred-info->formals pred-info))
       (cong-thms (defind-assert-acc-equiv-cong-thm-names
                    cinfo.name pred-formals name))
       (equal-thm (defind-equal-of-assert-thm-name cinfo.name name))
       (assert-acc-constr-thms
        (defind-assert-acc-of-constr-thm-names cinfo.name pred-formals name))
       (assert-fix-equiv-thm (defind-assert-fix-equiv-thm-name cinfo.name name))
       (concl-return-thm (defind-proof-concl-return-thm-name cinfo.name name))
       (fix-return-thm (defind-assert-fix-return-thm-name cinfo.name name)))
    `(define ,fn-name (,@concl-vars ,@subproof-formals)
       :returns (,proof-var ,proof-recog
                            :hints (("Goal" :in-theory '(,fn-name
                                                         ,proof-return))))
       ,@(and xdocp
              `(:parents (,(symbol-lfix name))
                :short ,(str::cat "Proof of @('"
                                  (str::downcase-string
                                   (symbol-name cinfo.name))
                                  "') rooted at rule @('"
                                  (str::downcase-string
                                   (symbol-name info.name))
                                  "').")))
       (,proof-constr (,assert ,@concl-args) ,@subproof-vars)
       :verify-guards nil
       ///
       (defret ,valid-thm
         (,proof-valid-fn ,proof-var)
         :hyp (and ,@subproof-hyps
                   ,@other-prems
                   ,@subproof-eqs)
         :hints (("Goal"
                  :use (:instance ,suff/def-thm
                                  (,concl (,assert ,@concl-args))
                                  ,@prem-insts)
                  :in-theory '(,cong-thm
                               ,fn-name
                               ,proof-valid-fn
                               ,fix-id-thm
                               ,assert-return-thm
                               ,concl-fix-thm
                               ,proof-fix-equiv-thm
                               ,concl-of-constr-thm
                               ,@prem-of-constr-thms
                               ,proof-return))))
       (defret ,concl-thm
         (equal (,concl-fn ,proof-var)
                (,assert ,@concl-args))
         :hints (("Goal" :in-theory '(,@cong-thms
                                      ,concl-fn
                                      ,fn-name
                                      ,equal-thm
                                      ,@assert-acc-constr-thms
                                      ,assert-fix-equiv-thm
                                      ,concl-return-thm
                                      ,concl-of-constr-thm
                                      ,proof-return
                                      ,fix-return-thm))))
       (in-theory (disable ,valid-thm
                           ,concl-thm))))
  :no-function nil
  :guard-hints (("Goal" :in-theory (enable set::sets-are-true-lists)))
  :prepwork
  ((define defind-gen-irule-proof-fn-loop ((irule-name symbolp)
                                           (infos defind-premise-info-listp)
                                           (num posp)
                                           (name symbolp))
     :returns (mv (subproof-vars symbol-listp)
                  (subproof-formals true-listp)
                  (subproof-hyps true-listp)
                  (subproof-eqs true-listp)
                  (prem-insts true-listp)
                  (prem-thms symbol-listp)
                  (other-prems true-listp))
     :parents nil
     (b* (((when (endp infos)) (mv nil nil nil nil nil nil nil))
          (info (car infos)))
       (defind-premise-info-case
         info
         :pred (b* ((subproof-var (defind-prem-proof-var-name num name))
                    (proof-recog (defind-proof-recog-name info.name name))
                    (subproof-formal `(,subproof-var ,proof-recog))
                    (proof-valid (defind-proof-valid-fn-name info.name name))
                    (subproof-hyp `(,proof-valid ,subproof-var))
                    (proof-concl (defind-proof-concl-fn-name info.name name))
                    (assert (defind-assert-type-name info.name name))
                    (args (defind-term-info-list->uterm info.args))
                    (subproof-eq `(equal (,proof-concl ,subproof-var)
                                         (,assert ,@args)))
                    (prem-var (defind-prem-var-name num name))
                    (prem-inst `(,prem-var (,assert ,@args)))
                    (prem-thm (defind-proof-prem-of-constr-thm-name
                                info.name irule-name num name))
                    ((mv subproof-vars
                         subproof-formals
                         subproof-hyps
                         subproof-eqs
                         prem-insts
                         prem-thms
                         other-prems)
                     (defind-gen-irule-proof-fn-loop
                       irule-name (cdr infos) (1+ (lposfix num)) name)))
                 (mv (cons subproof-var subproof-vars)
                     (cons subproof-formal subproof-formals)
                     (cons subproof-hyp subproof-hyps)
                     (cons subproof-eq subproof-eqs)
                     (cons prem-inst prem-insts)
                     (cons prem-thm prem-thms)
                     other-prems))
         :other (b* (((mv subproof-vars
                          subproof-formals
                          subproof-hyps
                          subproof-eqs
                          prem-insts
                          prem-thms
                          other-prems)
                      (defind-gen-irule-proof-fn-loop
                        irule-name (cdr infos) num name)))
                  (mv subproof-vars
                      subproof-formals
                      subproof-hyps
                      subproof-eqs
                      prem-insts
                      prem-thms
                      (cons (defind-term-info->uterm info.term)
                            other-prems))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-irule-proof-fns ((irule-infos defind-irule-info-listp)
                                    (pred-infos defind-pred-info-listp)
                                    (name symbolp)
                                    (xdocp booleanp))
  :guard (and (no-duplicatesp-equal (defind-irule-info-list->name irule-infos))
              (no-duplicatesp-equal (defind-pred-info-list->name pred-infos)))
  :returns (events pseudo-event-form-listp)
  :short "Generate all the @('p[l[k]]-proof-for-rule[k]') functions."
  (cond ((endp irule-infos) nil)
        (t (cons (defind-gen-irule-proof-fn
                   (car irule-infos) pred-infos name xdocp)
                 (defind-gen-irule-proof-fns
                   (cdr irule-infos) pred-infos name xdocp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-irule-thm-hyps ((infos defind-premise-info-listp))
  :returns (mv (pred-hyps true-listp)
               (other-hyps true-listp))
  :short "Generate the hypotheses of a @('p[l[k]]-rule[k]') theorem."
  :long
  (xdoc::topstring
   (xdoc::p
    "We separate the hypotheses according to the two kinds of premises."))
  (b* (((when (endp infos)) (mv nil nil))
       (info (car infos))
       ((mv pred-hyps other-hyps) (defind-gen-irule-thm-hyps (cdr infos))))
    (defind-premise-info-case
      info
      :pred (mv (cons `(,info.name ,@(defind-term-info-list->uterm info.args))
                      pred-hyps)
                other-hyps)
      :other (mv pred-hyps
                 (cons (defind-term-info->uterm info.term)
                       other-hyps)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-irule-thm ((info defind-irule-infop)
                              (infos defind-pred-info-listp)
                              (name symbolp))
  :guard (no-duplicatesp-equal (defind-pred-info-list->name infos))
  :returns (event pseudo-event-formp)
  :short "Generate a @('p[l[k]]-rule[k]') theorem."
  (b* (((defind-irule-info info))
       ((defind-conclusion-info cinfo) info.conclusion)
       (concl-args (defind-term-info-list->uterm cinfo.args))
       (concl `(,cinfo.name ,@concl-args))
       ((mv pred-hyps other-hyps) (defind-gen-irule-thm-hyps info.premises))
       (thm-name (defind-pred-irule-thm-name cinfo.name info.name name))
       (pred-suff (defind-pred-suff-thm-name cinfo.name name))
       ((mv witcalls prem-vars)
        (defind-gen-irule-thm-loop info.premises 1 name))
       (prooffn (defind-proof-for-rule-fn-name cinfo.name info.name name))
       (concl-vars (defind-conclusion-info-free-vars cinfo))
       (proofcall `(,prooffn ,@concl-vars ,@witcalls))
       (pinfo (defind-lookup-pred cinfo.name infos))
       ((unless pinfo)
        (raise "Internal error: predicate ~x0 not found." cinfo.name)
        '(_))
       (formals (defind-pred-info->formals pinfo))
       (formals-inst (alist-to-doublets (pairlis$ formals concl-args)))
       (proof-var (defind-proof-var-name name))
       (valid-thm
        (defind-valid-proof-for-rule-thm-name cinfo.name info.name name))
       (valid-thm-inst (alist-to-doublets (pairlis$ prem-vars witcalls)))
       (concl-thm
        (defind-concl-proof-for-rule-thm-name cinfo.name info.name name))
       (return-thm
        (defind-irule-proof-return-thm-name cinfo.name info.name name)))
    `(defruled ,thm-name
       (implies (and ,@pred-hyps ,@other-hyps) ,concl)
       ,@(and pred-hyps
              (list :expand pred-hyps))
       :use ((:instance ,pred-suff
                        (,proof-var ,proofcall)
                        ,@formals-inst)
             (:instance ,valid-thm
                        ,@valid-thm-inst))
       :in-theory '(,concl-thm
                    ,return-thm)))
  :no-function nil
  :guard-hints (("Goal" :in-theory (enable set::sets-are-true-lists)))
  :prepwork
  ((define defind-gen-irule-thm-loop ((infos defind-premise-info-listp)
                                      (num posp)
                                      (name symbolp))
     :returns (mv (witcalls true-listp)
                  (prem-vars symbol-listp))
     :parents nil
     (b* (((when (endp infos)) (mv nil nil))
          (info (car infos)))
       (defind-premise-info-case
         info
         :pred (b* ((witfn (defind-proof-witness-fn-name info.name name))
                    (witcall
                     `(,witfn ,@(defind-term-info-list->uterm info.args)))
                    (prem-var (defind-prem-proof-var-name num name))
                    ((mv witcalls prem-vars)
                     (defind-gen-irule-thm-loop
                       (cdr infos) (1+ (lposfix num)) name)))
                 (mv (cons witcall witcalls)
                     (cons prem-var prem-vars)))
         :other (defind-gen-irule-thm-loop (cdr infos) num name))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-irule-thms ((irule-infos defind-irule-info-listp)
                               (pred-infos defind-pred-info-listp)
                               (name symbolp))
  :guard (and (no-duplicatesp-equal (defind-pred-info-list->name pred-infos))
              (no-duplicatesp-equal (defind-irule-info-list->name irule-infos)))
  :returns (events pseudo-event-form-listp)
  :short "Generate all the @('p[l[k]]-rule[k]') theorems."
  (cond ((endp irule-infos) nil)
        (t (cons (defind-gen-irule-thm (car irule-infos) pred-infos name)
                 (defind-gen-irule-thms (cdr irule-infos) pred-infos name)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-irule-defsection ((irule-infos defind-irule-info-listp)
                                     (pred-infos defind-pred-info-listp)
                                     (name symbolp)
                                     (xdocp booleanp))
  :guard (and (no-duplicatesp-equal (defind-pred-info-list->name pred-infos))
              (no-duplicatesp-equal (defind-irule-info-list->name irule-infos)))
  :returns (event pseudo-event-formp)
  :short "Generate a @(tsee defsection) or @(tsee progn) with
          all the @('p[l[k]]-rule[k]') theorems,
          depending on whether XDOC is to be generated."
  (b* ((thms (defind-gen-irule-thms irule-infos pred-infos name)))
    (if xdocp
        `(defsection ,(defind-rule-thm-section-name name)
           :short "Theorems corresponding to the inference rules."
           ,@thms)
      `(progn ,@thms))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-pred-alt-stubs ((infos defind-pred-info-listp)
                                   (name symbolp))
  :guard (no-duplicatesp-equal (defind-pred-info-list->name infos))
  :returns (events pseudo-event-form-listp)
  :short "Generate the @('p[i]-alt') stubs."
  (b* (((when (endp infos)) nil)
       ((defind-pred-info info) (car infos))
       (fn-name (defind-pred-alt-fn-name info.name name))
       (stub `(defstub ,fn-name ,(repeat (len info.formals) '*) => *))
       (stubs (defind-gen-pred-alt-stubs (cdr infos) name)))
    (cons stub stubs)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-pred-alt-irule-prop-prems ((infos defind-premise-info-listp)
                                              (name symbolp))
  :returns (prems true-listp)
  :short "Premises of the proposition (nullary function) saying that
          a @('p[i]-alt') stub satisfies an inference rule."
  (b* (((when (endp infos)) nil)
       (prems (defind-gen-pred-alt-irule-prop-prems (cdr infos) name))
       (info (car infos)))
    (defind-premise-info-case
      info
      :pred (cons `(,(defind-pred-alt-fn-name info.name name)
                    ,@(defind-term-info-list->uterm info.args))
                  prems)
      :other (cons (defind-term-info->uterm info.term)
                   prems))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-pred-alt-irule-prop ((info defind-irule-infop)
                                        (name symbolp))
  :returns (mv (event pseudo-event-formp)
               call)
  :short "Proposition (nullary function) saying that
          a @('p[i]-alt') stub satisfies an inference rule."
  :long
  (xdoc::topstring
   (xdoc::p
    "We also return a term that is the call of the function."))
  (b* (((defind-irule-info info))
       ((defind-conclusion-info cinfo) info.conclusion)
       (fn-name (defind-pred-alt-irule-fn-name cinfo.name info.name name))
       (prems (defind-gen-pred-alt-irule-prop-prems info.premises name))
       (concl `(,(defind-pred-alt-fn-name cinfo.name name)
                ,@(defind-term-info-list->uterm cinfo.args)))
       (vars (defind-irule-info-free-vars info))
       (event (if (set::emptyp vars)
                  `(defun ,fn-name ()
                     (declare (xargs :verify-guards nil))
                     (implies (and ,@prems) ,concl))
                `(defun-sk ,fn-name ()
                   (declare (xargs :verify-guards nil))
                   (forall ,vars (implies (and ,@prems) ,concl)))))
       (call `(,fn-name)))
    (mv event call)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-pred-alt-irule-props ((infos defind-irule-info-listp)
                                         (name symbolp))
  :guard (no-duplicatesp-equal (defind-irule-info-list->name infos))
  :returns (mv (events pseudo-event-form-listp)
               (calls true-listp))
  :short "Propositions (nullary functions) saying that
          the @('p[i]-alt') stubs satisfy the inference rules."
  :long
  (xdoc::topstring
   (xdoc::p
    "We also return the list of terms that are the calls of these functions."))
  (b* (((when (endp infos)) (mv nil nil))
       ((mv event call) (defind-gen-pred-alt-irule-prop (car infos) name))
       ((mv events calls) (defind-gen-pred-alt-irule-props (cdr infos) name)))
    (mv (cons event events) (cons call calls))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-irule-witness-call ((info defind-irule-infop) (name symbolp))
  :returns call
  :short "Rule validity witness call for the hints of
          a @('p[1]-alt-when-proof-validp') theroem."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the witness function called on
     the conclusion of the proof and
     on the conclusions of the premise proofs."))
  (b* (((defind-irule-info info))
       ((defind-conclusion-info cinfo) info.conclusion)
       (proof (defind-proof-var-name name))
       (concl-acc (defind-proof-concl-acc-name cinfo.name info.name name))
       (concl-arg `(,concl-acc ,proof))
       (prem-args (defind-gen-irule-witness-call-loop
                    info.premises cinfo.name info.name 1 name))
       (wit (defind-irule-witness-fn-name cinfo.name info.name name)))
    `(,wit ,concl-arg ,@prem-args))
  :prepwork
  ((define defind-gen-irule-witness-call-loop ((infos defind-premise-info-listp)
                                               (pred-name symbolp)
                                               (irule-name symbolp)
                                               (num posp)
                                               (name symbolp))
     :returns (args true-listp)
     :parents nil
     (b* (((when (endp infos)) nil)
          (info (car infos)))
       (defind-premise-info-case
         info
         :pred
         (b* ((acc (defind-proof-prem-acc-name pred-name irule-name num name))
              (concl-fn (defind-proof-concl-fn-name info.name name))
              (proof (defind-proof-var-name name))
              (arg `(,concl-fn (,acc ,proof))))
           (cons arg
                 (defind-gen-irule-witness-call-loop
                   (cdr infos) pred-name irule-name (1+ (lposfix num)) name)))
         :other (defind-gen-irule-witness-call-loop
                  (cdr infos) pred-name irule-name num name))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-irule-mv-nth-doublets ((vars symbol-setp)
                                          (num natp)
                                          (witcall "A term."))
  :returns (doublets doublet-listp)
  :short "Doublets of a lemma instance for the hints of
          a @('p[1]-alt-when-proof-validp') theroem."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used when there are two or more free variables in the rule,
     which are associated with different @(tsee mv-nth) components."))
  (cond ((set::emptyp (symbol-sfix vars)) nil)
        (t (cons `(,(set::head vars) (mv-nth ,(lnfix num) ,witcall))
                 (defind-gen-irule-mv-nth-doublets
                   (set::tail vars) (1+ (lnfix num)) witcall))))
  :prepwork ((local (in-theory (enable symbol-sfix doublet-listp length len)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-pred-alt-when-proof-valid-thm
  ((pred-name symbolp)
   (pred-formals symbol-listp)
   (irule-infos defind-irule-info-listp)
   (prop-calls true-listp)
   (name symbolp))
  :guard (no-duplicatesp-equal (defind-irule-info-list->name irule-infos))
  :returns (event pseudo-event-formp)
  :short "Generate a @('p[i]-alt-when-proof-validp') theorem."
  :long
  (xdoc::topstring
   (xdoc::p
    "For now we generate a single theorem,
     because we only support one predicate,
     as stated in @(tsee definductive).
     So all the hints go here."))
  (b* ((thm-name (defind-pred-alt-when-proof-valid-thm-name pred-name name))
       (valid-fn (defind-proof-valid-fn-name pred-name name))
       (proof (defind-proof-var-name name))
       (assert (defind-assert-type-name pred-name name))
       (concl (defind-concl-var-name name))
       (concl-fn (defind-proof-concl-fn-name pred-name name))
       (pred-alt (defind-pred-alt-fn-name pred-name name))
       (concls (defind-concl-formal-var-names pred-formals name))
       ((mv irule-valid-fns irule-concl-accs lemma-instances)
        (defind-gen-pred-alt-when-proof-valid-thm-loop irule-infos name))
       (poss-thm (defind-proof-kind-poss-thm-name pred-name name))
       (equal-thm (defind-equal-of-assert-thm-name pred-name name))
       (fix-thm (defind-assert-fix-id-thm-name pred-name name)))
    `(defruled ,thm-name
       (implies (and ,@prop-calls
                     (,valid-fn ,proof))
                (b* (((,assert ,concl) (,concl-fn ,proof)))
                  (,pred-alt ,@concls)))
       :induct t
       :in-theory '(,valid-fn
                    ,@irule-valid-fns
                    ,concl-fn
                    ,poss-thm
                    ,equal-thm
                    ,fix-thm
                    ,@irule-concl-accs)
       :hints ('(:use ,lemma-instances))))
  :prepwork
  ((define defind-gen-pred-alt-when-proof-valid-thm-loop
     ((infos defind-irule-info-listp)
      (name symbolp))
     :guard (no-duplicatesp-equal (defind-irule-info-list->name infos))
     :returns (mv (irule-valid-fns symbol-listp)
                  (irule-acc-thms symbol-listp)
                  (lemma-instances true-listp))
     :parents nil
     (b* (((when (endp infos)) (mv nil nil nil))
          ((defind-irule-info info) (car infos))
          ((defind-conclusion-info cinfo) info.conclusion)
          (irule-valid-fn (defind-irule-valid-fn-name cinfo.name info.name name))
          (irule-acc-thm
           (defind-proof-concl-acc-return-thm-name cinfo.name info.name name))
          (necc/def-rule
           (if (set::emptyp (defind-irule-info-free-vars info))
               (defind-pred-alt-irule-fn-name cinfo.name info.name name)
             (defind-pred-alt-irule-thm-name cinfo.name info.name name)))
          (vars (defind-irule-info-free-vars info))
          (witcall (defind-gen-irule-witness-call info name))
          (inst-doublets (if (= (set::cardinality vars) 1)
                             (list `(,(set::head vars) ,witcall))
                           (defind-gen-irule-mv-nth-doublets vars 0 witcall)))
          (lemma-instance `(:instance ,necc/def-rule ,@inst-doublets))
          ((mv irule-valid-fns irule-acc-thms lemma-instances)
           (defind-gen-pred-alt-when-proof-valid-thm-loop (cdr infos) name)))
       (mv (cons irule-valid-fn irule-valid-fns)
           (cons irule-acc-thm irule-acc-thms)
           (cons lemma-instance lemma-instances)))
     :guard-hints (("Goal" :in-theory (enable set::cardinality))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-pred-alt-when-proof-valid-thms
  ((pred-infos defind-pred-info-listp)
   (irule-infos defind-irule-info-listp)
   (prop-calls true-listp)
   (name symbolp))
  :guard (and (no-duplicatesp-equal (defind-pred-info-list->name pred-infos))
              (no-duplicatesp-equal (defind-irule-info-list->name irule-infos)))
  :returns (events pseudo-event-form-listp)
  :short "Generate all the @('p[i]-alt-when-proof-validp') theorems."
  (b* (((when (endp pred-infos)) nil)
       ((defind-pred-info info) (car pred-infos))
       (thm (defind-gen-pred-alt-when-proof-valid-thm
              info.name info.formals irule-infos prop-calls name))
       (thms (defind-gen-pred-alt-when-proof-valid-thms
               (cdr pred-infos) irule-infos prop-calls name)))
    (cons thm thms)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-pred-alt-when-pred-thm ((pred-name symbolp)
                                           (pred-formals symbol-listp)
                                           (prop-calls true-listp)
                                           (name symbolp))
  :returns (event pseudo-event-formp)
  :short "Generate a @('p[i]-alt-when-p[i]') theorem."
  (b* ((thm-name (defind-pred-alt-when-pred-thm-name pred-name name))
       (pred-alt (defind-pred-alt-fn-name pred-name name))
       (equal-thm (defind-equal-of-assert-thm-name pred-name name))
       (valid-thm (defind-pred-alt-when-proof-valid-thm-name pred-name name))
       (proof-var (defind-proof-var-name name))
       (proof-wit (defind-proof-witness-fn-name pred-name name)))
    `(defruled ,thm-name
       (implies (and ,@prop-calls
                     (,(symbol-lfix pred-name)
                      ,@(symbol-list-fix pred-formals)))
                (,pred-alt ,@(symbol-list-fix pred-formals)))
       :in-theory '(,(symbol-lfix pred-name) ,equal-thm)
       :use (:instance ,valid-thm
                       (,proof-var
                        (,proof-wit ,@(symbol-list-fix pred-formals)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-pred-alt-when-pred-thms ((pred-infos defind-pred-info-listp)
                                            (prop-calls true-listp)
                                            (name symbolp))
  :guard (no-duplicatesp-equal (defind-pred-info-list->name pred-infos))
  :returns (events pseudo-event-form-listp)
  :short "Generate all the @('p[i]-alt-when-p[i]') theorems."
  (b* (((when (endp pred-infos)) nil)
       ((defind-pred-info info) (car pred-infos))
       (thm (defind-gen-pred-alt-when-pred-thm
              info.name info.formals prop-calls name))
       (thms (defind-gen-pred-alt-when-pred-thms
               (cdr pred-infos) prop-calls name)))
    (cons thm thms)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-minimality-defsection ((pred-infos defind-pred-info-listp)
                                          (irule-infos defind-irule-info-listp)
                                          (name symbolp)
                                          (xdocp booleanp))
  :guard (and (no-duplicatesp-equal (defind-pred-info-list->name pred-infos))
              (no-duplicatesp-equal (defind-irule-info-list->name irule-infos)))
  :returns (event pseudo-event-formp)
  :short "Generate a @(tsee defsection) or @(tsee progn) with
          all the @('p[i]-alt') stubs,
          all the @('p[l[k]]-alt-rule[k]-p') propositions,
          all the @('p[i]-alt-when-proof-validp') theorems,
          and all the @('p[i]-alt-when-p[i]') theorems."
  (b* ((stubs (defind-gen-pred-alt-stubs pred-infos name))
       ((mv props prop-calls)
        (defind-gen-pred-alt-irule-props irule-infos name))
       (valid-thms (defind-gen-pred-alt-when-proof-valid-thms
                     pred-infos irule-infos prop-calls name))
       (min-thms
        (defind-gen-pred-alt-when-pred-thms pred-infos prop-calls name))
       (events (append stubs props valid-thms min-thms)))
    (if xdocp
        `(defsection ,(defind-minimality-section-name name)
           :short "Minimality of the predicates."
           ,@events)
      `(progn ,@events)))
  :guard-hints
  (("Goal"
    :in-theory (enable true-listp-when-pseudo-event-form-listp-rewrite))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-events ((name symbolp)
                           (pred-infos defind-pred-info-listp)
                           (irule-infos defind-irule-info-listp)
                           (parents symbol-listp)
                           short
                           long
                           (xdocp booleanp))
  :guard (and (no-duplicatesp-equal (defind-pred-info-list->name pred-infos))
              (no-duplicatesp-equal (defind-irule-info-list->name irule-infos)))
  :returns (event pseudo-event-formp)
  :short "Generate all the events."
  :long
  (xdoc::topstring
   (xdoc::p
    "The events are wrapped into an @(tsee encapsulate)."))
  (b* ((name-doc-event
        (defind-gen-name-defxdoc+ name parents short long xdocp))
       (assert-type-events
        (defind-gen-assertion-defprods pred-infos name xdocp))
       (proof-type-events
        (defind-gen-proof-deftagsums pred-infos irule-infos name xdocp))
       (proof-concl-events
        (defind-gen-proof-concl-fns pred-infos irule-infos name xdocp))
       (irule-valid-events
        (defind-gen-irule-valid-fns irule-infos name xdocp))
       (proof-valid-events
        (defind-gen-proof-valid-fns pred-infos irule-infos name xdocp))
       (pred-events
        (defind-gen-preds pred-infos name xdocp))
       (proof-for-rule-events
        (defind-gen-irule-proof-fns irule-infos pred-infos name xdocp))
       (irules-event
        (defind-gen-irule-defsection irule-infos pred-infos name xdocp))
       (minimality-event
        (defind-gen-minimality-defsection pred-infos irule-infos name xdocp))
       (all-events (append (list name-doc-event)
                           assert-type-events
                           proof-type-events
                           proof-concl-events
                           irule-valid-events
                           proof-valid-events
                           pred-events
                           proof-for-rule-events
                           (list irules-event)
                           (list minimality-event))))
    `(encapsulate
       ()
       ,@all-events
       (value-triple :invisible))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-process-inputs-and-gen-events (name
                                              preds
                                              (preds-suppliedp booleanp)
                                              irules
                                              (irules-suppliedp booleanp)
                                              parents
                                              (parents-suppliedp booleanp)
                                              short
                                              (short-suppliedp booleanp)
                                              long
                                              (long-suppliedp booleanp)
                                              state)
  :returns (mv erp (event pseudo-event-formp))
  :parents (definductive-implementation)
  :short "Process the inputs and generate all the events."
  (b* (((reterr) '(_))
       ((erp name pred-infos irule-infos parents short long xdocp)
        (defind-process-inputs
          name
          preds preds-suppliedp
          irules irules-suppliedp
          parents parents-suppliedp
          short short-suppliedp
          long long-suppliedp
          state))
       (event (defind-gen-events
                name pred-infos irule-infos parents short long xdocp)))
    (retok event)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define definductive-fn (name
                         preds
                         (preds-suppliedp booleanp)
                         irules
                         (irules-suppliedp booleanp)
                         parents
                         (parents-suppliedp booleanp)
                         short
                         (short-suppliedp booleanp)
                         long
                         (long-suppliedp booleanp)
                         (ctx ctxp)
                         state)
  :returns (mv erp
               (event pseudo-event-formp)
               state)
  :parents (definductive-implementation)
  :short "Event expansion of @(tsee definductive) from the inputs."
  (b* (((mv erp event)
        (defind-process-inputs-and-gen-events
          name
          preds preds-suppliedp
          irules irules-suppliedp
          parents parents-suppliedp
          short short-suppliedp
          long long-suppliedp
          state))
       ((when erp) (er-soft+ ctx t '(_) "~@0" erp)))
    (value event)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection definductive-definition
  :parents (definductive-implementation)
  :short "Definition of the @(tsee definductive) macro."
  (defmacro definductive (name
                          &key
                          (preds 'nil preds-suppliedp)
                          (irules 'nil irules-suppliedp)
                          (parents 'nil parents-suppliedp)
                          (short 'nil short-suppliedp)
                          (long 'nil long-suppliedp))
    `(make-event
      (definductive-fn
        ',name
        ',preds
        ',preds-suppliedp
        ',irules
        ',irules-suppliedp
        ',parents
        ',parents-suppliedp
        ',short
        ',short-suppliedp
        ',long
        ',long-suppliedp
        (cons 'definductive ',name)
        state))))
