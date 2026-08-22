; Standard Utilities Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "centaur/fty/top" :dir :system)
(include-book "clause-processors/pseudo-term-fty" :dir :system)
(include-book "kestrel/event-macros/cw-event" :dir :system)
(include-book "kestrel/event-macros/make-event-terse" :dir :system)
(include-book "kestrel/event-macros/restore-output" :dir :system)
(include-book "kestrel/event-macros/screen-printing" :dir :system)
(include-book "kestrel/fty/deffixequiv-sk" :dir :system)
(include-book "kestrel/fty/set-list" :dir :system)
(include-book "kestrel/fty/symbol-set" :dir :system)
(include-book "kestrel/fty/symbol-set-list" :dir :system)
(include-book "kestrel/fty/symbol-set-list-list" :dir :system)
(include-book "kestrel/fty/symbol-set-set" :dir :system)
(include-book "kestrel/utilities/er-soft-plus" :dir :system)
(include-book "kestrel/utilities/legal-variable-listp" :dir :system)
(include-book "kestrel/utilities/messages" :dir :system)
(include-book "std/basic/symbol-lfix" :dir :system)
(include-book "std/basic/two-nats-measure" :dir :system)
(include-book "std/system/check-user-term-dollar" :dir :system)
(include-book "std/system/fresh-namep" :dir :system)
(include-book "std/util/define-sk" :dir :system)
(include-book "std/util/defirrelevant" :dir :system)
(include-book "std/util/defprojection" :dir :system)
(include-book "std/util/error-value-tuples" :dir :system)
(include-book "system/pseudo-event-form-listp" :dir :system)

(local (include-book "kestrel/lists-light/no-duplicatesp-equal" :dir :system))
(local (include-book "kestrel/utilities/msgp" :dir :system))
(local (include-book "kestrel/utilities/ordinals" :dir :system))
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

(local (in-theory (enable true-listp-when-pseudo-event-form-listp-rewrite)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Library extensions.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Variant of CONSP-UNDER-IFF-WHEN-TRUE-LISTP
; in [books]/std/lists/true-listp.lisp.

(defruled consp-under-iff-when-true-listp-no-backchain-limit
  (implies (true-listp x)
           (iff (consp x) x)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; If X is within a universe U,
; and adding X to D actually adds something
; (i.e. their union is not already a subset of D),
; then the "gap" U minus D strictly shrinks in cardinality.
; The strictness witness is the head of (difference (union d x) d),
; which is in X (hence in U) but not in D.

(defruledl gap-cardinality-decreases
  (implies (and (set::subset x u)
                (not (set::subset (set::union d x) d)))
           (< (set::cardinality (set::difference u (set::union d x)))
              (set::cardinality (set::difference u d))))
  :hints
  (("Goal"
    :in-theory (acl2::enable* set::expensive-rules)
    :use ((:instance set::proper-subset-cardinality
                     (set::x (set::difference u (set::union d x)))
                     (set::y (set::difference u d)))
          (:instance set::in-head
                     (set::x (set::difference (set::union d x) d)))
          (:instance set::subset-in
                     (set::a (set::head (set::difference (set::union d x) d)))
                     (set::x x)
                     (set::y u))
          (:instance set::subset-in
                     (set::a (set::head (set::difference (set::union d x) d)))
                     (set::x (set::difference u d))
                     (set::y (set::difference u (set::union d x))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Removing from a set U a non-empty subset X of it
; strictly shrinks the cardinality.
; The strictness witness is the head of X,
; which is in U but not in (DIFFERENCE U X).

(defruledl difference-cardinality-decreases
  (implies (and (set::subset x u)
                (not (set::emptyp x)))
           (< (set::cardinality (set::difference u x))
              (set::cardinality u)))
  :hints
  (("Goal"
    :in-theory (acl2::enable* set::expensive-rules)
    :use ((:instance set::proper-subset-cardinality
                     (set::x (set::difference u x))
                     (set::y u))
          (:instance set::in-head
                     (set::x x))
          (:instance set::subset-in
                     (set::a (set::head x))
                     (set::x x)
                     (set::y u))
          (:instance set::subset-in
                     (set::a (set::head x))
                     (set::x u)
                     (set::y (set::difference u x)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; A set of sets of symbols is also a list of sets of symbols.

(defruledl symbol-set-listp-when-symbol-set-setp
  (implies (symbol-set-setp x)
           (symbol-set-listp x))
  :induct t
  :enable (symbol-set-setp symbol-set-listp))

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

  (xdoc::evmac-topic-implementation-item-input "print")

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
     (i) a @('p[i]') predicate applied to
     some terms not containing the predicates being defined,
     or (ii) some term not containing the predicates being defined."))
  (:pred ((name symbol)
          (args defind-term-info-list)))
  (:other ((term defind-term-info)))
  :pred defind-premise-infop)

;;;;;;;;;;;;;;;;;;;;

(fty::deflist defind-premise-info-list
  :short "Fixtype of lists of information about premises of a rule."
  :elt-type defind-premise-info
  :true-listp t
  :elementp-of-nil nil
  :pred defind-premise-info-listp)

;;;;;;;;;;

(defirrelevant irr-defind-premise-info
  :short "Irrelevant information about premises of a rule."
  :type defind-premise-infop
  :body (defind-premise-info-pred nil nil))

;;;;;;;;;;

(std::deflist defind-premise-info-list-case-pred (x)
  :guard (defind-premise-info-listp x)
  :short "Check if all the elements of
          a list of information about premises of a rule
          are of the @(':pred') kind."
  (defind-premise-info-case x :pred))

;;;;;;;;;;

(std::deflist defind-premise-info-list-case-other (x)
  :guard (defind-premise-info-listp x)
  :short "Check if all the elements of
          a list of information about premises of a rule
          are of the @(':other') kind."
  (defind-premise-info-case x :other))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod defind-conclusion-info
  :short "Fixtype of information about a conclusion of a rule."
  :long
  (xdoc::topstring
   (xdoc::p
    "Conclusions always have the form of
     a @('p[i]') predicate applied to
     some terms not containing the predicates being defined.
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

(define defind-irule-info-recursivep ((info defind-irule-infop))
  :returns (yes/no booleanp)
  :short "Check if a rule is recursive."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the case when at least one premise is a @(':pred'),
     i.e. when not all are @(':other') premises.")
   (xdoc::p
    "See @(tsee defind-pred-recursivep)
     for the related notion of recursive predicate."))
  (not (defind-premise-info-list-case-other
         (defind-irule-info->premises info))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-pred-names-unambp ((infos defind-pred-info-listp))
  :returns (yes/no booleanp)
  :short "Check if the names of the given predicates are unambiguous."
  :long
  (xdoc::topstring
   (xdoc::p
    "That is, check if the names are all distinct."))
  (no-duplicatesp-equal (defind-pred-info-list->name infos))

  ///

  (defrule defind-pred-names-unambp-of-cdr
    (implies (defind-pred-names-unambp infos)
             (defind-pred-names-unambp (cdr infos)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-lookup-pred ((pred-name symbolp) (infos defind-pred-info-listp))
  :guard (defind-pred-names-unambp infos)
  :returns (info? defind-pred-info-optionp)
  :short "Look up the information about the predicate."
  :long
  (xdoc::topstring
   (xdoc::p
    "The first match is returned,
     but the names in the list are unambiguous (see guard),
     so if there is a match it is the only one."))
  (b* (((when (endp infos)) nil)
       ((defind-pred-info info) (car infos))
       ((when (eq (symbol-lfix pred-name) info.name))
        (defind-pred-info-fix info)))
    (defind-lookup-pred pred-name (cdr infos))))

;;;;;;;;;;;;;;;;;;;;

(define defind-lookup-pred-set ((preds symbol-setp)
                                (infos defind-pred-info-listp))
  :returns (selected-infos defind-pred-info-listp)
  :short "Look up the information about the predicates in a given set."
  :long
  (xdoc::topstring
   (xdoc::p
    "This lifts @(tsee defind-lookup-pred) to a set of predicates:
     we return the information for the predicates in the set,
     in the same order in which the information appears
     in the input list."))
  (b* (((when (endp infos)) nil)
       (info (defind-pred-info-fix (car infos)))
       (infos (defind-lookup-pred-set preds (cdr infos))))
    (if (set::in (defind-pred-info->name info) (symbol-sfix preds))
        (cons info infos)
      infos))

  ///

  (defret subsetp-equal-of-names-of-defind-lookup-pred-set
    (subsetp-equal (defind-pred-info-list->name selected-infos)
                   (defind-pred-info-list->name infos))
    :hints (("Goal" :induct t)))

  (defret defind-pred-names-unambp-of-defind-lookup-pred-set
    (implies (defind-pred-names-unambp infos)
             (defind-pred-names-unambp selected-infos))
    :hints (("Goal"
             :induct t
             :in-theory (enable defind-pred-names-unambp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-irules-of-pred ((pred-name symbolp)
                               (infos defind-irule-info-listp))
  :returns (selected-infos defind-irule-info-listp)
  :short "Inference rules whose conclusion is a given predicate."
  :long
  (xdoc::topstring
   (xdoc::p
    "The rules are returned in the same order in which
     they appear in the input list."))
  (b* (((when (endp infos)) nil)
       (info (defind-irule-info-fix (car infos)))
       (infos (defind-irules-of-pred pred-name (cdr infos))))
    (if (equal (defind-conclusion-info->name
                 (defind-irule-info->conclusion info))
               (symbol-lfix pred-name))
        (cons info infos)
      infos))

  ///

  (defret subsetp-equal-of-names-of-defind-irules-of-pred
    (subsetp-equal (defind-irule-info-list->name selected-infos)
                   (defind-irule-info-list->name infos))
    :hints (("Goal" :induct t)))

  (defret defind-irules-of-pred-of-defind-irules-of-pred
    (equal (defind-irules-of-pred pred-name selected-infos)
           selected-infos)
    :hints (("Goal" :induct t))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-irule-name-clash ((infos defind-irule-info-listp))
  :returns (mv (foundp booleanp)
               (irule-name symbolp)
               (pred-name symbolp))
  :short "Find the first clash among the names of the given inference rules."
  :long
  (xdoc::topstring
   (xdoc::p
    "A clash consists of two rules
     with the same name and the same conclusion predicate.
     If there is a clash, we return @('t') as the first result,
     along with the rule name and the predicate name.
     If there is no clash, we return @('nil') as all the results."))
  (b* (((when (endp infos)) (mv nil nil nil))
       ((defind-irule-info info) (car infos))
       (pred-name (defind-conclusion-info->name info.conclusion))
       (same-concl-infos (defind-irules-of-pred pred-name (cdr infos)))
       ((when (member-eq info.name
                         (defind-irule-info-list->name same-concl-infos)))
        (mv t info.name pred-name)))
    (defind-irule-name-clash (cdr infos)))

  ///

  (defrule defind-irule-name-clash-of-cdr
    (implies (not (mv-nth 0 (defind-irule-name-clash infos)))
             (not (mv-nth 0 (defind-irule-name-clash (cdr infos)))))
    :induct t)

  (defrule defind-irule-name-clash-of-defind-irules-of-pred
    (implies (not (mv-nth 0 (defind-irule-name-clash infos)))
             (not (mv-nth 0 (defind-irule-name-clash
                             (defind-irules-of-pred pred-name infos)))))
    :induct t
    :enable defind-irules-of-pred))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-irule-names-unambp ((infos defind-irule-info-listp))
  :returns (yes/no booleanp)
  :short "Check if the names of the given inference rules are unambiguous."
  :long
  (xdoc::topstring
   (xdoc::p
    "That is, check if the rules with the same conclusion predicate
     have distinct names, i.e. if there is no clash.
     Rules with different conclusion predicates may have the same name,
     because the names of the generated events
     that relate to rules incorporate the predicate names."))
  (b* (((mv foundp & &) (defind-irule-name-clash infos)))
    (not foundp))

  ///

  (defrule defind-irule-names-unambp-of-cdr
    (implies (defind-irule-names-unambp infos)
             (defind-irule-names-unambp (cdr infos))))

  (defrule defind-irule-names-unambp-of-defind-irules-of-pred
    (implies (defind-irule-names-unambp infos)
             (defind-irule-names-unambp
              (defind-irules-of-pred pred-name infos)))))

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-preds-in-premises ((infos defind-premise-info-listp))
  :returns (preds symbol-setp)
  :short "Predicates in the premises of a rule."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the names in the premises of the @(':pred') kind,
     i.e. the premises that contain predicates being defined;
     the premises of the @(':other') kind
     contain no predicate being defined."))
  (b* (((when (endp infos)) nil)
       (preds (defind-preds-in-premises (cdr infos)))
       (info (car infos)))
    (defind-premise-info-case
      info
      :pred (set::insert info.name preds)
      :other preds))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;

(define defind-preds-in-premises-of-irules
  ((irule-infos defind-irule-info-listp))
  :returns (preds symbol-setp)
  :short "Predicates in the premises of the given rules."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is @(tsee defind-preds-in-premises)
     unioned over all the given rules."))
  (b* (((when (endp irule-infos)) nil)
       ((defind-irule-info info) (car irule-infos)))
    (set::union (defind-preds-in-premises info.premises)
                (defind-preds-in-premises-of-irules (cdr irule-infos))))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;

(define defind-preds-direct-dependencies ((preds symbol-setp)
                                          (irule-infos defind-irule-info-listp))
  :returns (deps symbol-setp)
  :short "Predicates on which given predicates directly depend."
  :long
  (xdoc::topstring
   (xdoc::p
    "A predicate @('p[i]') directly depends on a predicate @('p[j]') when
     some rule has @('p[i]') in its conclusion and @('p[j]') in some premise.
     This function returns the set of all the predicates
     on which any of the predicates in @('preds') directly depends:
     it goes through the rules,
     and collects the predicates in the premises of
     the rules whose conclusion predicate is in @('preds').")
   (xdoc::p
    "This function operates on a set of predicates,
     instead of a single predicate,
     so that @(tsee defind-pred-dependencies) can use this function
     to extend a whole set of predicates with
     the direct dependencies of all its elements at once.")
   (xdoc::p
    "The direct dependencies of any set of predicates are always
     among the predicates in the premises of the rules
     (see @(tsee defind-preds-in-premises-of-irules)),
     as expressed by the theorem below."))
  (b* (((when (endp irule-infos)) nil)
       (deps (defind-preds-direct-dependencies preds (cdr irule-infos)))
       ((defind-irule-info info) (car irule-infos)))
    (if (set::in (defind-conclusion-info->name info.conclusion)
                 (symbol-sfix preds))
        (set::union (defind-preds-in-premises info.premises) deps)
      deps))
  :verify-guards :after-returns

  ///

  (defruled defind-direct-dependencies-subset-preds-in-premises
    (set::subset (defind-preds-direct-dependencies preds irule-infos)
                 (defind-preds-in-premises-of-irules irule-infos))
    :induct (defind-preds-in-premises-of-irules irule-infos)
    :enable (defind-preds-direct-dependencies
             defind-preds-in-premises-of-irules
             set::subset-transitive
             set::pick-a-point-subset-strategy
             set::subset-in)))

;;;;;;;;;;;;;;;;;;;;

(define defind-pred-dependencies ((pred-name symbolp)
                                  (irule-infos defind-irule-info-listp))
  :returns (deps symbol-setp)
  :short "Predicates on which a given predicate depends,
          directly or indirectly."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the transitive closure of
     the direct dependency relation on the given predicate
     (see @(tsee defind-preds-direct-dependencies)):
     starting with the direct dependencies of the predicate,
     we repeatedly add the direct dependencies of the set,
     until nothing new is added.")
   (xdoc::p
    "Since the closure is transitive but not reflexive,
     the predicate is not automatically among its own dependencies:
     it is among them if and only if it is recursive,
     i.e. if it depends on itself,
     directly or through other predicates.
     This is exactly how @(tsee defind-pred-recursivep) is defined.")
   (xdoc::p
    "The iteration terminates because the set of dependencies grows
     within the fixed universe of
     all the predicates in the premises of the rules
     (see @(tsee defind-preds-in-premises-of-irules)):
     each round that does not stop
     adds at least one predicate to the dependencies,
     so the ``gap'' between that universe and the dependencies,
     measured by its cardinality, strictly decreases.
     We use the fact that the direct dependencies are within that universe
     (see @('defind-direct-dependencies-subset-preds-in-premises'))."))
  (defind-pred-dependencies-loop
    (defind-preds-direct-dependencies
      (set::insert (symbol-lfix pred-name) nil)
      irule-infos)
    irule-infos)

  :prepwork
  ((define defind-pred-dependencies-loop ((deps symbol-setp)
                                          (irule-infos defind-irule-info-listp))
     :returns (final-deps symbol-setp)
     :parents nil
     (b* ((deps (symbol-sfix deps))
          (new-deps (set::union deps
                                (defind-preds-direct-dependencies
                                  deps irule-infos)))
          ((when (set::subset new-deps deps)) deps))
       (defind-pred-dependencies-loop new-deps irule-infos))
     :measure (set::cardinality
               (set::difference
                (defind-preds-in-premises-of-irules irule-infos)
                (symbol-sfix deps)))
     ;; GAP-CARDINALITY-DECREASES rewrites the measure decrease;
     ;; its hypothesis is relieved by
     ;; DEFIND-DIRECT-DEPENDENCIES-SUBSET-PREDS-IN-PREMISES.
     ;; UNION-EMPTYP-X and DIFFERENCE-EMPTYP-Y are disabled so that
     ;; the (union d x) and (difference u d) patterns that the former matches
     ;; survive the degenerate case where DEPS is the empty set.
     :hints
     (("Goal"
       :in-theory (e/d (symbol-sfix
                        gap-cardinality-decreases
                        defind-direct-dependencies-subset-preds-in-premises)
                       (set::expand-cardinality-of-difference
                        set::union-emptyp-x
                        set::difference-emptyp-y)))))))

;;;;;;;;;;;;;;;;;;;;

(define defind-pred-recursivep ((pred-name symbolp)
                                (irule-infos defind-irule-info-listp))
  :returns (yes/no booleanp)
  :short "Check if a predicate is recursive."
  :long
  (xdoc::topstring
   (xdoc::p
    "That is, check if the predicate depends on itself,
     directly or indirectly through other predicates being defined,
     i.e. check if the predicate is among its own dependencies
     (see @(tsee defind-pred-dependencies)).")
   (xdoc::p
    "Note the difference with @(tsee defind-irule-info-recursivep),
     which checks whether a single rule is recursive.
     When a single predicate is being defined,
     the predicate is recursive if and only if some rule is recursive.
     With multiple predicates, the relation is less direct:
     a predicate is recursive if and only if
     it is on a cycle of the direct dependency relation,
     each arc of which comes from a recursive rule."))
  (set::in (symbol-lfix pred-name)
           (defind-pred-dependencies pred-name irule-infos)))

;;;;;;;;;;;;;;;;;;;;

(define defind-preds-without-irules ((pred-names symbol-listp)
                                     (irule-infos defind-irule-info-listp))
  :returns (ruleless-preds symbol-listp)
  :short "List of the predicates that are not
          in the conclusion of any rule."
  :long
  (xdoc::topstring
   (xdoc::p
    "We go through the predicates being defined,
     and we collect the ones for which there is no rule
     (see @(tsee defind-irules-of-pred)),
     in the same order, which is convenient for error messages.
     Every predicate is in the conclusion of some rule exactly when
     the result is empty."))
  (b* (((when (endp pred-names)) nil)
       (ruleless-preds
        (defind-preds-without-irules (cdr pred-names) irule-infos))
       (pred-name (car pred-names))
       ((when (consp (defind-irules-of-pred pred-name irule-infos)))
        ruleless-preds))
    (cons (symbol-lfix pred-name) ruleless-preds)))

;;;;;;;;;;;;;;;;;;;;

(define defind-pred-clique ((pred-name symbolp)
                            (irule-infos defind-irule-info-listp))
  :returns (clique symbol-setp)
  :short "Clique of a predicate."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the set consisting of the predicate @('pred-name') itself,
     plus the predicates @('p[i]') such that
     the predicate @('pred-name') depends on @('p[i]')
     and @('p[i]') depends on @('pred-name'),
     directly or indirectly
     (see @(tsee defind-pred-dependencies)).
     We calculate it by going through the dependencies of the predicate,
     retaining the ones whose dependencies include the predicate,
     and adding the predicate itself;
     so the clique is never empty.")
   (xdoc::p
    "If the predicate is recursive,
     it is among its own dependencies,
     because mutual dependency with itself is just recursion;
     so it would be in the clique
     even without explicitly adding it.
     If instead the predicate is not recursive,
     it has no mutual dependency with any other predicate,
     because that would compose into
     a dependency of the predicate on itself;
     so the clique is the singleton of the predicate.
     In graph terminology, the cliques are
     the strongly connected components of the dependency graph,
     where a non-recursive predicate
     (a vertex without a cycle through it)
     forms a trivial component by itself."))
  (set::insert (symbol-lfix pred-name)
               (defind-pred-clique-loop
                 (defind-pred-dependencies pred-name irule-infos)
                 pred-name irule-infos))

  :prepwork
  ((define defind-pred-clique-loop ((deps symbol-setp)
                                    (pred-name symbolp)
                                    (irule-infos defind-irule-info-listp))
     :returns (clique symbol-setp)
     :parents nil
     (cond ((set::emptyp (symbol-sfix deps)) nil)
           (t (b* ((p (set::head deps))
                   (clique (defind-pred-clique-loop
                             (set::tail deps)
                             pred-name irule-infos)))
                (if (set::in (symbol-lfix pred-name)
                             (defind-pred-dependencies p irule-infos))
                    (set::insert p clique)
                  clique))))
     :verify-guards :after-returns
     :prepwork ((local (in-theory (enable symbol-sfix)))))))

;;;;;;;;;;;;;;;;;;;;

(define defind-cliques ((pred-names symbol-listp)
                        (irule-infos defind-irule-info-listp))
  :returns (cliques symbol-set-setp)
  :short "Set of the cliques formed by
          the predicates being defined, according to the rules."
  :long
  (xdoc::topstring
   (xdoc::p
    "The rules induce a dependency relation
     among the predicates being defined
     (see @(tsee defind-preds-direct-dependencies)),
     which partitions the predicates into cliques
     (see @(tsee defind-pred-clique)),
     where in particular each non-recursive predicate
     forms a singleton clique by itself.
     This function returns the set of the cliques,
     which is thus a set of non-empty sets of predicate names.")
   (xdoc::p
    "We go through the predicates,
     and we insert the clique of each predicate into the result.
     The predicates of a clique all contribute the same clique,
     which appears just once in the result, which is a set.")
   (xdoc::p
    "This function returns the cliques without any order.
     They are put in dependency order by @(tsee defind-order-cliques)."))
  (defind-cliques-loop pred-names irule-infos)

  :prepwork
  ((define defind-cliques-loop ((preds-to-do symbol-listp)
                                (irule-infos defind-irule-info-listp))
     :returns (cliques symbol-set-setp)
     :parents nil
     (b* (((when (endp preds-to-do)) nil)
          (cliques (defind-cliques-loop (cdr preds-to-do) irule-infos))
          (clique (defind-pred-clique (car preds-to-do) irule-infos)))
       (set::insert clique cliques))
     :verify-guards :after-returns)))

;;;;;;;;;;;;;;;;;;;;

(define defind-order-cliques ((cliques symbol-set-setp)
                              (irule-infos defind-irule-info-listp))
  :returns (ordered-cliques symbol-set-listp)
  :short "Order a set of cliques according to
          the dependencies among them."
  :long
  (xdoc::topstring
   (xdoc::p
    "A clique depends on another clique when
     some predicate in the first clique
     depends on some predicate in the second clique.
     Two distinct cliques cannot depend on each other:
     the dependencies would compose into mutual dependencies
     between predicates in the two cliques,
     which would thus be one clique;
     so the dependency relation among the cliques is acyclic.
     We return the list of the cliques in dependency order:
     each clique only depends on itself and on
     cliques that precede it in the list.")
   (xdoc::p
    "We compute the order iteratively, starting with the empty list:
     each round goes through the cliques not yet in the list,
     and finds the ones whose external dependencies,
     i.e. the direct dependencies of the predicates in the clique
     (see @(tsee defind-preds-direct-dependencies))
     minus the predicates in the clique itself,
     are all among the predicates of the cliques already in the list;
     these cliques, if any, are added to the list,
     in the order in which they appear in the set of cliques.
     We stop when a round finds no cliques to add.
     Termination is justified by the fact that
     each round that finds a (non-empty) collection of cliques to add
     strictly decreases the number of the cliques not yet in the list.")
   (xdoc::p
    "When this function is applied to
     the cliques of the predicates being defined
     (see @(tsee defind-cliques)),
     the acyclicity of the dependencies among the cliques ensures that
     each round finds at least one clique to add
     (except the final round, with no cliques left,
     which stops the computation):
     the resulting list consists of exactly the input cliques.
     However, this function is well-defined for any set of cliques:
     if a round finds no cliques to add
     while some cliques are not in the list yet,
     those remaining cliques are appended at the end of the list."))
  (defind-order-cliques-loop cliques nil irule-infos)

  :prepwork

  ((local (in-theory (enable emptyp-of-symbol-set-set-fix
                             symbol-set-listp-when-symbol-set-setp
                             set-listp-when-symbol-set-listp)))

   (define defind-order-cliques-loop ((cliques-to-do symbol-set-setp)
                                      (available symbol-setp)
                                      (irule-infos defind-irule-info-listp))
     :returns (ordered-cliques symbol-set-listp)
     :parents nil
     (b* (((when (set::emptyp (symbol-set-set-fix cliques-to-do))) nil)
          ((mv cliques-to-add still)
           (defind-order-cliques-round cliques-to-do available irule-infos))
          ((when (endp cliques-to-add)) cliques-to-do)
          (ordered-rest
           (defind-order-cliques-loop
             still
             (set::union (set::set-list-union cliques-to-add)
                         (symbol-sfix available))
             irule-infos)))
       (append cliques-to-add ordered-rest))
     :measure (set::cardinality (symbol-set-set-fix cliques-to-do))
     :verify-guards :after-returns
     :guard-hints
     (("Goal"
       :in-theory (enable true-listp-when-symbol-set-listp
                          consp-under-iff-when-true-listp-no-backchain-limit)))

     :prepwork

     ((define defind-order-cliques-round ((cliques-to-do symbol-set-setp)
                                          (available symbol-setp)
                                          (irule-infos defind-irule-info-listp))
        :returns (mv (cliques-to-add symbol-set-listp)
                     (still symbol-set-setp))
        :parents nil
        (b* (((when (set::emptyp (symbol-set-set-fix cliques-to-do)))
              (mv nil nil))
             (clique (set::head cliques-to-do))
             ((mv cliques-to-add still)
              (defind-order-cliques-round (set::tail cliques-to-do)
                                          available
                                          irule-infos)))
          (if (set::subset
               (set::difference
                (defind-preds-direct-dependencies clique irule-infos)
                clique)
               (symbol-sfix available))
              (mv (cons clique cliques-to-add) still)
            (mv cliques-to-add (set::insert clique still))))
        :verify-guards :after-returns

        ///

        (defret cardinality-upper-bound-of-defind-order-cliques-round.still
          (implies (symbol-set-setp cliques-to-do)
                   (<= (set::cardinality still)
                       (set::cardinality cliques-to-do)))
          :rule-classes :linear
          :hints (("Goal"
                   :induct t
                   :in-theory (acl2::enable* set::expensive-rules
                                             set::cardinality))))

        (defret cardinality-decrease-of-defind-order-cliques-round.still
          (implies (and (symbol-set-setp cliques-to-do)
                        (consp cliques-to-add))
                   (< (set::cardinality still)
                      (set::cardinality cliques-to-do)))
          :rule-classes :linear
          :hints (("Goal"
                   :induct t
                   :in-theory (acl2::enable* set::expensive-rules
                                             set::cardinality)))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-rule-deriving-pred ((pred-name symbolp)
                                   (preds symbol-setp)
                                   (irule-infos defind-irule-info-listp))
  :returns (rule? symbolp)
  :short "Find the first rule, if any, that
          has a given predicate as its conclusion
          and whose premises only contain predicates in a given set."
  :long
  (xdoc::topstring
   (xdoc::p
    "We go through the rules in order,
     and we return the name of the first rule that
     has the predicate @('pred-name') in its conclusion
     and whose premise predicates (see @(tsee defind-preds-in-premises))
     are all in the @('preds') set;
     we return @('nil') if there is no such rule.
     Such a rule can derive the predicate,
     given that the predicates in the set can be derived."))
  (b* (((when (endp irule-infos)) nil)
       ((defind-irule-info info) (car irule-infos))
       ((when (and (equal (defind-conclusion-info->name info.conclusion)
                          (symbol-lfix pred-name))
                   (set::subset (defind-preds-in-premises info.premises)
                                (symbol-sfix preds))))
        info.name))
    (defind-rule-deriving-pred pred-name preds (cdr irule-infos))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-pred-levels ((preds symbol-setp)
                            (preds-in-previous-cliques symbol-setp)
                            (irule-infos defind-irule-info-listp))
  :returns (mv (levels symbol-set-listp)
               (unleveled symbol-setp))
  :short "Organize a set of predicates into levels."
  :long
  (xdoc::topstring
   (xdoc::p
    "The levels of the predicates in @('preds') are relative to
     the predicates in @('preds-in-previous-cliques'),
     which are taken to be derivable:
     when @('preds') is a clique,
     @('preds-in-previous-cliques') consists of
     the predicates of the preceding cliques in dependency order
     (see @(tsee defind-leveled-cliques)).")
   (xdoc::p
    "A predicate is at level 0 if
     some rule can derive it from
     the predicates in @('preds-in-previous-cliques')
     (see @(tsee defind-rule-deriving-pred)),
     i.e. some rule has the predicate as its conclusion
     and all its premises that are predicates being defined
     contain predicates in @('preds-in-previous-cliques').
     A predicate is at level @('n+1') if
     it is not at any of the levels 0 to @('n'),
     and some rule can derive it from
     predicates at levels 0 to @('n')
     or in @('preds-in-previous-cliques').
     Not every predicate is necessarily at some level,
     e.g. if the predicate appears in the conclusion of only one rule,
     and that rule has the same predicate in a premise.")
   (xdoc::p
    "We compute the levels iteratively, starting from no levels:
     each round goes through the predicates not yet at any level,
     and finds the ones that some rule can derive
     from the predicates at the levels found so far
     or in @('preds-in-previous-cliques');
     these predicates, if any, form the next level.
     We stop when a round finds no new level.
     Termination is justified by the fact that
     each round that finds a (non-empty) new level
     strictly shrinks the set of the predicates not yet at any level.")
   (xdoc::p
    "We return the list of the levels in order:
     the element at position @('n') of the list is
     the set of the predicates at level @('n');
     each level is a non-empty set.
     We also return the set of the predicates at no level,
     which is empty exactly when all the predicates are at some level."))
  (defind-pred-levels-loop preds preds-in-previous-cliques irule-infos)

  :prepwork

  ((local (in-theory (enable emptyp-of-symbol-sfix)))

   (define defind-pred-levels-loop ((unleveled symbol-setp)
                                    (leveled symbol-setp)
                                    (irule-infos defind-irule-info-listp))
     :returns (mv (levels symbol-set-listp)
                  (still-unleveled symbol-setp))
     :parents nil
     (b* (((when (set::emptyp (symbol-sfix unleveled))) (mv nil nil))
          (new-leveled (defind-pred-levels-round unleveled leveled irule-infos))
          ((when (set::emptyp new-leveled)) (mv nil unleveled))
          ((mv levels still-unleveled)
           (defind-pred-levels-loop (set::difference unleveled new-leveled)
             (set::union new-leveled (symbol-sfix leveled))
             irule-infos)))
       (mv (cons new-leveled levels) still-unleveled))
     :measure (set::cardinality (symbol-sfix unleveled))
     ;; DIFFERENCE-CARDINALITY-DECREASES rewrites the measure decrease;
     ;; its subset hypothesis is relieved by
     ;; SUBSET-OF-DEFIND-PRED-LEVELS-ROUND.
     ;; EXPAND-CARDINALITY-OF-DIFFERENCE is disabled so that
     ;; the (cardinality (difference u x)) pattern
     ;; that the former matches is not rewritten away.
     :hints (("Goal" :in-theory (e/d (difference-cardinality-decreases)
                                     (set::expand-cardinality-of-difference))))
     :verify-guards :after-returns

     :prepwork
     ((define defind-pred-levels-round ((preds-to-do symbol-setp)
                                        (leveled symbol-setp)
                                        (irule-infos defind-irule-info-listp))
        :returns (new-leveled symbol-setp)
        :parents nil
        (b* (((when (set::emptyp (symbol-sfix preds-to-do))) nil)
             (pred (set::head preds-to-do))
             (new-leveled (defind-pred-levels-round
                            (set::tail preds-to-do)
                            leveled
                            irule-infos)))
          (if (defind-rule-deriving-pred pred leveled irule-infos)
              (set::insert pred new-leveled)
            new-leveled))
        :verify-guards :after-returns

        ///

        (defret subset-of-defind-pred-levels-round
          (implies (symbol-setp preds-to-do)
                   (set::subset new-leveled preds-to-do))
          :hints (("Goal"
                   :induct t
                   :in-theory (acl2::enable* set::expensive-rules)))))))))

;;;;;;;;;;;;;;;;;;;;

(define defind-leveled-cliques ((pred-names symbol-listp)
                                (irule-infos defind-irule-info-listp))
  :returns (mv (leveled-cliques symbol-set-list-listp)
               (unleveled symbol-setp))
  :short "Organize the predicates being defined into
          cliques in dependency order,
          each clique organized into levels."
  :long
  (xdoc::topstring
   (xdoc::p
    "We calculate the cliques formed by the predicates,
     we put them in dependency order,
     and we organize each clique into levels.
     The premise predicates of the rules that derive the predicates of a clique
     are all in the clique itself or in preceding cliques;
     so the levels of each clique are calculated
     by taking the predicates in the preceding cliques as derivable.")
   (xdoc::p
    "We return the list of the cliques in dependency order,
     each organized into levels:
     the element at position @('n') of the outer list consists of
     the levels of the @('n')-th clique in dependency order;
     see @(tsee defind-pred-levels) for
     the meaning of each inner list of levels.
     We also return the set of the predicates at no level,
     unioned over all the cliques,
     which is empty exactly when
     every predicate is at some level in its clique."))
  (b* ((cliques (defind-cliques pred-names irule-infos))
       (ordered-cliques (defind-order-cliques cliques irule-infos)))
    (defind-leveled-cliques-loop ordered-cliques nil irule-infos))

  :prepwork
  ((define defind-leveled-cliques-loop ((cliques-to-do symbol-set-listp)
                                        (preds-in-previous-cliques symbol-setp)
                                        (irule-infos defind-irule-info-listp))
     :returns (mv (leveled-cliques symbol-set-list-listp)
                  (unleveled symbol-setp))
     :parents nil
     (b* (((when (endp cliques-to-do)) (mv nil nil))
          (clique (car cliques-to-do))
          ((mv levels clique-unleveled)
           (defind-pred-levels clique preds-in-previous-cliques irule-infos))
          ((mv leveled-cliques unleveled)
           (defind-leveled-cliques-loop
             (cdr cliques-to-do)
             (set::union (symbol-sfix clique)
                         (symbol-sfix preds-in-previous-cliques))
             irule-infos)))
       (mv (cons levels leveled-cliques)
           (set::union clique-unleveled unleveled)))
     :verify-guards :after-returns)))

;;;;;;;;;;;;;;;;;;;;

(define defind-pred-level ((pred-name symbolp)
                           (levels symbol-set-listp))
  :returns (level natp)
  :short "Level of a predicate, among a list of levels."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('levels') input consists of the levels of a clique:
     the element at position @('n') of the list is
     the set of the predicates at level @('n').
     We return the position of the set that contains the predicate.")
   (xdoc::p
    "This function is called on
     a predicate of the clique whose levels are passed as input,
     so the predicate is always found in some set;
     if it is not (which should never happen),
     we raise an internal error."))
  (b* (((when (endp levels))
        (raise "Internal error: predicate ~x0 has no level."
               (symbol-lfix pred-name))
        0)
       ((when (set::in (symbol-lfix pred-name)
                       (symbol-sfix (car levels))))
        0))
    (1+ (defind-pred-level pred-name (cdr levels))))
  :no-function nil)

;;;;;;;;;;;;;;;;;;;;

(define defind-pred-override-rule ((pred-name symbolp)
                                   (level natp)
                                   (levels symbol-set-listp)
                                   (preds-in-previous-cliques symbol-setp)
                                   (irule-infos defind-irule-info-listp))
  :returns (rule symbolp)
  :short "Rule that provides the base case override
          for the proof fixtype of a predicate."
  :long
  (xdoc::topstring
   (xdoc::p
    "The proof fixtype generated for a predicate
     at level 1 or more in its clique
     needs a base case override:
     the designated summand must correspond to a rule that
     derives the predicate from predicates
     at strictly lower levels in the clique,
     or in previous cliques.
     This function finds the first such rule
     by passing to @(tsee defind-rule-deriving-pred)
     the union of the levels strictly below @('level'),
     which is the level of the predicate in question,
     and of the predicates in the previous cliques.")
   (xdoc::p
    "Since the predicate is at level @('level'),
     the rule always exists:
     the predicate was put at that level
     exactly because of such a rule
     (see @(tsee defind-pred-levels)).
     If the rule is not found (which should never happen),
     we raise an internal error."))
  (b* ((levels (symbol-set-list-fix levels))
       (derivable-preds
        (set::union (set::set-list-union (take (nfix level) levels))
                    (symbol-sfix preds-in-previous-cliques)))
       (rule (defind-rule-deriving-pred pred-name derivable-preds irule-infos))
       ((unless rule)
        (raise "Internal error: no override rule for predicate ~x0."
               (symbol-lfix pred-name))))
    rule)
  :no-function nil
  :guard-hints (("Goal" :in-theory (enable set-listp-when-symbol-set-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ definductive-names
  :parents (definductive-implementation)
  :short "Names of generated events and their constituents."
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-proof-type-name ((pred-name symbolp) (name symbolp))
  :returns (type-name symbolp)
  :short "Name of a @('p[i]-proof') fixtype."
  (packn-pos (list (symbol-lfix pred-name) '-proof) (symbol-lfix name)))

;;;;;;;;;;

(define defind-proof-type-clique-name ((pred-name symbolp) (name symbolp))
  :returns (deftypes-name symbolp)
  :short "Name of a @('p[i]-proof') fixtype clique."
  (packn-pos (list (symbol-lfix pred-name) '-proof-clique)
             (symbol-lfix name)))

;;;;;;;;;;;;;;;;;;;;

(define defind-proof-recog-name ((pred-name symbolp) (name symbolp))
  :returns (recog-name symbolp)
  :short "Name of the recognizer of a @('p[i]-proof') fixtype."
  (packn-pos (list (symbol-lfix pred-name) '-proofp) (symbol-lfix name)))

;;;;;;;;;;;;;;;;;;;;

(define defind-proof-fixer-name ((pred-name symbolp) (name symbolp))
  :returns (fixer-name symbolp)
  :short "Name of the fixer of a @('p[i]-proof') fixtype."
  (packn-pos (list (symbol-lfix pred-name) '-proof-fix) (symbol-lfix name)))

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

(define defind-prem-field-name ((num posp) (name symbolp))
  :returns (field-name symbolp)
  :short "Name of a premise field of a @('p[i]-proof') fixtype."
  (packn-pos (list 'premise (lposfix num) '-proof) (symbol-lfix name)))

;;;;;;;;;;

(define defind-prem-field-names ((num natp) (name symbolp))
  :returns (field-names symbol-listp)
  :short "Name of the premise fields of a @('p[i]-proof') fixtype."
  (cond ((zp num) nil)
        (t (append (defind-prem-field-names (1- (lnfix num)) name)
                   (list (defind-prem-field-name num name)))))
  :measure (nfix num)
  :prepwork ((local (in-theory (enable nfix)))))

;;;;;;;;;;;;;;;;;;;;

(define defind-proof-var-name ((name symbolp))
  :returns (var-name symbolp)
  :short "Name of the proof variable."
  (packn-pos (list 'proof) (symbol-lfix name)))

;;;;;;;;;;

(define defind-proof-xvar-name ((name symbolp))
  :returns (var-name symbolp)
  :short "Name of the @(':xvar') of a @('p[i]-proof') fixtype."
  :long
  (xdoc::topstring
   (xdoc::p
    "The fields of these fixtypes are named after the variables of the rules,
     so the @(':xvar') must differ from all of those;
     see @(tsee defind-gen-proof-deftagsum).")
   (xdoc::p
    "This is not the variable that the @('p[i]-proof-validp') functions
     use for their proof argument, which is @(tsee defind-proof-var-name).
     A variable of a rule may shadow that one without harm,
     because the case macro binds the fields of the proof
     before the shadowing takes place;
     it may not clash with this one,
     which @(tsee defind-check-proof-names) enforces."))
  (packn-pos (list (defind-proof-var-name name) '$) (symbol-lfix name)))

;;;;;;;;;;

(define defind-concl-var-name ((name symbolp))
  :returns (var-name symbolp)
  :short "Prefix of the names of the conclusion argument variables."
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

(define defind-proof-var-field-var-name ((var symbolp) (name symbolp))
  :returns (var-name symbolp)
  :short "Name of the variable bound to a variable field of a proof."
  :long
  (xdoc::topstring
   (xdoc::p
    "The summands of a @('p[i]-proof') fixtype have a field
     for each variable of the rule, named after the variable.
     This is the variable that the case macro of the fixtype
     binds to that field;
     @(tsee defind-proof-prem-var-name)
     is the analogous name for the premise fields.")
   (xdoc::p
    "The cases of a @('p[i]-proof-validp') function use these variables
     either as the right-hand sides of the bindings of the rule's variables
     or directly as arguments of the @('p[l[k]]-rule[k]-validp') function;
     see @(tsee defind-gen-proof-valid-fn-case-bindings)."))
  (packn-pos (list (defind-proof-var-name name)
                   #\.
                   (symbol-lfix var))
             (symbol-lfix name)))

;;;;;;;;;;

(define defind-proof-var-field-var-names ((vars symbol-listp) (name symbolp))
  :returns (var-names symbol-listp)
  :short "Names of the variables bound to
          all the variable fields of a proof."
  (cond ((endp vars) nil)
        (t (cons (defind-proof-var-field-var-name (car vars) name)
                 (defind-proof-var-field-var-names (cdr vars) name)))))

;;;;;;;;;;

(define defind-concl-formal-var-name ((formal symbolp) (name symbolp))
  :returns (var-name symbolp)
  :short "Name of the conclusion argument variable
          corresponding to a formal of a predicate."
  (packn-pos (list (defind-concl-var-name name)
                   #\.
                   (symbol-lfix formal))
             (symbol-lfix name)))

;;;;;;;;;;

(define defind-concl-formal-var-names ((formals symbol-listp) (name symbolp))
  :returns (var-names symbol-listp)
  :short "Names of the conclusion argument variables
          corresponding to the formals of a predicate."
  (cond ((endp formals) nil)
        (t (cons (defind-concl-formal-var-name (car formals) name)
                 (defind-concl-formal-var-names (cdr formals) name)))))

;;;;;;;;;;

(define defind-proof-concl-var-names ((formals symbol-listp) (name symbolp))
  :returns (var-names symbol-listp)
  :short "Names of the variables that a @('p[i]-proof-validp') function
          uses for the arguments of the conclusion."
  :long
  (xdoc::topstring
   (xdoc::p
    "These names must differ from the variables of the rules,
     which are bound, in each case of the function,
     to the corresponding fields of the proof:
     a rule variable with one of these names would shadow the formal,
     turning the equality for that argument of the conclusion
     into an equality of the field with itself.
     This is why @(tsee defind-check-proof-names) rejects such a rule.
     All the events that need these names obtain them here,
     so that the check cannot drift from what is generated."))
  (defind-concl-formal-var-names formals name))

;;;;;;;;;;;;;;;;;;;;

(define defind-proof-case-name ((pred-name symbolp) (name symbolp))
  :returns (case-name symbolp)
  :short "Name of the case macro of a @('p[i]-proof') fixtype."
  (packn-pos (list (defind-proof-type-name pred-name name) '-case)
             (symbol-lfix name)))

;;;;;;;;;;;;;;;;;;;;

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

(define defind-proof-var-acc-name ((pred-name symbolp)
                                   (irule-name symbolp)
                                   (var symbolp)
                                   (name symbolp))
  :returns (acc-name symbolp)
  :short "Name of a variable accessor of a @('p[i]-proof') summand."
  (packn-pos (list (defind-proof-constr-name pred-name irule-name name)
                   '->
                   (symbol-lfix var))
             (symbol-lfix name)))

;;;;;;;;;;

(define defind-proof-var-acc$inline-name ((pred-name symbolp)
                                          (irule-name symbolp)
                                          (var symbolp)
                                          (name symbolp))
  :returns (acc-name symbolp)
  :short "Name of the @('$inline') form of
          a variable accessor of a @('p[i]-proof') summand."
  (packn-pos (list (defind-proof-var-acc-name pred-name irule-name var name)
                   '$inline)
             (symbol-lfix name)))

;;;;;;;;;;;;;;;;;;;;

(define defind-proof-kind-fn-name ((pred-name symbolp) (name symbolp))
  :returns (fn-name symbolp)
  :short "Name of the kind function of a @('p[i]-proof') fixtype."
  (packn-pos (list (defind-proof-type-name pred-name name) '-kind)
             (symbol-lfix name)))

;;;;;;;;;;

(define defind-proof-kind$inline-fn-name ((pred-name symbolp) (name symbolp))
  :returns (fn-name symbolp)
  :short "Name of the @('$inline') kind function of a @('p[i]-proof') fixtype."
  (packn-pos (list (defind-proof-kind-fn-name pred-name name) '$inline)
             (symbol-lfix name)))

;;;;;;;;;;

(define defind-proof-count-fn-name ((pred-name symbolp) (name symbolp))
  :returns (fn-name symbolp)
  :short "Name of the count function of a @('p[i]-proof') fixtype."
  (packn-pos (list (defind-proof-type-name pred-name name) '-count)
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

(define defind-proof-valid-fn-name ((pred-name symbolp) (name symbolp))
  :returns (fn-name symbolp)
  :short "Name of a @('p[i]-proof-validp')."
  (packn-pos (list (defind-proof-type-name pred-name name) '-validp)
             (symbol-lfix name)))

;;;;;;;;;;

(define defind-proof-valid-fn-clique-name ((pred-name symbolp) (name symbolp))
  :returns (defines-name symbolp)
  :short "Name of a @(tsee defines) of @('p[i]-proof-validp') functions."
  (packn-pos (list (defind-proof-valid-fn-name pred-name name) '-clique)
             (symbol-lfix name)))

;;;;;;;;;;

(define defind-proof-valid-fn-clique-flag-name ((pred-name symbolp)
                                                (name symbolp))
  :returns (flag-fn-name symbolp)
  :short "Name of the flag function of a @(tsee defines) of
          @('p[i]-proof-validp') functions."
  (packn-pos (list (defind-proof-valid-fn-clique-name pred-name name) '-flag)
             (symbol-lfix name)))

;;;;;;;;;;

(define defind-proof-valid-fn-clique-flag-equivs-name ((pred-name symbolp)
                                                       (name symbolp))
  :returns (thm-name symbolp)
  :short "Name of the flag equivalence theorem of a @(tsee defines) of
          @('p[i]-proof-validp') functions."
  :long
  (xdoc::topstring
   (xdoc::p
    "This theorem is generated by the flag machinery,
     along with the flag function.
     It provides rewrite rules that turn
     calls of the flag function on constant flag values
     into calls of the corresponding functions of the clique."))
  (packn-pos (list (defind-proof-valid-fn-clique-flag-name pred-name name)
                   '-equivalences)
             (symbol-lfix name)))

;;;;;;;;;;

(define defind-proof-witness-fn-name ((pred-name symbolp) (name symbolp))
  :returns (fn-name symbolp)
  :short "Name of the witness function for a @('p[i]') predicate."
  (packn-pos (list (symbol-lfix pred-name) '-proof) (symbol-lfix name)))

;;;;;;;;;;

(define defind-proof-minimal-fn-name ((pred-name symbolp) (name symbolp))
  :returns (fn-name symbolp)
  :short "Name of a @('p[i]-proof-minimalp') predicate."
  (packn-pos (list (defind-proof-type-name pred-name name) '-minimalp)
             (symbol-lfix name)))

;;;;;;;;;;

(define defind-proof-minimal-return-thm-name ((pred-name symbolp)
                                              (name symbolp))
  :returns (thm-name symbolp)
  :short "Name of the boolean return theorem of
          a @('p[i]-proof-minimalp') predicate."
  (packn-pos (list 'booleanp-of-
                   (defind-proof-minimal-fn-name pred-name name))
             (symbol-lfix name)))

;;;;;;;;;;

(define defind-proof-minimal-witness-fn-name ((pred-name symbolp)
                                              (name symbolp))
  :returns (fn-name symbolp)
  :short "Name of the witness function of
          a @('p[i]-proof-minimalp') predicate."
  (packn-pos (list (defind-proof-minimal-fn-name pred-name name) '-witness)
             (symbol-lfix name)))

;;;;;;;;;;

(define defind-proof-minimal-var-name ((name symbolp))
  :returns (var-name symbolp)
  :short "Name of the proof variable quantified over by
          a @('p[i]-proof-minimalp') predicate."
  :long
  (xdoc::topstring
   (xdoc::p
    "This cannot clash with anything:
     the other formals of the predicate are
     the proof variable (see @(tsee defind-proof-var-name))
     and the variables for the arguments of the conclusion,
     which are all prefixed (see @(tsee defind-concl-formal-var-name));
     and the body mentions no user-supplied term."))
  (packn-pos (list (defind-proof-var-name name) '2) (symbol-lfix name)))

;;;;;;;;;;

(define defind-proof-descend-fn-name ((pred-name symbolp) (name symbolp))
  :returns (fn-name symbolp)
  :short "Name of a @('p[i]-descend') function."
  (packn-pos (list (symbol-lfix pred-name) '-descend) (symbol-lfix name)))

;;;;;;;;;;

(define defind-pred-when-valid-proof-thm-name ((pred-name symbolp)
                                               (name symbolp))
  :returns (thm-name symbolp)
  :short "Name of a @('p[i]-when-proof-validp') theorem."
  (packn-pos (list (symbol-lfix pred-name) '-when-proof-validp)
             (symbol-lfix name)))

;;;;;;;;;;

(define defind-proof-minimal-necc-thm-name ((pred-name symbolp)
                                            (name symbolp))
  :returns (thm-name symbolp)
  :short "Name of the necessity theorem of
          a @('p[i]-proof-minimalp') predicate."
  (packn-pos (list (defind-proof-minimal-fn-name pred-name name) '-necc)
             (symbol-lfix name)))

;;;;;;;;;;

(define defind-proof-count-bound-thm-name ((pred-name symbolp)
                                           (name symbolp))
  :returns (thm-name symbolp)
  :short "Name of a @('p[i]-proof-count-bound') theorem."
  (packn-pos (list (defind-proof-count-fn-name pred-name name) '-bound)
             (symbol-lfix name)))

;;;;;;;;;;

(define defind-ind-fn-name ((pred-name symbolp) (name symbolp))
  :returns (fn-name symbolp)
  :short "Name of a @('p[i]-induct') function."
  (packn-pos (list (symbol-lfix pred-name) '-induct) (symbol-lfix name)))

;;;;;;;;;;

(define defind-ind-fn-clique-name ((pred-name symbolp) (name symbolp))
  :returns (defines-name symbolp)
  :short "Name of a @(tsee defines) of @('p[i]-induct') functions."
  (packn-pos (list (defind-ind-fn-name pred-name name) '-clique)
             (symbol-lfix name)))

;;;;;;;;;;

(define defind-induction-thm-name ((pred-name symbolp) (name symbolp))
  :returns (thm-name symbolp)
  :short "Name of a @('p[i]-induction') theorem."
  (packn-pos (list (symbol-lfix pred-name) '-induction) (symbol-lfix name)))

;;;;;;;;;;

(define defind-ind-flag-fn-name ((pred-name symbolp) (name symbolp))
  :returns (fn-name symbolp)
  :short "Name of the flag function of a @(tsee defines) of
          @('p[i]-induct') functions."
  (packn-pos (list (defind-ind-fn-name pred-name name) '-flag)
             (symbol-lfix name)))

;;;;;;;;;;

(define defind-ind-flag-macro-name ((pred-name symbolp) (name symbolp))
  :returns (macro-name symbolp)
  :short "Name of the flag macro of a @(tsee defines) of
          @('p[i]-induct') functions."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the interface for rule induction
     over a clique of two or more predicates,
     so we name it after the @('p[i]-induction') rules,
     which serve that purpose for a clique of a single predicate,
     rather than leaving it the longer default name
     derived from the name of the @(tsee defines)."))
  (packn-pos (list 'defthm- (defind-induction-thm-name pred-name name))
             (symbol-lfix name)))

;;;;;;;;;;

(define defind-pred-alt-fn-name ((pred-name symbolp) (name symbolp))
  :returns (fn-name symbolp)
  :short "Name of a @('p[i]-alt') function name."
  (packn-pos (list (symbol-lfix pred-name) '-alt) (symbol-lfix name)))

;;;;;;;;;;

(define defind-pred-alt-fn-names ((pred-names symbol-listp) (name symbolp))
  :returns (fn-names symbol-listp)
  :short "Names of the @('p[i]-alt') functions for a list of predicates."
  (cond ((endp pred-names) nil)
        (t (cons (defind-pred-alt-fn-name (car pred-names) name)
                 (defind-pred-alt-fn-names (cdr pred-names) name)))))

;;;;;;;;;;;;;;;;;;;;

(define defind-proof-valid-fn-clique-defthm-macro-name ((pred-name symbolp)
                                                        (name symbolp))
  :returns (macro-name symbolp)
  :short "Name of the macro to prove theorems by induction on
          a clique of @('p[i]-proof-validp') functions."
  :long
  (xdoc::topstring
   (xdoc::p
    "This macro is generated by the flag machinery,
     along with the flag function."))
  (packn-pos (list 'defthm-
                   (defind-proof-valid-fn-clique-flag-name pred-name name))
             (symbol-lfix name)))

;;;;;;;;;;;;;;;;;;;;

(define defind-proof-kind-poss-thm-name ((pred-name symbolp) (name symbolp))
  :returns (thm-name symbolp)
  :short "Name of the kind possibilities theorem for a @('p[i]-proof') fixtype."
  (packn-pos (list (defind-proof-type-name pred-name name) '-kind-possibilities)
             (symbol-lfix name)))

;;;;;;;;;;

(define defind-proof-kind-fixing-thm-name ((pred-name symbolp)
                                           (name symbolp))
  :returns (thm-name symbolp)
  :short "Name of the kind fixing theorem for a @('p[i]-proof') fixtype."
  :long
  (xdoc::topstring
   (xdoc::p
    "The variable that ends the name is the @(':xvar') of the fixtype;
     see @(tsee defind-proof-prem-fixing-thm-name)."))
  (packn-pos (list (defind-proof-type-name pred-name name)
                   '-kind$inline-of-
                   (defind-proof-fixer-name pred-name name)
                   '-
                   (defind-proof-xvar-name name))
             (symbol-lfix name)))

;;;;;;;;;;

(define defind-proof-fix-id-thm-name ((pred-name symbolp) (name symbolp))
  :returns (thm-name symbolp)
  :short "Name of the fixing identity theorem for a @('p[i]-proof') fixtype."
  (packn-pos (list (defind-proof-fixer-name pred-name name)
                   '-when-
                   (defind-proof-recog-name pred-name name))
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

(define defind-proof-prem-acc-return-thm-name ((prem-pred-name symbolp)
                                               (pred-name symbolp)
                                               (irule-name symbolp)
                                               (num posp)
                                               (name symbolp))
  :returns (thm-name symbolp)
  :short "Name of the return theorem of a premise accessor of
          a @('p[i]-proof') fixtype."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('prem-pred-name') input is the name of
     the predicate in the premise,
     whose fixtype of proofs is the type of the accessed field."))
  (packn-pos (list (defind-proof-recog-name prem-pred-name name)
                   '-of-
                   (defind-proof-prem-acc-name pred-name irule-name num name))
             (symbol-lfix name)))

;;;;;;;;;;

(define defind-proof-count-return-thm-name ((pred-name symbolp)
                                            (name symbolp))
  :returns (thm-name symbolp)
  :short "Name of the return theorem of
          the count function of a @('p[i]-proof') fixtype."
  (packn-pos (list 'return-type-of-
                   (defind-proof-count-fn-name pred-name name)
                   '.count)
             (symbol-lfix name)))

;;;;;;;;;;

(define defind-proof-count-natp-thm-name ((pred-name symbolp)
                                          (standalonep booleanp)
                                          (name symbolp))
  :returns (thm-name symbolp)
  :short "Name of the theorem saying that
          the count function of a @('p[i]-proof') fixtype
          returns a natural number."
  :long
  (xdoc::topstring
   (xdoc::p
    "As with @(tsee defind-proof-valid-return-thm-name),
     the name depends on whether the predicate forms a singleton clique:
     FTY names this theorem after the return type and the function
     for a standalone fixtype,
     and in its own way for a fixtype of a clique of two or more."))
  (if standalonep
      (packn-pos (list 'natp-of-
                       (defind-proof-count-fn-name pred-name name))
                 (symbol-lfix name))
    (defind-proof-count-return-thm-name pred-name name)))

;;;;;;;;;;

(define defind-proof-prem-count-thm-name ((prem-pred-name symbolp)
                                          (pred-name symbolp)
                                          (irule-name symbolp)
                                          (num posp)
                                          (name symbolp))
  :returns (thm-name symbolp)
  :short "Name of the count theorem of a premise accessor of
          a @('p[i]-proof') fixtype."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('prem-pred-name') input is the name of
     the predicate in the premise,
     whose fixtype of proofs is the type of the accessed field,
     and thus provides the count function."))
  (packn-pos (list (defind-proof-count-fn-name prem-pred-name name)
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
  :long
  (xdoc::topstring
   (xdoc::p
    "The variable that ends the name is the @(':xvar') of the fixtype,
     which is not the default @('x')
     (see @(tsee defind-gen-proof-deftagsum))."))
  (packn-pos (list (defind-proof-prem-acc-name pred-name irule-name num name)
                   '$inline-of-
                   (defind-proof-fixer-name pred-name name)
                   '-
                   (defind-proof-xvar-name name))
             (symbol-lfix name)))

;;;;;;;;;;

(define defind-proof-var-acc-fixing-thm-names ((pred-name symbolp)
                                               (irule-name symbolp)
                                               (vars symbol-listp)
                                               (name symbolp))
  :returns (thm-names symbol-listp)
  :short "Names of the fixing theorems of the variable accessors of
          a @('p[i]-proof') summand."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the counterparts of
     @(tsee defind-proof-prem-fixing-thm-name),
     for the fields named after the variables of the rule;
     see that function
     for the variable that ends the names."))
  (cond ((endp vars) nil)
        (t (cons (packn-pos
                  (list (defind-proof-var-acc-name
                          pred-name irule-name (car vars) name)
                        '$inline-of-
                        (defind-proof-fixer-name pred-name name)
                        '-
                        (defind-proof-xvar-name name))
                  (symbol-lfix name))
                 (defind-proof-var-acc-fixing-thm-names
                   pred-name irule-name (cdr vars) name)))))

;;;;;;;;;;

(define defind-proof-var-of-constr-thm-names ((pred-name symbolp)
                                              (irule-name symbolp)
                                              (vars symbol-listp)
                                              (name symbolp))
  :returns (thm-names symbol-listp)
  :short "Names of the theorems about the application of
          the variable accessors of a @('p[i]-proof') fixtype
          to the constructor of the fixtype."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the counterparts of
     @(tsee defind-proof-prem-of-constr-thm-name),
     for the fields named after the variables of the rule."))
  (cond ((endp vars) nil)
        (t (cons (packn-pos
                  (list (defind-proof-var-acc-name
                          pred-name irule-name (car vars) name)
                        '-of-
                        (defind-proof-constr-name pred-name irule-name name))
                  (symbol-lfix name))
                 (defind-proof-var-of-constr-thm-names
                   pred-name irule-name (cdr vars) name)))))

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

(define defind-proof-valid-return-thm-name ((pred-name symbolp)
                                            (standalonep booleanp)
                                            (name symbolp))
  :returns (thm-name symbolp)
  :short "Name of the return theorem of a @('p[i]-proof-validp') function."
  :long
  (xdoc::topstring
   (xdoc::p
    "A standalone function is introduced by @(tsee define),
     which names this theorem after the return type and the function.
     A function of a clique of two or more predicates is introduced by
     a @(tsee define) inside a @(tsee defines),
     which names it in its own way instead,
     ignoring even an explicit @(':name') in the return specifier.
     So the name depends on
     whether the predicate forms a singleton clique."))
  (if standalonep
      (packn-pos (list 'booleanp-of-
                       (defind-proof-valid-fn-name pred-name name))
                 (symbol-lfix name))
    (packn-pos (list 'return-type-of-
                     (defind-proof-valid-fn-name pred-name name)
                     '|.|
                     'yes/no)
               (symbol-lfix name))))

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

(define defind-pred-alt-irule-thm-name ((pred-name symbolp)
                                        (irule-name symbolp)
                                        (name symbolp))
  :returns (thm-name symbolp)
  :short "Name of the @('p[l[k]]-alt-rule[k]') constraint theorem."
  (packn-pos (list (defind-pred-alt-fn-name pred-name name)
                   '-
                   (symbol-lfix irule-name))
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

(define defind-pred-alt-when-proof-valid-thm-names ((preds symbol-setp)
                                                    (name symbolp))
  :returns (thm-names true-listp)
  :short "Names of the @('p[i]-alt-when-proof-validp') theorems
          for a set of predicates."
  (b* (((when (set::emptyp (symbol-sfix preds))) nil)
       (pred (set::head preds))
       (thm-names
        (defind-pred-alt-when-proof-valid-thm-names (set::tail preds) name)))
    (cons (defind-pred-alt-when-proof-valid-thm-name pred name)
          thm-names))
  :prepwork ((local (in-theory (enable emptyp-of-symbol-sfix)))))

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

(define defind-valid-proof-thm-section-name ((name symbolp))
  :returns (topic symbolp)
  :short "Name of the @(tsee defsection) containing
          the @('p[i]-when-proof-validp') theorems
          and the @('p[i]-proof-count-bound') theorems."
  (packn-pos (list (symbol-lfix name) '-valid-proofs) (symbol-lfix name)))

;;;;;;;;;;

(define defind-induction-thm-section-name ((name symbolp))
  :returns (topic symbolp)
  :short "Name of the @(tsee defsection) containing
          the @('p[i]-induction') theorems."
  :long
  (xdoc::topstring
   (xdoc::p
    "The suffix is @('-induction-rules') and not @('-induction'),
     because the latter is the name of
     the @('p[i]-induction') theorem of a predicate named
     as the @('name') input, which is a common case."))
  (packn-pos (list (symbol-lfix name) '-induction-rules) (symbol-lfix name)))

;;;;;;;;;;

(define defind-rule-thm-section-name ((name symbolp))
  :returns (topic symbolp)
  :short "Name of the @(tsee defsection) containing
          the @('p[l[k]]-rule[k]') theorems."
  (packn-pos (list (symbol-lfix name) '-rules) (symbol-lfix name)))

;;;;;;;;;;;;;;;;;;;;

(define defind-minimality-section-name ((name symbolp))
  :returns (topic symbolp)
  :short "Name of the @(tsee defsection) containing
          the constrained functions, constraints, and theorems
          for the minimality of the predicates."
  (packn-pos (list (symbol-lfix name) '-minimal) (symbol-lfix name)))

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
       ((erp infos) (defind-process-preds-loop preds 1 wrld))
       ((unless (defind-pred-names-unambp infos))
        (reterr (msg "The names of the predicates in the :PREDS input ~
                      must be all distinct, ~
                      but there are duplicates among ~&0."
                     (defind-pred-info-list->name infos)))))
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

  (defret defind-pred-names-unambp-of-defind-process-preds
    (defind-pred-names-unambp infos)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-process-term (term (desc msgp) state)
  :returns (mv erp (info defind-term-infop) state)
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
     Thus, the translation of the term fails
     if the term mentions those predicates.
     So this automatically checks their absence from the term.")
   (xdoc::p
    "We ensure that the term is single-valued, not a stobj.")
   (xdoc::p
    "The @('desc') input of this function is
     a description of the term, for error messages."))
  (b* (((reterr) (irr-defind-term-info) state)
       ((mv term/msg stobjs-out state) (check-user-term$ term state))
       ((unless (pseudo-termp term/msg))
        ;; No period at the end of the following string
        ;; because TERM/MSG ends with period already.
        (reterr (msg "~@0 must be a valid untranslated term, but: ~@1"
                     desc term/msg)))
       ((unless (equal stobjs-out (list nil)))
        (reterr (msg "~@0 must return a single non-stobj value, ~
                      but it returns ~x1 instead."
                     desc stobjs-out))))
    (retok (make-defind-term-info :uterm term :tterm term/msg) state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-process-args ((args true-listp)
                             (prem/concl-desc msgp)
                             state)
  :returns (mv erp (infos defind-term-info-listp) state)
  :short "Process the arguments of a premise or conclusion of a rule
          that contains a predicate being defined."
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
     :returns (mv erp (infos defind-term-info-listp) state)
     :parents nil
     (b* (((reterr) nil state)
          ((when (endp args)) (retok nil state))
          (arg-desc (msg "the ~n0 argument of ~@1"
                         (list (lposfix q))
                         (msg-downcase-first prem/concl-desc)))
          ((erp info state) (defind-process-term (car args) arg-desc state))
          ((erp infos state) (defind-process-args-loop
                              (cdr args) prem/concl-desc (1+ (lposfix q))
                              state)))
       (retok (cons info infos) state))
     :guard-hints (("Goal" :in-theory (enable character-alistp))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-process-conclusion (concl
                                   (desc msgp)
                                   (pred-infos defind-pred-info-listp)
                                   state)
  :guard (defind-pred-names-unambp pred-infos)
  :returns (mv erp (info defind-conclusion-infop) state)
  :short "Process the conclusion of a rule."
  :long
  (xdoc::topstring
   (xdoc::p
    "This must have the form of a predicate @('p[i]') applied to some terms.")
   (xdoc::p
    "The @('desc') input of this function is
     a description of the conclusion, for error messages."))
  (b* (((reterr) (irr-defind-conclusion-info) state)
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
                      one of the predicates among ~&1 applied to some terms, ~
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
       ((erp arg-infos state) (defind-process-args args args-desc state)))
    (retok (make-defind-conclusion-info :name pred-name :args arg-infos)
           state))
  :guard-hints (("Goal" :in-theory (enable character-alistp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-process-premise (prem
                                (desc msgp)
                                (pred-infos defind-pred-info-listp)
                                state)
  :guard (defind-pred-names-unambp pred-infos)
  :returns (mv erp (info defind-premise-infop) state)
  :short "Process the premise of a rule."
  :long
  (xdoc::topstring
   (xdoc::p
    "This may contain a @('p[i]') predicate,
     as in @(tsee defind-process-conclusion),
     or it may be some other term not involving
     the predicates being defined.")
   (xdoc::p
    "The @('desc') input of this function is
     a description of the premise, for error messages."))
  (b* (((reterr) (irr-defind-premise-info) state)
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
             ((erp arg-infos state)
              (defind-process-args args args-desc state)))
          (retok (make-defind-premise-info-pred :name pred-name
                                                :args arg-infos)
                 state))
      (b* ((desc (msg "Since ~@0 does not have the form of ~
                       one of the predicates among ~&1 applied to some terms, ~
                       it"
                      (msg-downcase-first desc) pred-names))
           ((erp info state) (defind-process-term prem desc state)))
        (retok (make-defind-premise-info-other :term info) state))))
  :no-function nil
  :guard-hints (("Goal" :in-theory (enable character-alistp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-process-premises (prems
                                 (irule-desc msgp)
                                 (pred-infos defind-pred-info-listp)
                                 state)
  :guard (defind-pred-names-unambp pred-infos)
  :returns (mv erp (infos defind-premise-info-listp) state)
  :short "Process the premises of a rule."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('irule-desc') input of this function is
     a description of the rule that the premises belong to;
     it is used for error message."))
  (b* (((reterr) nil state)
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
     :guard (defind-pred-names-unambp pred-infos)
     :returns (mv erp (infos defind-premise-info-listp) state)
     :parents nil
     (b* (((reterr) nil state)
          ((when (endp prems)) (retok nil state))
          (prem (car prems))
          (prem-desc
           (msg "The ~n0 premise of ~@1"
                (list (lposfix q))
                (msg-downcase-first irule-desc)))
          ((erp info state)
           (defind-process-premise prem prem-desc pred-infos state))
          ((erp infos state) (defind-process-premises-loop
                              (cdr prems) (1+ (lposfix q))
                              irule-desc pred-infos state)))
       (retok (cons info infos) state))
     :guard-hints (("Goal" :in-theory (enable character-alistp))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-process-irule (irule
                              (desc msgp)
                              (pred-infos defind-pred-info-listp)
                              state)
  :guard (defind-pred-names-unambp pred-infos)
  :returns (mv erp (info defind-irule-infop) state)
  :short "Process a rule."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('desc') input of this function is
     a description of the rule, for error messages."))
  (b* (((reterr) (irr-defind-irule-info) state)
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
       ((erp prem-infos state)
        (defind-process-premises prems desc pred-infos state))
       (concl-desc (msg "The conclusion of ~@0" (msg-downcase-first desc)))
       ((erp concl-info state)
        (defind-process-conclusion concl concl-desc pred-infos state)))
    (retok (make-defind-irule-info :name name
                                   :premises prem-infos
                                   :conclusion concl-info)
           state))
  :guard-hints (("Goal" :in-theory (enable character-alistp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-process-irules (irules
                               (irules-suppliedp booleanp)
                               (pred-infos defind-pred-info-listp)
                               state)
  :guard (defind-pred-names-unambp pred-infos)
  :returns (mv erp
               (infos defind-irule-info-listp)
               (leveled-cliques symbol-set-list-listp)
               state)
  :short "Process the @(':irules') input."
  :long
  (xdoc::topstring
   (xdoc::p
    "Besides processing the individual rules,
     we check that the rule names are unambiguous.
     Then we organize the predicates into
     cliques in dependency order, each organized into levels,
     and we use the result to enforce the restrictions described next.")
   (xdoc::p
    "We check that every predicate is in the conclusion of some rule.
     A predicate without rules has no proof trees,
     which is also captured by the check on levels described below,
     but we check it first, for a more informative error message.")
   (xdoc::p
    "The predicates do not have to be all mutually recursive,
     and they do not have to be recursive at all:
     they form one or more cliques,
     which we return in dependency order,
     so that the events for each clique are generated
     after the events for the cliques it depends on.
     A predicate that is not recursive forms a singleton clique,
     and yields a non-recursive proof validity function.")
   (xdoc::p
    "We also check that every predicate is at some level in its clique.
     A predicate at no level would have no proof trees:
     the generated fixtype of its proofs would be empty,
     but fixtypes, like all ACL2 types, must be non-empty;
     concretely, FTY would reject the generated fixtype,
     for lack of a base case.
     For a single predicate,
     being at some level amounts to being at level 0,
     i.e. to the existence of a non-recursive rule,
     which provides a base case for the inductive definition.
     For multiple predicates, it suffices that some of them are at level 0,
     with the others reachable from those through the levels.")
   (xdoc::p
    "We return the leveled cliques along with the rule information,
     for use in event generation."))
  (b* (((reterr) nil nil state)
       ((unless irules-suppliedp)
        (reterr (msg "The :IRULES input must be supplied.")))
       ((unless (and (true-listp irules)
                     (consp irules)))
        (reterr (msg "The :IRULES input must be a non-empty list, ~
                      but it is ~x0 instead."
                     irules)))
       ((erp infos state)
        (defind-process-irules-loop irules 1 pred-infos state))
       ((unless (defind-irule-names-unambp infos))
        (b* (((mv & irule-name pred-name) (defind-irule-name-clash infos)))
          (reterr (msg "The rules in the :IRULES input ~
                        with the same predicate in the conclusion ~
                        must have distinct names, ~
                        but the name ~x0 is used by more than one rule ~
                        with the predicate ~x1 in the conclusion."
                       irule-name pred-name))))
       (pred-names (defind-pred-info-list->name pred-infos))
       (ruleless-preds (defind-preds-without-irules pred-names infos))
       ((when (consp ruleless-preds))
        (reterr (msg "Every predicate being defined must be ~
                      in the conclusion of at least one rule ~
                      in the :IRULES input. ~
                      This does not hold for ~&0. ~
                      A predicate without rules would have no proofs, ~
                      and thus it would be empty."
                     ruleless-preds)))
       ((mv leveled-cliques unleveled)
        (defind-leveled-cliques pred-names infos))
       ((unless (set::emptyp unleveled))
        (reterr (msg "Every predicate being defined ~
                      must be at some level: ~
                      a predicate is at level 0 if ~
                      some rule in the :IRULES input ~
                      has the predicate as its conclusion ~
                      and no premises that are ~
                      calls of the predicates being defined; ~
                      a predicate is at a higher level if ~
                      some rule has the predicate as its conclusion ~
                      and all its premises that are ~
                      calls of the predicates being defined ~
                      call predicates at lower levels. ~
                      This does not hold for ~&0. ~
                      For a predicate at no level, ~
                      the generated fixtype of its proofs would be empty, ~
                      but fixtypes must be non-empty."
                     unleveled))))
    (retok infos leveled-cliques state))
  :guard-hints
  (("Goal"
    :in-theory (enable consp-under-iff-when-true-listp-no-backchain-limit
                       true-listp-when-symbol-set-list-listp)))

  :prepwork
  ((define defind-process-irules-loop ((irules true-listp)
                                       (k posp)
                                       (pred-infos defind-pred-info-listp)
                                       state)
     :guard (defind-pred-names-unambp pred-infos)
     :returns (mv erp (infos defind-irule-info-listp) state)
     :parents nil
     (b* (((reterr) nil state)
          ((when (endp irules)) (retok nil state))
          (desc (msg "The ~n0 element of the :IRULES input" (list (lposfix k))))
          ((erp info state)
           (defind-process-irule (car irules) desc pred-infos state))
          ((erp infos state) (defind-process-irules-loop
                              (cdr irules) (1+ (lposfix k))
                              pred-infos state)))
       (retok (cons info infos) state))
     :guard-hints (("Goal" :in-theory (enable character-alistp)))))

  ///

  (defret defind-irule-names-unambp-of-defind-process-irules
    (defind-irule-names-unambp infos)))

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

(define defind-process-print (print)
  :returns (mv erp (print evmac-input-print-p))
  :short "Process the @(':print') input."
  (b* (((reterr) :error)
       ((unless (evmac-input-print-p print))
        (reterr (msg "The :PRINT input must be ~
                      :ERROR, :RESULT, :INFO, or :ALL, ~
                      but it is ~x0 instead."
                     print))))
    (retok print)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-check-proof-names ((irule-infos defind-irule-info-listp)
                                  (pred-infos defind-pred-info-listp)
                                  (name symbolp))
  :guard (defind-pred-names-unambp pred-infos)
  :returns (erp "@('nil') or an error message.")
  :short "Check that the variables of the rules do not clash with
          the names that the generated events reserve."
  :long
  (xdoc::topstring
   (xdoc::p
    "A summand of a @('p[i]-proof') fixtype has a field
     for each variable of the rule,
     so a variable that is also the @(':xvar') of the fixtype,
     or the name of one of the premise fields,
     makes FTY reject the fixtype.
     A variable that is also one of the variables
     for the arguments of the conclusion is worse:
     it shadows the formal of the @('p[i]-proof-validp') function
     in the case for the rule,
     which turns the equality for that argument of the conclusion
     into an equality of the field with itself,
     silently defining the wrong relation.")
   (xdoc::p
    "We take the names of the premise fields from
     @(tsee defind-gen-prem-fields),
     so that this check cannot drift from what is generated.
     This is why this check is here,
     among the event generation code,
     instead of with the rest of the input processing;
     it also needs the name of the macro call,
     which is not available in that phase.")
   (xdoc::p
    "We do not check the proof variable, @(tsee defind-proof-var-name):
     a rule variable with that name may shadow it without harm,
     because the case macro binds the fields of the proof
     before the shadowing takes place;
     see @(tsee defind-proof-xvar-name)."))
  (b* (((reterr))
       ((when (endp irule-infos)) (retok))
       ((defind-irule-info info) (car irule-infos))
       (pred-name (defind-conclusion-info->name info.conclusion))
       (pinfo (defind-lookup-pred pred-name pred-infos))
       ((unless pinfo) (retok)) ; never happens: checked while processing
       (reserved
        (cons (defind-proof-xvar-name name)
              (append (defind-proof-concl-var-names
                        (defind-pred-info->formals pinfo) name)
                      (defind-prem-field-names (len info.premises) name))))
       (clashing (intersection-eq (defind-irule-info-free-vars info) reserved))
       ((when clashing)
        (reterr (msg "The variables of a rule must differ from ~
                      the variables and field names that ~
                      the generated events use for ~
                      the arguments of the conclusion and the proofs. ~
                      This does not hold for the rule ~x0, ~
                      whose variables include ~&1."
                     info.name clashing))))
    (defind-check-proof-names (cdr irule-infos) pred-infos name))
  :guard-hints (("Goal" :in-theory (enable symbol-listp-when-symbol-setp
                                           set::sets-are-true-lists))))

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
                               print
                               state)
  :returns (mv erp
               (name symbolp)
               (pred-infos defind-pred-info-listp)
               (irule-infos defind-irule-info-listp)
               (leveled-cliques symbol-set-list-listp)
               (parents symbol-listp)
               short
               long
               (xdocp booleanp)
               (print evmac-input-print-p)
               state)
  :short "Process all the inputs."
  (b* (((reterr) nil nil nil nil nil nil nil nil :error state)
       (wrld (w state))
       ((erp name) (defind-process-name name wrld))
       ((erp pred-infos)
        (defind-process-preds preds preds-suppliedp wrld))
       ((erp irule-infos leveled-cliques state)
        (defind-process-irules irules irules-suppliedp pred-infos state))
       ((erp) (defind-check-proof-names irule-infos pred-infos name))
       ((erp parents short long xdocp)
        (defind-process-parents/short/long
          parents parents-suppliedp
          short short-suppliedp
          long long-suppliedp))
       ((erp print) (defind-process-print print)))
    (retok name pred-infos irule-infos leveled-cliques
           parents short long xdocp print state))

  ///

  (defret defind-pred-names-unambp-of-defind-process-inputs-preds
    (defind-pred-names-unambp pred-infos))

  (defret defind-irule-names-unambp-of-defind-process-inputs-irules
    (defind-irule-names-unambp irule-infos)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-event-generation definductive)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-conjunction ((conjuncts true-listp))
  :returns (term "An untranslated term.")
  :short "Generate a conjunction of zero or more untranslated terms."
  :long
  (xdoc::topstring
   (xdoc::p
    "If there are no conjuncts, we generate @('t').
     If there is exactly one conjunct, we generate that conjunct.
     If there are two or more conjuncts, we generate an @(tsee and) of them.
     This way, we avoid generating empty and singleton conjunctions."))
  (cond ((endp conjuncts) t)
        ((endp (cdr conjuncts)) (car conjuncts))
        (t `(and ,@(true-list-fix conjuncts)))))

;;;;;;;;;;;;;;;;;;;;

(define defind-gen-implication ((antecedents true-listp) consequent)
  :returns (term "An untranslated term.")
  :short "Generate an implication of a consequent
          from zero or more antecedents,
          all untranslated terms."
  :long
  (xdoc::topstring
   (xdoc::p
    "If there are no antecedents, we generate just the consequent.
     Otherwise, we generate an @(tsee implies)
     whose antecedent is the conjunction of the antecedents.
     This way, we avoid generating implications with trivial antecedents."))
  (if (consp antecedents)
      `(implies ,(defind-gen-conjunction antecedents) ,consequent)
    consequent))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-name-defxdoc+ ((name symbolp)
                                  (parents symbol-listp)
                                  short
                                  long
                                  (xdocp booleanp)
                                  (print evmac-input-print-p))
  :returns (events pseudo-event-form-listp)
  :short "Generate the @(tsee defxdoc+) for @('name'),
          if XDOC must be generated."
  (b* (((unless xdocp) nil)
       (name (symbol-lfix name))
       (xdoc-event
        `(defxdoc+ ,name
           ,@(and (consp parents)
                  (list :parents (symbol-list-fix parents)))
           ,@(and short
                  (list :short short))
           ,@(and long
                  (list :long long))
           :order-subtopics t
           :default-parent ,name))
       (print-event?
        (and (evmac-input-print->= print :result)
             `((cw-event "XDOC topic ~x0.~%" ',name)))))
    (cons xdoc-event print-event?))
  :type-prescription
  (true-listp (defind-gen-name-defxdoc+ name parents short long xdocp print)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-preds-doc-string ((pred-names symbol-listp))
  :returns (doc-string stringp)
  :short "Generate a documentation string listing predicate names."
  (b* (((when (endp pred-names)) "")
       (first-string
        (str::cat "@('"
                  (str::downcase-string
                   (symbol-name (symbol-lfix (car pred-names))))
                  "')"))
       ((when (endp (cdr pred-names))) first-string))
    (str::cat first-string
              ", "
              (defind-preds-doc-string (cdr pred-names)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-var-fields ((vars symbol-listp))
  :returns (fields true-list-listp)
  :short "Generate the variable fields of
          a summand of a @('p[i]-proof') fixtype."
  :long
  (xdoc::topstring
   (xdoc::p
    "The summand corresponds to an inference rule,
     and it has one field for each variable of the rule:
     the field is named after the variable and has no type.
     These fields are what lets the conclusion be
     an argument of the proof validity predicate,
     instead of a field of the proof."))
  (if (endp vars)
      nil
    (cons (list (symbol-lfix (car vars)))
          (defind-gen-var-fields (cdr vars)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-prem-fields ((infos defind-premise-info-listp)
                                (num posp)
                                (name symbolp))
  :returns (fields (and (true-list-listp fields)
                        (alistp fields))
                   :hints (("Goal" :induct t :in-theory (enable alistp))))
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
       (fields
        (defind-gen-prem-fields (cdr infos) (1+ (lposfix num)) name)))
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
       (var-fields
        (defind-gen-var-fields (defind-irule-info-free-vars info)))
       (prem-fields (defind-gen-prem-fields info.premises 1 name)))
    `(,tag (,@var-fields ,@prem-fields)))
  :guard-hints (("Goal" :in-theory (enable symbol-listp-when-symbol-setp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-proof-summands ((pred-name symbolp)
                                   (infos defind-irule-info-listp)
                                   (name symbolp))
  :guard (defind-irule-names-unambp infos)
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
                                    (levels symbol-set-listp)
                                    (preds-in-previous-cliques symbol-setp)
                                    (prepworkp booleanp)
                                    (name symbolp)
                                    (xdocp booleanp)
                                    (print evmac-input-print-p))
  :guard (defind-irule-names-unambp infos)
  :returns (mv (deftagsum-event pseudo-event-formp)
               (print-event? pseudo-event-form-listp))
  :short "Generate a @('p[i]-proof') fixtype."
  :long
  (xdoc::topstring
   (xdoc::p
    "The predicate is specified by its name, passed as input.
     The @('levels') input consists of
     the levels of the clique of the predicate;
     the @('preds-in-previous-cliques') input consists of
     the predicates in the preceding cliques.")
   (xdoc::p
    "If some predicate of the clique is at level 1 or more,
     every proof fixtype of the clique needs a measure,
     which lexicographically combines
     the size of the value with the level of the predicate;
     furthermore, the proof fixtypes of
     the predicates at level 1 or more
     need a base case override,
     which references the summand of a rule that
     derives the predicate from predicates
     at lower levels or in previous cliques.
     Neither is generated for a predicate that forms a singleton clique,
     which is necessarily at level 0.")
   (xdoc::p
    "The @('prepworkp') input determines whether the fixtype includes
     a @(':prepwork') that limits the induction depth:
     this is done when the fixtype is standalone;
     when the fixtype is inside
     a clique of mutually recursive fixtypes,
     the limit is in the enclosing @(tsee fty::deftypes) instead.")
   (xdoc::p
    "The @(':xvar') option is necessary:
     since the fields are named after the variables of the rules,
     the default @('x') would clash with a rule variable @('x'),
     which FTY rejects with a hard error.
     We use @(tsee defind-proof-xvar-name),
     which @(tsee defind-check-proof-names) establishes to be distinct from
     the variables of the rules."))
  (b* ((xvar (defind-proof-xvar-name name))
       (summands (defind-gen-proof-summands pred-name infos name))
       (measurep (consp (cdr (symbol-set-list-fix levels))))
       (level (defind-pred-level pred-name levels))
       (override-rule (and (< 0 level)
                           (defind-pred-override-rule
                             pred-name level levels
                             preds-in-previous-cliques infos)))
       (type-name (defind-proof-type-name pred-name name))
       (deftagsum-event
         `(fty::deftagsum ,type-name
            ,@(and xdocp
                   `(:parents (,(symbol-lfix name))
                     :short ,(str::cat
                              "Fixtype of proofs for predicate @('"
                              (str::downcase-string (symbol-name
                                                     (symbol-lfix pred-name)))
                              "').")))
            ,@summands
            ,@(and override-rule
                   `(:base-case-override ,(defind-irule-tag override-rule)))
            ,@(and measurep
                   `(:measure (two-nats-measure (acl2-count ,xvar) ,level)))
            :pred ,(defind-proof-recog-name pred-name name)
            :xvar ,xvar
            ,@(and prepworkp
                   '(:prepwork ((set-induction-depth-limit 1))))))
       (print-event?
        (and (evmac-input-print->= print :result)
             `((cw-event "Fixtype ~x0.~%" ',type-name)))))
    (mv deftagsum-event print-event?)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-proof-deftagsums ((pred-infos defind-pred-info-listp)
                                     (irule-infos defind-irule-info-listp)
                                     (levels symbol-set-listp)
                                     (preds-in-previous-cliques symbol-setp)
                                     (prepworkp booleanp)
                                     (name symbolp)
                                     (xdocp booleanp)
                                     (print evmac-input-print-p))
  :guard (and (defind-pred-names-unambp pred-infos)
              (defind-irule-names-unambp irule-infos))
  :returns (mv (deftagsum-events pseudo-event-form-listp)
               (print-events pseudo-event-form-listp))
  :short "Generate the @('p[i]-proof') fixtypes."
  (b* (((when (endp pred-infos)) (mv nil nil))
       (pred-name (defind-pred-info->name (car pred-infos)))
       ((mv deftagsum-event print-event?)
        (defind-gen-proof-deftagsum pred-name irule-infos
          levels preds-in-previous-cliques prepworkp name xdocp print))
       ((mv deftagsum-events print-events)
        (defind-gen-proof-deftagsums
          (cdr pred-infos) irule-infos
          levels preds-in-previous-cliques prepworkp name xdocp print)))
    (mv (cons deftagsum-event deftagsum-events)
        (append print-event? print-events))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-proof-fixtypes ((pred-infos defind-pred-info-listp)
                                   (irule-infos defind-irule-info-listp)
                                   (leveled-cliques symbol-set-list-listp)
                                   (name symbolp)
                                   (xdocp booleanp)
                                   (print evmac-input-print-p))
  :guard (and (defind-pred-names-unambp pred-infos)
              (defind-irule-names-unambp irule-infos))
  :returns (events pseudo-event-form-listp)
  :short "Generate the fixtypes of proofs, for all the cliques."
  :long
  (xdoc::topstring
   (xdoc::p
    "We generate one event per clique, in dependency order.
     For a clique of a single predicate,
     the event is the fixtype of proofs of the predicate.
     For a clique of multiple predicates,
     the event is a @(tsee fty::deftypes)
     with the mutually recursive fixtypes of proofs
     of the predicates of the clique;
     the @(tsee fty::deftypes) is named after
     the first predicate of the clique,
     and it includes the induction depth limit
     that is otherwise in the standalone fixtypes."))
  (defind-gen-proof-fixtypes-loop
    leveled-cliques nil pred-infos irule-infos name xdocp print)
  :type-prescription (true-listp (defind-gen-proof-fixtypes
                                   pred-infos irule-infos leveled-cliques
                                   name xdocp print))

  :prepwork

  ((define defind-gen-proof-fixtypes-loop
     ((leveled-cliques symbol-set-list-listp)
      (preds-in-previous-cliques symbol-setp)
      (pred-infos defind-pred-info-listp)
      (irule-infos defind-irule-info-listp)
      (name symbolp)
      (xdocp booleanp)
      (print evmac-input-print-p))
     :guard (and (defind-pred-names-unambp pred-infos)
                 (defind-irule-names-unambp irule-infos))
     :returns (events pseudo-event-form-listp)
     :parents nil
     (b* (((when (endp leveled-cliques)) nil)
          (levels (symbol-set-list-fix (car leveled-cliques)))
          (clique-preds (set::set-list-union levels))
          (clique-pred-infos (defind-lookup-pred-set clique-preds pred-infos))
          (events-rest (defind-gen-proof-fixtypes-loop
                         (cdr leveled-cliques)
                         (set::union clique-preds
                                     (symbol-sfix preds-in-previous-cliques))
                         pred-infos irule-infos name xdocp print))
          ((unless (consp clique-pred-infos))
           (raise "Internal error: no predicates in clique with levels ~x0."
                  levels)
           events-rest)
          ((mv type-event print-events)
           (if (endp (cdr clique-pred-infos))
               (defind-gen-proof-deftagsum
                 (defind-pred-info->name (car clique-pred-infos))
                 irule-infos levels preds-in-previous-cliques
                 t name xdocp print)
             (b* (((mv deftagsum-events print-events)
                   (defind-gen-proof-deftagsums
                     clique-pred-infos irule-infos
                     levels preds-in-previous-cliques
                     nil name xdocp print))
                  (deftypes-name
                    (defind-proof-type-clique-name
                      (defind-pred-info->name (car clique-pred-infos))
                      name)))
               (mv `(fty::deftypes ,deftypes-name
                      ,@(and xdocp
                             `(:parents (,(symbol-lfix name))
                               :short ,(str::cat
                                        "Fixtypes of proofs for predicates "
                                        (defind-preds-doc-string
                                         (defind-pred-info-list->name
                                          clique-pred-infos))
                                        ".")))
                      ,@deftagsum-events
                      :prepwork ((set-induction-depth-limit 1)))
                   print-events)))))
       (cons type-event (append print-events events-rest)))
     :no-function nil
     :guard-hints
     (("Goal" :in-theory (enable set-listp-when-symbol-set-listp))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-irule-valid-fn-prems
  ((infos defind-premise-info-listp))
  :returns (conjuncts true-listp)
  :short "Generate the conjuncts for the premises of an inference rule
          in a @('p[l[k]]-rule[k]-validp') function."
  :long
  (xdoc::topstring
   (xdoc::p
    "Only the premises that are not calls of the predicates being defined
     contribute:
     the other ones are checked
     against the proofs of those premises
     in the @('p[i]-proof-validp') function.
     The premises are used as written
     because the variables of the rule are formals of this function."))
  (b* (((when (endp infos)) nil)
       (info (car infos))
       ((when (defind-premise-info-case info :pred))
        (defind-gen-irule-valid-fn-prems (cdr infos)))
       (conjunct (defind-term-info->uterm
                  (defind-premise-info-other->term info))))
    (cons conjunct
          (defind-gen-irule-valid-fn-prems (cdr infos)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-irule-valid-fn-concl ((args defind-term-info-listp)
                                         (concl-vars symbol-listp))
  :returns (conjuncts true-listp)
  :short "Generate the conjuncts for the conclusion of an inference rule
          in a @('p[l[k]]-rule[k]-validp') function."
  :long
  (xdoc::topstring
   (xdoc::p
    "There is an equality for each argument of the conclusion,
     between the corresponding formal of the function
     and the argument as written.
     The two lists have the same length
     because the arity of the conclusion is checked during input processing."))
  (b* (((when (or (endp args) (endp concl-vars))) nil)
       (conjunct `(equal ,(symbol-lfix (car concl-vars))
                         ,(defind-term-info->uterm (car args)))))
    (cons conjunct
          (defind-gen-irule-valid-fn-concl
            (cdr args) (cdr concl-vars)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-irule-valid-fn ((info defind-irule-infop)
                                   (concl-vars symbol-listp)
                                   (name symbolp)
                                   (xdocp booleanp)
                                   (print evmac-input-print-p))
  :returns (events pseudo-event-form-listp)
  :short "Generate a @('p[l[k]]-rule[k]-validp') function."
  :long
  (xdoc::topstring
   (xdoc::p
    "This checks the conditions of the rule
     that do not involve the proofs of the premises,
     i.e. the premises that are not calls of the predicates being defined,
     and the equalities between the arguments of the conclusion
     and the ones that the rule derives.")
   (xdoc::p
    "This is never a @(tsee std::define-sk):
     the variables of the rule are formals of the function,
     which the caller supplies from the fields of the proof,
     and so there is nothing to quantify.
     For the same reason,
     there is no need to distinguish ground rules from non-ground ones.")
   (xdoc::p
    "All the variables of the rule are formals,
     including the ones that occur only in the premises
     that are calls of the predicates being defined,
     which therefore do not occur in the body;
     hence the @(':ignore-ok').
     Those formals are also irrelevant in the sense of
     @(see acl2::irrelevant-formals);
     hence the @(':irrelevant-formals-ok'),
     which is needed anyway
     because a premise or an argument of the conclusion
     could make a formal irrelevant,
     e.g. a premise @('(or t ...)')."))
  (b* (((defind-irule-info info))
       ((defind-conclusion-info cinfo) info.conclusion)
       (fn-name (defind-irule-valid-fn-name cinfo.name info.name name))
       (vars (defind-irule-info-free-vars info))
       (prem-conjuncts (defind-gen-irule-valid-fn-prems info.premises))
       (concl-conjuncts
        (defind-gen-irule-valid-fn-concl cinfo.args concl-vars))
       (body (defind-gen-conjunction
               (append prem-conjuncts concl-conjuncts)))
       (fn-event
        `(define ,fn-name (,@(symbol-list-fix concl-vars)
                           ,@(symbol-list-fix vars))
           :returns (yes/no booleanp
                            :rule-classes (:rewrite :type-prescription)
                            :hints (("Goal" :in-theory '(,fn-name booleanp))))
           ,@(and xdocp
                  `(:parents (,(symbol-lfix name))
                    :short ,(str::cat
                             "Validity of an instance of the rule @('"
                             (str::downcase-string (symbol-name info.name))
                             "'), except for the proofs of its premises.")))
           ,body
           :verify-guards nil
           :ignore-ok t
           :irrelevant-formals-ok t))
       (print-event?
        (and (evmac-input-print->= print :result)
             `((cw-event "Function ~x0.~%" ',fn-name)))))
    (cons fn-event print-event?))
  :guard-hints (("Goal" :in-theory (enable symbol-listp-when-symbol-setp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-irule-valid-fns ((infos defind-irule-info-listp)
                                    (pred-infos defind-pred-info-listp)
                                    (name symbolp)
                                    (xdocp booleanp)
                                    (print evmac-input-print-p))
  :guard (defind-pred-names-unambp pred-infos)
  :returns (events pseudo-event-form-listp)
  :short "Generate the @('p[l[k]]-rule[k]-validp') functions."
  (b* (((when (endp infos)) nil)
       ((defind-irule-info info) (car infos))
       (pred-name (defind-conclusion-info->name info.conclusion))
       (pinfo (defind-lookup-pred pred-name pred-infos))
       ((unless pinfo)
        (raise "Internal error: predicate ~x0 not found." pred-name))
       (concl-vars (defind-proof-concl-var-names
                     (defind-pred-info->formals pinfo) name))
       (events (defind-gen-irule-valid-fn
                 (car infos) concl-vars name xdocp print))
       (more-events (defind-gen-irule-valid-fns
                      (cdr infos) pred-infos name xdocp print)))
    (append events more-events))
  :no-function nil
  :type-prescription (true-listp (defind-gen-irule-valid-fns
                                   infos pred-infos name xdocp print)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-proof-valid-fn-case-bindings ((vars symbol-listp)
                                                 (name symbolp))
  :returns (bindings true-list-listp)
  :short "Generate the @(tsee let) bindings for the variables of a rule
          in a case of a @('p[i]-proof-validp') function."
  :long
  (xdoc::topstring
   (xdoc::p
    "Each variable of the rule is bound to the field of the proof
     named after it, which the case macro binds in turn.
     This is what lets the arguments of the premises
     that are calls of the predicates being defined
     be used as written with no substitution:
     we would need to translate the terms before substituting into them
     because in an untranslated term
     a variable may also occur inside a quoted constant.")
   (xdoc::p
    "These bindings are only needed by a rule
     that has premises that are calls of the predicates being defined;
     otherwise the variables are used
     just as arguments of the @('p[l[k]]-rule[k]-validp') function,
     which the caller passes directly."))
  (cond ((endp vars) nil)
        (t (cons (list (symbol-lfix (car vars))
                       (defind-proof-var-field-var-name (car vars) name))
                 (defind-gen-proof-valid-fn-case-bindings (cdr vars) name)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-proof-valid-fn-case-prems ((infos defind-premise-info-listp)
                                              (pred-name symbolp)
                                              (irule-name symbolp)
                                              (num posp)
                                              (name symbolp))
  :returns (mv (conjuncts true-listp)
               (count-thms symbol-listp)
               (fixing-thms symbol-listp))
  :short "Generate the conjuncts for the proofs of the premises
          of an inference rule
          in a case of a @('p[i]-proof-validp') function,
          along with the names of some relevant theorems."
  :long
  (xdoc::topstring
   (xdoc::p
    "Only the premises that are calls of the predicates being defined
     contribute.
     Each becomes a call of @('p[j]-proof-validp')
     on the proof of the premise
     and on the arguments of the premise as written.")
   (xdoc::p
    "Two different predicates are involved:
     the one of the premise, which determines
     the validity predicate applied to the proof of the premise,
     and the one of the conclusion of the rule, i.e. @('pred-name'),
     which determines the fixtype of proofs
     that has the summand for the rule,
     and thus the accessors of the proofs of the premises
     along with the theorems about them.")
   (xdoc::p
    "We return a count theorem only for the premises
     whose predicate is the one of the conclusion.
     These theorems are used in the termination proof of
     a standalone proof validity function,
     where those are exactly the premises that
     give rise to the recursive calls.
     FTY generates no such theorem for a premise
     whose fixtype of proofs is not in the same clique
     as the one of the conclusion:
     for a clique of multiple predicates,
     the termination proof expands the count functions instead."))
  (b* (((when (endp infos)) (mv nil nil nil))
       (info (car infos)))
    (defind-premise-info-case
      info
      :pred (b* ((valid-fn (defind-proof-valid-fn-name info.name name))
                 (prem-proof-var (defind-proof-prem-var-name num name))
                 (conjunct `(,valid-fn ,prem-proof-var
                                       ,@(defind-term-info-list->uterm
                                          info.args)))
                 (count-thm (and (equal info.name
                                        (symbol-lfix pred-name))
                                 (defind-proof-prem-count-thm-name
                                   info.name pred-name
                                   irule-name num name)))
                 (fixing-thm (defind-proof-prem-fixing-thm-name
                              pred-name irule-name num name))
                 ((mv conjuncts count-thms fixing-thms)
                  (defind-gen-proof-valid-fn-case-prems
                    (cdr infos) pred-name irule-name (1+ (lposfix num)) name)))
              (mv (cons conjunct conjuncts)
                  (if count-thm (cons count-thm count-thms) count-thms)
                  (cons fixing-thm fixing-thms)))
      :other (defind-gen-proof-valid-fn-case-prems
               (cdr infos) pred-name irule-name num name))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-proof-valid-fn-case ((info defind-irule-infop)
                                        (concl-vars symbol-listp)
                                        (name symbolp))
  :returns (mv (keyword+term true-listp)
               (return-thm symbolp)
               (count-thms symbol-listp)
               (prem-fixing-thms symbol-listp)
               (var-fixing-thms symbol-listp))
  :short "Generate a case of a @('p[i]-proof-validp') function,
          along with the names of some relevant theorems."
  :long
  (xdoc::topstring
   (xdoc::p
    "The conjuncts for the proofs of the premises come first,
     followed by a call of the @('p[l[k]]-rule[k]-validp') function
     on the arguments of the conclusion and on the variables of the rule.
     If the rule has premises that are calls of the predicates being defined,
     the variables of the rule are bound around the whole conjunction
     and passed as such to that call;
     otherwise there are no bindings,
     and the fields of the proof are passed directly."))
  (b* (((defind-irule-info info))
       ((defind-conclusion-info cinfo) info.conclusion)
       (tag (defind-irule-tag info.name))
       (vars (defind-irule-info-free-vars info))
       (recursivep (defind-irule-info-recursivep info))
       (valid-irule-fn
        (defind-irule-valid-fn-name cinfo.name info.name name))
       ((mv prem-conjuncts count-thms prem-fixing-thms)
        (defind-gen-proof-valid-fn-case-prems
          info.premises cinfo.name info.name 1 name))
       (var-args (if recursivep
                     (symbol-list-fix vars)
                   (defind-proof-var-field-var-names vars name)))
       (irule-conjunct `(,valid-irule-fn
                         ,@(symbol-list-fix concl-vars)
                         ,@var-args))
       (term (defind-gen-conjunction
              (append prem-conjuncts (list irule-conjunct))))
       (bindings (and recursivep
                      (defind-gen-proof-valid-fn-case-bindings vars name)))
       (term (if bindings `(let ,bindings ,term) term))
       (return-thm
        (defind-irule-valid-return-thm-name cinfo.name info.name name))
       (var-fixing-thms (defind-proof-var-acc-fixing-thm-names
                         cinfo.name info.name vars name)))
    (mv `(,tag ,term)
        return-thm count-thms prem-fixing-thms var-fixing-thms))
  :guard-hints (("Goal" :in-theory (enable symbol-listp-when-symbol-setp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-proof-valid-fn-cases ((pred-name symbolp)
                                         (concl-vars symbol-listp)
                                         (infos defind-irule-info-listp)
                                         (name symbolp))
  :guard (defind-irule-names-unambp infos)
  :returns (mv (keywords+terms true-listp)
               (return-thms symbol-listp)
               (count-thms symbol-listp)
               (prem-fixing-thms symbol-listp)
               (var-fixing-thms symbol-listp))
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
        (defind-gen-proof-valid-fn-cases
          pred-name concl-vars (cdr infos) name))
       ((mv keyword+term return-thm count-thms prem-fixing-thms var-fixing-thms)
        (defind-gen-proof-valid-fn-case info concl-vars name))
       ((mv keywords+terms
            more-return-thms
            more-count-thms
            more-prem-fixing-thms
            more-var-fixing-thms)
        (defind-gen-proof-valid-fn-cases
          pred-name concl-vars (cdr infos) name)))
    (mv (cons keyword+term keywords+terms)
        (cons return-thm more-return-thms)
        (append count-thms more-count-thms)
        (append prem-fixing-thms more-prem-fixing-thms)
        (append var-fixing-thms more-var-fixing-thms))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-proof-valid-fn ((pred-info defind-pred-infop)
                                   (infos defind-irule-info-listp)
                                   (standalonep booleanp)
                                   (name symbolp)
                                   (xdocp booleanp)
                                   (print evmac-input-print-p))
  :guard (defind-irule-names-unambp infos)
  :returns (mv (fn-event pseudo-event-formp)
               (print-event? pseudo-event-form-listp))
  :short "Generate a @('p[i]-proof-validp') function."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('standalonep') input says whether the function is standalone,
     which is the case when the predicate forms a singleton clique;
     otherwise, the function is a member of the @(tsee defines)
     generated for a clique of multiple predicates.")
   (xdoc::p
    "For a standalone function,
     we generate termination hints as part of the function,
     as well as fixing theorems and hints for the function.
     If the predicate is not recursive,
     the @('p[i]-proof') fixtype is not recursive,
     so the function is not recursive either:
     in that case, we omit the @(':measure'),
     termination hints,
     and @(':induct') hints.
     For a predicate that forms a singleton clique,
     the predicate is recursive
     exactly when some rule with the predicate as conclusion
     also has the predicate in some premise.")
   (xdoc::p
    "For a function that is not standalone,
     the measure is always generated,
     but the termination hints,
     the fixing equivalence,
     and the guard non-verification
     are in the enclosing @(tsee defines).")
   (xdoc::p
    "This takes the information about the predicate, not just its name,
     because the arguments of the conclusion are formals of this function;
     see @(tsee defind-proof-concl-var-names).")
   (xdoc::p
    "The @(':returns') theorem is also a type prescription rule,
     which @(tsee defind-gen-pred) uses."))
  (b* (((defind-pred-info pred-info))
       (fn-name (defind-proof-valid-fn-name pred-info.name name))
       (fn-formal (defind-proof-var-name name))
       (proof-recog (defind-proof-recog-name pred-info.name name))
       (proof-case (defind-proof-case-name pred-info.name name))
       (concl-vars (defind-proof-concl-var-names pred-info.formals name))
       ((mv keywords+terms
            return-thms
            count-thms
            prem-fixing-thms
            var-fixing-thms)
        (defind-gen-proof-valid-fn-cases
          pred-info.name concl-vars infos name))
       (count-fn (defind-proof-count-fn-name pred-info.name name))
       (print-event?
        (and (evmac-input-print->= print :result)
             `((cw-event "Function ~x0.~%" ',fn-name))))
       ((unless standalonep)
        (mv `(define ,fn-name ((,fn-formal ,proof-recog) ,@concl-vars)
               :returns (yes/no booleanp
                                :rule-classes (:rewrite :type-prescription))
               ,@(and xdocp
                      `(:parents (,(symbol-lfix name))
                        :short ,(str::cat "Validity of a proof for @('"
                                          (str::downcase-string
                                           (symbol-name pred-info.name))
                                          "').")))
               (,proof-case ,fn-formal ,@keywords+terms)
               :measure (,count-fn ,fn-formal))
            print-event?))
       (recursivep (defind-pred-recursivep pred-info.name infos))
       (poss-thm (defind-proof-kind-poss-thm-name pred-info.name name))
       (kind-fixing-thm (defind-proof-kind-fixing-thm-name
                         pred-info.name name)))
    (mv `(define ,fn-name ((,fn-formal ,proof-recog) ,@concl-vars)
           :returns (yes/no booleanp
                            :rule-classes (:rewrite :type-prescription)
                            :hints (("Goal"
                                     ,@(and recursivep '(:induct t))
                                     :in-theory '(,fn-name
                                                  (:e booleanp)
                                                  ,@return-thms))))
           ,@(and xdocp
                  `(:parents (,(symbol-lfix name))
                    :short ,(str::cat "Validity of proofs for predicate @('"
                                      (str::downcase-string
                                       (symbol-name pred-info.name))
                                      "').")))
           (,proof-case ,fn-formal ,@keywords+terms)
           ,@(and recursivep
                  `(:measure (,count-fn ,fn-formal)
                    :hints (("Goal" :in-theory '(o-p
                                                 o-finp
                                                 o<
                                                 (:t ,count-fn)
                                                 (:e tau-system)
                                                 ,poss-thm
                                                 ,@count-thms)))))
           :verify-guards nil
           :hooks ((:fix :hints (("Goal"
                                  ,@(and recursivep '(:induct t))
                                  :in-theory '(,fn-name
                                               ,kind-fixing-thm
                                               ,@prem-fixing-thms
                                               ,@var-fixing-thms))))))
        print-event?)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-proof-valid-fn-clique ((clique-pred-infos
                                           defind-pred-info-listp)
                                          (irule-infos defind-irule-info-listp)
                                          (name symbolp)
                                          (xdocp booleanp)
                                          (print evmac-input-print-p))
  :guard (and (consp clique-pred-infos)
              (defind-pred-names-unambp clique-pred-infos)
              (defind-irule-names-unambp irule-infos))
  :returns (events pseudo-event-form-listp)
  :short "Generate a @(tsee defines) with
          the @('p[i]-proof-validp') functions of
          a clique of multiple predicates."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @(tsee defines) is named after
     the first predicate of the clique.
     The termination hints expand the count functions of
     the fixtypes of proofs of the clique:
     the generated linear rules that relate the counts of the fields
     to the counts of the containing values
     have hypotheses about the summand kinds,
     which are not in the context for fixtypes with a single summand.
     The flag function is non-local because
     the minimality theorems, generated later,
     are proved by flag induction.
     The fixing equivalence of the functions
     is proved at the end, all together.")
   (xdoc::p
    "The hints for the fixing equivalence include @(':expand') hints
     for the calls of the validity functions
     on the proof variable and on its fixed version
     (in both cases with the conclusion arguments).
     Since the functions of the clique are mutually recursive,
     ACL2's heuristics do not expand those calls during the flag induction.
     This is unlike the case of a predicate that forms a singleton clique,
     where the induction is on the (single) validity function itself,
     and thus the calls of that function in the fixing equivalence
     are expanded as part of the induction.")
   (xdoc::p
    "The quoted theories of
     the termination hints and of the fixing equivalence use,
     for the count functions and for the rule validity predicates,
     the proved theorems instead of
     the type prescriptions that ACL2 infers:
     the return theorem of the count function,
     and the @(':returns') theorem of each rule validity predicate,
     which is also a type prescription rule
     (see @(tsee defind-gen-irule-valid-fn)).")
   (xdoc::p
    "We do not supply the induction hint of the fixing equivalence,
     for the reason given in
     @(tsee defind-gen-pred-alt-when-proof-valid-thm-clique):
     the flag function takes the arguments of the conclusions
     of all the predicates of the clique,
     and the flag machinery supplies the call on its formals."))
  (b* (((mv fn-events
            print-events
            expands
            term-thms
            fixequiv-expands
            fixequiv-thms)
        (defind-gen-proof-valid-fn-clique-loop
          clique-pred-infos irule-infos name xdocp print))
       ((mv valid-tps prem-acc-thms)
        (defind-gen-proof-valid-fn-clique-rules-loop
          irule-infos
          (defind-pred-info-list->name clique-pred-infos)
          name))
       (first-pred (defind-pred-info->name (car clique-pred-infos)))
       (defines-name (defind-proof-valid-fn-clique-name first-pred name))
       (flag-fn (defind-proof-valid-fn-clique-flag-name first-pred name)))
    (cons
     `(defines ,defines-name
        ,@(and xdocp
               `(:parents (,(symbol-lfix name))
                 :short ,(str::cat
                          "Validity of proofs for predicates "
                          (defind-preds-doc-string
                            (defind-pred-info-list->name clique-pred-infos))
                          ".")))
        ,@fn-events
        :hints (("Goal"
                 :expand ,expands
                 :in-theory '(eql
                              not
                              o-p
                              o-finp
                              o<
                              (:e equal)
                              (:e tau-system)
                              ,@term-thms
                              ,@valid-tps)))
        :verify-guards nil
        :flag-local nil
        ///
        (fty::deffixequiv-mutual ,defines-name
          :hints (("Goal"
                   :expand ,fixequiv-expands
                   :in-theory '(,flag-fn
                                not
                                (:e equal)
                                ,@fixequiv-thms
                                ,@prem-acc-thms)))))
     print-events))

  :prepwork

  ((define defind-gen-proof-valid-fn-clique-loop
     ((pred-infos defind-pred-info-listp)
      (irule-infos defind-irule-info-listp)
      (name symbolp)
      (xdocp booleanp)
      (print evmac-input-print-p))
     :guard (defind-irule-names-unambp irule-infos)
     :returns (mv (fn-events pseudo-event-form-listp)
                  (print-events pseudo-event-form-listp)
                  (expands true-listp)
                  (term-thms true-listp)
                  (fixequiv-expands true-listp)
                  (fixequiv-thms true-listp))
     :parents nil
     (b* (((when (endp pred-infos)) (mv nil nil nil nil nil nil))
          ((defind-pred-info info) (car pred-infos))
          ((mv fn-event print-event?)
           (defind-gen-proof-valid-fn
             (car pred-infos) irule-infos nil name xdocp print))
          (count-fn (defind-proof-count-fn-name info.name name))
          (fn-formal (defind-proof-var-name name))
          (expand `(,count-fn ,fn-formal))
          (poss-thm (defind-proof-kind-poss-thm-name info.name name))
          (term-thms1
           (list poss-thm
                 (defind-proof-count-return-thm-name info.name name)))
          (concl-vars (defind-proof-concl-var-names info.formals name))
          ((mv & & & prem-fixing-thms var-fixing-thms)
           (defind-gen-proof-valid-fn-cases
             info.name concl-vars irule-infos name))
          (valid-fn (defind-proof-valid-fn-name info.name name))
          (fixer (defind-proof-fixer-name info.name name))
          (fixequiv-expands1
           (list `(,valid-fn ,fn-formal ,@concl-vars)
                 `(,valid-fn (,fixer ,fn-formal) ,@concl-vars)))
          (fixequiv-thms1
           (append prem-fixing-thms
                   var-fixing-thms
                   (list valid-fn
                         poss-thm
                         (defind-proof-kind-fixing-thm-name info.name name)
                         (defind-proof-fix-id-thm-name info.name name))))
          ((mv fn-events
               print-events
               expands
               term-thms
               fixequiv-expands
               fixequiv-thms)
           (defind-gen-proof-valid-fn-clique-loop
             (cdr pred-infos) irule-infos name xdocp print)))
       (mv (cons fn-event fn-events)
           (append print-event? print-events)
           (cons expand expands)
           (append term-thms1 term-thms)
           (append fixequiv-expands1 fixequiv-expands)
           (append fixequiv-thms1 fixequiv-thms))))

   (define defind-gen-proof-valid-fn-clique-rules-loop
     ((irule-infos defind-irule-info-listp)
      (clique-pred-names symbol-listp)
      (name symbolp))
     :returns (mv (valid-tps true-listp)
                  (prem-acc-thms true-listp))
     :parents nil
     (b* (((when (endp irule-infos)) (mv nil nil))
          ((mv valid-tps prem-acc-thms)
           (defind-gen-proof-valid-fn-clique-rules-loop
             (cdr irule-infos) clique-pred-names name))
          ((defind-irule-info info) (car irule-infos))
          ((defind-conclusion-info cinfo) info.conclusion)
          ((unless (member-eq cinfo.name
                              (symbol-list-fix clique-pred-names)))
           (mv valid-tps prem-acc-thms))
          (valid-tp `(:type-prescription
                      ,(defind-irule-valid-return-thm-name
                         cinfo.name info.name name)))
          (prem-acc-thms1
           (defind-gen-proof-valid-fn-clique-rules-loop-loop
             info.premises cinfo.name info.name 1 name)))
       (mv (cons valid-tp valid-tps)
           (append prem-acc-thms1 prem-acc-thms)))

     :prepwork

     ((define defind-gen-proof-valid-fn-clique-rules-loop-loop
        ((prem-infos defind-premise-info-listp)
         (pred-name symbolp)
         (irule-name symbolp)
         (num posp)
         (name symbolp))
        :returns (thms true-listp)
        :parents nil
        (b* (((when (endp prem-infos)) nil)
             (info (car prem-infos)))
          (defind-premise-info-case
            info
            :pred
            (cons (defind-proof-prem-acc-return-thm-name
                    info.name
                    pred-name irule-name num name)
                  (defind-gen-proof-valid-fn-clique-rules-loop-loop
                    (cdr prem-infos) pred-name irule-name
                    (1+ (lposfix num)) name))
            :other
            (defind-gen-proof-valid-fn-clique-rules-loop-loop
              (cdr prem-infos) pred-name irule-name num name))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-proof-valid-fns ((pred-infos defind-pred-info-listp)
                                    (irule-infos defind-irule-info-listp)
                                    (leveled-cliques symbol-set-list-listp)
                                    (name symbolp)
                                    (xdocp booleanp)
                                    (print evmac-input-print-p))
  :guard (and (defind-pred-names-unambp pred-infos)
              (defind-irule-names-unambp irule-infos))
  :returns (events pseudo-event-form-listp)
  :short "Generate the proof validity functions, for all the cliques."
  :long
  (xdoc::topstring
   (xdoc::p
    "We generate one event per clique, in dependency order.
     For a clique of a single predicate,
     the event is the standalone proof validity function
     of the predicate.
     For a clique of multiple predicates,
     the event is a @(tsee defines) with
     the mutually recursive proof validity functions
     of the predicates of the clique.
     A rule may have premises with predicates in preceding cliques:
     the resulting calls of proof validity functions
     of preceding cliques are not part of the mutual recursion,
     and those functions are defined by the time they are called,
     since the cliques are in dependency order."))
  (defind-gen-proof-valid-fns-loop
    leveled-cliques pred-infos irule-infos name xdocp print)
  :type-prescription (true-listp (defind-gen-proof-valid-fns
                                   pred-infos irule-infos leveled-cliques
                                   name xdocp print))

  :prepwork

  ((define defind-gen-proof-valid-fns-loop
     ((leveled-cliques symbol-set-list-listp)
      (pred-infos defind-pred-info-listp)
      (irule-infos defind-irule-info-listp)
      (name symbolp)
      (xdocp booleanp)
      (print evmac-input-print-p))
     :guard (and (defind-pred-names-unambp pred-infos)
                 (defind-irule-names-unambp irule-infos))
     :returns (events pseudo-event-form-listp)
     :parents nil
     (b* (((when (endp leveled-cliques)) nil)
          (levels (symbol-set-list-fix (car leveled-cliques)))
          (clique-preds (set::set-list-union levels))
          (clique-pred-infos (defind-lookup-pred-set clique-preds pred-infos))
          (events-rest
           (defind-gen-proof-valid-fns-loop
             (cdr leveled-cliques) pred-infos irule-infos name xdocp print))
          ((unless (consp clique-pred-infos))
           (raise "Internal error: no predicates in clique with levels ~x0."
                  levels)
           events-rest)
          (events
           (if (endp (cdr clique-pred-infos))
               (b* (((mv fn-event print-event?)
                     (defind-gen-proof-valid-fn
                       (car clique-pred-infos) irule-infos t name xdocp print)))
                 (cons fn-event print-event?))
             (defind-gen-proof-valid-fn-clique
               clique-pred-infos irule-infos name xdocp print))))
       (append events events-rest))
     :no-function nil
     :guard-hints
     (("Goal" :in-theory (enable set-listp-when-symbol-set-listp))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-pred ((pred-info defind-pred-infop)
                         (irule-infos defind-irule-info-listp)
                         (standalonep booleanp)
                         (name symbolp)
                         (xdocp booleanp)
                         (print evmac-input-print-p))
  :returns (mv (def-events pseudo-event-form-listp)
               (thm-events pseudo-event-form-listp)
               (print-events pseudo-event-form-listp))
  :short "Generate a @('p[i]') predicate,
          along with its @('p[i]-proof-minimalp') predicate
          and its @('p[i]-when-proof-validp') theorem."
  :long
  (xdoc::topstring
   (xdoc::p
    "The predicate is defined as the existence of a valid proof,
     with the arguments of the conclusion passed to
     the proof validity predicate.")
   (xdoc::p
    "The @(':returns') proof needs to know that
     the proof validity predicate returns a boolean.
     We use the type prescription rule from its @(':returns') theorem,
     which is proved,
     rather than the type prescription that ACL2 infers for it.
     The inferred one is in fact a boolean
     because every conclusion has at least one argument
     and so every case of the function ends with an equality;
     but that is a property of the shape of the generated body,
     not something established.
     It also needs to know that
     the minimality predicate returns a boolean,
     for the conjunct described next.")
   (xdoc::p
    "The proof whose existence the predicate asserts
     is also required to be minimal.
     This does not change the meaning of the predicate,
     because a minimal valid proof exists
     exactly when any valid proof exists;
     it makes the witness a minimal proof,
     which is what supports reasoning by induction on proofs.")
   (xdoc::p
    "That requirement weakens the @('p[i]-suff') theorem
     that @(tsee defun-sk) generates,
     which now applies only to minimal proofs.
     So we generate @('p[i]-when-proof-validp'),
     which applies to any valid proof;
     it is exactly @('p[i]-suff')
     as it was before the minimality requirement.
     We generate it disabled, like the other theorems we generate;
     there is no need to disable @('p[i]-suff'),
     because @(tsee std::define-sk) already does that.
     It is proved by descending from the given proof to a minimal one:
     if the proof is not minimal,
     the negation of the minimality predicate
     yields a valid proof with a strictly smaller count,
     which need not be minimal either,
     so the descent is by induction,
     carried by the local @('p[i]-descend') function,
     whose value is irrelevant.")
   (xdoc::p
    "We return the theorem, along with the disabling of @('p[i]-suff'),
     separately from the definitions,
     so that the caller can collect the theorems of all the predicates
     into a single @(tsee defsection);
     see @(tsee defind-gen-preds)."))
  (b* (((defind-pred-info pred-info))
       (proof (defind-proof-var-name name))
       (proof2 (defind-proof-minimal-var-name name))
       (proofp (defind-proof-recog-name pred-info.name name))
       (proof-validp (defind-proof-valid-fn-name pred-info.name name))
       (valid-return-thm (defind-proof-valid-return-thm-name
                           pred-info.name standalonep name))
       (witness (defind-proof-witness-fn-name pred-info.name name))
       (minimalp (defind-proof-minimal-fn-name pred-info.name name))
       (minimalp-witness
        (defind-proof-minimal-witness-fn-name pred-info.name name))
       (minimalp-return-thm
        (defind-proof-minimal-return-thm-name pred-info.name name))
       (minimalp-necc (defind-proof-minimal-necc-thm-name pred-info.name name))
       (count-bound (defind-proof-count-bound-thm-name pred-info.name name))
       ;; FTY generates a count function only for a recursive proof fixtype;
       ;; for a non-recursive one, ACL2-COUNT serves just as well, since the
       ;; descent below only needs some measure that the minimality witness
       ;; strictly decreases.
       (recursivep (defind-pred-recursivep pred-info.name irule-infos))
       (count-fn (if recursivep
                     (defind-proof-count-fn-name pred-info.name name)
                   'acl2-count))
       ;; For ACL2-COUNT the type prescription suffices.
       (count-natp-thms
        (and recursivep
             (list (defind-proof-count-natp-thm-name
                     pred-info.name standalonep name))))
       (descend (defind-proof-descend-fn-name pred-info.name name))
       (when-valid-proof
        (defind-pred-when-valid-proof-thm-name pred-info.name name))
       (suff (defind-pred-suff-thm-name pred-info.name name))
       (concl-vars (defind-proof-concl-var-names pred-info.formals name))
       (minimalp-event
        `(define-sk ,minimalp (,proof ,@concl-vars)
           ,@(and xdocp
                  `(:parents (,(symbol-lfix name))
                    :short ,(str::cat "Minimality of a proof for predicate @('"
                                      (str::downcase-string
                                       (symbol-name pred-info.name))
                                      "').")))
           (forall (,proof2)
                   (implies (and (,proofp ,proof2)
                                 (,proof-validp ,proof2 ,@concl-vars))
                            (<= (,count-fn ,proof)
                                (,count-fn ,proof2))))
           :verify-guards nil))
       (fn-event
        `(define-sk ,pred-info.name (,@pred-info.formals)
           :returns (yes/no booleanp
                            :hints (("Goal"
                                     :in-theory
                                     '(,pred-info.name
                                       booleanp
                                       (:type-prescription
                                        ,valid-return-thm)
                                       (:type-prescription
                                        ,minimalp-return-thm)))))
           ,@(and xdocp
                  `(:parents (,(symbol-lfix name))
                    :short ,(str::cat "Definition of the predicate @('"
                                      (str::downcase-string
                                       (symbol-name pred-info.name))
                                      "') via proof existence.")))
           (exists (,proof)
                   (and (,proofp ,proof)
                        (,proof-validp ,proof ,@pred-info.formals)
                        (,minimalp ,proof ,@pred-info.formals)))
           :skolem-name ,witness
           :verify-guards nil))
       (when-valid-proof-event
        `(encapsulate ()
           (local
            (defun ,descend (,proof ,@concl-vars)
              (declare (xargs :measure (,count-fn ,proof)
                              :hints (("Goal"
                                       :use ,minimalp
                                       :in-theory '(o-p
                                                    o-finp
                                                    o<
                                                    natp
                                                    (:t ,count-fn)
                                                    ,@count-natp-thms)))))
              (if (and (,proofp ,proof)
                       (,proof-validp ,proof ,@concl-vars)
                       (not (,minimalp ,proof ,@concl-vars)))
                  (,descend (,minimalp-witness ,proof ,@concl-vars)
                            ,@concl-vars)
                nil)))
           (defruled ,when-valid-proof
             (implies (and (,proof-validp ,proof ,@concl-vars)
                           (,proofp ,proof))
                      (,pred-info.name ,@concl-vars))
             :hints (("Goal"
                      :induct (,descend ,proof ,@concl-vars)
                      :in-theory (enable ,suff ,minimalp))))))
       ;; The count bound is what ties the proof tree obtained from the
       ;; existential back to a concrete proof tree, which the measure of an
       ;; induction scheme needs. It is meaningful only for a recursive
       ;; predicate, which is also the only kind that can have such a scheme.
       (count-bound-events
        (and recursivep
             (list
              `(defrule ,count-bound
                 (implies (and (,proof-validp ,proof ,@concl-vars)
                               (,proofp ,proof))
                          (<= (,count-fn (,witness ,@concl-vars))
                              (,count-fn ,proof)))
                 :rule-classes
                 ((:linear :trigger-terms
                           ((,count-fn (,witness ,@concl-vars)))))
                 :hints (("Goal"
                          :use ((:instance ,pred-info.name
                                           ,@(alist-to-doublets
                                              (pairlis$ pred-info.formals
                                                        concl-vars)))
                                (:instance ,minimalp-necc
                                           (,proof (,witness ,@concl-vars))
                                           (,proof2 ,proof)))
                          :in-theory (e/d (,when-valid-proof)
                                          (,minimalp-necc))))))))
       (print-event?
        (and (evmac-input-print->= print :result)
             `((cw-event "Function ~x0.~%" ',minimalp)
               (cw-event "Function ~x0.~%" ',pred-info.name)
               (cw-event "Theorem ~x0.~%" ',when-valid-proof)
               ,@(and recursivep
                      `((cw-event "Theorem ~x0.~%" ',count-bound)))))))
    (mv (list minimalp-event fn-event)
        (cons when-valid-proof-event count-bound-events)
        print-event?))

  ///

  (more-returns
   (def-events true-listp :rule-classes :type-prescription)
   (thm-events true-listp :rule-classes :type-prescription)
   (print-events true-listp :rule-classes :type-prescription)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-ind-fn-case-calls ((infos defind-premise-info-listp)
                                      (clique-preds symbol-setp)
                                      (name symbolp))
  :returns (calls true-listp)
  :short "Generate the recursive calls of a case of a @('p[i]-induct') function."
  :long
  (xdoc::topstring
   (xdoc::p
    "There is one call for each premise that calls
     a predicate of the same clique.
     Premises that call predicates of preceding cliques are skipped:
     those predicates are already defined,
     and their induction schemes are separate.
     Premises that are not calls of the predicates being defined
     are skipped as well.")
   (xdoc::p
    "The arguments of the call are the arguments of the premise,
     used as written:
     the variables of the rule are bound, around the whole case,
     to the fields of the proof
     (see @(tsee defind-gen-proof-valid-fn-case-bindings))."))
  (b* (((when (endp infos)) nil)
       (calls (defind-gen-ind-fn-case-calls (cdr infos) clique-preds name))
       (info (car infos)))
    (defind-premise-info-case
      info
      :pred (if (set::in info.name (symbol-sfix clique-preds))
                (cons `(,(defind-ind-fn-name info.name name)
                        ,@(defind-term-info-list->uterm info.args))
                      calls)
              calls)
      :other calls)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-ind-fn-case ((info defind-irule-infop)
                                (clique-preds symbol-setp)
                                (name symbolp))
  :returns (keyword+term true-listp)
  :short "Generate a case of a @('p[i]-induct') function."
  :long
  (xdoc::topstring
   (xdoc::p
    "A rule with no premises that call predicates of the same clique
     is a base case of the induction, and yields @('nil');
     the value of the function is irrelevant,
     only its recursive structure matters.")
   (xdoc::p
    "As in a case of a @('p[i]-proof-validp') function,
     we bind all the variables of the rule
     (see @(tsee defind-gen-proof-valid-fn-case-bindings)).
     But here only the ones that occur in the arguments of the premises
     that call predicates of the same clique are used:
     a variable that occurs only in another premise,
     or only in the conclusion,
     is bound and not used.
     Hence the @('ignorable') declaration,
     which plays the role that
     the @(':ignore-ok') of the @('p[l[k]]-rule[k]-validp') functions
     plays there."))
  (b* (((defind-irule-info info))
       (tag (defind-irule-tag info.name))
       (calls (defind-gen-ind-fn-case-calls info.premises clique-preds name))
       ((when (endp calls)) (list tag nil))
       (term (if (endp (cdr calls)) (car calls) `(list ,@calls)))
       (vars (defind-irule-info-free-vars info))
       (bindings (defind-gen-proof-valid-fn-case-bindings vars name)))
    (list tag (if bindings
                  `(let ,bindings
                     (declare (ignorable ,@(symbol-list-fix vars)))
                     ,term)
                term)))
  :guard-hints (("Goal" :in-theory (enable symbol-listp-when-symbol-setp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-ind-fn-cases ((pred-name symbolp)
                                 (infos defind-irule-info-listp)
                                 (clique-preds symbol-setp)
                                 (name symbolp))
  :returns (keywords+terms true-listp)
  :short "Generate the cases of a @('p[i]-induct') function."
  (b* (((when (endp infos)) nil)
       ((defind-irule-info info) (car infos))
       (rest (defind-gen-ind-fn-cases
               pred-name (cdr infos) clique-preds name))
       ((unless (equal (defind-conclusion-info->name info.conclusion)
                       (symbol-lfix pred-name)))
        rest))
    (cons (defind-gen-ind-fn-case (car infos) clique-preds name) rest)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-ind-fn-body ((pred-info defind-pred-infop)
                                (irule-infos defind-irule-info-listp)
                                (clique-preds symbol-setp)
                                (name symbolp))
  :returns (body "An untranslated term.")
  :short "Generate the body of a @('p[i]-induct') function."
  :long
  (xdoc::topstring
   (xdoc::p
    "The function recurses on the arguments of the conclusions
     of the premises of the rule that the witness proof used,
     so it never mentions a proof;
     that is what lets it serve as an induction scheme
     for the predicate itself.
     The guard that the predicate holds is essential:
     the witness is meaningful only then,
     and the measure argument depends on it."))
  (b* (((defind-pred-info pred-info))
       (proof (defind-proof-var-name name))
       (witness (defind-proof-witness-fn-name pred-info.name name))
       (proof-case (defind-proof-case-name pred-info.name name))
       (cases (defind-gen-ind-fn-cases
                pred-info.name irule-infos clique-preds name)))
    `(and (,pred-info.name ,@pred-info.formals)
          (let ((,proof (,witness ,@pred-info.formals)))
            (,proof-case ,proof ,@cases)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-ind-fn-hint-parts ((pred-infos defind-pred-info-listp)
                                      (standalonep booleanp)
                                      (name symbolp))
  :returns (mv (expands true-listp)
               (uses true-listp)
               (enables true-listp))
  :short "Generate the pieces of the termination hints of
          the @('p[i]-induct') functions of a clique."
  :long
  (xdoc::topstring
   (xdoc::p
    "For each predicate of the clique we expand
     the validity and the count of its witness proof,
     and we supply the kind of that proof.
     The latter is needed because a fixtype of proofs with a single summand
     yields no case split, and so never establishes its kind,
     which leaves the FTY linear rules for the counts of its accessors,
     which are conditional on the kind, unable to fire.")
   (xdoc::p
    "The @('p[i]-proof-count-bound') theorems are not supplied explicitly:
     they are @(':linear') rules whose trigger terms
     occur in the measure conjecture,
     and whose validity hypothesis comes first,
     so that free variable matching binds the proof from it
     rather than from the weaker recognizer hypothesis."))
  (b* (((when (endp pred-infos)) (mv nil nil nil))
       ((defind-pred-info pred-info) (car pred-infos))
       (witness (defind-proof-witness-fn-name pred-info.name name))
       (wcall `(,witness ,@pred-info.formals))
       (proof-validp (defind-proof-valid-fn-name pred-info.name name))
       (count-fn (defind-proof-count-fn-name pred-info.name name))
       (poss-thm (defind-proof-kind-poss-thm-name pred-info.name name))
       (xvar (defind-proof-xvar-name name))
       (count-natp-thm (defind-proof-count-natp-thm-name
                         pred-info.name standalonep name))
       ((mv expands uses enables)
        (defind-gen-ind-fn-hint-parts (cdr pred-infos) standalonep name)))
    (mv (list* `(,proof-validp ,wcall ,@pred-info.formals)
               `(,count-fn ,wcall)
               expands)
        (cons `(:instance ,poss-thm (,xvar ,wcall)) uses)
        (list* pred-info.name count-natp-thm enables))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-ind-fns-for-clique ((pred-infos defind-pred-info-listp)
                                       (irule-infos defind-irule-info-listp)
                                       (clique-preds symbol-setp)
                                       (name symbolp)
                                       (xdocp booleanp)
                                       (print evmac-input-print-p))
  :returns (mv (fn-events pseudo-event-form-listp)
               (thm-events pseudo-event-form-listp)
               (print-events pseudo-event-form-listp))
  :short "Generate the @('p[i]-induct') functions of a clique,
          and the induction rules if any."
  :long
  (xdoc::topstring
   (xdoc::p
    "Nothing is generated for a non-recursive predicate:
     it admits no induction scheme at all.")
   (xdoc::p
    "For a clique of a single predicate, the scheme is a @(tsee define),
     and we turn it into an @(':induction') rule,
     so that a plain @(':induct') hint on a call of the predicate works.")
   (xdoc::p
    "For a clique of two or more predicates,
     the schemes are mutually recursive, and the event is a @(tsee defines).
     No @(':induction') rule is possible then:
     ACL2 derives no induction scheme from mutually recursive functions.
     Nor would one suffice,
     since the induction hypothesis for a premise that calls
     a different predicate of the clique
     would be about the predicate being defined instead.
     Mutual rule induction needs the whole clique proved together,
     so the interface is the flag macro that @(tsee defines) generates.
     We pass @(':flag-local nil'),
     because otherwise the flag function is local
     and that macro cannot be used afterwards.")
   (xdoc::p
    "As with the predicates,
     we return the induction rules separately from the functions,
     so that the caller can put them into a single @(tsee defsection);
     see @(tsee defind-gen-ind-fns)."))
  (b* (((when (endp pred-infos)) (mv nil nil nil))
       ((defind-pred-info pred-info1) (car pred-infos))
       ((unless (defind-pred-recursivep pred-info1.name irule-infos))
        (mv nil nil nil))
       (standalonep (endp (cdr pred-infos)))
       ((mv expands uses enables)
        (defind-gen-ind-fn-hint-parts pred-infos standalonep name))
       ;; The ordinal and arithmetic facts are enabled explicitly, because
       ;; the surrounding book may have restricted the theory; without them
       ;; the measure conjecture resorts to induction, which fails outright
       ;; where the induction depth limit is 0.
       (hints `(("Goal" :expand ,expands
                        :use ,uses
                        :in-theory (enable o-p o-finp o< natp ,@enables))))
       (fn-name1 (defind-ind-fn-name pred-info1.name name))
       (count-fn1 (defind-proof-count-fn-name pred-info1.name name))
       (witness1 (defind-proof-witness-fn-name pred-info1.name name))
       (measure1 `(,count-fn1 (,witness1 ,@pred-info1.formals)))
       (body1 (defind-gen-ind-fn-body
                (car pred-infos) irule-infos clique-preds name))
       (print-events
        (and (evmac-input-print->= print :result)
             (defind-gen-ind-fns-print-events pred-infos name)))
       ((when (endp (cdr pred-infos)))
        (b* ((induction-thm
              (defind-induction-thm-name pred-info1.name name)))
          (mv
           (list `(define ,fn-name1 (,@pred-info1.formals)
                    ,@(and xdocp
                           `(:parents (,(symbol-lfix name))
                             :short ,(str::cat
                                      "Rule induction scheme for predicate @('"
                                      (str::downcase-string
                                       (symbol-name pred-info1.name))
                                      "').")))
                    :measure ,measure1
                    :hints ,hints
                    ,body1
                    :verify-guards nil))
           (list `(defrule ,induction-thm
                    t
                    :rule-classes
                    ((:induction
                      :pattern (,pred-info1.name ,@pred-info1.formals)
                      :scheme (,fn-name1 ,@pred-info1.formals)))))
           print-events)))
       (clique-name (defind-ind-fn-clique-name pred-info1.name name))
       (defines-event
         `(defines ,clique-name
            :flag ,(defind-ind-flag-fn-name pred-info1.name name)
            :flag-defthm-macro ,(defind-ind-flag-macro-name
                                  pred-info1.name name)
            :flag-local nil
            :hints ,hints
            ,@(defind-gen-ind-fns-defines
                pred-infos irule-infos clique-preds name xdocp))))
    (mv (list defines-event) nil print-events))

  :prepwork

  ((define defind-gen-ind-fns-defines ((pred-infos defind-pred-info-listp)
                                       (irule-infos defind-irule-info-listp)
                                       (clique-preds symbol-setp)
                                       (name symbolp)
                                       (xdocp booleanp))
     :returns (defines true-listp)
     :parents nil
     (b* (((when (endp pred-infos)) nil)
          ((defind-pred-info pred-info) (car pred-infos))
          (fn-name (defind-ind-fn-name pred-info.name name))
          (count-fn (defind-proof-count-fn-name pred-info.name name))
          (witness (defind-proof-witness-fn-name pred-info.name name))
          (body (defind-gen-ind-fn-body
                  (car pred-infos) irule-infos clique-preds name)))
       (cons `(define ,fn-name (,@pred-info.formals)
                ,@(and xdocp
                       `(:parents (,(symbol-lfix name))
                         :short ,(str::cat
                                  "Rule induction scheme for predicate @('"
                                  (str::downcase-string
                                   (symbol-name pred-info.name))
                                  "').")))
                :measure (,count-fn (,witness ,@pred-info.formals))
                ,body
                :verify-guards nil)
             (defind-gen-ind-fns-defines
               (cdr pred-infos) irule-infos clique-preds name xdocp))))

   (define defind-gen-ind-fns-print-events ((pred-infos defind-pred-info-listp)
                                            (name symbolp))
     :returns (events pseudo-event-form-listp)
     :parents nil
     (b* (((when (endp pred-infos)) nil)
          ((defind-pred-info pred-info) (car pred-infos))
          (fn-name (defind-ind-fn-name pred-info.name name)))
       (cons `(cw-event "Function ~x0.~%" ',fn-name)
             (defind-gen-ind-fns-print-events (cdr pred-infos) name)))))

  ///

  (more-returns
   (fn-events true-listp :rule-classes :type-prescription)
   (thm-events true-listp :rule-classes :type-prescription)
   (print-events true-listp :rule-classes :type-prescription)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-ind-fns ((pred-infos defind-pred-info-listp)
                            (irule-infos defind-irule-info-listp)
                            (leveled-cliques symbol-set-list-listp)
                            (name symbolp)
                            (xdocp booleanp)
                            (print evmac-input-print-p))
  :guard (defind-pred-names-unambp pred-infos)
  :returns (mv (fn-events pseudo-event-form-listp)
               (thm-events pseudo-event-form-listp)
               (print-events pseudo-event-form-listp))
  :short "Generate all the @('p[i]-induct') functions and induction rules."
  :long
  (xdoc::topstring
   (xdoc::p
    "As for the predicates,
     we keep the induction rules separate from the functions,
     so that the caller can put them into a single @(tsee defsection);
     see @(tsee defind-gen-ind-fns-for-clique).
     Each induction rule mentions only
     the functions of its own clique,
     so it may follow the functions of all the cliques."))
  (b* (((when (endp leveled-cliques)) (mv nil nil nil))
       (levels (symbol-set-list-fix (car leveled-cliques)))
       (clique-preds (set::set-list-union levels))
       (clique-pred-infos (defind-lookup-pred-set clique-preds pred-infos))
       ((mv fns thms prints)
        (defind-gen-ind-fns-for-clique
          clique-pred-infos irule-infos clique-preds name xdocp print))
       ((mv more-fns more-thms more-prints)
        (defind-gen-ind-fns
          pred-infos irule-infos (cdr leveled-cliques)
          name xdocp print)))
    (mv (append fns more-fns)
        (append thms more-thms)
        (append prints more-prints)))
  :no-function nil
  :guard-hints
  (("Goal" :in-theory (enable set-listp-when-symbol-set-listp)))

  ///

  (more-returns
   (fn-events true-listp :rule-classes :type-prescription)
   (thm-events true-listp :rule-classes :type-prescription)
   (print-events true-listp :rule-classes :type-prescription)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define defind-gen-preds ((pred-infos defind-pred-info-listp)
                          (irule-infos defind-irule-info-listp)
                          (leveled-cliques symbol-set-list-listp)
                          (name symbolp)
                          (xdocp booleanp)
                          (print evmac-input-print-p))
  :guard (defind-pred-names-unambp pred-infos)
  :returns (mv (def-events pseudo-event-form-listp)
               (thm-events pseudo-event-form-listp)
               (print-events pseudo-event-form-listp))
  :short "Generate all the @('p[i]') predicates."
  :long
  (xdoc::topstring
   (xdoc::p
    "We go through the cliques, as @(tsee defind-gen-proof-valid-fns) does,
     because each predicate needs to know whether
     its proof validity predicate is standalone
     or a member of a clique of two or more;
     see @(tsee defind-proof-valid-return-thm-name).")
   (xdoc::p
    "We keep the theorems separate from the definitions,
     so that the caller can put them into a single @(tsee defsection);
     see @(tsee defind-gen-pred).
     Thus all the theorems follow all the definitions,
     which is fine:
     no definition depends on any of these theorems,
     and each theorem depends only on
     the definitions of its own predicate."))
  (b* (((when (endp leveled-cliques)) (mv nil nil nil))
       (levels (symbol-set-list-fix (car leveled-cliques)))
       (clique-preds (set::set-list-union levels))
       (clique-pred-infos (defind-lookup-pred-set clique-preds pred-infos))
       (standalonep (and (consp clique-pred-infos)
                         (endp (cdr clique-pred-infos))))
       ((mv defs thms prints)
        (defind-gen-preds-loop
          clique-pred-infos irule-infos standalonep name xdocp print))
       ((mv more-defs more-thms more-prints)
        (defind-gen-preds
          pred-infos irule-infos (cdr leveled-cliques)
          name xdocp print)))
    (mv (append defs more-defs)
        (append thms more-thms)
        (append prints more-prints)))
  :no-function nil
  :guard-hints
  (("Goal" :in-theory (enable set-listp-when-symbol-set-listp)))

  :prepwork
  ((define defind-gen-preds-loop ((pred-infos defind-pred-info-listp)
                                  (irule-infos defind-irule-info-listp)
                                  (standalonep booleanp)
                                  (name symbolp)
                                  (xdocp booleanp)
                                  (print evmac-input-print-p))
     :returns (mv (def-events pseudo-event-form-listp)
                  (thm-events pseudo-event-form-listp)
                  (print-events pseudo-event-form-listp))
     :parents nil
     (b* (((when (endp pred-infos)) (mv nil nil nil))
          ((mv defs thms prints)
           (defind-gen-pred
             (car pred-infos) irule-infos standalonep name xdocp print))
          ((mv more-defs more-thms more-prints)
           (defind-gen-preds-loop
             (cdr pred-infos) irule-infos standalonep name xdocp print)))
       (mv (append defs more-defs)
           (append thms more-thms)
           (append prints more-prints)))
     ///
     (more-returns
      (def-events true-listp :rule-classes :type-prescription)
      (thm-events true-listp :rule-classes :type-prescription)
      (print-events true-listp :rule-classes :type-prescription))))

  ///

  (more-returns
   (def-events true-listp :rule-classes :type-prescription)
   (thm-events true-listp :rule-classes :type-prescription)
   (print-events true-listp :rule-classes :type-prescription)))

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
       ((mv pred-hyps other-hyps)
        (defind-gen-irule-thm-hyps (cdr infos))))
    (defind-premise-info-case
      info
      :pred (mv (cons `(,info.name
                        ,@(defind-term-info-list->uterm info.args))
                      pred-hyps)
                other-hyps)
      :other (mv pred-hyps
                 (cons (defind-term-info->uterm info.term)
                       other-hyps)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-irule-thm-prems ((infos defind-premise-info-listp)
                                    (pred-name symbolp)
                                    (irule-name symbolp)
                                    (num posp)
                                    (name symbolp))
  :returns (mv (proofcalls true-listp)
               (of-constr-thms symbol-listp)
               (fix-id-thms symbol-listp))
  :short "Generate the proofs of the premises of a rule
          in a @('p[l[k]]-rule[k]') theorem,
          along with the names of some relevant theorems."
  :long
  (xdoc::topstring
   (xdoc::p
    "The proof of a premise that is a call of a predicate being defined
     is the witness of that call,
     which the corresponding hypothesis of the theorem provides.")
   (xdoc::p
    "The @('pred-name') input is the @('p[i]') predicate
     of the conclusion of the rule,
     because the accessors belong to the fixtype of its proofs.
     The fixing identity theorem of each premise is instead
     the one of the predicate of the premise,
     because that is the fixtype of the accessed field."))
  (b* (((when (endp infos)) (mv nil nil nil))
       (info (car infos)))
    (defind-premise-info-case
      info
      :pred (b* ((witfn (defind-proof-witness-fn-name info.name name))
                 (proofcall
                  `(,witfn ,@(defind-term-info-list->uterm info.args)))
                 (of-constr-thm (defind-proof-prem-of-constr-thm-name
                                  pred-name irule-name num name))
                 (fix-id-thm (defind-proof-fix-id-thm-name
                               info.name name))
                 ((mv proofcalls of-constr-thms fix-id-thms)
                  (defind-gen-irule-thm-prems
                    (cdr infos) pred-name irule-name (1+ (lposfix num)) name)))
              (mv (cons proofcall proofcalls)
                  (cons of-constr-thm of-constr-thms)
                  (cons fix-id-thm fix-id-thms)))
      :other (defind-gen-irule-thm-prems
               (cdr infos) pred-name irule-name num name))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-irule-thm ((info defind-irule-infop)
                              (pred-infos defind-pred-info-listp)
                              (name symbolp)
                              (print evmac-input-print-p))
  :guard (defind-pred-names-unambp pred-infos)
  :returns (mv (thm-event pseudo-event-formp)
               (print-event? pseudo-event-form-listp))
  :short "Generate a @('p[l[k]]-rule[k]') theorem."
  :long
  (xdoc::topstring
   (xdoc::p
    "The theorem is an implication
     with the premises of the rule as antecedents
     and with its conclusion as consequent;
     the premises that are calls of the predicates being defined
     become calls of those predicates.")
   (xdoc::p
    "The proof of the conclusion is built directly by
     the constructor of the fixtype of proofs,
     so we use the @('p[i]-suff') theorem on it.
     Expanding the hypotheses that are calls of the @('p[i]') predicates
     yields the proofs of those premises,
     which the constructor takes as its subproofs.
     Then the proof validity predicate opens on the known kind,
     the accessors of the constructor yield its arguments,
     and the @('p[l[k]]-rule[k]-validp') function
     closes the equalities for the arguments of the conclusion.")
   (xdoc::p
    "The theorem about the return type of the constructor
     gives both the recognizer and the kind of the constructed proof.
     For a rule with premises that are calls of the predicates being defined
     we also need @(tsee defind-proof-fix-id-thm-name);
     see that function."))
  (b* (((defind-irule-info info))
       ((defind-conclusion-info cinfo) info.conclusion)
       (concl-args (defind-term-info-list->uterm cinfo.args))
       (concl `(,cinfo.name ,@concl-args))
       ((mv pred-hyps other-hyps)
        (defind-gen-irule-thm-hyps info.premises))
       (thm-name (defind-pred-irule-thm-name cinfo.name info.name name))
       (pred-when-valid-proof
        (defind-pred-when-valid-proof-thm-name cinfo.name name))
       (vars (defind-irule-info-free-vars info))
       ((mv proofcalls prem-of-constr-thms fix-id-thms)
        (defind-gen-irule-thm-prems
          info.premises cinfo.name info.name 1 name))
       (constr (defind-proof-constr-name cinfo.name info.name name))
       (proofcall `(,constr ,@(symbol-list-fix vars) ,@proofcalls))
       (pinfo (defind-lookup-pred cinfo.name pred-infos))
       ((unless pinfo)
        (raise "Internal error: predicate ~x0 not found." cinfo.name)
        (mv '(_) nil))
       (formals (defind-pred-info->formals pinfo))
       (concl-vars (defind-proof-concl-var-names formals name))
       (formals-inst (alist-to-doublets (pairlis$ concl-vars concl-args)))
       (proof-var (defind-proof-var-name name))
       (proof-validp (defind-proof-valid-fn-name cinfo.name name))
       (irule-validp (defind-irule-valid-fn-name cinfo.name info.name name))
       (constr-return-thm
        (defind-proof-constr-return-thm cinfo.name info.name name))
       (var-of-constr-thms
        (defind-proof-var-of-constr-thm-names cinfo.name info.name vars name))
       (thm-event
        `(defruled ,thm-name
           ,(defind-gen-implication (append pred-hyps other-hyps) concl)
           ,@(and pred-hyps
                  (list :expand pred-hyps))
           :use (:instance ,pred-when-valid-proof
                           (,proof-var ,proofcall)
                           ,@formals-inst)
           :in-theory '(,proof-validp
                        ,irule-validp
                        ,constr-return-thm
                        ,@var-of-constr-thms
                        ,@prem-of-constr-thms
                        ,@fix-id-thms)))
       (print-event?
        (and (evmac-input-print->= print :result)
             `((cw-event "Theorem ~x0.~%" ',thm-name)))))
    (mv thm-event print-event?))
  :no-function nil
  :guard-hints (("Goal" :in-theory (enable set::sets-are-true-lists
                                           symbol-listp-when-symbol-setp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-irule-thms ((irule-infos defind-irule-info-listp)
                               (pred-infos defind-pred-info-listp)
                               (name symbolp)
                               (print evmac-input-print-p))
  :guard (and (defind-pred-names-unambp pred-infos)
              (defind-irule-names-unambp irule-infos))
  :returns (mv (thm-events pseudo-event-form-listp)
               (print-events pseudo-event-form-listp))
  :short "Generate all the @('p[l[k]]-rule[k]') theorems."
  (b* (((when (endp irule-infos)) (mv nil nil))
       ((mv thm-event print-event?)
        (defind-gen-irule-thm (car irule-infos) pred-infos name print))
       ((mv thm-events print-events)
        (defind-gen-irule-thms (cdr irule-infos) pred-infos name print)))
    (mv (cons thm-event thm-events)
        (append print-event? print-events))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-irule-defsection
  ((irule-infos defind-irule-info-listp)
   (pred-infos defind-pred-info-listp)
   (name symbolp)
   (xdocp booleanp)
   (print evmac-input-print-p))
  :guard (and (defind-pred-names-unambp pred-infos)
              (defind-irule-names-unambp irule-infos))
  :returns (mv (defsection-event pseudo-event-formp
                 :hints (("Goal" :in-theory (enable true-listp))))
               (print-events pseudo-event-form-listp))
  :short "Generate a @(tsee defsection) or @(tsee encapsulate) with
          all the @('p[l[k]]-rule[k]') theorems,
          depending on whether XDOC is to be generated."
  (b* (((mv thm-events print-events)
        (defind-gen-irule-thms irule-infos pred-infos name print))
       (defsection-event
         (if xdocp
             `(defsection ,(defind-rule-thm-section-name name)
                :short "Theorems corresponding to the inference rules."
                ,@thm-events)
           `(encapsulate () ,@thm-events))))
    (mv defsection-event print-events))

  ///

  (more-returns
   (print-events true-listp :rule-classes :type-prescription)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-pred-alt-fns ((infos defind-pred-info-listp)
                                 (name symbolp)
                                 (print evmac-input-print-p))
  :guard (defind-pred-names-unambp infos)
  :returns (mv (signatures true-listp)
               (witness-events pseudo-event-form-listp)
               (print-events pseudo-event-form-listp))
  :short "Generate the signatures and the local witnesses of
          the @('p[i]-alt') constrained functions."
  :long
  (xdoc::topstring
   (xdoc::p
    "The witness of each @('p[i]-alt') is @('p[i]') itself,
     i.e. the minimal predicate,
     which satisfies the constraints by the rule theorems.
     The witnesses are not guard-verified,
     because the @('p[i]') are not."))
  (b* (((when (endp infos)) (mv nil nil nil))
       ((defind-pred-info info) (car infos))
       (fn-name (defind-pred-alt-fn-name info.name name))
       (signature `((,fn-name ,@(repeat (len info.formals) '*)) => *))
       (witness-event `(local (defun ,fn-name ,info.formals
                                (declare (xargs :verify-guards nil))
                                (,info.name ,@info.formals))))
       (print-event?
        (and (evmac-input-print->= print :result)
             `((cw-event "Constrained function ~x0.~%" ',fn-name))))
       ((mv signatures witness-events print-events)
        (defind-gen-pred-alt-fns (cdr infos) name print)))
    (mv (cons signature signatures)
        (cons witness-event witness-events)
        (append print-event? print-events))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-pred-alt-irule-constraint-prems
  ((infos defind-premise-info-listp)
   (name symbolp))
  :returns (prems true-listp)
  :short "Premises of the constraint theorem saying that
          the @('p[i]-alt') constrained functions
          satisfy an inference rule."
  (b* (((when (endp infos)) nil)
       (prems (defind-gen-pred-alt-irule-constraint-prems
                (cdr infos) name))
       (info (car infos)))
    (defind-premise-info-case
      info
      :pred (cons `(,(defind-pred-alt-fn-name info.name name)
                    ,@(defind-term-info-list->uterm info.args))
                  prems)
      :other (cons (defind-term-info->uterm info.term)
                   prems))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-pred-alt-irule-constraint ((info defind-irule-infop)
                                              (pred-names symbol-listp)
                                              (name symbolp)
                                              (print evmac-input-print-p))
  :returns (mv (constraint-event pseudo-event-formp)
               (print-event? pseudo-event-form-listp))
  :short "Constraint theorem saying that
          the @('p[i]-alt') constrained functions
          satisfy an inference rule."
  :long
  (xdoc::topstring
   (xdoc::p
    "The theorem is an implication
     with the premises as antecedents
     and with the conclusion as consequent,
     with the @('p[i]-alt') functions in place of the @('p[i]') ones;
     its free variables are the free variables of the rule.
     For a rule without premises, it is just the conclusion.")
   (xdoc::p
    "The proof, local to the encapsulate,
     unfolds the witness definitions
     (see @(tsee defind-gen-pred-alt-fns)),
     which turns the theorem into an instance of the rule theorem."))
  (b* (((defind-irule-info info))
       ((defind-conclusion-info cinfo) info.conclusion)
       (thm-name (defind-pred-alt-irule-thm-name cinfo.name info.name name))
       (prems (defind-gen-pred-alt-irule-constraint-prems
                info.premises name))
       (concl `(,(defind-pred-alt-fn-name cinfo.name name)
                ,@(defind-term-info-list->uterm cinfo.args)))
       (formula (defind-gen-implication prems concl))
       (alt-fns (defind-pred-alt-fn-names pred-names name))
       (irule-thm (defind-pred-irule-thm-name cinfo.name info.name name))
       (constraint-event `(defruled ,thm-name
                            ,formula
                            :in-theory ',alt-fns
                            :use ,irule-thm))
       (print-event?
        (and (evmac-input-print->= print :result)
             `((cw-event "Constraint ~x0.~%" ',thm-name)))))
    (mv constraint-event print-event?)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-pred-alt-irule-constraints
  ((infos defind-irule-info-listp)
   (pred-names symbol-listp)
   (name symbolp)
   (print evmac-input-print-p))
  :guard (defind-irule-names-unambp infos)
  :returns (mv (constraint-events pseudo-event-form-listp)
               (print-events pseudo-event-form-listp))
  :short "Constraint theorems saying that
          the @('p[i]-alt') constrained functions
          satisfy the inference rules."
  (b* (((when (endp infos)) (mv nil nil))
       ((mv constraint-event print-event?)
        (defind-gen-pred-alt-irule-constraint
          (car infos) pred-names name print))
       ((mv constraint-events print-events)
        (defind-gen-pred-alt-irule-constraints
          (cdr infos) pred-names name print)))
    (mv (cons constraint-event constraint-events)
        (append print-event? print-events))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-pred-alt-encapsulate
  ((pred-infos defind-pred-info-listp)
   (irule-infos defind-irule-info-listp)
   (name symbolp)
   (print evmac-input-print-p))
  :guard (and (defind-pred-names-unambp pred-infos)
              (defind-irule-names-unambp irule-infos))
  :returns (mv (encapsulate-event pseudo-event-formp
                 :hints (("Goal" :in-theory (enable true-listp))))
               (print-events pseudo-event-form-listp))
  :short "Generate the @(tsee encapsulate) that introduces
          the @('p[i]-alt') constrained functions."
  :long
  (xdoc::topstring
   (xdoc::p
    "The functions are constrained to satisfy the inference rules,
     with the @('p[i]') predicates as witnesses."))
  (b* (((mv signatures witness-events fn-print-events)
        (defind-gen-pred-alt-fns pred-infos name print))
       (pred-names (defind-pred-info-list->name pred-infos))
       ((mv constraint-events constraint-print-events)
        (defind-gen-pred-alt-irule-constraints
          irule-infos pred-names name print))
       (encapsulate-event `(encapsulate ,signatures
                             ,@witness-events
                             ,@constraint-events)))
    (mv encapsulate-event
        (append fn-print-events constraint-print-events))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-var-acc$inline-calls ((vars symbol-listp)
                                         (pred-name symbolp)
                                         (irule-name symbolp)
                                         (name symbolp))
  :returns (calls true-listp)
  :short "Calls of the accessors of the fields of a @('p[i]-proof') summand
          named after the variables of a rule."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the @('$inline') forms of the accessors,
     which are the ones that occur in clauses;
     they are used to recognize the case of a rule
     when the proof fixtype has a single summand
     (see @(tsee defind-gen-pred-alt-irule-hints))."))
  (b* (((when (endp vars)) nil)
       (var (symbol-lfix (car vars)))
       (acc (defind-proof-var-acc$inline-name pred-name irule-name var name))
       (proof (defind-proof-var-name name)))
    (cons `(,acc ,proof)
          (defind-gen-var-acc$inline-calls
            (cdr vars) pred-name irule-name name))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-alt-inst-doublets ((vars symbol-listp)
                                      (pred-name symbolp)
                                      (irule-name symbolp)
                                      (name symbolp))
  :returns (doublets true-list-listp)
  :short "Bindings of the variables of a rule
          in the instance of the constraint theorem for that rule,
          in a @('p[i]-alt-when-proof-validp') theorem."
  :long
  (xdoc::topstring
   (xdoc::p
    "Each variable of the rule is bound to
     the field of the proof named after it:
     since the variables of the rule are fields of the proof,
     these are plain accessor calls."))
  (b* (((when (endp vars)) nil)
       (var (symbol-lfix (car vars)))
       (acc (defind-proof-var-acc-name pred-name irule-name var name))
       (proof (defind-proof-var-name name))
       (doublet `(,var (,acc ,proof))))
    (cons doublet
          (defind-gen-alt-inst-doublets
            (cdr vars) pred-name irule-name name))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-pred-alt-when-proof-valid-thm-formula
  ((pred-name symbolp)
   (pred-formals symbol-listp)
   (name symbolp))
  :returns (formula true-listp)
  :short "Formula of a @('p[i]-alt-when-proof-validp') theorem."
  :long
  (xdoc::topstring
   (xdoc::p
    "The conclusion is the @('p[i]-alt') constrained function
     on the arguments of the conclusion,
     which are arguments of the proof validity predicate,
     rather than fields of the proof to be extracted;
     so there is nothing to destructure."))
  (b* ((valid-fn (defind-proof-valid-fn-name pred-name name))
       (proof (defind-proof-var-name name))
       (pred-alt (defind-pred-alt-fn-name pred-name name))
       (concls (defind-proof-concl-var-names pred-formals name)))
    `(implies (,valid-fn ,proof ,@concls)
              (,pred-alt ,@concls))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-pred-alt-irule-hints ((infos defind-irule-info-listp)
                                         (pred-formals symbol-listp)
                                         (clique-preds symbol-setp)
                                         (first-kind symbolp)
                                         (singlep booleanp)
                                         (flag-equivs-thm symbolp)
                                         (name symbolp))
  :guard (defind-irule-names-unambp infos)
  :returns (mv (hint-branches true-listp)
               (lemma-instances true-listp)
               (irule-valid-fns symbol-listp))
  :short "Generate the hints for the inference rules of a predicate,
          to prove the @('p[i]-alt-when-proof-validp') theorem
          of that predicate."
  :long
  (xdoc::topstring
   (xdoc::p
    "The rules are the ones whose conclusion is the predicate
     (see @(tsee defind-irules-of-pred)), in order.")
   (xdoc::p
    "We generate computed hints with @(':use') hints
     of the constraint theorems for the various rules,
     each targeted to the inference rule that it pertains to.
     Putting them all in a single @(':use') hint makes the proofs slow,
     even with a moderate number of inference rules
     (that is what an initial implementation did):
     with eight rules we measured about sixty times as many prover steps.
     So we return, for each inference rule,
     a branch of a computed @(tsee cond) hint,
     used when the theorem is proved by induction,
     along with the constraint theorem instance
     and the rule validity function used,
     for when the theorem is proved without induction.")
   (xdoc::p
    "The computed condition says that the clause contains
     the equality of the summand kind of the proof value
     with the one corresponding to the inference rule;
     more precisely, that the negation appears in the clause,
     because it is a clause, and the equality is a hypothesis.
     But for the last branch and inference rule,
     the clause actually contains the positive equalities
     with all the summand kinds before the last one,
     which are conjunctive hypotheses saying that
     the proof kind is not any of those kinds
     (i.e. it is the last kind, since kinds are exhaustive).
     This is why this function takes the very first proof kind as argument,
     so that, for the last branch, we can check the presence of
     the equality of the proof kind with that kind.")
   (xdoc::p
    "If the predicate has a single inference rule,
     as indicated by the @('singlep') argument,
     the fixtype of proofs has a single summand,
     and thus no kind at all occurs in the clause.
     In this case the condition says that the clause contains
     the negation of the validity of the rule,
     which is a hypothesis of the case of the rule,
     applied to the arguments of the conclusion and to
     the fields of the proof named after the variables of the rule.
     The accessors are the @('$inline') ones because
     those are the ones that occur in the clause.
     This happens only if the predicate is
     in a clique with other predicates,
     because a predicate with a single rule
     is recursive only via other predicates.")
   (xdoc::p
    "The conclusion of the theorem is
     the @('p[i]-alt') constrained function
     on the arguments of the conclusion,
     which are arguments of the proof validity predicate,
     rather than fields of the proof to be extracted;
     so there is nothing to destructure,
     and each branch needs just the proof validity predicate,
     the one for the rule,
     and the theorems of the predicates of the premises
     in preceding cliques.")
   (xdoc::p
    "If a premise has a predicate in a preceding clique,
     i.e. not in @('clique-preds'),
     the theory of the branch includes
     the @('p[i]-alt-when-proof-validp') theorem of that predicate,
     which has been already proved at that point:
     it plays the role that,
     for a predicate in the same clique,
     is played by the induction hypothesis.")
   (xdoc::p
    "For a predicate in a clique with other predicates,
     the @('flag-equivs-thm') input is
     the name of the flag equivalence theorem of the clique
     (see @(tsee defind-proof-valid-fn-clique-flag-equivs-name)),
     which we include in the theory of each branch;
     for a predicate that forms a singleton clique,
     there is no flag function,
     and that input is @('nil').
     The theorem is needed because,
     in the flag induction,
     a rule with two or more premises
     that call predicates of the clique
     gives rise to induction cases in which
     the recursive call for a premise
     governs the recursive calls for the subsequent premises:
     in the cases in which that governing call is false,
     the hypothesis is phrased in terms of the flag function,
     and there are no induction hypotheses for the subsequent premises;
     those cases are vacuous,
     because the negated call of the flag function
     contradicts the validity of the proofs of the premises
     (obtained by expanding the proof validity hypothesis of the theorem),
     but the contradiction can only be exposed by rewriting
     the call of the flag function
     into a call of the corresponding validity function."))
  (b* (((when (endp infos)) (mv nil nil nil))
       ((defind-irule-info info) (car infos))
       ((defind-conclusion-info cinfo) info.conclusion)
       (proof (defind-proof-var-name name))
       (proof-kind (defind-proof-kind$inline-fn-name cinfo.name name))
       (kind (defind-irule-tag info.name))
       (lastp (endp (cdr infos)))
       (vars (defind-irule-info-free-vars info))
       (irule-valid-fn (defind-irule-valid-fn-name cinfo.name info.name name))
       (literal
        (if singlep
            `(not (,irule-valid-fn
                   ,@(defind-proof-concl-var-names pred-formals name)
                   ,@(defind-gen-var-acc$inline-calls
                       vars cinfo.name info.name name)))
          (if lastp
              `(equal (,proof-kind ,proof) ',(symbol-lfix first-kind))
            `(not (equal (,proof-kind ,proof) ',kind)))))
       (cond `(member-equal ',literal clause))
       (alt-irule-thm (defind-pred-alt-irule-thm-name
                        cinfo.name info.name name))
       (inst-doublets
        (defind-gen-alt-inst-doublets
          vars cinfo.name info.name name))
       (lemma-instance `(:instance ,alt-irule-thm ,@inst-doublets))
       (valid-fn (defind-proof-valid-fn-name cinfo.name name))
       (prem-preds (defind-preds-in-premises info.premises))
       (alt-thms (defind-pred-alt-when-proof-valid-thm-names
                   (set::difference prem-preds (symbol-sfix clique-preds))
                   name))
       (hint-branch
        `(,cond
          '(:use ,lemma-instance
            :in-theory '(,valid-fn
                         ,irule-valid-fn
                         ,@alt-thms
                         ,@(and (symbol-lfix flag-equivs-thm)
                                (list (symbol-lfix flag-equivs-thm)))))))
       ((mv hint-branches lemma-instances irule-valid-fns)
        (defind-gen-pred-alt-irule-hints
          (cdr infos) pred-formals clique-preds first-kind singlep
          flag-equivs-thm name)))
    (mv (cons hint-branch hint-branches)
        (cons lemma-instance lemma-instances)
        (cons irule-valid-fn irule-valid-fns)))
  :guard-hints (("Goal" :in-theory (enable symbol-listp-when-symbol-setp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-pred-alt-when-proof-valid-thm
  ((pred-name symbolp)
   (pred-formals symbol-listp)
   (irule-infos defind-irule-info-listp)
   (name symbolp)
   (print evmac-input-print-p))
  :guard (defind-irule-names-unambp irule-infos)
  :returns (mv (thm-event pseudo-event-formp)
               (print-event? pseudo-event-form-listp))
  :short "Generate a @('p[i]-alt-when-proof-validp') theorem,
          for a predicate that forms a singleton clique."
  :long
  (xdoc::topstring
   (xdoc::p
    "The theorem is proved by induction on the proof validity function
     when the predicate is recursive
     (see @(tsee defind-pred-recursivep)):
     then there are at least two proof kinds,
     namely at least one recursive rule and at least one base rule,
     which the last-branch logic of the @(tsee cond) hint relies on.")
   (xdoc::p
    "When the predicate is not recursive,
     the proof validity function is not recursive,
     so there is no induction,
     and the goal is a bounded case analysis on the proof kind.
     In that case we prove the theorem directly,
     with a single @(':use') of the constraint theorems of all the rules,
     opening the relevant functions."))
  (b* ((recursivep (defind-pred-recursivep pred-name irule-infos))
       (thm-name (defind-pred-alt-when-proof-valid-thm-name pred-name name))
       (valid-fn (defind-proof-valid-fn-name pred-name name))
       (formula (defind-gen-pred-alt-when-proof-valid-thm-formula
                  pred-name pred-formals name))
       (irule-infos (defind-irules-of-pred pred-name irule-infos))
       ((unless (consp irule-infos))
        (raise "Internal error: no inference rules for predicate ~x0."
               pred-name)
        (mv '(_) nil))
       (first-kind
        (defind-irule-tag (defind-irule-info->name (car irule-infos))))
       (singlep (endp (cdr irule-infos)))
       (clique-preds (set::insert (symbol-lfix pred-name) nil))
       ((mv hint-branches lemma-instances irule-valid-fns)
        (defind-gen-pred-alt-irule-hints
          irule-infos pred-formals clique-preds first-kind singlep nil name))
       (print-event?
        (and (evmac-input-print->= print :result)
             `((cw-event "Theorem ~x0.~%" ',thm-name))))
       ((when recursivep)
        (mv `(defruled ,thm-name
               ,formula
               :induct t
               :in-theory '(,valid-fn
                            eql)
               :hints ((cond ,@hint-branches)))
            print-event?))
       (poss-thm (defind-proof-kind-poss-thm-name pred-name name))
       (prem-preds (defind-preds-in-premises-of-irules irule-infos))
       (alt-thms (defind-pred-alt-when-proof-valid-thm-names
                   (set::difference prem-preds clique-preds)
                   name)))
    (mv `(defruled ,thm-name
           ,formula
           :use ,lemma-instances
           :in-theory '(,valid-fn
                        ,poss-thm
                        ,@irule-valid-fns
                        ,@alt-thms))
        print-event?))
  :no-function nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-pred-alt-when-proof-valid-thm-clique
  ((clique-pred-infos defind-pred-info-listp)
   (irule-infos defind-irule-info-listp)
   (name symbolp)
   (print evmac-input-print-p))
  :guard (and (consp clique-pred-infos)
              (defind-pred-names-unambp clique-pred-infos)
              (defind-irule-names-unambp irule-infos))
  :returns (mv (thm-event pseudo-event-formp)
               (print-events pseudo-event-form-listp))
  :short "Generate the @('p[i]-alt-when-proof-validp') theorems of
          a clique of multiple predicates."
  :long
  (xdoc::topstring
   (xdoc::p
    "The theorems are proved together, by mutual induction,
     via the macro generated by the flag machinery
     along with the flag function of the clique.
     Since the induction is on all the proof validity functions,
     the @(tsee cond) hint has a branch for
     every rule of every predicate of the clique.")
   (xdoc::p
    "We do not supply the induction hint.
     The proof validity functions of a clique
     do not all have the same formals,
     since each one takes the arguments of the conclusion of its predicate,
     so the flag function takes the ones of all of them;
     the macro generated by the flag machinery
     supplies the call of the flag function on its formals,
     which is what we want,
     so we leave that to it.")
   (xdoc::p
    "The theory of each branch of the @(tsee cond) hint
     includes the flag equivalence theorem of the clique;
     see @(tsee defind-gen-pred-alt-irule-hints) for the reason."))
  (b* ((first-pred (defind-pred-info->name (car clique-pred-infos)))
       (macro (defind-proof-valid-fn-clique-defthm-macro-name first-pred name))
       (flag-fn (defind-proof-valid-fn-clique-flag-name first-pred name))
       (flag-equivs-thm
        (defind-proof-valid-fn-clique-flag-equivs-name first-pred name))
       (clique-preds
        (set::mergesort (defind-pred-info-list->name clique-pred-infos)))
       ((mv thm-events print-events hint-branches valid-fns)
        (defind-gen-pred-alt-when-proof-valid-thm-clique-loop
          clique-pred-infos irule-infos clique-preds
          flag-equivs-thm name print))
       (thm-event
        `(,macro
          ,@thm-events
          :hints (("Goal"
                   :in-theory '(,flag-fn
                                ,@valid-fns
                                eql))
                  (cond ,@hint-branches)))))
    (mv thm-event print-events))

  :prepwork
  ((define defind-gen-pred-alt-when-proof-valid-thm-clique-loop
     ((pred-infos defind-pred-info-listp)
      (irule-infos defind-irule-info-listp)
      (clique-preds symbol-setp)
      (flag-equivs-thm symbolp)
      (name symbolp)
      (print evmac-input-print-p))
     :guard (and (defind-pred-names-unambp pred-infos)
                 (defind-irule-names-unambp irule-infos))
     :returns (mv (thm-events pseudo-event-form-listp)
                  (print-events pseudo-event-form-listp)
                  (hint-branches true-listp)
                  (valid-fns symbol-listp))
     :parents nil
     (b* (((when (endp pred-infos)) (mv nil nil nil nil))
          ((defind-pred-info info) (car pred-infos))
          (thm-name (defind-pred-alt-when-proof-valid-thm-name info.name name))
          (valid-fn (defind-proof-valid-fn-name info.name name))
          (formula (defind-gen-pred-alt-when-proof-valid-thm-formula
                     info.name info.formals name))
          (pred-irule-infos (defind-irules-of-pred info.name irule-infos))
          ((mv thm-events print-events hint-branches valid-fns)
           (defind-gen-pred-alt-when-proof-valid-thm-clique-loop
             (cdr pred-infos) irule-infos clique-preds
             flag-equivs-thm name print))
          ((unless (consp pred-irule-infos))
           (raise "Internal error: no inference rules for predicate ~x0."
                  info.name)
           (mv nil nil nil nil))
          (first-kind
           (defind-irule-tag (defind-irule-info->name (car pred-irule-infos))))
          (singlep (endp (cdr pred-irule-infos)))
          ((mv branches & &)
           (defind-gen-pred-alt-irule-hints
             pred-irule-infos info.formals clique-preds
             first-kind singlep flag-equivs-thm name))
          (thm-event `(defthmd ,thm-name
                        ,formula
                        :flag ,valid-fn))
          (print-event?
           (and (evmac-input-print->= print :result)
                `((cw-event "Theorem ~x0.~%" ',thm-name)))))
       (mv (cons thm-event thm-events)
           (append print-event? print-events)
           (append branches hint-branches)
           (cons valid-fn valid-fns)))
     :no-function nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-pred-alt-when-proof-valid-thms
  ((pred-infos defind-pred-info-listp)
   (irule-infos defind-irule-info-listp)
   (leveled-cliques symbol-set-list-listp)
   (name symbolp)
   (print evmac-input-print-p))
  :guard (and (defind-pred-names-unambp pred-infos)
              (defind-irule-names-unambp irule-infos))
  :returns (mv (thm-events pseudo-event-form-listp)
               (print-events pseudo-event-form-listp))
  :short "Generate all the @('p[i]-alt-when-proof-validp') theorems."
  :long
  (xdoc::topstring
   (xdoc::p
    "We generate one event per clique, in dependency order:
     a single theorem for a clique of a single predicate,
     and a bundle of theorems proved by mutual induction
     for a clique of multiple predicates.
     The cliques must be the same ones used for
     the fixtypes of proofs and the proof validity functions,
     since the induction follows those definitions."))
  (defind-gen-pred-alt-when-proof-valid-thms-loop
    leveled-cliques pred-infos irule-infos name print)

  :prepwork

  ((define defind-gen-pred-alt-when-proof-valid-thms-loop
     ((leveled-cliques symbol-set-list-listp)
      (pred-infos defind-pred-info-listp)
      (irule-infos defind-irule-info-listp)
      (name symbolp)
      (print evmac-input-print-p))
     :guard (and (defind-pred-names-unambp pred-infos)
                 (defind-irule-names-unambp irule-infos))
     :returns (mv (thm-events pseudo-event-form-listp)
                  (print-events pseudo-event-form-listp))
     :parents nil
     (b* (((when (endp leveled-cliques)) (mv nil nil))
          (levels (symbol-set-list-fix (car leveled-cliques)))
          (clique-preds (set::set-list-union levels))
          (clique-pred-infos (defind-lookup-pred-set clique-preds pred-infos))
          ((mv thm-events-rest print-events-rest)
           (defind-gen-pred-alt-when-proof-valid-thms-loop
             (cdr leveled-cliques)
             pred-infos irule-infos name print))
          ((unless (consp clique-pred-infos))
           (raise "Internal error: no predicates in clique with levels ~x0."
                  levels)
           (mv nil nil))
          ((mv thm-event print-events)
           (if (endp (cdr clique-pred-infos))
               (b* (((defind-pred-info info) (car clique-pred-infos)))
                 (defind-gen-pred-alt-when-proof-valid-thm
                   info.name info.formals irule-infos name print))
             (defind-gen-pred-alt-when-proof-valid-thm-clique
               clique-pred-infos irule-infos name print))))
       (mv (cons thm-event thm-events-rest)
           (append print-events print-events-rest)))
     :no-function nil
     :guard-hints
     (("Goal" :in-theory (enable set-listp-when-symbol-set-listp))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-pred-alt-when-pred-thm ((pred-name symbolp)
                                           (pred-formals symbol-listp)
                                           (name symbolp)
                                           (print evmac-input-print-p))
  :returns (mv (thm-event pseudo-event-formp)
               (print-event? pseudo-event-form-listp))
  :short "Generate a @('p[i]-alt-when-p[i]') theorem."
  (b* ((thm-name (defind-pred-alt-when-pred-thm-name pred-name name))
       (pred-alt (defind-pred-alt-fn-name pred-name name))
       (valid-thm (defind-pred-alt-when-proof-valid-thm-name pred-name name))
       (proof-var (defind-proof-var-name name))
       (proof-wit (defind-proof-witness-fn-name pred-name name))
       (formals (symbol-list-fix pred-formals))
       (concls (defind-proof-concl-var-names pred-formals name))
       (concls-inst (alist-to-doublets (pairlis$ concls formals)))
       (thm-event
        `(defruled ,thm-name
           (implies (,(symbol-lfix pred-name) ,@formals)
                    (,pred-alt ,@formals))
           :in-theory '(,(symbol-lfix pred-name))
           :use (:instance ,valid-thm
                           (,proof-var (,proof-wit ,@formals))
                           ,@concls-inst)))
       (print-event?
        (and (evmac-input-print->= print :result)
             `((cw-event "Theorem ~x0.~%" ',thm-name)))))
    (mv thm-event print-event?)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-pred-alt-when-pred-thms
  ((pred-infos defind-pred-info-listp)
   (name symbolp)
   (print evmac-input-print-p))
  :guard (defind-pred-names-unambp pred-infos)
  :returns (mv (thm-events pseudo-event-form-listp)
               (print-events pseudo-event-form-listp))
  :short "Generate all the @('p[i]-alt-when-p[i]') theorems."
  (b* (((when (endp pred-infos)) (mv nil nil))
       ((defind-pred-info info) (car pred-infos))
       ((mv thm-event print-event?)
        (defind-gen-pred-alt-when-pred-thm
          info.name info.formals name print))
       ((mv thm-events print-events)
        (defind-gen-pred-alt-when-pred-thms
          (cdr pred-infos) name print)))
    (mv (cons thm-event thm-events)
        (append print-event? print-events))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-minimality-defsection
  ((pred-infos defind-pred-info-listp)
   (irule-infos defind-irule-info-listp)
   (leveled-cliques symbol-set-list-listp)
   (name symbolp)
   (xdocp booleanp)
   (print evmac-input-print-p))
  :guard (and (defind-pred-names-unambp pred-infos)
              (defind-irule-names-unambp irule-infos))
  :returns (mv (defsection-event pseudo-event-formp
                 :hints (("Goal" :in-theory (enable true-listp))))
               (print-events pseudo-event-form-listp))
  :short "Generate a @(tsee defsection) or @(tsee encapsulate) with
          the @(tsee encapsulate) that introduces
          the @('p[i]-alt') constrained functions
          with the @('p[l[k]]-alt-rule[k]') constraints,
          all the @('p[i]-alt-when-proof-validp') theorems,
          and all the @('p[i]-alt-when-p[i]') theorems."
  (b* (((mv encapsulate-event encapsulate-print-events)
        (defind-gen-pred-alt-encapsulate
          pred-infos irule-infos name print))
       ((mv valid-thm-events valid-thm-print-events)
        (defind-gen-pred-alt-when-proof-valid-thms
          pred-infos irule-infos leveled-cliques name print))
       ((mv min-thm-events min-thm-print-events)
        (defind-gen-pred-alt-when-pred-thms
          pred-infos name print))
       (events
        (cons encapsulate-event (append valid-thm-events min-thm-events)))
       (defsection-event
         (if xdocp
             `(defsection ,(defind-minimality-section-name name)
                :short "Minimality of the predicates."
                ,@events)
           `(encapsulate () ,@events)))
       (print-events (append encapsulate-print-events
                             valid-thm-print-events
                             min-thm-print-events)))
    (mv defsection-event print-events))

  ///

  (more-returns
   (print-events true-listp :rule-classes :type-prescription)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-defsection ((topic symbolp)
                               (short stringp)
                               (events pseudo-event-form-listp)
                               (xdocp booleanp))
  :returns (section-events pseudo-event-form-listp
                           :hints (("Goal" :in-theory (enable true-listp))))
  :short "Wrap generated events into a @(tsee defsection)
          or @(tsee encapsulate),
          depending on whether XDOC is to be generated."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is for events that are collected from several predicates,
     and whose theorems are therefore documented as a group
     instead of individually,
     like the theorems corresponding to the inference rules;
     see @(tsee defind-gen-irule-defsection).")
   (xdoc::p
    "We generate nothing if there are no events,
     to avoid an empty XDOC topic."))
  (b* ((events (true-list-fix events))
       ((when (endp events)) nil))
    (list (if xdocp
              `(defsection ,(symbol-lfix topic)
                 :short ,(str-fix short)
                 ,@events)
            `(encapsulate () ,@events))))

  ///

  (more-returns
   (section-events true-listp :rule-classes :type-prescription)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define defind-gen-events ((name symbolp)
                           (pred-infos defind-pred-info-listp)
                           (irule-infos defind-irule-info-listp)
                           (leveled-cliques symbol-set-list-listp)
                           (parents symbol-listp)
                           short
                           long
                           (xdocp booleanp)
                           (print evmac-input-print-p))
  :guard (and (defind-pred-names-unambp pred-infos)
              (defind-irule-names-unambp irule-infos))
  :returns (event pseudo-event-formp)
  :short "Generate all the events."
  :long
  (xdoc::topstring
   (xdoc::p
    "The events are wrapped into a @(tsee progn).")
   (xdoc::p
    "If the @(':print') input is @(':all'),
     we use @(tsee restore-output?) to restore all the output,
     which @(tsee make-event-terse) otherwise suppresses."))
  (b* ((name-doc-events
        (defind-gen-name-defxdoc+ name parents short long xdocp print))
       (proof-type-events
        (defind-gen-proof-fixtypes pred-infos irule-infos
          leveled-cliques name xdocp print))
       (irule-valid-events
        (defind-gen-irule-valid-fns
          irule-infos pred-infos name xdocp print))
       (proof-valid-events
        (defind-gen-proof-valid-fns
          pred-infos irule-infos leveled-cliques name xdocp print))
       ((mv pred-events pred-thm-events pred-print-events)
        (defind-gen-preds
          pred-infos irule-infos leveled-cliques name xdocp print))
       (pred-thms-events
        (defind-gen-defsection
          (defind-valid-proof-thm-section-name name)
          "Theorems about valid proofs."
          pred-thm-events
          xdocp))
       ((mv ind-events ind-thm-events ind-print-events)
        (defind-gen-ind-fns
          pred-infos irule-infos leveled-cliques name xdocp print))
       (ind-thms-events
        (defind-gen-defsection
          (defind-induction-thm-section-name name)
          "Rules for reasoning by rule induction."
          ind-thm-events
          xdocp))
       ((mv irules-event irules-print-events)
        (defind-gen-irule-defsection
          irule-infos pred-infos name xdocp print))
       ((mv minimality-event minimality-print-events)
        (defind-gen-minimality-defsection
          pred-infos irule-infos leveled-cliques name xdocp print))
       (all-events (append name-doc-events
                           proof-type-events
                           irule-valid-events
                           proof-valid-events
                           pred-events
                           pred-thms-events
                           pred-print-events
                           ind-events
                           ind-thms-events
                           ind-print-events
                           (list irules-event)
                           irules-print-events
                           (list minimality-event)
                           minimality-print-events))
       (event `(progn
                 ,@all-events
                 (value-triple :invisible)))
       (event (restore-output? (eq (evmac-input-print-fix print) :all)
                               event)))
    event)
  :type-prescription :none ; for speed
  :normalize nil ; for speed
  :guard-simplify :limited ; for speed
  :guard-hints (("Goal" :in-theory (disable (:t append))))) ; for speed

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
                                              print
                                              state)
  :returns (mv erp (event pseudo-event-formp) state)
  :parents (definductive-implementation)
  :short "Process the inputs and generate all the events."
  (b* (((reterr) '(_) state)
       ((erp name pred-infos irule-infos leveled-cliques
             parents short long xdocp print state)
        (defind-process-inputs
          name
          preds preds-suppliedp
          irules irules-suppliedp
          parents parents-suppliedp
          short short-suppliedp
          long long-suppliedp
          print
          state))
       (event (defind-gen-events
                name pred-infos irule-infos leveled-cliques
                parents short long xdocp print)))
    (retok event state)))

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
                         print
                         (ctx ctxp)
                         state)
  :returns (mv erp
               (event pseudo-event-formp)
               state)
  :parents (definductive-implementation)
  :short "Event expansion of @(tsee definductive) from the inputs."
  (b* (((mv erp event state)
        (defind-process-inputs-and-gen-events
          name
          preds preds-suppliedp
          irules irules-suppliedp
          parents parents-suppliedp
          short short-suppliedp
          long long-suppliedp
          print
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
                          (long 'nil long-suppliedp)
                          (print ':result))
    `(make-event-terse
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
        ',print
        (cons 'definductive ',name)
        state))))
