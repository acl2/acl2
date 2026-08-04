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

  (defret no-duplicatesp-equal-of-names-of-defind-lookup-pred-set
    (implies (no-duplicatesp-equal (defind-pred-info-list->name infos))
             (no-duplicatesp-equal
              (defind-pred-info-list->name selected-infos)))
    :hints (("Goal" :induct t))))

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

  (defret no-duplicatesp-equal-of-names-of-defind-irules-of-pred
    (implies (no-duplicatesp-equal (defind-irule-info-list->name infos))
             (no-duplicatesp-equal
              (defind-irule-info-list->name selected-infos)))
    :hints (("Goal" :induct t))))

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

(define defind-irule-groundp ((info defind-irule-infop))
  :returns (yes/no booleanp)
  :short "Check if a rule is ground."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the case when the rule has no free variables."))
  (set::emptyp (defind-irule-info-free-vars info)))

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

(define defind-pred2-name ((pred-name symbolp) (name symbolp))
  :returns (pred2-name symbolp)
  :short "Name of a @('p[i]-2') predicate."
  :long
  (xdoc::topstring
   (xdoc::p
    "Besides each predicate @('p[i]'), we define a predicate @('p[i]-2'),
     which denotes the same relation,
     but whose proofs are represented differently:
     a proof records the variables of the rule that builds it
     instead of recording the conclusion.
     The conclusion arguments are instead
     passed to the proof validity predicate.
     We generate the two representations side by side,
     so that they can be compared;
     we may eventually drop one in favor of the other.")
   (xdoc::p
    "All the events for the second representation
     are named after @('p[i]-2'),
     via the same naming functions used for @('p[i]');
     so this is the only naming function specific to that representation."))
  (packn-pos (list (symbol-lfix pred-name) '-2) (symbol-lfix name)))

;;;;;;;;;;;;;;;;;;;;

(define defind-assert-type-name ((pred-name symbolp) (name symbolp))
  :returns (type-name symbolp)
  :short "Name of a @('p[i]-assertion') fixtype."
  (packn-pos (list (symbol-lfix pred-name) '-assertion) (symbol-lfix name)))

;;;;;;;;;;

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

(define defind-proof2-xvar-name ((name symbolp))
  :returns (var-name symbolp)
  :short "Name of the @(':xvar') of a @('p[i]-2-proof') fixtype."
  :long
  (xdoc::topstring
   (xdoc::p
    "The fields of these fixtypes are named after the variables of the rules,
     so the @(':xvar') must differ from all of those;
     see @(tsee defind-gen-proof2-deftagsum).")
   (xdoc::p
    "This is not the variable that the @('p[i]-2-proof-validp') functions
     use for their proof argument, which is @(tsee defind-proof-var-name).
     A variable of a rule may shadow that one without harm,
     because the case macro binds the fields of the proof
     before the shadowing takes place;
     it may not clash with this one,
     which @(tsee defind-check-proof2-names) enforces."))
  (packn-pos (list (defind-proof-var-name name) '$) (symbol-lfix name)))

;;;;;;;;;;

(define defind-flag-var-name ((name symbolp))
  :returns (var-name symbolp)
  :short "Name of the flag variable of a @(tsee defines) clique."
  (packn-pos (list 'flag) (symbol-lfix name)))

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

(define defind-proof-var-field-var-name ((var symbolp) (name symbolp))
  :returns (var-name symbolp)
  :short "Name of the variable bound to a variable field of a proof."
  :long
  (xdoc::topstring
   (xdoc::p
    "The summands of a @('p[i]-2-proof') fixtype have a field
     for each variable of the rule, named after the variable.
     This is the variable that the case macro of the fixtype
     binds to that field;
     @(tsee defind-proof-prem-var-name) and
     @(tsee defind-proof-concl-var-name)
     are the analogous names for the other kinds of field.")
   (xdoc::p
    "The cases of a @('p[i]-2-proof-validp') function use these variables
     either as the right-hand sides of the bindings of the rule's variables
     or directly as arguments of the @('p[l[k]]-2-rule[k]-validp') function;
     see @(tsee defind-gen-proof2-valid-fn-case-bindings)."))
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

;;;;;;;;;;

(define defind-proof2-concl-var-names ((formals symbol-listp) (name symbolp))
  :returns (var-names symbol-listp)
  :short "Names of the variables that a @('p[i]-2-proof-validp') function
          uses for the arguments of the conclusion."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the same names used for the formals of a conclusion assertion.")
   (xdoc::p
    "These names must differ from the variables of the rules,
     which are bound, in each case of the function,
     to the corresponding fields of the proof:
     a rule variable with one of these names would shadow the formal,
     turning the equality for that argument of the conclusion
     into an equality of the field with itself.
     This is why @(tsee defind-check-proof2-names) rejects such a rule.
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

(define defind-proof-prem-acc$inline-name ((pred-name symbolp)
                                           (irule-name symbolp)
                                           (num posp)
                                           (name symbolp))
  :returns (acc-name symbolp)
  :short "Name of the @('$inline') form of
          a premise accessor of a @('p[i]-proof') summand."
  (packn-pos (list (defind-proof-prem-acc-name pred-name irule-name num name)
                   '$inline)
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

;;;;;;;;;;

(define defind-proof-var-acc-name ((pred-name symbolp)
                                   (irule-name symbolp)
                                   (var symbolp)
                                   (name symbolp))
  :returns (acc-name symbolp)
  :short "Name of a variable accessor of a @('p[i]-2-proof') summand."
  (packn-pos (list (defind-proof-constr-name pred-name irule-name name)
                   '->
                   (symbol-lfix var))
             (symbol-lfix name)))

;;;;;;;;;;

(define defind-proof-concl-acc$inline-name ((pred-name symbolp)
                                            (irule-name symbolp)
                                            (name symbolp))
  :returns (acc-name symbolp)
  :short "Name of the @('$inline') form of
          the conclusion accessor of a @('p[i]-proof') summand."
  (packn-pos (list (defind-proof-concl-acc-name pred-name irule-name name)
                   '$inline)
             (symbol-lfix name)))

;;;;;;;;;;

(define defind-proof-var-acc$inline-name ((pred-name symbolp)
                                          (irule-name symbolp)
                                          (var symbolp)
                                          (name symbolp))
  :returns (acc-name symbolp)
  :short "Name of the @('$inline') form of
          a variable accessor of a @('p[i]-2-proof') summand."
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

(define defind-proof2-kind-fixing-thm-name ((pred-name symbolp)
                                            (name symbolp))
  :returns (thm-name symbolp)
  :short "Name of the kind fixing theorem for a @('p[i]-2-proof') fixtype."
  :long
  (xdoc::topstring
   (xdoc::p
    "This differs from @(tsee defind-proof-kind-fixing-thm-name)
     only in the variable that ends the name;
     see @(tsee defind-proof2-prem-fixing-thm-name)."))
  (packn-pos (list (defind-proof-type-name pred-name name)
                   '-kind$inline-of-
                   (defind-proof-fixer-name pred-name name)
                   '-
                   (defind-proof2-xvar-name name))
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

(define defind-proof-concl-return-thm-name ((pred-name symbolp)
                                            (name symbolp))
  :returns (thm-name symbolp)
  :short "Name of the return theorem of a @('p[i]-proof->conclusion') function."
  (packn-pos (list (defind-assert-recog-name pred-name name)
                   '-of-
                   (defind-proof-concl-fn-name pred-name name))
             (symbol-lfix name)))

;;;;;;;;;;

(define defind-concl-assert-thm-names ((preds symbol-setp) (name symbolp))
  :returns (thm-names true-listp)
  :short "Names of the theorems to relate
          the conclusions of proofs to assertions,
          for a set of predicates."
  :long
  (xdoc::topstring
   (xdoc::p
    "For each predicate, these are the theorems that
     decompose an equality of assertions,
     remove the assertion fixer,
     and establish that the conclusion of a proof is an assertion."))
  (b* (((when (set::emptyp (symbol-sfix preds))) nil)
       (pred (set::head preds))
       (thm-names (defind-concl-assert-thm-names (set::tail preds) name)))
    (list* (defind-equal-of-assert-thm-name pred name)
           (defind-assert-fix-id-thm-name pred name)
           (defind-proof-concl-return-thm-name pred name)
           thm-names))
  :prepwork ((local (in-theory (enable emptyp-of-symbol-sfix)))))

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
  (packn-pos (list (defind-proof-prem-acc-name pred-name irule-name num name)
                   '$inline-of-
                   (defind-proof-fixer-name pred-name name)
                   '-x)
             (symbol-lfix name)))

;;;;;;;;;;

(define defind-proof2-prem-fixing-thm-name ((pred-name symbolp)
                                            (irule-name symbolp)
                                            (num posp)
                                            (name symbolp))
  :returns (thm-name symbolp)
  :short "Name of the fixing theorem of a premise accessor of
          a @('p[i]-2-proof') fixtype."
  :long
  (xdoc::topstring
   (xdoc::p
    "This differs from @(tsee defind-proof-prem-fixing-thm-name)
     only in the variable that ends the name,
     which is the @(':xvar') of the fixtype:
     the @('p[i]-proof') fixtypes use the default @('x'),
     while the @('p[i]-2-proof') fixtypes cannot
     (see @(tsee defind-gen-proof2-deftagsum))."))
  (packn-pos (list (defind-proof-prem-acc-name pred-name irule-name num name)
                   '$inline-of-
                   (defind-proof-fixer-name pred-name name)
                   '-
                   (defind-proof2-xvar-name name))
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

(define defind-proof2-var-acc-fixing-thm-names ((pred-name symbolp)
                                                (irule-name symbolp)
                                                (vars symbol-listp)
                                                (name symbolp))
  :returns (thm-names symbol-listp)
  :short "Names of the fixing theorems of the variable accessors of
          a @('p[i]-2-proof') summand."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the counterparts of
     @(tsee defind-proof-concl-acc-fixing-thm-name),
     for the fields named after the variables of the rule;
     see @(tsee defind-proof2-prem-fixing-thm-name)
     for the variable that ends the names."))
  (cond ((endp vars) nil)
        (t (cons (packn-pos
                  (list (defind-proof-var-acc-name
                          pred-name irule-name (car vars) name)
                        '$inline-of-
                        (defind-proof-fixer-name pred-name name)
                        '-
                        (defind-proof2-xvar-name name))
                  (symbol-lfix name))
                 (defind-proof2-var-acc-fixing-thm-names
                   pred-name irule-name (cdr vars) name)))))

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

(define defind-proof-var-of-constr-thm-names ((pred-name symbolp)
                                              (irule-name symbolp)
                                              (vars symbol-listp)
                                              (name symbolp))
  :returns (thm-names symbol-listp)
  :short "Names of the theorems about the application of
          the variable accessors of a @('p[i]-2-proof') fixtype
          to the constructor of the fixtype."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the counterparts of
     @(tsee defind-proof-concl-of-constr-thm-name),
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
     whether the predicate forms a singleton clique.")
   (xdoc::p
    "The events for the first representation of proofs
     never refer to this theorem,
     because the bodies of the @('p[i]') predicates
     end with an equality, which is a boolean by type reasoning,
     while the ones of the @('p[i]-2') predicates
     end with a call of the proof validity predicate."))
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

(define defind-irule-valid-suff-thm-name ((pred-name symbolp)
                                          (irule-name symbolp)
                                          (name symbolp))
  :returns (thm-name symbolp)
  :short "Name of the sufficiency theorem of
          a @('p[l[k]]-rule[k]-validp') function."
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

(define defind-proof2-pred-alt-when-proof-valid-thm-names ((preds symbol-setp)
                                                           (name symbolp))
  :returns (thm-names true-listp)
  :short "Names of the @('p[i]-2-alt-when-proof-validp') theorems
          for a set of predicates."
  :long
  (xdoc::topstring
   (xdoc::p
    "The set consists of predicates as supplied by the user,
     which we turn into the corresponding @('p[i]-2') predicates."))
  (b* (((when (set::emptyp (symbol-sfix preds))) nil)
       (pred (set::head preds))
       (thm-names (defind-proof2-pred-alt-when-proof-valid-thm-names
                    (set::tail preds) name)))
    (cons (defind-pred-alt-when-proof-valid-thm-name
            (defind-pred2-name pred name) name)
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

(define defind-rule-thm-section-name ((name symbolp))
  :returns (topic symbolp)
  :short "Name of the @(tsee defsection) containing
          the @('p[l[k]]-rule[k]') theorems."
  (packn-pos (list (symbol-lfix name) '-rules) (symbol-lfix name)))

;;;;;;;;;;

(define defind-proof2-rule-thm-section-name ((name symbolp))
  :returns (topic symbolp)
  :short "Name of the @(tsee defsection) containing
          the @('p[l[k]]-2-rule[k]') theorems."
  (packn-pos (list (symbol-lfix name) '-2-rules) (symbol-lfix name)))

;;;;;;;;;;;;;;;;;;;;

(define defind-pred-alt-irule-witness-fn-name ((pred-name symbolp)
                                               (irule-name symbolp)
                                               (name symbolp))
  :returns (fn-name symbolp)
  :short "Name of the witness function of
          a @('p[l[k]]-alt-rule[k]-p') function."
  (packn-pos (list (defind-pred-alt-irule-fn-name pred-name irule-name name)
                   '-witness)
             (symbol-lfix name)))

;;;;;;;;;;;;;;;;;;;;

(define defind-pred2-when-pred-thm-name ((pred-name symbolp) (name symbolp))
  :returns (thm-name symbolp)
  :short "Name of a @('p[i]-2-when-p[i]') theorem."
  (packn-pos (list (defind-pred2-name pred-name name)
                   '-when-
                   (symbol-lfix pred-name))
             (symbol-lfix name)))

;;;;;;;;;;

(define defind-pred-when-pred2-thm-name ((pred-name symbolp) (name symbolp))
  :returns (thm-name symbolp)
  :short "Name of a @('p[i]-when-p[i]-2') theorem."
  (packn-pos (list (symbol-lfix pred-name)
                   '-when-
                   (defind-pred2-name pred-name name))
             (symbol-lfix name)))

;;;;;;;;;;

(define defind-pred2-is-pred-thm-name ((pred-name symbolp) (name symbolp))
  :returns (thm-name symbolp)
  :short "Name of a @('p[i]-2-is-p[i]') theorem."
  (packn-pos (list (defind-pred2-name pred-name name)
                   '-is-
                   (symbol-lfix pred-name))
             (symbol-lfix name)))

;;;;;;;;;;;;;;;;;;;;

(define defind-pred-return-thm-name ((pred-name symbolp) (name symbolp))
  :returns (thm-name symbolp)
  :short "Name of the return theorem of a @('p[i]') predicate."
  (packn-pos (list 'booleanp-of- (symbol-lfix pred-name))
             (symbol-lfix name)))

;;;;;;;;;;;;;;;;;;;;

(define defind-proof2-equivalence-section-name ((name symbolp))
  :returns (topic symbolp)
  :short "Name of the @(tsee defsection) containing
          the theorems that relate the two representations of proofs."
  (packn-pos (list (symbol-lfix name) '-2-same) (symbol-lfix name)))

;;;;;;;;;;;;;;;;;;;;

(define defind-proof2-minimality-section-name ((name symbolp))
  :returns (topic symbolp)
  :short "Name of the @(tsee defsection) containing
          the stubs, propositions, and theorems
          for the minimality of the @('p[i]-2') predicates."
  (packn-pos (list (symbol-lfix name) '-2-minimal) (symbol-lfix name)))

;;;;;;;;;;;;;;;;;;;;

(define defind-minimality-section-name ((name symbolp))
  :returns (topic symbolp)
  :short "Name of the @(tsee defsection) containing
          the stubs, propositions, and theorems
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
  :guard (no-duplicatesp-equal (defind-pred-info-list->name pred-infos))
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
  :guard (no-duplicatesp-equal (defind-pred-info-list->name pred-infos))
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
  :guard (no-duplicatesp-equal (defind-pred-info-list->name pred-infos))
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
     :guard (no-duplicatesp-equal (defind-pred-info-list->name pred-infos))
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
  :guard (no-duplicatesp-equal (defind-pred-info-list->name pred-infos))
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
  :guard (no-duplicatesp-equal (defind-pred-info-list->name pred-infos))
  :returns (mv erp
               (infos defind-irule-info-listp)
               (leveled-cliques symbol-set-list-listp)
               state)
  :short "Process the @(':irules') input."
  :long
  (xdoc::topstring
   (xdoc::p
    "Besides processing the individual rules,
     we check that the rule names are all distinct.
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
       (irule-names (defind-irule-info-list->name infos))
       ((unless (no-duplicatesp-eq irule-names))
        (reterr (msg "The names of the rules in the :IRULES input ~
                      must be all distinct, ~
                      but there are duplicates among ~&0."
                     irule-names)))
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
     :guard (no-duplicatesp-equal (defind-pred-info-list->name pred-infos))
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

(define defind-check-proof2-names ((irule-infos defind-irule-info-listp)
                                   (pred-infos defind-pred-info-listp)
                                   (name symbolp))
  :guard (no-duplicatesp-equal (defind-pred-info-list->name pred-infos))
  :returns (erp "@('nil') or an error message.")
  :short "Check that the variables of the rules do not clash with
          the names that the second representation reserves."
  :long
  (xdoc::topstring
   (xdoc::p
    "A summand of a @('p[i]-2-proof') fixtype has a field
     for each variable of the rule,
     so a variable that is also the @(':xvar') of the fixtype,
     or the name of one of the premise fields,
     makes FTY reject the fixtype.
     A variable that is also one of the variables
     for the arguments of the conclusion is worse:
     it shadows the formal of the @('p[i]-2-proof-validp') function
     in the case for the rule,
     which turns the equality for that argument of the conclusion
     into an equality of the field with itself,
     silently defining the wrong relation.")
   (xdoc::p
    "We take the names of the premise fields from
     @(tsee defind-gen-proof2-prem-fields),
     so that this check cannot drift from what is generated.
     This is why this check is here,
     among the event generation code,
     instead of with the rest of the input processing;
     it also needs the name of the macro call,
     which is not available in that phase.")
   (xdoc::p
    "These names are reserved only by the second representation of proofs:
     if that representation is dropped, so is this check.")
   (xdoc::p
    "We do not check the proof variable, @(tsee defind-proof-var-name).
     A rule variable with that name does make the macro fail,
     but in the events for the first representation,
     at the theorem about the conclusion of a proof built by a rule.
     That failure predates the second representation
     and does not involve it,
     so it belongs with the first representation;
     until it is fixed,
     such a rule is rejected by a proof failure
     instead of by a message from here."))
  (b* (((reterr))
       ((when (endp irule-infos)) (retok))
       ((defind-irule-info info) (car irule-infos))
       (pred-name (defind-conclusion-info->name info.conclusion))
       (pinfo (defind-lookup-pred pred-name pred-infos))
       ((unless pinfo) (retok)) ; never happens: checked while processing
       (reserved
        (cons (defind-proof2-xvar-name name)
              (append (defind-proof2-concl-var-names
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
    (defind-check-proof2-names (cdr irule-infos) pred-infos name))
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
               state)
  :short "Process all the inputs."
  (b* (((reterr) nil nil nil nil nil nil nil nil state)
       (wrld (w state))
       ((erp name) (defind-process-name name wrld))
       ((erp pred-infos)
        (defind-process-preds preds preds-suppliedp wrld))
       ((erp irule-infos leveled-cliques state)
        (defind-process-irules irules irules-suppliedp pred-infos state))
       ((erp) (defind-check-proof2-names irule-infos pred-infos name))
       ((erp parents short long xdocp)
        (defind-process-parents/short/long
          parents parents-suppliedp
          short short-suppliedp
          long long-suppliedp)))
    (retok name pred-infos irule-infos leveled-cliques
           parents short long xdocp state))

  ///

  (defret no-duplicatesp-equal-of-defind-process-inputs-preds
    (no-duplicatesp-equal (defind-pred-info-list->name pred-infos)))

  (defret no-duplicatesp-equal-of-defind-process-inputs-irules
    (no-duplicatesp-equal (defind-irule-info-list->name irule-infos))))

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
                                    (levels symbol-set-listp)
                                    (preds-in-previous-cliques symbol-setp)
                                    (prepworkp booleanp)
                                    (name symbolp)
                                    (xdocp booleanp))
  :guard (no-duplicatesp-equal (defind-irule-info-list->name infos))
  :returns (deftagsum pseudo-event-formp)
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
     the limit is in the enclosing @(tsee fty::deftypes) instead."))
  (b* ((summands (defind-gen-proof-summands pred-name infos name))
       (measurep (consp (cdr (symbol-set-list-fix levels))))
       (level (defind-pred-level pred-name levels))
       (override-rule (and (< 0 level)
                           (defind-pred-override-rule
                             pred-name level levels
                             preds-in-previous-cliques infos))))
    `(fty::deftagsum ,(defind-proof-type-name pred-name name)
       ,@(and xdocp
              `(:parents (,(symbol-lfix name))
                :short ,(str::cat
                         "Fixtype of proofs for predicate @('"
                         (str::downcase-string (symbol-name pred-name))
                         "').")))
       ,@summands
       ,@(and override-rule
              `(:base-case-override ,(defind-irule-tag override-rule)))
       ,@(and measurep
              `(:measure (two-nats-measure (acl2-count x) ,level)))
       :pred ,(defind-proof-recog-name pred-name name)
       ,@(and prepworkp
              '(:prepwork ((set-induction-depth-limit 1)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-proof-deftagsums ((pred-infos defind-pred-info-listp)
                                     (irule-infos defind-irule-info-listp)
                                     (levels symbol-set-listp)
                                     (preds-in-previous-cliques symbol-setp)
                                     (prepworkp booleanp)
                                     (name symbolp)
                                     (xdocp booleanp))
  :guard (and (no-duplicatesp-equal (defind-pred-info-list->name pred-infos))
              (no-duplicatesp-equal (defind-irule-info-list->name irule-infos)))
  :returns (deftagsums pseudo-event-form-listp)
  :short "Generate the @('p[i]-proof') fixtypes."
  (b* (((when (endp pred-infos)) nil)
       (pred-name (defind-pred-info->name (car pred-infos)))
       (event (defind-gen-proof-deftagsum pred-name irule-infos
                levels preds-in-previous-cliques prepworkp name xdocp))
       (events (defind-gen-proof-deftagsums
                 (cdr pred-infos) irule-infos
                 levels preds-in-previous-cliques prepworkp name xdocp)))
    (cons event events)))

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

(define defind-gen-proof-fixtypes ((pred-infos defind-pred-info-listp)
                                   (irule-infos defind-irule-info-listp)
                                   (leveled-cliques symbol-set-list-listp)
                                   (name symbolp)
                                   (xdocp booleanp))
  :guard (and (no-duplicatesp-equal (defind-pred-info-list->name pred-infos))
              (no-duplicatesp-equal (defind-irule-info-list->name irule-infos)))
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
    leveled-cliques nil pred-infos irule-infos name xdocp)

  :prepwork

  ((define defind-gen-proof-fixtypes-loop
     ((leveled-cliques symbol-set-list-listp)
      (preds-in-previous-cliques symbol-setp)
      (pred-infos defind-pred-info-listp)
      (irule-infos defind-irule-info-listp)
      (name symbolp)
      (xdocp booleanp))
     :guard (and (no-duplicatesp-equal
                  (defind-pred-info-list->name pred-infos))
                 (no-duplicatesp-equal
                  (defind-irule-info-list->name irule-infos)))
     :returns (events pseudo-event-form-listp)
     :parents nil
     (b* (((when (endp leveled-cliques)) nil)
          (levels (symbol-set-list-fix (car leveled-cliques)))
          (clique-preds (set::set-list-union levels))
          (clique-pred-infos (defind-lookup-pred-set clique-preds pred-infos))
          (events (defind-gen-proof-fixtypes-loop
                    (cdr leveled-cliques)
                    (set::union clique-preds
                                (symbol-sfix preds-in-previous-cliques))
                    pred-infos irule-infos name xdocp))
          ((unless (consp clique-pred-infos))
           (raise "Internal error: no predicates in clique with levels ~x0."
                  levels)
           events)
          (event
           (if (endp (cdr clique-pred-infos))
               (defind-gen-proof-deftagsum
                 (defind-pred-info->name (car clique-pred-infos))
                 irule-infos levels preds-in-previous-cliques
                 t name xdocp)
             (b* ((deftagsums (defind-gen-proof-deftagsums
                                clique-pred-infos irule-infos
                                levels preds-in-previous-cliques
                                nil name xdocp))
                  (deftypes-name
                    (defind-proof-type-clique-name
                      (defind-pred-info->name (car clique-pred-infos))
                      name)))
               `(fty::deftypes ,deftypes-name
                  ,@(and xdocp
                         `(:parents (,(symbol-lfix name))
                           :short ,(str::cat
                                    "Fixtypes of proofs for predicates "
                                    (defind-preds-doc-string
                                      (defind-pred-info-list->name
                                        clique-pred-infos))
                                    ".")))
                  ,@deftagsums
                  :prepwork ((set-induction-depth-limit 1)))))))
       (cons event events))
     :no-function nil
     :guard-hints
     (("Goal" :in-theory (enable set-listp-when-symbol-set-listp))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-proof2-var-fields ((vars symbol-listp))
  :returns (fields true-list-listp)
  :short "Generate the variable fields of
          a summand of a @('p[i]-2-proof') fixtype."
  :long
  (xdoc::topstring
   (xdoc::p
    "The summand corresponds to an inference rule,
     and it has one field for each variable of the rule:
     the field is named after the variable and has no type.
     These fields, which the @('p[i]-proof') fixtypes do not have,
     are what lets the conclusion be
     an argument of the proof validity predicate,
     instead of a field of the proof."))
  (if (endp vars)
      nil
    (cons (list (symbol-lfix (car vars)))
          (defind-gen-proof2-var-fields (cdr vars)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-proof2-prem-fields ((infos defind-premise-info-listp)
                                       (num posp)
                                       (name symbolp))
  :returns (fields (and (true-list-listp fields)
                        (alistp fields))
                   :hints (("Goal" :induct t :in-theory (enable alistp))))
  :short "Generate the premise fields of
          a summand of a @('p[i]-2-proof') fixtype."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is like @(tsee defind-gen-prem-fields),
     but the fields have the @('p[j]-2-proof') fixtypes."))
  (b* (((when (endp infos)) nil)
       (info (car infos))
       ((when (defind-premise-info-case info :other))
        (defind-gen-proof2-prem-fields (cdr infos) (lposfix num) name))
       (pred-name (defind-premise-info-pred->name info))
       (field-name (defind-prem-field-name num name))
       (field-type (defind-proof-type-name
                    (defind-pred2-name pred-name name) name))
       (field `(,field-name ,field-type))
       (fields
        (defind-gen-proof2-prem-fields (cdr infos) (1+ (lposfix num)) name)))
    (cons field fields)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-proof2-summand ((info defind-irule-infop) (name symbolp))
  :returns (summand true-listp)
  :short "Generate a summand of a @('p[i]-2-proof') fixtype."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is like @(tsee defind-gen-proof-summand),
     but with a field for each variable of the rule
     instead of a field for the conclusion."))
  (b* (((defind-irule-info info))
       (tag (defind-irule-tag info.name))
       (var-fields
        (defind-gen-proof2-var-fields (defind-irule-info-free-vars info)))
       (prem-fields (defind-gen-proof2-prem-fields info.premises 1 name)))
    `(,tag (,@var-fields ,@prem-fields)))
  :guard-hints (("Goal" :in-theory (enable symbol-listp-when-symbol-setp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-proof2-summands ((pred-name symbolp)
                                    (infos defind-irule-info-listp)
                                    (name symbolp))
  :guard (no-duplicatesp-equal (defind-irule-info-list->name infos))
  :returns (summands true-list-listp)
  :short "Generate the summands of a @('p[i]-2-proof') fixtype."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is like @(tsee defind-gen-proof-summands).
     The @('pred-name') input is @('p[i]'), not @('p[i]-2')
     because it is matched against the conclusions of the rules."))
  (b* (((when (endp infos)) nil)
       ((defind-irule-info info) (car infos))
       ((defind-conclusion-info info.conclusion))
       ((unless (equal info.conclusion.name (symbol-lfix pred-name)))
        (defind-gen-proof2-summands pred-name (cdr infos) name))
       (summand (defind-gen-proof2-summand info name))
       (summands (defind-gen-proof2-summands pred-name (cdr infos) name)))
    (cons summand summands)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-proof2-deftagsum ((pred-name symbolp)
                                     (infos defind-irule-info-listp)
                                     (levels symbol-set-listp)
                                     (preds-in-previous-cliques symbol-setp)
                                     (prepworkp booleanp)
                                     (name symbolp)
                                     (xdocp booleanp))
  :guard (no-duplicatesp-equal (defind-irule-info-list->name infos))
  :returns (deftagsum pseudo-event-formp)
  :short "Generate a @('p[i]-2-proof') fixtype."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is like @(tsee defind-gen-proof-deftagsum);
     see that function for the treatment of levels.")
   (xdoc::p
    "Here the @(':xvar') option is not just advisable but necessary:
     since the fields are named after the variables of the rules,
     the default @('x') would clash with a rule variable @('x'),
     which FTY rejects with a hard error.
     We use @(tsee defind-proof2-xvar-name),
     which @(tsee defind-check-proof2-names) establishes to be distinct from
     the variables of the rules;
     this is the caveat noted in @(tsee defind-gen-assertion-defprod),
     discharged here."))
  (b* ((pred2-name (defind-pred2-name pred-name name))
       (xvar (defind-proof2-xvar-name name))
       (summands (defind-gen-proof2-summands pred-name infos name))
       (measurep (consp (cdr (symbol-set-list-fix levels))))
       (level (defind-pred-level pred-name levels))
       (override-rule (and (< 0 level)
                           (defind-pred-override-rule
                             pred-name level levels
                             preds-in-previous-cliques infos))))
    `(fty::deftagsum ,(defind-proof-type-name pred2-name name)
       ,@(and xdocp
              `(:parents (,(symbol-lfix name))
                :short ,(str::cat
                         "Fixtype of proofs for predicate @('"
                         (str::downcase-string (symbol-name pred2-name))
                         "').")))
       ,@summands
       ,@(and override-rule
              `(:base-case-override ,(defind-irule-tag override-rule)))
       ,@(and measurep
              `(:measure (two-nats-measure (acl2-count ,xvar) ,level)))
       :pred ,(defind-proof-recog-name pred2-name name)
       :xvar ,xvar
       ,@(and prepworkp
              '(:prepwork ((set-induction-depth-limit 1)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-proof2-deftagsums ((pred-infos defind-pred-info-listp)
                                      (irule-infos defind-irule-info-listp)
                                      (levels symbol-set-listp)
                                      (preds-in-previous-cliques symbol-setp)
                                      (prepworkp booleanp)
                                      (name symbolp)
                                      (xdocp booleanp))
  :guard (and (no-duplicatesp-equal (defind-pred-info-list->name pred-infos))
              (no-duplicatesp-equal (defind-irule-info-list->name irule-infos)))
  :returns (deftagsums pseudo-event-form-listp)
  :short "Generate the @('p[i]-2-proof') fixtypes."
  (b* (((when (endp pred-infos)) nil)
       (pred-name (defind-pred-info->name (car pred-infos)))
       (event (defind-gen-proof2-deftagsum pred-name irule-infos
                levels preds-in-previous-cliques prepworkp name xdocp))
       (events (defind-gen-proof2-deftagsums
                 (cdr pred-infos) irule-infos
                 levels preds-in-previous-cliques prepworkp name xdocp)))
    (cons event events)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-proof2-fixtypes ((pred-infos defind-pred-info-listp)
                                    (irule-infos defind-irule-info-listp)
                                    (leveled-cliques symbol-set-list-listp)
                                    (name symbolp)
                                    (xdocp booleanp))
  :guard (and (no-duplicatesp-equal (defind-pred-info-list->name pred-infos))
              (no-duplicatesp-equal (defind-irule-info-list->name irule-infos)))
  :returns (events pseudo-event-form-listp)
  :short "Generate the fixtypes of proofs for the @('p[i]-2') predicates,
          for all the cliques."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is like @(tsee defind-gen-proof-fixtypes)."))
  (defind-gen-proof2-fixtypes-loop
    leveled-cliques nil pred-infos irule-infos name xdocp)

  :prepwork

  ((define defind-gen-proof2-fixtypes-loop
     ((leveled-cliques symbol-set-list-listp)
      (preds-in-previous-cliques symbol-setp)
      (pred-infos defind-pred-info-listp)
      (irule-infos defind-irule-info-listp)
      (name symbolp)
      (xdocp booleanp))
     :guard (and (no-duplicatesp-equal
                  (defind-pred-info-list->name pred-infos))
                 (no-duplicatesp-equal
                  (defind-irule-info-list->name irule-infos)))
     :returns (events pseudo-event-form-listp)
     :parents nil
     (b* (((when (endp leveled-cliques)) nil)
          (levels (symbol-set-list-fix (car leveled-cliques)))
          (clique-preds (set::set-list-union levels))
          (clique-pred-infos (defind-lookup-pred-set clique-preds pred-infos))
          (events (defind-gen-proof2-fixtypes-loop
                    (cdr leveled-cliques)
                    (set::union clique-preds
                                (symbol-sfix preds-in-previous-cliques))
                    pred-infos irule-infos name xdocp))
          ((unless (consp clique-pred-infos))
           (raise "Internal error: no predicates in clique with levels ~x0."
                  levels)
           events)
          (event
           (if (endp (cdr clique-pred-infos))
               (defind-gen-proof2-deftagsum
                 (defind-pred-info->name (car clique-pred-infos))
                 irule-infos levels preds-in-previous-cliques
                 t name xdocp)
             (b* ((deftagsums (defind-gen-proof2-deftagsums
                                clique-pred-infos irule-infos
                                levels preds-in-previous-cliques
                                nil name xdocp))
                  (deftypes-name
                    (defind-proof-type-clique-name
                      (defind-pred2-name
                        (defind-pred-info->name (car clique-pred-infos))
                        name)
                      name)))
               `(fty::deftypes ,deftypes-name
                  ,@(and xdocp
                         `(:parents (,(symbol-lfix name))
                           :short ,(str::cat
                                    "Fixtypes of proofs for predicates "
                                    (defind-preds-doc-string
                                      (defind-pred-info-list->name
                                        clique-pred-infos))
                                    ".")))
                  ,@deftagsums
                  :prepwork ((set-induction-depth-limit 1)))))))
       (cons event events))
     :no-function nil
     :guard-hints
     (("Goal" :in-theory (enable set-listp-when-symbol-set-listp))))))

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
    "If a premise contains a @('p[i]') predicate,
     we generate an equality between the premise and the variable.
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
  :long
  (xdoc::topstring
   (xdoc::p
    "The theories for the fixing equivalence include
     the assertion theorems for the predicates of
     both the conclusion and the premises of the rule
     (without duplicates)."))
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
       (assert-thms (defind-gen-irule-valid-fn-loop
                      (set::insert info.conclusion.name
                                   (defind-preds-in-premises info.premises))
                      name))
       (xdoc?
        (and xdocp
             `(:parents (,(symbol-lfix name))
               :short ,(str::cat "Validity of an instance of the rule @('"
                                 (str::downcase-string (symbol-name info.name))
                                 "').")))))
    (if (defind-irule-groundp info)
        `(define ,fn-name (,concl-formal ,@prem-formals)
           :returns (yes/no booleanp
                            :hints (("Goal" :in-theory '(,fn-name
                                                         booleanp))))
           ,@xdoc?
           ,body/matrix
           :verify-guards nil
           :hooks ((:fix :hints (("Goal" :in-theory '(,fn-name
                                                      ,@assert-thms))))))
      `(define-sk ,fn-name (,concl-formal ,@prem-formals)
         :returns (yes/no booleanp
                          :hints (("Goal" :in-theory '(,fn-name
                                                       booleanp))))
         ,@xdoc?
         (exists ,vars ,body/matrix)
         :verify-guards nil
         ///
         (local (in-theory '(,@assert-thms)))
         (fty::deffixequiv-sk ,fn-name
           :args (,concl-formal ,@prem-formals)))))

  :prepwork

  ((local (in-theory (enable emptyp-of-symbol-sfix)))

   (define defind-gen-irule-valid-fn-loop ((preds symbol-setp)
                                           (name symbolp))
     :returns (thms true-listp)
     :parents nil
     (b* (((when (set::emptyp (symbol-sfix preds))) nil)
          (pred (set::head preds))
          (thms (defind-gen-irule-valid-fn-loop (set::tail preds) name)))
       (list* (defind-assert-fix-id-thm-name pred name)
              (defind-assert-fix-return-thm-name pred name)
              (defind-equal-of-assert-thm-name pred name)
              thms)))))

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

(define defind-gen-proof2-irule-valid-fn-prems
  ((infos defind-premise-info-listp))
  :returns (conjuncts true-listp)
  :short "Generate the conjuncts for the premises of an inference rule
          in a @('p[l[k]]-2-rule[k]-validp') function."
  :long
  (xdoc::topstring
   (xdoc::p
    "Only the premises that are not calls of the predicates being defined
     contribute:
     the other ones are checked
     against the proofs of those premises
     in the @('p[i]-2-proof-validp') function.
     The premises are used as written
     because the variables of the rule are formals of this function."))
  (b* (((when (endp infos)) nil)
       (info (car infos))
       ((when (defind-premise-info-case info :pred))
        (defind-gen-proof2-irule-valid-fn-prems (cdr infos)))
       (conjunct (defind-term-info->uterm
                  (defind-premise-info-other->term info))))
    (cons conjunct
          (defind-gen-proof2-irule-valid-fn-prems (cdr infos)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-proof2-irule-valid-fn-concl ((args defind-term-info-listp)
                                                (concl-vars symbol-listp))
  :returns (conjuncts true-listp)
  :short "Generate the conjuncts for the conclusion of an inference rule
          in a @('p[l[k]]-2-rule[k]-validp') function."
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
          (defind-gen-proof2-irule-valid-fn-concl
            (cdr args) (cdr concl-vars)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-proof2-irule-valid-fn ((info defind-irule-infop)
                                          (concl-vars symbol-listp)
                                          (name symbolp)
                                          (xdocp booleanp))
  :returns (event pseudo-event-formp)
  :short "Generate a @('p[l[k]]-2-rule[k]-validp') function."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the counterpart of @(tsee defind-gen-irule-valid-fn).
     It checks the conditions of the rule
     that do not involve the proofs of the premises,
     i.e. the premises that are not calls of the predicates being defined,
     and the equalities between the arguments of the conclusion
     and the ones that the rule derives.")
   (xdoc::p
    "Unlike @(tsee defind-gen-irule-valid-fn),
     this is never a @(tsee std::define-sk):
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
       (pred2-name (defind-pred2-name cinfo.name name))
       (fn-name (defind-irule-valid-fn-name pred2-name info.name name))
       (vars (defind-irule-info-free-vars info))
       (prem-conjuncts (defind-gen-proof2-irule-valid-fn-prems info.premises))
       (concl-conjuncts
        (defind-gen-proof2-irule-valid-fn-concl cinfo.args concl-vars))
       (body (defind-gen-conjunction
              (append prem-conjuncts concl-conjuncts))))
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
  :guard-hints (("Goal" :in-theory (enable symbol-listp-when-symbol-setp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-proof2-irule-valid-fns ((infos defind-irule-info-listp)
                                           (pred-infos defind-pred-info-listp)
                                           (name symbolp)
                                           (xdocp booleanp))
  :guard (no-duplicatesp-equal (defind-pred-info-list->name pred-infos))
  :returns (events pseudo-event-form-listp)
  :short "Generate the @('p[l[k]]-2-rule[k]-validp') functions."
  (b* (((when (endp infos)) nil)
       ((defind-irule-info info) (car infos))
       (pred-name (defind-conclusion-info->name info.conclusion))
       (pinfo (defind-lookup-pred pred-name pred-infos))
       ((unless pinfo)
        (raise "Internal error: predicate ~x0 not found." pred-name))
       (concl-vars (defind-proof2-concl-var-names
                     (defind-pred-info->formals pinfo) name))
       (event (defind-gen-proof2-irule-valid-fn
                (car infos) concl-vars name xdocp))
       (events (defind-gen-proof2-irule-valid-fns
                 (cdr infos) pred-infos name xdocp)))
    (cons event events))
  :no-function nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-proof-valid-fn-case-prems ((infos defind-premise-info-listp)
                                              (pred-name symbolp)
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
  :long
  (xdoc::topstring
   (xdoc::p
    "Two different predicates are involved here.
     The predicate of a premise determines
     the validity and conclusion functions applied to the proof of the premise.
     The predicate of the conclusion of the rule, i.e. @('pred-name'),
     determines instead the fixtype of proofs that has
     the summand for the rule, and thus the accessors of the premise proofs,
     along with the theorems about those accessors.")
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
  (b* (((when (endp infos)) (mv nil nil nil nil))
       (info (car infos)))
    (defind-premise-info-case
      info
      :pred (b* ((valid-fn (defind-proof-valid-fn-name info.name name))
                 (concl-fn (defind-proof-concl-fn-name info.name name))
                 (prem-proof-var (defind-proof-prem-var-name num name))
                 (conjunct `(,valid-fn ,prem-proof-var))
                 (concl-call `(,concl-fn ,prem-proof-var))
                 (count-thm (and (equal info.name (symbol-lfix pred-name))
                                 (defind-proof-prem-count-thm-name
                                   info.name pred-name irule-name num name)))
                 (fixing-thm (defind-proof-prem-fixing-thm-name
                               pred-name irule-name num name))
                 ((mv conjuncts concl-calls count-thms fixing-thms)
                  (defind-gen-proof-valid-fn-case-prems
                    (cdr infos) pred-name irule-name (1+ (lposfix num)) name)))
              (mv (cons conjunct conjuncts)
                  (cons concl-call concl-calls)
                  (if count-thm (cons count-thm count-thms) count-thms)
                  (cons fixing-thm fixing-thms)))
      :other (defind-gen-proof-valid-fn-case-prems
               (cdr infos) pred-name irule-name num name))))

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
        (defind-gen-proof-valid-fn-case-prems
          infos pred-name irule-name 1 name))
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
                                   (standalonep booleanp)
                                   (name symbolp)
                                   (xdocp booleanp))
  :guard (no-duplicatesp-equal (defind-irule-info-list->name infos))
  :returns (event pseudo-event-formp)
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
     are in the enclosing @(tsee defines)."))
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
       ((unless standalonep)
        `(define ,fn-name ((,fn-formal ,proof-recog))
           :returns (yes/no booleanp)
           ,@(and xdocp
                  `(:parents (,(symbol-lfix name))
                    :short ,(str::cat "Validity of a proof for @('"
                                      (str::downcase-string
                                       (symbol-name pred-name))
                                      "').")))
           (,proof-case ,fn-formal ,@keywords+terms)
           :measure (,count-fn ,fn-formal)))
       (recursivep (defind-pred-recursivep pred-name infos))
       (poss-thm (defind-proof-kind-poss-thm-name pred-name name))
       (kind-fixing-thm (defind-proof-kind-fixing-thm-name pred-name name)))
    `(define ,fn-name ((,fn-formal ,proof-recog))
       :returns (yes/no booleanp
                        :hints (("Goal"
                                 ,@(and recursivep '(:induct t))
                                 :in-theory '(,fn-name
                                              (:e booleanp)
                                              ,@return-thms))))
       ,@(and xdocp
              `(:parents (,(symbol-lfix name))
                :short ,(str::cat "Validity of proofs for predicate @('"
                                  (str::downcase-string (symbol-name pred-name))
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
                                           ,@concl-fixing-thms))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-proof-valid-fn-clique ((clique-pred-infos
                                           defind-pred-info-listp)
                                          (irule-infos defind-irule-info-listp)
                                          (name symbolp)
                                          (xdocp booleanp))
  :guard (and (consp clique-pred-infos)
              (no-duplicatesp-equal
               (defind-pred-info-list->name clique-pred-infos))
              (no-duplicatesp-equal
               (defind-irule-info-list->name irule-infos)))
  :returns (event pseudo-event-formp)
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
     on the proof variable and on its fixed version.
     Since the functions of the clique are mutually recursive,
     ACL2's heuristics do not expand those calls during the flag induction.
     This is unlike the case of a predicate that forms a singleton clique,
     where the induction is on the (single) validity function itself,
     and thus the calls of that function in the fixing equivalence
     are expanded as part of the induction."))
  (b* (((mv members expands term-thms fixequiv-expands fixequiv-thms)
        (defind-gen-proof-valid-fn-clique-loop
          clique-pred-infos irule-infos name xdocp))
       ((mv valid-tps prem-acc-thms)
        (defind-gen-proof-valid-fn-clique-rules-loop
          irule-infos
          (defind-pred-info-list->name clique-pred-infos)
          name))
       (first-pred (defind-pred-info->name (car clique-pred-infos)))
       (defines-name (defind-proof-valid-fn-clique-name first-pred name))
       (flag-fn (defind-proof-valid-fn-clique-flag-name first-pred name))
       (fn-formal (defind-proof-var-name name)))
    `(defines ,defines-name
       ,@(and xdocp
              `(:parents (,(symbol-lfix name))
                :short ,(str::cat
                         "Validity of proofs for predicates "
                         (defind-preds-doc-string
                           (defind-pred-info-list->name clique-pred-infos))
                         ".")))
       ,@members
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
                  :induct (,flag-fn ,(defind-flag-var-name name) ,fn-formal)
                  :expand ,fixequiv-expands
                  :in-theory '(,flag-fn
                               not
                               (:e equal)
                               ,@fixequiv-thms
                               ,@prem-acc-thms))))))

  :guard-hints
  (("Goal"
    :in-theory (enable true-listp-when-pseudo-event-form-listp-rewrite)))

  :prepwork

  ((define defind-gen-proof-valid-fn-clique-loop
     ((pred-infos defind-pred-info-listp)
      (irule-infos defind-irule-info-listp)
      (name symbolp)
      (xdocp booleanp))
     :guard (no-duplicatesp-equal (defind-irule-info-list->name irule-infos))
     :returns (mv (events pseudo-event-form-listp)
                  (expands true-listp)
                  (term-thms true-listp)
                  (fixequiv-expands true-listp)
                  (fixequiv-thms true-listp))
     :parents nil
     (b* (((when (endp pred-infos)) (mv nil nil nil nil nil))
          (pred-name (defind-pred-info->name (car pred-infos)))
          (event (defind-gen-proof-valid-fn
                   pred-name irule-infos nil name xdocp))
          (count-fn (defind-proof-count-fn-name pred-name name))
          (fn-formal (defind-proof-var-name name))
          (expand `(,count-fn ,fn-formal))
          (term-thms1
           (list (defind-proof-kind-poss-thm-name pred-name name)
                 `(:t ,count-fn)
                 (defind-proof-count-return-thm-name pred-name name)))
          ((mv & & & prem-fixing-thms concl-fixing-thms)
           (defind-gen-proof-valid-fn-cases pred-name irule-infos name))
          (valid-fn (defind-proof-valid-fn-name pred-name name))
          (fixer (defind-proof-fixer-name pred-name name))
          (fixequiv-expands1
           (list `(,valid-fn ,fn-formal)
                 `(,valid-fn (,fixer ,fn-formal))))
          (fixequiv-thms1
           (append prem-fixing-thms
                   concl-fixing-thms
                   (list valid-fn
                         (defind-proof-kind-poss-thm-name pred-name name)
                         (defind-proof-kind-fixing-thm-name pred-name name)
                         (defind-proof-fix-id-thm-name pred-name name))))
          ((mv events expands term-thms fixequiv-expands fixequiv-thms)
           (defind-gen-proof-valid-fn-clique-loop
             (cdr pred-infos) irule-infos name xdocp)))
       (mv (cons event events)
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
          (valid-tp `(:t ,(defind-irule-valid-fn-name cinfo.name
                                                      info.name
                                                      name)))
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
                    info.name pred-name irule-name num name)
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
                                    (xdocp booleanp))
  :guard (and (no-duplicatesp-equal (defind-pred-info-list->name pred-infos))
              (no-duplicatesp-equal (defind-irule-info-list->name irule-infos)))
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
    leveled-cliques pred-infos irule-infos name xdocp)

  :prepwork

  ((define defind-gen-proof-valid-fns-loop
     ((leveled-cliques symbol-set-list-listp)
      (pred-infos defind-pred-info-listp)
      (irule-infos defind-irule-info-listp)
      (name symbolp)
      (xdocp booleanp))
     :guard (and (no-duplicatesp-equal
                  (defind-pred-info-list->name pred-infos))
                 (no-duplicatesp-equal
                  (defind-irule-info-list->name irule-infos)))
     :returns (events pseudo-event-form-listp)
     :parents nil
     (b* (((when (endp leveled-cliques)) nil)
          (levels (symbol-set-list-fix (car leveled-cliques)))
          (clique-preds (set::set-list-union levels))
          (clique-pred-infos (defind-lookup-pred-set clique-preds pred-infos))
          (events (defind-gen-proof-valid-fns-loop
                    (cdr leveled-cliques) pred-infos irule-infos name xdocp))
          ((unless (consp clique-pred-infos))
           (raise "Internal error: no predicates in clique with levels ~x0."
                  levels)
           events)
          (event
           (if (endp (cdr clique-pred-infos))
               (defind-gen-proof-valid-fn
                 (defind-pred-info->name (car clique-pred-infos))
                 irule-infos t name xdocp)
             (defind-gen-proof-valid-fn-clique
               clique-pred-infos irule-infos name xdocp))))
       (cons event events))
     :no-function nil
     :guard-hints
     (("Goal" :in-theory (enable set-listp-when-symbol-set-listp))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-proof2-valid-fn-case-bindings ((vars symbol-listp)
                                                  (name symbolp))
  :returns (bindings true-list-listp)
  :short "Generate the @(tsee let) bindings for the variables of a rule
          in a case of a @('p[i]-2-proof-validp') function."
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
     just as arguments of the @('p[l[k]]-2-rule[k]-validp') function,
     which the caller passes directly."))
  (cond ((endp vars) nil)
        (t (cons (list (symbol-lfix (car vars))
                       (defind-proof-var-field-var-name (car vars) name))
                 (defind-gen-proof2-valid-fn-case-bindings (cdr vars) name)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-proof2-valid-fn-case-prems ((infos defind-premise-info-listp)
                                               (pred-name symbolp)
                                               (irule-name symbolp)
                                               (num posp)
                                               (name symbolp))
  :returns (mv (conjuncts true-listp)
               (count-thms symbol-listp)
               (fixing-thms symbol-listp))
  :short "Generate the conjuncts for the proofs of the premises
          of an inference rule
          in a case of a @('p[i]-2-proof-validp') function,
          along with the names of some relevant theorems."
  :long
  (xdoc::topstring
   (xdoc::p
    "As in @(tsee defind-gen-proof-valid-fn-case-prems),
     only the premises that are calls of the predicates being defined
     contribute.
     Each becomes a call of @('p[j]-2-proof-validp')
     on the proof of the premise
     and on the arguments of the premise as written.")
   (xdoc::p
    "As in @(tsee defind-gen-proof-valid-fn-case-prems),
     two different predicates are involved:
     the one of the premise, which determines
     the validity predicate applied to the proof of the premise,
     and the one of the conclusion of the rule, i.e. @('pred-name'),
     which determines the fixtype of proofs
     that has the summand for the rule,
     and thus the accessors of the proofs of the premises
     along with the theorems about them.
     Both are @('p[i]-2') predicates.
     We return a count theorem only for the premises
     whose predicate is the one of the conclusion;
     see that function for why."))
  (b* (((when (endp infos)) (mv nil nil nil))
       (info (car infos)))
    (defind-premise-info-case
      info
      :pred (b* ((prem-pred2-name (defind-pred2-name info.name name))
                 (valid-fn (defind-proof-valid-fn-name prem-pred2-name name))
                 (prem-proof-var (defind-proof-prem-var-name num name))
                 (conjunct `(,valid-fn ,prem-proof-var
                                       ,@(defind-term-info-list->uterm
                                          info.args)))
                 (count-thm (and (equal prem-pred2-name
                                        (symbol-lfix pred-name))
                                 (defind-proof-prem-count-thm-name
                                   prem-pred2-name pred-name
                                   irule-name num name)))
                 (fixing-thm (defind-proof2-prem-fixing-thm-name
                              pred-name irule-name num name))
                 ((mv conjuncts count-thms fixing-thms)
                  (defind-gen-proof2-valid-fn-case-prems
                    (cdr infos) pred-name irule-name (1+ (lposfix num)) name)))
              (mv (cons conjunct conjuncts)
                  (if count-thm (cons count-thm count-thms) count-thms)
                  (cons fixing-thm fixing-thms)))
      :other (defind-gen-proof2-valid-fn-case-prems
               (cdr infos) pred-name irule-name num name))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-proof2-valid-fn-case ((info defind-irule-infop)
                                         (concl-vars symbol-listp)
                                         (name symbolp))
  :returns (mv (keyword+term true-listp)
               (return-thm symbolp)
               (count-thms symbol-listp)
               (prem-fixing-thms symbol-listp)
               (var-fixing-thms symbol-listp))
  :short "Generate a case of a @('p[i]-2-proof-validp') function,
          along with the names of some relevant theorems."
  :long
  (xdoc::topstring
   (xdoc::p
    "The conjuncts for the proofs of the premises come first,
     followed by a call of the @('p[l[k]]-2-rule[k]-validp') function
     on the arguments of the conclusion and on the variables of the rule.
     If the rule has premises that are calls of the predicates being defined,
     the variables of the rule are bound around the whole conjunction
     and passed as such to that call;
     otherwise there are no bindings,
     and the fields of the proof are passed directly."))
  (b* (((defind-irule-info info))
       ((defind-conclusion-info cinfo) info.conclusion)
       (pred2-name (defind-pred2-name cinfo.name name))
       (tag (defind-irule-tag info.name))
       (vars (defind-irule-info-free-vars info))
       (recursivep (defind-irule-info-recursivep info))
       (valid-irule-fn
        (defind-irule-valid-fn-name pred2-name info.name name))
       ((mv prem-conjuncts count-thms prem-fixing-thms)
        (defind-gen-proof2-valid-fn-case-prems
          info.premises pred2-name info.name 1 name))
       (var-args (if recursivep
                     (symbol-list-fix vars)
                   (defind-proof-var-field-var-names vars name)))
       (irule-conjunct `(,valid-irule-fn
                         ,@(symbol-list-fix concl-vars)
                         ,@var-args))
       (term (defind-gen-conjunction
              (append prem-conjuncts (list irule-conjunct))))
       (bindings (and recursivep
                      (defind-gen-proof2-valid-fn-case-bindings vars name)))
       (term (if bindings `(let ,bindings ,term) term))
       (return-thm
        (defind-irule-valid-return-thm-name pred2-name info.name name))
       (var-fixing-thms (defind-proof2-var-acc-fixing-thm-names
                         pred2-name info.name vars name)))
    (mv `(,tag ,term)
        return-thm count-thms prem-fixing-thms var-fixing-thms))
  :guard-hints (("Goal" :in-theory (enable symbol-listp-when-symbol-setp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-proof2-valid-fn-cases ((pred-name symbolp)
                                          (concl-vars symbol-listp)
                                          (infos defind-irule-info-listp)
                                          (name symbolp))
  :guard (no-duplicatesp-equal (defind-irule-info-list->name infos))
  :returns (mv (keywords+terms true-listp)
               (return-thms symbol-listp)
               (count-thms symbol-listp)
               (prem-fixing-thms symbol-listp)
               (var-fixing-thms symbol-listp))
  :short "Generate the cases of a @('p[i]-2-proof-validp') function,
          along with the names of some relevant theorems."
  :long
  (xdoc::topstring
   (xdoc::p
    "There is one case for each rule whose conclusion is @('p[i]');
     the @('pred-name') input is @('p[i]'), not @('p[i]-2')
     because it is matched against the conclusions of the rules."))
  (b* (((when (endp infos)) (mv nil nil nil nil nil))
       ((defind-irule-info info) (car infos))
       ((unless (equal (defind-conclusion-info->name info.conclusion)
                       (symbol-lfix pred-name)))
        (defind-gen-proof2-valid-fn-cases
          pred-name concl-vars (cdr infos) name))
       ((mv keyword+term return-thm count-thms prem-fixing-thms var-fixing-thms)
        (defind-gen-proof2-valid-fn-case info concl-vars name))
       ((mv keywords+terms
            more-return-thms
            more-count-thms
            more-prem-fixing-thms
            more-var-fixing-thms)
        (defind-gen-proof2-valid-fn-cases
          pred-name concl-vars (cdr infos) name)))
    (mv (cons keyword+term keywords+terms)
        (cons return-thm more-return-thms)
        (append count-thms more-count-thms)
        (append prem-fixing-thms more-prem-fixing-thms)
        (append var-fixing-thms more-var-fixing-thms))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-proof2-valid-fn ((pred-info defind-pred-infop)
                                    (infos defind-irule-info-listp)
                                    (standalonep booleanp)
                                    (name symbolp)
                                    (xdocp booleanp))
  :guard (no-duplicatesp-equal (defind-irule-info-list->name infos))
  :returns (event pseudo-event-formp)
  :short "Generate a @('p[i]-2-proof-validp') function."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is like @(tsee defind-gen-proof-valid-fn);
     see that function for the @('standalonep') input
     and for the treatment of non-recursive predicates.")
   (xdoc::p
    "This takes the information about the predicate, not just its name,
     because the arguments of the conclusion are formals of this function;
     see @(tsee defind-proof2-concl-var-names).")
   (xdoc::p
    "The @(':returns') theorem is also a type prescription rule,
     which @(tsee defind-gen-proof2-pred) uses."))
  (b* (((defind-pred-info pred-info))
       (pred2-name (defind-pred2-name pred-info.name name))
       (fn-name (defind-proof-valid-fn-name pred2-name name))
       (fn-formal (defind-proof-var-name name))
       (proof-recog (defind-proof-recog-name pred2-name name))
       (proof-case (defind-proof-case-name pred2-name name))
       (concl-vars (defind-proof2-concl-var-names pred-info.formals name))
       ((mv keywords+terms
            return-thms
            count-thms
            prem-fixing-thms
            var-fixing-thms)
        (defind-gen-proof2-valid-fn-cases
          pred-info.name concl-vars infos name))
       (count-fn (defind-proof-count-fn-name pred2-name name))
       ((unless standalonep)
        `(define ,fn-name ((,fn-formal ,proof-recog) ,@concl-vars)
           :returns (yes/no booleanp
                            :rule-classes (:rewrite :type-prescription))
           ,@(and xdocp
                  `(:parents (,(symbol-lfix name))
                    :short ,(str::cat "Validity of a proof for @('"
                                      (str::downcase-string
                                       (symbol-name pred2-name))
                                      "').")))
           (,proof-case ,fn-formal ,@keywords+terms)
           :measure (,count-fn ,fn-formal)))
       (recursivep (defind-pred-recursivep pred-info.name infos))
       (poss-thm (defind-proof-kind-poss-thm-name pred2-name name))
       (kind-fixing-thm (defind-proof2-kind-fixing-thm-name pred2-name name)))
    `(define ,fn-name ((,fn-formal ,proof-recog) ,@concl-vars)
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
                                   (symbol-name pred2-name))
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
                                           ,@var-fixing-thms))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-proof2-valid-fn-clique ((clique-pred-infos
                                            defind-pred-info-listp)
                                           (irule-infos defind-irule-info-listp)
                                           (name symbolp)
                                           (xdocp booleanp))
  :guard (and (consp clique-pred-infos)
              (no-duplicatesp-equal
               (defind-pred-info-list->name clique-pred-infos))
              (no-duplicatesp-equal
               (defind-irule-info-list->name irule-infos)))
  :returns (event pseudo-event-formp)
  :short "Generate a @(tsee defines) with
          the @('p[i]-2-proof-validp') functions of
          a clique of multiple predicates."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is like @(tsee defind-gen-proof-valid-fn-clique),
     including the quoted theories of
     the termination hints and of the fixing equivalence.")
   (xdoc::p
    "Where that function uses the type prescriptions that ACL2 infers
     for the count functions and for the rule validity predicates,
     we use the proved ones instead:
     the return theorem of the count function,
     and the @(':returns') theorem of each rule validity predicate,
     which is also a type prescription rule
     (see @(tsee defind-gen-proof2-irule-valid-fn)).")
   (xdoc::p
    "We do not supply the induction hint of the fixing equivalence,
     for the reason given in
     @(tsee defind-gen-proof2-pred-alt-when-proof-valid-thm-clique):
     the flag function takes the arguments of the conclusions
     of all the predicates of the clique,
     and the flag machinery supplies the call on its formals."))
  (b* (((mv members expands term-thms fixequiv-thms)
        (defind-gen-proof2-valid-fn-clique-loop
          clique-pred-infos irule-infos name xdocp))
       ((mv valid-tps prem-acc-thms)
        (defind-gen-proof2-valid-fn-clique-rules-loop
          irule-infos
          (defind-pred-info-list->name clique-pred-infos)
          name))
       (first-pred2 (defind-pred2-name
                      (defind-pred-info->name (car clique-pred-infos))
                      name))
       (defines-name (defind-proof-valid-fn-clique-name first-pred2 name))
       (flag-fn (defind-proof-valid-fn-clique-flag-name first-pred2 name)))
    `(defines ,defines-name
       ,@(and xdocp
              `(:parents (,(symbol-lfix name))
                :short ,(str::cat
                         "Validity of proofs for predicates "
                         (defind-preds-doc-string
                           (defind-pred-info-list->name clique-pred-infos))
                         ".")))
       ,@members
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
                  :in-theory '(,flag-fn
                               not
                               (:e equal)
                               ,@fixequiv-thms
                               ,@prem-acc-thms))))))

  :guard-hints
  (("Goal"
    :in-theory (enable true-listp-when-pseudo-event-form-listp-rewrite)))

  :prepwork

  ((define defind-gen-proof2-valid-fn-clique-loop
     ((pred-infos defind-pred-info-listp)
      (irule-infos defind-irule-info-listp)
      (name symbolp)
      (xdocp booleanp))
     :guard (no-duplicatesp-equal (defind-irule-info-list->name irule-infos))
     :returns (mv (events pseudo-event-form-listp)
                  (expands true-listp)
                  (term-thms true-listp)
                  (fixequiv-thms true-listp))
     :parents nil
     (b* (((when (endp pred-infos)) (mv nil nil nil nil))
          ((defind-pred-info info) (car pred-infos))
          (pred2-name (defind-pred2-name info.name name))
          (event (defind-gen-proof2-valid-fn
                   (car pred-infos) irule-infos nil name xdocp))
          (count-fn (defind-proof-count-fn-name pred2-name name))
          (fn-formal (defind-proof-var-name name))
          (expand `(,count-fn ,fn-formal))
          (poss-thm (defind-proof-kind-poss-thm-name pred2-name name))
          (term-thms1
           (list poss-thm
                 (defind-proof-count-return-thm-name pred2-name name)))
          (concl-vars (defind-proof2-concl-var-names info.formals name))
          ((mv & & & prem-fixing-thms var-fixing-thms)
           (defind-gen-proof2-valid-fn-cases
             info.name concl-vars irule-infos name))
          (fixequiv-thms1
           (append prem-fixing-thms
                   var-fixing-thms
                   (list (defind-proof-valid-fn-name pred2-name name)
                         poss-thm
                         (defind-proof2-kind-fixing-thm-name pred2-name name)
                         (defind-proof-fix-id-thm-name pred2-name name))))
          ((mv events expands term-thms fixequiv-thms)
           (defind-gen-proof2-valid-fn-clique-loop
             (cdr pred-infos) irule-infos name xdocp)))
       (mv (cons event events)
           (cons expand expands)
           (append term-thms1 term-thms)
           (append fixequiv-thms1 fixequiv-thms))))

   (define defind-gen-proof2-valid-fn-clique-rules-loop
     ((irule-infos defind-irule-info-listp)
      (clique-pred-names symbol-listp)
      (name symbolp))
     :returns (mv (valid-tps true-listp)
                  (prem-acc-thms true-listp))
     :parents nil
     (b* (((when (endp irule-infos)) (mv nil nil))
          ((mv valid-tps prem-acc-thms)
           (defind-gen-proof2-valid-fn-clique-rules-loop
             (cdr irule-infos) clique-pred-names name))
          ((defind-irule-info info) (car irule-infos))
          ((defind-conclusion-info cinfo) info.conclusion)
          ((unless (member-eq cinfo.name
                              (symbol-list-fix clique-pred-names)))
           (mv valid-tps prem-acc-thms))
          (pred2-name (defind-pred2-name cinfo.name name))
          (valid-tp `(:type-prescription
                      ,(defind-irule-valid-return-thm-name
                         pred2-name info.name name)))
          (prem-acc-thms1
           (defind-gen-proof2-valid-fn-clique-rules-loop-loop
             info.premises pred2-name info.name 1 name)))
       (mv (cons valid-tp valid-tps)
           (append prem-acc-thms1 prem-acc-thms)))

     :prepwork

     ((define defind-gen-proof2-valid-fn-clique-rules-loop-loop
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
                    (defind-pred2-name info.name name)
                    pred-name irule-name num name)
                  (defind-gen-proof2-valid-fn-clique-rules-loop-loop
                    (cdr prem-infos) pred-name irule-name
                    (1+ (lposfix num)) name))
            :other
            (defind-gen-proof2-valid-fn-clique-rules-loop-loop
              (cdr prem-infos) pred-name irule-name num name))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-proof2-valid-fns ((pred-infos defind-pred-info-listp)
                                     (irule-infos defind-irule-info-listp)
                                     (leveled-cliques symbol-set-list-listp)
                                     (name symbolp)
                                     (xdocp booleanp))
  :guard (and (no-duplicatesp-equal (defind-pred-info-list->name pred-infos))
              (no-duplicatesp-equal (defind-irule-info-list->name irule-infos)))
  :returns (events pseudo-event-form-listp)
  :short "Generate the proof validity functions
          of the @('p[i]-2') predicates, for all the cliques."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is like @(tsee defind-gen-proof-valid-fns)."))
  (defind-gen-proof2-valid-fns-loop
    leveled-cliques pred-infos irule-infos name xdocp)

  :prepwork

  ((define defind-gen-proof2-valid-fns-loop
     ((leveled-cliques symbol-set-list-listp)
      (pred-infos defind-pred-info-listp)
      (irule-infos defind-irule-info-listp)
      (name symbolp)
      (xdocp booleanp))
     :guard (and (no-duplicatesp-equal
                  (defind-pred-info-list->name pred-infos))
                 (no-duplicatesp-equal
                  (defind-irule-info-list->name irule-infos)))
     :returns (events pseudo-event-form-listp)
     :parents nil
     (b* (((when (endp leveled-cliques)) nil)
          (levels (symbol-set-list-fix (car leveled-cliques)))
          (clique-preds (set::set-list-union levels))
          (clique-pred-infos (defind-lookup-pred-set clique-preds pred-infos))
          (events (defind-gen-proof2-valid-fns-loop
                    (cdr leveled-cliques) pred-infos irule-infos name xdocp))
          ((unless (consp clique-pred-infos))
           (raise "Internal error: no predicates in clique with levels ~x0."
                  levels)
           events)
          (event
           (if (endp (cdr clique-pred-infos))
               (defind-gen-proof2-valid-fn
                 (car clique-pred-infos) irule-infos t name xdocp)
             (defind-gen-proof2-valid-fn-clique
               clique-pred-infos irule-infos name xdocp))))
       (cons event events))
     :no-function nil
     :guard-hints
     (("Goal" :in-theory (enable set-listp-when-symbol-set-listp))))))

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

(define defind-gen-proof2-pred ((pred-info defind-pred-infop)
                                (standalonep booleanp)
                                (name symbolp)
                                (xdocp booleanp))
  :returns (event pseudo-event-formp)
  :short "Generate a @('p[i]-2') predicate."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is like @(tsee defind-gen-pred),
     but the arguments of the conclusion are arguments of
     the proof validity predicate,
     instead of being compared with the conclusion of the proof.
     So this needs neither the @('p[i]-proof->conclusion') function
     nor the @('p[i]-assertion') fixtype.")
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
     not something established."))
  (b* (((defind-pred-info pred-info))
       (pred2-name (defind-pred2-name pred-info.name name))
       (proof (defind-proof-var-name name))
       (proofp (defind-proof-recog-name pred2-name name))
       (proof-validp (defind-proof-valid-fn-name pred2-name name))
       (valid-return-thm (defind-proof-valid-return-thm-name
                           pred2-name standalonep name))
       (witness (defind-proof-witness-fn-name pred2-name name)))
    `(define-sk ,pred2-name (,@pred-info.formals)
       :returns (yes/no booleanp
                        :hints (("Goal"
                                 :in-theory
                                 '(,pred2-name
                                   booleanp
                                   (:type-prescription ,valid-return-thm)))))
       ,@(and xdocp
              `(:parents (,(symbol-lfix name))
                :short ,(str::cat "Definition of the predicate @('"
                                  (str::downcase-string
                                   (symbol-name pred2-name))
                                  "') via proof existence.")))
       (exists (,proof)
               (and (,proofp ,proof)
                    (,proof-validp ,proof ,@pred-info.formals)))
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

(define defind-gen-proof2-preds ((pred-infos defind-pred-info-listp)
                                 (leveled-cliques symbol-set-list-listp)
                                 (name symbolp)
                                 (xdocp booleanp))
  :guard (no-duplicatesp-equal (defind-pred-info-list->name pred-infos))
  :returns (events pseudo-event-form-listp)
  :short "Generate all the @('p[i]-2') predicates."
  :long
  (xdoc::topstring
   (xdoc::p
    "We go through the cliques, as @(tsee defind-gen-proof2-valid-fns) does,
     because each predicate needs to know whether
     its proof validity predicate is standalone
     or a member of a clique of two or more;
     see @(tsee defind-proof-valid-return-thm-name)."))
  (b* (((when (endp leveled-cliques)) nil)
       (levels (symbol-set-list-fix (car leveled-cliques)))
       (clique-preds (set::set-list-union levels))
       (clique-pred-infos (defind-lookup-pred-set clique-preds pred-infos))
       (standalonep (and (consp clique-pred-infos)
                         (endp (cdr clique-pred-infos))))
       (events (defind-gen-proof2-preds
                 pred-infos (cdr leveled-cliques) name xdocp)))
    (append (defind-gen-proof2-preds-loop
              clique-pred-infos standalonep name xdocp)
            events))
  :no-function nil
  :guard-hints
  (("Goal" :in-theory (enable set-listp-when-symbol-set-listp)))

  :prepwork
  ((define defind-gen-proof2-preds-loop ((pred-infos defind-pred-info-listp)
                                         (standalonep booleanp)
                                         (name symbolp)
                                         (xdocp booleanp))
     :returns (events pseudo-event-form-listp)
     :parents nil
     (cond ((endp pred-infos) nil)
           (t (cons (defind-gen-proof2-pred
                      (car pred-infos) standalonep name xdocp)
                    (defind-gen-proof2-preds-loop
                      (cdr pred-infos) standalonep name xdocp)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-irule-proof-fn ((info defind-irule-infop)
                                   (pred-infos defind-pred-info-listp)
                                   (name symbolp)
                                   (xdocp booleanp))
  :guard (no-duplicatesp-equal (defind-pred-info-list->name pred-infos))
  :returns (event pseudo-event-formp)
  :short "Generate a @('p[l[k]]-proof-for-rule[k]') function."
  :long
  (xdoc::topstring
   (xdoc::p
    "The theory for the validity theorem includes
     the fixing theorems for the predicates of
     both the conclusion and the premises of the rule
     (without duplicates).
     The theory for the conclusion theorem
     only involves the predicate of the conclusion."))
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
        (defind-gen-irule-proof-fn-loop
          cinfo.name info.name info.premises 1 name))
       (all-hyps (append subproof-hyps other-prems subproof-eqs))
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
        (if (defind-irule-groundp info)
            (defind-irule-valid-fn-name cinfo.name info.name name)
          (defind-irule-valid-suff-thm-name cinfo.name info.name name)))
       (concl (defind-concl-var-name name))
       (fixing-thms (defind-gen-irule-proof-fn-preds-loop
                      (set::insert cinfo.name
                                   (defind-preds-in-premises info.premises))
                      name))
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
         ,@(and all-hyps
                (list :hyp (defind-gen-conjunction all-hyps)))
         :hints (("Goal"
                  :use (:instance ,suff/def-thm
                                  (,concl (,assert ,@concl-args))
                                  ,@prem-insts)
                  :in-theory '(,@fixing-thms
                               ,fn-name
                               ,proof-valid-fn
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

  ((local (in-theory (enable emptyp-of-symbol-sfix)))

   (define defind-gen-irule-proof-fn-preds-loop ((preds symbol-setp)
                                                 (name symbolp))
     :returns (thms true-listp)
     :parents nil
     (b* (((when (set::emptyp (symbol-sfix preds))) nil)
          (pred (set::head preds))
          (thms (defind-gen-irule-proof-fn-preds-loop (set::tail preds) name)))
       (list* (defind-valid-congruence-thm-name pred name)
              (defind-assert-fix-id-thm-name pred name)
              (defind-assert-constr-return-thm-name pred name)
              (defind-proof-concl-fixing-thm-name pred name)
              (defind-proof-fix-equiv-thm-name pred name)
              thms)))

   (define defind-gen-irule-proof-fn-loop ((pred-name symbolp)
                                           (irule-name symbolp)
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
                                pred-name irule-name num name))
                    ((mv subproof-vars
                         subproof-formals
                         subproof-hyps
                         subproof-eqs
                         prem-insts
                         prem-thms
                         other-prems)
                     (defind-gen-irule-proof-fn-loop
                       pred-name irule-name (cdr infos)
                       (1+ (lposfix num)) name)))
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
                        pred-name irule-name (cdr infos) num name)))
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
       ,(defind-gen-implication (append pred-hyps other-hyps) concl)
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

(define defind-gen-proof2-irule-thm-hyps ((infos defind-premise-info-listp)
                                          (name symbolp))
  :returns (mv (pred-hyps true-listp)
               (other-hyps true-listp))
  :short "Generate the hypotheses of a @('p[l[k]]-2-rule[k]') theorem."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is like @(tsee defind-gen-irule-thm-hyps),
     but the premises that are calls of the predicates being defined
     become calls of the @('p[i]-2') predicates."))
  (b* (((when (endp infos)) (mv nil nil))
       (info (car infos))
       ((mv pred-hyps other-hyps)
        (defind-gen-proof2-irule-thm-hyps (cdr infos) name)))
    (defind-premise-info-case
      info
      :pred (mv (cons `(,(defind-pred2-name info.name name)
                        ,@(defind-term-info-list->uterm info.args))
                      pred-hyps)
                other-hyps)
      :other (mv pred-hyps
                 (cons (defind-term-info->uterm info.term)
                       other-hyps)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-proof2-irule-thm-prems ((infos defind-premise-info-listp)
                                           (pred-name symbolp)
                                           (irule-name symbolp)
                                           (num posp)
                                           (name symbolp))
  :returns (mv (proofcalls true-listp)
               (of-constr-thms symbol-listp)
               (fix-id-thms symbol-listp))
  :short "Generate the proofs of the premises of a rule
          in a @('p[l[k]]-2-rule[k]') theorem,
          along with the names of some relevant theorems."
  :long
  (xdoc::topstring
   (xdoc::p
    "The proof of a premise that is a call of a predicate being defined
     is the witness of that call,
     which the corresponding hypothesis of the theorem provides.")
   (xdoc::p
    "The @('pred-name') input is the @('p[i]-2') predicate
     of the conclusion of the rule,
     because the accessors belong to the fixtype of its proofs.
     The fixing identity theorem of each premise is instead
     the one of the predicate of the premise,
     because that is the fixtype of the accessed field."))
  (b* (((when (endp infos)) (mv nil nil nil))
       (info (car infos)))
    (defind-premise-info-case
      info
      :pred (b* ((prem-pred2-name (defind-pred2-name info.name name))
                 (witfn (defind-proof-witness-fn-name prem-pred2-name name))
                 (proofcall
                  `(,witfn ,@(defind-term-info-list->uterm info.args)))
                 (of-constr-thm (defind-proof-prem-of-constr-thm-name
                                  pred-name irule-name num name))
                 (fix-id-thm (defind-proof-fix-id-thm-name
                               prem-pred2-name name))
                 ((mv proofcalls of-constr-thms fix-id-thms)
                  (defind-gen-proof2-irule-thm-prems
                    (cdr infos) pred-name irule-name (1+ (lposfix num)) name)))
              (mv (cons proofcall proofcalls)
                  (cons of-constr-thm of-constr-thms)
                  (cons fix-id-thm fix-id-thms)))
      :other (defind-gen-proof2-irule-thm-prems
               (cdr infos) pred-name irule-name num name))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-proof2-irule-thm ((info defind-irule-infop)
                                     (pred-infos defind-pred-info-listp)
                                     (name symbolp))
  :guard (no-duplicatesp-equal (defind-pred-info-list->name pred-infos))
  :returns (event pseudo-event-formp)
  :short "Generate a @('p[l[k]]-2-rule[k]') theorem."
  :long
  (xdoc::topstring
   (xdoc::p
    "The statement is the one of @(tsee defind-gen-irule-thm),
     with @('p[i]-2') in place of @('p[i]').")
   (xdoc::p
    "Unlike @(tsee defind-gen-irule-thm),
     the proof does not go through a function that builds the proof:
     the constructor of the fixtype of proofs is that proof,
     so we use the @('p[i]-2-suff') theorem on it directly.
     Expanding the hypotheses that are calls of the @('p[i]-2') predicates
     yields the proofs of those premises,
     which the constructor takes as its subproofs.
     Then the proof validity predicate opens on the known kind,
     the accessors of the constructor yield its arguments,
     and the @('p[l[k]]-2-rule[k]-validp') function
     closes the equalities for the arguments of the conclusion.")
   (xdoc::p
    "The theorem about the return type of the constructor
     gives both the recognizer and the kind of the constructed proof.
     For a rule with premises that are calls of the predicates being defined
     we also need @(tsee defind-proof-fix-id-thm-name);
     see that function."))
  (b* (((defind-irule-info info))
       ((defind-conclusion-info cinfo) info.conclusion)
       (pred2-name (defind-pred2-name cinfo.name name))
       (concl-args (defind-term-info-list->uterm cinfo.args))
       (concl `(,pred2-name ,@concl-args))
       ((mv pred-hyps other-hyps)
        (defind-gen-proof2-irule-thm-hyps info.premises name))
       (thm-name (defind-pred-irule-thm-name pred2-name info.name name))
       (pred-suff (defind-pred-suff-thm-name pred2-name name))
       (vars (defind-irule-info-free-vars info))
       ((mv proofcalls prem-of-constr-thms fix-id-thms)
        (defind-gen-proof2-irule-thm-prems
          info.premises pred2-name info.name 1 name))
       (constr (defind-proof-constr-name pred2-name info.name name))
       (proofcall `(,constr ,@(symbol-list-fix vars) ,@proofcalls))
       (pinfo (defind-lookup-pred cinfo.name pred-infos))
       ((unless pinfo)
        (raise "Internal error: predicate ~x0 not found." cinfo.name)
        '(_))
       (formals (defind-pred-info->formals pinfo))
       (formals-inst (alist-to-doublets (pairlis$ formals concl-args)))
       (proof-var (defind-proof-var-name name))
       (proof-validp (defind-proof-valid-fn-name pred2-name name))
       (irule-validp (defind-irule-valid-fn-name pred2-name info.name name))
       (constr-return-thm
        (defind-proof-constr-return-thm pred2-name info.name name))
       (var-of-constr-thms
        (defind-proof-var-of-constr-thm-names pred2-name info.name vars name)))
    `(defruled ,thm-name
       ,(defind-gen-implication (append pred-hyps other-hyps) concl)
       ,@(and pred-hyps
              (list :expand pred-hyps))
       :use (:instance ,pred-suff
                       (,proof-var ,proofcall)
                       ,@formals-inst)
       :in-theory '(,proof-validp
                    ,irule-validp
                    ,constr-return-thm
                    ,@var-of-constr-thms
                    ,@prem-of-constr-thms
                    ,@fix-id-thms)))
  :no-function nil
  :guard-hints (("Goal" :in-theory (enable set::sets-are-true-lists
                                           symbol-listp-when-symbol-setp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-proof2-irule-thms ((irule-infos defind-irule-info-listp)
                                      (pred-infos defind-pred-info-listp)
                                      (name symbolp))
  :guard (and (no-duplicatesp-equal (defind-pred-info-list->name pred-infos))
              (no-duplicatesp-equal (defind-irule-info-list->name irule-infos)))
  :returns (events pseudo-event-form-listp)
  :short "Generate all the @('p[l[k]]-2-rule[k]') theorems."
  (cond ((endp irule-infos) nil)
        (t (cons (defind-gen-proof2-irule-thm
                   (car irule-infos) pred-infos name)
                 (defind-gen-proof2-irule-thms
                   (cdr irule-infos) pred-infos name)))))

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

(define defind-gen-proof2-irule-defsection
  ((irule-infos defind-irule-info-listp)
   (pred-infos defind-pred-info-listp)
   (name symbolp)
   (xdocp booleanp))
  :guard (and (no-duplicatesp-equal (defind-pred-info-list->name pred-infos))
              (no-duplicatesp-equal (defind-irule-info-list->name irule-infos)))
  :returns (event pseudo-event-formp)
  :short "Generate a @(tsee defsection) or @(tsee progn) with
          all the @('p[l[k]]-2-rule[k]') theorems,
          depending on whether XDOC is to be generated."
  (b* ((thms (defind-gen-proof2-irule-thms irule-infos pred-infos name)))
    (if xdocp
        `(defsection ,(defind-proof2-rule-thm-section-name name)
           :short "Theorems corresponding to the inference rules,
                   for the second representation of proofs."
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
       (body/matrix (defind-gen-implication prems concl))
       (event (if (defind-irule-groundp info)
                  `(defun ,fn-name ()
                     (declare (xargs :verify-guards nil))
                     ,body/matrix)
                `(defun-sk ,fn-name ()
                   (declare (xargs :verify-guards nil))
                   (forall ,vars ,body/matrix))))
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

(define defind-gen-prem-concl-calls ((infos defind-premise-info-listp)
                                     (pred-name symbolp)
                                     (irule-name symbolp)
                                     (num posp)
                                     (inlinep booleanp)
                                     (name symbolp))
  :returns (calls true-listp)
  :short "Generate the calls of the conclusion functions on
          the proofs of the premises of an inference rule,
          accessed from a proof rooted at the rule."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('inlinep') flag says whether to use
     the @('$inline') forms of the premise accessors.
     Those are the forms that occur in clauses,
     while the other forms are adequate for terms in hints."))
  (b* (((when (endp infos)) nil)
       (info (car infos)))
    (defind-premise-info-case
      info
      :pred (b* ((concl-fn (defind-proof-concl-fn-name info.name name))
                 (acc (if inlinep
                          (defind-proof-prem-acc$inline-name
                            pred-name irule-name num name)
                        (defind-proof-prem-acc-name
                          pred-name irule-name num name)))
                 (proof (defind-proof-var-name name))
                 (calls (defind-gen-prem-concl-calls (cdr infos)
                                                     pred-name
                                                     irule-name
                                                     (1+ (lposfix num))
                                                     inlinep
                                                     name)))
              (cons `(,concl-fn (,acc ,proof)) calls))
      :other (defind-gen-prem-concl-calls
               (cdr infos) pred-name irule-name num inlinep name))))

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
       (prem-args (defind-gen-prem-concl-calls
                    info.premises cinfo.name info.name 1 nil name))
       (wit (defind-irule-witness-fn-name cinfo.name info.name name)))
    `(,wit ,concl-arg ,@prem-args)))

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

(define defind-gen-pred-alt-when-proof-valid-thm-formula
  ((pred-name symbolp)
   (pred-formals symbol-listp)
   (prop-calls true-listp)
   (name symbolp))
  :returns (formula true-listp)
  :short "Generate the formula of a @('p[i]-alt-when-proof-validp') theorem."
  (b* ((valid-fn (defind-proof-valid-fn-name pred-name name))
       (proof (defind-proof-var-name name))
       (assert (defind-assert-type-name pred-name name))
       (concl (defind-concl-var-name name))
       (concl-fn (defind-proof-concl-fn-name pred-name name))
       (pred-alt (defind-pred-alt-fn-name pred-name name))
       (concls (defind-concl-formal-var-names pred-formals name)))
    `(implies (and ,@prop-calls
                   (,valid-fn ,proof))
              (b* (((,assert ,concl) (,concl-fn ,proof)))
                (,pred-alt ,@concls)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-pred-alt-irule-hints ((infos defind-irule-info-listp)
                                         (clique-preds symbol-setp)
                                         (first-kind symbolp)
                                         (singlep booleanp)
                                         (name symbolp))
  :guard (no-duplicatesp-equal (defind-irule-info-list->name infos))
  :returns (mv (hint-branches true-listp)
               (lemma-instances true-listp)
               (irule-valid-fns symbol-listp)
               (irule-acc-thms symbol-listp))
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
     of the necessity theorems for the various rules,
     each targeted to the inference rule that it pertains to.
     Putting them all in a single @(':use') hint makes the proofs slow,
     even with a moderate number of inference rules
     (that is what an initial implementation did).
     So we return, for each inference rule,
     a branch of a computed @(tsee cond) hint,
     used when the theorem is proved by induction,
     along with the necessity theorem instance
     and the rule validity and conclusion accessor theorems used (flattened),
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
     which is a hypothesis of the case of the rule.
     This happens only if the predicate is
     in a clique with other predicates,
     because a predicate with a single rule
     is recursive only via other predicates.")
   (xdoc::p
    "The theory of each branch includes,
     for the predicate of the conclusion
     and for the predicates of the premises,
     the theorems that relate the conclusions of proofs to assertions.")
   (xdoc::p
    "If a premise has a predicate in a preceding clique,
     i.e. not in @('clique-preds'),
     the theory of the branch also includes
     the @('p[i]-alt-when-proof-validp') theorem of that predicate,
     which has been already proved at that point:
     it plays the role that,
     for a predicate in the same clique,
     is played by the induction hypothesis."))
  (b* (((when (endp infos)) (mv nil nil nil nil))
       ((defind-irule-info info) (car infos))
       ((defind-conclusion-info cinfo) info.conclusion)
       (proof (defind-proof-var-name name))
       (proof-kind (defind-proof-kind$inline-fn-name cinfo.name name))
       (kind (defind-irule-tag info.name))
       (lastp (endp (cdr infos)))
       (irule-valid-fn (defind-irule-valid-fn-name cinfo.name info.name name))
       (concl-acc (defind-proof-concl-acc$inline-name
                    cinfo.name info.name name))
       (concl-calls (defind-gen-prem-concl-calls
                      info.premises cinfo.name info.name 1 t name))
       (literal
        (if singlep
            `(not (,irule-valid-fn (,concl-acc ,proof) ,@concl-calls))
          (if lastp
              `(equal (,proof-kind ,proof) ',(symbol-lfix first-kind))
            `(not (equal (,proof-kind ,proof) ',kind)))))
       (cond `(member-equal ',literal clause))
       (necc/def-rule
        (if (defind-irule-groundp info)
            (defind-pred-alt-irule-fn-name cinfo.name info.name name)
          (defind-pred-alt-irule-thm-name cinfo.name info.name name)))
       (vars (defind-irule-info-free-vars info))
       (witcall (defind-gen-irule-witness-call info name))
       (inst-doublets (if (= (set::cardinality vars) 1)
                          (list `(,(set::head vars) ,witcall))
                        (defind-gen-irule-mv-nth-doublets vars 0 witcall)))
       (lemma-instance `(:instance ,necc/def-rule ,@inst-doublets))
       (valid-fn (defind-proof-valid-fn-name cinfo.name name))
       (prem-preds (defind-preds-in-premises info.premises))
       (assert-thms (defind-concl-assert-thm-names
                      (set::insert cinfo.name prem-preds)
                      name))
       (alt-thms (defind-pred-alt-when-proof-valid-thm-names
                   (set::difference prem-preds (symbol-sfix clique-preds))
                   name))
       (irule-acc-thm
        (defind-proof-concl-acc-return-thm-name cinfo.name info.name name))
       (concl-fn (defind-proof-concl-fn-name cinfo.name name))
       (hint-branch
        `(,cond
          '(:use ,lemma-instance
            :expand (,concl-fn ,proof)
            :in-theory '(,valid-fn
                         ,irule-valid-fn
                         ,@assert-thms
                         ,@alt-thms
                         ,irule-acc-thm))))
       ((mv hint-branches lemma-instances irule-valid-fns irule-acc-thms)
        (defind-gen-pred-alt-irule-hints
          (cdr infos) clique-preds first-kind singlep name)))
    (mv (cons hint-branch hint-branches)
        (cons lemma-instance lemma-instances)
        (cons irule-valid-fn irule-valid-fns)
        (cons irule-acc-thm irule-acc-thms)))
  :guard-hints (("Goal" :in-theory (enable set::cardinality))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-pred-alt-when-proof-valid-thm
  ((pred-name symbolp)
   (pred-formals symbol-listp)
   (irule-infos defind-irule-info-listp)
   (prop-calls true-listp)
   (name symbolp))
  :guard (no-duplicatesp-equal (defind-irule-info-list->name irule-infos))
  :returns (event pseudo-event-formp)
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
     with a single @(':use') of the necessity theorems of all the rules,
     opening the relevant functions."))
  (b* ((recursivep (defind-pred-recursivep pred-name irule-infos))
       (thm-name (defind-pred-alt-when-proof-valid-thm-name pred-name name))
       (valid-fn (defind-proof-valid-fn-name pred-name name))
       (proof (defind-proof-var-name name))
       (concl-fn (defind-proof-concl-fn-name pred-name name))
       (formula (defind-gen-pred-alt-when-proof-valid-thm-formula
                  pred-name pred-formals prop-calls name))
       (irule-infos (defind-irules-of-pred pred-name irule-infos))
       ((unless (consp irule-infos))
        (raise "Internal error: no inference rules for predicate ~x0."
               pred-name)
        '(_))
       (first-kind
        (defind-irule-tag (defind-irule-info->name (car irule-infos))))
       (singlep (endp (cdr irule-infos)))
       (clique-preds (set::insert (symbol-lfix pred-name) nil))
       ((mv hint-branches lemma-instances irule-valid-fns irule-acc-thms)
        (defind-gen-pred-alt-irule-hints
          irule-infos clique-preds first-kind singlep name))
       ((when recursivep)
        `(defruled ,thm-name
           ,formula
           :induct t
           :in-theory '(,valid-fn
                        eql)
           :hints ((cond ,@hint-branches))))
       (poss-thm (defind-proof-kind-poss-thm-name pred-name name))
       (prem-preds (defind-preds-in-premises-of-irules irule-infos))
       (assert-thms
        (defind-concl-assert-thm-names
          (set::insert (symbol-lfix pred-name) prem-preds)
          name))
       (alt-thms
        (defind-pred-alt-when-proof-valid-thm-names
          (set::difference prem-preds clique-preds)
          name)))
    `(defruled ,thm-name
       ,formula
       :expand (,concl-fn ,proof)
       :use ,lemma-instances
       :in-theory '(,valid-fn
                    ,concl-fn
                    ,poss-thm
                    ,@assert-thms
                    ,@alt-thms
                    ,@irule-valid-fns
                    ,@irule-acc-thms)))
  :no-function nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-pred-alt-when-proof-valid-thm-clique
  ((clique-pred-infos defind-pred-info-listp)
   (irule-infos defind-irule-info-listp)
   (prop-calls true-listp)
   (name symbolp))
  :guard (and (consp clique-pred-infos)
              (no-duplicatesp-equal
               (defind-pred-info-list->name clique-pred-infos))
              (no-duplicatesp-equal
               (defind-irule-info-list->name irule-infos)))
  :returns (event pseudo-event-formp)
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
     every rule of every predicate of the clique."))
  (b* ((first-pred (defind-pred-info->name (car clique-pred-infos)))
       (macro (defind-proof-valid-fn-clique-defthm-macro-name first-pred name))
       (flag-fn (defind-proof-valid-fn-clique-flag-name first-pred name))
       (flag (defind-flag-var-name name))
       (proof (defind-proof-var-name name))
       (clique-preds
        (set::mergesort (defind-pred-info-list->name clique-pred-infos)))
       ((mv thms hint-branches valid-fns)
        (defind-gen-pred-alt-when-proof-valid-thm-clique-loop
          clique-pred-infos irule-infos clique-preds prop-calls name)))
    `(,macro
      ,@thms
      :hints (("Goal"
               :induct (,flag-fn ,flag ,proof)
               :in-theory '(,flag-fn
                            ,@valid-fns
                            eql))
              (cond ,@hint-branches))))
  :guard-hints
  (("Goal"
    :in-theory (enable true-listp-when-pseudo-event-form-listp-rewrite)))

  :prepwork
  ((define defind-gen-pred-alt-when-proof-valid-thm-clique-loop
     ((pred-infos defind-pred-info-listp)
      (irule-infos defind-irule-info-listp)
      (clique-preds symbol-setp)
      (prop-calls true-listp)
      (name symbolp))
     :guard (and (no-duplicatesp-equal
                  (defind-pred-info-list->name pred-infos))
                 (no-duplicatesp-equal
                  (defind-irule-info-list->name irule-infos)))
     :returns (mv (thms pseudo-event-form-listp)
                  (hint-branches true-listp)
                  (valid-fns symbol-listp))
     :parents nil
     (b* (((when (endp pred-infos)) (mv nil nil nil))
          ((defind-pred-info info) (car pred-infos))
          (thm-name (defind-pred-alt-when-proof-valid-thm-name info.name name))
          (valid-fn (defind-proof-valid-fn-name info.name name))
          (formula (defind-gen-pred-alt-when-proof-valid-thm-formula
                     info.name info.formals prop-calls name))
          (pred-irule-infos (defind-irules-of-pred info.name irule-infos))
          ((mv thms hint-branches valid-fns)
           (defind-gen-pred-alt-when-proof-valid-thm-clique-loop
             (cdr pred-infos) irule-infos clique-preds prop-calls name))
          ((unless (consp pred-irule-infos))
           (raise "Internal error: no inference rules for predicate ~x0."
                  info.name)
           (mv thms hint-branches valid-fns))
          (first-kind
           (defind-irule-tag (defind-irule-info->name (car pred-irule-infos))))
          (singlep (endp (cdr pred-irule-infos)))
          ((mv branches & & &)
           (defind-gen-pred-alt-irule-hints
             pred-irule-infos clique-preds first-kind singlep name))
          (thm `(defthmd ,thm-name
                  ,formula
                  :flag ,valid-fn)))
       (mv (cons thm thms)
           (append branches hint-branches)
           (cons valid-fn valid-fns)))
     :no-function nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-pred-alt-when-proof-valid-thms
  ((pred-infos defind-pred-info-listp)
   (irule-infos defind-irule-info-listp)
   (leveled-cliques symbol-set-list-listp)
   (prop-calls true-listp)
   (name symbolp))
  :guard (and (no-duplicatesp-equal (defind-pred-info-list->name pred-infos))
              (no-duplicatesp-equal (defind-irule-info-list->name irule-infos)))
  :returns (events pseudo-event-form-listp)
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
    leveled-cliques pred-infos irule-infos prop-calls name)

  :prepwork

  ((define defind-gen-pred-alt-when-proof-valid-thms-loop
     ((leveled-cliques symbol-set-list-listp)
      (pred-infos defind-pred-info-listp)
      (irule-infos defind-irule-info-listp)
      (prop-calls true-listp)
      (name symbolp))
     :guard (and (no-duplicatesp-equal
                  (defind-pred-info-list->name pred-infos))
                 (no-duplicatesp-equal
                  (defind-irule-info-list->name irule-infos)))
     :returns (events pseudo-event-form-listp)
     :parents nil
     (b* (((when (endp leveled-cliques)) nil)
          (levels (symbol-set-list-fix (car leveled-cliques)))
          (clique-preds (set::set-list-union levels))
          (clique-pred-infos (defind-lookup-pred-set clique-preds pred-infos))
          (events (defind-gen-pred-alt-when-proof-valid-thms-loop
                    (cdr leveled-cliques)
                    pred-infos irule-infos prop-calls name))
          ((unless (consp clique-pred-infos))
           (raise "Internal error: no predicates in clique with levels ~x0."
                  levels)
           events)
          (event
           (if (endp (cdr clique-pred-infos))
               (b* (((defind-pred-info info) (car clique-pred-infos)))
                 (defind-gen-pred-alt-when-proof-valid-thm
                   info.name info.formals irule-infos prop-calls name))
             (defind-gen-pred-alt-when-proof-valid-thm-clique
               clique-pred-infos irule-infos prop-calls name))))
       (cons event events))
     :no-function nil
     :guard-hints
     (("Goal" :in-theory (enable set-listp-when-symbol-set-listp))))))

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
                                          (leveled-cliques
                                           symbol-set-list-listp)
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
                     pred-infos irule-infos leveled-cliques prop-calls name))
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

(define defind-gen-proof2-pred-alt-stubs ((infos defind-pred-info-listp)
                                          (name symbolp))
  :guard (no-duplicatesp-equal (defind-pred-info-list->name infos))
  :returns (events pseudo-event-form-listp)
  :short "Generate the @('p[i]-2-alt') stubs."
  (b* (((when (endp infos)) nil)
       ((defind-pred-info info) (car infos))
       (fn-name (defind-pred-alt-fn-name
                  (defind-pred2-name info.name name) name))
       (stub `(defstub ,fn-name ,(repeat (len info.formals) '*) => *))
       (stubs (defind-gen-proof2-pred-alt-stubs (cdr infos) name)))
    (cons stub stubs)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-proof2-pred-alt-irule-prop-prems
  ((infos defind-premise-info-listp)
   (name symbolp))
  :returns (prems true-listp)
  :short "Premises of the proposition (nullary function) saying that
          a @('p[i]-2-alt') stub satisfies an inference rule."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is like @(tsee defind-gen-pred-alt-irule-prop-prems),
     with the @('p[i]-2-alt') stubs in place of the @('p[i]-alt') ones."))
  (b* (((when (endp infos)) nil)
       (prems (defind-gen-proof2-pred-alt-irule-prop-prems (cdr infos) name))
       (info (car infos)))
    (defind-premise-info-case
      info
      :pred (cons `(,(defind-pred-alt-fn-name
                       (defind-pred2-name info.name name) name)
                    ,@(defind-term-info-list->uterm info.args))
                  prems)
      :other (cons (defind-term-info->uterm info.term)
                   prems))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-proof2-pred-alt-irule-prop ((info defind-irule-infop)
                                               (name symbolp))
  :returns (mv (event pseudo-event-formp)
               call)
  :short "Proposition (nullary function) saying that
          a @('p[i]-2-alt') stub satisfies an inference rule."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is like @(tsee defind-gen-pred-alt-irule-prop);
     in particular, a ground rule yields a @(tsee defun)
     instead of a @(tsee defun-sk),
     since there is nothing to quantify."))
  (b* (((defind-irule-info info))
       ((defind-conclusion-info cinfo) info.conclusion)
       (pred2-name (defind-pred2-name cinfo.name name))
       (fn-name (defind-pred-alt-irule-fn-name pred2-name info.name name))
       (prems (defind-gen-proof2-pred-alt-irule-prop-prems info.premises name))
       (concl `(,(defind-pred-alt-fn-name pred2-name name)
                ,@(defind-term-info-list->uterm cinfo.args)))
       (vars (defind-irule-info-free-vars info))
       (body/matrix (defind-gen-implication prems concl))
       (event (if (defind-irule-groundp info)
                  `(defun ,fn-name ()
                     (declare (xargs :verify-guards nil))
                     ,body/matrix)
                `(defun-sk ,fn-name ()
                   (declare (xargs :verify-guards nil))
                   (forall ,vars ,body/matrix))))
       (call `(,fn-name)))
    (mv event call)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-proof2-pred-alt-irule-props
  ((infos defind-irule-info-listp)
   (name symbolp))
  :guard (no-duplicatesp-equal (defind-irule-info-list->name infos))
  :returns (mv (events pseudo-event-form-listp)
               (calls true-listp))
  :short "Propositions (nullary functions) saying that
          the @('p[i]-2-alt') stubs satisfy the inference rules."
  (b* (((when (endp infos)) (mv nil nil))
       ((mv event call)
        (defind-gen-proof2-pred-alt-irule-prop (car infos) name))
       ((mv events calls)
        (defind-gen-proof2-pred-alt-irule-props (cdr infos) name)))
    (mv (cons event events) (cons call calls))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-proof2-var-acc$inline-calls ((vars symbol-listp)
                                                (pred-name symbolp)
                                                (irule-name symbolp)
                                                (name symbolp))
  :returns (calls true-listp)
  :short "Calls of the accessors of the fields of a @('p[i]-2-proof') summand
          named after the variables of a rule."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the @('$inline') forms of the accessors,
     which are the ones that occur in clauses;
     they are used to recognize the case of a rule
     when the proof fixtype has a single summand
     (see @(tsee defind-gen-proof2-pred-alt-irule-hints))."))
  (b* (((when (endp vars)) nil)
       (var (symbol-lfix (car vars)))
       (acc (defind-proof-var-acc$inline-name pred-name irule-name var name))
       (proof (defind-proof-var-name name)))
    (cons `(,acc ,proof)
          (defind-gen-proof2-var-acc$inline-calls
            (cdr vars) pred-name irule-name name))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-proof2-alt-inst-doublets ((vars symbol-listp)
                                             (pred-name symbolp)
                                             (irule-name symbolp)
                                             (name symbolp))
  :returns (doublets true-list-listp)
  :short "Bindings of the variables of a rule
          in the instance of the proposition for that rule,
          in a @('p[i]-2-alt-when-proof-validp') theorem."
  :long
  (xdoc::topstring
   (xdoc::p
    "Each variable of the rule is bound to
     the field of the proof named after it.
     This is where the second representation of proofs pays off
     in this theorem: the variables of the rule are fields of the proof,
     so these are plain accessor calls,
     while @(tsee defind-gen-pred-alt-when-proof-valid-thm) must extract them
     from the witness of the validity of the rule
     (see @(tsee defind-gen-irule-mv-nth-doublets))."))
  (b* (((when (endp vars)) nil)
       (var (symbol-lfix (car vars)))
       (acc (defind-proof-var-acc-name pred-name irule-name var name))
       (proof (defind-proof-var-name name))
       (doublet `(,var (,acc ,proof))))
    (cons doublet
          (defind-gen-proof2-alt-inst-doublets
            (cdr vars) pred-name irule-name name))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-proof2-pred-alt-when-proof-valid-thm-formula
  ((pred-name symbolp)
   (pred-formals symbol-listp)
   (prop-calls true-listp)
   (name symbolp))
  :returns (formula true-listp)
  :short "Formula of a @('p[i]-2-alt-when-proof-validp') theorem."
  :long
  (xdoc::topstring
   (xdoc::p
    "The conclusion is the @('p[i]-2-alt') stub
     on the arguments of the conclusion,
     which are arguments of the proof validity predicate,
     rather than fields of the proof to be extracted;
     so, unlike @(tsee defind-gen-pred-alt-when-proof-valid-thm-formula),
     there is nothing to destructure."))
  (b* ((pred2-name (defind-pred2-name pred-name name))
       (valid-fn (defind-proof-valid-fn-name pred2-name name))
       (proof (defind-proof-var-name name))
       (pred-alt (defind-pred-alt-fn-name pred2-name name))
       (concls (defind-proof2-concl-var-names pred-formals name)))
    `(implies (and ,@prop-calls
                   (,valid-fn ,proof ,@concls))
              (,pred-alt ,@concls))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-proof2-pred-alt-irule-hints ((infos defind-irule-info-listp)
                                                (pred-formals symbol-listp)
                                                (clique-preds symbol-setp)
                                                (first-kind symbolp)
                                                (singlep booleanp)
                                                (name symbolp))
  :guard (no-duplicatesp-equal (defind-irule-info-list->name infos))
  :returns (mv (hint-branches true-listp)
               (lemma-instances true-listp)
               (irule-valid-fns symbol-listp))
  :short "Generate the hints for the inference rules of a predicate,
          to prove the @('p[i]-2-alt-when-proof-validp') theorem
          of that predicate."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is like @(tsee defind-gen-pred-alt-irule-hints);
     see that function for the shape of the computed conditions,
     including the treatment of the last branch,
     and for the theorems of the predicates of the premises
     in preceding cliques.
     Using a single @(':use') hint with all the instances instead
     is much slower, as noted there:
     with eight rules we measured about sixty times as many prover steps.")
   (xdoc::p
    "The conclusion of the theorem is
     the @('p[i]-2-alt') stub on the arguments of the conclusion,
     which are arguments of the proof validity predicate,
     rather than fields of the proof to be extracted;
     so, unlike @(tsee defind-gen-pred-alt-irule-hints),
     there is nothing to destructure,
     and each branch needs just the proof validity predicate,
     the one for the rule,
     and the theorems of the predicates of the premises
     in preceding cliques.")
   (xdoc::p
    "In the @('singlep') case the condition takes the same form as in
     @(tsee defind-gen-pred-alt-irule-hints),
     but with the arguments of the conclusion and
     the fields of the proof named after the variables of the rule
     in place of the conclusion of the proof and of those of the premises.
     The accessors are the @('$inline') ones because
     those are the ones that occur in the clause."))
  (b* (((when (endp infos)) (mv nil nil nil))
       ((defind-irule-info info) (car infos))
       ((defind-conclusion-info cinfo) info.conclusion)
       (pred2-name (defind-pred2-name cinfo.name name))
       (proof (defind-proof-var-name name))
       (proof-kind (defind-proof-kind$inline-fn-name pred2-name name))
       (kind (defind-irule-tag info.name))
       (lastp (endp (cdr infos)))
       (vars (defind-irule-info-free-vars info))
       (irule-valid-fn (defind-irule-valid-fn-name pred2-name info.name name))
       (literal
        (if singlep
            `(not (,irule-valid-fn
                   ,@(defind-proof2-concl-var-names pred-formals name)
                   ,@(defind-gen-proof2-var-acc$inline-calls
                       vars pred2-name info.name name)))
          (if lastp
              `(equal (,proof-kind ,proof) ',(symbol-lfix first-kind))
            `(not (equal (,proof-kind ,proof) ',kind)))))
       (cond `(member-equal ',literal clause))
       (necc/def-rule
        (if (defind-irule-groundp info)
            (defind-pred-alt-irule-fn-name pred2-name info.name name)
          (defind-pred-alt-irule-thm-name pred2-name info.name name)))
       (inst-doublets
        (defind-gen-proof2-alt-inst-doublets
          vars pred2-name info.name name))
       (lemma-instance `(:instance ,necc/def-rule ,@inst-doublets))
       (valid-fn (defind-proof-valid-fn-name pred2-name name))
       (prem-preds (defind-preds-in-premises info.premises))
       (alt-thms (defind-proof2-pred-alt-when-proof-valid-thm-names
                   (set::difference prem-preds (symbol-sfix clique-preds))
                   name))
       (hint-branch
        `(,cond
          '(:use ,lemma-instance
            :in-theory '(,valid-fn
                         ,irule-valid-fn
                         ,@alt-thms))))
       ((mv hint-branches lemma-instances irule-valid-fns)
        (defind-gen-proof2-pred-alt-irule-hints
          (cdr infos) pred-formals clique-preds first-kind singlep name)))
    (mv (cons hint-branch hint-branches)
        (cons lemma-instance lemma-instances)
        (cons irule-valid-fn irule-valid-fns)))
  :guard-hints (("Goal" :in-theory (enable symbol-listp-when-symbol-setp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-proof2-pred-alt-when-proof-valid-thm
  ((pred-name symbolp)
   (pred-formals symbol-listp)
   (irule-infos defind-irule-info-listp)
   (prop-calls true-listp)
   (name symbolp))
  :guard (no-duplicatesp-equal (defind-irule-info-list->name irule-infos))
  :returns (event pseudo-event-formp)
  :short "Generate a @('p[i]-2-alt-when-proof-validp') theorem,
          for a predicate that forms a singleton clique."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is like @(tsee defind-gen-pred-alt-when-proof-valid-thm);
     see that function for the treatment of non-recursive predicates."))
  (b* ((recursivep (defind-pred-recursivep pred-name irule-infos))
       (pred2-name (defind-pred2-name pred-name name))
       (thm-name (defind-pred-alt-when-proof-valid-thm-name pred2-name name))
       (valid-fn (defind-proof-valid-fn-name pred2-name name))
       (formula (defind-gen-proof2-pred-alt-when-proof-valid-thm-formula
                  pred-name pred-formals prop-calls name))
       (irule-infos (defind-irules-of-pred pred-name irule-infos))
       ((unless (consp irule-infos))
        (raise "Internal error: no inference rules for predicate ~x0."
               pred-name)
        '(_))
       (first-kind
        (defind-irule-tag (defind-irule-info->name (car irule-infos))))
       (singlep (endp (cdr irule-infos)))
       (clique-preds (set::insert (symbol-lfix pred-name) nil))
       ((mv hint-branches lemma-instances irule-valid-fns)
        (defind-gen-proof2-pred-alt-irule-hints
          irule-infos pred-formals clique-preds first-kind singlep name))
       ((when recursivep)
        `(defruled ,thm-name
           ,formula
           :induct t
           :in-theory '(,valid-fn
                        eql)
           :hints ((cond ,@hint-branches))))
       (poss-thm (defind-proof-kind-poss-thm-name pred2-name name))
       (prem-preds (defind-preds-in-premises-of-irules irule-infos))
       (alt-thms (defind-proof2-pred-alt-when-proof-valid-thm-names
                   (set::difference prem-preds clique-preds)
                   name)))
    `(defruled ,thm-name
       ,formula
       :use ,lemma-instances
       :in-theory '(,valid-fn
                    ,poss-thm
                    ,@irule-valid-fns
                    ,@alt-thms)))
  :no-function nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-proof2-pred-alt-when-proof-valid-thm-clique
  ((clique-pred-infos defind-pred-info-listp)
   (irule-infos defind-irule-info-listp)
   (prop-calls true-listp)
   (name symbolp))
  :guard (and (consp clique-pred-infos)
              (no-duplicatesp-equal
               (defind-pred-info-list->name clique-pred-infos))
              (no-duplicatesp-equal
               (defind-irule-info-list->name irule-infos)))
  :returns (event pseudo-event-formp)
  :short "Generate the @('p[i]-2-alt-when-proof-validp') theorems of
          a clique of multiple predicates."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is like @(tsee defind-gen-pred-alt-when-proof-valid-thm-clique),
     except that we do not supply the induction hint.
     The proof validity functions of a clique
     do not all have the same formals here,
     since each one takes the arguments of the conclusion of its predicate,
     so the flag function takes the ones of all of them;
     the macro generated by the flag machinery
     supplies the call of the flag function on its formals,
     which is what we want,
     so we leave that to it."))
  (b* ((first-pred2 (defind-pred2-name
                      (defind-pred-info->name (car clique-pred-infos))
                      name))
       (macro (defind-proof-valid-fn-clique-defthm-macro-name first-pred2 name))
       (flag-fn (defind-proof-valid-fn-clique-flag-name first-pred2 name))
       (clique-preds
        (set::mergesort (defind-pred-info-list->name clique-pred-infos)))
       ((mv thms hint-branches valid-fns)
        (defind-gen-proof2-pred-alt-when-proof-valid-thm-clique-loop
          clique-pred-infos irule-infos clique-preds prop-calls name)))
    `(,macro
      ,@thms
      :hints (("Goal"
               :in-theory '(,flag-fn
                            ,@valid-fns
                            eql))
              (cond ,@hint-branches))))
  :guard-hints
  (("Goal"
    :in-theory (enable true-listp-when-pseudo-event-form-listp-rewrite)))

  :prepwork
  ((define defind-gen-proof2-pred-alt-when-proof-valid-thm-clique-loop
     ((pred-infos defind-pred-info-listp)
      (irule-infos defind-irule-info-listp)
      (clique-preds symbol-setp)
      (prop-calls true-listp)
      (name symbolp))
     :guard (and (no-duplicatesp-equal
                  (defind-pred-info-list->name pred-infos))
                 (no-duplicatesp-equal
                  (defind-irule-info-list->name irule-infos)))
     :returns (mv (thms pseudo-event-form-listp)
                  (hint-branches true-listp)
                  (valid-fns symbol-listp))
     :parents nil
     (b* (((when (endp pred-infos)) (mv nil nil nil))
          ((defind-pred-info info) (car pred-infos))
          (pred2-name (defind-pred2-name info.name name))
          (thm-name (defind-pred-alt-when-proof-valid-thm-name pred2-name name))
          (valid-fn (defind-proof-valid-fn-name pred2-name name))
          (formula (defind-gen-proof2-pred-alt-when-proof-valid-thm-formula
                     info.name info.formals prop-calls name))
          (pred-irule-infos (defind-irules-of-pred info.name irule-infos))
          ((mv thms hint-branches valid-fns)
           (defind-gen-proof2-pred-alt-when-proof-valid-thm-clique-loop
             (cdr pred-infos) irule-infos clique-preds prop-calls name))
          ((unless (consp pred-irule-infos))
           (raise "Internal error: no inference rules for predicate ~x0."
                  info.name)
           (mv thms hint-branches valid-fns))
          (first-kind
           (defind-irule-tag (defind-irule-info->name (car pred-irule-infos))))
          (singlep (endp (cdr pred-irule-infos)))
          ((mv branches & &)
           (defind-gen-proof2-pred-alt-irule-hints
             pred-irule-infos info.formals clique-preds
             first-kind singlep name))
          (thm `(defthmd ,thm-name
                  ,formula
                  :flag ,valid-fn)))
       (mv (cons thm thms)
           (append branches hint-branches)
           (cons valid-fn valid-fns)))
     :no-function nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-proof2-pred-alt-when-proof-valid-thms
  ((pred-infos defind-pred-info-listp)
   (irule-infos defind-irule-info-listp)
   (leveled-cliques symbol-set-list-listp)
   (prop-calls true-listp)
   (name symbolp))
  :guard (and (no-duplicatesp-equal (defind-pred-info-list->name pred-infos))
              (no-duplicatesp-equal (defind-irule-info-list->name irule-infos)))
  :returns (events pseudo-event-form-listp)
  :short "Generate all the @('p[i]-2-alt-when-proof-validp') theorems."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is like @(tsee defind-gen-pred-alt-when-proof-valid-thms):
     one event per clique, in dependency order."))
  (defind-gen-proof2-pred-alt-when-proof-valid-thms-loop
    leveled-cliques pred-infos irule-infos prop-calls name)

  :prepwork

  ((define defind-gen-proof2-pred-alt-when-proof-valid-thms-loop
     ((leveled-cliques symbol-set-list-listp)
      (pred-infos defind-pred-info-listp)
      (irule-infos defind-irule-info-listp)
      (prop-calls true-listp)
      (name symbolp))
     :guard (and (no-duplicatesp-equal
                  (defind-pred-info-list->name pred-infos))
                 (no-duplicatesp-equal
                  (defind-irule-info-list->name irule-infos)))
     :returns (events pseudo-event-form-listp)
     :parents nil
     (b* (((when (endp leveled-cliques)) nil)
          (levels (symbol-set-list-fix (car leveled-cliques)))
          (clique-preds (set::set-list-union levels))
          (clique-pred-infos (defind-lookup-pred-set clique-preds pred-infos))
          (events (defind-gen-proof2-pred-alt-when-proof-valid-thms-loop
                    (cdr leveled-cliques)
                    pred-infos irule-infos prop-calls name))
          ((unless (consp clique-pred-infos))
           (raise "Internal error: no predicates in clique with levels ~x0."
                  levels)
           events)
          (event
           (if (endp (cdr clique-pred-infos))
               (b* (((defind-pred-info info) (car clique-pred-infos)))
                 (defind-gen-proof2-pred-alt-when-proof-valid-thm
                   info.name info.formals irule-infos prop-calls name))
             (defind-gen-proof2-pred-alt-when-proof-valid-thm-clique
               clique-pred-infos irule-infos prop-calls name))))
       (cons event events))
     :no-function nil
     :guard-hints
     (("Goal" :in-theory (enable set-listp-when-symbol-set-listp))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-proof2-pred-alt-when-pred-thm ((pred-name symbolp)
                                                  (pred-formals symbol-listp)
                                                  (prop-calls true-listp)
                                                  (name symbolp))
  :returns (event pseudo-event-formp)
  :short "Generate a @('p[i]-2-alt-when-p[i]-2') theorem."
  (b* ((pred2-name (defind-pred2-name pred-name name))
       (thm-name (defind-pred-alt-when-pred-thm-name pred2-name name))
       (pred-alt (defind-pred-alt-fn-name pred2-name name))
       (valid-thm (defind-pred-alt-when-proof-valid-thm-name pred2-name name))
       (proof-var (defind-proof-var-name name))
       (proof-wit (defind-proof-witness-fn-name pred2-name name))
       (formals (symbol-list-fix pred-formals))
       (concls (defind-proof2-concl-var-names pred-formals name))
       (concls-inst (alist-to-doublets (pairlis$ concls formals))))
    `(defruled ,thm-name
       (implies (and ,@prop-calls
                     (,pred2-name ,@formals))
                (,pred-alt ,@formals))
       :in-theory '(,pred2-name)
       :use (:instance ,valid-thm
                       (,proof-var (,proof-wit ,@formals))
                       ,@concls-inst))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-proof2-pred-alt-when-pred-thms
  ((pred-infos defind-pred-info-listp)
   (prop-calls true-listp)
   (name symbolp))
  :guard (no-duplicatesp-equal (defind-pred-info-list->name pred-infos))
  :returns (events pseudo-event-form-listp)
  :short "Generate all the @('p[i]-2-alt-when-p[i]-2') theorems."
  (b* (((when (endp pred-infos)) nil)
       ((defind-pred-info info) (car pred-infos))
       (thm (defind-gen-proof2-pred-alt-when-pred-thm
              info.name info.formals prop-calls name))
       (thms (defind-gen-proof2-pred-alt-when-pred-thms
               (cdr pred-infos) prop-calls name)))
    (cons thm thms)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-proof2-minimality-defsection
  ((pred-infos defind-pred-info-listp)
   (irule-infos defind-irule-info-listp)
   (leveled-cliques symbol-set-list-listp)
   (name symbolp)
   (xdocp booleanp))
  :guard (and (no-duplicatesp-equal (defind-pred-info-list->name pred-infos))
              (no-duplicatesp-equal (defind-irule-info-list->name irule-infos)))
  :returns (event pseudo-event-formp)
  :short "Generate a @(tsee defsection) or @(tsee progn) with
          all the @('p[i]-2-alt') stubs,
          all the @('p[l[k]]-2-alt-rule[k]-p') propositions,
          all the @('p[i]-2-alt-when-proof-validp') theorems,
          and all the @('p[i]-2-alt-when-p[i]-2') theorems."
  (b* ((stubs (defind-gen-proof2-pred-alt-stubs pred-infos name))
       ((mv props prop-calls)
        (defind-gen-proof2-pred-alt-irule-props irule-infos name))
       (valid-thms (defind-gen-proof2-pred-alt-when-proof-valid-thms
                     pred-infos irule-infos leveled-cliques prop-calls name))
       (min-thms (defind-gen-proof2-pred-alt-when-pred-thms
                   pred-infos prop-calls name))
       (events (append stubs props valid-thms min-thms)))
    (if xdocp
        `(defsection ,(defind-proof2-minimality-section-name name)
           :short "Minimality of the predicates,
                   for the second representation of proofs."
           ,@events)
      `(progn ,@events)))
  :guard-hints
  (("Goal"
    :in-theory (enable true-listp-when-pseudo-event-form-listp-rewrite))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-proof2-same-alt-subst ((pred-names symbol-listp)
                                          (pred2p booleanp)
                                          (name symbolp))
  :returns (subst true-listp)
  :short "Substitutions for the stubs of the predicates,
          in a theorem that relates the two representations of proofs."
  :long
  (xdoc::topstring
   (xdoc::p
    "The minimality theorem of one representation mentions the stubs of
     all the predicates being defined, via the propositions for the rules,
     so all of them must be replaced with
     the predicates of the other representation;
     the propositions are then discharged by the rule theorems of the latter.
     See @(tsee defind-gen-proof2-same-thm)."))
  (b* (((when (endp pred-names)) nil)
       (pred-name (symbol-lfix (car pred-names)))
       (pred2-name (defind-pred2-name pred-name name))
       (alt-fn (defind-pred-alt-fn-name
                 (if pred2p pred2-name pred-name) name))
       (to (if pred2p pred-name pred2-name)))
    (cons `(,alt-fn ,to)
          (defind-gen-proof2-same-alt-subst (cdr pred-names) pred2p name))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-proof2-same-subst ((infos defind-irule-info-listp)
                                      (pred2p booleanp)
                                      (name symbolp))
  :guard (no-duplicatesp-equal (defind-irule-info-list->name infos))
  :returns (mv (subst true-listp)
               (irule-thms symbol-listp))
  :short "Substitutions for the propositions of the rules,
          in a theorem that relates the two representations of proofs,
          along with the rule theorems that discharge them."
  :long
  (xdoc::topstring
   (xdoc::p
    "The minimality theorem of one representation is used
     with the predicate of the other in place of the stub;
     see @(tsee defind-gen-proof2-same-thm).
     Each proposition saying that the stub satisfies a rule
     is replaced by @('t'),
     which leaves, as proof obligation, that the other predicate
     satisfies that rule: this is its rule theorem.")
   (xdoc::p
    "A proposition for a non-ground rule is a @(tsee defun-sk),
     so its witness must be replaced as well;
     any value of the right shape will do,
     which is a single one for a rule with one variable
     and an @(tsee mv) of the right length otherwise.
     A proposition for a ground rule is a @(tsee defun),
     which has no witness.")
   (xdoc::p
    "The @('pred2p') input says which of the two representations
     the propositions belong to:
     the ones of the first when it is @('nil'),
     the ones of the second when it is @('t').
     The rule theorems returned are the ones of the other representation."))
  (b* (((when (endp infos)) (mv nil nil))
       ((defind-irule-info info) (car infos))
       ((defind-conclusion-info cinfo) info.conclusion)
       (pred2-name (defind-pred2-name cinfo.name name))
       (prop-pred (if pred2p pred2-name cinfo.name))
       (thm-pred (if pred2p cinfo.name pred2-name))
       (prop (defind-pred-alt-irule-fn-name prop-pred info.name name))
       (irule-thm (defind-pred-irule-thm-name thm-pred info.name name))
       (vars (defind-irule-info-free-vars info))
       (nvars (set::cardinality vars))
       (prop-subst `(,prop (lambda () t)))
       (witness-subst
        (and (not (defind-irule-groundp info))
             (b* ((witness (defind-pred-alt-irule-witness-fn-name
                             prop-pred info.name name))
                  (value (if (= nvars 1)
                             nil
                           `(mv ,@(repeat nvars nil)))))
               (list `(,witness (lambda () ,value))))))
       ((mv subst irule-thms)
        (defind-gen-proof2-same-subst (cdr infos) pred2p name)))
    (mv (cons prop-subst (append witness-subst subst))
        (cons irule-thm irule-thms)))
  :guard-hints (("Goal" :in-theory (enable set::cardinality))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-proof2-same-thm ((pred-name symbolp)
                                    (pred-formals symbol-listp)
                                    (pred-names symbol-listp)
                                    (irule-infos defind-irule-info-listp)
                                    (pred2p booleanp)
                                    (name symbolp))
  :guard (no-duplicatesp-equal (defind-irule-info-list->name irule-infos))
  :returns (event pseudo-event-formp)
  :short "Generate a @('p[i]-2-when-p[i]') or @('p[i]-when-p[i]-2') theorem."
  :long
  (xdoc::topstring
   (xdoc::p
    "Each of these two theorems is one inclusion between
     the predicate of one representation and the one of the other.
     It follows from the minimality theorem of the first of the two:
     the predicate of the second satisfies the rules,
     by its rule theorems,
     and so it is no smaller than the predicate of the first.")
   (xdoc::p
    "The functional instantiation replaces the stubs of
     all the predicates being defined, not just the one of this theorem;
     see @(tsee defind-gen-proof2-same-alt-subst).")
   (xdoc::p
    "The @('pred2p') input says which of the two inclusions to generate:
     @('p[i]-2-when-p[i]') when it is @('nil'),
     since that one uses the minimality theorem of @('p[i]');
     @('p[i]-when-p[i]-2') when it is @('t')."))
  (b* ((pred2-name (defind-pred2-name pred-name name))
       (formals (symbol-list-fix pred-formals))
       (from (if pred2p pred2-name (symbol-lfix pred-name)))
       (to (if pred2p (symbol-lfix pred-name) pred2-name))
       (thm-name (if pred2p
                     (defind-pred-when-pred2-thm-name pred-name name)
                   (defind-pred2-when-pred-thm-name pred-name name)))
       (min-thm (defind-pred-alt-when-pred-thm-name
                  (if pred2p pred2-name (symbol-lfix pred-name)) name))
       (alt-subst (defind-gen-proof2-same-alt-subst pred-names pred2p name))
       ((mv subst irule-thms)
        (defind-gen-proof2-same-subst irule-infos pred2p name)))
    `(defruled ,thm-name
       (implies (,from ,@formals)
                (,to ,@formals))
       :use ((:functional-instance ,min-thm
                                   ,@alt-subst
                                   ,@subst))
       :in-theory '(,@irule-thms))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-proof2-is-pred-thm ((pred-name symbolp)
                                       (pred-formals symbol-listp)
                                       (name symbolp))
  :returns (event pseudo-event-formp)
  :short "Generate a @('p[i]-2-is-p[i]') theorem."
  :long
  (xdoc::topstring
   (xdoc::p
    "This says that the two representations of proofs
     define the same predicate.
     It follows from the two inclusions,
     since both predicates are booleans."))
  (b* ((pred2-name (defind-pred2-name pred-name name))
       (formals (symbol-list-fix pred-formals))
       (thm-name (defind-pred2-is-pred-thm-name pred-name name))
       (thm1 (defind-pred2-when-pred-thm-name pred-name name))
       (thm2 (defind-pred-when-pred2-thm-name pred-name name))
       (return-thm (defind-pred-return-thm-name pred-name name))
       (return-thm2 (defind-pred-return-thm-name pred2-name name)))
    `(defruled ,thm-name
       (equal (,pred2-name ,@formals)
              (,(symbol-lfix pred-name) ,@formals))
       :use (,thm1
             ,thm2
             (:instance ,return-thm)
             (:instance ,return-thm2))
       :in-theory '(booleanp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-proof2-same-defsection
  ((pred-infos defind-pred-info-listp)
   (irule-infos defind-irule-info-listp)
   (name symbolp)
   (xdocp booleanp))
  :guard (and (no-duplicatesp-equal (defind-pred-info-list->name pred-infos))
              (no-duplicatesp-equal (defind-irule-info-list->name irule-infos)))
  :returns (event pseudo-event-formp)
  :short "Generate a @(tsee defsection) or @(tsee progn) with
          all the theorems that relate the two representations of proofs."
  (b* ((pred-names (defind-pred-info-list->name pred-infos))
       (events (defind-gen-proof2-same-thms
                 pred-infos pred-names irule-infos name)))
    (if xdocp
        `(defsection ,(defind-proof2-equivalence-section-name name)
           :short "Sameness of the predicates of
                   the two representations of proofs."
           ,@events)
      `(progn ,@events)))
  :guard-hints
  (("Goal"
    :in-theory (enable true-listp-when-pseudo-event-form-listp-rewrite)))

  :prepwork
  ((define defind-gen-proof2-same-thms
     ((pred-infos defind-pred-info-listp)
      (pred-names symbol-listp)
      (irule-infos defind-irule-info-listp)
      (name symbolp))
     :guard (and (no-duplicatesp-equal
                  (defind-pred-info-list->name pred-infos))
                 (no-duplicatesp-equal
                  (defind-irule-info-list->name irule-infos)))
     :returns (events pseudo-event-form-listp)
     :parents nil
     (b* (((when (endp pred-infos)) nil)
          ((defind-pred-info info) (car pred-infos))
          (events (defind-gen-proof2-same-thms
                    (cdr pred-infos) pred-names irule-infos name))
          (thm1 (defind-gen-proof2-same-thm
                  info.name info.formals pred-names irule-infos nil name))
          (thm2 (defind-gen-proof2-same-thm
                  info.name info.formals pred-names irule-infos t name))
          (thm3 (defind-gen-proof2-is-pred-thm
                  info.name info.formals name)))
       (list* thm1 thm2 thm3 events)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defind-gen-events ((name symbolp)
                           (pred-infos defind-pred-info-listp)
                           (irule-infos defind-irule-info-listp)
                           (leveled-cliques symbol-set-list-listp)
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
        (defind-gen-proof-fixtypes pred-infos irule-infos
          leveled-cliques name xdocp))
       (proof2-type-events
        (defind-gen-proof2-fixtypes pred-infos irule-infos
          leveled-cliques name xdocp))
       (proof-concl-events
        (defind-gen-proof-concl-fns pred-infos irule-infos name xdocp))
       (irule-valid-events
        (defind-gen-irule-valid-fns irule-infos name xdocp))
       (proof2-irule-valid-events
        (defind-gen-proof2-irule-valid-fns irule-infos pred-infos name xdocp))
       (proof-valid-events
        (defind-gen-proof-valid-fns
          pred-infos irule-infos leveled-cliques name xdocp))
       (proof2-valid-events
        (defind-gen-proof2-valid-fns
          pred-infos irule-infos leveled-cliques name xdocp))
       (pred-events
        (defind-gen-preds pred-infos name xdocp))
       (proof2-pred-events
        (defind-gen-proof2-preds pred-infos leveled-cliques name xdocp))
       (proof-for-rule-events
        (defind-gen-irule-proof-fns irule-infos pred-infos name xdocp))
       (irules-event
        (defind-gen-irule-defsection irule-infos pred-infos name xdocp))
       (proof2-irules-event
        (defind-gen-proof2-irule-defsection
          irule-infos pred-infos name xdocp))
       (minimality-event
        (defind-gen-minimality-defsection
          pred-infos irule-infos leveled-cliques name xdocp))
       (proof2-minimality-event
        (defind-gen-proof2-minimality-defsection
          pred-infos irule-infos leveled-cliques name xdocp))
       (proof2-same-event
        (defind-gen-proof2-same-defsection
          pred-infos irule-infos name xdocp))
       (all-events (append (list name-doc-event)
                           assert-type-events
                           proof-type-events
                           proof2-type-events
                           proof-concl-events
                           irule-valid-events
                           proof2-irule-valid-events
                           proof-valid-events
                           proof2-valid-events
                           pred-events
                           proof2-pred-events
                           proof-for-rule-events
                           (list irules-event)
                           (list proof2-irules-event)
                           (list minimality-event)
                           (list proof2-minimality-event)
                           (list proof2-same-event))))
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
  :returns (mv erp (event pseudo-event-formp) state)
  :parents (definductive-implementation)
  :short "Process the inputs and generate all the events."
  (b* (((reterr) '(_) state)
       ((erp name pred-infos irule-infos leveled-cliques
             parents short long xdocp state)
        (defind-process-inputs
          name
          preds preds-suppliedp
          irules irules-suppliedp
          parents parents-suppliedp
          short short-suppliedp
          long long-suppliedp
          state))
       (event (defind-gen-events
                name pred-infos irule-infos leveled-cliques
                parents short long xdocp)))
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
