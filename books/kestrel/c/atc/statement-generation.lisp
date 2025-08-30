; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2025 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "expression-generation")
(include-book "object-tables")

(include-book "std/system/close-lambdas" :dir :system)
(include-book "std/system/make-mv-let-call" :dir :system)
(include-book "kestrel/utilities/make-cons-nest" :dir :system)

(local (include-book "std/system/w" :dir :system))
(local (include-book "std/alists/assoc" :dir :system))
(local (include-book "std/lists/len" :dir :system))
(local (include-book "std/typed-lists/atom-listp" :dir :system))
(local (include-book "std/typed-lists/boolean-listp" :dir :system))
(local (include-book "std/typed-lists/pseudo-term-listp" :dir :system))
(local (include-book "std/typed-lists/symbol-listp" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrulel posp-of-+-when-both-posp
  (implies (and (posp x)
                (posp y))
           (posp (+ x y))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atc-statement-generation
  :parents (atc-event-and-code-generation)
  :short "Generation of C statements."
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-var-assignablep ((var symbolp)
                             (innermostp booleanp)
                             (affect symbol-listp))
  :returns (yes/no booleanp :hyp (booleanp innermostp))
  :short "Check if a variable is assignable,
          based on whether it is in the innermost scope
          and based on the variables being currently affected."
  :long
  (xdoc::topstring
   (xdoc::p
    "A variable may be destructively assigned to
     if any of the following conditions apply:
     (i) it is declared in the innermost scope,
     because in that case it cannot be accessed after exiting the scope;
     (ii) it is being affected,
     because in that case its modified value is returned
     and used in subsequent code;
     (iii) no variable is being affected,
     because in that case there is no subsequent code."))
  (or innermostp
      (and (member-eq var affect) t)
      (null affect)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-vars-assignablep ((var-list symbol-listp)
                              (innermostp-list boolean-listp)
                              (affect symbol-listp))
  :guard (equal (len var-list) (len innermostp-list))
  :returns (yes/no booleanp :hyp (boolean-listp innermostp-list))
  :short "Lift @(tsee atc-var-assignablep) to lists."
  (or (endp var-list)
      (and
       (atc-var-assignablep (car var-list) (car innermostp-list) affect)
       (atc-vars-assignablep (cdr var-list) (cdr innermostp-list) affect))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-affecting-term-for-let-p ((term pseudo-termp)
                                      (prec-fns atc-symbol-fninfo-alistp))
  :returns (yes/no booleanp)
  :short "Check if a term @('term') has the basic structure
          required for representing code affecting variables
          in @('(let ((var term)) body)')
          or @('(mv-let (var1 ... varn) term body)')."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is explained in the user documentation.
     Here we perform a shallow check,
     because we examine the term in full detail
     when recursively generating C code from it.
     In essence, here we check that the term is either
     (i) an @(tsee if) whose test is not @(tsee mbt) or
     (ii) a call of a (preceding) target function."))
  (case-match term
    (('if test . &) (b* (((mv mbtp &) (check-mbt-call test)))
                      (not mbtp)))
    ((fn . &) (and (symbolp fn)
                   (consp (assoc-eq fn prec-fns))))
    (& nil))
  :guard-hints (("Goal" :in-theory (enable pseudo-termp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-make-mv-nth-terms ((indices nat-listp) (term pseudo-termp))
  :returns (terms pseudo-term-listp
                  :hints (("Goal" :induct t :in-theory (enable pseudo-termp))))
  :short "Create a list of @(tsee mv-nth)s applied to a term
          for a list of indices."
  (cond ((endp indices) nil)
        (t (cons `(mv-nth ',(car indices) ,(pseudo-term-fix term))
                 (atc-make-mv-nth-terms (cdr indices) term))))
  ///
  (defret len-of-atc-make-mv-nth-terms
    (equal (len terms)
           (len indices))
    :hints (("Goal" :induct t))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-update-var-term-alist ((vars symbol-listp)
                                   (terms pseudo-term-listp)
                                   (alist symbol-pseudoterm-alistp))
  :returns (new-alist symbol-pseudoterm-alistp)
  :short "Update an alist from symbols to terms."
  (append (pairlis$ (symbol-list-fix vars)
                    (pseudo-term-list-fix terms))
          (symbol-pseudoterm-alist-fix alist)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-ensure-formals-not-lost
  ((bind-affect symbol-listp)
   (fn-affect symbol-listp)
   (fn-typed-formals atc-symbol-varinfo-alistp)
   (fn symbolp)
   (wrld plist-worldp))
  :returns erp
  :short "Ensure that no affected formals are lost."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the body of a non-recursive function @('fn')
     includes an @(tsee mv-let)s or a @(tsee let)
     that affects a formal of @('fn') of pointer or array type,
     or a formal of integer type that represents an external object,
     that formal must be among the variables affected by @('fn').
     If the body of a recursive function @('fn')
     includes an @(tsee mv-let)s or a @(tsee let)
     that affects a formal of @('fn') of any type,
     that formal must be among the variables affected by @('fn').
     In other words, no modification of formals must be ``lost''.
     The case of formals of pointer or array types is clear,
     because it means that objects in the heap are affected.
     The case of formals of integer type that represent external objects
     is also clear, as that object is globally accessible.
     The case of formals of non-pointer non-array types
     applies to recursive functions
     because they represent loops,
     which may affect local variables in the function where they appear.")
   (xdoc::p
    "This ACL2 function ensures that no formals are lost in the sense above.
     The parameter @('bind-affect') consists of
     the variable affected by the @(tsee mv-let) or @(tsee let).
     The parameter @('fn-affect') consists of
     the variables purported to be affected by @('fn').
     We go through the elements of @('bind-affect')
     and check each one against the formals of @('fn'),
     taking into account the information about the formals
     and whether @('fn') is recursive."))
  (b* (((reterr))
       ((when (endp bind-affect)) (retok))
       (var (car bind-affect))
       (info (cdr (assoc-eq var fn-typed-formals)))
       ((when (and info
                   (or (irecursivep+ fn wrld)
                       (type-case (atc-var-info->type info) :pointer)
                       (type-case (atc-var-info->type info) :array)
                       (atc-var-info->externalp info))
                   (not (member-eq var fn-affect))))
        (reterr
         (msg "When generating C code for the function ~x0, ~
               the formal parameter ~x1 is being affected ~
               in an MV-LET or LET term, ~
               but it is not being returned by ~x0."
              fn var))))
    (atc-ensure-formals-not-lost (cdr bind-affect)
                                 fn-affect
                                 fn-typed-formals
                                 fn
                                 wrld)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-make-lets-of-uterms ((let/let* symbolp)
                                 bindings
                                 (uterms true-listp))
  :returns (let-uterms true-listp)
  :short "Create a list of @(tsee let)s or @(tsee let*)s with the same bindings
          and with bodies from a list of terms, in the same order."
  (cond ((endp uterms) nil)
        (t (cons `(,let/let* ,bindings ,(car uterms))
                 (atc-make-lets-of-uterms let/let* bindings (cdr uterms)))))
  ///
  (defret len-of-atc-make-lets-of-uterms
    (equal (len let-uterms)
           (len uterms))
    :hints (("Goal" :induct t))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-make-mv-lets-of-uterms (vars vars-uterms (uterms true-listp))
  :returns (mv-let-uterms true-listp)
  :short "Create a list of @(tsee mv-let)s with the same bindings
          and with bodies from a list of terms, in the same order."
  (cond ((endp uterms) nil)
        (t (cons `(mv-let ,vars ,vars-uterms ,(car uterms))
                 (atc-make-mv-lets-of-uterms vars vars-uterms (cdr uterms)))))
  ///
  (defret len-of-atc-make-mv-lets-of-uterms
    (equal (len mv-let-uterms)
           (len uterms))
    :hints (("Goal" :induct t))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-symbolp-list ((list true-listp))
  :returns (bools boolean-listp)
  :short "Check if each element of a list is a symbol or not,
          returning a list of booleans, one per element."
  :long
  (xdoc::topstring
   (xdoc::p
    "This lifts @(tsee symbolp) to lists.
     Note that it differs from @(tsee symbol-listp).
     This belongs to a more general library."))
  (cond ((endp list) nil)
        (t (cons (symbolp (car list))
                 (atc-symbolp-list (cdr list)))))
  ///
  (defret len-of-atc-symbolp-list
    (equal (len bools)
           (len list))
    :hints (("Goal" :induct t))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-uterm-to-components ((uterm "An untranslated term.") (comps posp))
  :returns (mv (uterms true-listp
                       :rule-classes :type-prescription
                       "Untranslated terms.")
               (varps boolean-listp)
               (bound-vars symbol-listp))
  :short "Split a term into component terms."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used in generation of type assertions in modular proofs,
     precisely in @(tsee atc-gen-term-type-formula).
     A term may return one or more results, in general.
     For terms that represent C constructs, each result has a C type,
     and the type assertions in modular theorems say just that.
     This ACL2 function turns a term into one or more terms,
     one for each returned result:
     the resulting terms represent the results of the term,
     and can be individually used as arguments of type predicates
     in the generated theorems.")
   (xdoc::p
    "A seemingly easy way to do this would be to apply @(tsee mv-nth)
     with increasing indices to the term if it returns two or more results,
     and instead return the term unchanged if it returns a single result.
     But then, because of the presence of the @(tsee mv-nth) in certain places,
     the generated theorems would not be readily applicable as rewrite rules,
     in subsequent theorems that depend on them.
     We need to ``push'' the @(tsee mv-nth)s into the term, but only to a point:
     we push them through @(tsee let)s and @(tsee mv-let)s,
     and also through @(tsee mv)s;
     in all other cases, we apply the @(tsee mv-nth)s.
     This leads to the following recursive definition,
     which includes some defensive checks.
     The @('comps') input is the number of results.")
   (xdoc::p
    "We also return a list of the bound variables encountered along the way.
     We also return a list of boolean flags, one for each component,
     each of which says whether
     pushing the @(tsee mv-nth) through the corresponding term
     reached a variable.
     The purpose of this list of bound variables
     and of this list of boolean flags
     is explained in @(tsee atc-gen-term-type-formula)."))
  (b* (((when (symbolp uterm))
        (b* (((unless (eql comps 1))
              (raise "Internal error: ~x0 components for ~x1." comps uterm)
              (mv nil nil nil)))
          (mv (list uterm)
              (list t)
              nil)))
       ((unless (and (true-listp uterm)
                     (consp uterm)))
        (raise "Internal error: unexpected term ~x0." uterm)
        (mv nil nil nil))
       ((when (eq (car uterm) 'list))
        (b* ((uterms (cdr uterm))
             ((unless (eql (len uterms) comps))
              (raise "Internal error: ~x0 components for ~x1." comps uterm)
              (mv nil nil nil)))
          (mv uterms
              (atc-symbolp-list uterms)
              nil)))
       ((when (member-eq (car uterm) '(let let*)))
        (b* (((unless (and (consp (cdr uterm))
                           (consp (cddr uterm))
                           (endp (cdddr uterm))))
              (raise "Internal error: malformed LET or LET* ~x0." uterm)
              (mv nil nil nil))
             (bindings (cadr uterm))
             ((unless (and (alistp bindings) ; really a doublet list
                           (symbol-listp (strip-cars bindings))))
              (raise "Internal error: malformed LET or LET* bindings ~x0."
                     bindings)
              (mv nil nil nil))
             (vars (strip-cars bindings))
             (body-uterm (caddr uterm))
             ((mv body-uterms varsp body-bound-vars)
              (atc-uterm-to-components body-uterm comps)))
          (mv (atc-make-lets-of-uterms (car uterm) bindings body-uterms)
              varsp
              (append vars body-bound-vars))))
       ((when (eq (car uterm) 'mv-let))
        (b* (((unless (and (consp (cdr uterm))
                           (consp (cddr uterm))
                           (consp (cdddr uterm))
                           (endp (cddddr uterm))))
              (raise "Internal error: malformed MV-LET ~x0." uterm)
              (mv nil nil nil))
             (vars (cadr uterm))
             ((unless (symbol-listp vars))
              (raise "Internal error: MV-LET bound variables not symbols." vars)
              (mv nil nil nil))
             (vars-uterms (caddr uterm))
             (body-uterm (cadddr uterm))
             ((mv body-uterms varsp body-bound-vars)
              (atc-uterm-to-components body-uterm comps)))
          (mv (atc-make-mv-lets-of-uterms vars vars-uterms body-uterms)
              varsp
              (append vars body-bound-vars)))))
    (if (eql comps 1)
        (mv (list uterm)
            (list nil)
            nil)
      (mv (rev (atc-uterm-to-components-aux uterm comps))
          (repeat comps nil)
          nil)))
  :hints (("Goal" :in-theory (enable o< o-finp)))
  :verify-guards :after-returns
  :prepwork
  ((define atc-uterm-to-components-aux ((uterm "An untranslated term.")
                                        (comps natp))
     :returns (uterms true-listp "Untranslated terms.")
     :parents nil
     (cond ((zp comps) nil)
           (t (cons `(mv-nth ,(1- comps) ,uterm)
                    (atc-uterm-to-components-aux uterm (1- comps)))))
     ///
     (defret len-of-atc-uterm-to-components-aux
       (equal (len uterms)
              (nfix comps))
       :hints (("Goal" :induct t :in-theory (enable nfix fix))))))
  ///
  (defret len-of-atc-uterm-to-components.varps
    (equal (len varps)
           (len uterms))
    :hints (("Goal" :induct t)))
  (in-theory (disable len-of-atc-uterm-to-components.varps)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-term-type-formula ((uterm "An untranslated term.")
                                   (type typep)
                                   (affect symbol-listp)
                                   (inscope atc-symbol-varinfo-alist-listp)
                                   (prec-tags atc-string-taginfo-alistp))
  :returns (mv (formula "An untranslated term.")
               (thm-names symbol-listp))
  :short "Generate a type formula for a term."
  :long
  (xdoc::topstring
   (xdoc::p
    "Each ACL2 term translated to C
     returns 0 or 1 C values
     and affects 0 or more C objects:
     the returned C value (if any) and the affected C objects
     are represented by the ACL2 values returned by the term.
     (So if the term returns 0 C values, it must affect at least one C object,
     because terms always return at least one ACL2 value.)
     Each value returned by the term has a C type,
     which has a corresponding ACL2 recognizer.
     Here we return a formula that is a conjunction of assertions,
     one per value returned by the term,
     which applies the associated recognizer
     to the corresponding term's result.")
   (xdoc::p
    "For each array value returned by the term,
     we also return, as part of the formula,
     an assertion saying that the length of the array
     is the same as the corresponding variable.
     Since a C array type is described by both the element type and the size,
     it makes sense that assertions about the length
     accompany assertions involving the recognizers
     (which only talk about the element type).
     These assertions are not generated
     when they would lead to rewrite rules
     that rewrite a term to itself,
     which are illegal rewrite rules;
     the exact circumstances are explained below.")
   (xdoc::p
    "We also return the names of the theorems from the symbol table
     that are associated to each variable for the affected objects.
     These are used to prove the formula returned here.")
   (xdoc::p
    "We go through the @('affect') list and collect
     the list of corresponding types, from the symbol table @('inscope').
     If @('type') is not @('void'), we @(tsee cons) it to the list.
     This way, we obtain the list of all the types of
     all the values returned by the term.
     This list cannot be empty, because a term always returns some values.
     Then we use @(tsee atc-uterm-to-components) to obtain terms for the results
     (see that function's documentation).
     Finally we go through the types and terms,
     which must be equal in number,
     and return formulas for the terms.
     We skip the array length sub-formula exactly when
     the boolean flag returned by @(tsee atc-uterm-to-components) is @('nil')
     or it is not but the (affected) variable is bound in the term."))
  (b* (((mv affect-types thm-names) (atc-gen-type-formulas-aux1 affect inscope))
       (types (if (type-case type :void)
                  affect-types
                (cons type affect-types)))
       ((when (endp types))
        (raise "Internal error: term ~x0 returns no values." uterm)
        (mv nil nil))
       ((mv uterms varps bound-vars)
        (atc-uterm-to-components uterm (len types)))
       (conjuncts
        (atc-gen-type-formulas-aux2 types
                                    uterms
                                    varps
                                    bound-vars
                                    (if (type-case type :void)
                                        affect
                                      (cons nil affect))
                                    prec-tags))
       (formula (if (endp (cdr conjuncts))
                    (car conjuncts)
                  `(and ,@conjuncts))))
    (mv formula thm-names))
  :guard-hints (("Goal" :in-theory (enable posp)))

  :prepwork

  ((define atc-gen-type-formulas-aux1 ((affect symbol-listp)
                                       (inscope atc-symbol-varinfo-alist-listp))
     :returns (mv (types type-listp)
                  (thm-names symbol-listp))
     :parents nil
     (b* (((when (endp affect)) (mv nil nil))
          (var (car affect))
          (info (atc-get-var var inscope))
          ((unless info)
           (raise "Internal error: no information for variable ~x0." var)
           (mv nil nil))
          (type (atc-var-info->type info))
          (thm-name (atc-var-info->thm info))
          ((mv more-types more-thm-names)
           (atc-gen-type-formulas-aux1 (cdr affect) inscope)))
       (mv (cons type more-types)
           (cons thm-name more-thm-names)))
     ///
     (more-returns
      (types true-listp :rule-classes :type-prescription)))

   (define atc-gen-type-formulas-aux2 ((types type-listp)
                                       (uterms true-listp)
                                       (varps boolean-listp)
                                       (bound-vars symbol-listp)
                                       (affected-vars symbol-listp)
                                       (prec-tags atc-string-taginfo-alistp))
     :returns (conjuncts true-listp)
     :parents nil
     (b* (((when (endp types)) nil)
          (type (car types))
          (uterm (car uterms))
          (affected-var (car affected-vars))
          (pred (atc-type-to-recognizer type prec-tags))
          (conjuncts
           (if (type-case type :array)
               (b* ((elemtype (type-array->of type))
                    (elemfixtype (type-kind elemtype))
                    (array-length (pack elemfixtype '-array-length)))
                 `((,pred ,uterm)
                   ,@(and (or (not (car varps))
                              (member-eq affected-var bound-vars))
                          `((equal (,array-length ,uterm)
                                   (,array-length ,affected-var))))))
             `((,pred ,uterm))))
          (more-conjuncts (atc-gen-type-formulas-aux2 (cdr types)
                                                      (cdr uterms)
                                                      (cdr varps)
                                                      bound-vars
                                                      (cdr affected-vars)
                                                      prec-tags)))
       (append conjuncts more-conjuncts)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-stmt-value-term-and-type-formula
  ((uterm "An untranslated term.")
   (type typep)
   (affect symbol-listp)
   (inscope atc-symbol-varinfo-alist-listp)
   (prec-tags atc-string-taginfo-alistp))
  :returns (mv (stmt-value "An untranslated term.")
               (type-formula "An untranslated term.")
               (type-thms symbol-listp))
  :short "Generates a statement value term and a type formula for a term."
  :long
  (xdoc::topstring
   (xdoc::p
    "This extends @(tsee atc-gen-term-type-formula)
     to also return a term that is the statement value result of @('uterm').
     We should probably integrate this code
     with @(tsee atc-gen-term-type-formula)."))
  (b* (((mv type-formula type-thms)
        (atc-gen-term-type-formula uterm type affect inscope prec-tags))
       ((when (type-case type :void))
        (mv '(stmt-value-none) type-formula type-thms))
       ((mv uterms & &) (atc-uterm-to-components uterm (1+ (len affect)))))
    (mv `(stmt-value-return ,(car uterms)) type-formula type-thms)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-call-result-and-endstate
  ((type typep "Return type of the C function.")
   (affect symbol-listp "Variables affected by the C function.")
   (inscope atc-symbol-varinfo-alist-listp)
   (compst-var symbolp)
   (call "An untranslated term."))
  :returns (mv (result "An untranslated term.")
               (new-compst "An untranslated term."))
  :short "Generate a term representing the result value
          and a term representing the ending computation state
          of the execution of a C function call."
  :long
  (xdoc::topstring
   (xdoc::p
    "If no variables are affected,
     the computation state is unchanged,
     and the call is the result.
     (In this case the type is not @('void'),
     but this is not an explicitly checked invariant in this code.)")
   (xdoc::p
    "Otherwise, if exactly one variable is affected,
     and additionally the function is @('void'),
     we return @('nil') as the result term,
     while the new computation state is obtained
     by updating the affected object with the call.")
   (xdoc::p
    "Otherwise, there are two cases.
     If the function is @('void'), we return @('nil') as result term,
     and as new computation state we return the nest of object updates
     for all the @(tsee mv-nth) components of the call, starting with index 0.
     If the function is not @('void'),
     we return the @(tsee mv-nth) of index 0 of the call as result term,
     and as new computation state the nest of object updates
     with the @(tsee mv-nth) components starting with index 1.
     In either case, the nest is calculated by an auxiliary function."))
  (b* (((when (endp affect)) (mv call compst-var))
       ((when (and (endp (cdr affect))
                   (type-case type :void)))
        (b* ((var (car affect))
             (info (atc-get-var var inscope))
             ((when (not info))
              (raise "Internal error: variable ~x0 not found." var)
              (mv nil nil))
             (type (atc-var-info->type info))
             ((unless (or (type-case type :pointer)
                          (type-case type :array)
                          (atc-var-info->externalp info)))
              (raise "Internal error:
                      affected variable ~x0 ~
                      has type ~x1 and is not an external object."
                     var type)
              (mv nil nil))
             (new-compst
              (if (atc-var-info->externalp info)
                  `(update-static-var (ident ,(symbol-name var))
                                      ,call
                                      ,compst-var)
                `(update-object ,(add-suffix-to-fn var "-OBJDES")
                                ,call
                                ,compst-var))))
          (mv nil new-compst))))
    (if (type-case type :void)
        (mv nil
            (atc-gen-call-endstate affect inscope compst-var call 0))
      (mv `(mv-nth 0 ,call)
          (atc-gen-call-endstate affect inscope compst-var call 1))))

  :prepwork
  ((define atc-gen-call-endstate ((affect symbol-listp)
                                  (inscope atc-symbol-varinfo-alist-listp)
                                  (compst-var symbolp)
                                  (call "An untranslated term.")
                                  (index natp))
     :returns (term "An untranslated term.")
     :parents nil
     (b* (((when (endp affect)) compst-var)
          (var (car affect))
          (info (atc-get-var var inscope))
          ((when (not info))
           (raise "Internal error: variable ~x0 not found." var))
          (type (atc-var-info->type info))
          ((unless (or (type-case type :pointer)
                       (type-case type :array)
                       (atc-var-info->externalp info)))
           (raise "Internal error:
                   affected variable ~x0 ~
                   has type ~x1 and is not an external object."
                  var type)))
       (if (atc-var-info->externalp info)
           `(update-static-var (ident ,(symbol-name var))
                               (mv-nth ,index ,call)
                               ,(atc-gen-call-endstate (cdr affect)
                                                       inscope
                                                       compst-var
                                                       call
                                                       (1+ index)))
         `(update-object ,(add-suffix-to-fn var "-OBJDES")
                         (mv-nth ,index ,call)
                         ,(atc-gen-call-endstate (cdr affect)
                                                 inscope
                                                 compst-var
                                                 call
                                                 (1+ index))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-remove-extobj-args ((args expr-listp)
                                (formals symbol-listp)
                                (extobjs symbol-listp))
  :returns (filtered-args expr-listp :hyp (expr-listp args))
  :short "Remove from a list of argument terms
          the ones that are external objects."
  :long
  (xdoc::topstring
   (xdoc::p
    "While ACL2 functions have explicit arguments for external objects,
     the corresponding C functions do not, because they access them directly.
     Thus, when generating code for C function calls,
     we must omit the ACL2 function arguments that are external objects.
     Those arguments are removed using this code."))
  (b* (((when (endp args))
        (b* (((unless (endp formals))
              (raise "Internal error: extra formals ~x0." formals)))
          nil))
       ((unless (consp formals))
        (raise "Internal error: extra arguments ~x0." args))
       (arg (car args))
       (formal (car formals)))
    (if (member-eq formal extobjs)
        (atc-remove-extobj-args (cdr args) (cdr formals) extobjs)
      (cons arg (atc-remove-extobj-args (cdr args) (cdr formals) extobjs)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod stmt-gin
  :short "Inputs for C statement generation."
  :long
  (xdoc::topstring
   (xdoc::p
    "This does not include the term, which is passed as a separate input."))
  ((context atc-contextp
            "Described in @(see atc-implementation).
             It is the context just before this statement,
             i.e. the context in which this statement is generated.")
   (var-term-alist symbol-pseudoterm-alist
                   "Described in @(see atc-implementation).")
   (typed-formals atc-symbol-varinfo-alist
                  "Described in @(see atc-implementation).")
   (inscope atc-symbol-varinfo-alist-list
            "Described in @(see atc-implementation).
             It contains the variables in scope just before this statement,
             i.e. the ones in scope for this statement.")
   (loop-flag booleanp
              "The @('L') flag described in the user documentation.")
   (affect symbol-list
           "Described in @(see atc-implementation).")
   (fn symbolp
       "Described in @(see atc-implementation).
        It is the target function for which the statement is generated.")
   (fn-guard symbol
             "Described in @(see atc-implementation).")
   (compst-var symbol
               "Described in @(see atc-implementation).")
   (fenv-var symbol
             "Described in @(see atc-implementation).")
   (limit-var symbol
              "Described in @(see atc-implementation).")
   (prec-fns atc-symbol-fninfo-alist
             "Described in @(see atc-implementation).")
   (prec-tags atc-string-taginfo-alist
              "Described in @(see atc-implementation).")
   (prec-objs atc-string-objinfo-alist
              "Described in @(see atc-implementation).")
   (thm-index pos
              "Described in @(see atc-implementation).")
   (names-to-avoid symbol-list
                   "Described in @(see atc-implementation).")
   (proofs bool
           "A flag indicating whether modular proof generation
            should continue or not.
            This will be eliminated when modular proof generation
            will cover all of the ATC-generated code."))
  :pred stmt-ginp)

;;;;;;;;;;;;;;;;;;;;

(fty::defprod stmt-gout
  :short "Outputs for C statement generation."
  :long
  (xdoc::topstring
   (xdoc::p
    "We actually generate a list of block items.
     These can be regarded as forming a compound statement,
     but lists of block items are compositional (via concatenation)."))
  ((items block-item-list
          "We actually generate a list of block items.
           These can be regarded as forming a compound statement,
           but lists of block items are compositional (via concatenation).")
   (type type
         "The type returned by the block items.
          It may be @('void').")
   (term pseudo-termp
         "The term from which the block items are generated.
          The term is transformed by replacing @(tsee if) with @(tsee if*)
          and a few other changes.")
   (context atc-context
            "Described in @(see atc-implementation).
             It is the context after the block items,
             i.e. the context for subsequent block items (if any).")
   (inscope atc-symbol-varinfo-alist-list
            "Described in @(see atc-implementation).
             It contains the variables in scope just after these block items,
             i.e. the ones in scope for subsequent block items (if any).
             This is @('nil') if there are no subsequent block items,
             which happens exactly when
             these block items return a non-@('void') type.")
   (limit pseudo-term
          "Symbolic limit value
           that suffices for @(tsee exec-block-item-list)
           to execute the block items completely.")
   (events pseudo-event-form-list
           "All the events generated for the block items.")
   (thm-name symbol
             "The name of the theorem about @(tsee exec-block-item-list)
              applied to the block items.
              This theorem is one of the events in @('events').
              It is @('nil') if no theorem was generated,
              because modular proof generation is not yet available
              for some constructs;
              eventually this will be never @('nil'),
              when modular proof generation covers
              all the ATC-generated code.")
   (thm-index pos
              "Described in @(see atc-implementation).")
   (names-to-avoid symbol-list
                   "Described in @(see atc-implementation)."))
  :pred stmt-goutp)

;;;;;;;;;;

(defirrelevant irr-stmt-gout
  :short "An irrelevant output for C statement generation."
  :type stmt-goutp
  :body (make-stmt-gout :items nil
                        :type (irr-type)
                        :term nil
                        :context (irr-atc-context)
                        :inscope nil
                        :limit nil
                        :events nil
                        :thm-name nil
                        :thm-index 1
                        :names-to-avoid nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-expr ((term pseudo-termp) (gin stmt-ginp) state)
  :returns (mv erp
               (expr exprp)
               (type typep)
               (term* pseudo-termp :hyp (pseudo-termp term))
               (result "An untranslated term.")
               (new-compst "An untranslated term.")
               (limit pseudo-termp)
               (events pseudo-event-form-listp)
               (thm-name symbolp)
               (new-inscope atc-symbol-varinfo-alist-listp)
               (new-context atc-contextp)
               (thm-index posp)
               (names-to-avoid symbol-listp))
  :short "Generate a C expression from an ACL2 term
          that must be an expression term."
  :long
  (xdoc::topstring
   (xdoc::p
    "At the same time,
     we check that the term is an expression term,
     as described in the user documentation.")
   (xdoc::p
    "It may seem surprising that this function is
     under @(see atc-statement-generation)
     instead of @(see atc-expression-generation),
     but it needs to come after @(tsee stmt-gin)
     because it takes that as an input.
     Indeed, this ACL2 function is used
     for top-level or near-top-level expressions within statements,
     and so it is not unreasonable that
     this function is ``close'' to the statement generation functions.
     Note that functions to generate assignment expressions
     are also under @(see atc-statement-generation),
     since they are top-level expressions
     (in C terminology, they are full expressions [C17:6.8/4]).")
   (xdoc::p
    "We also return the C type of the expression,
     the transformed term,
     the term for the C result of the expression,
     the term for the C computation state after the execution of the expression,
     a limit that suffices for @(tsee exec-expr-call-or-pure)
     to execute the expression completely,
     and then the usual outputs.")
   (xdoc::p
    "If the term is a call of a function that precedes @('fn')
     in the list of target functions among @('t1'), ..., @('tp'),
     we translate it to a C function call on the translated arguments.
     The type of the expression is the result type of the function,
     which is looked up in the function alist passed as input:
     we ensure that this type is not @('void').
     A sufficient limit for @(tsee exec-fun) to execute the called function
     is retrieved from the called function's information;
     we add 2 to it, to take into account the decrementing of the limit
     to go from @(tsee exec-expr-call-or-pure) to @(tsee exec-expr-call)
     and from there to @(tsee exec-fun).
     If the called function affects no objects,
     the @('result') term is essentially the untranslation of the input term,
     and @('new-compst') is the same as the computation state variable;
     if the called function affects objects,
     the @('result') term is @(tsee mv-nth) of 0 applied to the call,
     and @('new-compst') updates the computation state variable
     with the @(tsee mv-nth)s of 1, 2, etc. applied to the call.")
   (xdoc::p
    "Otherwise, we attempt to translate the term as a pure expression term.
     The type is the one returned by that translation.
     As limit we return 1, which suffices for @(tsee exec-expr-call-or-pure)
     to not stop right away due to the limit being 0.
     In this case, @('result') is essentially the untranslated input term,
     and @('new-compst') is the computation state variable unchanged."))
  (b* (((reterr)
        (irr-expr)
        (irr-type)
        nil
        nil
        nil
        nil
        nil
        nil
        nil
        (irr-atc-context)
        1
        nil)
       ((stmt-gin gin) gin)
       (wrld (w state))
       ((erp okp
             called-fn
             arg-terms
             in-types
             out-type
             affect
             extobjs
             limit
             called-fn-guard)
        (atc-check-cfun-call term gin.var-term-alist gin.prec-fns wrld))
       ((when okp)
        (b* (((when (type-case out-type :void))
              (reterr
               (msg "A call ~x0 of the function ~x1, which returns void, ~
                     is being used where ~
                     an expression term returning a a non-void C type ~
                     is expected."
                    term called-fn)))
             ((unless (equal affect gin.affect))
              (reterr
               (msg "The call ~x0 affects ~x1, ~
                     but it should affect ~x2 instead."
                    term gin.affect affect)))
             ((erp (exprs-gout args))
              (atc-gen-expr-pure-list arg-terms
                                      (make-exprs-gin
                                       :context gin.context
                                       :inscope gin.inscope
                                       :prec-tags gin.prec-tags
                                       :fn gin.fn
                                       :fn-guard gin.fn-guard
                                       :compst-var gin.compst-var
                                       :thm-index gin.thm-index
                                       :names-to-avoid gin.names-to-avoid
                                       :proofs gin.proofs)
                                      state))
             ((unless (equal args.types in-types))
              (reterr
               (msg "The function ~x0 with input types ~x1 ~
                     is applied to expression terms ~x2 returning ~x3. ~
                     This is indicative of provably dead code, ~
                     given that the code is guard-verified."
                    called-fn in-types arg-terms args.types)))
             (call-args (atc-remove-extobj-args args.exprs
                                                (formals+ called-fn wrld)
                                                extobjs))
             (expr (make-expr-call
                    :fun (make-ident :name (symbol-name called-fn))
                    :args call-args))
             ((when (eq called-fn 'quote))
              (reterr (raise "Internal error: called function is QUOTE.")))
             (term `(,called-fn ,@args.terms))
             (uterm (untranslate$ term nil state))
             (fninfo (cdr (assoc-eq called-fn gin.prec-fns)))
             ((unless fninfo)
              (reterr (raise "Internal error: function ~x0 has no info."
                             called-fn)))
             (called-fn-thm (atc-fn-info->correct-mod-thm fninfo))
             ((when (or (not gin.proofs)
                        (not called-fn-thm)))
              (retok expr
                     out-type
                     term
                     nil
                     nil
                     `(binary-+ '2 ,limit)
                     args.events
                     nil
                     gin.inscope
                     gin.context
                     args.thm-index
                     args.names-to-avoid))
             (guard-lemma-name
              (pack gin.fn '-call- args.thm-index '-guard-lemma))
             ((mv guard-lemma-name names-to-avoid)
              (fresh-logical-name-with-$s-suffix guard-lemma-name
                                                 nil
                                                 args.names-to-avoid
                                                 wrld))
             (thm-index (1+ args.thm-index))
             (guard-lemma-formula `(,called-fn-guard ,@args.terms))
             (guard-lemma-formula (atc-contextualize guard-lemma-formula
                                                     gin.context
                                                     gin.fn
                                                     gin.fn-guard
                                                     nil
                                                     nil
                                                     nil
                                                     nil
                                                     wrld))
             (guard-lemma-hints
              `(("Goal"
                 :in-theory '(,gin.fn-guard ,called-fn-guard if* test*)
                 :use (:guard-theorem ,gin.fn))))
             ((mv guard-lemma-event &)
              (evmac-generate-defthm guard-lemma-name
                                     :formula guard-lemma-formula
                                     :hints guard-lemma-hints
                                     :enable nil))
             (call-thm-name (pack gin.fn '-correct- thm-index))
             ((mv call-thm-name names-to-avoid)
              (fresh-logical-name-with-$s-suffix
               call-thm-name nil names-to-avoid wrld))
             (thm-index (1+ thm-index))
             (called-formals (formals+ called-fn wrld))
             ((unless (equal (len called-formals) (len args.terms)))
              (reterr
               (raise "Internal error: ~x0 has formals ~x1 but actuals ~x2."
                      called-fn called-formals args.terms)))
             (call-limit `(binary-+ '2 ,limit))
             ((mv result new-compst)
              (atc-gen-call-result-and-endstate out-type
                                                gin.affect
                                                gin.inscope
                                                gin.compst-var
                                                uterm))
             (exec-formula `(equal (exec-expr-call-or-pure ',expr
                                                           ,gin.compst-var
                                                           ,gin.fenv-var
                                                           ,gin.limit-var)
                                   (mv ,result ,new-compst)))
             (exec-formula (atc-contextualize exec-formula
                                              gin.context
                                              gin.fn
                                              gin.fn-guard
                                              gin.compst-var
                                              gin.limit-var
                                              call-limit
                                              t
                                              wrld))
             ((mv type-formula &)
              (atc-gen-term-type-formula uterm
                                         out-type
                                         gin.affect
                                         gin.inscope
                                         gin.prec-tags))
             (type-formula (atc-contextualize type-formula
                                              gin.context
                                              gin.fn
                                              gin.fn-guard
                                              nil
                                              nil
                                              nil
                                              nil
                                              wrld))
             (call-formula `(and ,exec-formula ,type-formula))
             (call-hints
              `(("Goal"
                 :in-theory
                 '(exec-expr-call-or-pure-when-call
                   exec-expr-call-open
                   exec-expr-pure-list-of-nil
                   exec-expr-pure-list-when-consp
                   ,@args.thm-names
                   ,called-fn-thm
                   ,guard-lemma-name
                   ,@(atc-symbol-varinfo-alist-list-to-thms gin.inscope)
                   exec-fun-of-const-identifier
                   (:e identp)
                   (:e ident->name)
                   (:e expr-kind)
                   (:e expr-call->fun)
                   (:e expr-call->args)
                   not-zp-of-limit-variable
                   not-zp-of-limit-minus-const
                   expr-valuep-of-expr-value
                   expr-value->value-of-expr-value
                   value-listp-of-cons
                   (:e value-listp)
                   apconvert-expr-value-when-not-value-array
                   value-kind-when-ucharp
                   value-kind-when-scharp
                   value-kind-when-ushortp
                   value-kind-when-sshortp
                   value-kind-when-uintp
                   value-kind-when-sintp
                   value-kind-when-ulongp
                   value-kind-when-slongp
                   value-kind-when-ullongp
                   value-kind-when-sllongp
                   ,@(atc-string-taginfo-alist-to-value-kind-thms gin.prec-tags)
                   value-fix-when-valuep
                   valuep-when-ucharp
                   valuep-when-scharp
                   valuep-when-ushortp
                   valuep-when-sshortp
                   valuep-when-uintp
                   valuep-when-sintp
                   valuep-when-ulongp
                   valuep-when-slongp
                   valuep-when-ullongp
                   valuep-when-sllongp
                   ,@(atc-string-taginfo-alist-to-valuep-thms gin.prec-tags)
                   compustatep-of-add-var
                   compustatep-of-enter-scope
                   compustatep-of-add-frame
                   write-object-to-update-object
                   write-object-okp-when-valuep-of-read-object-no-syntaxp
                   write-object-okp-of-update-object-same
                   write-object-okp-of-update-object-disjoint
                   object-disjointp-commutative
                   type-of-value-when-ucharp
                   type-of-value-when-scharp
                   type-of-value-when-ushortp
                   type-of-value-when-sshortp
                   type-of-value-when-uintp
                   type-of-value-when-sintp
                   type-of-value-when-ulongp
                   type-of-value-when-slongp
                   type-of-value-when-ullongp
                   type-of-value-when-sllongp
                   type-of-value-when-uchar-arrayp
                   type-of-value-when-schar-arrayp
                   type-of-value-when-ushort-arrayp
                   type-of-value-when-sshort-arrayp
                   type-of-value-when-uint-arrayp
                   type-of-value-when-sint-arrayp
                   type-of-value-when-ulong-arrayp
                   type-of-value-when-slong-arrayp
                   type-of-value-when-ullong-arrayp
                   type-of-value-when-sllong-arrayp
                   ,@(atc-string-taginfo-alist-to-type-of-value-thms
                      gin.prec-tags)))))
             ((mv call-event &) (evmac-generate-defthm call-thm-name
                                                       :formula call-formula
                                                       :hints call-hints
                                                       :enable nil)))
          (retok expr
                 out-type
                 term
                 result
                 new-compst
                 `(binary-+ '2 ,limit)
                 (append args.events
                         (list guard-lemma-event
                               call-event))
                 nil ; TODO: call-thm-name
                 gin.inscope
                 gin.context
                 thm-index
                 names-to-avoid)))
       ((erp (expr-gout pure))
        (atc-gen-expr-pure term
                           (make-expr-gin :context gin.context
                                          :inscope gin.inscope
                                          :prec-tags gin.prec-tags
                                          :fn gin.fn
                                          :fn-guard gin.fn-guard
                                          :compst-var gin.compst-var
                                          :thm-index gin.thm-index
                                          :names-to-avoid gin.names-to-avoid
                                          :proofs gin.proofs)
                           state))
       (bound '(quote 1))
       ((when (not gin.proofs))
        (retok pure.expr
               pure.type
               pure.term
               (untranslate$ pure.term nil state)
               gin.compst-var
               bound
               pure.events
               nil
               gin.inscope
               gin.context
               pure.thm-index
               pure.names-to-avoid))
       (thm-name (pack gin.fn '-correct- pure.thm-index))
       ((mv thm-name names-to-avoid) (fresh-logical-name-with-$s-suffix
                                      thm-name nil pure.names-to-avoid wrld))
       (type-pred (atc-type-to-recognizer pure.type gin.prec-tags))
       (valuep-when-type-pred
        (atc-type-to-valuep-thm pure.type gin.prec-tags))
       (value-kind-when-type-pred
        (atc-type-to-value-kind-thm pure.type gin.prec-tags))
       (uterm* (untranslate$ pure.term nil state))
       (formula1 `(equal (exec-expr-call-or-pure ',pure.expr
                                                 ,gin.compst-var
                                                 ,gin.fenv-var
                                                 ,gin.limit-var)
                         (mv ,uterm* ,gin.compst-var)))
       (formula2 `(,type-pred ,uterm*))
       (formula1 (atc-contextualize formula1
                                    gin.context
                                    gin.fn
                                    gin.fn-guard
                                    gin.compst-var
                                    gin.limit-var
                                    ''1
                                    t
                                    wrld))
       (formula2 (atc-contextualize formula2
                                    gin.context
                                    gin.fn
                                    gin.fn-guard
                                    nil
                                    nil
                                    nil
                                    nil
                                    wrld))
       (formula `(and ,formula1 ,formula2))
       (hints `(("Goal" :in-theory '(compustatep-of-add-frame
                                     compustatep-of-add-var
                                     compustatep-of-enter-scope
                                     compustatep-of-update-var
                                     compustatep-of-update-object
                                     compustatep-of-exit-scope
                                     compustatep-of-if*-when-both-compustatep
                                     exec-expr-call-or-pure-when-pure
                                     (:e expr-kind)
                                     not-zp-of-limit-variable
                                     ,pure.thm-name
                                     expr-valuep-of-expr-value
                                     expr-value->value-of-expr-value
                                     value-fix-when-valuep
                                     ,valuep-when-type-pred
                                     apconvert-expr-value-when-not-value-array
                                     ,value-kind-when-type-pred))))
       ((mv event &) (evmac-generate-defthm thm-name
                                            :formula formula
                                            :hints hints
                                            :enable nil)))
    (retok pure.expr
           pure.type
           pure.term
           (untranslate$ pure.term nil state)
           gin.compst-var
           bound
           (append pure.events (list event))
           thm-name
           gin.inscope
           gin.context
           (1+ pure.thm-index)
           names-to-avoid))
  :guard-hints
  (("Goal"
    :in-theory
    (e/d (length
          alistp-when-atc-symbol-fninfo-alistp-rewrite)
         ((:e tau-system)))))
  :prepwork ((local (in-theory (enable pseudo-termp)))
             (defrulel verify-guards-lemma
               (implies (symbol-listp x)
                        (not (stringp x))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-block-item-stmt ((stmt stmtp)
                                 (stmt-limit pseudo-termp)
                                 (stmt-events pseudo-event-form-listp)
                                 (stmt-thm symbolp)
                                 (uterm? "An untranslated term.")
                                 (type typep)
                                 (stmt-value "An untranslated term.")
                                 (new-compst "An untranslated term.")
                                 (gin stmt-ginp)
                                 state)
  :returns (mv (item block-itemp)
               (item-limit pseudo-termp)
               (item-events pseudo-event-form-listp
                            :hyp (pseudo-event-form-listp stmt-events))
               (item-thm symbolp)
               (thm-index posp :rule-classes (:rewrite :type-prescription))
               (names-to-avoid symbol-listp))
  :short "Generate a C block item that consists of a given statement."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used to lift generated statements
     to generated block items.
     Besides the block item,
     we also generate a theorem saying that
     @(tsee exec-block-item) applied to the quoted block item
     yields an @(tsee mv) pair consisting of
     a statement value term
     and a possibly updated computation state;
     these are the same as the ones for the statement theorem.")
   (xdoc::p
    "If @('uterm?') is not @('nil'),
     we also generate, as part of the theorem,
     an assertion that the term returns a value, or values,
     of the expected type(s).
     Callers pass a non-@('nil') @('uterm?')
     when the block item corresponds to a full ACL2 term
     (e.g. a conditional);
     while they pass @('nil') otherwise
     (e.g. for an assignment).")
   (xdoc::p
    "The limit for the block item is
     1 more than the limit for the statement,
     because we need 1 to go from @(tsee exec-block-item)
     to the @(':stmt') case and @(tsee exec-stmt)."))
  (b* (((stmt-gin gin) gin)
       (wrld (w state))
       (item (block-item-stmt stmt))
       (item-limit (pseudo-term-fncall
                    'binary-+
                    (list (pseudo-term-quote 1)
                          stmt-limit)))
       (name (pack gin.fn '-correct- gin.thm-index))
       (thm-index (1+ gin.thm-index))
       ((mv name names-to-avoid)
        (fresh-logical-name-with-$s-suffix name nil gin.names-to-avoid wrld))
       (exec-formula `(equal (exec-block-item ',item
                                              ,gin.compst-var
                                              ,gin.fenv-var
                                              ,gin.limit-var)
                             (mv ,stmt-value ,new-compst)))
       (exec-formula (atc-contextualize exec-formula
                                        gin.context
                                        gin.fn
                                        gin.fn-guard
                                        gin.compst-var
                                        gin.limit-var
                                        item-limit
                                        t
                                        wrld))
       (formula
        (if uterm?
            (b* (((mv type-formula &)
                  (atc-gen-term-type-formula uterm?
                                             type
                                             gin.affect
                                             gin.inscope
                                             gin.prec-tags))
                 (type-formula (atc-contextualize type-formula
                                                  gin.context
                                                  gin.fn
                                                  gin.fn-guard
                                                  nil
                                                  nil
                                                  nil
                                                  nil
                                                  wrld)))
              `(and ,exec-formula ,type-formula))
          exec-formula))
       (hints
        `(("Goal" :in-theory '(exec-block-item-when-stmt
                               (:e block-item-kind)
                               not-zp-of-limit-variable
                               (:e block-item-stmt->get)
                               ,stmt-thm
                               uchar-array-length-of-uchar-array-write
                               schar-array-length-of-schar-array-write
                               ushort-array-length-of-ushort-array-write
                               sshort-array-length-of-sshort-array-write
                               uint-array-length-of-uint-array-write
                               sint-array-length-of-sint-array-write
                               ulong-array-length-of-ulong-array-write
                               slong-array-length-of-slong-array-write
                               ullong-array-length-of-ullong-array-write
                               sllong-array-length-of-sllong-array-write))))
       ((mv event &) (evmac-generate-defthm name
                                            :formula formula
                                            :hints hints
                                            :enable nil)))
    (mv item
        item-limit
        (append stmt-events (list event))
        name
        thm-index
        names-to-avoid)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-block-item-declon ((var symbolp)
                                   (type typep)
                                   (expr exprp)
                                   (expr-term pseudo-termp)
                                   (expr-limit pseudo-termp)
                                   (expr-events pseudo-event-form-listp)
                                   (expr-thm symbolp)
                                   (gin stmt-ginp)
                                   state)
  :returns (mv (item block-itemp)
               (item-limit pseudo-termp :hyp (pseudo-termp expr-limit))
               (item-events pseudo-event-form-listp
                            :hyp (pseudo-event-form-listp expr-events))
               (item-thm symbolp)
               (new-inscope atc-symbol-varinfo-alist-listp)
               (new-context atc-contextp)
               (thm-index posp)
               (names-to-avoid symbol-listp))
  :short "Generate a C block item that consists of an object declaration."
  :long
  (xdoc::topstring
   (xdoc::p
    "We get the (ACL2) variable, the type, and the expressions as inputs.
     We return not only the block item,
     and also a symbol table updated with the variable.")
   (xdoc::p
    "We generate a theorem about executing the initializer,
     and a theorem about executing the block item."))
  (b* (((stmt-gin gin) gin)
       (wrld (w state))
       ((mv tyspec declor) (ident+type-to-tyspec+declor
                            (make-ident :name (symbol-name var))
                            type))
       (initer (initer-single expr))
       (initer-limit `(binary-+ '1 ,expr-limit))
       (declon (make-obj-declon :scspec (scspecseq-none)
                                :tyspec tyspec
                                :declor declor
                                :init? initer))
       (item (block-item-declon declon))
       (item-limit `(binary-+ '2 ,initer-limit))
       (varinfo (make-atc-var-info :type type :thm nil :externalp nil))
       ((when (not gin.proofs))
        (mv item
            item-limit
            expr-events
            nil
            (atc-add-var var varinfo gin.inscope)
            gin.context
            gin.thm-index
            gin.names-to-avoid))
       (initer-thm-name (pack gin.fn '-correct- gin.thm-index))
       (thm-index (1+ gin.thm-index))
       ((mv initer-thm-name names-to-avoid)
        (fresh-logical-name-with-$s-suffix initer-thm-name
                                           nil
                                           gin.names-to-avoid
                                           wrld))
       (initer-formula `(equal (exec-initer ',initer
                                            ,gin.compst-var
                                            ,gin.fenv-var
                                            ,gin.limit-var)
                               (mv (init-value-single ,expr-term)
                                   ,gin.compst-var)))
       (initer-formula
        (atc-contextualize initer-formula
                           gin.context
                           gin.fn
                           gin.fn-guard
                           gin.compst-var
                           gin.limit-var
                           initer-limit
                           t
                           wrld))
       (valuep-when-type-pred (atc-type-to-valuep-thm type gin.prec-tags))
       (initer-hints `(("Goal" :in-theory '(exec-initer-when-single
                                            (:e initer-kind)
                                            not-zp-of-limit-variable
                                            (:e initer-single->get)
                                            ,expr-thm
                                            ,valuep-when-type-pred
                                            mv-nth-of-cons
                                            (:e zp)))))
       ((mv initer-thm-event &) (evmac-generate-defthm initer-thm-name
                                                       :formula initer-formula
                                                       :hints initer-hints
                                                       :enable nil))
       (new-compst
        `(add-var (ident ',(symbol-name var)) ,expr-term ,gin.compst-var))
       (item-thm-name (pack gin.fn '-correct- thm-index))
       (thm-index (1+ thm-index))
       ((mv item-thm-name names-to-avoid)
        (fresh-logical-name-with-$s-suffix item-thm-name
                                           nil
                                           names-to-avoid
                                           wrld))
       (item-formula `(equal (exec-block-item ',item
                                              ,gin.compst-var
                                              ,gin.fenv-var
                                              ,gin.limit-var)
                             (mv (stmt-value-none)
                                 ,(untranslate$ new-compst nil state))))
       (item-formula (atc-contextualize item-formula
                                        gin.context
                                        gin.fn
                                        gin.fn-guard
                                        gin.compst-var
                                        gin.limit-var
                                        item-limit
                                        t
                                        wrld))
       (type-of-value-when-type-pred
        (atc-type-to-type-of-value-thm type gin.prec-tags))
       (e-type `(:e ,(car (type-to-maker type))))
       (item-hints
        `(("Goal"
           :in-theory '(exec-block-item-when-declon
                        exec-obj-declon-open
                        (:e block-item-kind)
                        not-zp-of-limit-variable
                        not-zp-of-limit-minus-const
                        (:e block-item-declon->get)
                        (:e obj-declon-to-ident+scspec+tyname+init)
                        mv-nth-of-cons
                        (:e zp)
                        (:e scspecseq-kind)
                        (:e tyname-to-type)
                        (:e type-kind)
                        ,initer-thm-name
                        return-type-of-init-value-single
                        init-value-to-value-when-single
                        ,expr-thm
                        ,valuep-when-type-pred
                        ,type-of-value-when-type-pred
                        ,e-type
                        create-var-of-const-identifier
                        (:e identp)
                        (:e ident->name)
                        create-var-to-add-var
                        create-var-okp-of-add-var
                        create-var-okp-of-enter-scope
                        create-var-okp-of-add-frame
                        create-var-okp-of-update-var
                        create-var-okp-of-update-object
                        ident-fix-when-identp
                        equal-of-ident-and-ident
                        (:e str-fix)
                        identp-of-ident
                        compustate-frames-number-of-add-var-not-zero
                        compustate-frames-number-of-enter-scope-not-zero
                        compustate-frames-number-of-add-frame-not-zero
                        compustate-frames-number-of-update-var
                        compustate-frames-number-of-update-object
                        compustatep-of-add-var))))
       ((mv item-thm-event &) (evmac-generate-defthm item-thm-name
                                                     :formula item-formula
                                                     :hints item-hints
                                                     :enable nil))
       ((mv new-inscope new-context new-inscope-events thm-index names-to-avoid)
        (atc-gen-vardecl-inscope gin.fn
                                 gin.fn-guard
                                 gin.inscope
                                 gin.context
                                 var
                                 type
                                 (untranslate$ expr-term nil state)
                                 expr-thm
                                 gin.compst-var
                                 gin.prec-tags
                                 thm-index
                                 names-to-avoid
                                 wrld)))
    (mv item
        item-limit
        (append expr-events
                (list initer-thm-event
                      item-thm-event)
                new-inscope-events)
        item-thm-name
        new-inscope
        new-context
        thm-index
        names-to-avoid))
  :guard-hints (("Goal" :in-theory (enable pseudo-termp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-block-item-var-decl ((var symbolp)
                                     (var-info? atc-var-info-optionp)
                                     (val-term pseudo-termp)
                                     (gin stmt-ginp)
                                     state)
  :returns (mv erp
               (item block-itemp)
               (val-term* pseudo-termp :hyp (pseudo-termp val-term))
               (limit pseudo-termp)
               (events pseudo-event-form-listp)
               (thm-name symbolp)
               (new-inscope atc-symbol-varinfo-alist-listp)
               (new-context atc-contextp)
               (thm-index posp)
               (names-to-avoid symbol-listp))
  :short "Generate a C block item statement that consists of
          a variable declaration."
  :long
  (xdoc::topstring
   (xdoc::p
    "The information about the variable,
     retrieved in @(tsee atc-gen-stmt) and passed here,
     must be absent (i.e. @('nil')):
     the declared variable must be new."))
  (b* (((reterr) (irr-block-item) nil nil nil nil nil (irr-atc-context) 1 nil)
       ((stmt-gin gin) gin)
       ((when var-info?)
        (reterr
         (msg "The variable ~x0 in the function ~x1 ~
               is already in scope and cannot be re-declared."
              var gin.fn)))
       ((unless (paident-stringp (symbol-name var)))
        (reterr
         (msg "The symbol name ~s0 of ~
               the LET variable ~x1 of the function ~x2 ~
               must be a portable ASCII C identifier, ~
               but it is not."
              (symbol-name var) var gin.fn)))
       ((erp init.expr
             init.type
             init.term
             & ; init.result
             & ; init.new-compst
             init.limit
             init.events
             init.thm-name
             & ; init.new-inscope
             & ; init.new-context
             init.thm-index
             init.names-to-avoid)
        (atc-gen-expr val-term
                      (change-stmt-gin gin :affect nil)
                      state))
       ((when (or (type-case init.type :pointer)
                  (type-case init.type :array)))
        (reterr
         (msg "When generating C code for the function ~x0, ~
               the term ~x1 of type ~x2 ~
               is being assigned to a new variable ~x3. ~
               This is currently disallowed, ~
               because it would create an alias."
              gin.fn val-term init.type var)))
       ((mv item
            item-limit
            item-events
            item-thm
            inscope-body
            context-body
            thm-index
            names-to-avoid)
        (atc-gen-block-item-declon var
                                   init.type
                                   init.expr
                                   init.term
                                   init.limit
                                   init.events
                                   init.thm-name
                                   (change-stmt-gin
                                    gin
                                    :thm-index init.thm-index
                                    :names-to-avoid init.names-to-avoid
                                    :proofs (and init.thm-name t))
                                   state)))
    (retok item
           init.term
           item-limit
           item-events
           item-thm
           inscope-body
           context-body
           thm-index
           names-to-avoid)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-block-item-asg ((asg exprp)
                                (asg-limit pseudo-termp)
                                (asg-events pseudo-event-form-listp)
                                (asg-thm-name symbolp)
                                (new-compst "An untranslated term.")
                                (gin stmt-ginp)
                                state)
  :returns (mv (item block-itemp)
               (item-limit pseudo-termp)
               (item-events pseudo-event-form-listp
                            :hyp (pseudo-event-form-listp asg-events))
               (item-thm symbolp)
               (thm-index posp :rule-classes (:rewrite :type-prescription))
               (names-to-avoid symbol-listp))
  :short "Generate a C block item that consists of a given assignment."
  :long
  (xdoc::topstring
   (xdoc::p
    "This lifts an assignment to a block item with the assignment.
     It also lifts the theorem about the assignment
     to a theorem about the block item."))
  (b* (((stmt-gin gin) gin)
       (wrld (w state))
       (expr-thm-name (pack gin.fn '-correct- gin.thm-index))
       ((mv expr-thm-name names-to-avoid)
        (fresh-logical-name-with-$s-suffix
         expr-thm-name nil gin.names-to-avoid wrld))
       (thm-index (1+ gin.thm-index))
       (expr-limit `(binary-+ '1 ,asg-limit))
       (expr-formula `(equal (exec-expr-call-or-asg ',asg
                                                    ,gin.compst-var
                                                    ,gin.fenv-var
                                                    ,gin.limit-var)
                             ,new-compst))
       (expr-formula (atc-contextualize expr-formula
                                        gin.context
                                        gin.fn
                                        gin.fn-guard
                                        gin.compst-var
                                        gin.limit-var
                                        expr-limit
                                        t
                                        wrld))
       (expr-hints
        `(("Goal" :in-theory '(exec-expr-call-or-asg-when-asg
                               (:e expr-kind)
                               not-zp-of-limit-variable
                               compustatep-of-add-frame
                               compustatep-of-add-var
                               compustatep-of-enter-scope
                               compustatep-of-update-var
                               compustatep-of-update-object
                               compustatep-of-update-static-var
                               ,asg-thm-name))))
       ((mv expr-event &) (evmac-generate-defthm expr-thm-name
                                                 :formula expr-formula
                                                 :hints expr-hints
                                                 :enable nil))
       (stmt (stmt-expr asg))
       (stmt-thm-name (pack gin.fn '-correct- thm-index))
       ((mv stmt-thm-name names-to-avoid)
        (fresh-logical-name-with-$s-suffix
         stmt-thm-name nil names-to-avoid wrld))
       (thm-index (1+ thm-index))
       (stmt-limit `(binary-+ '1 ,expr-limit))
       (stmt-formula `(equal (exec-stmt ',stmt
                                        ,gin.compst-var
                                        ,gin.fenv-var
                                        ,gin.limit-var)
                             (mv (stmt-value-none) ,new-compst)))
       (stmt-formula (atc-contextualize stmt-formula
                                        gin.context
                                        gin.fn
                                        gin.fn-guard
                                        gin.compst-var
                                        gin.limit-var
                                        stmt-limit
                                        t
                                        wrld))
       (stmt-hints
        `(("Goal" :in-theory '(exec-stmt-when-expr
                               (:e stmt-kind)
                               not-zp-of-limit-variable
                               (:e stmt-expr->get)
                               ,expr-thm-name
                               compustatep-of-update-var
                               compustatep-of-update-object
                               compustatep-of-update-static-var))))
       ((mv stmt-event &) (evmac-generate-defthm stmt-thm-name
                                                 :formula stmt-formula
                                                 :hints stmt-hints
                                                 :enable nil)))
    (atc-gen-block-item-stmt stmt
                             stmt-limit
                             (append asg-events
                                     (list expr-event
                                           stmt-event))
                             stmt-thm-name
                             nil
                             (type-void)
                             '(stmt-value-none)
                             new-compst
                             (change-stmt-gin
                              gin
                              :thm-index thm-index
                              :names-to-avoid names-to-avoid
                              :proofs (and stmt-thm-name t))
                             state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-block-item-var-asg ((var symbolp)
                                    (var-info? atc-var-info-optionp)
                                    (val-term pseudo-termp)
                                    (gin stmt-ginp)
                                    state)
  :returns (mv erp
               (item block-itemp)
               (val-term* pseudo-termp :hyp (pseudo-termp val-term))
               (limit pseudo-termp)
               (events pseudo-event-form-listp)
               (thm-name symbolp)
               (new-inscope atc-symbol-varinfo-alist-listp)
               (new-context atc-contextp)
               (thm-index posp)
               (names-to-avoid symbol-listp))
  :short "Generate a C block item statement that consists of
          an assignment to a variable."
  :long
  (xdoc::topstring
   (xdoc::p
    "We increase the limit by one
     for the theorem about @(tsee exec-expr-asg),
     because that is what it takes, in @(tsee exec-expr-asg),
     to go to @(tsee exec-expr-call-or-pure).")
   (xdoc::p
    "We further increase the limit by one
     for the theorem about @(tsee exec-expr-call-or-asg),
     because that is what it takes, in  @(tsee exec-expr-call-or-asg),
     to go to @(tsee exec-expr-asg).")
   (xdoc::p
    "We further increase the limit by one
     for the theorem about @(tsee exec-stmt),
     because that is what it takes, in @(tsee exec-stmt),
     to go to @(tsee exec-expr-call-or-asg)."))
  (b* (((reterr) (irr-block-item) nil nil nil nil nil (irr-atc-context) 1 nil)
       ((stmt-gin gin) gin)
       (wrld (w state))
       ((unless var-info?)
        (reterr (raise "Internal error: no information for variable ~x0." var)))
       (var-info var-info?)
       (prev-type (atc-var-info->type var-info))
       ((erp rhs.expr
             rhs.type
             rhs.term
             & ; rhs.result
             & ; rhs.new-compst
             rhs.limit
             rhs.events
             rhs.thm-name
             & ; rhs.new-inscope
             & ; rhs.new-context
             rhs.thm-index
             rhs.names-to-avoid)
        (atc-gen-expr val-term
                      (change-stmt-gin gin :affect nil)
                      state))
       ((unless (equal prev-type rhs.type))
        (reterr
         (msg "The type ~x0 of the term ~x1 ~
               assigned to the LET variable ~x2 ~
               of the function ~x3 ~
               differs from the type ~x4 ~
               of a variable with the same symbol in scope."
              rhs.type val-term var gin.fn prev-type)))
       ((when (type-case rhs.type :array))
        (reterr
         (msg "The term ~x0 to which the variable ~x1 is bound ~
               must not have a C array type, ~
               but it has type ~x2 instead."
              val-term var rhs.type)))
       ((when (type-case rhs.type :pointer))
        (reterr
         (msg "The term ~x0 to which the variable ~x1 is bound ~
               must not have a C pointer type, ~
               but it has type ~x2 instead."
              val-term var rhs.type)))
       (asg (make-expr-binary
             :op (binop-asg)
             :arg1 (expr-ident (make-ident :name (symbol-name var)))
             :arg2 rhs.expr))
       (stmt (stmt-expr asg))
       (item (block-item-stmt stmt))
       (asg-limit `(binary-+ '1 ,rhs.limit))
       (expr-limit `(binary-+ '1 ,asg-limit))
       (stmt-limit `(binary-+ '1 ,expr-limit))
       (item-limit `(binary-+ '1 ,stmt-limit))
       ((when (not rhs.thm-name))
        (retok item
               rhs.term
               item-limit
               rhs.events
               nil
               gin.inscope
               gin.context
               rhs.thm-index
               rhs.names-to-avoid))
       (new-compst
        (if (atc-var-info->externalp var-info)
            `(update-static-var (ident ',(symbol-name var))
                                ,rhs.term
                                ,gin.compst-var)
          `(update-var (ident ',(symbol-name var))
                       ,rhs.term
                       ,gin.compst-var)))
       (new-compst (untranslate$ new-compst nil state))
       (asg-thm-name (pack gin.fn '-correct- rhs.thm-index))
       ((mv asg-thm-name names-to-avoid)
        (fresh-logical-name-with-$s-suffix
         asg-thm-name nil rhs.names-to-avoid wrld))
       (thm-index (1+ rhs.thm-index))
       (asg-formula `(equal (exec-expr-asg ',asg
                                           ,gin.compst-var
                                           ,gin.fenv-var
                                           ,gin.limit-var)
                            ,new-compst))
       (asg-formula (atc-contextualize asg-formula
                                       gin.context
                                       gin.fn
                                       gin.fn-guard
                                       gin.compst-var
                                       gin.limit-var
                                       asg-limit
                                       t
                                       wrld))
       (valuep-when-type (atc-type-to-valuep-thm rhs.type gin.prec-tags))
       (type-of-value-when-type
        (atc-type-to-type-of-value-thm rhs.type gin.prec-tags))
       (asg-hints
        `(("Goal"
           :in-theory '(exec-expr-asg-ident-via-object
                        (:e expr-kind)
                        (:e expr-binary->op)
                        (:e expr-binary->arg1)
                        (:e expr-binary->arg2)
                        (:e binop-kind)
                        not-zp-of-limit-variable
                        ,rhs.thm-name
                        mv-nth-of-cons
                        (:e zp)
                        ,valuep-when-type
                        objdesign-of-var-of-const-identifier
                        (:e identp)
                        (:e ident->name)
                        (:e expr-ident->get)
                        ,(atc-var-info->thm var-info)
                        write-object-of-objdesign-of-var-to-write-var
                        write-var-to-update-var
                        compustate-frames-number-of-add-var-not-zero
                        compustate-frames-number-of-enter-scope-not-zero
                        compustate-frames-number-of-add-frame-not-zero
                        compustate-frames-number-of-update-var
                        write-var-okp-of-add-var
                        write-var-okp-of-enter-scope
                        write-var-okp-of-update-var
                        ident-fix-when-identp
                        identp-of-ident
                        equal-of-ident-and-ident
                        (:e str-fix)
                        ,type-of-value-when-type
                        write-var-to-write-static-var
                        var-autop-of-add-frame
                        var-autop-of-enter-scope
                        var-autop-of-add-var
                        var-autop-of-update-var
                        var-autop-of-update-static-var
                        var-autop-of-update-object
                        write-static-var-to-update-static-var
                        write-static-var-okp-of-add-var
                        write-static-var-okp-of-enter-scope
                        write-static-var-okp-of-add-frame
                        write-static-var-okp-when-valuep-of-read-static-var
                        read-object-of-objdesign-static))))
       ((mv asg-event &) (evmac-generate-defthm asg-thm-name
                                                :formula asg-formula
                                                :hints asg-hints
                                                :enable nil))
       ((mv item item-limit item-events item-thm-name thm-index names-to-avoid)
        (atc-gen-block-item-asg asg
                                asg-limit
                                (append rhs.events
                                        (list asg-event))
                                asg-thm-name
                                new-compst
                                (change-stmt-gin
                                 gin
                                 :thm-index thm-index
                                 :names-to-avoid names-to-avoid
                                 :proofs (and asg-thm-name t))
                                state))
       (new-context
        (atc-context-extend
         gin.context
         (list
          (make-atc-premise-cvalue
           :var var
           :term rhs.term)
          (make-atc-premise-compustate
           :var gin.compst-var
           :term (if (atc-var-info->externalp var-info)
                     `(update-static-var (ident ,(symbol-name var))
                                         ,var
                                         ,gin.compst-var)
                   `(update-var (ident ,(symbol-name var))
                                ,var
                                ,gin.compst-var))))))
       (notflexarrmem-thms
        (atc-type-to-notflexarrmem-thms rhs.type gin.prec-tags))
       (new-inscope-rules
        `(,rhs.thm-name
          remove-flexible-array-member-when-absent
          ,@notflexarrmem-thms
          value-fix-when-valuep
          ,valuep-when-type
          objdesign-of-var-of-update-var-iff
          read-object-of-objdesign-of-var-of-update-var
          ident-fix-when-identp
          identp-of-ident
          equal-of-ident-and-ident
          (:e str-fix)
          objdesign-of-var-of-update-static-var-iff
          read-object-of-objdesign-of-var-of-update-static-var-different
          read-object-of-objdesign-of-var-of-update-static-var-same
          var-autop-of-add-frame
          var-autop-of-enter-scope
          var-autop-of-add-var
          var-autop-of-update-var
          var-autop-of-update-static-var
          var-autop-of-update-object))
       ((mv new-inscope new-inscope-events names-to-avoid)
        (atc-gen-new-inscope gin.fn
                             gin.fn-guard
                             gin.inscope
                             new-context
                             gin.compst-var
                             new-inscope-rules
                             gin.prec-tags
                             thm-index
                             names-to-avoid
                             wrld))
       (thm-index (1+ thm-index))
       (events (append item-events
                       new-inscope-events)))
    (retok item
           rhs.term
           item-limit
           events
           item-thm-name
           new-inscope
           new-context
           thm-index
           names-to-avoid))
  :guard-hints
  (("Goal"
    :in-theory
    (enable pseudo-termp
            acl2::true-listp-when-pseudo-event-form-listp-rewrite))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-block-item-array-asg ((var symbolp)
                                      (val-term pseudo-termp)
                                      (sub-term pseudo-termp)
                                      (elem-term pseudo-termp)
                                      (elem-type typep)
                                      (array-write-fn symbolp)
                                      (wrapper? symbolp)
                                      (gin stmt-ginp)
                                      state)
  :returns (mv erp
               (item block-itemp)
               (val-term* pseudo-termp :hyp (symbolp array-write-fn))
               (limit pseudo-termp)
               (events pseudo-event-form-listp)
               (thm-name symbolp)
               (new-inscope atc-symbol-varinfo-alist-listp)
               (new-context atc-contextp)
               (thm-index posp)
               (names-to-avoid symbol-listp))
  :short "Generate a C block item statement that consists of
          an assignment to an array element."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is somewhat analogous to @(tsee atc-gen-block-item-var-asg)."))
  (b* (((reterr) (irr-block-item) nil nil nil nil nil (irr-atc-context) 1 nil)
       ((stmt-gin gin) gin)
       (wrld (w state))
       ((unless (eq wrapper? nil))
        (reterr
         (msg "The array write term ~x0 to which ~x1 is bound ~
               has the ~x2 wrapper, which is disallowed."
              val-term var wrapper?)))
       ((unless (member-eq var gin.affect))
        (reterr
         (msg "The array ~x0 is being written to, ~
               but it is not among the variables ~x1 ~
               currently affected."
              var gin.affect)))
       ((erp (expr-gout arr))
        (atc-gen-expr-pure var
                           (make-expr-gin
                            :context gin.context
                            :inscope gin.inscope
                            :prec-tags gin.prec-tags
                            :fn gin.fn
                            :fn-guard gin.fn-guard
                            :compst-var gin.compst-var
                            :thm-index gin.thm-index
                            :names-to-avoid gin.names-to-avoid
                            :proofs gin.proofs)
                           state))
       ((erp (expr-gout sub))
        (atc-gen-expr-pure sub-term
                           (make-expr-gin
                            :context gin.context
                            :inscope gin.inscope
                            :prec-tags gin.prec-tags
                            :fn gin.fn
                            :fn-guard gin.fn-guard
                            :compst-var gin.compst-var
                            :thm-index arr.thm-index
                            :names-to-avoid arr.names-to-avoid
                            :proofs (and arr.thm-name t))
                           state))
       ((erp (expr-gout elem))
        (atc-gen-expr-pure elem-term
                           (make-expr-gin
                            :context gin.context
                            :inscope gin.inscope
                            :prec-tags gin.prec-tags
                            :fn gin.fn
                            :fn-guard gin.fn-guard
                            :compst-var gin.compst-var
                            :thm-index sub.thm-index
                            :names-to-avoid sub.names-to-avoid
                            :proofs (and sub.thm-name t))
                           state))
       ((unless (and (type-case arr.type :array)
                     (equal (type-array->of arr.type)
                            elem-type)))
        (reterr
         (msg "The array ~x0 of type ~x1 ~
               does not have the expected array type of ~x2. ~
               This is indicative of ~
               unreachable code under the guards, ~
               given that the code is guard-verified."
              var arr.type elem-type)))
       ((unless (type-integerp sub.type))
        (reterr
         (msg "The array ~x0 of type ~x1 ~
               is being indexed with ~
               a subscript ~x2 of non-integer type ~x3, ~
               instead of integer type as expected.
               This is indicative of ~
               unreachable code under the guards, ~
               given that the code is guard-verified."
              var arr.type sub-term sub.type)))
       ((unless (equal elem.type elem-type))
        (reterr
         (msg "The array ~x0 of type ~x1 ~
               is being written to with ~
               an element ~x2 of type x3, ~
               instead of type ~x4 as expected.
               This is indicative of ~
               unreachable code under the guards, ~
               given that the code is guard-verified."
              var arr.type elem-term elem.type elem-type)))
       (asg (make-expr-binary
             :op (binop-asg)
             :arg1 (make-expr-arrsub :arr arr.expr
                                     :sub sub.expr)
             :arg2 elem.expr))
       (stmt (stmt-expr asg))
       (item (block-item-stmt stmt))
       (asg-limit ''1)
       (expr-limit `(binary-+ '1 ,asg-limit))
       (stmt-limit `(binary-+ '1 ,expr-limit))
       (item-limit `(binary-+ '1 ,stmt-limit))
       (varinfo (atc-get-var var gin.inscope))
       ((unless varinfo)
        (reterr (raise "Internal error: no information for variable ~x0." var)))
       ((when (eq array-write-fn 'quote))
        (reterr (raise "Internal error: array writer is QUOTE.")))
       (array-write-term `(,array-write-fn ,var ,sub.term ,elem.term))
       ((when (not elem.thm-name))
        (retok item
               array-write-term
               item-limit
               (append arr.events sub.events elem.events)
               nil
               gin.inscope
               gin.context
               elem.thm-index
               elem.names-to-avoid))
       (okp-lemma-name (pack gin.fn '-asg- elem.thm-index '-okp-lemma))
       ((mv okp-lemma-name names-to-avoid)
        (fresh-logical-name-with-$s-suffix okp-lemma-name
                                           nil
                                           elem.names-to-avoid
                                           wrld))
       (thm-index (1+ elem.thm-index))
       (elem-fixtype (pack (type-kind elem-type)))
       (index-okp (pack elem-fixtype '-array-index-okp))
       (okp-lemma-formula `(,index-okp ,var ,sub.term))
       (okp-lemma-formula (atc-contextualize okp-lemma-formula
                                             gin.context
                                             gin.fn
                                             gin.fn-guard
                                             nil
                                             nil
                                             nil
                                             nil
                                             wrld))
       (okp-lemma-hints
        `(("Goal"
           :in-theory '(,gin.fn-guard if* test* declar assign)
           :use (:guard-theorem ,gin.fn))))
       ((mv okp-lemma-event &)
        (evmac-generate-defthm okp-lemma-name
                               :formula okp-lemma-formula
                               :hints okp-lemma-hints
                               :enable nil))
       (new-compst
        (if (atc-var-info->externalp varinfo)
            `(update-static-var (ident ',(symbol-name var))
                                ,array-write-term
                                ,gin.compst-var)
          `(update-object ,(add-suffix-to-fn var "-OBJDES")
                          ,array-write-term
                          ,gin.compst-var)))
       (new-compst (untranslate$ new-compst nil state))
       (asg-thm-name (pack gin.fn '-correct- thm-index))
       ((mv asg-thm-name names-to-avoid)
        (fresh-logical-name-with-$s-suffix asg-thm-name nil names-to-avoid wrld))
       (thm-index (1+ thm-index))
       (asg-formula `(equal (exec-expr-asg ',asg
                                           ,gin.compst-var
                                           ,gin.fenv-var
                                           ,gin.limit-var)
                            ,new-compst))
       (asg-formula (atc-contextualize asg-formula
                                       gin.context
                                       gin.fn
                                       gin.fn-guard
                                       gin.compst-var
                                       gin.limit-var
                                       asg-limit
                                       t
                                       wrld))
       (exec-expr-asg-arrsub-when-elem-fixtype-arrayp-for-modular-proofs
        (pack 'exec-expr-asg-arrsub-when-
              elem-fixtype
              '-arrayp-for-modular-proofs))
       (value-kind-when-sub-type-pred
        (atc-type-to-value-kind-thm sub.type gin.prec-tags))
       (value-kind-when-elem-type-pred
        (atc-type-to-value-kind-thm elem-type gin.prec-tags))
       (valuep-when-sub-type-pred
        (atc-type-to-valuep-thm sub.type gin.prec-tags))
       (valuep-when-elem-type-pred
        (atc-type-to-valuep-thm elem-type gin.prec-tags))
       (valuep-when-arr-type-pred
        (atc-type-to-valuep-thm arr.type gin.prec-tags))
       (sub-type-pred (atc-type-to-recognizer sub.type gin.prec-tags))
       (cintegerp-when-sub-type-pred (pack 'cintegerp-when- sub-type-pred))
       (elem-fixtype-arrayp-of-elem-fixtype-array-write
        (pack elem-fixtype '-arrayp-of- elem-fixtype '-array-write))
       (elem-fixtype-array-length-of-elem-fixtype-array-write
        (pack elem-fixtype '-array-length-of- elem-fixtype '-array-write))
       (type-of-value-when-elem-fixtype-arrayp
        (atc-type-to-type-of-value-thm arr.type gin.prec-tags))
       (value-array->length-when-elem-fixtype-arrayp
        (pack 'value-array->length-when- elem-fixtype '-arrayp))
       (apconvert-expr-value-when-elem-fixtype-arrayp
        (pack 'apconvert-expr-value-when- elem-fixtype '-arrayp))
       (return-type-of-type-elem-fixtype
        (pack 'return-type-of-type- elem-fixtype))
       (asg-hints
        `(("Goal"
           :in-theory
           '(,exec-expr-asg-arrsub-when-elem-fixtype-arrayp-for-modular-proofs
             (:e expr-kind)
             (:e expr-binary->op)
             (:e expr-binary->arg1)
             (:e expr-binary->arg2)
             (:e expr-arrsub->arr)
             (:e expr-arrsub->sub)
             (:e expr-ident->get)
             (:e binop-kind)
             not-zp-of-limit-variable
             ,arr.thm-name
             expr-valuep-of-expr-value
             apconvert-expr-value-when-not-value-array
             expr-value->value-of-expr-value
             value-fix-when-valuep
             ,(atc-var-info->thm varinfo)
             ,sub.thm-name
             ,value-kind-when-sub-type-pred
             ,valuep-when-sub-type-pred
             ,cintegerp-when-sub-type-pred
             ,okp-lemma-name
             ,elem.thm-name
             ,value-kind-when-elem-type-pred
             ,valuep-when-elem-type-pred
             write-object-to-update-object
             write-object-okp-when-valuep-of-read-object-no-syntaxp
             ,valuep-when-arr-type-pred
             ,elem-fixtype-arrayp-of-elem-fixtype-array-write
             ,type-of-value-when-elem-fixtype-arrayp
             ,value-array->length-when-elem-fixtype-arrayp
             ,elem-fixtype-array-length-of-elem-fixtype-array-write
             ,apconvert-expr-value-when-elem-fixtype-arrayp
             objdesign-optionp-of-objdesign-of-var
             objdesignp-when-objdesign-optionp
             return-type-of-value-pointer
             value-pointer-validp-of-value-pointer
             return-type-of-pointer-valid
             value-pointer->reftype-of-value-pointer
             type-fix-when-typep
             ,return-type-of-type-elem-fixtype
             value-pointer->designator-of-value-pointer
             pointer-valid->get-of-pointer-valid
             objdesign-fix-when-objdesignp
             write-object-of-objdesign-of-var-to-write-var
             write-var-to-write-static-var
             var-autop-of-add-frame
             var-autop-of-enter-scope
             var-autop-of-add-var
             var-autop-of-update-var
             var-autop-of-update-static-var
             var-autop-of-update-object
             write-static-var-to-update-static-var
             write-static-var-okp-of-add-var
             write-static-var-okp-of-enter-scope
             write-static-var-okp-of-add-frame
             write-static-var-okp-when-valuep-of-read-static-var
             read-object-of-objdesign-static
             ident-fix-when-identp
             identp-of-ident
             equal-of-ident-and-ident
             (:e str-fix)))))
       ((mv asg-event &) (evmac-generate-defthm asg-thm-name
                                                :formula asg-formula
                                                :hints asg-hints
                                                :enable nil))
       ((mv item
            item-limit
            item-events
            item-thm-name
            thm-index
            names-to-avoid)
        (atc-gen-block-item-asg asg
                                asg-limit
                                (append arr.events
                                        sub.events
                                        elem.events
                                        (list okp-lemma-event
                                              asg-event))
                                asg-thm-name
                                new-compst
                                (change-stmt-gin
                                 gin
                                 :thm-index thm-index
                                 :names-to-avoid names-to-avoid
                                 :proofs (and asg-thm-name t))
                                state))
       (new-context
        (atc-context-extend
         gin.context
         (list
          (make-atc-premise-cvalue
           :var var
           :term array-write-term)
          (make-atc-premise-compustate
           :var gin.compst-var
           :term (if (atc-var-info->externalp varinfo)
                     `(update-static-var (ident ,(symbol-name var))
                                         ,var
                                         ,gin.compst-var)
                   `(update-object ,(add-suffix-to-fn var "-OBJDES")
                                   ,var
                                   ,gin.compst-var))))))
       (new-inscope-rules
        `(objdesign-of-var-of-update-object
          objdesign-of-var-of-enter-scope-iff
          objdesign-of-var-of-add-var-iff
          read-object-auto/static-of-update-object-alloc
          read-object-of-update-object-same
          read-object-of-update-object-disjoint
          read-object-of-objdesign-of-var-of-add-var
          read-object-of-objdesign-of-var-of-enter-scope
          objdesign-kind-of-objdesign-of-var
          compustate-frames-number-of-add-var-not-zero
          compustate-frames-number-of-enter-scope-not-zero
          object-disjointp-commutative
          value-fix-when-valuep
          remove-flexible-array-member-when-absent
          not-flexible-array-member-p-when-ucharp
          not-flexible-array-member-p-when-scharp
          not-flexible-array-member-p-when-ushortp
          not-flexible-array-member-p-when-sshortp
          not-flexible-array-member-p-when-uintp
          not-flexible-array-member-p-when-sintp
          not-flexible-array-member-p-when-ulongp
          not-flexible-array-member-p-when-slongp
          not-flexible-array-member-p-when-ullongp
          not-flexible-array-member-p-when-sllongp
          not-flexible-array-member-p-when-uchar-arrayp
          not-flexible-array-member-p-when-schar-arrayp
          not-flexible-array-member-p-when-ushort-arrayp
          not-flexible-array-member-p-when-sshort-arrayp
          not-flexible-array-member-p-when-uint-arrayp
          not-flexible-array-member-p-when-sint-arrayp
          not-flexible-array-member-p-when-ulong-arrayp
          not-flexible-array-member-p-when-slong-arrayp
          not-flexible-array-member-p-when-ullong-arrayp
          not-flexible-array-member-p-when-sllong-arrayp
          not-flexible-array-member-p-when-value-pointer
          valuep-when-ucharp
          valuep-when-scharp
          valuep-when-ushortp
          valuep-when-sshortp
          valuep-when-uintp
          valuep-when-sintp
          valuep-when-ulongp
          valuep-when-slongp
          valuep-when-ullongp
          valuep-when-sllongp
          ,valuep-when-arr-type-pred
          ,elem-fixtype-arrayp-of-elem-fixtype-array-write
          ident-fix-when-identp
          identp-of-ident
          equal-of-ident-and-ident
          (:e str-fix)
          objdesign-of-var-of-update-static-var-iff
          read-object-of-objdesign-of-var-of-update-static-var-different
          read-object-of-objdesign-of-var-of-update-static-var-same
          var-autop-of-add-frame
          var-autop-of-enter-scope
          var-autop-of-add-var
          var-autop-of-update-var
          var-autop-of-update-static-var
          var-autop-of-update-object))
       ((mv new-inscope new-inscope-events names-to-avoid)
        (atc-gen-new-inscope gin.fn
                             gin.fn-guard
                             gin.inscope
                             new-context
                             gin.compst-var
                             new-inscope-rules
                             gin.prec-tags
                             thm-index
                             names-to-avoid
                             wrld))
       (thm-index (1+ thm-index))
       (events (append item-events
                       new-inscope-events)))
    (retok item
           array-write-term
           item-limit
           events
           item-thm-name
           new-inscope
           new-context
           thm-index
           names-to-avoid))
  :guard-hints
  (("Goal"
    :in-theory
    (e/d (pseudo-termp
          acl2::true-listp-when-pseudo-event-form-listp-rewrite)
         ((:e tau-system))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-block-item-struct-scalar-asg ((var symbolp)
                                              (val-term pseudo-termp)
                                              (tag identp)
                                              (member-name identp)
                                              (member-term pseudo-termp)
                                              (member-type typep)
                                              (struct-write-fn symbolp)
                                              (wrapper? symbolp)
                                              (gin stmt-ginp)
                                              state)
  :returns (mv erp
               (item block-itemp)
               (val-term* pseudo-termp :hyp (and (symbolp struct-write-fn)
                                                 (pseudo-termp member-term)
                                                 (symbolp var)))
               (limit pseudo-termp)
               (events pseudo-event-form-listp)
               (thm-name symbolp)
               (new-inscope atc-symbol-varinfo-alist-listp)
               (new-context atc-contextp)
               (thm-index posp)
               (names-to-avoid symbol-listp))
  :short "Generate a C block item statement that consists of
          an assignment to a scalar member of a structure."
  (b* (((reterr) (irr-block-item) nil nil nil nil nil (irr-atc-context) 1 nil)
       (wrld (w state))
       ((stmt-gin gin) gin)
       ((unless (eq wrapper? nil))
        (reterr
         (msg "The structure write term ~x0 ~
               to which ~x1 is bound ~
               has the ~x2 wrapper, which is disallowed."
              val-term var wrapper?)))
       ((erp (expr-gout struct))
        (atc-gen-expr-pure var
                           (make-expr-gin
                            :context gin.context
                            :inscope gin.inscope
                            :prec-tags gin.prec-tags
                            :fn gin.fn
                            :fn-guard gin.fn-guard
                            :compst-var gin.compst-var
                            :thm-index gin.thm-index
                            :names-to-avoid gin.names-to-avoid
                            :proofs gin.proofs)
                           state))
       ((unless (member-equal struct.type
                              (list (type-struct tag)
                                    (type-pointer (type-struct tag)))))
        (reterr
         (msg "The structure ~x0 of type ~x1 ~
               does not have the expected type ~x2 or ~x3. ~
               This is indicative of ~
               unreachable code under the guards, ~
               given that the code is guard-verified."
              var
              struct.type
              (type-struct tag)
              (type-pointer (type-struct tag)))))
       (pointerp (type-case struct.type :pointer))
       ((when (and pointerp
                   (not (member-eq var gin.affect))))
        (reterr
         (msg "The structure ~x0 ~
               is being written to by pointer, ~
               but it is not among the variables ~x1 ~
               currently affected."
              var gin.affect)))
       ((erp (expr-gout member))
        (atc-gen-expr-pure member-term
                           (make-expr-gin
                            :context gin.context
                            :inscope gin.inscope
                            :prec-tags gin.prec-tags
                            :fn gin.fn
                            :fn-guard gin.fn-guard
                            :compst-var gin.compst-var
                            :thm-index struct.thm-index
                            :names-to-avoid struct.names-to-avoid
                            :proofs (and struct.thm-name t))
                           state))
       ((unless (equal member.type member-type))
        (reterr
         (msg "The structure ~x0 of type ~x1 ~
               is being written to with ~
               a member ~x2 of type ~x3, ~
               instead of type ~x4 as expected. ~
               This is indicative of ~
               unreachable code under the guards, ~
               given that the code is guard-verified."
              var struct.type member-term
              member.type member-type)))
       (asg-mem (if pointerp
                    (make-expr-memberp :target struct.expr
                                       :name member-name)
                  (make-expr-member :target struct.expr
                                    :name member-name)))
       (asg (make-expr-binary :op (binop-asg)
                              :arg1 asg-mem
                              :arg2 member.expr))
       (stmt (stmt-expr asg))
       (item (block-item-stmt stmt))
       (asg-limit ''1)
       (expr-limit `(binary-+ '1 ,asg-limit))
       (stmt-limit `(binary-+ '1 ,expr-limit))
       (item-limit `(binary-+ '1 ,stmt-limit))
       ((when (eq struct-write-fn 'quote))
        (reterr (raise "Internal error: structure writer is QUOTE.")))
       (struct-write-term `(,struct-write-fn ,member.term ,var))
       (varinfo (atc-get-var var gin.inscope))
       ((unless varinfo)
        (reterr (raise "Internal error: no information for variable ~x0." var)))
       ((when (not member.thm-name))
        (retok item
               struct-write-term
               item-limit
               (append struct.events member.events)
               nil
               gin.inscope
               gin.context
               member.thm-index
               member.names-to-avoid))
       (new-compst (if pointerp
                       `(update-object ,(add-suffix-to-fn var "-OBJDES")
                                       ,struct-write-term
                                       ,gin.compst-var)
                     `(update-var (ident ',(symbol-name var))
                                  ,struct-write-term
                                  ,gin.compst-var)))
       (new-compst (untranslate$ new-compst nil state))
       (asg-thm-name (pack gin.fn '-correct- member.thm-index))
       ((mv asg-thm-name names-to-avoid)
        (fresh-logical-name-with-$s-suffix asg-thm-name
                                           nil
                                           member.names-to-avoid
                                           wrld))
       (thm-index (1+ member.thm-index))
       (asg-formula `(equal (exec-expr-asg ',asg
                                           ,gin.compst-var
                                           ,gin.fenv-var
                                           ,gin.limit-var)
                            ,new-compst))
       (asg-formula (atc-contextualize asg-formula
                                       gin.context
                                       gin.fn
                                       gin.fn-guard
                                       gin.compst-var
                                       gin.limit-var
                                       asg-limit
                                       t
                                       wrld))
       (exec-expr-asg-thms
        (atc-string-taginfo-alist-to-member-write-thms gin.prec-tags))
       (type-of-value-thms
        (atc-string-taginfo-alist-to-type-of-value-thms gin.prec-tags))
       (writer-return-thms
        (atc-string-taginfo-alist-to-writer-return-thms gin.prec-tags))
       (valuep-when-member-type-pred
        (atc-type-to-valuep-thm member-type gin.prec-tags))
       (valuep-thms (atc-string-taginfo-alist-to-valuep-thms gin.prec-tags))
       (asg-hints
        (if pointerp
            `(("Goal"
               :in-theory
               '(,@exec-expr-asg-thms
                 (:e expr-kind)
                 (:e expr-binary->op)
                 (:e expr-binary->arg1)
                 (:e expr-binary->arg2)
                 (:e expr-memberp->target)
                 (:e expr-memberp->name)
                 (:e expr-ident->get)
                 (:e binop-kind)
                 equal-of-const-and-ident
                 (:e identp)
                 (:e ident->name)
                 (:e str-fix)
                 not-zp-of-limit-variable
                 read-var-to-read-object-of-objdesign-of-var
                 ,(atc-var-info->thm varinfo)
                 objdesign-of-var-of-const-identifier
                 ,member.thm-name
                 expr-valuep-of-expr-value
                 expr-value->value-of-expr-value
                 value-fix-when-valuep
                 ,valuep-when-member-type-pred
                 write-object-to-update-object
                 write-object-okp-of-enter-scope
                 write-object-okp-of-add-var
                 write-object-okp-of-add-frame
                 write-object-okp-when-valuep-of-read-object-no-syntaxp
                 ,@valuep-thms
                 ,@type-of-value-thms
                 ,@writer-return-thms)))
          `(("Goal"
             :in-theory
             '(,@exec-expr-asg-thms
               (:e expr-kind)
               (:e expr-binary->op)
               (:e expr-binary->arg1)
               (:e expr-binary->arg2)
               (:e expr-member->target)
               (:e expr-member->name)
               (:e expr-ident->get)
               (:e binop-kind)
               equal-of-const-and-ident
               (:e identp)
               (:e ident->name)
               (:e str-fix)
               not-zp-of-limit-variable
               read-var-to-read-object-of-objdesign-of-var
               ,(atc-var-info->thm varinfo)
               objdesign-of-var-of-const-identifier
               ,member.thm-name
               expr-valuep-of-expr-value
               expr-value->value-of-expr-value
               value-fix-when-valuep
               ,valuep-when-member-type-pred
               write-var-of-const-identifier
               write-var-to-update-var
               compustate-frames-number-of-enter-scope-not-zero
               compustate-frames-number-of-add-var-not-zero
               write-var-okp-of-enter-scope
               write-var-okp-of-add-var
               ,@type-of-value-thms
               ,@writer-return-thms
               ident-fix-when-identp
               identp-of-ident
               equal-of-ident-and-ident
               compustate-frames-number-of-update-var
               write-var-okp-of-update-var)))))
       ((mv asg-event &) (evmac-generate-defthm asg-thm-name
                                                :formula asg-formula
                                                :hints asg-hints
                                                :enable nil))
       ((mv item
            item-limit
            item-events
            item-thm-name
            thm-index
            names-to-avoid)
        (atc-gen-block-item-asg asg
                                asg-limit
                                (append struct.events
                                        member.events
                                        (list asg-event))
                                asg-thm-name
                                new-compst
                                (change-stmt-gin
                                 gin
                                 :thm-index thm-index
                                 :names-to-avoid names-to-avoid
                                 :proofs t)
                                state))
       (new-context
        (atc-context-extend gin.context
                            (list
                             (make-atc-premise-cvalue
                              :var var
                              :term struct-write-term)
                             (make-atc-premise-compustate
                              :var gin.compst-var
                              :term (if pointerp
                                        `(update-object
                                          ,(add-suffix-to-fn var "-OBJDES")
                                          ,var
                                          ,gin.compst-var)
                                      `(update-var
                                        (ident ,(symbol-name var))
                                        ,var
                                        ,gin.compst-var))))))
       (notflexarrmem-thms (atc-type-to-notflexarrmem-thms (type-struct tag)
                                                           gin.prec-tags))
       (value-kind-thms
        (atc-string-taginfo-alist-to-value-kind-thms gin.prec-tags))
       (new-inscope-rules
        (if pointerp
            `(objdesign-of-var-of-update-object-iff
              read-object-of-objdesign-of-var-to-read-var
              read-object-of-update-object-same
              read-object-of-update-object-disjoint
              read-var-of-update-object
              compustate-frames-number-of-enter-scope-not-zero
              read-var-of-enter-scope
              compustate-frames-number-of-add-var-not-zero
              compustate-frames-number-of-update-object
              read-var-of-add-var
              not-flexible-array-member-p-when-ucharp
              not-flexible-array-member-p-when-scharp
              not-flexible-array-member-p-when-ushortp
              not-flexible-array-member-p-when-sshortp
              not-flexible-array-member-p-when-uintp
              not-flexible-array-member-p-when-sintp
              not-flexible-array-member-p-when-ulongp
              not-flexible-array-member-p-when-slongp
              not-flexible-array-member-p-when-ullongp
              not-flexible-array-member-p-when-sllongp
              not-flexible-array-member-p-when-value-pointer
              read-object-of-update-object-same
              remove-flexible-array-member-when-absent
              value-fix-when-valuep
              valuep-when-ucharp
              valuep-when-scharp
              valuep-when-ushortp
              valuep-when-sshortp
              valuep-when-uintp
              valuep-when-sintp
              valuep-when-ulongp
              valuep-when-slongp
              valuep-when-ullongp
              valuep-when-sllongp
              ,@valuep-thms
              ,@writer-return-thms
              equal-of-ident-and-ident
              (:e str-fix)
              ident-fix-when-identp
              identp-of-ident)
          `(objdesign-of-var-of-update-var-iff
            read-object-of-objdesign-of-var-of-update-var
            remove-flexible-array-member-when-absent
            ,@notflexarrmem-thms
            ,@value-kind-thms
            value-fix-when-valuep
            ,@valuep-thms
            ,@writer-return-thms
            equal-of-ident-and-ident
            (:e str-fix)
            ident-fix-when-identp
            identp-of-ident)))
       ((mv new-inscope new-inscope-events names-to-avoid)
        (atc-gen-new-inscope gin.fn
                             gin.fn-guard
                             gin.inscope
                             new-context
                             gin.compst-var
                             new-inscope-rules
                             gin.prec-tags
                             thm-index
                             names-to-avoid
                             wrld))
       (thm-index (1+ thm-index))
       (events (append item-events
                       new-inscope-events)))
    (retok item
           struct-write-term
           item-limit
           events
           item-thm-name
           new-inscope
           new-context
           thm-index
           names-to-avoid))
  :guard-hints
  (("Goal"
    :in-theory
    (e/d (pseudo-termp
          acl2::true-listp-when-pseudo-event-form-listp-rewrite)
         ((:e tau-system))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-block-item-struct-array-asg ((var symbolp)
                                             (val-term pseudo-termp)
                                             (tag identp)
                                             (member-name identp)
                                             (index-term pseudo-termp)
                                             (elem-term pseudo-termp)
                                             (elem-type typep)
                                             (flexiblep booleanp)
                                             (struct-write-fn symbolp)
                                             (wrapper? symbolp)
                                             (gin stmt-ginp)
                                             state)
  :returns (mv erp
               (item block-itemp)
               (val-term* pseudo-termp :hyp (and (symbolp struct-write-fn)
                                                 (pseudo-termp index-term)
                                                 (pseudo-termp elem-term)
                                                 (symbolp var)))
               (limit pseudo-termp)
               (events pseudo-event-form-listp)
               (thm-name symbolp)
               (new-inscope atc-symbol-varinfo-alist-listp)
               (new-context atc-contextp)
               (thm-index posp)
               (names-to-avoid symbol-listp))
  :short "Generate a C block item statement that consists of
          an assignment to an element of an array member of a structure."
  (b* (((reterr) (irr-block-item) nil nil nil nil nil (irr-atc-context) 1 nil)
       ((stmt-gin gin) gin)
       (wrld (w state))
       ((unless (eq wrapper? nil))
        (reterr
         (msg "The structure write term ~x0 ~
               to which ~x1 is bound ~
               has the ~x2 wrapper, which is disallowed."
              val-term var wrapper?)))
       ((erp (expr-gout struct))
        (atc-gen-expr-pure var
                           (make-expr-gin
                            :context gin.context
                            :inscope gin.inscope
                            :prec-tags gin.prec-tags
                            :fn gin.fn
                            :fn-guard gin.fn-guard
                            :compst-var gin.compst-var
                            :thm-index gin.thm-index
                            :names-to-avoid gin.names-to-avoid
                            :proofs gin.proofs)
                           state))
       ((unless (member-equal struct.type
                              (list (type-struct tag)
                                    (type-pointer (type-struct tag)))))
        (reterr
         (msg "The structure ~x0 of type ~x1 ~
               does not have the expected type ~x2 or ~x3. ~
               This is indicative of ~
               unreachable code under the guards, ~
               given that the code is guard-verified."
              var
              struct.type
              (type-struct tag)
              (type-pointer (type-struct tag)))))
       (pointerp (type-case struct.type :pointer))
       ((when (and pointerp
                   (not (member-eq var gin.affect))))
        (reterr
         (msg "The structure ~x0 ~
               is being written to by pointer, ~
               but it is not among the variables ~x1 ~
               currently affected."
              var gin.affect)))
       ((erp (expr-gout index))
        (atc-gen-expr-pure index-term
                           (make-expr-gin
                            :context gin.context
                            :inscope gin.inscope
                            :prec-tags gin.prec-tags
                            :fn gin.fn
                            :fn-guard gin.fn-guard
                            :compst-var gin.compst-var
                            :thm-index struct.thm-index
                            :names-to-avoid struct.names-to-avoid
                            :proofs (and struct.thm-name t))
                           state))
       ((unless (type-integerp index.type))
        (reterr
         (msg "The structure ~x0 of type ~x1 ~
               is being written to with ~
               an index ~x2 of type ~x3, ~
               instead of a C integer type as expected. ~
               This is indicative of ~
               unreachable code under the guards, ~
               given that the code is guard-verified."
              var struct.type index-term index.type)))
       ((erp (expr-gout elem))
        (atc-gen-expr-pure elem-term
                           (make-expr-gin
                            :context gin.context
                            :inscope gin.inscope
                            :prec-tags gin.prec-tags
                            :fn gin.fn
                            :fn-guard gin.fn-guard
                            :compst-var gin.compst-var
                            :thm-index index.thm-index
                            :names-to-avoid index.names-to-avoid
                            :proofs (and index.thm-name t))
                           state))
       ((unless (equal elem.type elem-type))
        (reterr
         (msg "The structure ~x0 of type ~x1 ~
               is being written to with ~
               a member array element ~x2 of type ~x3, ~
               instead of type ~x4 as expected.
               This is indicative of ~
               unreachable code under the guards, ~
               given that the code is guard-verified."
              var struct.type elem-term elem.type elem-type)))
       (asg-mem (if pointerp
                    (make-expr-memberp :target struct.expr
                                       :name member-name)
                  (make-expr-member :target struct.expr
                                    :name member-name)))
       (asg (make-expr-binary
             :op (binop-asg)
             :arg1 (make-expr-arrsub :arr asg-mem
                                     :sub index.expr)
             :arg2 elem.expr))
       (stmt (stmt-expr asg))
       (item (block-item-stmt stmt))
       (asg-limit ''1)
       (expr-limit `(binary-+ '1 ,asg-limit))
       (stmt-limit `(binary-+ '1 ,expr-limit))
       (item-limit `(binary-+ '1 ,stmt-limit))
       ((when (eq struct-write-fn 'quote))
        (reterr (raise "Internal error: structure writer is QUOTE.")))
       (struct-write-term `(,struct-write-fn ,index.term ,elem.term ,var))
       (varinfo (atc-get-var var gin.inscope))
       ((unless varinfo)
        (reterr (raise "Internal error: no information for variable ~x0." var)))
       ((when (not elem.thm-name))
        (retok item
               struct-write-term
               item-limit
               (append struct.events index.events elem.events)
               nil
               gin.inscope
               gin.context
               elem.thm-index
               elem.names-to-avoid))
       (okp-lemma-name (pack gin.fn '-asg- elem.thm-index '-okp-lemma))
       ((mv okp-lemma-name names-to-avoid)
        (fresh-logical-name-with-$s-suffix okp-lemma-name
                                           nil
                                           elem.names-to-avoid
                                           wrld))
       (thm-index (1+ elem.thm-index))
       (info (atc-get-tag-info tag gin.prec-tags))
       (struct-tag (defstruct-info->fixtype (atc-tag-info->defstruct info)))
       (index-okp (packn-pos (list struct-tag
                                   '-
                                   (ident->name member-name)
                                   '-index-okp)
                             struct-write-fn))
       (okp-lemma-formula
        (if flexiblep
            `(,index-okp ,index-term ,var)
          `(,index-okp ,index-term)))
       (okp-lemma-formula (atc-contextualize okp-lemma-formula
                                             gin.context
                                             gin.fn
                                             gin.fn-guard
                                             nil
                                             nil
                                             nil
                                             nil
                                             wrld))
       (okp-lemma-hints
        `(("Goal"
           :in-theory '(,gin.fn-guard if* test* declar assign)
           :use (:guard-theorem ,gin.fn))))
       ((mv okp-lemma-event &)
        (evmac-generate-defthm okp-lemma-name
                               :formula okp-lemma-formula
                               :hints okp-lemma-hints
                               :enable nil))
       (new-compst (if pointerp
                       `(update-object ,(add-suffix-to-fn var "-OBJDES")
                                       ,struct-write-term
                                       ,gin.compst-var)
                     `(update-var (ident ',(symbol-name var))
                                  ,struct-write-term
                                  ,gin.compst-var)))
       (new-compst (untranslate$ new-compst nil state))
       (asg-thm-name (pack gin.fn '-correct- thm-index))
       ((mv asg-thm-name names-to-avoid)
        (fresh-logical-name-with-$s-suffix
         asg-thm-name nil names-to-avoid wrld))
       (thm-index (1+ thm-index))
       (asg-formula `(equal (exec-expr-asg ',asg
                                           ,gin.compst-var
                                           ,gin.fenv-var
                                           ,gin.limit-var)
                            ,new-compst))
       (asg-formula (atc-contextualize asg-formula
                                       gin.context
                                       gin.fn
                                       gin.fn-guard
                                       gin.compst-var
                                       gin.limit-var
                                       asg-limit
                                       t
                                       wrld))
       (exec-expr-asg-thms
        (atc-string-taginfo-alist-to-member-write-thms gin.prec-tags))
       (valuep-when-elem-type-pred
        (atc-type-to-valuep-thm elem.type gin.prec-tags))
       (valuep-when-index-type-pred
        (atc-type-to-valuep-thm index.type gin.prec-tags))
       (value-kind-when-elem-type-pred
        (atc-type-to-value-kind-thm elem.type gin.prec-tags))
       (value-kind-when-index-type-pred
        (atc-type-to-value-kind-thm index.type gin.prec-tags))
       (index-type-pred (atc-type-to-recognizer index.type gin.prec-tags))
       (cintegerp-when-index-type-pred (pack 'cintegerp-when- index-type-pred))
       (valuep-thms (atc-string-taginfo-alist-to-valuep-thms gin.prec-tags))
       (type-of-value-thms
        (atc-string-taginfo-alist-to-type-of-value-thms gin.prec-tags))
       (writer-return-thms
        (atc-string-taginfo-alist-to-writer-return-thms gin.prec-tags))
       (asg-hints
        (if pointerp
            `(("Goal"
               :in-theory
               '(,@exec-expr-asg-thms
                 (:e expr-kind)
                 (:e expr-binary->op)
                 (:e expr-binary->arg1)
                 (:e expr-binary->arg2)
                 (:e expr-arrsub->arr)
                 (:e expr-arrsub->sub)
                 (:e expr-memberp->target)
                 (:e expr-memberp->name)
                 (:e expr-ident->get)
                 (:e binop-kind)
                 equal-of-const-and-ident
                 (:e identp)
                 (:e ident->name)
                 (:e str-fix)
                 not-zp-of-limit-variable
                 read-var-to-read-object-of-objdesign-of-var
                 ,(atc-var-info->thm varinfo)
                 objdesign-of-var-of-const-identifier
                 ,index.thm-name
                 ,elem.thm-name
                 expr-valuep-of-expr-value
                 apconvert-expr-value-when-not-value-array
                 ,valuep-when-elem-type-pred
                 ,valuep-when-index-type-pred
                 ,value-kind-when-elem-type-pred
                 ,value-kind-when-index-type-pred
                 expr-value->value-of-expr-value
                 value-fix-when-valuep
                 ,cintegerp-when-index-type-pred
                 ,okp-lemma-name
                 write-object-to-update-object
                 write-object-okp-of-enter-scope
                 write-object-okp-of-add-var
                 write-object-okp-of-add-frame
                 write-object-okp-when-valuep-of-read-object-no-syntaxp
                 ,@valuep-thms
                 ,@type-of-value-thms
                 ,@writer-return-thms)))
          `(("Goal"
             :in-theory
             '(,@exec-expr-asg-thms
               (:e expr-kind)
               (:e expr-binary->op)
               (:e expr-binary->arg1)
               (:e expr-binary->arg2)
               (:e expr-arrsub->arr)
               (:e expr-arrsub->sub)
               (:e expr-member->target)
               (:e expr-member->name)
               (:e expr-ident->get)
               (:e binop-kind)
               equal-of-const-and-ident
               (:e identp)
               (:e ident->name)
               (:e str-fix)
               not-zp-of-limit-variable
               read-var-to-read-object-of-objdesign-of-var
               ,(atc-var-info->thm varinfo)
               objdesign-of-var-of-const-identifier
               ,elem.thm-name
               expr-valuep-of-expr-value
               apconvert-expr-value-when-not-value-array
               value-kind-when-sintp
               expr-value->value-of-expr-value
               value-fix-when-valuep
               ,valuep-when-elem-type-pred
               ,valuep-when-index-type-pred
               ,cintegerp-when-index-type-pred
               ,okp-lemma-name
               ,index.thm-name
               write-var-of-const-identifier
               write-var-to-update-var
               compustate-frames-number-of-enter-scope-not-zero
               compustate-frames-number-of-add-var-not-zero
               write-var-okp-of-enter-scope
               write-var-okp-of-add-var
               ,@type-of-value-thms
               ,@writer-return-thms
               ident-fix-when-identp
               identp-of-ident
               equal-of-ident-and-ident
               compustate-frames-number-of-update-var
               write-var-okp-of-update-var)))))
       ((mv asg-event &) (evmac-generate-defthm asg-thm-name
                                                :formula asg-formula
                                                :hints asg-hints
                                                :enable nil))
       ((mv item
            item-limit
            item-events
            item-thm-name
            thm-index
            names-to-avoid)
        (atc-gen-block-item-asg asg
                                asg-limit
                                (append struct.events
                                        index.events
                                        elem.events
                                        (list okp-lemma-event
                                              asg-event))
                                asg-thm-name
                                new-compst
                                (change-stmt-gin
                                 gin
                                 :thm-index thm-index
                                 :names-to-avoid names-to-avoid
                                 :proofs t)
                                state))
       (new-context
        (atc-context-extend gin.context
                            (list
                             (make-atc-premise-cvalue
                              :var var
                              :term struct-write-term)
                             (make-atc-premise-compustate
                              :var gin.compst-var
                              :term (if pointerp
                                        `(update-object
                                          ,(add-suffix-to-fn var "-OBJDES")
                                          ,var
                                          ,gin.compst-var)
                                      `(update-var
                                        (ident ,(symbol-name var))
                                        ,var
                                        ,gin.compst-var))))))
       (notflexarrmem-thms (atc-type-to-notflexarrmem-thms (type-struct tag)
                                                           gin.prec-tags))
       (value-kind-thms
        (atc-string-taginfo-alist-to-value-kind-thms gin.prec-tags))
       (new-inscope-rules
        (if pointerp
            `(objdesign-of-var-of-update-object-iff
              read-object-of-objdesign-of-var-to-read-var
              read-object-of-update-object-same
              read-object-of-update-object-disjoint
              read-var-of-update-object
              compustate-frames-number-of-enter-scope-not-zero
              read-var-of-enter-scope
              compustate-frames-number-of-add-var-not-zero
              compustate-frames-number-of-update-object
              read-var-of-add-var
              not-flexible-array-member-p-when-ucharp
              not-flexible-array-member-p-when-scharp
              not-flexible-array-member-p-when-ushortp
              not-flexible-array-member-p-when-sshortp
              not-flexible-array-member-p-when-uintp
              not-flexible-array-member-p-when-sintp
              not-flexible-array-member-p-when-ulongp
              not-flexible-array-member-p-when-slongp
              not-flexible-array-member-p-when-ullongp
              not-flexible-array-member-p-when-sllongp
              not-flexible-array-member-p-when-value-pointer
              read-object-of-update-object-same
              remove-flexible-array-member-when-absent
              value-fix-when-valuep
              valuep-when-ucharp
              valuep-when-scharp
              valuep-when-ushortp
              valuep-when-sshortp
              valuep-when-uintp
              valuep-when-sintp
              valuep-when-ulongp
              valuep-when-slongp
              valuep-when-ullongp
              valuep-when-sllongp
              ,@valuep-thms
              ,@writer-return-thms
              equal-of-ident-and-ident
              (:e str-fix)
              ident-fix-when-identp
              identp-of-ident)
          `(objdesign-of-var-of-update-var-iff
            read-object-of-objdesign-of-var-of-update-var
            remove-flexible-array-member-when-absent
            ,@notflexarrmem-thms
            ,@value-kind-thms
            value-fix-when-valuep
            ,@valuep-thms
            ,@writer-return-thms
            equal-of-ident-and-ident
            (:e str-fix)
            ident-fix-when-identp
            identp-of-ident)))
       ((mv new-inscope new-inscope-events names-to-avoid)
        (atc-gen-new-inscope gin.fn
                             gin.fn-guard
                             gin.inscope
                             new-context
                             gin.compst-var
                             new-inscope-rules
                             gin.prec-tags
                             thm-index
                             names-to-avoid
                             wrld))
       (thm-index (1+ thm-index))
       (events (append item-events
                       new-inscope-events)))
    (retok item
           struct-write-term
           item-limit
           events
           item-thm-name
           new-inscope
           new-context
           thm-index
           names-to-avoid))
  :guard-hints
  (("Goal"
    :in-theory
    (e/d (pseudo-termp
          acl2::true-listp-when-pseudo-event-form-listp-rewrite)
         ((:e tau-system))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-block-item-integer-asg ((var symbolp)
                                        (val-term pseudo-termp)
                                        (arg-term pseudo-termp)
                                        (type typep)
                                        (integer-write-fn symbolp)
                                        (wrapper? symbolp)
                                        (gin stmt-ginp)
                                        state)
  :returns (mv erp
               (item block-itemp)
               (val-term* pseudo-termp :hyp (symbolp integer-write-fn))
               (limit pseudo-termp)
               (events pseudo-event-form-listp)
               (thm-name symbolp)
               (new-inscope atc-symbol-varinfo-alist-listp)
               (new-context atc-contextp)
               (thm-index posp)
               (names-to-avoid symbol-listp))
  :short "Generate a C block item statement that consists of
          an assignment to a pointed integer."
  (b* (((reterr) (irr-block-item) nil nil nil nil nil (irr-atc-context) 1 nil)
       (wrld (w state))
       ((stmt-gin gin) gin)
       ((unless (eq wrapper? nil))
        (reterr
         (msg "The pointed integer write term ~x0 ~
               to which ~x1 is bound ~
               has the ~x2 wrapper, which is disallowed."
              val-term var wrapper?)))
       ((unless (member-eq var gin.affect))
        (reterr
         (msg "The pointed integer ~x0 is being written to, ~
               but it is not among the variables ~x1 ~
               currently affected."
              var gin.affect)))
       ((erp (expr-gout ptr))
        (atc-gen-expr-pure var
                           (make-expr-gin
                            :context gin.context
                            :inscope gin.inscope
                            :prec-tags gin.prec-tags
                            :fn gin.fn
                            :fn-guard gin.fn-guard
                            :compst-var gin.compst-var
                            :thm-index gin.thm-index
                            :names-to-avoid gin.names-to-avoid
                            :proofs gin.proofs)
                           state))
       ((unless (equal ptr.type (type-pointer type)))
        (reterr
         (msg "The variable ~x0 of type ~x1 does not have ~
               the expected type ~x2. ~
               This is indicative of ~
               unreachable code under the guards, ~
               given that the code is guard-verified."
              var ptr.type (type-pointer type))))
       ((erp (expr-gout int))
        (atc-gen-expr-pure arg-term
                           (make-expr-gin
                            :context gin.context
                            :inscope gin.inscope
                            :prec-tags gin.prec-tags
                            :fn gin.fn
                            :fn-guard gin.fn-guard
                            :compst-var gin.compst-var
                            :thm-index ptr.thm-index
                            :names-to-avoid ptr.names-to-avoid
                            :proofs (and ptr.thm-name t))
                           state))
       ((unless (equal int.type type))
        (reterr
         (msg "The term ~x0 of type ~x1 does not have ~
               the expected type ~x2. ~
               This is indicative of ~
               unreachable code under the guards, ~
               given that the code is guard-verified."
              arg-term int.type type)))
       (asg (make-expr-binary
             :op (binop-asg)
             :arg1 (make-expr-unary
                    :op (unop-indir)
                    :arg ptr.expr)
             :arg2 int.expr))
       (stmt (stmt-expr asg))
       (item (block-item-stmt stmt))
       (asg-limit ''1)
       (expr-limit `(binary-+ '1 ,asg-limit))
       (stmt-limit `(binary-+ '1 ,expr-limit))
       (item-limit `(binary-+ '1 ,stmt-limit))
       ((when (eq integer-write-fn 'quote))
        (reterr (raise "Internal error: integer writer is QUOTE.")))
       (integer-write-term `(,integer-write-fn ,int.term))
       (varinfo (atc-get-var var gin.inscope))
       ((unless varinfo)
        (reterr (raise "Internal error: no information for variable ~x0." var)))
       ((when (not int.thm-name))
        (retok item
               integer-write-term
               item-limit
               (append ptr.events
                       int.events)
               nil
               gin.inscope
               gin.context
               int.thm-index
               int.names-to-avoid))
       (new-compst `(update-object ,(add-suffix-to-fn var "-OBJDES")
                                   ,integer-write-term
                                   ,gin.compst-var))
       (new-compst (untranslate$ new-compst nil state))
       (asg-thm-name (pack gin.fn '-correct- int.thm-index))
       ((mv asg-thm-name names-to-avoid)
        (fresh-logical-name-with-$s-suffix asg-thm-name
                                           nil
                                           int.names-to-avoid
                                           wrld))
       (thm-index (1+ int.thm-index))
       (asg-formula `(equal (exec-expr-asg ',asg
                                           ,gin.compst-var
                                           ,gin.fenv-var
                                           ,gin.limit-var)
                            ,new-compst))
       (asg-formula (atc-contextualize asg-formula
                                       gin.context
                                       gin.fn
                                       gin.fn-guard
                                       gin.compst-var
                                       gin.limit-var
                                       asg-limit
                                       t
                                       wrld))
       (type-pred (atc-type-to-recognizer type gin.prec-tags))
       (exec-expr-asg-thm
        (pack 'exec-expr-asg-indir-when- type-pred '-for-modular-proofs))
       (value-kind-thm (atc-type-to-value-kind-thm type gin.prec-tags))
       (valuep-when-type-pred (atc-type-to-valuep-thm type gin.prec-tags))
       (type-of-value-thm (atc-type-to-type-of-value-thm type gin.prec-tags))
       (type-pred-of-integer-write-fn (pack type-pred '-of- integer-write-fn))
       (asg-hints
        `(("Goal"
           :in-theory '(,exec-expr-asg-thm
                        (:e expr-kind)
                        (:e expr-binary->op)
                        (:e expr-binary->arg1)
                        (:e expr-binary->arg2)
                        (:e binop-kind)
                        (:e expr-unary->op)
                        (:e expr-unary->arg)
                        (:e unop-kind)
                        not-zp-of-limit-variable
                        (:e expr-ident->get)
                        read-var-of-const-identifier
                        (:e identp)
                        (:e ident->name)
                        read-var-to-read-object-of-objdesign-of-var
                        ,(atc-var-info->thm varinfo)
                        ,ptr.thm-name
                        ,int.thm-name
                        expr-valuep-of-expr-value
                        apconvert-expr-value-when-not-value-array
                        ,value-kind-thm
                        expr-value->value-of-expr-value
                        value-fix-when-valuep
                        ,valuep-when-type-pred
                        write-object-to-update-object
                        write-object-okp-of-add-var
                        write-object-okp-of-add-frame
                        write-object-okp-when-valuep-of-read-object-no-syntaxp
                        ,type-of-value-thm
                        ,type-pred-of-integer-write-fn))))
       ((mv asg-event &) (evmac-generate-defthm asg-thm-name
                                                :formula asg-formula
                                                :hints asg-hints
                                                :enable nil))
       ((mv item
            item-limit
            item-events
            item-thm-name
            thm-index
            names-to-avoid)
        (atc-gen-block-item-asg asg
                                asg-limit
                                (append ptr.events
                                        int.events
                                        (list asg-event))
                                asg-thm-name
                                new-compst
                                (change-stmt-gin
                                 gin
                                 :thm-index thm-index
                                 :names-to-avoid names-to-avoid
                                 :proofs t)
                                state))
       (new-context
        (atc-context-extend gin.context
                            (list
                             (make-atc-premise-cvalue
                              :var var
                              :term integer-write-term)
                             (make-atc-premise-compustate
                              :var gin.compst-var
                              :term `(update-object
                                      ,(add-suffix-to-fn var "-OBJDES")
                                      ,var
                                      ,gin.compst-var)))))
       (type-pred-of-type-write (pack type-pred '-of- (type-kind type) '-write))
       (not-flexible-array-member-p-when-type-pred
        (pack 'not-flexible-array-member-p-when- type-pred))
       (new-inscope-rules
        `(objdesign-of-var-of-update-object-iff
          read-object-of-objdesign-of-var-to-read-var
          read-var-of-update-object
          compustate-frames-number-of-add-var-not-zero
          read-object-of-update-object-same
          read-object-of-update-object-disjoint
          object-disjointp-commutative
          read-var-of-add-var
          remove-flexible-array-member-when-absent
          not-flexible-array-member-p-when-ucharp
          not-flexible-array-member-p-when-scharp
          not-flexible-array-member-p-when-ushortp
          not-flexible-array-member-p-when-sshortp
          not-flexible-array-member-p-when-uintp
          not-flexible-array-member-p-when-sintp
          not-flexible-array-member-p-when-ulongp
          not-flexible-array-member-p-when-slongp
          not-flexible-array-member-p-when-ullongp
          not-flexible-array-member-p-when-sllongp
          not-flexible-array-member-p-when-value-pointer
          value-fix-when-valuep
          valuep-when-ucharp
          valuep-when-scharp
          valuep-when-ushortp
          valuep-when-sshortp
          valuep-when-uintp
          valuep-when-sintp
          valuep-when-ulongp
          valuep-when-slongp
          valuep-when-ullongp
          valuep-when-sllongp
          ,type-pred-of-type-write
          ,not-flexible-array-member-p-when-type-pred
          ident-fix-when-identp
          identp-of-ident
          equal-of-ident-and-ident
          (:e str-fix)
          read-var-of-update-object
          compustate-frames-number-of-enter-scope-not-zero
          read-var-of-enter-scope
          read-var-of-update-object
          compustate-frames-number-of-update-object))
       ((mv new-inscope new-inscope-events names-to-avoid)
        (atc-gen-new-inscope gin.fn
                             gin.fn-guard
                             gin.inscope
                             new-context
                             gin.compst-var
                             new-inscope-rules
                             gin.prec-tags
                             thm-index
                             names-to-avoid
                             wrld))
       (thm-index (1+ thm-index))
       (events (append item-events
                       new-inscope-events)))
    (retok item
           integer-write-term
           item-limit
           events
           item-thm-name
           new-inscope
           new-context
           thm-index
           names-to-avoid))
  :guard-hints
  (("Goal"
    :in-theory
    (e/d (pseudo-termp
          acl2::true-listp-when-pseudo-event-form-listp-rewrite)
         ((:e tau-system))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-block-item-list-none ((term pseudo-termp)
                                      (gin stmt-ginp)
                                      state)
  :returns (gout stmt-goutp)
  :short "Generate an empty list of block items."
  :long
  (xdoc::topstring
   (xdoc::p
    "The empty list of block items itself is trivial of course,
     but we also generate a theorem about
     @(tsee exec-block-item-list) applied to the empty list of block items.
     This provide uniformity with non-empty lists of block items,
     when lists of block items that may be empty or not are involved
     within larger constructs.")
   (xdoc::p
    "We return 1 as the limit,
     which is needed in @(tsee exec-block-item-list)
     to not return an error due to the limit being exhausted."))
  (b* (((stmt-gin gin) gin)
       (wrld (w state))
       (limit (pseudo-term-quote 1))
       ((when (not gin.proofs))
        (make-stmt-gout
         :items nil
         :type (type-void)
         :term term
         :context gin.context
         :inscope gin.inscope
         :limit limit
         :events nil
         :thm-name nil
         :thm-index gin.thm-index
         :names-to-avoid gin.names-to-avoid))
       (name (pack gin.fn '-correct- gin.thm-index))
       ((mv name names-to-avoid)
        (fresh-logical-name-with-$s-suffix name nil gin.names-to-avoid wrld))
       (thm-index (1+ gin.thm-index))
       (exec-formula `(equal (exec-block-item-list nil
                                                   ,gin.compst-var
                                                   ,gin.fenv-var
                                                   ,gin.limit-var)
                             (mv (stmt-value-none) ,gin.compst-var)))
       (exec-formula (atc-contextualize exec-formula
                                        gin.context
                                        gin.fn
                                        gin.fn-guard
                                        gin.compst-var
                                        gin.limit-var
                                        limit
                                        t
                                        wrld))
       ((mv type-formula type-thms)
        (atc-gen-term-type-formula (untranslate$ term nil state)
                                   (type-void)
                                   gin.affect
                                   gin.inscope
                                   gin.prec-tags))
       (type-formula (atc-contextualize type-formula
                                        gin.context
                                        gin.fn
                                        gin.fn-guard
                                        nil
                                        nil
                                        nil
                                        nil
                                        wrld))
       (formula `(and ,exec-formula ,type-formula))
       (hints
        `(("Goal" :in-theory '(exec-block-item-list-of-nil
                               not-zp-of-limit-variable
                               compustatep-of-add-frame
                               compustatep-of-enter-scope
                               compustatep-of-exit-scope
                               compustatep-of-add-var
                               compustatep-of-update-var
                               compustatep-of-update-object
                               compustatep-of-update-static-var
                               compustatep-of-if*-when-both-compustatep
                               ,@type-thms
                               uchar-array-length-of-uchar-array-write
                               schar-array-length-of-schar-array-write
                               ushort-array-length-of-ushort-array-write
                               sshort-array-length-of-sshort-array-write
                               uint-array-length-of-uint-array-write
                               sint-array-length-of-sint-array-write
                               ulong-array-length-of-ulong-array-write
                               slong-array-length-of-slong-array-write
                               ullong-array-length-of-ullong-array-write
                               sllong-array-length-of-sllong-array-write
                               mv-nth-of-cons
                               (:e zp)))))
       ((mv event &) (evmac-generate-defthm name
                                            :formula formula
                                            :hints hints
                                            :enable nil)))
    (make-stmt-gout
     :items nil
     :type (type-void)
     :term term
     :context gin.context
     :inscope gin.inscope
     :limit limit
     :events (list event)
     :thm-name name
     :thm-index thm-index
     :names-to-avoid names-to-avoid)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-block-item-list-one
  ((term pseudo-termp)
   (type typep)
   (item block-itemp)
   (item-limit pseudo-termp)
   (item-events pseudo-event-form-listp)
   (item-thm symbolp)
   (stmt-value "An untranslated term.")
   (new-compst "An untranslated term.")
   (new-context atc-contextp)
   (new-inscope atc-symbol-varinfo-alist-listp)
   (gin stmt-ginp)
   state)
  :returns (gout stmt-goutp)
  :short "Generate a list of C block items that consists of a given item."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used to lift generated block items to generated block item lists.
     Besides the (singleton) block item list,
     we also generate a theorem saying that
     @(tsee exec-block-item-list) applied to the quoted block item list
     yields an @(tsee mv) pair consisting of
     a statement value term
     and a possibly updated computation state;
     these are the same as the ones for the single item theorem.")
   (xdoc::p
    "The limit for the block item list is
     1 more than the limit for the block item,
     because we need 1 to go from @(tsee exec-block-item-list)
     to @(tsee exec-block-item).")
   (xdoc::p
    "When this function is called on a block item
     that is an @('if') that returns @('void'),
     @('new-compst') is an @(tsee if*)
     whose branches have the form @('(exit-scope ...)')
     (after expanding @(tsee let)s).
     The combination of the rules
     @('compustatep-of-exit-scope') and
     @('compustatep-of-if*-when-both-compustatep')
     serves to show that @(tsee compustatep) holds on the @(tsee if*),
     as needed during the proof,
     without having to expand the @(tsee if*).")
   (xdoc::p
    "The @('new-inscope') input is the variable table
     just after the block item."))
  (b* (((stmt-gin gin) gin)
       (wrld (w state))
       (items (list item))
       (items-limit (pseudo-term-fncall
                     'binary-+
                     (list (pseudo-term-quote 1)
                           item-limit)))
       ((when (not gin.proofs))
        (make-stmt-gout
         :items items
         :type type
         :term term
         :context new-context
         :inscope new-inscope
         :limit items-limit
         :events item-events
         :thm-name nil
         :thm-index gin.thm-index
         :names-to-avoid gin.names-to-avoid))
       (name (pack gin.fn '-correct- gin.thm-index))
       (thm-index (1+ gin.thm-index))
       ((mv name names-to-avoid)
        (fresh-logical-name-with-$s-suffix name nil gin.names-to-avoid wrld))
       (voidp (type-case type :void))
       (exec-formula `(equal (exec-block-item-list ',items
                                                   ,gin.compst-var
                                                   ,gin.fenv-var
                                                   ,gin.limit-var)
                             (mv ,stmt-value ,new-compst)))
       (exec-formula (atc-contextualize exec-formula
                                        gin.context
                                        gin.fn
                                        gin.fn-guard
                                        gin.compst-var
                                        gin.limit-var
                                        items-limit
                                        t
                                        wrld))
       (uterm (untranslate$ term nil state))
       ((mv type-formula &)
        (atc-gen-term-type-formula
         uterm type gin.affect gin.inscope gin.prec-tags))
       (type-formula (atc-contextualize type-formula
                                        gin.context
                                        gin.fn
                                        gin.fn-guard
                                        nil
                                        nil
                                        nil
                                        nil
                                        wrld))
       (formula `(and ,exec-formula ,type-formula))
       (hints
        `(("Goal" :in-theory '(exec-block-item-list-when-consp
                               not-zp-of-limit-variable
                               mv-nth-of-cons
                               (:e zp)
                               value-optionp-when-valuep
                               (:e value-optionp)
                               (:e valuep)
                               ,@(and (not voidp)
                                      (list
                                       (atc-type-to-valuep-thm type
                                                               gin.prec-tags)))
                               ,item-thm
                               exec-block-item-list-of-nil
                               return-type-of-stmt-value-return
                               return-type-of-stmt-value-none
                               stmt-value-return->value?-of-stmt-value-return
                               stmt-value-return-of-value-option-fix-value?
                               value-option-fix-when-value-optionp
                               not-zp-of-limit-minus-const
                               compustatep-of-exit-scope
                               compustatep-of-update-object
                               compustatep-of-update-static-var
                               compustatep-of-if*-when-both-compustatep
                               uchar-array-length-of-uchar-array-write
                               schar-array-length-of-schar-array-write
                               ushort-array-length-of-ushort-array-write
                               sshort-array-length-of-sshort-array-write
                               uint-array-length-of-uint-array-write
                               sint-array-length-of-sint-array-write
                               ulong-array-length-of-ulong-array-write
                               slong-array-length-of-slong-array-write
                               ullong-array-length-of-ullong-array-write
                               sllong-array-length-of-sllong-array-write))))
       ((mv event &) (evmac-generate-defthm name
                                            :formula formula
                                            :hints hints
                                            :enable nil)))
    (make-stmt-gout
     :items items
     :type type
     :term term
     :context new-context
     :inscope new-inscope
     :limit items-limit
     :events (append item-events (list event))
     :thm-name name
     :thm-index thm-index
     :names-to-avoid names-to-avoid)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-block-item-list-cons
  ((term pseudo-termp)
   (item block-itemp)
   (item-limit pseudo-termp)
   (item-events pseudo-event-form-listp)
   (item-thm symbolp)
   (items block-item-listp)
   (items-limit pseudo-termp)
   (items-events pseudo-event-form-listp)
   (items-thm symbolp)
   (items-type typep)
   (new-context atc-contextp)
   (new-inscope atc-symbol-varinfo-alist-listp)
   (gin stmt-ginp)
   state)
  :returns (gout stmt-goutp)
  :short "Generate a list of block items by @(tsee cons)ing
          a block item to a list of block items."
  :long
  (xdoc::topstring
   (xdoc::p
    "We need a limit that suffices for both @('item') and @('items').
     We take their sum (instead of the maximum), so the term remains linear.
     We also need to add 1, because it takes 1 to go
     from the execution of @('(cons item items)')
     to the execution of @('item') and @('items').")
   (xdoc::p
    "The context in @('gin') is the one before all the items,
     while the context @('new-context') is the one after all the items.
     The former should be always a prefix of the latter.
     In order to calculate the computation state after all the items,
     we take the ``difference'' between the two contexts
     and use it to contextualize the computation state variable,
     obtaining the computation state after all the items;
     note that, at that spot in the generated theorem,
     the computation state variable already accumulates
     the contextual premises in @('gin').")
   (xdoc::p
    "The @('new-inscope') input is the variable table after all the items.")
   (xdoc::p
    "Currently this function is only called on a @('term')
     that returns a single value,
     which is either the returned C value (if the C type is not @('void')),
     or a side-effected variables (if the C type is @('void')).
     Thus, if the type if not @('void'),
     we can take the whole term
     as the first result of @(tsee exec-block-item-list).
     In the future, this will need to be generalized
     to be @('(mv-nth 0 term)') when the term returns multiple results
     and the type is not @('void')."))
  (b* ((wrld (w state))
       ((stmt-gin gin) gin)
       (all-items (cons item items))
       (all-items-limit `(binary-+ '1 (binary-+ ,item-limit ,items-limit)))
       ((when (not gin.proofs))
        (make-stmt-gout
         :items all-items
         :type items-type
         :term term
         :context gin.context
         :inscope gin.inscope
         :limit all-items-limit
         :events (append item-events items-events)
         :thm-name nil
         :thm-index gin.thm-index
         :names-to-avoid gin.names-to-avoid))
       (new-compst (atc-contextualize-compustate gin.compst-var
                                                 gin.context
                                                 new-context))
       ((mv stmt-value type-formula &)
        (atc-gen-stmt-value-term-and-type-formula (untranslate$ term nil state)
                                                  items-type
                                                  gin.affect
                                                  gin.inscope
                                                  gin.prec-tags))
       (exec-formula `(equal (exec-block-item-list ',all-items
                                                   ,gin.compst-var
                                                   ,gin.fenv-var
                                                   ,gin.limit-var)
                             (mv ,stmt-value ,new-compst)))
       (exec-formula (atc-contextualize exec-formula
                                        gin.context
                                        gin.fn
                                        gin.fn-guard
                                        gin.compst-var
                                        gin.limit-var
                                        all-items-limit
                                        t
                                        wrld))
       (type-formula (atc-contextualize type-formula
                                        gin.context
                                        gin.fn
                                        gin.fn-guard
                                        nil
                                        nil
                                        nil
                                        nil
                                        wrld))
       (formula `(and ,exec-formula ,type-formula))
       (hints
        `(("Goal" :in-theory '(exec-block-item-list-when-consp
                               not-zp-of-limit-variable
                               ,item-thm
                               mv-nth-of-cons
                               (:e zp)
                               (:e value-optionp)
                               (:e value-option-fix)
                               not-zp-of-limit-minus-const
                               return-type-of-stmt-value-return
                               return-type-of-stmt-value-none
                               stmt-value-return->value?-of-stmt-value-return
                               stmt-value-return-of-value-option-fix-value?
                               (:e valuep)
                               ,items-thm
                               uchar-array-length-of-uchar-array-write
                               schar-array-length-of-schar-array-write
                               ushort-array-length-of-ushort-array-write
                               sshort-array-length-of-sshort-array-write
                               uint-array-length-of-uint-array-write
                               sint-array-length-of-sint-array-write
                               ulong-array-length-of-ulong-array-write
                               slong-array-length-of-slong-array-write
                               ullong-array-length-of-ullong-array-write
                               sllong-array-length-of-sllong-array-write))))
       (thm-name (pack gin.fn '-correct- gin.thm-index))
       (thm-index (1+ gin.thm-index))
       ((mv thm-name names-to-avoid) (fresh-logical-name-with-$s-suffix
                                      thm-name nil gin.names-to-avoid wrld))
       ((mv event &) (evmac-generate-defthm thm-name
                                            :formula formula
                                            :hints hints
                                            :enable nil)))
    (make-stmt-gout :items all-items
                    :type items-type
                    :term term
                    :context new-context
                    :inscope new-inscope
                    :limit all-items-limit
                    :events (append item-events
                                    items-events
                                    (list event))
                    :thm-name thm-name
                    :thm-index thm-index
                    :names-to-avoid names-to-avoid))
  :guard-hints (("Goal" :in-theory (enable pseudo-termp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-block-item-list-append
  ((term pseudo-termp)
   (items1 block-item-listp)
   (items2 block-item-listp)
   (items1-limit pseudo-termp)
   (items2-limit pseudo-termp)
   (items1-events pseudo-event-form-listp)
   (items2-events pseudo-event-form-listp)
   (items1-thm symbolp)
   (items2-thm symbolp)
   (type typep "Returned by @('items2').")
   (new-context atc-contextp "After all items.")
   (new-inscope atc-symbol-varinfo-alist-listp "After all items.")
   (gin stmt-ginp)
   state)
  :returns (gout stmt-goutp)
  :short "Generate a list of block items by @(tsee append)ing
          two lists of block items."
  :long
  (xdoc::topstring
   (xdoc::p
    "Besides concatenating the two lists, which is easy,
     we also generate a theorem about @(tsee exec-block-item-list)
     applied to the concatenation,
     given theorems about @(tsee exec-block-item-list)
     applied to each of the two lists.")
   (xdoc::p
    "The generated theorem applies @(tsee exec-block-item-list)
     to a quoted list of block items that is the concatenation.
     Thus, we cannot just use a rule
     about @(tsee exec-block-item-list) applied to @(tsee append).
     Instead, we need a rule that backchains to
     two applications of @(tsee exec-block-item-list)
     to sublists of the quoted list,
     obtained via @(tsee take) and @(tsee nthcdr).
     We generate this rule as a lemma before the theorem.")
   (xdoc::p
    "We need a limit that suffices for all items.
     We take the sum of the limits of the two lists of items
     (instead of the maximum), so the term remains linear.
     That suffices to execute the items from the first list,
     but we also need to add 1 to the limit
     because it takes 1 step to go from the end of the first list
     to starting the second list."))
  (b* ((wrld (w state))
       ((stmt-gin gin) gin)
       (items (append items1 items2))
       (items-limit `(binary-+ '1 (binary-+ ,items1-limit ,items2-limit)))
       ((when (not gin.proofs))
        (make-stmt-gout
         :items items
         :type type
         :term term
         :context gin.context
         :inscope gin.inscope
         :limit items-limit
         :events (append items1-events items2-events)
         :thm-name nil
         :thm-index gin.thm-index
         :names-to-avoid gin.names-to-avoid))
       (lemma-name
        (pack gin.fn '-exec-block-item-list-concatenation- gin.thm-index))
       ((mv lemma-name names-to-avoid) (fresh-logical-name-with-$s-suffix
                                        lemma-name nil gin.names-to-avoid wrld))
       (thm-index (1+ gin.thm-index))
       (n (len items1))
       (m (+ n (len items2)))
       (lemma-formula
        `(implies (and (syntaxp (and (quotep items)
                                     (equal (len (cadr items)) ,m)))
                       (equal (len items) ,m)
                       (not (zp limit))
                       (equal sval+compst1
                              (exec-block-item-list (take ,n items)
                                                    compst
                                                    fenv
                                                    limit))
                       (equal sval (mv-nth 0 sval+compst1))
                       (stmt-valuep sval)
                       (equal compst1 (mv-nth 1 sval+compst1)))
                  (equal (exec-block-item-list items compst fenv limit)
                         (if (equal (stmt-value-kind sval) :return)
                             (mv sval compst1)
                           (exec-block-item-list (nthcdr ,n items)
                                                 compst1
                                                 fenv
                                                 (- limit ,n))))))
       (lemma-hints
        `(("Goal"
           :in-theory '(stmt-value-return-of-fields
                        stmt-value-fix-when-stmt-valuep
                        valuep-when-value-optionp
                        value-optionp-of-stmt-value-return->value?
                        (:e valuep)
                        append-of-take-and-nthcdr
                        (:e nfix)
                        value-optionp
                        not-errorp-when-stmt-valuep
                        (:e errorp)
                        len-of-take
                        commutativity-of-+)
           :use (:instance exec-block-item-list-of-append
                           (items1 (take ,n items))
                           (items2 (nthcdr ,n items))))))
       ((mv lemma-event &)
        (evmac-generate-defthm lemma-name
                               :formula lemma-formula
                               :hints lemma-hints
                               :enable nil))
       (thm-name (pack gin.fn '-correct- thm-index))
       ((mv thm-name names-to-avoid) (fresh-logical-name-with-$s-suffix
                                      thm-name nil names-to-avoid wrld))
       (thm-index (1+ thm-index))
       (new-compst (atc-contextualize-compustate gin.compst-var
                                                 gin.context
                                                 new-context))
       ((mv stmt-value type-formula &)
        (atc-gen-stmt-value-term-and-type-formula (untranslate$ term nil state)
                                                  type
                                                  gin.affect
                                                  gin.inscope
                                                  gin.prec-tags))
       (exec-formula `(equal (exec-block-item-list ',items
                                                   ,gin.compst-var
                                                   ,gin.fenv-var
                                                   ,gin.limit-var)
                             (mv ,stmt-value ,new-compst)))
       (exec-formula (atc-contextualize exec-formula
                                        gin.context
                                        gin.fn
                                        gin.fn-guard
                                        gin.compst-var
                                        gin.limit-var
                                        items-limit
                                        t
                                        wrld))
       (type-formula (atc-contextualize type-formula
                                        gin.context
                                        gin.fn
                                        gin.fn-guard
                                        nil
                                        nil
                                        nil
                                        nil
                                        wrld))
       (formula `(and ,exec-formula ,type-formula))
       (hints
        `(("Goal" :in-theory '(,lemma-name
                               (:e len)
                               (:e take)
                               (:e nthcdr)
                               not-zp-of-limit-variable
                               ,items1-thm
                               mv-nth-of-cons
                               (:e zp)
                               (:e value-optionp)
                               ,items2-thm
                               (:e valuep)
                               (:e value-option-fix)
                               return-type-of-stmt-value-return
                               return-type-of-stmt-value-none
                               stmt-value-return->value?-of-stmt-value-return
                               uchar-array-length-of-uchar-array-write
                               schar-array-length-of-schar-array-write
                               ushort-array-length-of-ushort-array-write
                               sshort-array-length-of-sshort-array-write
                               uint-array-length-of-uint-array-write
                               sint-array-length-of-sint-array-write
                               ulong-array-length-of-ulong-array-write
                               slong-array-length-of-slong-array-write
                               ullong-array-length-of-ullong-array-write
                               sllong-array-length-of-sllong-array-write))))
       ((mv event &) (evmac-generate-defthm thm-name
                                            :formula formula
                                            :hints hints
                                            :enable nil)))
    (make-stmt-gout :items items
                    :type type
                    :term term
                    :context new-context
                    :inscope new-inscope
                    :limit items-limit
                    :events (append items1-events
                                    items2-events
                                    (list lemma-event event))
                    :thm-name thm-name
                    :thm-index thm-index
                    :names-to-avoid names-to-avoid)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-return-stmt ((term pseudo-termp)
                             (mvp booleanp)
                             (gin stmt-ginp)
                             state)
  :returns (mv erp (gout stmt-goutp))
  :short "Generate a C return statement from an ACL2 term."
  :long
  (xdoc::topstring
   (xdoc::p
    "The term passed here as parameter is the one representing
     the expression to be returned by the statement.
     This may come from two possible places
     (i.e. from two possible calls in @(tsee atc-gen-stmt)):
     when encountering a term @('(mv ret v1 ... vn)')
     affecting variables @('v1'), ..., @('vn'),
     in which case @('ret') is passed to this function
     and @('mvp') is @('t');
     when encountering a term @('term')
     that must be an expression term used as a statement term,
     in which case @('term') is passed to this function
     and @('mvp') is @('nil').
     The flag @('mvp') is used to easily distinguish these two cases,
     which need slightly different treatment.
     Note that, in @('(mv ret v1 ... vn)'),
     @('ret') may be either a pure expression term or a function call,
     and the same holds for the second case discussed above;
     thus, the two situations cannot be readily distinguished
     just by looking at the term alone.")
   (xdoc::p
    "If @('mvp') is @('t'),
     we call @(tsee atc-gen-expr) with @('term') (i.e. @('ret'))
     and we set the affected variables in @('gin') to @('nil').
     In @('(mv ret v1 ... vn)'), @('ret') must not affect any variables,
     which is guaranteed by ACL2 checks on multiple values,
     which cannot be nested:
     if @('ret') affected variables, it would have to return multiple values,
     and could not be an argument of @(tsee mv) in ACL2.")
   (xdoc::p
    "If instead @('mvp') is @('nil'),
     we also call @(tsee atc-gen-expr) with @('term'),
     but without modifying the affected variables in @('gin').
     This is because the term in question is the whole thing
     returned by the ACL2 function being translated to C at that point,
     and so it has to affect exactly the variables that the function affects.")
   (xdoc::p
    "We generate three theorems, which build upon each other:
     one for @(tsee exec-stmt) applied to the return statement,
     one for @(tsee exec-block-item) applied to
     the block item that consists of the return statement,
     and one for @(tsee exec-block-item-list) applied to
     the singleton list of that block item.
     It is the latter term that refers to the list of block items
     returned as the @('gout') result of this ACL2 function.
     We start with the first of the three theorems,
     we will add the other two next.")
   (xdoc::p
    "The limit for the @(tsee exec-stmt) theorem is set to
     1 more than the limit for the expression theorem,
     because we need 1 to go from @(tsee exec-stmt)
     to the @(':return') case and @(tsee exec-expr-call-or-pure).
     The limit for the @(tsee exec-block-item) theorem is set to
     1 more than the limit for the previous theorem,
     because we need 1 to go from @(tsee exec-block-item)
     to the @(':stmt') case and @(tsee exec-stmt).
     The limit for the @(tsee exec-block-item-list) theorem is set to
     1 more than the limit for the previous theorem,
     because we need 1 to go from @(tsee exec-block-item-list)
     to @(tsee exec-block-item).
     The limit returned from this ACL2 function is the latter,
     because it refers to @(tsee exec-block-item-list)."))
  (b* (((reterr) (irr-stmt-gout))
       ((stmt-gin gin) gin)
       (wrld (w state))
       ((erp expr.expr
             expr.type
             expr.term
             expr.result
             expr.new-compst
             expr.limit
             expr.events
             expr.thm-name
             & ; expr.new-inscope
             & ; expr.new-context
             expr.thm-index
             expr.names-to-avoid)
        (atc-gen-expr term
                      (if mvp
                          (change-stmt-gin gin :affect nil)
                        gin)
                      state))
       ((when (type-case expr.type :void))
        (reterr
         (raise "Internal error: return term ~x0 has type void." term)))
       ((when (type-case expr.type :array))
        (reterr
         (msg "When generating a return statement for function ~x0, ~
               the term ~x1 that represents the return expression ~
               has array type ~x2, which is disallowed."
              gin.fn term expr.type)))
       ((when (type-case expr.type :pointer))
        (reterr
         (msg "When generating a return statement for function ~x0, ~
               the term ~x1 that represents the return expression ~
               has pointer type ~x2, which is disallowed."
              gin.fn term expr.type)))
       (stmt (make-stmt-return :value expr.expr))
       (term (if mvp
                 (acl2::make-cons-nest (cons expr.term gin.affect))
               expr.term))
       (uterm (untranslate$ term nil state))
       ((when (not expr.thm-name))
        (retok (make-stmt-gout
                :items (list (block-item-stmt stmt))
                :type expr.type
                :term term
                :context gin.context
                :inscope gin.inscope
                :limit (pseudo-term-fncall
                        'binary-+
                        (list (pseudo-term-quote 3)
                              expr.limit))
                :events expr.events
                :thm-name nil
                :thm-index expr.thm-index
                :names-to-avoid expr.names-to-avoid)))
       (stmt-limit (pseudo-term-fncall
                    'binary-+
                    (list (pseudo-term-quote 1)
                          expr.limit)))
       (thm-index expr.thm-index)
       (names-to-avoid expr.names-to-avoid)
       (valuep-when-type-pred (atc-type-to-valuep-thm expr.type gin.prec-tags))
       (stmt-thm-name (pack gin.fn '-correct- thm-index))
       (thm-index (1+ thm-index))
       ((mv stmt-thm-name names-to-avoid)
        (fresh-logical-name-with-$s-suffix
         stmt-thm-name nil names-to-avoid wrld))
       (stmt-formula1 `(equal (exec-stmt ',stmt
                                         ,gin.compst-var
                                         ,gin.fenv-var
                                         ,gin.limit-var)
                              (mv (stmt-value-return ,expr.result)
                                  ,expr.new-compst)))
       (stmt-formula1 (atc-contextualize stmt-formula1
                                         gin.context
                                         gin.fn
                                         gin.fn-guard
                                         gin.compst-var
                                         gin.limit-var
                                         stmt-limit
                                         t
                                         wrld))
       ((mv stmt-formula2 type-thms)
        (atc-gen-term-type-formula uterm
                                   expr.type
                                   gin.affect
                                   gin.inscope
                                   gin.prec-tags))
       (stmt-formula2 (atc-contextualize stmt-formula2
                                         gin.context
                                         gin.fn
                                         gin.fn-guard
                                         nil
                                         nil
                                         nil
                                         nil
                                         wrld))
       (stmt-formula `(and ,stmt-formula1 ,stmt-formula2))
       (stmt-hints
        `(("Goal" :in-theory '(exec-stmt-when-return
                               (:e stmt-kind)
                               not-zp-of-limit-variable
                               (:e stmt-return->value)
                               mv-nth-of-cons
                               (:e zp)
                               ,valuep-when-type-pred
                               ,expr.thm-name
                               ,@type-thms))))
       ((mv stmt-event &) (evmac-generate-defthm stmt-thm-name
                                                 :formula stmt-formula
                                                 :hints stmt-hints
                                                 :enable nil))
       ((mv item
            item-limit
            item-events
            item-thm-name
            thm-index
            names-to-avoid)
        (atc-gen-block-item-stmt stmt
                                 stmt-limit
                                 (append expr.events
                                         (list stmt-event))
                                 stmt-thm-name
                                 uterm
                                 expr.type
                                 `(stmt-value-return ,expr.result)
                                 expr.new-compst
                                 (change-stmt-gin
                                  gin
                                  :thm-index thm-index
                                  :names-to-avoid names-to-avoid)
                                 state))
       (gout (atc-gen-block-item-list-one term
                                          expr.type
                                          item
                                          item-limit
                                          item-events
                                          item-thm-name
                                          `(stmt-value-return ,expr.result)
                                          expr.new-compst
                                          gin.context
                                          nil
                                          (change-stmt-gin
                                           gin
                                           :thm-index thm-index
                                           :names-to-avoid names-to-avoid
                                           :proofs (and item-thm-name t))
                                          state)))
    (retok gout))
  :guard-hints
  (("Goal"
    :in-theory (e/d (acl2::true-listp-when-pseudo-event-form-listp-rewrite)
                    ((:e tau-system)))))
  :prepwork
  ((defrulel not-consp-when-posp
     (implies (posp x)
              (not (consp x))))
   (defrulel acl2-numberp-when-posp
     (implies (posp x)
              (acl2-numberp x)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-mbt-block-items ((test-term pseudo-termp)
                                 (then-term pseudo-termp)
                                 (else-term pseudo-termp)
                                 (then-items block-item-listp)
                                 (then-type typep)
                                 (then-limit pseudo-termp)
                                 (then-events pseudo-event-form-listp)
                                 (then-thm symbolp)
                                 (new-context atc-contextp)
                                 (new-inscope atc-symbol-varinfo-alist-listp)
                                 (gin stmt-ginp)
                                 state)
  :returns (mv erp (gout stmt-goutp))
  :short "Generate a list of block items
          from an ACL2 conditional with an @(tsee mbt) test."
  :long
  (xdoc::topstring
   (xdoc::p
    "A statement term may be an ACL2 @(tsee if) with an @(tsee mbt) test.
     This represents the same C code as the `then' branch.
     Thus, @(tsee atc-gen-stmt), when encountering an @(tsee if) of this form,
     processes the `then' branch, obtaining
     a list of block items and other related pieces of information,
     which are all passed to this function,
     along with the three argument terms of the @(tsee if).")
   (xdoc::p
    "Here we generate two theorems.")
   (xdoc::p
    "The first one is a lemma that says that the ACL2 conditional
     is equal to its `then' branch under the guard
     and under all the contextual assumptions that involve ACL2 terms
     (i.e. not involving computation states).
     We use @(tsee if*) for the ACL2 conditional,
     consistently with other ACL2 conditionals that we translate to C,
     to avoid unwanted case splits.
     This lemma is proved using the guard theorem,
     and enabling the guard function,
     @(tsee if*), @(tsee test*), @(tsee declar), and @(tsee assign),
     just like in the @('okp') theorems
     generated for expressions (e.g. see atc-gen-expr-unary).")
   (xdoc::p
    "The second one is the correctness theorem for the ACL2 conditional.
     It is just like the one for the `then' branch,
     except that it has the conditional (with @(tsee if*))
     instead of the `then' term.
     It is proved using the correctness theorem for the `then' branch,
     and enabling the lemma described just above.")
   (xdoc::p
    "Since @(tsee atc-gen-fn-def*) replaces every @(tsee if) with @(tsee if*)
     in the whole body of the function,
     we need to perform this replacement in both the test and `else' branch,
     because these are not recursively processed to generate code.")
   (xdoc::p
    "The @('new-context') parameter is the context just after the `then' branch,
     which is also the context after the whole @(tsee if).")
   (xdoc::p
    "The generation of modular proofs in this code currently assumes that
     @('then-term') returns a single value,
     which is either a returned C value
     or a side-effected C variable
     (the distinction is based on @('then-type')).
     This is reflected in the generated modular theorems.
     This will need to be generalized to the case in which the term
     returns multiple values."))
  (b* (((reterr) (irr-stmt-gout))
       ((stmt-gin gin) gin)
       (wrld (w state))
       (test-term `(mbt ,(fty-if-to-if* test-term)))
       (else-term (fty-if-to-if* else-term))
       (term `(if* ,test-term ,then-term ,else-term))
       ((when (not gin.proofs))
        (retok (make-stmt-gout :items then-items
                               :type then-type
                               :term term
                               :context gin.context
                               :inscope gin.inscope
                               :limit then-limit
                               :events then-events
                               :thm-name nil
                               :thm-index gin.thm-index
                               :names-to-avoid gin.names-to-avoid)))
       (lemma-name (pack gin.fn '-if-mbt- gin.thm-index))
       ((mv lemma-name names-to-avoid) (fresh-logical-name-with-$s-suffix
                                        lemma-name nil gin.names-to-avoid wrld))
       (thm-index (1+ gin.thm-index))
       (lemma-formula `(equal ,term ,then-term))
       (lemma-formula (untranslate$ lemma-formula nil state))
       (lemma-formula (atc-contextualize lemma-formula
                                         gin.context
                                         gin.fn
                                         gin.fn-guard
                                         nil
                                         nil
                                         nil
                                         nil
                                         wrld))
       (lemma-hints `(("Goal"
                       :in-theory '(,gin.fn-guard if* test* declar assign)
                       :use (:guard-theorem ,gin.fn))))
       ((mv lemma-event &)
        (evmac-generate-defthm lemma-name
                               :formula lemma-formula
                               :hints lemma-hints
                               :enable nil))
       (thm-name (pack gin.fn '-correct- thm-index))
       ((mv thm-name names-to-avoid)
        (fresh-logical-name-with-$s-suffix thm-name nil names-to-avoid wrld))
       (thm-index (1+ thm-index))
       (uterm (untranslate$ term nil state))
       (formula1 `(equal (exec-block-item-list ',then-items
                                               ,gin.compst-var
                                               ,gin.fenv-var
                                               ,gin.limit-var)
                         (mv ,(if (type-case then-type :void)
                                  '(stmt-value-none)
                                `(stmt-value-return ,uterm))
                             ,gin.compst-var)))
       (formula1 (atc-contextualize formula1
                                    gin.context
                                    gin.fn
                                    gin.fn-guard
                                    gin.compst-var
                                    gin.limit-var
                                    then-limit
                                    t
                                    wrld))
       (formula (if (type-case then-type :void)
                    formula1
                  (b* ((type-pred
                        (atc-type-to-recognizer then-type gin.prec-tags))
                       (formula2 `(,type-pred ,term))
                       (formula2 (atc-contextualize formula2
                                                    gin.context
                                                    gin.fn
                                                    gin.fn-guard
                                                    nil
                                                    nil
                                                    nil
                                                    nil
                                                    wrld)))
                    `(and ,formula1 ,formula2))))
       (hints `(("Goal" :use ,then-thm :in-theory '(,lemma-name))))
       ((mv thm-event &) (evmac-generate-defthm thm-name
                                                :formula formula
                                                :hints hints
                                                :enable nil)))
    (retok (make-stmt-gout :items then-items
                           :type then-type
                           :term term
                           :context new-context
                           :inscope new-inscope
                           :limit then-limit
                           :events (append then-events
                                           (list lemma-event
                                                 thm-event))
                           :thm-name thm-name
                           :thm-index thm-index
                           :names-to-avoid names-to-avoid)))
  :guard-hints (("Goal" :in-theory (enable pseudo-termp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-if/ifelse-stmt ((test-term pseudo-termp)
                                (then-term pseudo-termp)
                                (else-term pseudo-termp)
                                (test-expr exprp)
                                (then-items block-item-listp)
                                (else-items block-item-listp)
                                (test-type typep)
                                (then-type typep)
                                (else-type typep)
                                (then-limit pseudo-termp)
                                (else-limit pseudo-termp)
                                (test-thm symbolp)
                                (then-thm symbolp)
                                (else-thm symbolp)
                                (then-context-start atc-contextp)
                                (else-context-start atc-contextp)
                                (then-context-end atc-contextp)
                                (else-context-end atc-contextp)
                                (then-inscope atc-symbol-varinfo-alist-listp)
                                (else-inscope atc-symbol-varinfo-alist-listp)
                                (test-events pseudo-event-form-listp)
                                (then-events pseudo-event-form-listp)
                                (else-events pseudo-event-form-listp)
                                (gin stmt-ginp)
                                state)
  :returns (mv erp (gout stmt-goutp))
  :short "Generate a C @('if') or @('if')-@('else') statement
          from an ACL2 term."
  :long
  (xdoc::topstring
   (xdoc::p
    "We generate an @('if') if the `else' branch is empty.
     Otherwise we generate an @('if')-@('else').")
   (xdoc::p
    "We generate a theorem for each branch:
     each theorem is about the compound statement
     that consists of the block items of the branch.
     Recall that @(tsee atc-gen-stmt) recursively generates
     theorems for those lists of block items;
     these are put into compound statements
     that become the actual branches of the conditional,
     so we need to lift the theorems to those compound statements.
     We generate the theorem for the `else' compound statement
     regardless of whether it is empty or not, for uniformity.
     The limit for each compound statement is
     1 plus the one for the block item list,
     because we need 1 to go from @(tsee exec-stmt)
     to the @(':compound') case and @(tsee exec-block-item-list).")
   (xdoc::p
    "We generate a theorem for the conditional statement,
     based on the theorems for the test and branches.
     We turn the ACL2 @(tsee if) into @(tsee if*),
     to prevent unwanted case splits in larger terms that may contain this term
     (as we generate C code from those larger terms).
     We use proof builder commands to split on this @(tsee if*).
     The limit for the conditional statement is
     one more than the sum of the ones for the branches;
     we could take one plus the maximum,
     but the sum avoids case splits.
     We include the compound recognizer @('booleanp-compound-recognizer')
     for the same reason explained in @(tsee atc-gen-expr-bool-from-type).")
   (xdoc::p
    "We lift the theorem for the conditional statement
     to a block item and to a singleton list of block items.")
   (xdoc::p
    "The generation of modular proofs in this code currently assumes that
     the @(tsee if) returns a single value,
     which is either the returned C value (if the C type is not @('void')),
     or a side-effected variables (if the C type is @('void')).
     This is reflected in the generated modular theorems.
     This will need to be generalized."))
  (b* (((reterr) (irr-stmt-gout))
       ((stmt-gin gin) gin)
       (wrld (w state))
       ((unless (equal then-type else-type))
        (reterr
         (msg "When generating C code for the function ~x0, ~
               two branches ~x1 and ~x2 of a conditional term ~
               have different types ~x3 and ~x4; ~
               use conversion operations, if needed, ~
               to make the branches of the same type."
              gin.fn then-term else-term then-type else-type)))
       (type then-type)
       (voidp (type-case type :void))
       (then-stmt (make-stmt-compound :items then-items))
       (else-stmt (make-stmt-compound :items else-items))
       (stmt (if (consp else-items)
                 (make-stmt-ifelse :test test-expr
                                   :then then-stmt
                                   :else else-stmt)
               (make-stmt-if :test test-expr
                             :then then-stmt)))
       (term `(if* ,test-term ,then-term ,else-term))
       ((when (not gin.proofs))
        (retok
         (make-stmt-gout
          :items (list (block-item-stmt stmt))
          :type type
          :term term
          :context gin.context
          :inscope gin.inscope
          :limit (pseudo-term-fncall
                  'binary-+
                  (list
                   (pseudo-term-quote 5)
                   (pseudo-term-fncall
                    'binary-+
                    (list then-limit else-limit))))
          :events (append test-events then-events else-events)
          :thm-name nil
          :thm-index gin.thm-index
          :names-to-avoid gin.names-to-avoid)))
       (thm-index gin.thm-index)
       (names-to-avoid gin.names-to-avoid)
       (then-stmt-thm (pack gin.fn '-correct- thm-index))
       (thm-index (1+ thm-index))
       ((mv then-stmt-thm names-to-avoid)
        (fresh-logical-name-with-$s-suffix
         then-stmt-thm nil names-to-avoid wrld))
       (else-stmt-thm (pack gin.fn '-correct- thm-index))
       (thm-index (1+ thm-index))
       ((mv else-stmt-thm names-to-avoid)
        (fresh-logical-name-with-$s-suffix
         else-stmt-thm nil names-to-avoid wrld))
       (valuep-when-type-pred (and (not voidp)
                                   (atc-type-to-valuep-thm type gin.prec-tags)))
       (then-stmt-limit `(binary-+ '1 ,then-limit))
       (else-stmt-limit `(binary-+ '1 ,else-limit))
       (then-uterm (untranslate$ then-term nil state))
       (else-uterm (untranslate$ else-term nil state))
       ((mv then-stmt-value then-stmt-type-formula &)
        (atc-gen-stmt-value-term-and-type-formula then-uterm
                                                  type
                                                  gin.affect
                                                  gin.inscope
                                                  gin.prec-tags))
       ((mv else-stmt-value else-stmt-type-formula &)
        (atc-gen-stmt-value-term-and-type-formula else-uterm
                                                  type
                                                  gin.affect
                                                  gin.inscope
                                                  gin.prec-tags))
       (then-context-end
        (atc-context-extend then-context-end
                            (list (make-atc-premise-compustate
                                   :var gin.compst-var
                                   :term `(exit-scope ,gin.compst-var)))))
       (else-context-end
        (atc-context-extend else-context-end
                            (list (make-atc-premise-compustate
                                   :var gin.compst-var
                                   :term `(exit-scope ,gin.compst-var)))))
       (then-new-compst (atc-contextualize-compustate gin.compst-var
                                                      then-context-start
                                                      then-context-end))
       (else-new-compst (atc-contextualize-compustate gin.compst-var
                                                      else-context-start
                                                      else-context-end))
       (then-stmt-exec-formula `(equal (exec-stmt ',then-stmt
                                                  ,gin.compst-var
                                                  ,gin.fenv-var
                                                  ,gin.limit-var)
                                       (mv ,then-stmt-value ,then-new-compst)))
       (then-stmt-exec-formula (atc-contextualize then-stmt-exec-formula
                                                  then-context-start
                                                  gin.fn
                                                  gin.fn-guard
                                                  gin.compst-var
                                                  gin.limit-var
                                                  then-stmt-limit
                                                  t
                                                  wrld))
       (else-stmt-exec-formula `(equal (exec-stmt ',else-stmt
                                                  ,gin.compst-var
                                                  ,gin.fenv-var
                                                  ,gin.limit-var)
                                       (mv ,else-stmt-value ,else-new-compst)))
       (else-stmt-exec-formula (atc-contextualize else-stmt-exec-formula
                                                  else-context-start
                                                  gin.fn
                                                  gin.fn-guard
                                                  gin.compst-var
                                                  gin.limit-var
                                                  else-stmt-limit
                                                  t
                                                  wrld))
       (then-stmt-type-formula (atc-contextualize then-stmt-type-formula
                                                  then-context-start
                                                  gin.fn
                                                  gin.fn-guard
                                                  nil
                                                  nil
                                                  nil
                                                  nil
                                                  wrld))
       (else-stmt-type-formula (atc-contextualize else-stmt-type-formula
                                                  else-context-start
                                                  gin.fn
                                                  gin.fn-guard
                                                  nil
                                                  nil
                                                  nil
                                                  nil
                                                  wrld))
       (then-stmt-formula `(and ,then-stmt-exec-formula
                                ,then-stmt-type-formula))
       (else-stmt-formula `(and ,else-stmt-exec-formula
                                ,else-stmt-type-formula))
       (then-stmt-hints
        `(("Goal" :in-theory '(exec-stmt-when-compound
                               (:e stmt-kind)
                               not-zp-of-limit-variable
                               (:e stmt-compound->items)
                               ,then-thm
                               mv-nth-of-cons
                               (:e zp)
                               (:e value-optionp)
                               value-optionp-when-valuep
                               ,@(and (not voidp)
                                      (list valuep-when-type-pred))
                               return-type-of-stmt-value-return
                               return-type-of-stmt-value-none
                               exit-scope-of-enter-scope
                               exit-scope-of-add-var
                               compustate-frames-number-of-add-frame-not-zero
                               compustate-frames-number-of-enter-scope-not-zero
                               compustate-frames-number-of-add-var-not-zero
                               compustatep-of-add-frame
                               compustatep-of-add-var
                               compustatep-of-enter-scope
                               uchar-array-length-of-uchar-array-write
                               schar-array-length-of-schar-array-write
                               ushort-array-length-of-ushort-array-write
                               sshort-array-length-of-sshort-array-write
                               uint-array-length-of-uint-array-write
                               sint-array-length-of-sint-array-write
                               ulong-array-length-of-ulong-array-write
                               slong-array-length-of-slong-array-write
                               ullong-array-length-of-ullong-array-write
                               sllong-array-length-of-sllong-array-write))))
       (else-stmt-hints
        `(("Goal" :in-theory '(exec-stmt-when-compound
                               (:e stmt-kind)
                               not-zp-of-limit-variable
                               (:e stmt-compound->items)
                               ,else-thm
                               mv-nth-of-cons
                               (:e zp)
                               (:e value-optionp)
                               value-optionp-when-valuep
                               ,@(and (not voidp)
                                      (list valuep-when-type-pred))
                               return-type-of-stmt-value-return
                               return-type-of-stmt-value-none
                               exit-scope-of-enter-scope
                               exit-scope-of-add-var
                               compustate-frames-number-of-add-frame-not-zero
                               compustate-frames-number-of-enter-scope-not-zero
                               compustate-frames-number-of-add-var-not-zero
                               compustatep-of-add-frame
                               compustatep-of-add-var
                               compustatep-of-enter-scope
                               uchar-array-length-of-uchar-array-write
                               schar-array-length-of-schar-array-write
                               ushort-array-length-of-ushort-array-write
                               sshort-array-length-of-sshort-array-write
                               uint-array-length-of-uint-array-write
                               sint-array-length-of-sint-array-write
                               ulong-array-length-of-ulong-array-write
                               slong-array-length-of-slong-array-write
                               ullong-array-length-of-ullong-array-write
                               sllong-array-length-of-sllong-array-write))))
       ((mv then-stmt-event &)
        (evmac-generate-defthm then-stmt-thm
                               :formula then-stmt-formula
                               :hints then-stmt-hints
                               :enable nil))
       ((mv else-stmt-event &)
        (evmac-generate-defthm else-stmt-thm
                               :formula else-stmt-formula
                               :hints else-stmt-hints
                               :enable nil))
       (if-stmt-thm (pack gin.fn '-correct- thm-index))
       (thm-index (1+ thm-index))
       ((mv if-stmt-thm names-to-avoid)
        (fresh-logical-name-with-$s-suffix if-stmt-thm nil names-to-avoid wrld))
       (if-stmt-limit
        `(binary-+ '1 (binary-+ ,then-stmt-limit ,else-stmt-limit)))
       (uterm (untranslate$ term nil state))
       ((mv if-stmt-value if-stmt-type-formula if-stmt-type-thms)
        (atc-gen-stmt-value-term-and-type-formula uterm
                                                  type
                                                  gin.affect
                                                  gin.inscope
                                                  gin.prec-tags))
       (test-uterm (untranslate$ test-term nil state))
       (new-compst `(if* ,test-uterm ,then-new-compst ,else-new-compst))
       (if-stmt-exec-formula `(equal (exec-stmt ',stmt
                                                ,gin.compst-var
                                                ,gin.fenv-var
                                                ,gin.limit-var)
                                     (mv ,if-stmt-value ,new-compst)))
       (if-stmt-exec-formula (atc-contextualize if-stmt-exec-formula
                                                gin.context
                                                gin.fn
                                                gin.fn-guard
                                                gin.compst-var
                                                gin.limit-var
                                                if-stmt-limit
                                                t
                                                wrld))
       (if-stmt-type-formula (atc-contextualize if-stmt-type-formula
                                                gin.context
                                                gin.fn
                                                gin.fn-guard
                                                nil
                                                nil
                                                nil
                                                nil
                                                wrld))
       (if-stmt-formula `(and ,if-stmt-exec-formula
                              ,if-stmt-type-formula))
       (test-type-pred (atc-type-to-recognizer test-type gin.prec-tags))
       (valuep-when-test-type-pred (pack 'valuep-when- test-type-pred))
       (value-kind-when-test-type-pred (pack 'value-kind-when- test-type-pred))
       (if-stmt-hints
        (if (consp else-items)
            `(("Goal" :in-theory '(exec-stmt-when-ifelse-and-true
                                   exec-stmt-when-ifelse-and-false
                                   (:e stmt-kind)
                                   not-zp-of-limit-variable
                                   (:e stmt-ifelse->test)
                                   ,test-thm
                                   ,@(and (not voidp)
                                          (list valuep-when-type-pred))
                                   (:e stmt-ifelse->then)
                                   ,then-stmt-thm
                                   (:e stmt-ifelse->else)
                                   ,else-stmt-thm
                                   ,valuep-when-test-type-pred
                                   booleanp-compound-recognizer
                                   expr-valuep-of-expr-value
                                   expr-value->value-of-expr-value
                                   value-fix-when-valuep
                                   ,valuep-when-test-type-pred
                                   apconvert-expr-value-when-not-value-array
                                   ,value-kind-when-test-type-pred
                                   uchar-array-length-of-uchar-array-write
                                   schar-array-length-of-schar-array-write
                                   ushort-array-length-of-ushort-array-write
                                   sshort-array-length-of-sshort-array-write
                                   uint-array-length-of-uint-array-write
                                   sint-array-length-of-sint-array-write
                                   ulong-array-length-of-ulong-array-write
                                   slong-array-length-of-slong-array-write
                                   ullong-array-length-of-ullong-array-write
                                   sllong-array-length-of-sllong-array-write
                                   mv-nth-of-cons
                                   (:e zp))))
          `(("Goal" :in-theory '(exec-stmt-when-if-and-true
                                 exec-stmt-when-if-and-false
                                 (:e stmt-kind)
                                 not-zp-of-limit-variable
                                 (:e stmt-if->test)
                                 ,test-thm
                                 ,@(and (not voidp)
                                        (list valuep-when-type-pred))
                                 (:e stmt-if->then)
                                 ,then-stmt-thm
                                 ,valuep-when-test-type-pred
                                 booleanp-compound-recognizer
                                 expr-valuep-of-expr-value
                                 expr-value->value-of-expr-value
                                 value-fix-when-valuep
                                 ,valuep-when-test-type-pred
                                 apconvert-expr-value-when-not-value-array
                                 ,value-kind-when-test-type-pred
                                 compustatep-of-add-var
                                 compustate-frames-number-of-add-var-not-zero
                                 exit-scope-of-enter-scope
                                 ,@if-stmt-type-thms
                                 uchar-array-length-of-uchar-array-write
                                 schar-array-length-of-schar-array-write
                                 ushort-array-length-of-ushort-array-write
                                 sshort-array-length-of-sshort-array-write
                                 uint-array-length-of-uint-array-write
                                 sint-array-length-of-sint-array-write
                                 ulong-array-length-of-ulong-array-write
                                 slong-array-length-of-slong-array-write
                                 ullong-array-length-of-ullong-array-write
                                 sllong-array-length-of-sllong-array-write
                                 mv-nth-of-cons
                                 (:e zp))))))
       (if-stmt-instructions
        `((casesplit ,(atc-contextualize
                       test-term
                       gin.context nil nil nil nil nil nil wrld))
          (claim ,(atc-contextualize `(test* ,test-term)
                                     gin.context nil nil nil nil nil nil wrld)
                 :hints (("Goal" :in-theory '(test*))))
          (drop 1)
          (claim ,(atc-contextualize
                   `(equal (if* ,test-term ,then-term ,else-term)
                           ,then-term)
                   gin.context nil nil nil nil nil nil wrld)
                 :hints (("Goal"
                          :in-theory '(acl2::if*-when-true test*))))
          (claim ,(atc-contextualize
                   `(equal ,new-compst ,then-new-compst)
                   gin.context nil nil gin.compst-var nil nil nil wrld)
                 :hints (("Goal" :in-theory '(acl2::if*-when-true test*))))
          (prove :hints ,if-stmt-hints)
          (claim ,(atc-contextualize `(test* (not ,test-term))
                                     gin.context nil nil nil nil nil nil wrld)
                 :hints (("Goal" :in-theory '(test*))))
          (drop 1)
          (claim ,(atc-contextualize
                   `(equal (if* ,test-term ,then-term ,else-term)
                           ,else-term)
                   gin.context nil nil nil nil nil nil wrld)
                 :hints (("Goal" :in-theory '(acl2::if*-when-false test*))))
          (claim ,(atc-contextualize
                   `(equal ,new-compst ,else-new-compst)
                   gin.context nil nil gin.compst-var nil nil nil wrld)
                 :hints (("Goal" :in-theory '(acl2::if*-when-false test*))))
          (prove :hints ,if-stmt-hints)))
       ((mv if-stmt-event &)
        (evmac-generate-defthm if-stmt-thm
                               :formula if-stmt-formula
                               :instructions if-stmt-instructions
                               :enable nil))
       ((mv item
            item-limit
            item-events
            item-thm-name
            thm-index
            names-to-avoid)
        (atc-gen-block-item-stmt stmt
                                 if-stmt-limit
                                 (append test-events
                                         then-events
                                         else-events
                                         (list then-stmt-event
                                               else-stmt-event
                                               if-stmt-event))
                                 if-stmt-thm
                                 (untranslate$ term nil state)
                                 type
                                 if-stmt-value
                                 new-compst
                                 (change-stmt-gin
                                  gin
                                  :thm-index thm-index
                                  :names-to-avoid names-to-avoid
                                  :proofs (and if-stmt-thm t))
                                 state))
       (new-context (atc-context-extend gin.context
                                        (list (make-atc-premise-compustate
                                               :var gin.compst-var
                                               :term new-compst))))
       (new-context (if (consp gin.affect)
                        (if (consp (cdr gin.affect))
                            (atc-context-extend new-context
                                                (list (make-atc-premise-cvalues
                                                       :vars gin.affect
                                                       :term uterm)))
                          (atc-context-extend new-context
                                              (list (make-atc-premise-cvalue
                                                     :var (car gin.affect)
                                                     :term uterm))))
                      new-context))
       ((mv new-inscope new-inscope-events thm-index names-to-avoid)
        (if voidp
            (atc-gen-if/ifelse-inscope gin.fn
                                       gin.fn-guard
                                       gin.inscope
                                       then-inscope
                                       else-inscope
                                       gin.context
                                       new-context
                                       (untranslate$ test-term nil state)
                                       (untranslate$ then-term nil state)
                                       (untranslate$ else-term nil state)
                                       gin.compst-var
                                       new-compst
                                       then-new-compst
                                       else-new-compst
                                       gin.prec-tags
                                       thm-index
                                       names-to-avoid
                                       wrld)
          (mv nil nil thm-index names-to-avoid))))
    (retok
     (atc-gen-block-item-list-one term
                                  type
                                  item
                                  item-limit
                                  (append item-events
                                          new-inscope-events)
                                  item-thm-name
                                  if-stmt-value
                                  new-compst
                                  new-context
                                  (and voidp new-inscope)
                                  (change-stmt-gin
                                   gin
                                   :thm-index thm-index
                                   :names-to-avoid names-to-avoid
                                   :proofs (and item-thm-name t))
                                  state)))
  :guard-hints
  (("Goal"
    :in-theory
    (e/d (acl2::true-listp-when-pseudo-event-form-listp-rewrite)
         ((:e tau-system))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-cfun-call-stmt ((called-fn symbolp)
                                (arg-terms pseudo-term-listp)
                                (arg-types type-listp)
                                (affect symbol-listp)
                                (extobjs symbol-listp)
                                (limit pseudo-termp)
                                (called-fn-guard symbolp)
                                (gin stmt-ginp)
                                state)
  :returns (mv erp (gout stmt-goutp))
  :short "Generate a C block item statement that consists of
          a call of a @('void') function."
  :long
  (xdoc::topstring
   (xdoc::p
    "We also generate a theorem about @(tsee exec-expr-call-or-asg)
     applied to the call expression.
     The limit is 2 more than the function's limit:
     it takes 1 to go from @(tsee exec-expr-call-or-asg)
     to @(tsee exec-expr-call),
     and another 1 to go from there to @(tsee exec-expr-pure-list).
     Since the limit term for the function is over the function's formal,
     we need to perform a substitution of the formals with the actuals."))
  (b* (((reterr) (irr-stmt-gout))
       (wrld (w state))
       ((stmt-gin gin) gin)
       ((when gin.loop-flag)
        (reterr
         (msg "A loop body must end with ~
               a recursive call on every path, ~
               but in the function ~x0 it ends with ~
               a call of ~x1 on arguments ~x2 instead."
              gin.fn called-fn arg-terms)))
       ((unless (equal gin.affect affect))
        (reterr
         (msg "When generating C code for the function ~x0, ~
               a call of the non-recursive function ~x1 ~
               has been encountered that affects ~x2, ~
               which differs from the variables ~x3 ~
               being affected here."
              gin.fn called-fn affect gin.affect)))
       ((erp (exprs-gout args))
        (atc-gen-expr-pure-list arg-terms
                                (make-exprs-gin
                                 :context gin.context
                                 :inscope gin.inscope
                                 :prec-tags gin.prec-tags
                                 :fn gin.fn
                                 :fn-guard gin.fn-guard
                                 :compst-var gin.compst-var
                                 :thm-index gin.thm-index
                                 :names-to-avoid gin.names-to-avoid
                                 :proofs gin.proofs)
                                state))
       ((unless (equal args.types arg-types))
        (reterr
         (msg "The function ~x0 with argument types ~x1 is applied to ~
               expression terms ~x2 returning ~x3. ~
               This is indicative of provably dead code, ~
               given that the code is guard-verified."
              called-fn arg-types arg-terms args.types)))
       (call-args (atc-remove-extobj-args args.exprs
                                          (formals+ called-fn wrld)
                                          extobjs))
       (call-expr
        (make-expr-call :fun (make-ident :name (symbol-name called-fn))
                        :args call-args))
       ((when (eq called-fn 'quote))
        (reterr (raise "Internal error: called function is QUOTE.")))
       (term `(,called-fn ,@args.terms))
       (uterm (untranslate$ term nil state))
       (fninfo (cdr (assoc-eq called-fn gin.prec-fns)))
       ((unless fninfo)
        (reterr (raise "Internal error: function ~x0 has no info." called-fn)))
       (called-fn-thm (atc-fn-info->correct-mod-thm fninfo))
       ((when (or (not gin.proofs)
                  (not called-fn-thm)))
        (retok (make-stmt-gout
                :items (list (block-item-stmt (stmt-expr call-expr)))
                :type (type-void)
                :term term
                :context gin.context
                :inscope gin.inscope
                :limit `(binary-+ '5 ,limit)
                :events args.events
                :thm-name nil
                :thm-index args.thm-index
                :names-to-avoid args.names-to-avoid)))
       (guard-lemma-name (pack gin.fn '-call- args.thm-index '-guard-lemma))
       ((mv guard-lemma-name names-to-avoid)
        (fresh-logical-name-with-$s-suffix guard-lemma-name
                                           nil
                                           args.names-to-avoid
                                           wrld))
       (thm-index (1+ args.thm-index))
       (guard-lemma-formula `(,called-fn-guard ,@args.terms))
       (guard-lemma-formula (atc-contextualize guard-lemma-formula
                                               gin.context
                                               gin.fn
                                               gin.fn-guard
                                               nil
                                               nil
                                               nil
                                               nil
                                               wrld))
       (guard-lemma-hints
        `(("Goal"
           :in-theory '(,gin.fn-guard ,called-fn-guard if* test*)
           :use (:guard-theorem ,gin.fn))))
       ((mv guard-lemma-event &)
        (evmac-generate-defthm guard-lemma-name
                               :formula guard-lemma-formula
                               :hints guard-lemma-hints
                               :enable nil))
       (call-thm-name (pack gin.fn '-correct- thm-index))
       ((mv call-thm-name names-to-avoid)
        (fresh-logical-name-with-$s-suffix
         call-thm-name nil names-to-avoid wrld))
       (thm-index (1+ thm-index))
       (called-formals (formals+ called-fn wrld))
       ((unless (equal (len called-formals) (len args.terms)))
        (reterr (raise "Internal error: ~x0 has formals ~x1 but actuals ~x2."
                       called-fn called-formals args.terms)))
       (call-limit `(binary-+ '2 ,limit))
       ((mv & new-compst)
        (atc-gen-call-result-and-endstate (type-void)
                                          gin.affect
                                          gin.inscope
                                          gin.compst-var
                                          uterm))
       (exec-formula `(equal (exec-expr-call-or-asg ',call-expr
                                                    ,gin.compst-var
                                                    ,gin.fenv-var
                                                    ,gin.limit-var)
                             ,new-compst))
       (exec-formula (atc-contextualize exec-formula
                                        gin.context
                                        gin.fn
                                        gin.fn-guard
                                        gin.compst-var
                                        gin.limit-var
                                        call-limit
                                        t
                                        wrld))
       ((mv type-formula inscope-thms)
        (atc-gen-term-type-formula uterm
                                   (type-void)
                                   gin.affect
                                   gin.inscope
                                   gin.prec-tags))
       (type-formula (atc-contextualize type-formula
                                        gin.context
                                        gin.fn
                                        gin.fn-guard
                                        nil
                                        nil
                                        nil
                                        nil
                                        wrld))
       (call-formula `(and ,exec-formula ,type-formula))
       (call-hints
        `(("Goal"
           :in-theory
           '(exec-expr-call-or-asg-when-call
             exec-expr-call-open
             exec-expr-pure-list-of-nil
             exec-expr-pure-list-when-consp
             ,@args.thm-names
             ,called-fn-thm
             ,guard-lemma-name
             ,@inscope-thms
             exec-fun-of-const-identifier
             (:e identp)
             (:e ident->name)
             apconvert-expr-value-when-not-value-array
             value-kind-when-ucharp
             value-kind-when-scharp
             value-kind-when-ushortp
             value-kind-when-sshortp
             value-kind-when-uintp
             value-kind-when-sintp
             value-kind-when-ulongp
             value-kind-when-slongp
             value-kind-when-ullongp
             value-kind-when-sllongp
             value-kind-when-uchar-arrayp
             value-kind-when-schar-arrayp
             value-kind-when-ushort-arrayp
             value-kind-when-sshort-arrayp
             value-kind-when-uint-arrayp
             value-kind-when-sint-arrayp
             value-kind-when-ulong-arrayp
             value-kind-when-slong-arrayp
             value-kind-when-ullong-arrayp
             value-kind-when-sllong-arrayp
             ,@(atc-string-taginfo-alist-to-value-kind-thms gin.prec-tags)
             valuep-when-ucharp
             valuep-when-scharp
             valuep-when-ushortp
             valuep-when-sshortp
             valuep-when-uintp
             valuep-when-sintp
             valuep-when-ulongp
             valuep-when-slongp
             valuep-when-ullongp
             valuep-when-sllongp
             valuep-when-uchar-arrayp
             valuep-when-schar-arrayp
             valuep-when-ushort-arrayp
             valuep-when-sshort-arrayp
             valuep-when-uint-arrayp
             valuep-when-sint-arrayp
             valuep-when-ulong-arrayp
             valuep-when-slong-arrayp
             valuep-when-ullong-arrayp
             valuep-when-sllong-arrayp
             ,@(atc-string-taginfo-alist-to-valuep-thms gin.prec-tags)
             type-of-value-when-ucharp
             type-of-value-when-scharp
             type-of-value-when-ushortp
             type-of-value-when-sshortp
             type-of-value-when-uintp
             type-of-value-when-sintp
             type-of-value-when-ulongp
             type-of-value-when-slongp
             type-of-value-when-ullongp
             type-of-value-when-sllongp
             type-of-value-when-uchar-arrayp
             type-of-value-when-schar-arrayp
             type-of-value-when-ushort-arrayp
             type-of-value-when-sshort-arrayp
             type-of-value-when-uint-arrayp
             type-of-value-when-sint-arrayp
             type-of-value-when-ulong-arrayp
             type-of-value-when-slong-arrayp
             type-of-value-when-ullong-arrayp
             type-of-value-when-sllong-arrayp
             ,@(atc-string-taginfo-alist-to-type-of-value-thms gin.prec-tags)
             expr-valuep-of-expr-value
             expr-value->value-of-expr-value
             value-fix-when-valuep
             (:e value-listp)
             value-listp-of-cons
             (:e value-optionp)
             (:e expr-kind)
             (:e expr-call->fun)
             (:e expr-call->args)
             not-zp-of-limit-variable
             not-zp-of-limit-minus-const
             compustatep-of-add-var
             compustatep-of-enter-scope
             compustatep-of-add-frame
             mv-nth-of-cons
             (:e zp)
             write-object-to-update-object
             write-object-okp-of-add-var
             write-object-okp-of-enter-scope
             write-object-okp-of-add-frame
             write-object-okp-of-update-object-same
             write-object-okp-of-update-object-disjoint
             write-object-okp-when-valuep-of-read-object-no-syntaxp
             value-array->length-when-uchar-arrayp
             value-array->length-when-schar-arrayp
             value-array->length-when-ushort-arrayp
             value-array->length-when-sshort-arrayp
             value-array->length-when-uint-arrayp
             value-array->length-when-sint-arrayp
             value-array->length-when-ulong-arrayp
             value-array->length-when-slong-arrayp
             value-array->length-when-ullong-arrayp
             value-array->length-when-sllong-arrayp
             read-object-of-objdesign-static-to-objdesign-of-var
             read-object-of-objdesign-static
             var-autop-of-add-frame
             var-autop-of-enter-scope
             var-autop-of-add-var
             var-autop-of-update-var
             var-autop-of-update-static-var
             var-autop-of-update-object
             write-static-var-to-update-static-var
             write-static-var-okp-of-add-var
             write-static-var-okp-of-enter-scope
             write-static-var-okp-of-add-frame
             write-static-var-okp-when-valuep-of-read-static-var))))
       ((mv call-event &) (evmac-generate-defthm call-thm-name
                                                 :formula call-formula
                                                 :hints call-hints
                                                 :enable nil))
       (stmt (stmt-expr call-expr))
       (stmt-limit `(binary-+ '1 ,call-limit))
       (stmt-thm-name (pack gin.fn '-correct- thm-index))
       ((mv stmt-thm-name names-to-avoid)
        (fresh-logical-name-with-$s-suffix stmt-thm-name
                                           nil
                                           names-to-avoid
                                           wrld))
       (thm-index (1+ thm-index))
       (stmt-exec-formula `(equal (exec-stmt ',stmt
                                             ,gin.compst-var
                                             ,gin.fenv-var
                                             ,gin.limit-var)
                                  (mv (stmt-value-none) ,new-compst)))
       (stmt-exec-formula (atc-contextualize stmt-exec-formula
                                             gin.context
                                             gin.fn
                                             gin.fn-guard
                                             gin.compst-var
                                             gin.limit-var
                                             stmt-limit
                                             t
                                             wrld))
       ((mv stmt-type-formula &) (atc-gen-term-type-formula uterm
                                                            (type-void)
                                                            gin.affect
                                                            gin.inscope
                                                            gin.prec-tags))
       (stmt-type-formula (atc-contextualize stmt-type-formula
                                             gin.context
                                             gin.fn
                                             gin.fn-guard
                                             nil
                                             nil
                                             nil
                                             nil
                                             wrld))
       (stmt-formula `(and ,stmt-exec-formula ,stmt-type-formula))
       (stmt-hints
        `(("Goal" :in-theory '(exec-stmt-when-expr
                               (:e stmt-kind)
                               (:e stmt-expr->get)
                               not-zp-of-limit-variable
                               ,call-thm-name
                               compustatep-of-update-var
                               compustatep-of-update-object
                               compustatep-of-update-static-var))))
       ((mv stmt-event &) (evmac-generate-defthm stmt-thm-name
                                                 :formula stmt-formula
                                                 :hints stmt-hints
                                                 :enable nil))
       ((mv item
            item-limit
            item-events
            item-thm-name
            thm-index
            names-to-avoid)
        (atc-gen-block-item-stmt stmt
                                 stmt-limit
                                 (append args.events
                                         (list guard-lemma-event
                                               call-event
                                               stmt-event))
                                 stmt-thm-name
                                 uterm
                                 (type-void)
                                 '(stmt-value-none)
                                 new-compst
                                 (change-stmt-gin
                                  gin
                                  :thm-index thm-index
                                  :names-to-avoid names-to-avoid
                                  :proofs (and stmt-thm-name t))
                                 state))
       (new-context (atc-context-extend gin.context
                                        (list (make-atc-premise-compustate
                                               :var gin.compst-var
                                               :term new-compst))))
       (premise (if (consp (cdr gin.affect))
                    (make-atc-premise-cvalues :vars gin.affect
                                              :term term)
                  (make-atc-premise-cvalue :var (car gin.affect)
                                           :term term)))
       (new-context (atc-context-extend new-context (list premise)))
       (new-inscope-rules
        `(objdesign-of-var-of-update-object-iff
          read-object-of-objdesign-of-var-to-read-var
          read-var-of-update-object
          compustate-frames-number-of-add-var-not-zero
          compustate-frames-number-of-update-object
          read-var-of-add-var
          remove-flexible-array-member-when-absent
          not-flexible-array-member-p-when-ucharp
          not-flexible-array-member-p-when-scharp
          not-flexible-array-member-p-when-ushortp
          not-flexible-array-member-p-when-sshortp
          not-flexible-array-member-p-when-uintp
          not-flexible-array-member-p-when-sintp
          not-flexible-array-member-p-when-ulongp
          not-flexible-array-member-p-when-slongp
          not-flexible-array-member-p-when-ullongp
          not-flexible-array-member-p-when-sllongp
          not-flexible-array-member-p-when-uchar-arrayp
          not-flexible-array-member-p-when-schar-arrayp
          not-flexible-array-member-p-when-ushort-arrayp
          not-flexible-array-member-p-when-sshort-arrayp
          not-flexible-array-member-p-when-uint-arrayp
          not-flexible-array-member-p-when-sint-arrayp
          not-flexible-array-member-p-when-ulong-arrayp
          not-flexible-array-member-p-when-slong-arrayp
          not-flexible-array-member-p-when-ullong-arrayp
          not-flexible-array-member-p-when-sllong-arrayp
          not-flexible-array-member-p-when-value-pointer
          value-fix-when-valuep
          valuep-when-ucharp
          valuep-when-scharp
          valuep-when-ushortp
          valuep-when-sshortp
          valuep-when-uintp
          valuep-when-sintp
          valuep-when-ulongp
          valuep-when-slongp
          valuep-when-ullongp
          valuep-when-sllongp
          valuep-when-uchar-arrayp
          valuep-when-schar-arrayp
          valuep-when-ushort-arrayp
          valuep-when-sshort-arrayp
          valuep-when-uint-arrayp
          valuep-when-sint-arrayp
          valuep-when-ulong-arrayp
          valuep-when-slong-arrayp
          valuep-when-ullong-arrayp
          valuep-when-sllong-arrayp
          ,@(atc-string-taginfo-alist-to-valuep-thms gin.prec-tags)
          read-object-of-update-object-same
          read-object-of-update-object-disjoint
          ,called-fn-thm
          ,guard-lemma-name
          ident-fix-when-identp
          identp-of-ident
          equal-of-ident-and-ident
          (:e str-fix)
          objdesign-of-var-of-update-static-var-iff
          read-object-of-objdesign-static
          read-var-to-read-static-var
          read-static-var-of-update-static-var
          var-autop-of-add-frame
          var-autop-of-enter-scope
          var-autop-of-add-var
          var-autop-of-update-var
          var-autop-of-update-static-var
          var-autop-of-update-object
          object-disjointp-commutative))
       ((mv new-inscope new-inscope-events names-to-avoid)
        (atc-gen-new-inscope gin.fn
                             gin.fn-guard
                             gin.inscope
                             new-context
                             gin.compst-var
                             new-inscope-rules
                             gin.prec-tags
                             thm-index
                             names-to-avoid
                             wrld))
       (thm-index (1+ thm-index))
       (events (append item-events
                       new-inscope-events))
       (gout (atc-gen-block-item-list-one term
                                          (type-void)
                                          item
                                          item-limit
                                          events
                                          item-thm-name
                                          '(stmt-value-none)
                                          new-compst
                                          new-context
                                          new-inscope
                                          (change-stmt-gin
                                           gin
                                           :thm-index thm-index
                                           :names-to-avoid names-to-avoid
                                           :proofs (and item-thm-name t))
                                          state)))
    (retok gout))
  :guard-hints
  (("Goal"
    :in-theory
    (e/d (length
          acl2::true-listp-when-pseudo-event-form-listp-rewrite
          alistp-when-atc-symbol-fninfo-alistp-rewrite)
         ((:e tau-system)))))
  :prepwork
  ((local (in-theory (disable mv-nth-of-cons)))
   (defrulel verify-guards-lemma
     (implies (symbol-listp x)
              (not (stringp x))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-stmt ((term pseudo-termp) (gin stmt-ginp) state)
  :returns (mv erp
               (gout stmt-goutp
                     :hints ; for speed
                     (("Goal"
                       :expand (atc-gen-stmt term gin state)
                       :in-theory (disable atc-gen-stmt)))))
  :short "Generate a C statement from an ACL2 term."
  :long
  (xdoc::topstring
   (xdoc::p
    "At the same time, we check that the term is a statement term,
     as described in the user documentation.")
   (xdoc::p
    "If the term is a conditional, there are two cases.
     If the test is @(tsee mbt),
     we recursively generate code just for the `then' branch,
     and then we delegate the rest to a separate function;
     note that we do not extend the context with the test,
     because the test is redundant, implied by the guard.
     If the test is not @(tsee mbt),
     we generate an @('if') statement
     (as a singleton block item list),
     with recursively generated compound statements as branches;
     the test expression is generated from the test term;
     we ensure that the two branches have the same type.
     When we process the branches,
     we extend the symbol table with a new empty scope for each branch.
     The calculation of the limit result is a bit more complicated in this case:
     we need 1 to go from @(tsee exec-block-item-list)
     to @(tsee exec-block-item),
     another 1 to go from that to @(tsee exec-stmt),
     and another 1 to go to the @(':if') or @(':ifelse') case there;
     the test is pure and so it needs no addition to the limit;
     since either branch may be taken,
     we return the sum of the limits for the two branches.
     More precisely, the limit recursively returned for each branch
     pertains to the block item list in the branch,
     but those are put into a compound statement;
     thus, we need to increase the recursively calculated limit
     by 1 to go from @(tsee exec-block-item-list) to @(tsee exec-block-item),
     and another 1 to go from there to @(tsee exec-stmt).
     In principle we could return the maximum from the two branches
     instead of their sum,
     but we want the limits to be
     linear combinations of sub-limits,
     so that ACL2's linear arithmetic can handle the reasoning about limits
     during the generated proofs.")
   (xdoc::p
    "If the term is a @(tsee mv-let),
     there are three cases.
     If the term involves a @('declar<n>') wrapper,
     we ensure that a variable with
     the same symbol name as the first bound variable
     is not already in scope
     (i.e. in the symbol table)
     and that the name is a portable ASCII identifier;
     we generate a declaration for the variable,
     initialized with the expression obtained
     from the term that the variable is bound to,
     which also determines the type of the variable,
     and which must affect the bound variables except the first one;
     the type must not be a pointer or array type
     (code generation fails if it is);
     we also ensure that the other variables are assignable.
     Otherwise, if the term involves an @('assign<n>') wrapper,
     we ensure that the first bound variable is assignable,
     which implies that it must be in scope,
     and we also ensure that it has the same type as the one in scope;
     we generate an assignment whose right-hand side is
     obtained from the unwrapped term,
     which must be an expression term returning a C value
     that affects the bound variables except the first one;
     we also ensure that the other variables are assignable.
     Otherwise, if the term involves no wrapper,
     we ensure that the bound variables are all assignable,
     and that the non-wrapped term has the form
     described in the user documentation;
     we generate code that affects the variables from that term.
     In all cases, we recursively generate the block items for the body
     and we put those just after the preceding code.
     We use the sum of the two limits as the overall limit:
     thus, after @(tsee exec-block-item-list) executes
     the block items for the bound term,
     it still has enough limit to execute the block items for the body term.")
   (xdoc::p
    "If the term is a @(tsee let), there are seven cases.
     If the binding has the form of a write to a pointed integer,
     we generate an assignment where the left-hand side
     uses the indirection unary operator.
     If the binding has the form of an array write,
     we generate an array assignment.
     If the binding has the form of a structure scalar member write,
     we generate an assignment to
     the member of the structure,
     by value or by pointer
     If the binding has the form of a structure array member write,
     we generate an assignment to
     the element of the member of the structure,
     by value or by pointer.
     The other three cases are similar to
     the three @(tsee mv-let) cases above.
     The limit is calculated as follows.
     For the case of the term representing code that affects variables,
     we add up the two limits,
     similarly to the @(tsee mv-let) case.
     For the other cases, we have one block item followed by block items.
     First, we need 1 to go from @(tsee exec-block-item-list)
     to @(tsee exec-block-item).
     Then we take the sum of the limit for the first block item
     and the limit for the remaining block items
     (in principle we could take the maximum,
     but see the discussion above for @(tsee if)
     for why we take the sum instead).
     The first block item is a declaration, an assignment, or a function call.
     If it is a declaration, we need 1 to go from @(tsee exec-block-item)
     to the @(':declon') case and to @(tsee exec-expr-call-or-pure),
     for which we get the limit.
     If it is an assignment, we need 1 to go from @(tsee exec-block-item)
     to the @(':stmt') case and to @(tsee exec-stmt),
     another 1 to go from there to the @(':expr') case
     and to @(tsee exec-expr-call-or-asg),
     another 1 to fo from there to @(tsee exec-expr-asg),
     and another 1 to go from there to @(tsee exec-expr-call-or-pure),
     for which we recursively get the limit.
     For the remaining block items, we need to add another 1
     to go from @(tsee exec-block-item-list) to its recursive call.")
   (xdoc::p
    "If the term is a single variable
     and @('affect') is a singleton list with that variable,
     there are two cases:
     if the loop flag is @('t'), it is an error;
     otherwise, we return nothing, because
     this is the end of a list of block items that affects that variable.
     We generate 1 as the limit,
     because we need 1 to go from @(tsee exec-block-item-list)
     to the empty list case.")
   (xdoc::p
    "If the term is an @(tsee mv), there are three cases.
     If the loop flag is @('t'), it is an error.
     Otherwise, if the arguments of @(tsee mv) are the @('affect') variables,
     we return nothing, because
     this is the end of a list of block items that affects that variable;
     we return 1 as the limit, for the same reason as the case above.
     Otherwise, if the @(tsee cdr) of the arguments of @(tsee mv)
     are the @('affect') variables,
     we treat the @(tsee car) of the arguments of @(tsee mv)
     as an expression term that must affect no variables,
     and generate a return statement for it.")
   (xdoc::p
    "If the term is a call of a recursive target function on its formals,
     different from the current function @('fn'),
     then the term represents a loop.
     The loop flag must be @('nil') for this to be allowed.
     We retrieve the associated loop statement and return it.
     We also retrieve the associated limit term,
     which, as explained in @(tsee atc-fn-info),
     suffices to execute @(tsee exec-stmt-while).
     But here we are executing lists of block items,
     so we need to add 1 to go from @(tsee exec-block-item-list)
     to the call to @(tsee exec-block-item),
     another 1 to go from there to the call to @(tsee exec-stmt),
     and another 1 to go from there to the call to @(tsee exec-stmt-while).")
   (xdoc::p
    "If the term is a call of the current function @('fn') on its formals,
     we ensure that the loop flag is @('t'),
     and we generate no code.
     This represents the conclusion of a loop body (on some path).")
   (xdoc::p
    "If the term is a call of
     a non-recursive target function that returns @('void'),
     the term represents an expression statement
     consisting of a call to the corresponding C function.
     The loop flag must be @('nil') for this to be allowed.
     We ensure that all the pointer and array arguments
     are equal to the formals,
     and that the variables affected by the called function are correct.
     We retrieve the limit term associated to the called function,
     which, as explained in @(tsee atc-fn-info),
     suffices to execute @(tsee exec-fun).
     But here we are executing lists of block items,
     so we need to add 1 to go from @(tsee exec-block-item-list)
     to the call of @(tsee exec-block-item),
     another 1 to go from there to the call of @(tsee exec-stmt),
     another 1 to go from there to the call of @(tsee exec-expr-call-or-asg),
     another 1 to go from there to the call of @(tsee exec-expr-call),
     and another 1 to go from there to the call of @(tsee exec-fun).")
   (xdoc::p
    "If the term does not have any of the forms above,
     we treat it as an expression term returning a C value.
     We ensure that the loop flag is @('nil').
     We also ensure that the expression affects
     the same variables as the statement term.
     For the limit, we need 1 to go from @(tsee exec-block-item-list)
     to @(tsee exec-block-item),
     another 1 to go from there to the @(':stmt') case and @(tsee exec-stmt),
     another 1 to go from there to the @(':return') case
     and @(tsee exec-expr-call-or-pure),
     for which we use the recursively calculated limit."))
  (b* (((reterr) (irr-stmt-gout))
       (wrld (w state))
       ((stmt-gin gin) gin)
       ((mv okp test-term then-term else-term) (fty-check-if-call term))
       ((when okp)
        (b* (((mv mbtp test-arg-term) (check-mbt-call test-term))
             ((when mbtp)
              (b* (((erp (stmt-gout then)) (atc-gen-stmt then-term gin state))
                   (gin (change-stmt-gin gin
                                         :thm-index then.thm-index
                                         :names-to-avoid then.names-to-avoid
                                         :proofs (and then.thm-name t))))
                (atc-gen-mbt-block-items test-arg-term
                                         then.term
                                         else-term
                                         then.items
                                         then.type
                                         then.limit
                                         then.events
                                         then.thm-name
                                         then.context
                                         then.inscope
                                         gin
                                         state)))
             ((erp (expr-gout test))
              (atc-gen-expr-bool test-term
                                 (make-expr-gin
                                  :context gin.context
                                  :inscope gin.inscope
                                  :prec-tags gin.prec-tags
                                  :fn gin.fn
                                  :fn-guard gin.fn-guard
                                  :compst-var gin.compst-var
                                  :thm-index gin.thm-index
                                  :names-to-avoid gin.names-to-avoid
                                  :proofs gin.proofs)
                                 state))
             ((erp (stmt-gout then)
                   then-context-start
                   then-context-end)
              (b* (((reterr)
                    (irr-stmt-gout) (irr-atc-context) (irr-atc-context))
                   (then-cond (untranslate$ test.term t state))
                   (then-premise (atc-premise-test then-cond))
                   (then-context-start
                    (atc-context-extend gin.context (list then-premise)))
                   ((mv then-inscope
                        then-enter-scope-context
                        then-enter-scope-events
                        thm-index
                        names-to-avoid)
                    (if test.thm-name
                        (atc-gen-enter-inscope gin.fn
                                               gin.fn-guard
                                               gin.inscope
                                               then-context-start
                                               gin.compst-var
                                               gin.prec-tags
                                               test.thm-index
                                               test.names-to-avoid
                                               wrld)
                      (mv (cons nil gin.inscope)
                          then-context-start
                          nil
                          test.thm-index
                          test.names-to-avoid)))
                   ((erp gout)
                    (atc-gen-stmt then-term
                                  (change-stmt-gin
                                   gin
                                   :context then-enter-scope-context
                                   :inscope then-inscope
                                   :thm-index thm-index
                                   :names-to-avoid names-to-avoid
                                   :proofs (and test.thm-name t))
                                  state))
                   (then-context-end (stmt-gout->context gout)))
                (retok
                 (change-stmt-gout gout
                                   :events (append
                                            then-enter-scope-events
                                            (stmt-gout->events gout)))
                 then-context-start
                 then-context-end)))
             ((erp (stmt-gout else)
                   else-context-start
                   else-context-end)
              (b* (((reterr)
                    (irr-stmt-gout) (irr-atc-context) (irr-atc-context))
                   (not-test-term `(not ,test.term))
                   (else-cond (untranslate$ not-test-term t state))
                   (else-premise (atc-premise-test else-cond))
                   (else-context-start
                    (atc-context-extend gin.context (list else-premise)))
                   ((mv else-inscope
                        else-enter-scope-context
                        else-enter-scope-events
                        thm-index
                        names-to-avoid)
                    (if test.thm-name
                        (atc-gen-enter-inscope gin.fn
                                               gin.fn-guard
                                               gin.inscope
                                               else-context-start
                                               gin.compst-var
                                               gin.prec-tags
                                               then.thm-index
                                               then.names-to-avoid
                                               wrld)
                      (mv (cons nil gin.inscope)
                          else-context-start
                          nil
                          then.thm-index
                          then.names-to-avoid)))
                   ((erp gout)
                    (atc-gen-stmt else-term
                                  (change-stmt-gin
                                   gin
                                   :context else-enter-scope-context
                                   :inscope else-inscope
                                   :thm-index thm-index
                                   :names-to-avoid names-to-avoid
                                   :proofs (and test.thm-name t))
                                  state))
                   (else-context-end (stmt-gout->context gout)))
                (retok
                 (change-stmt-gout gout
                                   :events (append
                                            else-enter-scope-events
                                            (stmt-gout->events gout)))
                 else-context-start
                 else-context-end))))
          (atc-gen-if/ifelse-stmt test.term then.term else.term
                                  test.expr then.items else.items
                                  test.type then.type else.type
                                  then.limit else.limit
                                  test.thm-name then.thm-name else.thm-name
                                  then-context-start else-context-start
                                  then-context-end else-context-end
                                  then.inscope else.inscope
                                  test.events then.events else.events
                                  (change-stmt-gin
                                   gin
                                   :thm-index else.thm-index
                                   :names-to-avoid else.names-to-avoid
                                   :proofs (and test.thm-name
                                                then.thm-name
                                                else.thm-name
                                                t))
                                  state)))
       ((mv okp var? vars indices val-term body-term wrapper? mv-var)
        (atc-check-mv-let term))
       ((when okp)
        (b* ((all-vars (if var? (cons var? vars) vars))
             (val-instance (fty-fsublis-var gin.var-term-alist val-term))
             (vals (atc-make-mv-nth-terms indices val-instance))
             (var-term-alist-body
              (atc-update-var-term-alist all-vars vals gin.var-term-alist))
             ((when (eq wrapper? 'declar))
              (b* ((var var?)
                   ((mv info? & errorp) (atc-check-var var gin.inscope))
                   ((when errorp)
                    (reterr
                     (msg "When generating C code for the function ~x0, ~
                           a new variable ~x1 has been encountered ~
                           that has the same symbol name as, ~
                           but different package name from, ~
                           a variable already in scope. ~
                           This is disallowed."
                          gin.fn var)))
                   ((when info?)
                    (reterr
                     (msg "The variable ~x0 in the function ~x1 ~
                           is already in scope and cannot be re-declared."
                          var gin.fn)))
                   ((unless (paident-stringp (symbol-name var)))
                    (reterr
                     (msg "The symbol name ~s0 of ~
                           the MV-LET variable ~x1 of the function ~x2 ~
                           must be a portable ASCII C identifier, ~
                           but it is not."
                          (symbol-name var) var gin.fn)))
                   ((mv info?-list innermostp-list)
                    (atc-get-vars-check-innermost vars gin.inscope))
                   ((when (member-eq nil info?-list))
                    (reterr
                     (msg "When generating C code for the function ~x0, ~
                           an attempt is made to modify the variables ~x1, ~
                           not all of which are in scope."
                          gin.fn vars)))
                   ((unless (atc-vars-assignablep
                             vars innermostp-list gin.affect))
                    (reterr
                     (msg "When generating C code for the function ~x0, ~
                           an attempt is made to modify the variables ~x1, ~
                           not all of which are assignable."
                          gin.fn vars)))
                   ((erp init.expr
                         init.type
                         & ; init.term
                         & ; init.result
                         & ; init.new-compst
                         init.limit
                         init.events
                         & ; init.thm-name
                         & ; init.new-inscope
                         & ; init.new-context
                         init.thm-index
                         init.names-to-avoid)
                    (atc-gen-expr val-term
                                  (change-stmt-gin gin :affect vars)
                                  state))
                   ((when (or (type-case init.type :pointer)
                              (type-case init.type :array)))
                    (reterr
                     (msg "When generating C code for the function ~x0, ~
                           the term ~x1 of type ~x2 ~
                           is being assigned to a new variable ~x3. ~
                           This is currently disallowed, ~
                           because it would create an alias."
                          gin.fn val-term init.type var)))
                   ((erp)
                    (atc-ensure-formals-not-lost vars
                                                 gin.affect
                                                 gin.typed-formals
                                                 gin.fn
                                                 wrld))
                   ((mv tyspec declor) (ident+type-to-tyspec+declor
                                        (make-ident :name (symbol-name var))
                                        init.type))
                   (declon (make-obj-declon :scspec (scspecseq-none)
                                            :tyspec tyspec
                                            :declor declor
                                            :init? (initer-single init.expr)))
                   (item (block-item-declon declon))
                   (varinfo (make-atc-var-info :type init.type
                                               :thm nil
                                               :externalp nil))
                   (inscope-body (atc-add-var var varinfo gin.inscope))
                   ((erp (stmt-gout body))
                    (atc-gen-stmt body-term
                                  (change-stmt-gin
                                   gin
                                   :var-term-alist var-term-alist-body
                                   :inscope inscope-body
                                   :thm-index init.thm-index
                                   :names-to-avoid init.names-to-avoid
                                   :proofs nil)
                                  state))
                   (type body.type)
                   (limit (pseudo-term-fncall
                           'binary-+
                           (list (pseudo-term-quote 3)
                                 (pseudo-term-fncall
                                  'binary-+
                                  (list init.limit body.limit))))))
                (retok (make-stmt-gout
                        :items (cons item body.items)
                        :type type
                        :term term
                        :context gin.context
                        :inscope gin.inscope
                        :limit limit
                        :events (append init.events body.events)
                        :thm-name nil
                        :thm-index body.thm-index
                        :names-to-avoid body.names-to-avoid))))
             ((when (eq wrapper? 'assign))
              (b* ((var var?)
                   ((mv info? innermostp &) (atc-check-var var gin.inscope))
                   ((unless info?)
                    (reterr
                     (msg "When generating C code for the function ~x0, ~
                           an attempt is being made ~
                           to modify a variable ~x1 not in scope."
                          gin.fn var)))
                   ((unless (atc-var-assignablep var innermostp gin.affect))
                    (reterr
                     (msg "When generating C code for the function ~x0, ~
                           an attempt is being made ~
                           to modify a non-assignable variable ~x1."
                          gin.fn var)))
                   (prev-type (atc-var-info->type info?))
                   ((erp rhs.expr
                         rhs.type
                         & ; rhs.term
                         & ; rhs.result
                         & ; rhs.new-compst
                         rhs.limit
                         rhs.events
                         & ; rhs.thm-name
                         & ; rhs.new-inscope
                         & ; rhs.new-context
                         rhs.thm-index
                         rhs.names-to-avoid)
                    (atc-gen-expr val-term
                                  (change-stmt-gin gin :affect vars)
                                  state))
                   ((unless (equal prev-type rhs.type))
                    (reterr
                     (msg "The type ~x0 of the term ~x1 ~
                           assigned to the LET variable ~x2 ~
                           of the function ~x3 ~
                           differs from the type ~x4 ~
                           of a variable with the same symbol in scope."
                          rhs.type val-term var gin.fn prev-type)))
                   ((erp)
                    (atc-ensure-formals-not-lost vars
                                                 gin.affect
                                                 gin.typed-formals
                                                 gin.fn
                                                 wrld))
                   ((when (type-case rhs.type :array))
                    (reterr
                     (msg "The term ~x0 to which the variable ~x1 is bound ~
                           must not have a C array type, ~
                           but it has type ~x2 instead."
                          val-term var rhs.type)))
                   ((when (type-case rhs.type :pointer))
                    (reterr
                     (msg "The term ~x0 to which the variable ~x1 is bound ~
                           must not have a C pointer type, ~
                           but it has type ~x2 instead."
                          val-term var rhs.type)))
                   (asg (make-expr-binary
                         :op (binop-asg)
                         :arg1 (expr-ident (make-ident :name (symbol-name var)))
                         :arg2 rhs.expr))
                   (stmt (stmt-expr asg))
                   (item (block-item-stmt stmt))
                   ((erp (stmt-gout body))
                    (atc-gen-stmt body-term
                                  (change-stmt-gin
                                   gin
                                   :var-term-alist var-term-alist-body
                                   :thm-index rhs.thm-index
                                   :names-to-avoid rhs.names-to-avoid
                                   :proofs nil)
                                  state))
                   (type body.type)
                   (limit (pseudo-term-fncall
                           'binary-+
                           (list (pseudo-term-quote 6)
                                 (pseudo-term-fncall
                                  'binary-+
                                  (list rhs.limit body.limit))))))
                (retok (make-stmt-gout
                        :items (cons item body.items)
                        :type type
                        :term term
                        :context gin.context
                        :inscope gin.inscope
                        :limit limit
                        :events (append rhs.events body.events)
                        :thm-name nil
                        :thm-index body.thm-index
                        :names-to-avoid body.names-to-avoid))))
             ((unless (eq wrapper? nil))
              (reterr
               (raise "Internal error: MV-LET wrapper is ~x0." wrapper?)))
             ((mv info?-list innermostp-list)
              (atc-get-vars-check-innermost vars gin.inscope))
             ((when (member-eq nil info?-list))
              (reterr
               (msg "When generating C code for the function ~x0, ~
                     an attempt is made to modify the variables ~x1, ~
                     not all of which are in scope."
                    gin.fn vars)))
             ((unless (atc-vars-assignablep vars innermostp-list gin.affect))
              (reterr
               (msg "When generating C code for the function ~x0, ~
                     an attempt is made to modify the variables ~x1, ~
                     not all of which are assignable."
                    gin.fn vars)))
             ((unless (atc-affecting-term-for-let-p val-term gin.prec-fns))
              (reterr
               (msg "When generating C code for the function ~x0, ~
                     an MV-LET has been encountered ~
                     whose term ~x1 to which the variables are bound ~
                     does not have the required form."
                    gin.fn val-term)))
             ((erp)
              (atc-ensure-formals-not-lost vars
                                           gin.affect
                                           gin.typed-formals
                                           gin.fn
                                           wrld))
             ((erp (stmt-gout xform))
              (atc-gen-stmt val-term
                            (change-stmt-gin gin
                                             :affect vars
                                             :loop-flag nil)
                            state))
             ((unless (type-case xform.type :void))
              (reterr
               (msg "When generating C code for the function ~x0, ~
                     an MV-LET has been encountered ~
                     whose term ~x1 to which the variables are bound ~
                     has the non-void type ~x2, ~
                     which is disallowed."
                    gin.fn val-term xform.type)))
             ((erp (stmt-gout body))
              (atc-gen-stmt body-term
                            (change-stmt-gin
                             gin
                             :context xform.context
                             :inscope xform.inscope
                             :var-term-alist var-term-alist-body
                             :thm-index xform.thm-index
                             :names-to-avoid xform.names-to-avoid
                             :proofs (and xform.thm-name t))
                            state))
             ((unless (equal (len all-vars) (len indices)))
              (reterr
               (raise "Internal error: ~
                       variables ~x0 and indices ~x1 ~
                       do not match in number."
                      all-vars indices)))
             (term (acl2::close-lambdas
                    (acl2::make-mv-let-call
                     mv-var all-vars indices xform.term body.term)))
             (items (append xform.items body.items))
             (type body.type)
             (limit (pseudo-term-fncall 'binary-+
                                        (list xform.limit body.limit))))
          (retok (make-stmt-gout
                  :items items
                  :type type
                  :term term
                  :context gin.context
                  :inscope gin.inscope
                  :limit limit
                  :events (append xform.events body.events)
                  :thm-name nil
                  :thm-index body.thm-index
                  :names-to-avoid body.names-to-avoid))))
       ((mv okp var val-term body-term wrapper?) (atc-check-let term))
       ((when okp)
        (b* ((val-instance (fty-fsublis-var gin.var-term-alist val-term))
             (var-term-alist-body
              (atc-update-var-term-alist (list var)
                                         (list val-instance)
                                         gin.var-term-alist))
             ((erp okp fn arg-term type) (atc-check-integer-write val-term))
             ((when okp)
              (b* (((erp asg-item
                         asg-term
                         asg-limit
                         asg-events
                         asg-thm
                         new-inscope
                         new-context
                         thm-index
                         names-to-avoid)
                    (atc-gen-block-item-integer-asg var
                                                    val-term
                                                    arg-term
                                                    type
                                                    fn
                                                    wrapper?
                                                    gin
                                                    state))
                   ((erp (stmt-gout body))
                    (atc-gen-stmt body-term
                                  (change-stmt-gin
                                   gin
                                   :context new-context
                                   :var-term-alist var-term-alist-body
                                   :inscope new-inscope
                                   :thm-index thm-index
                                   :names-to-avoid names-to-avoid
                                   :proofs (and asg-thm t))
                                  state))
                   (term (acl2::close-lambdas
                          `((lambda (,var) ,body.term) ,asg-term)))
                   (items-gout
                    (atc-gen-block-item-list-cons
                     term
                     asg-item
                     asg-limit
                     asg-events
                     asg-thm
                     body.items
                     body.limit
                     body.events
                     body.thm-name
                     body.type
                     body.context
                     body.inscope
                     (change-stmt-gin
                      gin
                      :thm-index body.thm-index
                      :names-to-avoid body.names-to-avoid
                      :proofs (and body.thm-name t))
                     state)))
                (retok items-gout)))
             ((erp okp fn sub-term elem-term elem-type)
              (atc-check-array-write var val-term))
             ((when okp)
              (b* (((erp asg-item
                         asg-term
                         asg-limit
                         asg-events
                         asg-thm
                         new-inscope
                         new-context
                         thm-index
                         names-to-avoid)
                    (atc-gen-block-item-array-asg var
                                                  val-term
                                                  sub-term
                                                  elem-term
                                                  elem-type
                                                  fn
                                                  wrapper?
                                                  gin
                                                  state))
                   ((erp (stmt-gout body))
                    (atc-gen-stmt body-term
                                  (change-stmt-gin
                                   gin
                                   :context new-context
                                   :var-term-alist var-term-alist-body
                                   :inscope new-inscope
                                   :thm-index thm-index
                                   :names-to-avoid names-to-avoid
                                   :proofs (and asg-thm t))
                                  state))
                   (term (acl2::close-lambdas
                          `((lambda (,var) ,body.term) ,asg-term)))
                   (items-gout
                    (atc-gen-block-item-list-cons
                     term
                     asg-item
                     asg-limit
                     asg-events
                     asg-thm
                     body.items
                     body.limit
                     body.events
                     body.thm-name
                     body.type
                     body.context
                     body.inscope
                     (change-stmt-gin
                      gin
                      :thm-index body.thm-index
                      :names-to-avoid body.names-to-avoid
                      :proofs (and body.thm-name t))
                     state)))
                (retok items-gout)))
             ((erp okp fn member-term tag member-name member-type)
              (atc-check-struct-write-scalar var val-term gin.prec-tags))
             ((when okp)
              (b* (((erp asg-item
                         asg-term
                         asg-limit
                         asg-events
                         asg-thm
                         new-inscope
                         new-context
                         thm-index
                         names-to-avoid)
                    (atc-gen-block-item-struct-scalar-asg var
                                                          val-term
                                                          tag
                                                          member-name
                                                          member-term
                                                          member-type
                                                          fn
                                                          wrapper?
                                                          gin
                                                          state))
                   ((erp (stmt-gout body))
                    (atc-gen-stmt body-term
                                  (change-stmt-gin
                                   gin
                                   :context new-context
                                   :var-term-alist var-term-alist-body
                                   :inscope new-inscope
                                   :thm-index thm-index
                                   :names-to-avoid names-to-avoid
                                   :proofs (and asg-thm t))
                                  state))
                   (term (acl2::close-lambdas
                          `((lambda (,var) ,body.term) ,asg-term)))
                   (items-gout
                    (atc-gen-block-item-list-cons
                     term
                     asg-item
                     asg-limit
                     asg-events
                     asg-thm
                     body.items
                     body.limit
                     body.events
                     body.thm-name
                     body.type
                     body.context
                     body.inscope
                     (change-stmt-gin
                      gin
                      :thm-index body.thm-index
                      :names-to-avoid body.names-to-avoid
                      :proofs (and body.thm-name t))
                     state)))
                (retok items-gout)))
             ((erp okp
                   fn
                   index-term
                   elem-term
                   tag
                   member-name
                   elem-type
                   flexiblep)
              (atc-check-struct-write-array var val-term gin.prec-tags))
             ((when okp)
              (b* (((erp asg-item
                         asg-term
                         asg-limit
                         asg-events
                         asg-thm
                         new-inscope
                         new-context
                         thm-index
                         names-to-avoid)
                    (atc-gen-block-item-struct-array-asg var
                                                         val-term
                                                         tag
                                                         member-name
                                                         index-term
                                                         elem-term
                                                         elem-type
                                                         flexiblep
                                                         fn
                                                         wrapper?
                                                         gin
                                                         state))
                   ((erp (stmt-gout body))
                    (atc-gen-stmt body-term
                                  (change-stmt-gin
                                   gin
                                   :context new-context
                                   :var-term-alist var-term-alist-body
                                   :inscope new-inscope
                                   :thm-index thm-index
                                   :names-to-avoid names-to-avoid
                                   :proofs (and asg-thm t))
                                  state))
                   (term (acl2::close-lambdas
                          `((lambda (,var) ,body.term) ,asg-term)))
                   (items-gout
                    (atc-gen-block-item-list-cons
                     term
                     asg-item
                     asg-limit
                     asg-events
                     asg-thm
                     body.items
                     body.limit
                     body.events
                     body.thm-name
                     body.type
                     body.context
                     body.inscope
                     (change-stmt-gin
                      gin
                      :thm-index body.thm-index
                      :names-to-avoid body.names-to-avoid
                      :proofs (and body.thm-name t))
                     state)))
                (retok items-gout)))
             ((mv info? innermostp errorp) (atc-check-var var gin.inscope))
             ((when errorp)
              (reterr
               (msg "When generating C code for the function ~x0, ~
                     a new variable ~x1 has been encountered ~
                     that has the same symbol name as, ~
                     but different package name from, ~
                     a variable already in scope. ~
                     This is disallowed."
                    gin.fn var)))
             ((when (eq wrapper? 'declar))
              (b* (((erp decl-item
                         decl-term
                         decl-limit
                         decl-events
                         decl-thm
                         new-inscope
                         new-context
                         thm-index
                         names-to-avoid)
                    (atc-gen-block-item-var-decl var
                                                 info?
                                                 val-term
                                                 gin
                                                 state))
                   ((erp (stmt-gout body))
                    (atc-gen-stmt body-term
                                  (change-stmt-gin
                                   gin
                                   :context new-context
                                   :var-term-alist var-term-alist-body
                                   :inscope new-inscope
                                   :thm-index thm-index
                                   :names-to-avoid names-to-avoid
                                   :proofs (and decl-thm t))
                                  state))
                   (term (acl2::close-lambdas
                          `((lambda (,var) ,body.term) ,decl-term)))
                   (items-gout
                    (atc-gen-block-item-list-cons
                     term
                     decl-item
                     decl-limit
                     decl-events
                     decl-thm
                     body.items
                     body.limit
                     body.events
                     body.thm-name
                     body.type
                     body.context
                     body.inscope
                     (change-stmt-gin
                      gin
                      :thm-index body.thm-index
                      :names-to-avoid body.names-to-avoid
                      :proofs (and body.thm-name t))
                     state)))
                (retok items-gout)))
             ((unless (atc-var-assignablep var innermostp gin.affect))
              (reterr
               (msg "When generating C code for the function ~x0, ~
                     an attempt is being made ~
                     to modify a non-assignable variable ~x1."
                    gin.fn var)))
             ((when (eq wrapper? 'assign))
              (b* (((erp asg-item
                         asg-term
                         asg-limit
                         asg-events
                         asg-thm
                         new-inscope
                         new-context
                         thm-index
                         names-to-avoid)
                    (atc-gen-block-item-var-asg var
                                                info?
                                                val-term
                                                gin
                                                state))
                   ((erp (stmt-gout body))
                    (atc-gen-stmt body-term
                                  (change-stmt-gin
                                   gin
                                   :context new-context
                                   :var-term-alist var-term-alist-body
                                   :inscope new-inscope
                                   :thm-index thm-index
                                   :names-to-avoid names-to-avoid
                                   :proofs (and asg-thm t))
                                  state))
                   (term (acl2::close-lambdas
                          `((lambda (,var) ,body.term) ,asg-term)))
                   (items-gout
                    (atc-gen-block-item-list-cons
                     term
                     asg-item
                     asg-limit
                     asg-events
                     asg-thm
                     body.items
                     body.limit
                     body.events
                     body.thm-name
                     body.type
                     body.context
                     body.inscope
                     (change-stmt-gin
                      gin
                      :thm-index body.thm-index
                      :names-to-avoid body.names-to-avoid
                      :proofs (and body.thm-name t))
                     state)))
                (retok items-gout)))
             ((unless (eq wrapper? nil))
              (reterr (raise "Internal error: LET wrapper is ~x0." wrapper?)))
             ((unless (atc-affecting-term-for-let-p val-term gin.prec-fns))
              (reterr
               (msg "When generating C code for the function ~x0, ~
                     we encountered a LET binding ~
                     of the variable ~x1 to the term ~x2 ~
                     that does not have any of the allowed forms. ~
                     See the user documentation."
                    gin.fn var val-term)))
             ((erp)
              (atc-ensure-formals-not-lost (list var)
                                           gin.affect
                                           gin.typed-formals
                                           gin.fn
                                           wrld))
             ((erp (stmt-gout xform))
              (atc-gen-stmt val-term
                            (change-stmt-gin gin
                                             :affect (list var)
                                             :loop-flag nil)
                            state))
             ((unless (type-case xform.type :void))
              (reterr
               (msg "When generating C code for the function ~x0, ~
                     a LET has been encountered ~
                     whose unwrapped term ~x1 ~
                     to which the variable is bound ~
                     has the non-void type ~x2, ~
                     which is disallowed."
                    gin.fn val-term xform.type)))
             ((erp (stmt-gout body))
              (atc-gen-stmt body-term
                            (change-stmt-gin
                             gin
                             :context xform.context
                             :inscope xform.inscope
                             :var-term-alist var-term-alist-body
                             :thm-index xform.thm-index
                             :names-to-avoid xform.names-to-avoid
                             :proofs (and xform.thm-name t))
                            state))
             (term (acl2::close-lambdas
                    `((lambda (,var) ,body.term) ,xform.term))))
          (if (consp body.items)
              (retok
               (atc-gen-block-item-list-append
                term
                xform.items
                body.items
                xform.limit
                body.limit
                xform.events
                body.events
                xform.thm-name
                body.thm-name
                body.type
                body.context
                body.inscope
                (change-stmt-gin
                 gin
                 :thm-index body.thm-index
                 :names-to-avoid body.names-to-avoid
                 :proofs (and body.thm-name t))
                state))
            (retok
             (change-stmt-gout xform :term term)))))
       ((when (and (pseudo-term-case term :var)
                   (equal gin.affect
                          (list (pseudo-term-var->name term)))))
        (if gin.loop-flag
            (reterr
             (msg "A loop body must end with ~
                   a recursive call on every path, ~
                   but in the function ~x0 it ends with ~x1 instead."
                  gin.fn term))
          (retok (atc-gen-block-item-list-none term gin state))))
       ((mv okp terms) (fty-check-list-call term))
       ((when okp)
        (b* (((unless (>= (len terms) 2))
              (reterr (raise "Internal error: MV applied to ~x0." terms)))
             ((when gin.loop-flag)
              (reterr
               (msg "A loop body must end with ~
                     a recursive call on every path, ~
                     but in the function ~x0 it ends with ~x1 instead."
                    gin.fn term))))
          (cond
           ((equal terms gin.affect)
            (retok (atc-gen-block-item-list-none (acl2::make-cons-nest terms)
                                                 gin
                                                 state)))
           ((equal (cdr terms) gin.affect)
            (atc-gen-return-stmt (car terms) t gin state))
           (t (reterr
               (msg "When generating C code for the function ~x0, ~
                     a term ~x0 has been encountered, ~
                     which is disallowed."
                    gin.fn term))))))
       ((mv okp loop-fn loop-args in-types loop-affect loop-stmt loop-limit)
        (atc-check-loop-call term gin.var-term-alist gin.prec-fns))
       ((when okp)
        (b* (((when gin.loop-flag)
              (reterr
               (msg "A loop body must end with ~
                     a recursive call on every path, ~
                     but in the function ~x0 it ends with ~x1 instead."
                    gin.fn term)))
             (formals (formals+ loop-fn wrld))
             ((unless (equal formals loop-args))
              (reterr
               (msg "When generating C code for the function ~x0, ~
                     a call of the recursive function ~x1 ~
                     has been encountered ~
                     that is not on its formals, ~
                     but instead on the arguments ~x2.
                     This is disallowed; see the ATC user documentation."
                    gin.fn loop-fn loop-args)))
             ((unless (equal gin.affect loop-affect))
              (reterr
               (msg "When generating C code for the function ~x0, ~
                     a call of the recursive function ~x1 ~
                     has been encountered
                     that represents a loop affecting ~x2, ~
                     which differs from the variables ~x3 ~
                     being affected here."
                    gin.fn loop-fn loop-affect gin.affect)))
             (infos (atc-get-vars formals gin.inscope))
             ((unless (atc-var-info-listp infos))
              (reterr
               (raise "Internal error: not all formals ~x0 have information ~x1."
                      formals infos)))
             (types (atc-var-info-list->type-list infos))
             ((unless (equal types in-types))
              (reterr
               (msg "The loop function ~x0 with input types ~x1 ~
                     is applied to terms ~x2 returning ~x3. ~
                     This is indicative of dead code under the guards, ~
                     given that the code is guard-verified."
                    loop-fn in-types formals types)))
             (limit (pseudo-term-fncall
                     'binary-+
                     (list (pseudo-term-quote 3)
                           loop-limit))))
          (retok (make-stmt-gout
                  :items (list (block-item-stmt loop-stmt))
                  :type (type-void)
                  :term term
                  :context gin.context
                  :inscope gin.inscope
                  :limit limit
                  :events nil
                  :thm-name nil
                  :thm-index gin.thm-index
                  :names-to-avoid gin.names-to-avoid))))
       ((when (equal term `(,gin.fn ,@(formals+ gin.fn wrld))))
        (if gin.loop-flag
            (retok (make-stmt-gout
                    :items nil
                    :type (type-void)
                    :term term
                    :context gin.context
                    :inscope gin.inscope
                    :limit (pseudo-term-quote 1)
                    :events nil
                    :thm-name nil
                    :thm-index gin.thm-index
                    :names-to-avoid gin.names-to-avoid))
          (reterr
           (msg "When generating code for the recursive function ~x0, ~
                 a recursive call to the loop function occurs ~
                 not at the end of the computation on some path."
                gin.fn))))
       ((erp okp
             called-fn
             arg-terms
             in-types
             out-type
             fn-affect
             extobjs
             limit
             called-fn-guard)
        (atc-check-cfun-call term gin.var-term-alist gin.prec-fns wrld))
       ((when (and okp
                   (type-case out-type :void)))
        (atc-gen-cfun-call-stmt called-fn
                                arg-terms
                                in-types
                                fn-affect
                                extobjs
                                limit
                                called-fn-guard
                                gin
                                state))
       ((when gin.loop-flag)
        (reterr
         (msg "A loop body must end with ~
               a recursive call on every path, ~
               but in the function ~x0 it ends with ~x1 instead."
              gin.fn term))))
    (atc-gen-return-stmt term nil gin state))

  :prepwork ((local (in-theory (disable equal-of-type-pointer
                                        equal-of-type-array
                                        equal-of-type-struct))))

  :measure (pseudo-term-count term)

  :hints (("Goal" :in-theory (enable o< o-finp)))

  :verify-guards nil ; done below

  ///

  (defrulel pseudo-termp-when-symbolp
    (implies (symbolp x)
             (pseudo-termp x))
    :enable pseudo-termp)

  (verify-guards atc-gen-stmt
    :hints (("Goal"
             :do-not '(preprocess) ; for speed
             :in-theory
             (e/d (pseudo-termp
                   length
                   true-listp-when-atc-var-info-option-listp-rewrite
                   acl2::true-listp-when-pseudo-event-form-listp-rewrite
                   alistp-when-atc-symbol-fninfo-alistp-rewrite
                   symbol-alistp-when-atc-symbol-fninfo-alistp)
                  (atc-gen-stmt))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod lstmt-gin
  :short "Inputs for C loop statement generation."
  :long
  (xdoc::topstring
   (xdoc::p
    "This does not include the term, which is passed as a separate input.")
   (xdoc::p
    "The @('measure-for-fn') component is the name of the
     locally generated measure function for
     the target function @('fn') that represents the loop."))
  ((context atc-contextp)
   (typed-formals atc-symbol-varinfo-alist)
   (inscope atc-symbol-varinfo-alist-list)
   (fn symbol)
   (fn-guard symbol)
   (compst-var symbol)
   (fenv-var symbol)
   (limit-var symbol)
   (measure-for-fn symbol)
   (measure-formals symbol-list)
   (prec-fns atc-symbol-fninfo-alist)
   (prec-tags atc-string-taginfo-alist)
   (prec-objs atc-string-objinfo-alist)
   (thm-index pos)
   (names-to-avoid symbol-list)
   (proofs bool))
  :pred lstmt-ginp)

;;;;;;;;;;;;;;;;;;;;

(fty::defprod lstmt-gout
  :short "Outputs for C loop statement generation."
  :long
  (xdoc::topstring
   (xdoc::p
    "The generated (loop) statement is @('stmt').
     We may actually split it into a test and body at some point.")
   (xdoc::p
    "We also return the test and body ACL2 terms.")
   (xdoc::p
    "We return two limit terms:
     one for just the body,
     and one for the whole loop."))
  ((stmt stmtp)
   (test-term pseudo-term)
   (body-term pseudo-term)
   (affect symbol-list)
   (limit-body pseudo-term)
   (limit-all pseudo-term)
   (events pseudo-event-form-list)
   (thm-name symbol)
   (thm-index pos)
   (names-to-avoid symbol-list))
  :pred lstmt-goutp)

;;;;;;;;;;

(defirrelevant irr-lstmt-gout
  :short "An irrelevant output for C loop statement generation."
  :type lstmt-goutp
  :body (make-lstmt-gout :stmt (irr-stmt)
                         :test-term nil
                         :body-term nil
                         :affect nil
                         :limit-body nil
                         :limit-all nil
                         :events nil
                         :thm-name nil
                         :thm-index 1
                         :names-to-avoid nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-loop-stmt ((term pseudo-termp) (gin lstmt-ginp) state)
  :returns (mv erp (gout lstmt-goutp))
  :short "Generate a C loop statement from an ACL2 term."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is called on loop terms (see user documentation).")
   (xdoc::p
    "The term must be an @(tsee if).
     If the test is an @(tsee mbt),
     test and `else' branch are ignored,
     while the `then' branch is recursively processed.
     Otherwise, the test must be an expression term returning a boolean
     from which we generate the loop test;
     the `then' branch must be a statement term,
     from which we generate the loop body;
     and the `else' branch must be either a single variable
     or an @(tsee mv) call on variables,
     which must be a subset of the function's formals,
     and from those variables we determine
     the variables affected by the loop.
     The statement term in the `then' branch
     must affect the variables found in the `else' branch.
     We return
     the term that represents the loop test,
     the term that represent the loop body
     and the variables affected by the loop.
     The loop test and body are used to generate more modular theorems.")
   (xdoc::p
    "Note that we push a new scope before processing the loop body.
     This is because the loop body is a block, which opens a new scope in C.")
   (xdoc::p
    "We return a limit that suffices
     to execute @(tsee exec-stmt-while) on (the test and body of)
     the loop statement, as follows.
     We need 1 to get to executing the test,
     which is pure and so does not contribute to the overall limit.
     If the test is true, we need to add the limit to execute the body.
     After that, @(tsee exec-stmt-while) is called recursively,
     decrementing the limit:
     given that we know that the loop function terminates,
     its measure must suffice as the limit.
     The loop function decreases the measure by at least 1 (maybe more)
     at every recursive call, so the limit does not decrease any faster,
     and we will never run out of the limit before the measure runs out.
     Thus the measure is an over-approximation for the limit, which is sound.
     We also note that the measure refers to the initial call of the function,
     while here it would suffice
     to take the measure at the first recursive call,
     but taking the whole measure is simpler,
     and again it is sound to over-appoximate.
     Note that we use the measure function for @('fn')
     that is generated by ATC,
     for the reasons explained in @(tsee atc-gen-loop-measure-fn).
     Besides the @('limit-all') result,
     which is the limit for the whole loop,
     we also return @('limit-body'), which is just for the loop body;
     this is in support for more modular proofs. "))
  (b* (((reterr) (change-lstmt-gout (irr-lstmt-gout)
                                    :stmt (make-stmt-while :test (irr-expr)
                                                           :body (irr-stmt))))
       ((lstmt-gin gin) gin)
       (wrld (w state))
       ((mv okp test-term then-term else-term) (fty-check-if-call term))
       ((unless okp)
        (reterr
         (msg "When generating C loop code for the recursive function ~x0, ~
               a term ~x1 that is not an IF has been encountered."
              gin.fn term)))
       ((mv mbtp &) (check-mbt-call test-term))
       ((when mbtp) (atc-gen-loop-stmt then-term gin state))
       ((erp (expr-gout test))
        (atc-gen-expr-bool test-term
                           (make-expr-gin
                            :context gin.context
                            :inscope gin.inscope
                            :prec-tags gin.prec-tags
                            :fn gin.fn
                            :fn-guard gin.fn-guard
                            :compst-var gin.compst-var
                            :thm-index gin.thm-index
                            :names-to-avoid gin.names-to-avoid
                            :proofs gin.proofs)
                           state))
       (formals (formals+ gin.fn wrld))
       ((mv okp affect)
        (b* (((when (member-eq else-term formals)) (mv t (list else-term)))
             ((mv okp terms) (fty-check-list-call else-term))
             ((when (and okp
                         (subsetp-eq terms formals)))
              (mv t terms)))
          (mv nil nil)))
       ((unless okp)
        (reterr
         (msg "The 'else' branch ~x0 of the function ~x1, ~
               which should be the non-recursive branch, ~
               does not have the required form. ~
               See the user documentation."
              else-term gin.fn)))
       ((erp (stmt-gout body))
        (atc-gen-stmt then-term
                      (make-stmt-gin
                       :context gin.context
                       :var-term-alist nil
                       :typed-formals gin.typed-formals
                       :inscope (cons nil gin.inscope)
                       :loop-flag t
                       :affect affect
                       :fn gin.fn
                       :fn-guard gin.fn-guard
                       :compst-var gin.compst-var
                       :prec-fns gin.prec-fns
                       :prec-tags gin.prec-tags
                       :prec-objs gin.prec-objs
                       :thm-index test.thm-index
                       :names-to-avoid test.names-to-avoid
                       :proofs (and test.thm-name t))
                      state))
       ((unless (type-case body.type :void))
        (reterr
         (raise "Internal error: ~
                 the loop body ~x0 of ~x1 ~ returns type ~x2."
                then-term gin.fn body.type)))
       (body-stmt (make-stmt-compound :items body.items))
       (stmt (make-stmt-while :test test.expr :body body-stmt))
       ((when (eq gin.measure-for-fn 'quote))
        (reterr
         (raise "Internal error: the measure function is QUOTE.")))
       (measure-call (pseudo-term-fncall gin.measure-for-fn
                                         gin.measure-formals))
       (limit `(binary-+ '1 (binary-+ ,body.limit ,measure-call))))
    (retok (make-lstmt-gout :stmt stmt
                            :test-term test-term
                            :body-term then-term
                            :affect affect
                            :limit-body body.limit
                            :limit-all limit
                            :thm-name nil
                            :thm-index body.thm-index
                            :names-to-avoid body.names-to-avoid)))
  :measure (pseudo-term-count term)
  :hints (("Goal" :in-theory (enable o< o-finp)))
  :guard-hints (("Goal" :in-theory (enable acl2::pseudo-fnsym-p)))
  ///

  (defret stmt-kind-of-atc-gen-loop-stmt
    (equal (stmt-kind (lstmt-gout->stmt gout)) :while)
    :hints (("Goal" :induct t))))
