; Standard System Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "dumb-occur-var-open")
(include-book "remove-trivial-vars")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-mv-let-call ((term pseudo-termp))
  :returns (mv (yes/no booleanp)
               (mv-var symbolp :hyp :guard)
               (vars symbol-listp :hyp :guard)
               (mv-term pseudo-termp :hyp :guard)
               (body-term pseudo-termp :hyp :guard))
  :parents (std/system/term-queries)
  :short "Check if a term is a (translated) call of @(tsee mv-let)."
  :long
  (xdoc::topstring
   (xdoc::p
    "In translated form, @('(mv-let (var1 ... varn) mv-term body-term)') is")
   (xdoc::codeblock
    "((lambda (mv)"
    "         ((lambda (var1 ... varn) body-term-trans)"
    "          (mv-nth '0 mv)"
    "          ..."
    "          (mv-nth 'n-1 mv)))"
    " mv-term-trans)")
   (xdoc::p
    "where @('mv-term-trans') and @('body-term-trans') are
     the translations of @('mv-term') and @('body-term').")
   (xdoc::p
    "This utility checks if a translated term has the form above;
     it also checks that @('mv') does not occur free in @('body-term')
     (via @(tsee dumb-occur-var-open) for greater flexibility).
     If all these checks pass, it returns @('t') as first result,
     and additionally the variable @('mv'),
     the list @('(var1 ... varn)'),
     the term @('mv-term-trans'),
     and the term @('body-term-trans').
     If the input term does not have that form,
     this utility returns @('nil') for each result.")
   (xdoc::p
    "If the input term has the form above,
     it is not necessarily the result of translating @(tsee mv-let).
     It could be the translation of
     @('(let ((mv mv-term))
          (let ((var1 (mv-nth 0 mv)) ... (varn (mv-nth n-1 mv)))
            mv-body))')
     instead;
     it depends on whether @('mv-term') is single-valued or multi-valued,
     and also on whether the terms is translated for execution or not.
     However, the result of translating @(tsee mv-let)
     necessarily has the form above.")
   (xdoc::p
    "Note, however, that lambda expressions are always closed
     in translated terms directly obtained from untranslated terms.
     ACL2 accomplishes this closure
     by adding formal paramaters to the lambda expressions
     for the otherwise free variables,
     and adding actual arguments identical to those variables;
     see @(tsee remove-trivial-vars).
     This means that the lambda expressions above may have extra variables.
     To ``correct'' for this, before examing the two lambda expressions,
     we remove all their formal parameters
     that are identical to the corresponding arguments,
     via @(tsee remove-trivial-vars)'s auxiliary function
     @('remove-trivial-vars-aux'), which does exactly that.
     We do not use @(tsee remove-trivial-vars) because that one
     removes the trivial variables at all levels,
     while here we only want to remove the ones
     from the two lambda expressions being examined.")
   (xdoc::p
    "Note also that, due to this lambda expression closure,
     the @('mv') variable is not always the symbol `@('mv')':
     if that symbol happens to be a free variable,
     ACL2's translation picks a different symbol
     for the first formal argument of the outer lambda expression above.
     For instance,")
   (xdoc::codeblock
    ":trans (let ((mv 0)) (mv-let (x y) (f mv) (list x y mv)))")
   (xdoc::p
    "produces a translated term with the symbol `@('mv0')'
     as the variable bound to the multiple value.
     This is why this utility returns this variable
     as one of its results.")
   (xdoc::p
    "This utility is essentially the inverse of @(tsee make-mv-let-call)."))
  (b* (((when (variablep term)) (mv nil nil nil nil nil))
       ((when (fquotep term)) (mv nil nil nil nil nil))
       ((unless (flambda-applicationp term)) (mv nil nil nil nil nil))
       (outer-lambda-expr (ffn-symb term))
       (formals (lambda-formals outer-lambda-expr))
       (actuals (fargs term))
       ((mv list-mv list-mv-term) (remove-trivial-vars-aux formals actuals))
       ((unless (and (consp list-mv)
                     (not (consp (cdr list-mv)))))
        (mv nil nil nil nil nil))
       (mv-var (car list-mv))
       ((unless (and (consp list-mv-term)
                     (not (consp (cdr list-mv-term)))))
        (mv nil nil nil nil nil))
       (mv-term (car list-mv-term))
       (inner-lambda-expr-call (lambda-body outer-lambda-expr))
       ((when (variablep inner-lambda-expr-call)) (mv nil nil nil nil nil))
       ((when (fquotep inner-lambda-expr-call)) (mv nil nil nil nil nil))
       ((unless (flambda-applicationp inner-lambda-expr-call))
        (mv nil nil nil nil nil))
       (inner-lambda-expr (ffn-symb inner-lambda-expr-call))
       (formals (lambda-formals inner-lambda-expr))
       (actuals (fargs inner-lambda-expr-call))
       ((mv vars mv-nths) (remove-trivial-vars-aux formals actuals))
       (body-term (lambda-body inner-lambda-expr))
       ((when (dumb-occur-var-open mv-var body-term)) (mv nil nil nil nil nil))
       ((unless (check-mv-let-call-aux mv-nths 0 mv-var))
        (mv nil nil nil nil nil)))
    (mv t mv-var vars mv-term body-term))

  :prepwork

  ((define check-mv-let-call-aux ((terms pseudo-term-listp)
                                  (index natp)
                                  (mv-var symbolp))
     :returns (yes/no booleanp)
     (or (endp terms)
         (and (equal (car terms) `(mv-nth ',index ,mv-var))
              (check-mv-let-call-aux (cdr terms) (1+ index) mv-var))))

   (local (include-book "std/typed-lists/symbol-listp" :dir :system))
   (local (include-book "std/typed-lists/pseudo-term-listp" :dir :system)))

  ///

  (local
   (defthm acl2-count-of-check-mv-let-call.mv-term-lemma
     (implies (consp x)
              (< (acl2-count (car x))
                 (acl2-count x)))
     :rule-classes :linear))

  (defret acl2-count-of-check-mv-let-call.mv-term
    (implies yes/no
             (< (acl2-count mv-term)
                (acl2-count term)))
    :rule-classes :linear)

  (defret acl2-count-of-check-mv-let-call.body-term
    (implies yes/no
             (< (acl2-count body-term)
                (acl2-count term)))
    :rule-classes :linear))
