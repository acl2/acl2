; Standard System Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/util/define" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(include-book "dumb-occur-var-open")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-mv-let-call ((term pseudo-termp))
  :returns (mv (yes/no booleanp)
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
     If it does, it returns @('t') as first result,
     and additionally the list @('(var1 ... varn)'),
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
    "This utility is essentially the inverse of @(tsee make-mv-let-call)."))
  (b* (((when (variablep term)) (mv nil nil nil nil))
       ((when (fquotep term)) (mv nil nil nil nil))
       (lambda-mv (ffn-symb term))
       ((unless (flambdap lambda-mv)) (mv nil nil nil nil))
       (list-mv (lambda-formals lambda-mv))
       ((unless (equal list-mv (list 'mv))) (mv nil nil nil nil))
       (mv-term (fargn term 1))
       (lambda-vars-of-mv-nths (lambda-body lambda-mv))
       ((when (variablep lambda-vars-of-mv-nths)) (mv nil nil nil nil))
       ((when (fquotep lambda-vars-of-mv-nths)) (mv nil nil nil nil))
       (lambda-vars (ffn-symb lambda-vars-of-mv-nths))
       ((unless (flambdap lambda-vars)) (mv nil nil nil nil))
       (vars (lambda-formals lambda-vars))
       (body-term (lambda-body lambda-vars))
       ((when (dumb-occur-var-open 'mv body-term)) (mv nil nil nil nil))
       (mv-nths (fargs lambda-vars-of-mv-nths))
       ((unless (check-mv-let-call-aux mv-nths 0)) (mv nil nil nil nil)))
    (mv t vars mv-term body-term))

  :prepwork
  ((define check-mv-let-call-aux ((terms pseudo-term-listp) (index natp))
     :returns (yes/no booleanp)
     (or (endp terms)
         (and (equal (car terms) `(mv-nth ',index mv))
              (check-mv-let-call-aux (cdr terms) (1+ index)))))))
