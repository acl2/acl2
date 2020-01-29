; Standard System Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "check-list-call")
(include-book "quote-term-list")
(include-book "unquote-term")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define mvify ((term pseudo-termp))
  :returns (new-term pseudo-termp :hyp :guard)
  :parents (std/system/term-transformations)
  :short "Turn a single-value term into a multi-value term."
  :long
  (xdoc::topstring
   (xdoc::p
    "When a multi-value term is translated by ACL2,
     it looks like a single-value term,
     i.e. @('(mv x y z)') and @('(list x y x)')
     are the same in translated form.
     Thus, if the term, or a transformed version of it,
     is untranslated (via @(tsee untranslate)) back,
     the result is a single-value term, unlike the original term.")
   (xdoc::p
    "This utility can help obtain a multi-value untranslated term instead,
     by turning certain translated occurrences of @('(list ...)')
     into occurrences of @('(mv ...)') with the same arguments.
     The resulting term is not quite a valid translated term
     because @(tsee mv) is a macro and not a function,
     but it is a pseudo-term,
     and @(tsee untranslate) should handle occurrences of @(tsee mv)
     as if it were a function (i.e. by leaving it unchanged).")
   (xdoc::p
    "This utility operates on translated terms,
     assuming that they are obtained
     either by translating valid untranslated multi-value terms,
     or by transforming translated multi-value terms
     in a way that preserves well-formedness with respect to multiple values
     (i.e. that they always return
     lists of two or more terms of the same length).")
   (xdoc::p
    "Certain term transformations may turn
     a translated @('(list ...)') term whose arguments are all quoted constants
     into a single quoted list constant with the unquoted elements.
     For this reason, this utility also turns quoted list constants
     into @(tsee mv) calls on the quoted elements.")
   (xdoc::p
    "This utility replaces occurrences of translated @('(list ...)') subterms,
     or of quoted list constants,
     at the ``leaves'' of the term.
     We only consider @(tsee if), @(tsee return-last), and lambda applications
     as non-leaf tree nodes:
     @(tsee if) has two subtrees for the `then' and `else' arguments;
     @(tsee return-last) has two subtrees for the second and  third arguments;
     and a lambda application has one subtree for the body.
     In other words, we descend down (certain arguments of)
     @(tsee if)s and @(tsee return-last)s,
     and we descend down bodies of lambda expressions.
     This is of course related to the fact that
     the value of the built-in constant @('*stobjs-out-invalid*')
     is @('(if return-last)').")
   (xdoc::p
    "All the other function calls are left unchanged
     (i.e. they are considered tree leaves),
     because presumably such functions already return multi-value results.
     If a variable or non-list quoted constant is encountered, it is an error:
     a variable or non-list quoted constant can never return a multiple value;
     this utility must be applied to a term that returns multiple values,
     which excludes variables and non-list quoted constants,
     and the recursion will stop before reaching
     any variable or non-list quoted constant
     if the term satisfies the assumptions stated earlier."))
  (b* (((when (variablep term))
        (raise "Unexpected term: ~x0." term))
       ((when (fquotep term))
        (b* ((const (unquote-term term)))
          (if (true-listp const)
              (fcons-term 'mv (quote-term-list const))
            (raise "Unexpected term: ~x0." term))))
       (fn (ffn-symb term))
       ((when (flambdap fn))
        (fcons-term (make-lambda (lambda-formals fn)
                                 (mvify (lambda-body fn)))
                    (fargs term)))
       ((when (eq fn 'if))
        (fcons-term 'if
                    (list (fargn term 1)
                          (mvify (fargn term 2))
                          (mvify (fargn term 3)))))
       ((when (eq fn 'return-last))
        (fcons-term 'return-last
                    (list (fargn term 1)
                          (mvify (fargn term 2))
                          (mvify (fargn term 3)))))
       ((mv list-call-p args) (check-list-call term)))
    (if list-call-p
        (fcons-term 'mv args)
      term)))
