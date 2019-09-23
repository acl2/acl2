; Standard System Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/util/defines" :dir :system)
(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines remove-progn-from-term
  :parents (std/system)
  :short "Turn every call of @(tsee prog2$) and @(tsee progn$) in a term
          into just its last argument."
  :long
  (xdoc::topstring
   (xdoc::p
    "In translated terms, @(tsee prog2$) and @(tsee progn$)
     have the form @('(return-last 'progn a b)').
     We turn that form into just @('b')."))

  (define remove-progn-from-term ((term pseudo-termp))
    :returns (new-term pseudo-termp :hyp (pseudo-termp term))
    (b* (((when (variablep term)) term)
         ((when (fquotep term)) term)
         (fn (ffn-symb term))
         (args (fargs term))
         ((when (and (eq fn 'return-last)
                     (equal (first args) '(quote progn))))
          (remove-progn-from-term (third args)))
         (new-fn (if (symbolp fn)
                     fn
                   (make-lambda (lambda-formals fn)
                                (remove-progn-from-term (lambda-body fn)))))
         (new-args (remove-progn-from-terms args)))
      (fcons-term new-fn new-args)))

  (define remove-progn-from-terms ((terms pseudo-term-listp))
    :returns (new-terms (and (pseudo-term-listp new-terms)
                             (equal (len new-terms) (len terms)))
                        :hyp (pseudo-term-listp terms))
    (b* (((when (endp terms)) nil)
         ((cons term terms) terms)
         (new-term (remove-progn-from-term term))
         (new-terms (remove-progn-from-terms terms)))
      (cons new-term new-terms))))
