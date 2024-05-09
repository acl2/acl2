; C Library
;
; Copyright (C) 2023 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2023 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "std/util/define" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(local (xdoc::set-default-parents atc-symbolic-execution-rules))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-syntaxp-hyp-for-expr-pure ((var symbolp))
  :returns (hyp pseudo-termp
                :hyp (symbolp var)
                :hints (("Goal" :in-theory (enable pseudo-termp
                                                   pseudo-term-listp))))
  :short "Construct a @(tsee syntaxp) hypothesis for
          a symbolic execution rule for pure expressions."
  :long
  (xdoc::topstring
   (xdoc::p
    "We use these hypotheses to ensure that
     certain execution subterms are rewritten
     to their shallow embedding counterparts
     before their enclosing terms are rewritten.
     These hypotheses require that the (sub)term in question
     does not contain any of the execution functions
     that are expected to be rewritten
     to their shallow embedding counterparts."))
  `(syntaxp (or (atom ,var)
                (not (member-eq (car ,var) '(exec-const
                                             exec-ident
                                             exec-address
                                             exec-indir
                                             exec-unary
                                             exec-binary-strict-pure
                                             exec-cast
                                             exec-arrsub
                                             exec-member
                                             exec-memberp
                                             exec-arrsub-of-member
                                             exec-arrsub-of-memberp
                                             exec-expr-pure
                                             test-value))))))
