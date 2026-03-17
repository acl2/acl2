; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2026 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "std/util/define" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(include-book "std/basic/controlled-configuration" :dir :system)
(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define syntaxp-for-expr-pure ((var symbolp))
  :returns (hyp pseudo-termp
                :hyp (symbolp var)
                :hints (("Goal" :in-theory (enable pseudo-termp
                                                   pseudo-term-listp))))
  :parents (atc-symbolic-execution-rules)
  :short "Construct a @(tsee syntaxp) hypothesis for
          certain symbolic execution rules for pure expressions."
  :long
  (xdoc::topstring
   (xdoc::p
    "These hypotheses can be used to ensure that
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
                                             test-value)))))
  :hooks nil)
