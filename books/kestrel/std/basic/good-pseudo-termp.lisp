; Standard Basic Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "good-valuep")

(include-book "std/util/defines" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines good-pseudo-termp
  :parents (std/basic-extensions std/basic)
  :short "Check if a pseudo-term only contains good values,
          i.e. no bad atoms."
  :long
  (xdoc::topstring
   (xdoc::p
    "That is, check if every value of every quoted constant in the term
     satisfies @(tsee good-valuep)."))

  (define good-pseudo-termp ((term pseudo-termp))
    :returns (yes/no booleanp)
    (cond ((variablep term) t)
          ((fquotep term) (good-valuep (unquote term)))
          (t (and (good-pseudo-term-listp (fargs term))
                  (or (symbolp (ffn-symb term))
                      (good-pseudo-termp (lambda-body (ffn-symb term))))))))

  (define good-pseudo-term-listp ((terms pseudo-term-listp))
    :returns (yes/no booleanp)
    (or (endp terms)
        (and (good-pseudo-termp (car terms))
             (good-pseudo-term-listp (cdr terms))))))
