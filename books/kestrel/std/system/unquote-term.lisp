; Standard System Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/util/define" :dir :system)
(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define unquote-term ((term (and (pseudo-termp term)
                                 (quotep term))))
  :returns value
  :parents (std/system)
  :short "Unquote a term that is a quoted constant."
  :long
  (xdoc::topstring
   (xdoc::p
    "The result is the quoted value, which may have any type.")
   (xdoc::p
    "This has the same effect of @(tsee unquote) on terms,
     but it is a function instead of a macro and it has a guard."))
  (unquote term))

(define unquote-term-list ((terms (and (pseudo-term-listp terms)
                                       (quote-listp terms))))
  :returns (values true-listp)
  :parents (std/system unquote-term)
  :short "Lift @(tsee unquote-term) to lists."
  (cond ((endp terms) nil)
        (t (cons (unquote-term (car terms))
                 (unquote-term-list (cdr terms))))))
