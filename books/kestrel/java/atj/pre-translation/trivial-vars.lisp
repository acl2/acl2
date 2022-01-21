; Java Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

(include-book "kestrel/std/system/remove-trivial-vars" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc atj-pre-translation-trivial-vars
  :parents (atj-pre-translation)
  :short "Pre-translation step performed by ATJ:
          removal of all the trivial lambda-bound variables."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is done only in the shallow embedding.")
   (xdoc::p
    "We remove all the lambda-bound variables,
     and corresponding actual arguments,
     that are identical to the corresponding actual arguments.
     See the discussion in @(tsee remove-trivial-vars),
     which is the utility that we use
     to accomplish this pre-translation step.")
   (xdoc::p
    "This pre-translation step makes terms simpler to work with
     (for the purpose of ATJ)
     by only keeping the ``true'' @(tsee let)s in a term
     (which are lambda expressions in translated terms),
     avoiding the ``artificial'' ones to close the lambda expressions.
     Indeed, @(tsee let) terms are generally not closed in other languages,
     or even in ACL2's untranslated terms.")))
