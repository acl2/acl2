; Standard System Library
;
; Copyright (C) 2019 Regents of the University of Texas
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Main Author: Matt Kaufmann (kaufmann@cs.utexas.edu)
; Contributing Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/util/define" :dir :system)
(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define all-vars-in-untranslated-term (x (wrld plist-worldp))
  :returns (term "A @(tsee pseudo-termp).")
  :mode :program
  :parents (std/system/term-queries)
  :short "The variables free in the given untranslated term."
  :long
  (xdoc::topstring
   (xdoc::p
    "This function returns the variables of the given untranslated term.
     They are returned in reverse order of print occurrence,
     for consistency with the function, @(tsee all-vars).")
   (xdoc::p
    "The input is translated for reasoning,
     so restrictions for executability are not enforced.
     There is also no restriction on the input being
     in @(':')@(tsee logic) mode."))
  (let ((ctx 'all-vars-in-untranslated-term))
    (mv-let (erp term)
      (translate-cmp x
                     t ; stobjs-out
                     nil ; logic-modep (not required)
                     nil ; known-stobjs
                     ctx
                     wrld
                     (default-state-vars nil))
      (cond (erp (er hard erp "~@0" term))
            (t (all-vars term))))))
