; Java Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

(include-book "kestrel/std/system/remove-mbe" :dir :system)
(include-book "kestrel/std/system/remove-progn" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atj-pre-translation-remove-return-last
  :parents (atj-pre-translation)
  :short "Pre-translation step performed by ATJ:
          removal of @(tsee return-last)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is done in both the deep and shallow embedding approach.")
   (xdoc::p
    "We selectively remove the @(':logic') or @(':exec') parts of @(tsee mbe)s
     (which are translated to @('(return-last 'mbe1-raw <exec> <logic>)'))
     based on the @(':guards') input.
     We remove all the non-last arguments of @(tsee prog2$)s and @(tsee progn$)s
     (which are translated to @('(return-last 'progn <non-last> <last>)')).")
   (xdoc::p
    "These are the only @(tsee return-last) forms
     that make it through input validation.
     Note that the non-last arguments of @(tsee prog2$) and @(tsee progn$)
     are checked to be free of side effects by ATJ,
     and thus their removal is safe and semantics-preserving."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-remove-return-last ((term pseudo-termp) (guards$ booleanp))
  :returns (new-term pseudo-termp :hyp (pseudo-termp term))
  :short "Remove all the @(tsee return-last)s from a term."
  (b* ((term (if guards$
                 (remove-mbe-logic term)
               (remove-mbe-exec term)))
       (term (remove-progn term)))
    term))
