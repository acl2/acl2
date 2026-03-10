; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "centaur/fty/top" :dir :system)
(include-book "std/util/defirrelevant" :dir :system)

(include-book "std/basic/controlled-configuration" :dir :system)
(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ preprocessor-options
  :parents (preprocessor)
  :short "Options for the @(see preprocessor)."
  :long
  (xdoc::topstring
   (xdoc::p
    "Our preprocessor can work in slightly different ways,
     under the control of user options.
     Here we define a data structure for these options.
     We start with something simple,
     and we will add more in the future."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod ppoptions
  :short "Fixtype of preprocessor options."
  :long
  (xdoc::topstring
   (xdoc::p
    "We support options to specify whether:")
   (xdoc::ul
    (xdoc::li
     "The preprocessing directives should be fully expanded,
      as opposed to preserved under suitable conditions.")
    (xdoc::li
     "Comments should be preserved or not.")
    (xdoc::li
     "Comments should be generated
      to trace the expansion of @('#include') directives.")
    (xdoc::li
     "The @('#error') and @('#warning') directives should be ignored,
      in the sense of not causing actual errors or warnings."))
   (xdoc::p
    "These options, except the last one,
     are explained in more detail in @(tsee input-files),
     which provides an interface to setting these options.
     The last option is for internal preprocessor use,
     not accessible via @(tsee input-files)."))
  ((full-expansion bool)
   (keep-comments bool)
   (trace-expansion bool)
   (no-errors/warnings bool))
  :pred ppoptionsp)

;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-ppoptions
  :short "Irrelevant preprocessor options."
  :type ppoptionsp
  :body (ppoptions nil nil nil nil))
