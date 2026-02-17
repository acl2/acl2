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
    "We support the following options:")
   (xdoc::ul
    (xdoc::li
     "One to specify whether
      the preprocessing directives should be fully expanded,
      as typical C preprocessors do,
      as opposed to preserved under suitable conditions.")
    (xdoc::li
     "One to specify whether comments should be preserved or not.")))
  ((full-expansion bool)
   (keep-comments bool))
  :pred ppoptionsp)

;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-ppoptions
  :short "Irrelevant preprocessor options."
  :type ppoptionsp
  :body (ppoptions nil nil))
