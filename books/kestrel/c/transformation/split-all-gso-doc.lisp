; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C2C")

(include-book "kestrel/event-macros/xdoc-constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ split-all-gso
  :parents (transformation-tools)
  :short "A transformation to split all global struct objects."
  :long
  (xdoc::topstring
    (xdoc::evmac-section-intro
      (xdoc::p
        "This is a meta transformation which repeatedly applies @(see splitgso)
         to any global struct object it can."))
   (xdoc::evmac-section-form
     (xdoc::codeblock
       "(split-all-gso const-old"
       "               const-new"
       "               :gcc  ... ; optional"
       "               :ienv ... ; optional"
       "  )"
      ))
   (xdoc::evmac-section-inputs
     (xdoc::desc
       "@('const-old')"
       (xdoc::p
         "Specifies the code to be transformed.")
       (xdoc::p
         "This must be a symbol that names an existing ACL2 constant
          that contains a  validated translation unit ensemble,
          i.e. a value of type @(tsee transunit-ensemble)
          resulting from "
         (xdoc::seetopic "c$::validator" "validation")
         ", and in particular containing "
         (xdoc::seetopic "c$::validation-information" "validation information")
         ". This constant could result from @(tsee c$::input-files),
          or from some other "
         (xdoc::seetopic "transformation-tools" "transformation")
         "."))
     (xdoc::desc
       "@('const-new')"
       (xdoc::p
         "Specifies the name of the constant for the transformed code.")
       (xdoc::p
         "This must be a symbol that is valid name for a new ACL2 constant."))
     (xdoc::desc
       "@(':gcc') &mdash; default @('nil')"
       (xdoc::p
         "Boolean flag saying whether certain GCC extensions should be accepted
          or not. This is used when re-validating intermediate outputs (see
          @(see c$::validator))."))
     (xdoc::desc
       "@(':ienv') &mdash; default @('(c$::ienv-default)')"
       (xdoc::p
         "The "
         (xdoc::seetopic "c$::ienv" "implementation environment")
         " under which re-validation is performed."))))
  :order-subtopics t)
