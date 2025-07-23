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

(defxdoc+ split-fn
  :parents (transformation-tools)
  :short "A C-to-C transformation to split a function in two."
  :long
  (xdoc::topstring
    (xdoc::evmac-section-intro
      (xdoc::p
        "This transformation splits out the second half of a function. The
         function body of the original function is truncated at the split
         point, at which point it calls the new function containing the
         remainder of the statements. Necessary values are passed by pointer to
         the split-out function."))
    (xdoc::evmac-section-form
      (xdoc::codeblock
        "(split-fn const-old"
        "          const-new"
        "          :target      ... ; required"
        "          :new-fn      ... ; required"
        "          :split-point ... ; required"
        "  )"
        ))
    (xdoc::evmac-section-inputs
      (xdoc::desc
       "@('const-old')"
       (xdoc::p
         "Specifies the code to be transformed.")
       (xdoc::p
         "This must be a symbol that names an existing ACL2 constant
          that contains a translation unit ensemble,
          i.e. a value of type @(tsee transunit-ensemble).
          This constant could result from @(tsee c$::input-files),
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
       "@(':target')"
       (xdoc::p
         "A string denoting the identifier of the function which should be
          split.")
       (xdoc::box
         (xdoc::b "Note")
         ": There is currently no way to specify the translation unit to allow
          for disambiguation of functions of the same name with internal
          linkage. Eventually, a @(':target-filepath') keyword argument will be
          introduced to accommodate this case. Until then, the transformation
          will apply to all functions of the specified name."))
     (xdoc::desc
       "@(':new-fn')"
       (xdoc::p
         "A string denoting the identifier which shall be used as the name of
          the new function introduced by the transformation.")
       (xdoc::box
         (xdoc::b "Note")
         ": This identifier should be free to avoid name conflict, but this
          condition is not current checked."))
     (xdoc::desc
       "@(':split-point')"
       (xdoc::p
         "A natural number indicating the position in the function body at
          which to split. This is the number of top-level "
          (xdoc::seetopic "c$::block-item" "block items")
         " in the function body before the split point. Splits within nested
          statement blocks are not yet supported."))))
  :order-subtopics t)
