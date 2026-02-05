; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C2C")

(include-book "kestrel/event-macros/xdoc-constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ add-section-attr
  :parents (transformation-tools)
  :short "A C-to-C transformation to introduce ``section'' attributes."
  :long
  (xdoc::topstring
    (xdoc::evmac-section-intro
      (xdoc::p
        "This transformation adds ``section'' attributes "
        (xdoc::ahref
          "https://gcc.gnu.org/onlinedocs/gcc/Common-Function-Attributes.html"
          "[GCCM:6.4.1.1]")
        " according to some mapping
         from file-scope identifiers to section names.
         When there exist multiple declarations of the same function or object,
         a section attribute is added to <i>each</i> declaration.
         This is likely unnecessary,
         as attributes should typically be ``merged''
         (see @(see add-attributes))."))
    (xdoc::evmac-section-form
      (xdoc::codeblock
        "(add-section-attr const-old"
        "                  const-new"
        "                  :attr ... ; required"
        "  )"
        ))
    (xdoc::evmac-section-inputs
      (xdoc::desc
       "@('const-old')"
       (xdoc::p
         "Specifies the code to be transformed.")
       (xdoc::p
         "This must be a symbol that names an existing ACL2 constant
          that contains a code ensemble,
          i.e. a value of type @(tsee code-ensemble).
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
       "@(':attr')"
       (xdoc::p
         "An alist from @(see qualified-ident)s to strings.
          Each @(see qualified-ident) denotes a file-scope identifier.
          The string associated to the @(see qualified-ident) under the alist
          is the name of the section for the section attribute
          which is to be added."))))
  :order-subtopics t)
