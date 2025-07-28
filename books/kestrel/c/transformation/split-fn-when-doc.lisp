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

(defxdoc+ split-fn-when
  :parents (transformation-tools)
  :short "A C-to-C transformation to split functions according to some trigger
          pattern."
  :long
  (xdoc::topstring
    (xdoc::evmac-section-intro
      (xdoc::p
        "This transformation traverse finds location in functions which match
         the provided trigger pattern. When such a pattern is found, the
         function is split (see @(see split-fn)) and the transformation
         continues looking for further pattern matches. The transformation
         finishes when no more trigger patterns are found."))
    (xdoc::evmac-section-form
      (xdoc::codeblock
        "(split-fn-when const-old"
        "               const-new"
        "               :triggers ... ; required"
        "  )"
        ))
    (xdoc::evmac-section-inputs
      (xdoc::desc
       "@('const-old')"
       (xdoc::p
         "Specifies the code to be transformed.")
       (xdoc::p
         "This must be a symbol that names an existing ACL2 constant that
          contains a translation unit ensemble. This constant could result
          from @(tsee c$::input-files), or from some other "
         (xdoc::seetopic "transformation-tools" "transformation")
         "."))
     (xdoc::desc
       "@('const-new')"
       (xdoc::p
         "Specifies the name of the constant for the transformed code.")
       (xdoc::p
         "This must be a symbol that is valid name for a new ACL2 constant."))
      (xdoc::desc
        "@(':triggers')"
        (xdoc::p
          "A string or string list representing identifiers. A statement
           matches the trigger pattern if it is a simple function call whose
           function is an identifier included in this string list. The
           split-point inferred from such a statement will be immediately
           before the statement. The first statement of a function will never
           match the trigger pattern, as splitting in such cases would do
           nothing. Only top-level statements of a function body will current
           match a trigger pattern (e.g., statements within an @('if') then/else
           block will not be considered).")
        (xdoc::p
          "This current representation of a trigger pattern is very limited. It
           may be expanded in the future to describe various types of
           expressions at various points in a statement, and causing a split
           either before or after the statement."))))
  :order-subtopics t
  :default-parent t)
