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

(defxdoc+ specialize
  :parents (transformation-tools)
  :short "A C-to-C transformation to specialize a function."
  :long
  (xdoc::topstring
    (xdoc::evmac-section-intro
      (xdoc::p
        "This transformation specializes a function by moving one of its
         parameters to a declaration at the top of the function body,
         initialized to some constant.")
      (xdoc::p
        "Note that this modifies the target function; it does not make a copy
         of the function. If you want to specialize a copy of a function, first
         employ the @(see copy-fn) transformation.")
      (xdoc::p
        "It is often desirable to propagate constants and eliminate dead code
         after specializing. The @(see specialize) transformation does not
         implement such behavior. Eventually, we will want to implement
         separate constant propagation and dead code elimination
         transformations."))
    (xdoc::evmac-section-form
      (xdoc::codeblock
        "(specialize const-old"
        "            const-new"
        "            :target ... ; required"
        "            :param  ... ; required"
        "            :const  ... ; required"
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
       "@(:target)"
       (xdoc::p
         "A string denoting the identifier of the function which should be
          specialize.")
       (xdoc::box
         (xdoc::b "Note")
         ": There is currently no way to specify the translation unit to allow
          for disambiguation of functions of the same name with internal
          linkage. Eventually, a @(':target-filepath') keyword argument will be
          introduced to accommodate this case. Until then, the transformation
          will apply to all functions of the specified name."))
     (xdoc::desc
       "@(:param)"
       (xdoc::p
         "A string denoting the identifier of the function parameter which is
          to be specialized."))
     (xdoc::desc
       "@(:const)"
       (xdoc::p
         "An @(tsee c$::exprp) which denotes the value that the @(':param')
          will be specialized to.")
       (xdoc::box
         (xdoc::b "Note")
         ": This value should be a constant, but this condition is not
          currently checked.")))
    (xdoc::section
      "Example"
      (xdoc::p
        "For a concrete example, consider the following C code:")
      (xdoc::codeblock
        "int foo(int y, int z) {"
        "  int x = 5;"
        "  return x + y - z;"
        "}")
      (xdoc::p
        "Assuming this function exists in a translation unit ensemble stored in
         the constant @('foo'), we can specialize the argument @('y') with the
         constant @('1') with the following use of @(tsee specialize).")
      (xdoc::codeblock
        "(specialize *old*"
        "            *new*"
        "            :target \"foo\""
        "            :param  \"y\""
        "            :const  (c$::expr-const"
        "                      (c$::const-int"
        "                        (c$::make-iconst"
        "                          :core (c$::dec/oct/hex-const-dec 1)))))")
      (xdoc::p
        "This will produce the following:")
      (xdoc::codeblock
        "int foo(int z) {"
        "  int y = 1;"
        "  int x = 5;"
        "  return x + y - z;"
        "}")
      (xdoc::p
        "Clearly a call of @('foo(z)'), where @('z') is arbitrary and @('foo')
         is the specialized function, is equal to @('foo(1, z)') for the old
         function @('foo').")))
  :order-subtopics t)
