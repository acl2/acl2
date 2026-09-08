; Standard Utilities Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defmacro-plus" :dir :system)
(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ defirrelevant (name
                           &key
                           type
                           body
                           (parents 'nil parents-p)
                           short
                           (long 'nil long-p))
  :parents (std/util)
  :short "Define an irrelevant value of a type."
  :long
  (xdoc::topstring
   (xdoc::p
    "This macro defines a nullary function, named @('name'),
     that returns a fixed value of a type:
     the value of the term @('body'),
     which must satisfy the predicate @('type')
     (this is proved as a @(tsee define) @(':returns') theorem).
     The @(':parents'), @(':short'), and @(':long') inputs
     are for the XDOC topic of the function;
     if @(':long') is absent, a default is generated.")
   (xdoc::codeblock
    "(defirrelevant name"
    "  :type ...     ; recognizer of the type"
    "  :body ...     ; a term whose value has the type"
    "  :parents ...  ; optional"
    "  :short ...    ; a string"
    "  :long ...     ; optional"
    "  )")
   (xdoc::p
    "The purpose of the function is to provide
     a value of the type whose specific identity does not matter;
     hence `irrelevant':
     what is irrelevant is which value of the type the function returns,
     not the function itself, which serves a real purpose.
     Typical uses are
     to fill the non-error result slots of a function
     that is returning an error
     (e.g. with @(see error-value-tuples),
     whose @('reterr') must supply well-typed results
     for the error case),
     and to complete branches that are provably unreachable
     (e.g. guarded by @(tsee impossible))
     but must still yield a well-typed value.")
   (xdoc::p
    "The function is made opaque:
     no built-in type-prescription rule is generated
     (this macro passes @(':type-prescription :none')
     to @(tsee define)),
     the definition is disabled
     (which @(tsee define) does by default),
     and the executable counterpart is disabled
     (which this macro does explicitly).
     Thus, unless the definition or executable counterpart
     is deliberately enabled,
     proofs cannot depend on which value the function returns,
     but only on its type, via the @(':returns') theorem;
     accidental dependence on the specific value
     shows up as a proof failure.
     This, together with the fact that the named function
     documents at each use site that the value is arbitrary,
     is the advantage of this macro over
     just using some specific value of the type directly.")
   (xdoc::p
    "The type-prescription rule is suppressed,
     rather than merely disabled,
     because if @('body') is a constant, like @('0') or @('nil'),
     the type-prescription rule that ACL2 computes at admission time
     determines the value exactly,
     which would defeat the opacity just described
     (type-prescription rules are normally enabled,
     and disabling them by default would be unexpected)."))
  `(define ,name ()
     :returns (irr ,type)
     :type-prescription :none
     ,@(and parents-p `(:parents ,parents))
     :short ,short
     :long
     ,(if long-p
          long
        (xdoc::topstring
         (xdoc::p
          "This is a fixed but arbitrary value of the type; see "
          (xdoc::seetopic "acl2::defirrelevant" "defirrelevant")
          " for the purpose of such values.")))
     ,body
     ///
     (in-theory (disable (:e ,name)))))
