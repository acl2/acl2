; C Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2022 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "std/util/define" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ pointer-types
  :parents (atc-shallow-embedding)
  :short "Representation of pointer types in the shallow embedding."
  :long
  (xdoc::topstring
   (xdoc::p
    "Currently, the shallow embedding does not represent pointers explicitly.
     That is, the ACL2 functions that represent C functions
     always operate on values, including array values,
     not on pointers to them.
     However, these manipulations on values may represent
     manipulations on pointers,
     more precisely on the values referenced by pointers.
     An example is arrays, which in fact, in C,
     are mostly operated upon as pointers,
     via the array-to-pointer conversions.
     Other values, such as structures or integers,
     may be operated upon either by value or by pointer.")
   (xdoc::p
    "To distinguish the two cases, i.e. by value or by pointer,
     we introduce an identity wrapper @(tsee pointer),
     which we can use to wrap recognizers of C values
     to signify that we mean pointers to those values.
     This wrapper can be used in guards of ACL2 functions
     that represent C functions,
     to wrap the conjuncts from which the function's parameter C types
     are derived."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pointer (x)
  :short "Wrapper to represent a C pointer type."
  :long
  (xdoc::topstring
   (xdoc::p
    "The idea is that @('(pointer (P ...))') represents,
     for the purpose of generating a C type,
     the pointer type @('T*')
     if the recognizer @('P') represents type @('T')."))
  x)
