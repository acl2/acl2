; Prime Fields Library Documentation
;
; Copyright (C) 2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "PFIELD")

(include-book "xdoc/constructors" :dir :system)

(xdoc::defxdoc prime-fields
  :parents (acl2::kestrel-books acl2::algebra)
  :short "A library about prime fields."
  :long
  (xdoc::topstring
   (xdoc::p
    "The prime-fields library contains executable formal specifications of
    prime fields and related operations, along with a number of rules about
    those operations.  The elements of the field corresponding to the
    prime " (xdoc::tt "p") " are the natural numbers less
    than " (xdoc::tt "p") ".")
   (xdoc::p
    "To define the notion of primality, we currently use the
    function " (xdoc::tt "rtl::primep") " defined
    in " (xdoc::tt "[books]/projects/quadratic-reciprocity/euclid") ".")
   (xdoc::p "The following "
            (xdoc::tt "include-book")
            " command may be helpful to bring in the library:")
   (xdoc::@{}
    "(include-book \"kestrel/prime-fields/prime-fields\" :dir :system)")
   (xdoc::p "The key functions in the library are:")
   (xdoc::ul
    (xdoc::li (xdoc::tt "(fep x p)") ": \The \"Field-element predicate\". Tests whether @('x') is an element of the field for the prime @('p').")
    (xdoc::li (xdoc::tt "(add x y p)") ": Addition in the field: Computes the sum of @('x') and @('y') modulo the prime @('p').")
    (xdoc::li (xdoc::tt "(sub x y p)") ": Subtraction in the field: Computes the difference of @('x') and @('y') modulo the prime @('p').")
    (xdoc::li (xdoc::tt "(neg x p)") ": Negation (additive inverse) in the field: Computes the (unary) negation of @('x') modulo the prime @('p').")
    (xdoc::li (xdoc::tt "(mul x y p)") ": Multiplication in the field: Computes the product of @('x') and @('y') modulo the prime @('p').")
    (xdoc::li (xdoc::tt "(pow x n p)") ": Exponentiation in the field: Computes @('x') to the nth power @(x^n) modulo the prime @('p').  Note that @('n') can be any natural.")
    (xdoc::li (xdoc::tt "(inv x p)") ": Multiplicative inverse in the field: Computes @('1/x') modulo the prime @('p').  Requires @('x') to be non-zero.")
    (xdoc::li (xdoc::tt "(div x y p)") ": Division in the field: Computes @('x/y') modulo the prime @('p').  Requires @('y') to be non-zero.")
    (xdoc::li (xdoc::tt "(minus1 p)") ": Returns @('p-1').  This is often very large (if @('p')is very large), but it can help to think of this value as @('-1')."))))
