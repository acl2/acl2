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

(include-book "../integer-operations")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-not-rules
  :short "Rules related to @(tsee not)."
  :long
  (xdoc::topstring
   (xdoc::p
    "ATC currently allows the logical negation operator @('!')
     to be represented via not only the @('lognot-<type>') functions,
     but also @(tsee not), with appropriate conversions with booleans as needed.
     That is, an ACL2 target function, from which C code is generate,
     may represent logical negation in two different ways.
     The dynamic semantics of C, during symbolic execution,
     turns expressions with the logical negation operator into one form.
     Thus, we need rules to normalize one of the two forms into the other.")
   (xdoc::p
    "We choose to normalize things to use @(tsee not).
     Thus, we add rules saying that @('(boolean-from-<type> (lognot-<type> x))')
     becomes @('(not (boolean-from-<type> x))').")
   (xdoc::p
    "Because these rules may be applied to terms
     that result from execution and that must be checked not to be errors,
     we also add a rule saying that a call of @(tsee not) is not an error.
     Otherwise, terms of the form @('(errorp (not ...))')
     arise during symbolic execution and cause proofs to fail.")
   (xdoc::p
    "It may be better to change ATC to require
     a unique representation of the logical negation operator,
     and avoid these rules altogether.
     This approach will be considered in the future."))

  (defruled boolean-from-uchar-of-lognot-uchar
    (equal (boolean-from-uchar (lognot-uchar x))
           (not (boolean-from-uchar x)))
    :enable (boolean-from-uchar lognot-uchar))

  (defruled boolean-from-schar-of-lognot-schar
    (equal (boolean-from-schar (lognot-schar x))
           (not (boolean-from-schar x)))
    :enable (boolean-from-schar lognot-schar))

  (defruled boolean-from-ushort-of-lognot-ushort
    (equal (boolean-from-ushort (lognot-ushort x))
           (not (boolean-from-ushort x)))
    :enable (boolean-from-ushort lognot-ushort))

  (defruled boolean-from-sshort-of-lognot-sshort
    (equal (boolean-from-sshort (lognot-sshort x))
           (not (boolean-from-sshort x)))
    :enable (boolean-from-sshort lognot-sshort))

  (defruled boolean-from-uint-of-lognot-uint
    (equal (boolean-from-uint (lognot-uint x))
           (not (boolean-from-uint x)))
    :enable (boolean-from-uint lognot-uint))

  (defruled boolean-from-sint-of-lognot-sint
    (equal (boolean-from-sint (lognot-sint x))
           (not (boolean-from-sint x)))
    :enable (boolean-from-sint lognot-sint))

  (defruled boolean-from-ulong-of-lognot-ulong
    (equal (boolean-from-ulong (lognot-ulong x))
           (not (boolean-from-ulong x)))
    :enable (boolean-from-ulong lognot-ulong))

  (defruled boolean-from-slong-of-lognot-slong
    (equal (boolean-from-slong (lognot-slong x))
           (not (boolean-from-slong x)))
    :enable (boolean-from-slong lognot-slong))

  (defruled boolean-from-ullong-of-lognot-ullong
    (equal (boolean-from-ullong (lognot-ullong x))
           (not (boolean-from-ullong x)))
    :enable (boolean-from-ullong lognot-ullong))

  (defruled boolean-from-sllong-of-lognot-sllong
    (equal (boolean-from-sllong (lognot-sllong x))
           (not (boolean-from-sllong x)))
    :enable (boolean-from-sllong lognot-sllong))

  (defruled not-errorp-of-not
    (not (c::errorp (not x)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *atc-not-rules*
  :short "List of rules related to @(tsee not)."
  '(boolean-from-uchar-of-lognot-uchar
    boolean-from-schar-of-lognot-schar
    boolean-from-ushort-of-lognot-ushort
    boolean-from-sshort-of-lognot-sshort
    boolean-from-uint-of-lognot-uint
    boolean-from-sint-of-lognot-sint
    boolean-from-ulong-of-lognot-ulong
    boolean-from-slong-of-lognot-slong
    boolean-from-ullong-of-lognot-ullong
    boolean-from-sllong-of-lognot-sllong
    not-errorp-of-not))
