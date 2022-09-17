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

(include-book "../execution")

(include-book "syntaxp")
(include-book "value-integer-get")

(local (xdoc::set-default-parents atc-symbolic-execution-rules))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-test-value-rules
  :short "Rules for executing tests on values."
  :long
  (xdoc::topstring
   (xdoc::p
    "Each rule turns @('(test-value x)')
     into @('(boolean-from-<type> x)'),
     where @('<type>') is the type of @('x').
     The @(tsee test-value) terms result
     from the symbolic execution of the C code,
     while the @('boolean-from-<type>') terms occur
     in the ACL2 functions that represent the C code."))

  (make-event
   `(local (in-theory (enable test-value
                              test-scalar-value
                              test-integer-value
                              ,@*atc-value-integer->get-rules*
                              boolean-from-schar
                              boolean-from-uchar
                              boolean-from-sshort
                              boolean-from-ushort
                              boolean-from-sint
                              boolean-from-uint
                              boolean-from-slong
                              boolean-from-ulong
                              boolean-from-sllong
                              boolean-from-ullong))))

  (make-event
   `(defruled test-value-when-scharp
      (implies (and ,(atc-syntaxp-hyp-for-expr-pure 'x)
                    (scharp x))
               (equal (test-value x)
                      (boolean-from-schar x)))))

  (make-event
   `(defruled test-value-when-ucharp
      (implies (and ,(atc-syntaxp-hyp-for-expr-pure 'x)
                    (ucharp x))
               (equal (test-value x)
                      (boolean-from-uchar x)))))

  (make-event
   `(defruled test-value-when-sshortp
      (implies (and ,(atc-syntaxp-hyp-for-expr-pure 'x)
                    (sshortp x))
               (equal (test-value x)
                      (boolean-from-sshort x)))))

  (make-event
   `(defruled test-value-when-ushortp
      (implies (and ,(atc-syntaxp-hyp-for-expr-pure 'x)
                    (ushortp x))
               (equal (test-value x)
                      (boolean-from-ushort x)))))

  (make-event
   `(defruled test-value-when-sintp
      (implies (and ,(atc-syntaxp-hyp-for-expr-pure 'x)
                    (sintp x))
               (equal (test-value x)
                      (boolean-from-sint x)))))

  (make-event
   `(defruled test-value-when-uintp
      (implies (and ,(atc-syntaxp-hyp-for-expr-pure 'x)
                    (uintp x))
               (equal (test-value x)
                      (boolean-from-uint x)))))

  (make-event
   `(defruled test-value-when-slongp
      (implies (and ,(atc-syntaxp-hyp-for-expr-pure 'x)
                    (slongp x))
               (equal (test-value x)
                      (boolean-from-slong x)))))

  (make-event
   `(defruled test-value-when-ulongp
      (implies (and ,(atc-syntaxp-hyp-for-expr-pure 'x)
                    (ulongp x))
               (equal (test-value x)
                      (boolean-from-ulong x)))))

  (make-event
   `(defruled test-value-when-sllongp
      (implies (and ,(atc-syntaxp-hyp-for-expr-pure 'x)
                    (sllongp x))
               (equal (test-value x)
                      (boolean-from-sllong x)))))

  (make-event
   `(defruled test-value-when-ullongp
      (implies (and ,(atc-syntaxp-hyp-for-expr-pure 'x)
                    (ullongp x))
               (equal (test-value x)
                      (boolean-from-ullong x)))))

  (defval *atc-test-value-rules*
    '(test-value-when-scharp
      test-value-when-ucharp
      test-value-when-sshortp
      test-value-when-ushortp
      test-value-when-sintp
      test-value-when-uintp
      test-value-when-slongp
      test-value-when-ulongp
      test-value-when-sllongp
      test-value-when-ullongp)))
