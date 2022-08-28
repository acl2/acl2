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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-exec-test-rules
  :short "Rules for executing tests on values."
  :long
  (xdoc::topstring
   (xdoc::p
    "Each rule turns @('(exec-test x)')
     into @('(boolean-from-<type> x)'),
     where @('<type>') is the type of @('x').
     The @(tsee exec-test) terms result
     from the symbolic execution of the C code,
     while the @('boolean-from-<type>') terms occur
     in the ACL2 functions that represent the C code."))

  (make-event
   `(defruled exec-test-when-scharp
      (implies (and ,(atc-syntaxp-hyp-for-expr-pure 'x)
                    (scharp x))
               (equal (exec-test x)
                      (boolean-from-schar x)))
      :enable exec-test))

  (make-event
   `(defruled exec-test-when-ucharp
      (implies (and ,(atc-syntaxp-hyp-for-expr-pure 'x)
                    (ucharp x))
               (equal (exec-test x)
                      (boolean-from-uchar x)))
      :enable exec-test))

  (make-event
   `(defruled exec-test-when-sshortp
      (implies (and ,(atc-syntaxp-hyp-for-expr-pure 'x)
                    (sshortp x))
               (equal (exec-test x)
                      (boolean-from-sshort x)))
      :enable exec-test))

  (make-event
   `(defruled exec-test-when-ushortp
      (implies (and ,(atc-syntaxp-hyp-for-expr-pure 'x)
                    (ushortp x))
               (equal (exec-test x)
                      (boolean-from-ushort x)))
      :enable exec-test))

  (make-event
   `(defruled exec-test-when-sintp
      (implies (and ,(atc-syntaxp-hyp-for-expr-pure 'x)
                    (sintp x))
               (equal (exec-test x)
                      (boolean-from-sint x)))
      :enable exec-test))

  (make-event
   `(defruled exec-test-when-uintp
      (implies (and ,(atc-syntaxp-hyp-for-expr-pure 'x)
                    (uintp x))
               (equal (exec-test x)
                      (boolean-from-uint x)))
      :enable exec-test))

  (make-event
   `(defruled exec-test-when-slongp
      (implies (and ,(atc-syntaxp-hyp-for-expr-pure 'x)
                    (slongp x))
               (equal (exec-test x)
                      (boolean-from-slong x)))
      :enable exec-test))

  (make-event
   `(defruled exec-test-when-ulongp
      (implies (and ,(atc-syntaxp-hyp-for-expr-pure 'x)
                    (ulongp x))
               (equal (exec-test x)
                      (boolean-from-ulong x)))
      :enable exec-test))

  (make-event
   `(defruled exec-test-when-sllongp
      (implies (and ,(atc-syntaxp-hyp-for-expr-pure 'x)
                    (sllongp x))
               (equal (exec-test x)
                      (boolean-from-sllong x)))
      :enable exec-test))

  (make-event
   `(defruled exec-test-when-ullongp
      (implies (and ,(atc-syntaxp-hyp-for-expr-pure 'x)
                    (ullongp x))
               (equal (exec-test x)
                      (boolean-from-ullong x)))
      :enable exec-test))

  (defval *atc-exec-test-rules*
    '(exec-test-when-scharp
      exec-test-when-ucharp
      exec-test-when-sshortp
      exec-test-when-ushortp
      exec-test-when-sintp
      exec-test-when-uintp
      exec-test-when-slongp
      exec-test-when-ulongp
      exec-test-when-sllongp
      exec-test-when-ullongp)))
