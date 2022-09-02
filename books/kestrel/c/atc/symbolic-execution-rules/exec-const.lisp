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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-exec-const-rules
  :short "Rules for executing constants."
  :long
  (xdoc::topstring
   (xdoc::p
    "To symbolically execute a constant,
     which in our current C subset may only be an integer constant,
     we use rules corresponding to the possible integer types of the constant.
     The rules are openers for @(tsee exec-const),
     under suitable conditions.
     The argument of @(tsee exec-const) is a quoted constant
     during symbolic execution,
     because it is taken from the ASTs being executed;
     thus, we enable the executable counterparts
     of the fixtype functions that operate on constants
     and of the @('<type>-integerp') predicates."))

  (defruled exec-const-to-sint
    (implies (and (syntaxp (quotep const))
                  (const-case const :int)
                  (equal iconst (const-int->get const))
                  (not (iconst->unsignedp iconst))
                  (iconst-length-case (iconst->length iconst) :none)
                  (equal value (iconst->value iconst))
                  (sint-integerp value))
             (equal (exec-const const)
                    (sint value)))
    :enable (exec-const
             exec-iconst
             value-sint->get
             sint
             value-kind
             valuep))

  (defruled exec-const-to-slong
    (implies (and (syntaxp (quotep const))
                  (const-case const :int)
                  (equal iconst (const-int->get const))
                  (not (iconst->unsignedp iconst))
                  (equal value (iconst->value iconst))
                  (slong-integerp value)
                  (equal length (iconst->length iconst))
                  (equal base (iconst->base iconst))
                  (or (and (iconst-length-case length :none)
                           (not (sint-integerp value))
                           (or (iconst-base-case base :dec)
                               (not (uint-integerp value))))
                      (iconst-length-case length :long)))
             (equal (exec-const const)
                    (slong value)))
    :enable (exec-const
             exec-iconst
             value-slong->get
             slong
             value-kind
             valuep))

  (defruled exec-const-to-sllong
    (implies (and (syntaxp (quotep const))
                  (const-case const :int)
                  (equal iconst (const-int->get const))
                  (not (iconst->unsignedp iconst))
                  (equal value (iconst->value iconst))
                  (sllong-integerp value)
                  (equal length (iconst->length iconst))
                  (equal base (iconst->base iconst))
                  (or (and (iconst-length-case length :none)
                           (not (slong-integerp value))
                           (or (iconst-base-case base :dec)
                               (not (ulong-integerp value))))
                      (and (iconst-length-case length :long)
                           (not (slong-integerp value))
                           (or (iconst-base-case base :dec)
                               (not (ulong-integerp value))))
                      (iconst-length-case length :llong)))
             (equal (exec-const const)
                    (sllong value)))
    :enable (exec-const
             exec-iconst
             slong-integerp-alt-def
             sint-integerp-alt-def
             ulong-integerp-alt-def
             uint-integerp-alt-def
             value-sllong->get
             sllong
             value-kind
             valuep))

  (defruled exec-const-to-uint
    (implies (and (syntaxp (quotep const))
                  (const-case const :int)
                  (equal iconst (const-int->get const))
                  (iconst-length-case (iconst->length iconst) :none)
                  (equal value (iconst->value iconst))
                  (uint-integerp value)
                  (or (iconst->unsignedp iconst)
                      (and (not (iconst-base-case (iconst->base iconst) :dec))
                           (not (sint-integerp value)))))
             (equal (exec-const const)
                    (uint value)))
    :enable (exec-const
             exec-iconst
             value-uint->get
             uint
             value-kind
             valuep))

  (defruled exec-const-to-ulong
    (implies (and (syntaxp (quotep const))
                  (const-case const :int)
                  (equal iconst (const-int->get const))
                  (equal value (iconst->value iconst))
                  (ulong-integerp value)
                  (equal length (iconst->length iconst))
                  (equal base (iconst->base iconst))
                  (or (and (iconst->unsignedp iconst)
                           (or (and (iconst-length-case length :none)
                                    (not (uint-integerp value)))
                               (iconst-length-case length :long)))
                      (and (not (iconst-base-case base :dec))
                           (not (slong-integerp value))
                           (or (and (iconst-length-case length :none)
                                    (not (uint-integerp value)))
                               (iconst-length-case length :long)))))
             (equal (exec-const const)
                    (ulong value)))
    :enable (exec-const
             exec-iconst
             sint-integerp-alt-def
             slong-integerp-alt-def
             value-ulong->get
             ulong
             value-kind
             valuep))

  (defruled exec-const-to-ullong
    (implies (and (syntaxp (quotep const))
                  (const-case const :int)
                  (equal iconst (const-int->get const))
                  (equal value (iconst->value iconst))
                  (ullong-integerp value)
                  (equal length (iconst->length iconst))
                  (equal base (iconst->base iconst))
                  (or (and (iconst->unsignedp iconst)
                           (or (iconst-length-case length :llong)
                               (not (ulong-integerp value))))
                      (and (not (iconst-base-case base :dec))
                           (not (sllong-integerp value))
                           (or (iconst-length-case length :llong)
                               (not (ulong-integerp value))))))
             (equal (exec-const const)
                    (ullong value)))
    :enable (exec-const
             exec-iconst
             sint-integerp-alt-def
             slong-integerp-alt-def
             sllong-integerp-alt-def
             uint-integerp-alt-def
             ulong-integerp-alt-def
             value-ullong->get
             ullong
             value-kind
             valuep))

  (defval *atc-exec-const-rules*
    '(exec-const-to-sint
      exec-const-to-uint
      exec-const-to-slong
      exec-const-to-ulong
      exec-const-to-sllong
      exec-const-to-ullong
      (:e const-kind)
      (:e const-int->get)
      (:e iconst->base)
      (:e iconst->length)
      (:e iconst->unsignedp)
      (:e iconst->value)
      (:e iconst-length-kind)
      (:e iconst-base-kind)
      (:e sint-integerp)
      (:e uint-integerp)
      (:e slong-integerp)
      (:e ulong-integerp)
      (:e sllong-integerp)
      (:e ullong-integerp))))
