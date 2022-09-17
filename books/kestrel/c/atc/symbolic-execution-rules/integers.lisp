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

(include-book "../integers")

(include-book "../../language/values")

(include-book "../defthm-disjoint")

(local (xdoc::set-default-parents atc-symbolic-execution-rules))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection integer-value-disjoint-rules
  :short "Rules about disjointness of integer values."

  (local (in-theory (enable value-kind)))

  (defthm-disjoint *integer-value-disjoint-rules*
    ucharp
    scharp
    ushortp
    sshortp
    uintp
    sintp
    ulongp
    slongp
    ullongp
    sllongp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule valuep-possibilities
  :short "Possible integer and other predicates for values."
  (implies (valuep x)
           (or (ucharp x)
               (scharp x)
               (ushortp x)
               (sshortp x)
               (uintp x)
               (sintp x)
               (ulongp x)
               (slongp x)
               (ullongp x)
               (sllongp x)
               (value-case x :pointer)
               (value-case x :array)
               (value-case x :struct)))
  :enable (valuep
           ucharp
           scharp
           ushortp
           sshortp
           uintp
           sintp
           ulongp
           slongp
           ullongp
           sllongp
           value-kind)
  :rule-classes :forward-chaining)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection valuep-when-valuepred
  :short "Theorem saying that the value recognizers imply @(tsee valuep)."

  (defrule valuep-when-ucharp
    (implies (ucharp x)
             (valuep x))
    :enable (valuep ucharp))

  (defrule valuep-when-scharp
    (implies (scharp x)
             (valuep x))
    :enable (valuep scharp))

  (defrule valuep-when-ushortp
    (implies (ushortp x)
             (valuep x))
    :enable (valuep ushortp))

  (defrule valuep-when-sshortp
    (implies (sshortp x)
             (valuep x))
    :enable (valuep sshortp))

  (defrule valuep-when-uintp
    (implies (uintp x)
             (valuep x))
    :enable (valuep uintp))

  (defrule valuep-when-sintp
    (implies (sintp x)
             (valuep x))
    :enable (valuep sintp))

  (defrule valuep-when-ulongp
    (implies (ulongp x)
             (valuep x))
    :enable (valuep ulongp))

  (defrule valuep-when-slongp
    (implies (slongp x)
             (valuep x))
    :enable (valuep slongp))

  (defrule valuep-when-ullongp
    (implies (ullongp x)
             (valuep x))
    :enable (valuep ullongp))

  (defrule valuep-when-sllongp
    (implies (sllongp x)
             (valuep x))
    :enable (valuep sllongp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection value-listp-when-valuepred-listp
  :short "Theorems saying that
          the value list recognizers imply @(tsee value-listp)."

  (defrule value-listp-when-uchar-listp
    (implies (uchar-listp x)
             (value-listp x))
    :induct (len x)
    :enable value-listp)

  (defrule value-listp-when-schar-listp
    (implies (schar-listp x)
             (value-listp x))
    :induct (len x)
    :enable value-listp)

  (defrule value-listp-when-ushort-listp
    (implies (ushort-listp x)
             (value-listp x))
    :induct (len x)
    :enable value-listp)

  (defrule value-listp-when-sshort-listp
    (implies (sshort-listp x)
             (value-listp x))
    :induct (len x)
    :enable value-listp)

  (defrule value-listp-when-uint-listp
    (implies (uint-listp x)
             (value-listp x))
    :induct (len x)
    :enable value-listp)

  (defrule value-listp-when-sint-listp
    (implies (sint-listp x)
             (value-listp x))
    :induct (len x)
    :enable value-listp)

  (defrule value-listp-when-ulong-listp
    (implies (ulong-listp x)
             (value-listp x))
    :induct (len x)
    :enable value-listp)

  (defrule value-listp-when-slong-listp
    (implies (slong-listp x)
             (value-listp x))
    :induct (len x)
    :enable value-listp)

  (defrule value-listp-when-ullong-listp
    (implies (ullong-listp x)
             (value-listp x))
    :induct (len x)
    :enable value-listp)

  (defrule value-listp-when-sllong-listp
    (implies (sllong-listp x)
             (value-listp x))
    :induct (len x)
    :enable value-listp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection value-kind-when-valuepred
  :short "Theorem providing the kind of value for different types."

  (defruled value-kind-when-scharp
    (implies (scharp x)
             (equal (value-kind x)
                    :schar))
    :enable (scharp value-kind))

  (defruled value-kind-when-ucharp
    (implies (ucharp x)
             (equal (value-kind x)
                    :uchar))
    :enable (ucharp value-kind))

  (defruled value-kind-when-sshortp
    (implies (sshortp x)
             (equal (value-kind x)
                    :sshort))
    :enable (sshortp value-kind))

  (defruled value-kind-when-ushortp
    (implies (ushortp x)
             (equal (value-kind x)
                    :ushort))
    :enable (ushortp value-kind))

  (defruled value-kind-when-sintp
    (implies (sintp x)
             (equal (value-kind x)
                    :sint))
    :enable (sintp value-kind))

  (defruled value-kind-when-uintp
    (implies (uintp x)
             (equal (value-kind x)
                    :uint))
    :enable (uintp value-kind))

  (defruled value-kind-when-slongp
    (implies (slongp x)
             (equal (value-kind x)
                    :slong))
    :enable (slongp value-kind))

  (defruled value-kind-when-ulongp
    (implies (ulongp x)
             (equal (value-kind x)
                    :ulong))
    :enable (ulongp value-kind))

  (defruled value-kind-when-sllongp
    (implies (sllongp x)
             (equal (value-kind x)
                    :sllong))
    :enable (sllongp value-kind))

  (defruled value-kind-when-ullongp
    (implies (ullongp x)
             (equal (value-kind x)
                    :ullong))
    :enable (ullongp value-kind)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection valuepred-when-value-kind
  :short "Theorems saying that specific @(tsee value-kind)s
          imply corresponding value predicates."

  (defruled scharp-when-valuep-and-kind-schar
    (implies (and (valuep val)
                  (value-case val :schar))
             (scharp val))
    :enable (valuep value-kind scharp))

  (defruled ucharp-when-valuep-and-kind-uchar
    (implies (and (valuep val)
                  (value-case val :uchar))
             (ucharp val))
    :enable (valuep value-kind ucharp))

  (defruled sshortp-when-valuep-and-kind-sshort
    (implies (and (valuep val)
                  (value-case val :sshort))
             (sshortp val))
    :enable (valuep value-kind sshortp))

  (defruled ushortp-when-valuep-and-kind-ushort
    (implies (and (valuep val)
                  (value-case val :ushort))
             (ushortp val))
    :enable (valuep value-kind ushortp))

  (defruled sintp-when-valuep-and-kind-sint
    (implies (and (valuep val)
                  (value-case val :sint))
             (sintp val))
    :enable (valuep value-kind sintp))

  (defruled uintp-when-valuep-and-kind-uint
    (implies (and (valuep val)
                  (value-case val :uint))
             (uintp val))
    :enable (valuep value-kind uintp))

  (defruled slongp-when-valuep-and-kind-slong
    (implies (and (valuep val)
                  (value-case val :slong))
             (slongp val))
    :enable (valuep value-kind slongp))

  (defruled ulongp-when-valuep-and-kind-ulong
    (implies (and (valuep val)
                  (value-case val :ulong))
             (ulongp val))
    :enable (valuep value-kind ulongp))

  (defruled sllongp-when-valuep-and-kind-sllong
    (implies (and (valuep val)
                  (value-case val :sllong))
             (sllongp val))
    :enable (valuep value-kind sllongp))

  (defruled ullongp-when-valuep-and-kind-ullong
    (implies (and (valuep val)
                  (value-case val :ullong))
             (ullongp val))
    :enable (valuep value-kind ullongp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled value-signed-integerp-alt-def
  :short "Alternative definition of @(tsee value-signed-integerp),
          in terms of the shallow embedding's integer value recognizers."
  (equal (value-signed-integerp val)
         (b* ((val (value-fix val)))
           (or (scharp val)
               (sshortp val)
               (sintp val)
               (slongp val)
               (sllongp val))))
  :use (:instance lemma (val (value-fix val)))
  :prep-lemmas
  ((defruled lemma
     (implies (valuep val)
              (equal (value-signed-integerp val)
                     (or (scharp val)
                         (sshortp val)
                         (sintp val)
                         (slongp val)
                         (sllongp val))))
     :enable (valuep
              value-kind
              value-signed-integerp
              scharp
              sshortp
              sintp
              slongp
              sllongp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled value-unsigned-integerp-alt-def
  :short "Alternative definition of @(tsee value-unsigned-integerp),
          in terms of the shallow embedding's integer value recognizers."
  (equal (value-unsigned-integerp val)
         (b* ((val (value-fix val)))
           (or (ucharp val)
               (ushortp val)
               (uintp val)
               (ulongp val)
               (ullongp val))))
  :use (:instance lemma (val (value-fix val)))
  :prep-lemmas
  ((defruled lemma
     (implies (valuep val)
              (equal (value-unsigned-integerp val)
                     (or (ucharp val)
                         (ushortp val)
                         (uintp val)
                         (ulongp val)
                         (ullongp val))))
     :enable (valuep
              value-kind
              value-unsigned-integerp
              ucharp
              ushortp
              uintp
              ulongp
              ullongp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled value-promoted-arithmeticp-alt-def
  :short "Alternative definition of @(tsee value-promoted-arithmeticp),
          in terms of the shallow embedding's integer value recognizers."
  (implies (valuep val)
           (equal (value-promoted-arithmeticp val)
                  (or (uintp val)
                      (sintp val)
                      (ulongp val)
                      (slongp val)
                      (ullongp val)
                      (sllongp val))))
  :enable (value-promoted-arithmeticp
           value-arithmeticp
           value-realp
           value-integerp
           value-unsigned-integerp-alt-def
           value-signed-integerp-alt-def))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection value-tau-rules
  :short "Some tau rules about values."

  (defrule signed-integer-value-kinds
    (implies (or (scharp x)
                 (sshortp x)
                 (sintp x)
                 (slongp x)
                 (sllongp x))
             (and (value-scalarp x)
                  (value-arithmeticp x)
                  (value-realp x)
                  (value-integerp x)
                  (value-signed-integerp x)))
    :rule-classes :tau-system
    :enable (value-scalarp
             value-arithmeticp
             value-realp
             value-integerp
             value-signed-integerp-alt-def))

  (defrule unsigned-integer-value-kinds
    (implies (or (ucharp x)
                 (ushortp x)
                 (uintp x)
                 (ulongp x)
                 (ullongp x))
             (and (value-scalarp x)
                  (value-arithmeticp x)
                  (value-realp x)
                  (value-integerp x)
                  (value-unsigned-integerp x)))
    :rule-classes :tau-system
    :enable (value-scalarp
             value-arithmeticp
             value-realp
             value-integerp
             value-unsigned-integerp-alt-def)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection valuepred-to-type-of-value-equalities
  :short "Rules that rewrite predicates for values
          to equalities of the types of the values."

  (defruled ucharp-to-type-of-value
    (implies (valuep x)
             (equal (ucharp x)
                    (equal (type-of-value x)
                           (type-uchar))))
    :enable (type-of-value
             valuep
             value-kind
             ucharp))

  (defruled scharp-to-type-of-value
    (implies (valuep x)
             (equal (scharp x)
                    (equal (type-of-value x)
                           (type-schar))))
    :enable (type-of-value
             valuep
             value-kind
             scharp))

  (defruled ushortp-to-type-of-value
    (implies (valuep x)
             (equal (ushortp x)
                    (equal (type-of-value x)
                           (type-ushort))))
    :enable (type-of-value
             valuep
             value-kind
             ushortp))

  (defruled sshortp-to-type-of-value
    (implies (valuep x)
             (equal (sshortp x)
                    (equal (type-of-value x)
                           (type-sshort))))
    :enable (type-of-value
             valuep
             value-kind
             sshortp))

  (defruled uintp-to-type-of-value
    (implies (valuep x)
             (equal (uintp x)
                    (equal (type-of-value x)
                           (type-uint))))
    :enable (type-of-value
             valuep
             value-kind
             uintp))

  (defruled sintp-to-type-of-value
    (implies (valuep x)
             (equal (sintp x)
                    (equal (type-of-value x)
                           (type-sint))))
    :enable (type-of-value
             valuep
             value-kind
             sintp))

  (defruled ulongp-to-type-of-value
    (implies (valuep x)
             (equal (ulongp x)
                    (equal (type-of-value x)
                           (type-ulong))))
    :enable (type-of-value
             valuep
             value-kind
             ulongp))

  (defruled slongp-to-type-of-value
    (implies (valuep x)
             (equal (slongp x)
                    (equal (type-of-value x)
                           (type-slong))))
    :enable (type-of-value
             valuep
             value-kind
             slongp))

  (defruled ullongp-to-type-of-value
    (implies (valuep x)
             (equal (ullongp x)
                    (equal (type-of-value x)
                           (type-ullong))))
    :enable (type-of-value
             valuep
             value-kind
             ullongp))

  (defruled sllongp-to-type-of-value
    (implies (valuep x)
             (equal (sllongp x)
                    (equal (type-of-value x)
                           (type-sllong))))
    :enable (type-of-value
             valuep
             value-kind
             sllongp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection type-of-value-when-valuepred
  :short "Rules that rewrite @(tsee type-of-value) to specific types
          under hypotheses on different types of values."

  (defruled type-of-value-when-ucharp
    (implies (ucharp x)
             (equal (type-of-value x)
                    (type-uchar)))
    :enable (type-of-value
             value-kind
             ucharp))

  (defruled type-of-value-when-scharp
    (implies (scharp x)
             (equal (type-of-value x)
                    (type-schar)))
    :enable (type-of-value
             value-kind
             scharp))

  (defruled type-of-value-when-ushortp
    (implies (ushortp x)
             (equal (type-of-value x)
                    (type-ushort)))
    :enable (type-of-value
             value-kind
             ushortp))

  (defruled type-of-value-when-sshortp
    (implies (sshortp x)
             (equal (type-of-value x)
                    (type-sshort)))
    :enable (type-of-value
             value-kind
             sshortp))

  (defruled type-of-value-when-uintp
    (implies (uintp x)
             (equal (type-of-value x)
                    (type-uint)))
    :enable (type-of-value
             value-kind
             uintp))

  (defruled type-of-value-when-sintp
    (implies (sintp x)
             (equal (type-of-value x)
                    (type-sint)))
    :enable (type-of-value
             value-kind
             sintp))

  (defruled type-of-value-when-ulongp
    (implies (ulongp x)
             (equal (type-of-value x)
                    (type-ulong)))
    :enable (type-of-value
             value-kind
             ulongp))

  (defruled type-of-value-when-slongp
    (implies (slongp x)
             (equal (type-of-value x)
                    (type-slong)))
    :enable (type-of-value
             value-kind
             slongp))

  (defruled type-of-value-when-ullongp
    (implies (ullongp x)
             (equal (type-of-value x)
                    (type-ullong)))
    :enable (type-of-value
             value-kind
             ullongp))

  (defruled type-of-value-when-sllongp
    (implies (sllongp x)
             (equal (type-of-value x)
                    (type-sllong)))
    :enable (type-of-value
             value-kind
             sllongp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection value-bridge-theorems
  :short "Bridge theorems between
          the deeply embedded integer values
          and the shallowly embedded integer values."
  :long
  (xdoc::topstring
   (xdoc::p
    "The deeply embedded integer values are
     a subset of the values of the fixtype @(tsee value).
     The shallowly embedded ineger values are
     the values of the fixtypes @(tsee uchar), @(tsee schar), etc.
     These have the same representation,
     and thus their constructors and destructors are equivelent.
     Here we prove these equivalences, leaving them disabled by default;
     they can be used to prove theorems that involve
     relations between deep and shallow embedding."))

  (defruled value-schar-to-schar
    (equal (value-schar x)
           (schar x))
    :enable (value-schar schar))

  (defruled value-uchar-to-uchar
    (equal (value-uchar x)
           (uchar x))
    :enable (value-uchar uchar))

  (defruled value-sshort-to-sshort
    (equal (value-sshort x)
           (sshort x))
    :enable (value-sshort sshort))

  (defruled value-ushort-to-ushort
    (equal (value-ushort x)
           (ushort x))
    :enable (value-ushort ushort))

  (defruled value-sint-to-sint
    (equal (value-sint x)
           (sint x))
    :enable (value-sint sint))

  (defruled value-uint-to-uint
    (equal (value-uint x)
           (uint x))
    :enable (value-uint uint))

  (defruled value-slong-to-slong
    (equal (value-slong x)
           (slong x))
    :enable (value-slong slong))

  (defruled value-ulong-to-ulong
    (equal (value-ulong x)
           (ulong x))
    :enable (value-ulong ulong))

  (defruled value-sllong-to-sllong
    (equal (value-sllong x)
           (sllong x))
    :enable (value-sllong sllong))

  (defruled value-ullong-to-ullong
    (equal (value-ullong x)
           (ullong x))
    :enable (value-ullong ullong))

  (defruled value-schar->get-to-schar->get
    (implies (value-case x :schar)
             (equal (value-schar->get x)
                    (schar->get x)))
    :enable (value-schar->get schar->get))

  (defruled value-uchar->get-to-uchar->get
    (implies (value-case x :uchar)
             (equal (value-uchar->get x)
                    (uchar->get x)))
    :enable (value-uchar->get uchar->get))

  (defruled value-sshort->get-to-sshort->get
    (implies (value-case x :sshort)
             (equal (value-sshort->get x)
                    (sshort->get x)))
    :enable (value-sshort->get sshort->get))

  (defruled value-ushort->get-to-ushort->get
    (implies (value-case x :ushort)
             (equal (value-ushort->get x)
                    (ushort->get x)))
    :enable (value-ushort->get ushort->get))

  (defruled value-sint->get-to-sint->get
    (implies (value-case x :sint)
             (equal (value-sint->get x)
                    (sint->get x)))
    :enable (value-sint->get sint->get))

  (defruled value-uint->get-to-uint->get
    (implies (value-case x :uint)
             (equal (value-uint->get x)
                    (uint->get x)))
    :enable (value-uint->get uint->get))

  (defruled value-slong->get-to-slong->get
    (implies (value-case x :slong)
             (equal (value-slong->get x)
                    (slong->get x)))
    :enable (value-slong->get slong->get))

  (defruled value-ulong->get-to-ulong->get
    (implies (value-case x :ulong)
             (equal (value-ulong->get x)
                    (ulong->get x)))
    :enable (value-ulong->get ulong->get))

  (defruled value-sllong->get-to-sllong->get
    (implies (value-case x :sllong)
             (equal (value-sllong->get x)
                    (sllong->get x)))
    :enable (value-sllong->get sllong->get))

  (defruled value-ullong->get-to-ullong->get
    (implies (value-case x :ullong)
             (equal (value-ullong->get x)
                    (ullong->get x)))
    :enable (value-ullong->get ullong->get)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-valuep-rules
  :short "Rules for discharging @(tsee valuep) hypotheses."
  :long
  (xdoc::topstring
   (xdoc::p
    "Some symbolic execution rules have hypotheses saying that
     certain terms are values, i.e. satisfy @(tsee valuep).
     These are discharged by backchaining to
     the fact that those terms satisfy specific value predicates,
     such as @(tsee sintp)."))

  (defval *atc-valuep-rules*
    '(valuep-when-scharp
      valuep-when-ucharp
      valuep-when-sshortp
      valuep-when-ushortp
      valuep-when-sintp
      valuep-when-uintp
      valuep-when-slongp
      valuep-when-ulongp
      valuep-when-sllongp
      valuep-when-ullongp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-value-kind-rules
  :short "Rules to resolve @(tsee value-kind) for various kinds of values."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are used to relieve the hypothesis of
     the rule for executing identifiers,
     in @(tsee atc-exec-ident-rules)."))

  (defval *atc-value-kind-rules*
    '(value-kind-when-scharp
      value-kind-when-ucharp
      value-kind-when-sshortp
      value-kind-when-ushortp
      value-kind-when-sintp
      value-kind-when-uintp
      value-kind-when-slongp
      value-kind-when-ulongp
      value-kind-when-sllongp
      value-kind-when-ullongp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-integer-const-rules
  :short "Definition rules of the @('<type>-<base>-const')."
  :long
  (xdoc::topstring
   (xdoc::p
    "It may seem surprising that we expand these functions,
     since those correspond to C constructs;
     we certainly do not expand functions like @(tsee add-sint-sint).
     The reason is that functions like @(tsee sint-dec-const)
     are used to represent C constants in ACL2 functions,
     but in the dynamic semantics,
     @(tsee exec-iconst) (which we expand, obviously)
     produces terms of the form @('(sint <quoted-integer>)').
     By expanding @(tsee sint-dec-const) in the ACL2 functions,
     we produce terms of the form @('(sint <quoted-integer>)'),
     which therefore match the ones from @(tsee exec-iconst)."))

  (defval *atc-integer-const-rules*
    '(sint-dec-const
      sint-oct-const
      sint-hex-const
      uint-dec-const
      uint-oct-const
      uint-hex-const
      slong-dec-const
      slong-oct-const
      slong-hex-const
      ulong-dec-const
      ulong-oct-const
      ulong-hex-const
      sllong-dec-const
      sllong-oct-const
      sllong-hex-const
      ullong-dec-const
      ullong-oct-const
      ullong-hex-const)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-integer-size-rules
  :short "Rules related to integer sizes."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the same as the linear rules,
     but they are rewrite rules."))

  (make-event
   `(defruled uchar-max-vs-sint-max-rewrite
      ,(if (<= (uchar-max) (sint-max))
           '(<= (uchar-max) (sint-max))
         '(> (uchar-max) (sint-max)))))

  (make-event
   `(defruled ushort-max-vs-sint-max-rewrite
      ,(if (<= (ushort-max) (sint-max))
           '(<= (ushort-max) (sint-max))
         '(> (ushort-max) (sint-max)))))

  (make-event
   `(defruled uchar-max-vs-slong-max-rewrite
      ,(if (<= (uchar-max) (slong-max))
           '(<= (uchar-max) (slong-max))
         '(> (uchar-max) (slong-max)))))

  (make-event
   `(defruled ushort-max-vs-slong-max-rewrite
      ,(if (<= (ushort-max) (slong-max))
           '(<= (ushort-max) (slong-max))
         '(> (ushort-max) (slong-max)))))

  (make-event
   `(defruled uint-max-vs-slong-max-rewrite
      ,(if (<= (uint-max) (slong-max))
           '(<= (uint-max) (slong-max))
         '(> (uint-max) (slong-max)))))

  (make-event
   `(defruled uchar-max-vs-sllong-max-rewrite
      ,(if (<= (uchar-max) (sllong-max))
           '(<= (uchar-max) (sllong-max))
         '(> (uchar-max) (sllong-max)))))

  (make-event
   `(defruled ushort-max-vs-sllong-max-rewrite
      ,(if (<= (ushort-max) (sllong-max))
           '(<= (ushort-max) (sllong-max))
         '(> (ushort-max) (sllong-max)))))

  (make-event
   `(defruled uint-max-vs-sllong-max-rewrite
      ,(if (<= (uint-max) (sllong-max))
           '(<= (uint-max) (sllong-max))
         '(> (uint-max) (sllong-max)))))

  (make-event
   `(defruled ulong-max-vs-sllong-max-rewrute
      ,(if (<= (ulong-max) (sllong-max))
           '(<= (ulong-max) (sllong-max))
         '(> (ulong-max) (sllong-max))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *atc-integer-size-rules*
  :short "List of rules related to integer sizes."
  '(uchar-max-vs-sint-max-rewrite
    ushort-max-vs-sint-max-rewrite
    uchar-max-vs-slong-max-rewrite
    ushort-max-vs-slong-max-rewrite
    uint-max-vs-slong-max-rewrite
    uchar-max-vs-sllong-max-rewrite
    ushort-max-vs-sllong-max-rewrite
    uint-max-vs-sllong-max-rewrite
    ulong-max-vs-sllong-max-rewrute))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-integer-ifix-rules
  :short "Rules to simplify @(tsee ifix) applied to accessors of C integers."
  :long
  (xdoc::topstring
   (xdoc::p
    "The rule @('ifix-of-<type>->get') serves to simplify away
     occurrences of @(tsee ifix) used in
     the definition of the shift operations."))

  (defruled ifix-of-schar->get
    (equal (ifix (schar->get x))
           (schar->get x)))

  (defruled ifix-of-uchar->get
    (equal (ifix (uchar->get x))
           (uchar->get x)))

  (defruled ifix-of-sshort->get
    (equal (ifix (sshort->get x))
           (sshort->get x)))

  (defruled ifix-of-ushort->get
    (equal (ifix (ushort->get x))
           (ushort->get x)))

  (defruled ifix-of-sint->get
    (equal (ifix (sint->get x))
           (sint->get x)))

  (defruled ifix-of-uint->get
    (equal (ifix (uint->get x))
           (uint->get x)))

  (defruled ifix-of-slong->get
    (equal (ifix (slong->get x))
           (slong->get x)))

  (defruled ifix-of-ulong->get
    (equal (ifix (ulong->get x))
           (ulong->get x)))

  (defruled ifix-of-sllong->get
    (equal (ifix (sllong->get x))
           (sllong->get x)))

  (defruled ifix-of-ullong->get
    (equal (ifix (ullong->get x))
           (ullong->get x)))

  (defval *atc-integer-ifix-rules*
    '(ifix-of-schar->get
      ifix-of-uchar->get
      ifix-of-sshort->get
      ifix-of-ushort->get
      ifix-of-sint->get
      ifix-of-uint->get
      ifix-of-slong->get
      ifix-of-ulong->get
      ifix-of-sllong->get
      ifix-of-ullong->get)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-integer-fix-rules
  :short "Rules to simplify @('<type>-fix') applies to C integers."

  (defval *atc-integer-fix-rules*
    '(schar-fix-when-scharp
      uchar-fix-when-ucharp
      sshort-fix-when-sshortp
      ushort-fix-when-ushortp
      sint-fix-when-sintp
      uint-fix-when-uintp
      slong-fix-when-slongp
      ulong-fix-when-ulongp
      sllong-fix-when-sllongp
      ullong-fix-when-ullongp)))
