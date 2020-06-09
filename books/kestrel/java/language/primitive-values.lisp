; Java Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

(include-book "floating-point-placeholders")

(include-book "kestrel/fty/defflatsum" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ primitive-values
  :parents (semantics)
  :short "Java primitive values [JLS:4.2]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We formalize the Java boolean and integral values.
     We also provide abstract notions of the Java floating-point values,
     as a placeholder for a more precise formalization of them.")
   (xdoc::p
    "Our formalization tags the Java primitive values
     with an indication of their types
     (and, for floating-point values, of their value sets),
     making values of different types (and of floating-point value sets)
     disjoint.
     This will allow us
     to define a defensive semantics of Java
     and to prove that the static checks at compile time
     guarantee type safety at run time,
     as often done in programming language formalizations."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod boolean-value
  :short "Fixtype of Java @('boolean') values [JLS:4.2.5]."
  ((bool bool))
  :tag :boolean
  :layout :list
  :pred boolean-valuep
  ///

  (defruled boolean-valuep-alt-def
    (equal (boolean-valuep x)
           (or (equal x (boolean-value t))
               (equal x (boolean-value nil))))
    :enable boolean-valuep))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod char-value
  :short "Fixtype of Java @('char') values [JLS:4.2.1]."
  ((nat ubyte16))
  :tag :char
  :layout :list
  :pred char-valuep
  ///

  (defrule char-value->nat-upper-bound
    (<= (char-value->nat x) 65535)
    :rule-classes :linear
    :enable (char-value->nat
             acl2::ubyte16p
             acl2::ubyte16-fix)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod byte-value
  :short "Fixtype of Java @('byte') values [JLS:4.2.1]."
  ((int sbyte8))
  :tag :byte
  :layout :list
  :pred byte-valuep
  ///

  (defrule byte-value->int-lower-bound
    (<= -128 (byte-value->int x))
    :rule-classes :linear
    :enable (byte-value->int
             acl2::sbyte8p
             acl2::sbyte8-fix))

  (defrule byte-value->int-upper-bound
    (<= (byte-value->int x) 127)
    :rule-classes :linear
    :enable (byte-value->int
             acl2::sbyte8p
             acl2::sbyte8-fix)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod short-value
  :short "Fixtype of Java @('short') values [JLS:4.2.1]."
  ((int sbyte16))
  :tag :short
  :layout :list
  :pred short-valuep
  ///

  (defrule short-value->int-lower-bound
    (<= -32768 (short-value->int x))
    :rule-classes :linear
    :enable (short-value->int
             acl2::sbyte16p
             acl2::sbyte16-fix))

  (defrule short-value->int-upper-bound
    (<= (short-value->int x) 32767)
    :rule-classes :linear
    :enable (short-value->int
             acl2::sbyte16p
             acl2::sbyte16-fix)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod int-value
  :short "Fixtype of Java @('int') values [JLS:4.2.1]."
  ((int sbyte32))
  :tag :int
  :layout :list
  :pred int-valuep
  ///

  (defrule int-value->int-lower-bound
    (<= -2147483648 (int-value->int x))
     :rule-classes :linear
    :enable (int-value->int
             acl2::sbyte32p
             acl2::sbyte32-fix))

  (defrule int-value->int-upper-bound
    (<= (int-value->int x) 2147483647)
    :rule-classes :linear
    :enable (int-value->int
             acl2::sbyte32p
             acl2::sbyte32-fix)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod long-value
  :short "Fixtype of Java @('long') values [JLS:4.2.1]."
  ((int sbyte64))
  :tag :long
  :layout :list
  :pred long-valuep
  ///

  (defrule long-value->int-lower-bound
    (<= -9223372036854775808 (long-value->int x))
     :rule-classes :linear
    :enable (long-value->int
             acl2::sbyte64p
             acl2::sbyte64-fix))

  (defrule long-value->int-upper-bound
    (<= (long-value->int x) 9223372036854775807)
    :rule-classes :linear
    :enable (long-value->int
             acl2::sbyte64p
             acl2::sbyte64-fix)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod float-value
  :short "Fixtype of Java @('float') values
          in the float value set [JLS:4.2.3]."
  ((float float-value-abs))
  :tag :float
  :layout :list
  :pred float-valuep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod double-value
  :short "Fixtype of Java @('double') values
          in the double value set [JLS:4.2.3]."
  ((double double-value-abs))
  :tag :double
  :layout :list
  :pred double-valuep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist boolean-value-list
  :short "Fixtype of lists of Java @('boolean') values."
  :elt-type boolean-value
  :true-listp t
  :elementp-of-nil nil
  :pred boolean-value-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist char-value-list
  :short "Fixtype of lists of Java @('char') values."
  :elt-type char-value
  :true-listp t
  :elementp-of-nil nil
  :pred char-value-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist byte-value-list
  :short "Fixtype of lists of Java @('byte') values."
  :elt-type byte-value
  :true-listp t
  :elementp-of-nil nil
  :pred byte-value-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist short-value-list
  :short "Fixtype of lists of Java @('short') values."
  :elt-type short-value
  :true-listp t
  :elementp-of-nil nil
  :pred short-value-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist int-value-list
  :short "Fixtype of lists of Java @('int') values."
  :elt-type int-value
  :true-listp t
  :elementp-of-nil nil
  :pred int-value-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist long-value-list
  :short "Fixtype of lists of Java @('long') values."
  :elt-type long-value
  :true-listp t
  :elementp-of-nil nil
  :pred long-value-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist float-value-list
  :short "Fixtype of lists of Java @('float') values."
  :elt-type float-value
  :true-listp t
  :elementp-of-nil nil
  :pred float-value-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist double-value-list
  :short "Fixtype of lists of Java @('double') values."
  :elt-type double-value
  :true-listp t
  :elementp-of-nil nil
  :pred double-value-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection floatx-value-fns
  :short "Recognizer, fixer, constructor, and destructor of
          Java @('float') values
          in the float-extended-exponent value set [JLS.4.2.3]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We define the recognizer analogously to the one of
     the fixtypes of other Java primitive values,
     by tagging the underlying values introduced in @(tsee floatx-value-abs).
     The recognizer is non-empty if and only if
     @(tsee floatx-param) is non-@('nil').
     We define a conditional fixer,
     but we cannot define a fixtype because the recognizer may be empty.
     We also define a conditional constructor and a conditional destructor,
     analogous to the ones of the fixtypes of other Java primitive values."))

  (define floatx-valuep (x)
    :returns (yes/no booleanp)
    :parents (floatx-value-fns)
    :short "Recognizer of Java @('float') values
            in the float-extended-exponent value set."
    (and (tuplep 2 x)
         (eq (first x) :floatx)
         (floatx-value-abs-p (second x)))
    ///
    (defrule no-floatx-value-when-unsupported
      (implies (not (floatx-param))
               (not (floatx-valuep x)))))

  (local (in-theory (enable floatx-valuep)))

  (define floatx-value-fix ((x floatx-valuep))
    :returns (fixed-x floatx-valuep :hyp (floatx-param))
    :parents (floatx-value-fns)
    :short "Fixer of Java @('float') values
            in the float-extended-exponent value set."
    (mbe :logic (if (floatx-valuep x)
                    x
                  (list :floatx (floatx-value-abs-pos-zero)))
         :exec x)
    ///
    (defrule floatx-value-fix-when-floatx-valuep
      (implies (floatx-valuep x)
               (equal (floatx-value-fix x) x))))

  (local (in-theory (enable floatx-value-fix)))

  (define floatx-value ((x floatx-value-abs-p))
    :returns (value floatx-valuep :hyp (floatx-param))
    :parents (floatx-value-fns)
    :short "Constructor of Java @('float') values
            in the float-extended-exponent value set."
    (list :floatx (floatx-value-abs-fix x)))

  (define floatx-value->floatx ((value floatx-valuep))
    :returns (x floatx-value-abs-p :hyp (floatx-param))
    :parents (floatx-value-fns)
    :short "Destructor of Java @('float') values
            in the float-extended-exponent value set."
    (second (floatx-value-fix value))
    ///
    (defrule floatx-value->floatx-of-floatx-value
      (implies (floatx-param)
               (equal (floatx-value->floatx (floatx-value x))
                      (floatx-value-abs-fix x)))
      :enable floatx-value)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection doublex-value-fns
  :short "Recognizer, fixer, constructor, and destructor of
          Java @('double') values
          in the double-extended-exponent value set [JLS.4.2.3]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We define the recognizer analogously to the one of
     the fixtypes of other Java primitive values,
     by tagging the underlying values introduced in @(tsee doublex-value-abs).
     The recognizer is non-empty if and only if
     @(tsee doublex-param) is non-@('nil').
     We define a conditional fixer,
     but we cannot define a fixtype because the recognizer may be empty.
     We also define a conditional constructor and a conditional destructor,
     analogous to the ones of the fixtypes of other Java primitive values."))

  (define doublex-valuep (x)
    :returns (yes/no booleanp)
    :parents (doublex-value-fns)
    :short "Recognizer of Java @('double') values
            in the double-extended-exponent value set."
    (and (tuplep 2 x)
         (eq (first x) :doublex)
         (doublex-value-abs-p (second x)))
    ///
    (defrule no-doublex-value-when-unsupported
      (implies (not (doublex-param))
               (not (doublex-valuep x)))))

  (local (in-theory (enable doublex-valuep)))

  (define doublex-value-fix ((x doublex-valuep))
    :returns (fixed-x doublex-valuep :hyp (doublex-param))
    :parents (doublex-value-fns)
    :short "Fixer of Java @('double') values
            in the double-extended-exponent value set."
    (mbe :logic (if (doublex-valuep x)
                    x
                  (list :doublex (doublex-value-abs-pos-zero)))
         :exec x)
    ///
    (defrule doublex-value-fix-when-doublex-valuep
      (implies (doublex-valuep x)
               (equal (doublex-value-fix x) x))))

  (local (in-theory (enable doublex-value-fix)))

  (define doublex-value ((x doublex-value-abs-p))
    :returns (value doublex-valuep :hyp (doublex-param))
    :parents (doublex-value-fns)
    :short "Constructor of Java @('double') values
            in the double-extended-exponent value set."
    (list :doublex (doublex-value-abs-fix x)))

  (define doublex-value->doublex ((value doublex-valuep))
    :returns (x doublex-value-abs-p :hyp (doublex-param))
    :parents (doublex-value-fns)
    :short "Destructor of Java @('double') values
            in the double-extended-exponent value set."
    (second (doublex-value-fix value))
    ///
    (defrule doublex-value->doublex-of-doublex-value
      (implies (doublex-param)
               (equal (doublex-value->doublex (doublex-value x))
                      (doublex-value-abs-fix x)))
      :enable doublex-value)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defflatsum integral-value
  :short "Fixtype of Java integral values [JLS:4.2.1]."
  (:char char-value)
  (:byte byte-value)
  (:short short-value)
  (:int int-value)
  (:long long-value)
  :pred integral-valuep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defflatsum floating-point-value
  :short "Fixtype of Java floating-point values [JLS:4.2.3],
          excluding extended-exponent values [JLS:4.2.3]."
  (:float float-value)
  (:double double-value)
  :pred floating-point-valuep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection floating-pointx-value
  :short "Fixtype of Java floating-point values [JLS:4.2.3],
          including extended-exponent values [JLS:4.2.3]."

  (define floating-pointx-valuep (x)
    :returns (yes/no booleanp)
    :parents (floating-pointx-value)
    :short "Recognizer for @(tsee floating-pointx-value)."
    (or (floating-point-valuep x)
        (floatx-valuep x)
        (doublex-valuep x))
    ///

    (defrule floating-pointx-valuep-when-floating-point-valuep
      (implies (floating-point-valuep x)
               (floating-pointx-valuep x)))

    (defrule floating-pointx-valuep-when-floatx-valuep
      (implies (floatx-valuep x)
               (floating-pointx-valuep x)))

    (defrule floating-pointx-valuep-when-doublex-valuep
      (implies (doublex-valuep x)
               (floating-pointx-valuep x))))

  (std::deffixer floating-pointx-value-fix
    :pred floating-pointx-valuep
    :body-fix (float-value (float-value-abs-pos-zero))
    :parents nil)

  (fty::deffixtype floating-pointx-value
    :pred floating-pointx-valuep
    :fix floating-pointx-value-fix
    :equiv floating-pointx-value-equiv
    :define t
    :forward t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defflatsum numeric-value
  :short "Fixtype of Java numeric values [JLS:4.2],
          excluding extended-exponent values [JLS:4.2.3]."
  (:char char-value)
  (:byte byte-value)
  (:short short-value)
  (:int int-value)
  (:long long-value)
  (:float float-value)
  (:double double-value)
  :pred numeric-valuep)

(defsection numeric-value-ext
  :extension numeric-value
  (defrule numeric-valuep-when-integral-valuep
    (implies (integral-valuep x)
             (numeric-valuep x))
    :enable integral-valuep))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection numericx-value
  :short "Fixtype of Java numeric values [JLS:4.2],
          including extended-exponent values [JLS:4.2.3]."

  (define numericx-valuep (x)
    :returns (yes/no booleanp)
    :parents (numericx-value)
    :short "Recognizer for @(tsee numericx-value)."
    (or (numeric-valuep x)
        (floatx-valuep x)
        (doublex-valuep x))
    ///

    (defrule numericx-valuep-when-numeric-valuep
      (implies (numeric-valuep x)
               (numericx-valuep x)))

    (defrule numericx-valuep-when-floatx-valuep
      (implies (floatx-valuep x)
               (numericx-valuep x)))

    (defrule numericx-valuep-when-doublex-valuep
      (implies (doublex-valuep x)
               (numericx-valuep x))))

  (std::deffixer numericx-value-fix
    :pred numericx-valuep
    :body-fix (char-value 0)
    :parents nil)

  (fty::deffixtype numericx-value
    :pred numericx-valuep
    :fix numericx-value-fix
    :equiv numericx-value-equiv
    :define t
    :forward t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defflatsum primitive-value
  :short "Fixtype of Java primitive values [JLS:4.2],
          excluding extended-exponent values [JLS:4.2.3]."
  (:boolean boolean-value)
  (:char char-value)
  (:byte byte-value)
  (:short short-value)
  (:int int-value)
  (:long long-value)
  (:float float-value)
  (:double double-value)
  :pred primitive-valuep)

(defsection primitive-value-ext
  :extension primitive-value
  (defrule primitive-valuep-when-numeric-valuep
    (implies (numeric-valuep x)
             (primitive-valuep x))
    :enable numeric-valuep))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection primitivex-value
  :short "Fixtype of Java primitive values [JLS:4.2],
          including extended-exponent values [JLS:4.2.3]."

  (define primitivex-valuep (x)
    :returns (yes/no booleanp)
    :parents (primitivex-value)
    :short "Recognizer for @(tsee primitivex-value)."
    (or (primitive-valuep x)
        (floatx-valuep x)
        (doublex-valuep x))
    ///

    (defrule primitivex-valuep-when-primitive-valuep
      (implies (primitive-valuep x)
               (primitivex-valuep x)))

    (defrule primitivex-valuep-when-numericx-valuep
      (implies (numericx-valuep x)
               (primitivex-valuep x))
      :enable numericx-valuep))

  (std::deffixer primitivex-value-fix
    :pred primitivex-valuep
    :body-fix (char-value 0)
    :parents (primitivex-value)
    :short "Fixer for @(tsee primitivex-value).")

  (fty::deffixtype primitivex-value
    :pred primitivex-valuep
    :fix primitivex-value-fix
    :equiv primitivex-value-equiv
    :define t
    :forward t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled disjoint-primitive-values
  :short "The tagging keywords make all the primitive values disjoint."
  (and (implies (boolean-valuep x)
                (and (not (char-valuep x))
                     (not (byte-valuep x))
                     (not (short-valuep x))
                     (not (int-valuep x))
                     (not (long-valuep x))
                     (not (float-valuep x))
                     (not (double-valuep x))
                     (not (floatx-valuep x))
                     (not (doublex-valuep x))))
       (implies (char-valuep x)
                (and (not (byte-valuep x))
                     (not (short-valuep x))
                     (not (int-valuep x))
                     (not (long-valuep x))
                     (not (float-valuep x))
                     (not (double-valuep x))
                     (not (floatx-valuep x))
                     (not (doublex-valuep x))))
       (implies (byte-valuep x)
                (and (not (short-valuep x))
                     (not (int-valuep x))
                     (not (long-valuep x))
                     (not (float-valuep x))
                     (not (double-valuep x))
                     (not (floatx-valuep x))
                     (not (doublex-valuep x))))
       (implies (short-valuep x)
                (and (not (int-valuep x))
                     (not (long-valuep x))
                     (not (float-valuep x))
                     (not (double-valuep x))
                     (not (floatx-valuep x))
                     (not (doublex-valuep x))))
       (implies (int-valuep x)
                (and (not (long-valuep x))
                     (not (float-valuep x))
                     (not (double-valuep x))
                     (not (floatx-valuep x))
                     (not (doublex-valuep x))))
       (implies (long-valuep x)
                (and (not (float-valuep x))
                     (not (double-valuep x))
                     (not (floatx-valuep x))
                     (not (doublex-valuep x))))
       (implies (float-valuep x)
                (and (not (double-valuep x))
                     (not (floatx-valuep x))
                     (not (doublex-valuep x))))
       (implies (double-valuep x)
                (and (not (floatx-valuep x))
                     (not (doublex-valuep x))))
       (implies (floatx-valuep x)
                (not (doublex-valuep x))))
  :enable (boolean-valuep
           char-valuep
           byte-valuep
           short-valuep
           int-valuep
           long-valuep
           float-valuep
           double-valuep
           floatx-valuep
           doublex-valuep))
