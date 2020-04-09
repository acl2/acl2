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
  ///

  (defruled boolean-value-p-alt-def
    (equal (boolean-value-p x)
           (or (equal x (boolean-value t))
               (equal x (boolean-value nil))))
    :enable boolean-value-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod char-value
  :short "Fixtype of Java @('char') values [JLS:4.2.1]."
  ((nat ubyte16))
  :tag :char
  :layout :list
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
  :layout :list)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod double-value
  :short "Fixtype of Java @('double') values
          in the double value set [JLS:4.2.3]."
  ((double double-value-abs))
  :tag :double
  :layout :list)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist boolean-value-list
  :short "Fixtype of true lists of Java @('boolean') values."
  :elt-type boolean-value
  :true-listp t
  :elementp-of-nil nil
  :pred boolean-value-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist char-value-list
  :short "Fixtype of true lists of Java @('char') values."
  :elt-type char-value
  :true-listp t
  :elementp-of-nil nil
  :pred char-value-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist byte-value-list
  :short "Fixtype of true lists of Java @('byte') values."
  :elt-type byte-value
  :true-listp t
  :elementp-of-nil nil
  :pred byte-value-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist short-value-list
  :short "Fixtype of true lists of Java @('short') values."
  :elt-type short-value
  :true-listp t
  :elementp-of-nil nil
  :pred short-value-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist int-value-list
  :short "Fixtype of true lists of Java @('int') values."
  :elt-type int-value
  :true-listp t
  :elementp-of-nil nil
  :pred int-value-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist long-value-list
  :short "Fixtype of true lists of Java @('long') values."
  :elt-type long-value
  :true-listp t
  :elementp-of-nil nil
  :pred long-value-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist float-value-list
  :short "Fixtype of true lists of Java @('float') values."
  :elt-type float-value
  :true-listp t
  :elementp-of-nil nil
  :pred float-value-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist double-value-list
  :short "Fixtype of true lists of Java @('double') values."
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

  (define floatx-value-p (x)
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
               (not (floatx-value-p x)))))

  (local (in-theory (enable floatx-value-p)))

  (define floatx-value-fix ((x floatx-value-p))
    :returns (fixed-x floatx-value-p :hyp (floatx-param))
    :parents (floatx-value-fns)
    :short "Fixer of Java @('float') values
            in the float-extended-exponent value set."
    (mbe :logic (if (floatx-value-p x)
                    x
                  (list :floatx (floatx-value-abs-pos-zero)))
         :exec x)
    ///
    (defrule floatx-value-fix-when-floatx-value-p
      (implies (floatx-value-p x)
               (equal (floatx-value-fix x) x))))

  (local (in-theory (enable floatx-value-fix)))

  (define floatx-value ((x floatx-value-abs-p))
    :returns (value floatx-value-p :hyp (floatx-param))
    :parents (floatx-value-fns)
    :short "Constructor of Java @('float') values
            in the float-extended-exponent value set."
    (list :floatx (floatx-value-abs-fix x)))

  (define floatx-value->floatx ((value floatx-value-p))
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

  (define doublex-value-p (x)
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
               (not (doublex-value-p x)))))

  (local (in-theory (enable doublex-value-p)))

  (define doublex-value-fix ((x doublex-value-p))
    :returns (fixed-x doublex-value-p :hyp (doublex-param))
    :parents (doublex-value-fns)
    :short "Fixer of Java @('double') values
            in the double-extended-exponent value set."
    (mbe :logic (if (doublex-value-p x)
                    x
                  (list :doublex (doublex-value-abs-pos-zero)))
         :exec x)
    ///
    (defrule doublex-value-fix-when-doublex-value-p
      (implies (doublex-value-p x)
               (equal (doublex-value-fix x) x))))

  (local (in-theory (enable doublex-value-fix)))

  (define doublex-value ((x doublex-value-abs-p))
    :returns (value doublex-value-p :hyp (doublex-param))
    :parents (doublex-value-fns)
    :short "Constructor of Java @('double') values
            in the double-extended-exponent value set."
    (list :doublex (doublex-value-abs-fix x)))

  (define doublex-value->doublex ((value doublex-value-p))
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
  (:long long-value))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defflatsum floating-point-value
  :short "Fixtype of Java floating-point values [JLS:4.2.3],
          excluding extended-exponent values [JLS:4.2.3]."
  (:float float-value)
  (:double double-value))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection floating-pointx-value
  :short "Fixtype of Java floating-point values [JLS:4.2.3],
          including extended-exponent values [JLS:4.2.3]."

  (define floating-pointx-value-p (x)
    :returns (yes/no booleanp)
    :parents (floating-pointx-value)
    :short "Recognizer for @(tsee floating-pointx-value)."
    (or (floating-point-value-p x)
        (floatx-value-p x)
        (doublex-value-p x))
    ///

    (defrule floating-pointx-value-p-when-floating-point-value-p
      (implies (floating-point-value-p x)
               (floating-pointx-value-p x)))

    (defrule floating-pointx-value-p-when-floatx-value-p
      (implies (floatx-value-p x)
               (floating-pointx-value-p x)))

    (defrule floating-pointx-value-p-when-doublex-value-p
      (implies (doublex-value-p x)
               (floating-pointx-value-p x))))

  (std::deffixer floating-pointx-value-fix
    :pred floating-pointx-value-p
    :body-fix (float-value (float-value-abs-pos-zero))
    :parents nil)

  (fty::deffixtype floating-pointx-value
    :pred floating-pointx-value-p
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
  (:double double-value))

(defsection numeric-value-ext
  :extension numeric-value
  (defrule numeric-value-p-when-integral-value-p
    (implies (integral-value-p x)
             (numeric-value-p x))
    :enable integral-value-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection numericx-value
  :short "Fixtype of Java numeric values [JLS:4.2],
          including extended-exponent values [JLS:4.2.3]."

  (define numericx-value-p (x)
    :returns (yes/no booleanp)
    :parents (numericx-value)
    :short "Recognizer for @(tsee numericx-value)."
    (or (numeric-value-p x)
        (floatx-value-p x)
        (doublex-value-p x))
    ///

    (defrule numericx-value-p-when-numeric-value-p
      (implies (numeric-value-p x)
               (numericx-value-p x)))

    (defrule numericx-value-p-when-floatx-value-p
      (implies (floatx-value-p x)
               (numericx-value-p x)))

    (defrule numericx-value-p-when-doublex-value-p
      (implies (doublex-value-p x)
               (numericx-value-p x))))

  (std::deffixer numericx-value-fix
    :pred numericx-value-p
    :body-fix (char-value 0)
    :parents nil)

  (fty::deffixtype numericx-value
    :pred numericx-value-p
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
  (:double double-value))

(defsection primitive-value-ext
  :extension primitive-value
  (defrule primitive-value-p-when-numeric-value-p
    (implies (numeric-value-p x)
             (primitive-value-p x))
    :enable numeric-value-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection primitivex-value
  :short "Fixtype of Java primitive values [JLS:4.2],
          including extended-exponent values [JLS:4.2.3]."

  (define primitivex-value-p (x)
    :returns (yes/no booleanp)
    :parents (primitivex-value)
    :short "Recognizer for @(tsee primitivex-value)."
    (or (primitive-value-p x)
        (floatx-value-p x)
        (doublex-value-p x))
    ///

    (defrule primitivex-value-p-when-primitive-value-p
      (implies (primitive-value-p x)
               (primitivex-value-p x)))

    (defrule primitivex-value-p-when-numericx-value-p
      (implies (numericx-value-p x)
               (primitivex-value-p x))
      :enable numericx-value-p))

  (std::deffixer primitivex-value-fix
    :pred primitivex-value-p
    :body-fix (char-value 0)
    :parents (primitivex-value)
    :short "Fixer for @(tsee primitivex-value).")

  (fty::deffixtype primitivex-value
    :pred primitivex-value-p
    :fix primitivex-value-fix
    :equiv primitivex-value-equiv
    :define t
    :forward t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled disjoint-primitive-values
  :short "The tagging keywords make all the primitive values disjoint."
  (and (implies (boolean-value-p x)
                (and (not (char-value-p x))
                     (not (byte-value-p x))
                     (not (short-value-p x))
                     (not (int-value-p x))
                     (not (long-value-p x))
                     (not (float-value-p x))
                     (not (double-value-p x))
                     (not (floatx-value-p x))
                     (not (doublex-value-p x))))
       (implies (char-value-p x)
                (and (not (byte-value-p x))
                     (not (short-value-p x))
                     (not (int-value-p x))
                     (not (long-value-p x))
                     (not (float-value-p x))
                     (not (double-value-p x))
                     (not (floatx-value-p x))
                     (not (doublex-value-p x))))
       (implies (byte-value-p x)
                (and (not (short-value-p x))
                     (not (int-value-p x))
                     (not (long-value-p x))
                     (not (float-value-p x))
                     (not (double-value-p x))
                     (not (floatx-value-p x))
                     (not (doublex-value-p x))))
       (implies (short-value-p x)
                (and (not (int-value-p x))
                     (not (long-value-p x))
                     (not (float-value-p x))
                     (not (double-value-p x))
                     (not (floatx-value-p x))
                     (not (doublex-value-p x))))
       (implies (int-value-p x)
                (and (not (long-value-p x))
                     (not (float-value-p x))
                     (not (double-value-p x))
                     (not (floatx-value-p x))
                     (not (doublex-value-p x))))
       (implies (long-value-p x)
                (and (not (float-value-p x))
                     (not (double-value-p x))
                     (not (floatx-value-p x))
                     (not (doublex-value-p x))))
       (implies (float-value-p x)
                (and (not (double-value-p x))
                     (not (floatx-value-p x))
                     (not (doublex-value-p x))))
       (implies (double-value-p x)
                (and (not (floatx-value-p x))
                     (not (doublex-value-p x))))
       (implies (floatx-value-p x)
                (not (doublex-value-p x))))
  :enable (boolean-value-p
           char-value-p
           byte-value-p
           short-value-p
           int-value-p
           long-value-p
           float-value-p
           double-value-p
           floatx-value-p
           doublex-value-p))
