; Java Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

(include-book "floating-point-value-set-parameters")

(include-book "kestrel/fty/ubyte16" :dir :system)
(include-book "kestrel/fty/sbyte8" :dir :system)
(include-book "kestrel/fty/sbyte16" :dir :system)
(include-book "kestrel/fty/sbyte32" :dir :system)
(include-book "kestrel/fty/sbyte64" :dir :system)
(include-book "kestrel/std/util/defconstrained-recognizer" :dir :system)
(include-book "kestrel/std/util/deffixer" :dir :system)

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection float-value-aux
  :short "Auxiliary fixtype for @(tsee float-value)."
  :long
  (xdoc::topstring
   (xdoc::p
    "We introduce a constrained predicate for the underlying values
     of Java @('float') values in the float value set.
     The latter are defined by tagging the underlying values,
     in the same way that our model of the Java @('int') values (for instance)
     is defined by tagging 32-bit signed integers as the underlying values.")
   (xdoc::p
    "The predicate is constrained to be non-empty:
     this is expressed via a constrained nullary witness function.
     These constraints enable the definition of a fixer and fixtype.")
   (xdoc::@def "float-value-aux-p")
   (xdoc::@def "float-value-aux-witness"))

  (std::defconstrained-recognizer float-value-aux-p
    :nonempty float-value-aux-witness)

  (std::deffixer float-value-aux-fix
    :pred float-value-aux-p
    :body-fix (float-value-aux-witness)
    :parents (float-value-aux)
    :short "Fixer for @(tsee float-value-aux).")

  (in-theory (disable (:e float-value-aux-fix)))

  (fty::deffixtype float-value-aux
    :pred float-value-aux-p
    :fix float-value-aux-fix
    :equiv float-value-aux-equiv
    :define t
    :forward t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod float-value
  :short "Fixtype of Java @('float') values
          in the float value set [JLS:4.2.3]."
  ((float float-value-aux))
  :tag :float
  :layout :list)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection double-value-aux
  :short "Auxiliary fixtype for @(tsee double-value)."
  :long
  (xdoc::topstring
   (xdoc::p
    "We introduce a constrained predicate for the underlying values
     of Java @('double') values in the double value set.
     The latter are defined by tagging the underlying values,
     in the same way that our model of the Java @('int') values (for instance)
     is defined by tagging 32-bit signed integers as the underlying values.")
   (xdoc::p
    "The predicate is constrained to be non-empty:
     this is expressed via a constrained nullary witness function.
     These constraints enable the definition of a fixer and fixtype.")
   (xdoc::@def "double-value-aux-p")
   (xdoc::@def "double-value-aux-witness"))

  (std::defconstrained-recognizer double-value-aux-p
    :nonempty double-value-aux-witness)

  (std::deffixer double-value-aux-fix
    :pred double-value-aux-p
    :body-fix (double-value-aux-witness)
    :parents (double-value-aux)
    :short "Fixer for @(tsee double-value-aux).")

  (in-theory (disable (:e double-value-aux-fix)))

  (fty::deffixtype double-value-aux
    :pred double-value-aux-p
    :fix double-value-aux-fix
    :equiv double-value-aux-equiv
    :define t
    :forward t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod double-value
  :short "Fixtype of Java @('double') values
          in the double value set [JLS:4.2.3]."
  ((double double-value-aux))
  :tag :double
  :layout :list)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection floatx-value-aux
  :short "Auxiliary recognizer and fixer
          for @(tsee floatx-value-p) and @('floatx-value-fix')."
  :long
  (xdoc::topstring
   (xdoc::p
    "We introduce a constrained predicate for the underlying values
     of Java @('float') values in the float-extended-exponent value set.
     The latter are defined by tagging the underlying values,
     in the same way that our model of the Java @('int') values (for instance)
     is defined by tagging 32-bit signed integers as the underlying values.")
   (xdoc::p
    "The predicate is constrained to be empty
     if and only if @(tsee floatx-param) is @('nil'),
     i.e. if there are no extended-exponent @('float') values.
     Non-emptiness is expressed via a constrained nullary witness function.
     Since the predicate may be empty,
     we cannot define a fixtype,
     but we define a conditional fixer.")
   (xdoc::@def "floatx-value-aux-p")
   (xdoc::@def "floatx-value-aux-witness"))

  (encapsulate
    (((floatx-value-aux-p *) => *)
     ((floatx-value-aux-witness) => *))
    (local (defun floatx-value-aux-p (x) (if (floatx-param) (natp x) nil)))
    (local (defun floatx-value-aux-witness () 0))
    (local (in-theory (disable (:e floatx-value-aux-p))))
    (defthm booleanp-of-floatx-value-aux-p
      (booleanp (floatx-value-aux-p x))
      :rule-classes (:rewrite :type-prescription))
    (defrule not-floatx-value-aux-p-when-not-floatx-param
      (implies (not (floatx-param))
               (not (floatx-value-aux-p x))))
    (defrule floatx-value-aux-p-of-floatx-value-aux-witness-when-floatx-param
      (implies (floatx-param)
               (floatx-value-aux-p (floatx-value-aux-witness)))))

  (define floatx-value-aux-fix ((x floatx-value-aux-p))
    :returns (fixed-x floatx-value-aux-p :hyp (floatx-param))
    (mbe :logic (if (floatx-value-aux-p x)
                    x
                  (floatx-value-aux-witness))
         :exec x)
    ///
    (defrule floatx-value-aux-fix-when-floatx-value-aux-p
      (implies (floatx-value-aux-p x)
               (equal (floatx-value-aux-fix x) x)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection floatx-value-fns
  :short "Recognizer, fixer, constructor, and destructor of
          Java @('float') values
          in the float-extended-exponent value set [JLS.4.2.3]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We define the recognizer analogously to the one of
     the fixtypes of other Java primitive values,
     by tagging the underlying values introduced in @(tsee floatx-value-aux).
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
         (floatx-value-aux-p (second x)))
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
                  (list :floatx (floatx-value-aux-witness)))
         :exec x)
    ///
    (defrule floatx-value-fix-when-floatx-value-p
      (implies (floatx-value-p x)
               (equal (floatx-value-fix x) x))))

  (local (in-theory (enable floatx-value-fix)))

  (define floatx-value ((x floatx-value-aux-p))
    :returns (value floatx-value-p :hyp (floatx-param))
    :parents (floatx-value-fns)
    :short "Constructor of Java @('float') values
            in the float-extended-exponent value set."
    (list :floatx (floatx-value-aux-fix x)))

  (define floatx-value->floatx ((value floatx-value-p))
    :returns (x floatx-value-aux-p :hyp (floatx-param))
    :parents (floatx-value-fns)
    :short "Destructor of Java @('float') values
            in the float-extended-exponent value set."
    (second (floatx-value-fix value))
    ///
    (defrule floatx-value->floatx-of-floatx-value
      (implies (floatx-param)
               (equal (floatx-value->floatx (floatx-value x))
                      (floatx-value-aux-fix x)))
      :enable floatx-value)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection doublex-value-aux
  :short "Auxiliary recognizer and fixer
          for @(tsee doublex-value-p) and @('doublex-value-fix')."
  :long
  (xdoc::topstring
   (xdoc::p
    "We introduce a constrained predicate for the underlying values
     of Java @('double') values in the double-extended-exponent value set.
     The latter are defined by tagging the underlying values,
     in the same way that our model of the Java @('int') values (for instance)
     is defined by tagging 32-bit signed integers as the underlying values.")
   (xdoc::p
    "The predicate is constrained to be empty
     if and only if @(tsee doublex-param) is @('nil'),
     i.e. if there are no extended-exponent @('double') values.
     Non-emptiness is expressed via a constrained nullary witness function.
     Since the predicate may be empty,
     we cannot define a fixtype,
     but we define a conditional fixer.")
   (xdoc::@def "doublex-value-aux-p")
   (xdoc::@def "doublex-value-aux-witness"))

  (encapsulate
    (((doublex-value-aux-p *) => *)
     ((doublex-value-aux-witness) => *))
    (local (defun doublex-value-aux-p (x) (if (doublex-param) (natp x) nil)))
    (local (defun doublex-value-aux-witness () 0))
    (local (in-theory (disable (:e doublex-value-aux-p))))
    (defthm booleanp-of-doublex-value-aux-p
      (booleanp (doublex-value-aux-p x))
      :rule-classes (:rewrite :type-prescription))
    (defrule not-doublex-value-aux-p-when-not-doublex-param
      (implies (not (doublex-param))
               (not (doublex-value-aux-p x))))
    (defrule doublex-value-aux-p-of-doublex-value-aux-witness-when-doublex-param
      (implies (doublex-param)
               (doublex-value-aux-p (doublex-value-aux-witness)))))

  (define doublex-value-aux-fix ((x doublex-value-aux-p))
    :returns (fixed-x doublex-value-aux-p :hyp (doublex-param))
    (mbe :logic (if (doublex-value-aux-p x)
                    x
                  (doublex-value-aux-witness))
         :exec x)
    ///
    (defrule doublex-value-aux-fix-when-doublex-value-aux-p
      (implies (doublex-value-aux-p x)
               (equal (doublex-value-aux-fix x) x)))))

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
     by tagging the underlying values introduced in @(tsee doublex-value-aux).
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
         (doublex-value-aux-p (second x)))
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
                  (list :doublex (doublex-value-aux-witness)))
         :exec x)
    ///
    (defrule doublex-value-fix-when-doublex-value-p
      (implies (doublex-value-p x)
               (equal (doublex-value-fix x) x))))

  (local (in-theory (enable doublex-value-fix)))

  (define doublex-value ((x doublex-value-aux-p))
    :returns (value doublex-value-p :hyp (doublex-param))
    :parents (doublex-value-fns)
    :short "Constructor of Java @('double') values
            in the double-extended-exponent value set."
    (list :doublex (doublex-value-aux-fix x)))

  (define doublex-value->doublex ((value doublex-value-p))
    :returns (x doublex-value-aux-p :hyp (doublex-param))
    :parents (doublex-value-fns)
    :short "Destructor of Java @('double') values
            in the double-extended-exponent value set."
    (second (doublex-value-fix value))
    ///
    (defrule doublex-value->doublex-of-doublex-value
      (implies (doublex-param)
               (equal (doublex-value->doublex (doublex-value x))
                      (doublex-value-aux-fix x)))
      :enable doublex-value)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defflexsum integral-value
  :short "Fixtype of Java integral values [JLS:4.2.1]."
  (:char
   :fields ((get :type char-value :acc-body x))
   :ctor-body get
   :cond (char-value-p x))
  (:byte
   :fields ((get :type byte-value :acc-body x))
   :ctor-body get
   :cond (byte-value-p x))
  (:short
   :fields ((get :type short-value :acc-body x))
   :ctor-body get
   :cond (short-value-p x))
  (:int
   :fields ((get :type int-value :acc-body x))
   :ctor-body get
   :cond (int-value-p x))
  (:long
   :fields ((get :type long-value :acc-body x))
   :ctor-body get)
  :prepwork ((local (in-theory (enable char-value-p
                                       byte-value-p
                                       short-value-p
                                       int-value-p
                                       long-value-p
                                       char-value-fix
                                       byte-value-fix
                                       short-value-fix
                                       int-value-fix
                                       long-value-fix))))
  ///

  (local (in-theory (enable integral-value-p)))

  (defrule integral-value-p-when-char-value-p
    (implies (char-value-p x)
             (integral-value-p x)))

  (defrule integral-value-p-when-byte-value-p
    (implies (byte-value-p x)
             (integral-value-p x)))

  (defrule integral-value-p-when-short-value-p
    (implies (short-value-p x)
             (integral-value-p x)))

  (defrule integral-value-p-when-int-value-p
    (implies (int-value-p x)
             (integral-value-p x)))

  (defrule integral-value-p-when-long-value-p
    (implies (long-value-p x)
             (integral-value-p x))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defflexsum floating-point-value
  :short "Fixtype of Java floating-point values [JLS:4.2.3],
          excluding extended-exponent values [JLS:4.2.3]."
  (:float
   :fields ((get :type float-value :acc-body x))
   :ctor-body get
   :cond (float-value-p x))
  (:double
   :fields ((get :type double-value :acc-body x))
   :ctor-body get)
  :prepwork ((local (in-theory (enable float-value-p
                                       double-value-p
                                       float-value-fix
                                       double-value-fix))))
  ///

  (local (in-theory (enable floating-point-value-p)))

  (defrule floating-point-value-p-when-float-value-p
    (implies (float-value-p x)
             (floating-point-value-p x)))

  (defrule floating-point-value-p-when-double-value-p
    (implies (double-value-p x)
             (floating-point-value-p x))))

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
    :body-fix (float-value (float-value-aux-witness)))

  (fty::deffixtype floating-pointx-value
    :pred floating-pointx-value-p
    :fix floating-pointx-value-fix
    :equiv floating-pointx-value-equiv
    :define t
    :forward t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defflexsum numeric-value
  :short "Fixtype of Java numeric values [JLS:4.2],
          excluding extended-exponent values [JLS:4.2.3]."
  (:char
   :fields ((get :type char-value :acc-body x))
   :ctor-body get
   :cond (char-value-p x))
  (:byte
   :fields ((get :type byte-value :acc-body x))
   :ctor-body get
   :cond (byte-value-p x))
  (:short
   :fields ((get :type short-value :acc-body x))
   :ctor-body get
   :cond (short-value-p x))
  (:int
   :fields ((get :type int-value :acc-body x))
   :ctor-body get
   :cond (int-value-p x))
  (:long
   :fields ((get :type long-value :acc-body x))
   :ctor-body get
   :cond (long-value-p x))
  (:float
   :fields ((get :type float-value :acc-body x))
   :ctor-body get
   :cond (float-value-p x))
  (:double
   :fields ((get :type double-value :acc-body x))
   :ctor-body get)
  :prepwork ((local (in-theory (enable char-value-p
                                       byte-value-p
                                       short-value-p
                                       int-value-p
                                       long-value-p
                                       float-value-p
                                       double-value-p
                                       char-value-fix
                                       byte-value-fix
                                       short-value-fix
                                       int-value-fix
                                       long-value-fix
                                       float-value-fix
                                       double-value-fix))))
  ///

  (local (in-theory (enable numeric-value-p)))

  (defrule numeric-value-p-when-integral-value-p
    (implies (integral-value-p x)
             (numeric-value-p x))
    :enable integral-value-p)

  (defrule numeric-value-p-when-float-value-p
    (implies (float-value-p x)
             (numeric-value-p x)))

  (defrule numeric-value-p-when-double-value-p
    (implies (double-value-p x)
             (numeric-value-p x))))

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
    :body-fix (char-value 0))

  (fty::deffixtype numericx-value
    :pred numericx-value-p
    :fix numericx-value-fix
    :equiv numericx-value-equiv
    :define t
    :forward t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defflexsum primitive-value
  :short "Fixtype of Java primitive values [JLS:4.2],
          excluding extended-exponent values [JLS:4.2.3]."
  (:boolean
   :fields ((get :type boolean-value :acc-body x))
   :ctor-body get
   :cond (boolean-value-p x))
  (:char
   :fields ((get :type char-value :acc-body x))
   :ctor-body get
   :cond (char-value-p x))
  (:byte
   :fields ((get :type byte-value :acc-body x))
   :ctor-body get
   :cond (byte-value-p x))
  (:short
   :fields ((get :type short-value :acc-body x))
   :ctor-body get
   :cond (short-value-p x))
  (:int
   :fields ((get :type int-value :acc-body x))
   :ctor-body get
   :cond (int-value-p x))
  (:long
   :fields ((get :type long-value :acc-body x))
   :ctor-body get
   :cond (long-value-p x))
  (:float
   :fields ((get :type float-value :acc-body x))
   :ctor-body get
   :cond (float-value-p x))
  (:double
   :fields ((get :type double-value :acc-body x))
   :ctor-body get)
  :prepwork ((local (in-theory (enable boolean-value-p
                                       char-value-p
                                       byte-value-p
                                       short-value-p
                                       int-value-p
                                       long-value-p
                                       float-value-p
                                       double-value-p
                                       boolean-value-fix
                                       char-value-fix
                                       byte-value-fix
                                       short-value-fix
                                       int-value-fix
                                       long-value-fix
                                       float-value-fix
                                       double-value-fix))))
  ///

  (local (in-theory (enable primitive-value-p)))

  (defrule primitive-value-p-when-boolean-value-p
    (implies (boolean-value-p x)
             (primitive-value-p x)))

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
