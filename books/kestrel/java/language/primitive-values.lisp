; Java Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

(include-book "kestrel/fty/defbyte-standard-instances" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ primitive-values
  :parents (language)
  :short "Java primitive values [JLS:4.2]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We formalize the Java boolean and integral values.
     We also provide an abstract notion of the Java floating-point values,
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
  :short "Java @('boolean') values [JLS:4.2.5]."
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
  :short "Java @('char') values [JLS:4.2.1]."
  ((nat ubyte16))
  :tag :char
  :layout :list)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod byte-value
  :short "Java @('byte') values [JLS:4.2.1]."
  ((int sbyte8))
  :tag :byte
  :layout :list)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod short-value
  :short "Java @('short') values [JLS:4.2.1]."
  ((int sbyte16))
  :tag :short
  :layout :list)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod int-value
  :short "Java @('int') values [JLS:4.2.1]."
  ((int sbyte32))
  :tag :int
  :layout :list)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod long-value
  :short "Java @('long') values [JLS:4.2.1]."
  ((int sbyte64))
  :tag :long
  :layout :list)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection float-value
  :short "Java @('float') values in the float value set [JLS:4.2.3]."
  :long
  (xdoc::topstring
   (xdoc::p
    "For now we model these by tagging, with @(':float'),
     the ACL2 values recognized by a constrained predicate.
     The tagging and layout are analogous to the way in which we model
     the Java boolean and integral values.")
   (xdoc::p
    "The predicate is constrained to be non-empty:
     this is expressed via a constrained nullary witness function.
     These constraints enable the definition of a fixer and fixtype.")
   (xdoc::@def "float-value-p-aux")
   (xdoc::@def "float-value-witness"))

  (encapsulate
    (((float-value-p-aux *) => *)
     ((float-value-witness) => *))
    (local (defun float-value-p-aux (x) (natp x)))
    (local (defun float-value-witness () 0))
    (defrule booleanp-of-float-value-p-aux
      (booleanp (float-value-p-aux x))
      :rule-classes (:rewrite :type-prescription))
    (defrule float-value-p-aux-of-float-value-witness
      (float-value-p-aux (float-value-witness))))

  (define float-value-p (x)
    :returns (yes/no booleanp)
    (and (tuplep 2 x)
         (eq (first x) :float)
         (float-value-p-aux (second x))))

  (define float-value-fix ((x float-value-p))
    :returns (fixed-x float-value-p
                      :hints (("Goal" :in-theory (enable float-value-p))))
    (mbe :logic (if (float-value-p x)
                    x
                  (list :float (float-value-witness)))
         :exec x)
    ///
    (defrule float-value-fix-when-float-value-p
      (implies (float-value-p x)
               (equal (float-value-fix x) x))))

  (fty::deffixtype float-value
    :pred float-value-p
    :fix float-value-fix
    :equiv float-value-equiv
    :define t
    :forward t
    :topic float-value))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection double-value
  :short "Java @('double') values in the double value set [JLS:4.2.3]."
  :long
  (xdoc::topstring
   (xdoc::p
    "For now we model these by tagging, with @(':double'),
     the ACL2 values recognized by a constrained predicate.
     The tagging and layout are analogous to the way in which we model
     the Java boolean and integral values.")
   (xdoc::p
    "The predicate is constrained to be non-empty:
     this is expressed via a constrained nullary witness function.
     These constraints enable the definition of a fixer and fixtype.")
   (xdoc::@def "double-value-p-aux")
   (xdoc::@def "double-value-witness"))

  (encapsulate
    (((double-value-p-aux *) => *)
     ((double-value-witness) => *))
    (local (defun double-value-p-aux (x) (natp x)))
    (local (defun double-value-witness () 0))
    (defrule booleanp-of-double-value-p-aux
      (booleanp (double-value-p-aux x))
      :rule-classes (:rewrite :type-prescription))
    (defrule double-value-p-aux-of-double-value-witness
      (double-value-p-aux (double-value-witness))))

  (define double-value-p (x)
    :returns (yes/no booleanp)
    (and (tuplep 2 x)
         (eq (first x) :double)
         (double-value-p-aux (second x))))

  (define double-value-fix ((x double-value-p))
    :returns (fixed-x double-value-p
                      :hints (("Goal" :in-theory (enable double-value-p))))
    (mbe :logic (if (double-value-p x)
                    x
                  (list :double (double-value-witness)))
         :exec x)
    ///
    (defrule double-value-fix-when-double-value-p
      (implies (double-value-p x)
               (equal (double-value-fix x) x))))

  (fty::deffixtype double-value
    :pred double-value-p
    :fix double-value-fix
    :equiv double-value-equiv
    :define t
    :forward t
    :topic double-value))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define floatx-param-p (k)
  :returns (yes/no booleanp)
  :short "Recognize the possible parameters that describe
          a Java implementation's support of
          the float-extended-exponent value set [JLS:4.2.3]."
  :long
  (xdoc::topstring
   (xdoc::p
    "A Java implementation
     may support a float-extended-exponent value set or not.
     If it does, an implementation-dependent constant @($K$) [JLS:4.2.3]
     determines the exact values supported.")
   (xdoc::p
    "Our Java formalization is parameterized over the specifics of this support,
     via the value of the nullary function @(tsee floatx-param),
     which is constrained to be either @('nil') (indicating no support)
     or a positive integer that is at least 11 (the value of @($K$))."))
  (or (null k)
      (and (natp k)
           (>= k 11))))

(defsection floatx-param
  :short "Parameter that describes the support of
          the float-extended-exponent value set."
  :long (xdoc::topstring-@def "floatx-param")

  (encapsulate
    (((floatx-param) => *))
    (local (defun floatx-param () 11))
    (defrule floatx-param-p-of-floatx-param
      (floatx-param-p (floatx-param))))

  (defrule posp-of-floatx-param-when-non-nil
    (implies (floatx-param)
             (posp (floatx-param)))
    :use floatx-param-p-of-floatx-param
    :disable floatx-param-p-of-floatx-param
    :enable floatx-param-p)

  (defrule floatx-param-lower-bound-when-non-nil
    (implies (floatx-param)
             (>= (floatx-param) 11))
    :rule-classes :linear
    :use floatx-param-p-of-floatx-param
    :disable floatx-param-p-of-floatx-param
    :enable floatx-param-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define doublex-param-p (k)
  :returns (yes/no booleanp)
  :short "Recognize the possible parameters that describe
          a Java implementation's support of
          the double-extended-exponent value set [JLS:4.2.3]."
  :long
  (xdoc::topstring
   (xdoc::p
    "A Java implementation
     may support a double-extended-exponent value set or not.
     If it does, an implementation-dependent constant @($K$) [JLS:4.2.3]
     determines the exact values supported.")
   (xdoc::p
    "Our Java formalization is parameterized over the specifics of this support,
     via the value of the nullary function @(tsee doublex-param),
     which is constrained to be either @('nil') (indicating no support)
     or a positive integer that is at least 15 (the value of @($K$))."))
  (or (null k)
      (and (natp k)
           (>= k 15))))

(defsection doublex-param
  :short "Parameter that describes the support of
          the double-extended-exponent value set."
  :long (xdoc::topstring-@def "doublex-param")

  (encapsulate
    (((doublex-param) => *))
    (local (defun doublex-param () 15))
    (defrule doublex-param-p-of-doublex-param
      (doublex-param-p (doublex-param))))

  (defrule posp-of-doublex-param-when-non-nil
    (implies (doublex-param)
             (posp (doublex-param)))
    :use doublex-param-p-of-doublex-param
    :disable doublex-param-p-of-doublex-param
    :enable doublex-param-p)

  (defrule doublex-param-lower-bound-when-non-nil
    (implies (doublex-param)
             (>= (doublex-param) 15))
    :rule-classes :linear
    :use doublex-param-p-of-doublex-param
    :disable doublex-param-p-of-doublex-param
    :enable doublex-param-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection floatx-value
  :short "Java @('float') values in the float-extended-exponent value set
          [JLS.4.2.3]."
  :long
  (xdoc::topstring
   (xdoc::p
    "For now we model these by tagging, with @(':floatx'),
     the ACL2 values recognized by a constrained predicate.
     The tagging and layout are analogous to the way in which we model
     the Java boolean and integral values.")
   (xdoc::p
    "The predicate is constrained to be empty
     iff @(tsee floatx-param) is @('nil');
     non-emptiness is expressed via a constrained nullary witness function.
     Since the predicate may be empty,
     we cannot define a fixtype,
     but we define a conditional fixer.")
   (xdoc::@def "floatx-value-p-aux")
   (xdoc::@def "floatx-value-witness"))

  (encapsulate
    (((floatx-value-p-aux *) => *)
     ((floatx-value-witness) => *))
    (local (defun floatx-value-p-aux (x) (if (floatx-param) (natp x) nil)))
    (local (defun floatx-value-witness () 0))
    (local (in-theory (disable (:e floatx-value-p-aux))))
    (defthm booleanp-of-floatx-value-p-aux
      (booleanp (floatx-value-p-aux x))
      :rule-classes (:rewrite :type-prescription))
    (defrule not-floatx-value-p-aux-when-not-floatx-param
      (implies (not (floatx-param))
               (not (floatx-value-p-aux x))))
    (defrule floatx-value-p-aux-of-floatx-value-witness-when-floatx-param
      (implies (floatx-param)
               (floatx-value-p-aux (floatx-value-witness)))))

  (define floatx-value-p (x)
    :returns (yes/no booleanp)
    (and (tuplep 2 x)
         (eq (first x) :floatx)
         (floatx-value-p-aux (second x)))
    ///
    (defrule no-floatx-value-when-unsupported
      (implies (not (floatx-param))
               (not (floatx-value-p x)))))

  (define floatx-value-fix ((x floatx-value-p))
    :returns (fixed-x floatx-value-p
                      :hyp (floatx-param)
                      :hints (("Goal" :in-theory (enable floatx-value-p))))
    (mbe :logic (if (floatx-value-p x)
                    x
                  (list :floatx (floatx-value-witness)))
         :exec x)
    ///
    (defrule floatx-value-fix-when-floatx-value-p
      (implies (floatx-value-p x)
               (equal (floatx-value-fix x) x)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection doublex-value
  :short "Java @('double') values in the double-extended-exponent value set
          [JLS.4.2.3]."
  :long
  (xdoc::topstring
   (xdoc::p
    "For now we model these by tagging, with @(':doublex'),
     the ACL2 values recognized by a constrained predicate.
     The tagging and layout are analogous to the way in which we model
     the Java boolean and integral values.")
   (xdoc::p
    "The predicate is constrained to be empty
     iff @(tsee doublex-param) is @('nil');
     non-emptiness is expressed via a constrained nullary witness function.
     Since the predicate may be empty,
     we cannot define a fixtype,
     but we define a conditional fixer.")
   (xdoc::@def "doublex-value-p-aux")
   (xdoc::@def "doublex-value-witness"))

  (encapsulate
    (((doublex-value-p-aux *) => *)
     ((doublex-value-witness) => *))
    (local (defun doublex-value-p-aux (x) (if (doublex-param) (natp x) nil)))
    (local (defun doublex-value-witness () 0))
    (local (in-theory (disable (:e doublex-value-p-aux))))
    (defthm booleanp-of-doublex-value-p-aux
      (booleanp (doublex-value-p-aux x))
      :rule-classes (:rewrite :type-prescription))
    (defrule not-doublex-value-p-aux-when-not-doublex-param
      (implies (not (doublex-param))
               (not (doublex-value-p-aux x))))
    (defrule doublex-value-p-aux-of-doublex-value-witness-when-doublex-param
      (implies (doublex-param)
               (doublex-value-p-aux (doublex-value-witness)))))

  (define doublex-value-p (x)
    :returns (yes/no booleanp)
    (and (tuplep 2 x)
         (eq (first x) :doublex)
         (doublex-value-p-aux (second x)))
    ///
    (defrule no-doublex-value-when-unsupported
      (implies (not (doublex-param))
               (not (doublex-value-p x)))))

  (define doublex-value-fix ((x doublex-value-p))
    :returns (fixed-x doublex-value-p
                      :hyp (doublex-param)
                      :hints (("Goal" :in-theory (enable doublex-value-p))))
    (mbe :logic (if (doublex-value-p x)
                    x
                  (list :doublex (doublex-value-witness)))
         :exec x)
    ///
    (defrule doublex-value-fix-when-doublex-value-p
      (implies (doublex-value-p x)
               (equal (doublex-value-fix x) x)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defflexsum integral-value
  :short "Java integral values [JLS:4.2.1]."
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

(fty::defflexsum numeric-value
  :short "Java numeric values [JLS:4.2],
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
  :short "Java numeric values [JLS:4.2],
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

  (define numericx-value-fix ((x numericx-value-p))
    :returns (fixed-x numericx-value-p)
    :parents (numericx-value)
    :short "Fixer for @(tsee numericx-value)."
    (mbe :logic (if (numericx-value-p x) x (char-value 0))
         :exec x)
    ///
    (defrule numericx-value-fix-when-numericx-value-p
      (implies (numericx-value-p x)
               (equal (numericx-value-fix x) x))))

  (fty::deffixtype numericx-value
    :pred numericx-value-p
    :fix numericx-value-fix
    :equiv numericx-value-equiv
    :define t
    :forward t
    :topic numericx-value))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defflexsum primitive-value
  :short "Java primitive values [JLS:4.2],
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
  :short "Java primitive values [JLS:4.2],
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

  (define primitivex-value-fix ((x primitivex-value-p))
    :returns (fixed-x primitivex-value-p)
    :parents (primitivex-value)
    :short "Fixer for @(tsee primitivex-value)."
    (mbe :logic (if (primitivex-value-p x) x (char-value 0))
         :exec x)
    ///
    (defrule primitivex-value-fix-when-primitivex-value-p
      (implies (primitivex-value-p x)
               (equal (primitivex-value-fix x) x))))

  (fty::deffixtype primitivex-value
    :pred primitivex-value-p
    :fix primitivex-value-fix
    :equiv primitivex-value-equiv
    :define t
    :forward t
    :topic primitivex-value))

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
