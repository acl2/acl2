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
(include-book "primitive-types")

(include-book "centaur/fty/top" :dir :system)
(include-book "kestrel/fty/ubyte16" :dir :system)
(include-book "kestrel/fty/sbyte8" :dir :system)
(include-book "kestrel/fty/sbyte16" :dir :system)
(include-book "kestrel/fty/sbyte32" :dir :system)
(include-book "kestrel/fty/sbyte64" :dir :system)
(include-book "kestrel/std/util/defconstrained-recognizer" :dir :system)
(include-book "kestrel/std/util/deffixer" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ floating-point-placeholders
  :parents (semantics)
  :short "Abstract placeholders for the Java floating-point
          values [JLS:4.2.3],
          operations [JLS:4.2.4],
          and conversions [JLS:5.1]."
  :long
  (xdoc::topstring
   (xdoc::p
    "Formalizing (Java) floating-point values and their operations is complex.
     Many interesting Java programs do not use floating-point values;
     these programs can be formally described by a formal model of Java
     that does not (yet) include floating-point values.
     Thus, for now our formal model of Java
     does not formalize floating-point values and operations.")
   (xdoc::p
    "However, instead of saying something like
     `there are no floating-point values',
     our model says something like
     `there are floating-point values, but we do not know much about them yet'.
     This is achieved by introducing weakly constrained ACL2 functions
     that recognize floating-point values
     and capture operations and conversions on them.
     These are analogues of the fully defined recognizers and other functions
     over the ACL2 values used to formalize the other (i.e. non-floating-point)
     Java primitive values and operations,
     such as the recognizer @(tsee sbyte32p) for @('int').")
   (xdoc::p
    "Eventually, these weakly constrained ACL2 functions
     will be replaced with fully defined ones that accurately capture
     floating-point values, operations, and conversions.
     This is expected to necessitate minimal (if any) adaptations
     to the rest of our formal model of Java,
     because the model already includes (abstract) Java floating-point values.
     In contrast, if our current model omitted floating-point values altogether,
     more laborious adaptations would be expected
     when adding the floating-point values later,
     e.g. functions defined by cases on the primitive values
     would have to be extended to cover the newly added cases."))
  :order-subtopics t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ floating-point-value-placeholders
  :parents (floating-point-placeholders)
  :short "Abstract placeholders for
          the Java floating-point values [JLS:4.2.3]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We introduce constrained recognizers for
     the float and double value sets, as well as for
     the float-extended-exponent and double-extended-exponent value sets
     [JLS:4.2.3].
     The recognizers for the float and double value sets
     are constrained to be non-empty,
     via a companion nullary witness function for each,
     which we also use to define a fixer and a fixtype.
     The recognizers of the extended-exponent value sets
     are constrained to be non-empty if and only if
     the respective value sets are supported,
     as described by the "
    (xdoc::seetopic "floating-point-value-set-parameters" "parameters")
    " of our model;
     their non-emptiness constraints is also expressed via
     companion nullary witness functions.
     Since the non-emptiness is conditional (to the parameter's value),
     we define conditional fixers, but cannot define fixtypes.
     The nullary witness function for each value sets
     is regarded as returning the positive 0 for that value set,
     which is the default value for floating-point variables [JLS:4.12.5];
     this is just reflected in the name of the witness function,
     not in any constraint property of it."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection float-value-abs
  :short "Abstract fixtype for the float value set [JLS:4.2.3]."
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
     this is expressed via a constrained nullary function
     that returns the positive 0 of the float value set.
     These constraints enable the definition of a fixer and fixtype.")
   (xdoc::@def "float-value-abs-p")
   (xdoc::@def "float-value-abs-pos-zero"))

  (std::defconstrained-recognizer float-value-abs-p
    :nonempty float-value-abs-pos-zero)

  (std::deffixer float-value-abs-fix
    :pred float-value-abs-p
    :body-fix (float-value-abs-pos-zero)
    :parents (float-value-abs)
    :short "Fixer for @(tsee float-value-abs).")

  (in-theory (disable (:e float-value-abs-fix)))

  (fty::deffixtype float-value-abs
    :pred float-value-abs-p
    :fix float-value-abs-fix
    :equiv float-value-abs-equiv
    :define t
    :forward t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection double-value-abs
  :short "Abstract fixtype for the double value set [JLS:4.2.3]."
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
     this is expressed via a constrained nullary function
     that returns the positive 0 of the double value set.
     These constraints enable the definition of a fixer and fixtype.")
   (xdoc::@def "double-value-abs-p")
   (xdoc::@def "double-value-abs-pos-zero"))

  (std::defconstrained-recognizer double-value-abs-p
    :nonempty double-value-abs-pos-zero)

  (std::deffixer double-value-abs-fix
    :pred double-value-abs-p
    :body-fix (double-value-abs-pos-zero)
    :parents (double-value-abs)
    :short "Fixer for @(tsee double-value-abs).")

  (in-theory (disable (:e double-value-abs-fix)))

  (fty::deffixtype double-value-abs
    :pred double-value-abs-p
    :fix double-value-abs-fix
    :equiv double-value-abs-equiv
    :define t
    :forward t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection floatx-value-abs
  :short "Abstract recognizer and fixer
          for the float-extended-exponent value set [JLS:4.2.3]."
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
     Non-emptiness is expressed via a constrained nullary function
     that returns the positive 0 of the float-extended-exponent value set.
     Since the predicate may be empty,
     we cannot define a fixtype,
     but we define a conditional fixer.")
   (xdoc::@def "floatx-value-abs-p")
   (xdoc::@def "floatx-value-abs-pos-zero"))

  (encapsulate
    (((floatx-value-abs-p *) => *)
     ((floatx-value-abs-pos-zero) => *))
    (local (defun floatx-value-abs-p (x) (if (floatx-param) (natp x) nil)))
    (local (defun floatx-value-abs-pos-zero () 0))
    (local (in-theory (disable (:e floatx-value-abs-p))))
    (defthm booleanp-of-floatx-value-abs-p
      (booleanp (floatx-value-abs-p x))
      :rule-classes (:rewrite :type-prescription))
    (defrule not-floatx-value-abs-p-when-not-floatx-param
      (implies (not (floatx-param))
               (not (floatx-value-abs-p x))))
    (defrule floatx-value-abs-p-of-floatx-value-abs-pos-zero-when-floatx-param
      (implies (floatx-param)
               (floatx-value-abs-p (floatx-value-abs-pos-zero)))))

  (define floatx-value-abs-fix ((x floatx-value-abs-p))
    :returns (fixed-x floatx-value-abs-p :hyp (floatx-param))
    :parents nil
    (mbe :logic (if (floatx-value-abs-p x)
                    x
                  (floatx-value-abs-pos-zero))
         :exec x)
    ///
    (defrule floatx-value-abs-fix-when-floatx-value-abs-p
      (implies (floatx-value-abs-p x)
               (equal (floatx-value-abs-fix x) x)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection doublex-value-abs
  :short "Abstract recognizer and fixer
          for the double-extended-exponent value set [JLS:4.2.3]."
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
     Non-emptiness is expressed via a constrained nullary function
     that returns the positive 0 of the double-extended-exponent value set.
     Since the predicate may be empty,
     we cannot define a fixtype,
     but we define a conditional fixer.")
   (xdoc::@def "doublex-value-abs-p")
   (xdoc::@def "doublex-value-abs-pos-zero"))

  (encapsulate
    (((doublex-value-abs-p *) => *)
     ((doublex-value-abs-pos-zero) => *))
    (local (defun doublex-value-abs-p (x) (if (doublex-param) (natp x) nil)))
    (local (defun doublex-value-abs-pos-zero () 0))
    (local (in-theory (disable (:e doublex-value-abs-p))))
    (defthm booleanp-of-doublex-value-abs-p
      (booleanp (doublex-value-abs-p x))
      :rule-classes (:rewrite :type-prescription))
    (defrule not-doublex-value-abs-p-when-not-doublex-param
      (implies (not (doublex-param))
               (not (doublex-value-abs-p x))))
    (defrule doublex-value-abs-p-of-doublex-value-abs-pos-zero-when-doublex-param
      (implies (doublex-param)
               (doublex-value-abs-p (doublex-value-abs-pos-zero)))))

  (define doublex-value-abs-fix ((x doublex-value-abs-p))
    :returns (fixed-x doublex-value-abs-p :hyp (doublex-param))
    :parents nil
    (mbe :logic (if (doublex-value-abs-p x)
                    x
                  (doublex-value-abs-pos-zero))
         :exec x)
    ///
    (defrule doublex-value-abs-fix-when-doublex-value-abs-p
      (implies (doublex-value-abs-p x)
               (equal (doublex-value-abs-fix x) x)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ floating-point-macro-placeholders
  :parents (floating-point-placeholders)
  :short "Macros to introduce more concisely the abstract placeholders for
          the Java floating-point operations and conversions."
  :long
  (xdoc::topstring
   (xdoc::p
    "All our abstract operations and conversions
     are weakly constraned ACL2 functions
     that unconditionally return results of the appropriate types.
     The macros capture this boilerplate structure.")
   (xdoc::p
    "For now we only introduce abstract functions that involve
     the float and double value sets,
     not the extended-exponent value sets.")
   (xdoc::p
    "The abstract functions operate not on the "
    (xdoc::seetopic "primitive-values" "tagged Java primitive values")
    ", but on their underlying (i.e. untagged) values."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define def-primitive-unary/binary-abs-term ((type primitive-typep))
  :returns (result "An untranslated term.")
  :short "Term for the result of a function introduced via
          @(tsee def-primitive-unary-abs) or @(tsee def-primitive-binary-abs)."
  (primitive-type-case type
                       :boolean nil
                       :char 0
                       :byte 0
                       :short 0
                       :int 0
                       :long 0
                       :float '(float-value-abs-pos-zero)
                       :double '(double-value-abs-pos-zero))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define def-primitive-unary/binary-abs-predicate ((type primitive-typep))
  :returns (predicate symbolp)
  :short "Predicate for the result of a function introduced via
          @(tsee def-primitive-unary-abs) or @(tsee def-primitive-binary-abs)."
  (primitive-type-case type
                       :boolean 'booleanp
                       :char 'ubyte16p
                       :byte 'sbyte8p
                       :short 'sbyte16p
                       :int 'sbyte32p
                       :long 'sbyte64p
                       :float 'float-value-abs-p
                       :double 'double-value-abs-p)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection def-primitive-unary-abs
  :short "Macro to introduce an abstract placeholder for
          a unary operation or a conversion
          involving floating-point values."
  :long
  (xdoc::topstring-@def "def-primitive-unary-abs")

  (define def-primitive-unary-abs-fn ((name symbolp) (type primitive-typep))
    :returns (event "A @(tsee acl2::pseudo-event-formp).")
    :parents nil
    (b* ((result (def-primitive-unary/binary-abs-term type))
         (predicate (def-primitive-unary/binary-abs-predicate type))
         (thm-name (add-suffix name "-TYPE")))
      `(encapsulate
         (((,name *) => *))
         (local (defun ,name (x) (declare (ignore x)) ,result))
         (defthm ,thm-name (,predicate (,name x))))))

  (defmacro def-primitive-unary-abs (name type)
    `(make-event (def-primitive-unary-abs-fn ',name ,type))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection def-primitive-binary-abs
  :short "Macro to introduce an abstract placeholder for
          a binary operation or a conversion
          involving floating-point values."
  :long
  (xdoc::topstring-@def "def-primitive-binary-abs")

  (define def-primitive-binary-abs-fn ((name symbolp) (type primitive-typep))
    :returns (event "A @(tsee acl2::pseudo-event-formp).")
    :parents nil
    (b* ((result (def-primitive-unary/binary-abs-term type))
         (predicate (def-primitive-unary/binary-abs-predicate type))
         (thm-name (add-suffix name "-TYPE")))
      `(encapsulate
         (((,name * *) => *))
         (local (defun ,name (x y) (declare (ignore x y)) ,result))
         (defthm ,thm-name (,predicate (,name x y))))))

  (defmacro def-primitive-binary-abs (name type)
    `(make-event (def-primitive-binary-abs-fn ',name ,type))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection floating-point-operation-placeholders
  :parents (floating-point-placeholders)
  :short "Abstract placeholders for
          the Java floating-point operations [JLS:4.2.4]."

  (def-primitive-unary-abs float-plus-abs (primitive-type-float))
  (def-primitive-unary-abs double-plus-abs (primitive-type-double))

  (def-primitive-unary-abs float-minus-abs (primitive-type-float))
  (def-primitive-unary-abs double-minus-abs (primitive-type-double))

  (def-primitive-binary-abs float-add-abs (primitive-type-float))
  (def-primitive-binary-abs double-add-abs (primitive-type-double))

  (def-primitive-binary-abs float-sub-abs (primitive-type-float))
  (def-primitive-binary-abs double-sub-abs (primitive-type-double))

  (def-primitive-binary-abs float-mul-abs (primitive-type-float))
  (def-primitive-binary-abs double-mul-abs (primitive-type-double))

  (def-primitive-binary-abs float-div-abs (primitive-type-float))
  (def-primitive-binary-abs double-div-abs (primitive-type-double))

  (def-primitive-binary-abs float-rem-abs (primitive-type-float))
  (def-primitive-binary-abs double-rem-abs (primitive-type-double))

  (def-primitive-binary-abs float-eq-abs (primitive-type-boolean))
  (def-primitive-binary-abs double-eq-abs (primitive-type-boolean))

  (def-primitive-binary-abs float-neq-abs (primitive-type-boolean))
  (def-primitive-binary-abs double-neq-abs (primitive-type-boolean))

  (def-primitive-binary-abs float-less-abs (primitive-type-boolean))
  (def-primitive-binary-abs double-less-abs (primitive-type-boolean))

  (def-primitive-binary-abs float-lesseq-abs (primitive-type-boolean))
  (def-primitive-binary-abs double-lesseq-abs (primitive-type-boolean))

  (def-primitive-binary-abs float-great-abs (primitive-type-boolean))
  (def-primitive-binary-abs double-great-abs (primitive-type-boolean))

  (def-primitive-binary-abs float-greateq-abs (primitive-type-boolean))
  (def-primitive-binary-abs double-greateq-abs (primitive-type-boolean)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection floating-point-conversion-placeholders
  :parents (floating-point-placeholders)
  :short "Abstract placeholders for
          the Java floating-point conversions [JLS:5.1]."

  ;; widening conversions:

  (def-primitive-unary-abs byte-to-float-abs (primitive-type-float))

  (def-primitive-unary-abs byte-to-double-abs (primitive-type-double))

  (def-primitive-unary-abs short-to-float-abs (primitive-type-float))

  (def-primitive-unary-abs short-to-double-abs (primitive-type-double))

  (def-primitive-unary-abs char-to-float-abs (primitive-type-float))

  (def-primitive-unary-abs char-to-double-abs (primitive-type-double))

  (def-primitive-unary-abs int-to-float-abs (primitive-type-float))

  (def-primitive-unary-abs int-to-double-abs (primitive-type-double))

  (def-primitive-unary-abs long-to-float-abs (primitive-type-float))

  (def-primitive-unary-abs long-to-double-abs (primitive-type-double))

  (def-primitive-unary-abs float-to-double-abs (primitive-type-double))

  ;; narrowing conversions:

  (def-primitive-unary-abs float-to-byte-abs (primitive-type-byte))

  (def-primitive-unary-abs float-to-short-abs (primitive-type-short))

  (def-primitive-unary-abs float-to-char-abs (primitive-type-char))

  (def-primitive-unary-abs float-to-int-abs (primitive-type-int))

  (def-primitive-unary-abs float-to-long-abs (primitive-type-long))

  (def-primitive-unary-abs double-to-byte-abs (primitive-type-byte))

  (def-primitive-unary-abs double-to-short-abs (primitive-type-short))

  (def-primitive-unary-abs double-to-char-abs (primitive-type-char))

  (def-primitive-unary-abs double-to-int-abs (primitive-type-int))

  (def-primitive-unary-abs double-to-long-abs (primitive-type-long))

  (def-primitive-unary-abs double-to-float-abs (primitive-type-float)))
