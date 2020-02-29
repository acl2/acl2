; Java Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

(include-book "primitive-values")
(include-book "primitive-function-macros")

(include-book "ihs/basic-definitions" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrulel sbyte32p-of-logext32
  (sbyte32p (logext 32 x))
  :enable sbyte32p
  :prep-books ((include-book "arithmetic-5/top" :dir :system)))

(defrulel sbyte64p-of-logext64
  (sbyte64p (logext 64 x))
  :enable sbyte64p
  :prep-books ((include-book "arithmetic-5/top" :dir :system)))

(local (in-theory (disable logext)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ primitive-operations
  :parents (semantics)
  :short "Java primitive operations [JLS:4.2]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We formalize the Java boolean and integer operations
     [JLS:4.2.5] [JLS:4.2.2].
     We also provide abstract notions of the Java floating-point operations,
     as a placeholder for a more precise formalization of them.
     Primitive conversions [JLS:5.1.2-4] are formalized "
    (xdoc::seetopic "primitive-conversions" "here")
    "."))
  :order-subtopics t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ boolean-operations
  :parents (primitive-operations)
  :short "Java boolean operations [JLS:4.2.5]."
  :long
  (xdoc::topstring
   (xdoc::p
    "Here we formalize all the strict operations
     that take boolean operands and return boolean results.")
   (xdoc::p
    "[JLS:4.2.5] also lists
     the conditional operators @('&&'), @('||'), and @('? :'),
     but those are non-strict,
     and therefore must be formalized as part of expression evaluation.")
   (xdoc::p
    "[JLS:4.2.5] also lists the string concatenation operator @('+'),
     but that is best formalized in terms of a boolean-to-string conversion,
     elsewhere."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-boolean-unary boolean-not
  :operation (not x)
  :short "Logical complement @('!') [JLS:4.2.5] [JLS:15.15.6].")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-boolean-binary boolean-and
  :operation (and x y)
  :short "Logical conjunction @('&') [JLS:4.2.5] [JLS:15.22.2].")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-boolean-binary boolean-xor
  :operation (not (equal x y))
  :short "Logical exclusive disjunction @('^') [JLS:4.2.5] [JLS:15.22.2].")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-boolean-binary boolean-ior
  :operation (or x y)
  :short "Logical inclusive disjunction @('|') [JLS:4.2.5] [JLS:15.22.2].")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-boolean-binary boolean-eq
  :operation (equal x y)
  :short "Equality @('==') on @('boolean')s [JLS:4.2.5] [JLS:15.21.2].")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-boolean-binary boolean-neq
  :operation (not (equal x y))
  :short "Non-equality @('!=') on @('boolean')s [JLS:4.2.5] [JLS:15.21.2].")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ integer-operations
  :parents (primitive-operations)
  :short "Java integer operations [JLS:4.2.2]."
  :long
  (xdoc::topstring
   (xdoc::p
    "Here we formalize all the unary and binary operations on integral values
     that are not conversions (those are formalized separately).
     The term `integer operations', as opposed to `integral operations',
     is used in the title of [JLS:4.2.2].")
   (xdoc::p
    "Since integral values are subjected to
     unary and binary numeric promotion [JLS:5.6.1] [JLS:5.6.2] [JLS:15],
     the operations on integral values actually only operate on
     @('int') and @('long') values as operands.")
   (xdoc::p
    "For the shift operations [JLS:15.19],
     unary numeric promotion is applied to the operands separately.
     Thus, for each such operation, there are four variants,
     corresponding to each operand being @('int') or @('long').")
   (xdoc::p
    "Some integer operations have boolean results.")
   (xdoc::p
    "[JLS:4.2.2] also lists the prefix and posfix @('++') and @('--') operators,
     but those operate on variables, not just values,
     and therefore must be formalized elsewhere.")
   (xdoc::p
    "[JLS:4.2.2] also lists the conditional operator @('? :'),
     but that one is non-strict,
     and therefore must be formalized as part of expression evaluation.")
   (xdoc::p
    "[JLS:4.2.2] also lists the string concatenation operator @('+'),
     but that is best formalized in terms of integral-to-string conversions,
     elsewhere.")
   (xdoc::p
    "[JLS:4.2.2] also lists the cast operator, which involves conversions,
     which, as mentioned above, are formalized separately."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-int-unary int-plus
  :operation x
  :short "Unary plus @('+') on @('int')s [JLS:4.2.2] [JLS:15.15.3].")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-long-unary long-plus
  :operation x
  :short "Unary plus @('+') on @('long')s [JLS:4.2.2] [JLS:15.15.3].")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-int-unary int-minus
  :operation (logext 32 (- x))
  :short "Unary minus @('-') on @('int')s [JLS:4.2.2] [JLS:15.15.4].")

(assert-event (equal (int-minus (int-value (- (expt 2 31))))
                     (int-value (- (expt 2 31)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-long-unary long-minus
  :operation (logext 64 (- x))
  :short "Unary minus @('-') on @('long')s [JLS:4.2.2] [JLS:15.15.4].")

(assert-event (equal (long-minus (long-value (- (expt 2 63))))
                     (long-value (- (expt 2 63)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-int-binary int-add
  :operation (logext 32 (+ x y))
  :short "Addition @('+') on @('int')s [JLS:4.2.2] [JLS:15.18.2].")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-long-binary long-add
  :operation (logext 64 (+ x y))
  :short "Addition @('+') on @('long')s [JLS:4.2.2] [JLS:15.18.2].")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-int-binary int-sub
  :operation (logext 32 (- x y))
  :short "Subtraction @('-') on @('int')s [JLS:4.2.2] [JLS:15.18.2].")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-long-binary long-sub
  :operation (logext 64 (- x y))
  :short "Subtraction @('-') on @('long')s [JLS:4.2.2] [JLS:15.18.2].")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-int-binary int-mul
  :operation (logext 32 (* x y))
  :short "Multiplication @('*') on @('int')s [JLS:4.2.2] [JLS:15.17.1].")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-long-binary long-mul
  :operation (logext 64 (* x y))
  :short "Multiplication @('*') on @('long')s [JLS:4.2.2] [JLS:15.17.1].")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-int-binary int-div
  :nonzero t
  :operation (logext 32 (truncate x y))
  :short "Division @('/') on @('int')s [JLS:4.2.2] [JLS:15.17.2].")

(assert-event (equal (int-div (int-value (- (expt 2 31)))
                              (int-value -1))
                     (int-value (- (expt 2 31)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-long-binary long-div
  :nonzero t
  :operation (logext 64 (truncate x y))
  :short "Division @('/') on @('long')s [JLS:4.2.2] [JLS:15.17.2].")

(assert-event (equal (long-div (long-value (- (expt 2 63)))
                               (long-value -1))
                     (long-value (- (expt 2 63)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-int-binary int-rem
  :nonzero t
  :operation (logext 32 (rem x y))
  :short "Remainder @('&') on @('int')s [JLS:4.2.2] [JLS:15.17.3].")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-long-binary long-rem
  :nonzero t
  :operation (logext 64 (rem x y))
  :short "Remainder @('&') on @('long')s [JLS:4.2.2] [JLS:15.17.3].")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-int-unary int-not
  :operation (logext 32 (lognot x))
  :short "Bitwise complement @('~') on @('int')s [JLS:4.2.2] [JLS:15.15.5].")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-long-unary long-not
  :operation (logext 64 (lognot x))
  :short "Bitwise complement @('~') on @('long')s [JLS:4.2.2] [JLS:15.15.5].")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-int-binary int-and
  :operation (logext 32 (logand x y))
  :short "Bitwise conjunction @('&') on @('int')s [JLS:4.2.2] [JLS:15.22.1].")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-long-binary long-and
  :operation (logext 64 (logand x y))
  :short "Bitwise conjunction @('&') on @('long')s [JLS:4.2.2] [JLS:15.22.1].")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-int-binary int-xor
  :operation (logext 32 (logxor x y))
  :short "Bitwise exclusive disjunction @('^') on @('int')s
          [JLS:4.2.2] [JLS:15.22.1].")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-long-binary long-xor
  :operation (logext 64 (logxor x y))
  :short "Bitwise exclusive disjunction @('^') on @('long')s
          [JLS:4.2.2] [JLS:15.22.1].")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-int-binary int-ior
  :operation (logext 32 (logior x y))
  :short "Bitwise inclusive disjunction @('|') on @('int')s
          [JLS:4.2.2] [JLS:15.22.1].")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-long-binary long-ior
  :operation (logext 64 (logior x y))
  :short "Bitwise inclusive disjunction @('|') on @('long')s
          [JLS:4.2.2] [JLS:15.22.1].")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-int=>boolean-binary int-eq
  :operation (equal x y)
  :short "Equality @('==') on @('int')s [JLS:4.2.2] [JLS:15.21.1].")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-long=>boolean-binary long-eq
  :operation (equal x y)
  :short "Equality @('==') on @('long')s [JLS:4.2.2] [JLS:15.21.1].")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-int=>boolean-binary int-neq
  :operation (not (equal x y))
  :short "Non-equality @('!=') on @('int')s [JLS:4.2.2] [JLS:15.21.1].")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-long=>boolean-binary long-neq
  :operation (not (equal x y))
  :short "Non-equality @('!=') on @('long')s [JLS:4.2.2] [JLS:15.21.1].")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-int=>boolean-binary int-less
  :operation (< x y)
  :short "Less-than comparison @('<') on @('int')s
          [JLS:4.2.2] [JLS:15.20.1].")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-long=>boolean-binary long-less
  :operation (< x y)
  :short "Less-than comparison @('<') on @('long')s
          [JLS:4.2.2] [JLS:15.20.1].")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-int=>boolean-binary int-lesseq
  :operation (<= x y)
  :short "Less-than-or-equal-to comparison @('<=') on @('int')s
          [JLS:4.2.2] [JLS:15.20.1].")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-long=>boolean-binary long-lesseq
  :operation (<= x y)
  :short "Less-than-or-equal-to comparison @('<=') on @('long')s
          [JLS:4.2.2] [JLS:15.20.1].")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-int=>boolean-binary int-great
  :operation (> x y)
  :short "Greater-than comparison @('>') on @('int')s
          [JLS:4.2.2] [JLS:15.20.1].")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-long=>boolean-binary long-great
  :operation (> x y)
  :short "Greater-than comparison @('>') on @('long')s
          [JLS:4.2.2] [JLS:15.20.1].")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-int=>boolean-binary int-greateq
  :operation (>= x y)
  :short "Greater-than-or-equal-to comparison @('>=') on @('int')s
          [JLS:4.2.2] [JLS:15.20.1].")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-long=>boolean-binary long-greateq
  :operation (>= x y)
  :short "Greater-than-or-equal-to comparison @('>=') on @('long')s
          [JLS:4.2.2] [JLS:15.20.1].")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-int-binary int-int-shiftl
  :operation (logext 32 (ash x (loghead 5 y)))
  :short "Left shift of an @('int') by an @('int') [JLS:4.2.2] [JLS:15.19]."
  :long
  (xdoc::topstring-p
   "Only the low 5 bits of the distance are used [JLS:15.19]."))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-long-binary long-long-shiftl
  :operation (logext 64 (ash x (loghead 6 y)))
  :short "Left shift of a @('long') by a @('long') [JLS:4.2.2] [JLS:15.19]."
  :long
  (xdoc::topstring-p
   "Only the low 6 bits of the distance are used [JLS:15.19]."))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-primitive-binary long-int-shiftl
  :in-type-left (primitive-type-long)
  :in-type-right (primitive-type-int)
  :out-type (primitive-type-long)
  :operation (logext 64 (ash x (loghead 6 y)))
  :short "Left shift of a @('long') by an @('int') [JLS:4.2.2] [JLS:15.19]."
  :long
  (xdoc::topstring-p
   "Only the low 6 bits of the distance are used [JLS:15.19]."))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-primitive-binary int-long-shiftl
  :in-type-left (primitive-type-int)
  :in-type-right (primitive-type-long)
  :out-type (primitive-type-int)
  :operation (logext 32 (ash x (loghead 5 y)))
  :short "Left shift of an @('int') by a @('long') [JLS:4.2.2] [JLS:15.19]."
  :long
  (xdoc::topstring-p
   "Only the low 5 bits of the distance are used [JLS:15.19]."))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-int-binary int-int-shiftr
  :operation (logext 32 (ash x (- (loghead 5 y))))
  :short "(Signed) right shift of an @('int') by an @('int')
          [JLS:4.2.2] [JLS:15.19]."
  :long
  (xdoc::topstring-p
   "Only the low 5 bits of the distance are used [JLS:15.19]."))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-long-binary long-long-shiftr
  :operation (logext 64 (ash x (- (loghead 6 y))))
  :short "(Signed) right shift of a @('long') by a @('long')
          [JLS:4.2.2] [JLS:15.19]."
  :long
  (xdoc::topstring-p
   "Only the low 6 bits of the distance are used [JLS:15.19]."))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-primitive-binary long-int-shiftr
  :in-type-left (primitive-type-long)
  :in-type-right (primitive-type-int)
  :out-type (primitive-type-long)
  :operation (logext 64 (ash x (- (loghead 6 y))))
  :short "(Signed) right shift of a @('long') by an @('int')
          [JLS:4.2.2] [JLS:15.19]."
  :long
  (xdoc::topstring-p
   "Only the low 6 bits of the distance are used [JLS:15.19]."))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-primitive-binary int-long-shiftr
  :in-type-left (primitive-type-int)
  :in-type-right (primitive-type-long)
  :out-type (primitive-type-int)
  :operation (logext 32 (ash x (- (loghead 5 y))))
  :short "(Signed) right shift of an @('int') by a @('long')
          [JLS:4.2.2] [JLS:15.19]."
  :long
  (xdoc::topstring-p
   "Only the low 5 bits of the distance are used [JLS:15.19]."))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-int-binary int-int-ushiftr
  :operation (logext 32 (ash (loghead 32 x)
                             (- (loghead 5 y))))
  :short "Unsigned right shift of an @('int') by an @('int')
          [JLS:4.2.2] [JLS:15.19]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We first convert the left operand to unsigned.")
   (xdoc::p
    "Only the low 5 bits of the distance are used [JLS:15.19].")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-long-binary long-long-ushiftr
  :operation (logext 64 (ash (loghead 64 x)
                             (- (loghead 6 y))))
  :short "Unsigned right shift of an @('long') by an @('long')
          [JLS:4.2.2] [JLS:15.19]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We first convert the left operand to unsigned.")
   (xdoc::p
    "Only the low 6 bits of the distance are used [JLS:15.19].")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-primitive-binary long-int-ushiftr
  :in-type-left (primitive-type-long)
  :in-type-right (primitive-type-int)
  :out-type (primitive-type-long)
  :operation (logext 64 (ash (loghead 64 x)
                             (- (loghead 6 y))))
  :short "Unsigned right shift of a @('long') by an @('int')
          [JLS:4.2.2] [JLS:15.19]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We first convert the left operand to unsigned.")
   (xdoc::p
    "Only the low 6 bits of the distance are used [JLS:15.19].")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-primitive-binary int-long-ushiftr
  :in-type-left (primitive-type-int)
  :in-type-right (primitive-type-long)
  :out-type (primitive-type-int)
  :operation (logext 32 (ash (loghead 32 x)
                             (- (loghead 5 y))))
  :short "Unsigned right shift of an @('int') by a @('long')
          [JLS:4.2.2] [JLS:15.19]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We first convert the left operand to unsigned.")
   (xdoc::p
    "Only the low 5 bits of the distance are used [JLS:15.19].")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ floating-point-operations
  :parents (primitive-operations)
  :short "Java floating-point operations [JLS:4.2.4]."
  :long
  (xdoc::topstring
   (xdoc::p
    "Here we provide abstract notions for
     all the unary and binary operations on floating-point values
     that are not conversions (those are formalized separately).")
   (xdoc::p
    "[JLS:4.2.4] also lists the prefix and posfix @('++') and @('--') operators,
     but those operate on variables, not just values,
     and therefore must be formalized elsewhere.")
   (xdoc::p
    "[JLS:4.2.4] also lists the conditional operator @('? :'),
     but that one is non-strict,
     and therefore must be formalized as part of expression evaluation.")
   (xdoc::p
    "[JLS:4.2.4] also lists the string concatenation operator @('+'),
     but that is best formalized in terms of integral-to-string conversions,
     elsewhere.")
   (xdoc::p
    "[JLS:4.2.4] also lists the cast operator, which involves conversions,
     which, as mentioned above, are formalized separately."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-float-unary float-plus
  :operation (float-plus-abs x)
  :short "Unary plus @('+') on @('float')s [JLS:4.2.4] [JLS:15.15.3].")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-double-unary double-plus
  :operation (double-plus-abs x)
  :short "Unary plus @('+') on @('double')s [JLS:4.2.4] [JLS:15.15.3].")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-float-unary float-minus
  :operation (float-minus-abs x)
  :short "Unary minus @('-') on @('float')s [JLS:4.2.4] [JLS:15.15.4].")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-double-unary double-minus
  :operation (double-minus-abs x)
  :short "Unary minus @('-') on @('double')s [JLS:4.2.4] [JLS:15.15.4].")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-float-binary float-add
  :operation (float-add-abs x y)
  :short "Addition @('+') on @('float')s [JLS:4.2.4] [JLS:15.18.2].")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-double-binary double-add
  :operation (double-add-abs x y)
  :short "Addition @('+') on @('double')s [JLS:4.2.4] [JLS:15.18.2].")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-float-binary float-sub
  :operation (float-sub-abs x y)
  :short "Subtraction @('-') on @('float')s [JLS:4.2.4] [JLS:15.18.2].")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-double-binary double-sub
  :operation (double-sub-abs x y)
  :short "Subtraction @('-') on @('double')s [JLS:4.2.4] [JLS:15.18.2].")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-float-binary float-mul
  :operation (float-mul-abs x y)
  :short "Multiplication @('*') on @('float')s [JLS:4.2.4] [JLS:15.17.1].")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-double-binary double-mul
  :operation (double-mul-abs x y)
  :short "Multiplication @('*') on @('double')s [JLS:4.2.4] [JLS:15.17.1].")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-float-binary float-div
  :operation (float-div-abs x y)
  :short "Division @('/') on @('float')s [JLS:4.2.4] [JLS:15.17.2].")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-double-binary double-div
  :operation (double-div-abs x y)
  :short "Division @('/') on @('double')s [JLS:4.2.4] [JLS:15.17.2].")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-float-binary float-rem
  :operation (float-rem-abs x y)
  :short "Remainder @('%') on @('float')s [JLS:4.2.4] [JLS:15.17.3].")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-double-binary double-rem
  :operation (double-rem-abs x y)
  :short "Remainder @('%') on @('double')s [JLS:4.2.4] [JLS:15.17.3].")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-float=>boolean-binary float-eq
  :operation (float-eq-abs x y)
  :short "Equality @('==') on @('float')s [JLS:4.2.4] [JLS:15.21.1].")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-double=>boolean-binary double-eq
  :operation (double-eq-abs x y)
  :short "Equality @('==') on @('double')s [JLS:4.2.4] [JLS:15.21.1].")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-float=>boolean-binary float-neq
  :operation (float-neq-abs x y)
  :short "Non-equality @('!=') on @('float')s [JLS:4.2.4] [JLS:15.21.1].")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-double=>boolean-binary double-neq
  :operation (double-neq-abs x y)
  :short "Non-equality @('!=') on @('double')s [JLS:4.2.4] [JLS:15.21.1].")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-float=>boolean-binary float-less
  :operation (float-less-abs x y)
  :short "Less-than comparison @('<') on @('float')s
          [JLS:4.2.4] [JLS:15.20.1].")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-double=>boolean-binary double-less
  :operation (double-less-abs x y)
  :short "Less-than comparison @('<') on @('double')s
          [JLS:4.2.4] [JLS:15.20.1].")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-float=>boolean-binary float-lesseq
  :operation (float-lesseq-abs x y)
  :short "Less-than-or-equal-to comparison @('<=') on @('float')s
          [JLS:4.2.4] [JLS:15.20.1].")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-double=>boolean-binary double-lesseq
  :operation (double-lesseq-abs x y)
  :short "Less-than-or-equal-to comparison @('<=') on @('double')s
          [JLS:4.2.4] [JLS:15.20.1].")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-float=>boolean-binary float-great
  :operation (float-great-abs x y)
  :short "Greater-than comparison @('>') on @('float')s
          [JLS:4.2.4] [JLS:15.20.1].")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-double=>boolean-binary double-great
  :operation (double-great-abs x y)
  :short "Greater-than-or-equal-to comparison @('>') on @('double')s
          [JLS:4.2.4] [JLS:15.20.1].")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-float=>boolean-binary float-greateq
  :operation (float-greateq-abs x y)
  :short "Greater-than-or-equal-to comparison @('>=') on @('float')s
          [JLS:4.2.4] [JLS:15.20.1].")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-double=>boolean-binary double-greateq
  :operation (double-greateq-abs x y)
  :short "Greater-than-or-equal-to comparison @('>=') on @('double')s
          [JLS:4.2.4] [JLS:15.20.1].")
