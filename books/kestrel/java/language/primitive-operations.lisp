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

(include-book "kestrel/fty/sbyte32-ihs-theorems" :dir :system)
(include-book "kestrel/fty/sbyte64-ihs-theorems" :dir :system)

(local (include-book "ihs/logops-lemmas" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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
  :short "Logical complement @('!') [JLS:4.2.5] [JLS:15.15.6]."
  :operation (not x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-boolean-binary boolean-and
  :short "Logical conjunction @('&') [JLS:4.2.5] [JLS:15.22.2]."
  :operation (and x y)
  :commutative t
  :commutative-hints (("Goal" :in-theory (enable boolean-value-fix
                                                 boolean-value->bool))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-boolean-binary boolean-xor
  :short "Logical exclusive disjunction @('^') [JLS:4.2.5] [JLS:15.22.2]."
  :operation (not (equal x y))
  :commutative t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-boolean-binary boolean-ior
  :short "Logical inclusive disjunction @('|') [JLS:4.2.5] [JLS:15.22.2]."
  :operation (or x y)
  :commutative t
  :commutative-hints (("Goal" :in-theory (enable boolean-value-fix
                                                 boolean-value->bool))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-boolean-binary boolean-eq
  :short "Equality @('==') on @('boolean')s [JLS:4.2.5] [JLS:15.21.2]."
  :operation (equal x y)
  :commutative t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-boolean-binary boolean-neq
  :short "Non-equality @('!=') on @('boolean')s [JLS:4.2.5] [JLS:15.21.2]."
  :operation (not (equal x y))
  :commutative t)

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
     unary and binary numeric promotion [JLS:5.6] [JLS:15],
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
  :short "Unary plus @('+') on @('int')s [JLS:4.2.2] [JLS:15.15.3]."
  :operation x)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-long-unary long-plus
  :short "Unary plus @('+') on @('long')s [JLS:4.2.2] [JLS:15.15.3]."
  :operation x)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-int-unary int-minus
  :short "Unary minus @('-') on @('int')s [JLS:4.2.2] [JLS:15.15.4]."
  :operation (logext 32 (- x)))

(assert-event (equal (int-minus (int-value (- (expt 2 31))))
                     (int-value (- (expt 2 31)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-long-unary long-minus
  :short "Unary minus @('-') on @('long')s [JLS:4.2.2] [JLS:15.15.4]."
  :operation (logext 64 (- x)))

(assert-event (equal (long-minus (long-value (- (expt 2 63))))
                     (long-value (- (expt 2 63)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-int-binary int-add
  :short "Addition @('+') on @('int')s [JLS:4.2.2] [JLS:15.18.2]."
  :operation (logext 32 (+ x y))
  :commutative t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-long-binary long-add
  :short "Addition @('+') on @('long')s [JLS:4.2.2] [JLS:15.18.2]."
  :operation (logext 64 (+ x y))
  :commutative t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-int-binary int-sub
  :short "Subtraction @('-') on @('int')s [JLS:4.2.2] [JLS:15.18.2]."
  :operation (logext 32 (- x y)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-long-binary long-sub
  :short "Subtraction @('-') on @('long')s [JLS:4.2.2] [JLS:15.18.2]."
  :operation (logext 64 (- x y)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-int-binary int-mul
  :short "Multiplication @('*') on @('int')s [JLS:4.2.2] [JLS:15.17.1]."
  :operation (logext 32 (* x y))
  :commutative t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-long-binary long-mul
  :short "Multiplication @('*') on @('long')s [JLS:4.2.2] [JLS:15.17.1]."
  :operation (logext 64 (* x y))
  :commutative t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-int-binary int-div
  :short "Division @('/') on @('int')s [JLS:4.2.2] [JLS:15.17.2]."
  :nonzero t
  :operation (logext 32 (truncate x y)))

(assert-event (equal (int-div (int-value (- (expt 2 31)))
                              (int-value -1))
                     (int-value (- (expt 2 31)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-long-binary long-div
  :short "Division @('/') on @('long')s [JLS:4.2.2] [JLS:15.17.2]."
  :nonzero t
  :operation (logext 64 (truncate x y)))

(assert-event (equal (long-div (long-value (- (expt 2 63)))
                               (long-value -1))
                     (long-value (- (expt 2 63)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-int-binary int-rem
  :short "Remainder @('&') on @('int')s [JLS:4.2.2] [JLS:15.17.3]."
  :nonzero t
  :operation (logext 32 (rem x y)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-long-binary long-rem
  :short "Remainder @('&') on @('long')s [JLS:4.2.2] [JLS:15.17.3]."
  :nonzero t
  :operation (logext 64 (rem x y)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-int-unary int-not
  :short "Bitwise complement @('~') on @('int')s [JLS:4.2.2] [JLS:15.15.5]."
  :operation (logext 32 (lognot x)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-long-unary long-not
  :short "Bitwise complement @('~') on @('long')s [JLS:4.2.2] [JLS:15.15.5]."
  :operation (logext 64 (lognot x)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-int-binary int-and
  :short "Bitwise conjunction @('&') on @('int')s [JLS:4.2.2] [JLS:15.22.1]."
  :operation (logext 32 (logand x y))
  :commutative t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-long-binary long-and
  :short "Bitwise conjunction @('&') on @('long')s [JLS:4.2.2] [JLS:15.22.1]."
  :operation (logext 64 (logand x y))
  :commutative t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-int-binary int-xor
  :short "Bitwise exclusive disjunction @('^') on @('int')s
          [JLS:4.2.2] [JLS:15.22.1]."
  :operation (logext 32 (logxor x y))
  :commutative t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-long-binary long-xor
  :short "Bitwise exclusive disjunction @('^') on @('long')s
          [JLS:4.2.2] [JLS:15.22.1]."
  :operation (logext 64 (logxor x y))
  :commutative t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-int-binary int-ior
  :short "Bitwise inclusive disjunction @('|') on @('int')s
          [JLS:4.2.2] [JLS:15.22.1]."
  :operation (logext 32 (logior x y))
  :commutative t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-long-binary long-ior
  :short "Bitwise inclusive disjunction @('|') on @('long')s
          [JLS:4.2.2] [JLS:15.22.1]."
  :operation (logext 64 (logior x y))
  :commutative t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-int=>boolean-binary int-eq
  :short "Equality @('==') on @('int')s [JLS:4.2.2] [JLS:15.21.1]."
  :operation (equal x y)
  :commutative t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-long=>boolean-binary long-eq
  :short "Equality @('==') on @('long')s [JLS:4.2.2] [JLS:15.21.1]."
  :operation (equal x y)
  :commutative t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-int=>boolean-binary int-neq
  :short "Non-equality @('!=') on @('int')s [JLS:4.2.2] [JLS:15.21.1]."
  :operation (not (equal x y))
  :commutative t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-long=>boolean-binary long-neq
  :short "Non-equality @('!=') on @('long')s [JLS:4.2.2] [JLS:15.21.1]."
  :operation (not (equal x y))
  :commutative t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-int=>boolean-binary int-less
  :short "Less-than comparison @('<') on @('int')s
          [JLS:4.2.2] [JLS:15.20.1]."
  :operation (< x y))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-long=>boolean-binary long-less
  :short "Less-than comparison @('<') on @('long')s
          [JLS:4.2.2] [JLS:15.20.1]."
  :operation (< x y))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-int=>boolean-binary int-lesseq
  :short "Less-than-or-equal-to comparison @('<=') on @('int')s
          [JLS:4.2.2] [JLS:15.20.1]."
  :operation (<= x y))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-long=>boolean-binary long-lesseq
  :short "Less-than-or-equal-to comparison @('<=') on @('long')s
          [JLS:4.2.2] [JLS:15.20.1]."
  :operation (<= x y))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-int=>boolean-binary int-great
  :short "Greater-than comparison @('>') on @('int')s
          [JLS:4.2.2] [JLS:15.20.1]."
  :operation (> x y))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-long=>boolean-binary long-great
  :short "Greater-than comparison @('>') on @('long')s
          [JLS:4.2.2] [JLS:15.20.1]."
  :operation (> x y))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-int=>boolean-binary int-greateq
  :short "Greater-than-or-equal-to comparison @('>=') on @('int')s
          [JLS:4.2.2] [JLS:15.20.1]."
  :operation (>= x y))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-long=>boolean-binary long-greateq
  :short "Greater-than-or-equal-to comparison @('>=') on @('long')s
          [JLS:4.2.2] [JLS:15.20.1]."
  :operation (>= x y))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-int-binary int-int-shiftl
  :short "Left shift of an @('int') by an @('int') [JLS:4.2.2] [JLS:15.19]."
  :long
  (xdoc::topstring-p
   "Only the low 5 bits of the distance are used [JLS:15.19].")
  :operation (logext 32 (ash x (loghead 5 y))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-long-binary long-long-shiftl
  :short "Left shift of a @('long') by a @('long') [JLS:4.2.2] [JLS:15.19]."
  :long
  (xdoc::topstring-p
   "Only the low 6 bits of the distance are used [JLS:15.19].")
  :operation (logext 64 (ash x (loghead 6 y))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-primitive-binary long-int-shiftl
  :short "Left shift of a @('long') by an @('int') [JLS:4.2.2] [JLS:15.19]."
  :long
  (xdoc::topstring-p
   "Only the low 6 bits of the distance are used [JLS:15.19].")
  :in-type-left (primitive-type-long)
  :in-type-right (primitive-type-int)
  :out-type (primitive-type-long)
  :operation (logext 64 (ash x (loghead 6 y))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-primitive-binary int-long-shiftl
  :short "Left shift of an @('int') by a @('long') [JLS:4.2.2] [JLS:15.19]."
  :long
  (xdoc::topstring-p
   "Only the low 5 bits of the distance are used [JLS:15.19].")
  :in-type-left (primitive-type-int)
  :in-type-right (primitive-type-long)
  :out-type (primitive-type-int)
  :operation (logext 32 (ash x (loghead 5 y))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-int-binary int-int-shiftr
  :short "(Signed) right shift of an @('int') by an @('int')
          [JLS:4.2.2] [JLS:15.19]."
  :long
  (xdoc::topstring-p
   "Only the low 5 bits of the distance are used [JLS:15.19].")
  :operation (logext 32 (ash x (- (loghead 5 y)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-long-binary long-long-shiftr
  :short "(Signed) right shift of a @('long') by a @('long')
          [JLS:4.2.2] [JLS:15.19]."
  :long
  (xdoc::topstring-p
   "Only the low 6 bits of the distance are used [JLS:15.19].")
  :operation (logext 64 (ash x (- (loghead 6 y)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-primitive-binary long-int-shiftr
  :short "(Signed) right shift of a @('long') by an @('int')
          [JLS:4.2.2] [JLS:15.19]."
  :long
  (xdoc::topstring-p
   "Only the low 6 bits of the distance are used [JLS:15.19].")
  :in-type-left (primitive-type-long)
  :in-type-right (primitive-type-int)
  :out-type (primitive-type-long)
  :operation (logext 64 (ash x (- (loghead 6 y)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-primitive-binary int-long-shiftr
  :short "(Signed) right shift of an @('int') by a @('long')
          [JLS:4.2.2] [JLS:15.19]."
  :long
  (xdoc::topstring-p
   "Only the low 5 bits of the distance are used [JLS:15.19].")
  :in-type-left (primitive-type-int)
  :in-type-right (primitive-type-long)
  :out-type (primitive-type-int)
  :operation (logext 32 (ash x (- (loghead 5 y)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-int-binary int-int-ushiftr
  :short "Unsigned right shift of an @('int') by an @('int')
          [JLS:4.2.2] [JLS:15.19]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We first convert the left operand to unsigned.")
   (xdoc::p
    "Only the low 5 bits of the distance are used [JLS:15.19]."))
  :operation (logext 32 (ash (loghead 32 x)
                             (- (loghead 5 y)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-long-binary long-long-ushiftr
  :short "Unsigned right shift of an @('long') by an @('long')
          [JLS:4.2.2] [JLS:15.19]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We first convert the left operand to unsigned.")
   (xdoc::p
    "Only the low 6 bits of the distance are used [JLS:15.19]."))
  :operation (logext 64 (ash (loghead 64 x)
                             (- (loghead 6 y)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-primitive-binary long-int-ushiftr
  :short "Unsigned right shift of a @('long') by an @('int')
          [JLS:4.2.2] [JLS:15.19]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We first convert the left operand to unsigned.")
   (xdoc::p
    "Only the low 6 bits of the distance are used [JLS:15.19]."))
  :in-type-left (primitive-type-long)
  :in-type-right (primitive-type-int)
  :out-type (primitive-type-long)
  :operation (logext 64 (ash (loghead 64 x)
                             (- (loghead 6 y)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-primitive-binary int-long-ushiftr
  :short "Unsigned right shift of an @('int') by a @('long')
          [JLS:4.2.2] [JLS:15.19]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We first convert the left operand to unsigned.")
   (xdoc::p
    "Only the low 5 bits of the distance are used [JLS:15.19]."))
  :in-type-left (primitive-type-int)
  :in-type-right (primitive-type-long)
  :out-type (primitive-type-int)
  :operation (logext 32 (ash (loghead 32 x)
                             (- (loghead 5 y)))))

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
  :short "Unary plus @('+') on @('float')s [JLS:4.2.4] [JLS:15.15.3]."
  :operation (float-plus-abs x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-double-unary double-plus
  :short "Unary plus @('+') on @('double')s [JLS:4.2.4] [JLS:15.15.3]."
  :operation (double-plus-abs x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-float-unary float-minus
  :short "Unary minus @('-') on @('float')s [JLS:4.2.4] [JLS:15.15.4]."
  :operation (float-minus-abs x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-double-unary double-minus
  :short "Unary minus @('-') on @('double')s [JLS:4.2.4] [JLS:15.15.4]."
  :operation (double-minus-abs x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-float-binary float-add
  :short "Addition @('+') on @('float')s [JLS:4.2.4] [JLS:15.18.2]."
  :operation (float-add-abs x y))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-double-binary double-add
  :short "Addition @('+') on @('double')s [JLS:4.2.4] [JLS:15.18.2]."
  :operation (double-add-abs x y))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-float-binary float-sub
  :short "Subtraction @('-') on @('float')s [JLS:4.2.4] [JLS:15.18.2]."
  :operation (float-sub-abs x y))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-double-binary double-sub
  :short "Subtraction @('-') on @('double')s [JLS:4.2.4] [JLS:15.18.2]."
  :operation (double-sub-abs x y))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-float-binary float-mul
  :short "Multiplication @('*') on @('float')s [JLS:4.2.4] [JLS:15.17.1]."
  :operation (float-mul-abs x y))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-double-binary double-mul
  :short "Multiplication @('*') on @('double')s [JLS:4.2.4] [JLS:15.17.1]."
  :operation (double-mul-abs x y))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-float-binary float-div
  :short "Division @('/') on @('float')s [JLS:4.2.4] [JLS:15.17.2]."
  :operation (float-div-abs x y))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-double-binary double-div
  :short "Division @('/') on @('double')s [JLS:4.2.4] [JLS:15.17.2]."
  :operation (double-div-abs x y))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-float-binary float-rem
  :short "Remainder @('%') on @('float')s [JLS:4.2.4] [JLS:15.17.3]."
  :operation (float-rem-abs x y))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-double-binary double-rem
  :short "Remainder @('%') on @('double')s [JLS:4.2.4] [JLS:15.17.3]."
  :operation (double-rem-abs x y))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-float=>boolean-binary float-eq
  :short "Equality @('==') on @('float')s [JLS:4.2.4] [JLS:15.21.1]."
  :operation (float-eq-abs x y))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-double=>boolean-binary double-eq
  :short "Equality @('==') on @('double')s [JLS:4.2.4] [JLS:15.21.1]."
  :operation (double-eq-abs x y))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-float=>boolean-binary float-neq
  :short "Non-equality @('!=') on @('float')s [JLS:4.2.4] [JLS:15.21.1]."
  :operation (float-neq-abs x y))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-double=>boolean-binary double-neq
  :short "Non-equality @('!=') on @('double')s [JLS:4.2.4] [JLS:15.21.1]."
  :operation (double-neq-abs x y))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-float=>boolean-binary float-less
  :short "Less-than comparison @('<') on @('float')s
          [JLS:4.2.4] [JLS:15.20.1]."
  :operation (float-less-abs x y))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-double=>boolean-binary double-less
  :short "Less-than comparison @('<') on @('double')s
          [JLS:4.2.4] [JLS:15.20.1]."
  :operation (double-less-abs x y))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-float=>boolean-binary float-lesseq
  :short "Less-than-or-equal-to comparison @('<=') on @('float')s
          [JLS:4.2.4] [JLS:15.20.1]."
  :operation (float-lesseq-abs x y))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-double=>boolean-binary double-lesseq
  :short "Less-than-or-equal-to comparison @('<=') on @('double')s
          [JLS:4.2.4] [JLS:15.20.1]."
  :operation (double-lesseq-abs x y))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-float=>boolean-binary float-great
  :short "Greater-than comparison @('>') on @('float')s
          [JLS:4.2.4] [JLS:15.20.1]."
  :operation (float-great-abs x y))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-double=>boolean-binary double-great
  :short "Greater-than-or-equal-to comparison @('>') on @('double')s
          [JLS:4.2.4] [JLS:15.20.1]."
  :operation (double-great-abs x y))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-float=>boolean-binary float-greateq
  :short "Greater-than-or-equal-to comparison @('>=') on @('float')s
          [JLS:4.2.4] [JLS:15.20.1]."
  :operation (float-greateq-abs x y))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-double=>boolean-binary double-greateq
  :short "Greater-than-or-equal-to comparison @('>=') on @('double')s
          [JLS:4.2.4] [JLS:15.20.1]."
  :operation (double-greateq-abs x y))
