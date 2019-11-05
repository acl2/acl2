; Java Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

(include-book "primitive-operations")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrulel sbyte8p-of-logext8
  (sbyte8p (logext 8 x))
  :enable sbyte8p
  :prep-books ((include-book "arithmetic-5/top" :dir :system)))

(defrulel sbyte16p-of-logext16
  (sbyte16p (logext 16 x))
  :enable sbyte16p
  :prep-books ((include-book "arithmetic-5/top" :dir :system)))

(defrulel sbyte32p-of-logext32
  (sbyte32p (logext 32 x))
  :enable sbyte32p
  :prep-books ((include-book "arithmetic-5/top" :dir :system)))

(defrulel ubyte16p-of-loghead16
  (ubyte16p (loghead 16 x))
  :enable (ubyte16p)
  :prep-books ((include-book "arithmetic-5/top" :dir :system)))

(local (in-theory (disable logext loghead)))

(defrulel sbyte16p-when-sbyte8p
  (implies (sbyte8p x)
           (sbyte16p x))
  :enable (sbyte8p sbyte16p))

(defrulel sbyte32p-when-sbyte8p
  (implies (sbyte8p x)
           (sbyte32p x))
  :enable (sbyte8p sbyte32p))

(defrulel sbyte64p-when-sbyte8p
  (implies (sbyte8p x)
           (sbyte64p x))
  :enable (sbyte8p sbyte64p))

(defrulel sbyte32p-when-sbyte16p
  (implies (sbyte16p x)
           (sbyte32p x))
  :enable (sbyte16p sbyte32p))

(defrulel sbyte64p-when-sbyte16p
  (implies (sbyte16p x)
           (sbyte64p x))
  :enable (sbyte16p sbyte64p))

(defrulel sbyte64p-when-sbyte32p
  (implies (sbyte32p x)
           (sbyte64p x))
  :enable (sbyte32p sbyte64p))

(defrulel sbyte32p-when-ubyte16p
  (implies (ubyte16p x)
           (sbyte32p x))
  :enable (ubyte16p sbyte32p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ primitive-conversions
  :parents (semantics)
  :short "Java primitive conversions [JLS:5.1.2-4]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We formalize the Java primitive conversions between integral types.
     Conversions between floating-point types,
     and between integral and floating-point types,
     will be formalized eventually."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ primitive-widening-conversions
  :parents (primitive-conversions)
  :short "Java primitive widening conversions [JLS:5.1.2]."
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-primitive-unary-op byte-to-short
  :in-type (primitive-type-byte)
  :out-type (primitive-type-short)
  :operation x
  :short "Widening conversion from @('byte') to @('short') [JLS:5.1.2].")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-primitive-unary-op byte-to-int
  :in-type (primitive-type-byte)
  :out-type (primitive-type-int)
  :operation x
  :short "Widening conversion from @('byte') to @('int') [JLS:5.1.2].")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-primitive-unary-op byte-to-long
  :in-type (primitive-type-byte)
  :out-type (primitive-type-long)
  :operation x
  :short "Widening conversion from @('byte') to @('long') [JLS:5.1.2].")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-primitive-unary-op short-to-int
  :in-type (primitive-type-short)
  :out-type (primitive-type-int)
  :operation x
  :short "Widening conversion from @('short') to @('int') [JLS:5.1.2].")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-primitive-unary-op short-to-long
  :in-type (primitive-type-short)
  :out-type (primitive-type-long)
  :operation x
  :short "Widening conversion from @('short') to @('long') [JLS:5.1.2].")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-primitive-unary-op int-to-long
  :in-type (primitive-type-int)
  :out-type (primitive-type-long)
  :operation x
  :short "Widening conversion from @('int') to @('long') [JLS:5.1.2].")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-primitive-unary-op char-to-int
  :in-type (primitive-type-char)
  :out-type (primitive-type-int)
  :operation x
  :short "Widening conversion from @('char') to @('int') [JLS:5.1.2].")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-primitive-unary-op char-to-long
  :in-type (primitive-type-char)
  :out-type (primitive-type-long)
  :operation x
  :short "Widening conversion from @('char') to @('long') [JLS:5.1.2].")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ primitive-narrowing-conversions
  :parents (primitive-conversions)
  :short "Java primitive narrowing conversions [JLS:5.1.3]."
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-primitive-unary-op short-to-byte
  :in-type (primitive-type-short)
  :out-type (primitive-type-byte)
  :operation (logext 8 x)
  :short "Narrowing conversion from @('short') to @('byte') [JLS:5.1.3].")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-primitive-unary-op int-to-byte
  :in-type (primitive-type-int)
  :out-type (primitive-type-byte)
  :operation (logext 8 x)
  :short "Narrowing conversion from @('int') to @('byte') [JLS:5.1.3].")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-primitive-unary-op long-to-byte
  :in-type (primitive-type-long)
  :out-type (primitive-type-byte)
  :operation (logext 8 x)
  :short "Narrowing conversion from @('long') to @('byte') [JLS:5.1.3].")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-primitive-unary-op char-to-byte
  :in-type (primitive-type-char)
  :out-type (primitive-type-byte)
  :operation (logext 8 x)
  :short "Narrowing conversion from @('char') to @('byte') [JLS:5.1.3].")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-primitive-unary-op int-to-short
  :in-type (primitive-type-int)
  :out-type (primitive-type-short)
  :operation (logext 16 x)
  :short "Narrowing conversion from @('int') to @('short') [JLS:5.1.3].")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-primitive-unary-op long-to-short
  :in-type (primitive-type-long)
  :out-type (primitive-type-short)
  :operation (logext 16 x)
  :short "Narrowing conversion from @('long') to @('short') [JLS:5.1.3].")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-primitive-unary-op char-to-short
  :in-type (primitive-type-char)
  :out-type (primitive-type-short)
  :operation (logext 16 x)
  :short "Narrowing conversion from @('char') to @('short') [JLS:5.1.3].")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-primitive-unary-op long-to-int
  :in-type (primitive-type-long)
  :out-type (primitive-type-int)
  :operation (logext 32 x)
  :short "Narrowing conversion from @('long') to @('int') [JLS:5.1.3].")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-primitive-unary-op short-to-char
  :in-type (primitive-type-short)
  :out-type (primitive-type-char)
  :operation (loghead 16 x)
  :short "Narrowing conversion from @('short') to @('char') [JLS:5.1.3].")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-primitive-unary-op int-to-char
  :in-type (primitive-type-int)
  :out-type (primitive-type-char)
  :operation (loghead 16 x)
  :short "Narrowing conversion from @('int') to @('char') [JLS:5.1.3].")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-primitive-unary-op long-to-char
  :in-type (primitive-type-long)
  :out-type (primitive-type-char)
  :operation (loghead 16 x)
  :short "Narrowing conversion from @('long') to @('char') [JLS:5.1.3].")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ primitive-widening-narrowing-conversions
  :parents (primitive-conversions)
  :short "Java primitive widening and narrowing conversions [JLS:5.1.4]."
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-primitive-unary-op byte-to-char
  :in-type (primitive-type-byte)
  :out-type (primitive-type-char)
  :operation (loghead 16 x)
  :short "Widening and narrowing conversion
          from @('byte') to @('char') [JLS:5.1.3].")
