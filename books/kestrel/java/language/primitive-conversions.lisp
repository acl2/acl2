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
     We also provide abstract notions of
     the Java primitive conversions that involve floating-point values,
     as a placeholder for a more precise formalization of them."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ primitive-widening-conversions
  :parents (primitive-conversions)
  :short "Java primitive widening conversions [JLS:5.1.2]."
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-primitive-unary byte-to-short
  :in-type (primitive-type-byte)
  :out-type (primitive-type-short)
  :operation x
  :short "Widening conversion from @('byte') to @('short') [JLS:5.1.2].")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-primitive-unary byte-to-int
  :in-type (primitive-type-byte)
  :out-type (primitive-type-int)
  :operation x
  :short "Widening conversion from @('byte') to @('int') [JLS:5.1.2].")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-primitive-unary byte-to-long
  :in-type (primitive-type-byte)
  :out-type (primitive-type-long)
  :operation x
  :short "Widening conversion from @('byte') to @('long') [JLS:5.1.2].")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-primitive-unary byte-to-float
  :in-type (primitive-type-byte)
  :out-type (primitive-type-float)
  :operation (byte-to-float-abs x)
  :short "Widening conversion from @('byte') to @('float') [JLS:5.1.2].")

(in-theory (disable (:e byte-to-float)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-primitive-unary byte-to-double
  :in-type (primitive-type-byte)
  :out-type (primitive-type-double)
  :operation (byte-to-double-abs x)
  :short "Widening conversion from @('byte') to @('double') [JLS:5.1.2].")

(in-theory (disable (:e byte-to-double)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-primitive-unary short-to-int
  :in-type (primitive-type-short)
  :out-type (primitive-type-int)
  :operation x
  :short "Widening conversion from @('short') to @('int') [JLS:5.1.2].")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-primitive-unary short-to-long
  :in-type (primitive-type-short)
  :out-type (primitive-type-long)
  :operation x
  :short "Widening conversion from @('short') to @('long') [JLS:5.1.2].")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-primitive-unary short-to-float
  :in-type (primitive-type-short)
  :out-type (primitive-type-float)
  :operation (short-to-float-abs x)
  :short "Widening conversion from @('short') to @('float') [JLS:5.1.2].")

(in-theory (disable (:e short-to-float)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-primitive-unary short-to-double
  :in-type (primitive-type-short)
  :out-type (primitive-type-double)
  :operation (short-to-double-abs x)
  :short "Widening conversion from @('short') to @('double') [JLS:5.1.2].")

(in-theory (disable (:e short-to-double)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-primitive-unary char-to-int
  :in-type (primitive-type-char)
  :out-type (primitive-type-int)
  :operation x
  :short "Widening conversion from @('char') to @('int') [JLS:5.1.2].")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-primitive-unary char-to-long
  :in-type (primitive-type-char)
  :out-type (primitive-type-long)
  :operation x
  :short "Widening conversion from @('char') to @('long') [JLS:5.1.2].")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-primitive-unary char-to-float
  :in-type (primitive-type-char)
  :out-type (primitive-type-float)
  :operation (char-to-float-abs x)
  :short "Widening conversion from @('char') to @('float') [JLS:5.1.2].")

(in-theory (disable (:e char-to-float)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-primitive-unary char-to-double
  :in-type (primitive-type-char)
  :out-type (primitive-type-double)
  :operation (char-to-double-abs x)
  :short "Widening conversion from @('char') to @('double') [JLS:5.1.2].")

(in-theory (disable (:e char-to-double)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-primitive-unary int-to-long
  :in-type (primitive-type-int)
  :out-type (primitive-type-long)
  :operation x
  :short "Widening conversion from @('int') to @('long') [JLS:5.1.2].")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-primitive-unary int-to-float
  :in-type (primitive-type-int)
  :out-type (primitive-type-float)
  :operation (int-to-float-abs x)
  :short "Widening conversion from @('int') to @('float') [JLS:5.1.2].")

(in-theory (disable (:e int-to-float)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-primitive-unary int-to-double
  :in-type (primitive-type-int)
  :out-type (primitive-type-double)
  :operation (int-to-double-abs x)
  :short "Widening conversion from @('int') to @('double') [JLS:5.1.2].")

(in-theory (disable (:e int-to-double)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-primitive-unary long-to-float
  :in-type (primitive-type-long)
  :out-type (primitive-type-float)
  :operation (long-to-float-abs x)
  :short "Widening conversion from @('long') to @('float') [JLS:5.1.2].")

(in-theory (disable (:e long-to-float)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-primitive-unary long-to-double
  :in-type (primitive-type-long)
  :out-type (primitive-type-double)
  :operation (long-to-double-abs x)
  :short "Widening conversion from @('long') to @('double') [JLS:5.1.2].")

(in-theory (disable (:e long-to-double)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-primitive-unary float-to-double
  :in-type (primitive-type-float)
  :out-type (primitive-type-double)
  :operation (float-to-double-abs x)
  :short "Widening conversion from @('float') to @('double') [JLS:5.1.2].")

(in-theory (disable (:e float-to-double)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ primitive-narrowing-conversions
  :parents (primitive-conversions)
  :short "Java primitive narrowing conversions [JLS:5.1.3]."
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-primitive-unary short-to-byte
  :in-type (primitive-type-short)
  :out-type (primitive-type-byte)
  :operation (logext 8 x)
  :short "Narrowing conversion from @('short') to @('byte') [JLS:5.1.3].")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-primitive-unary short-to-char
  :in-type (primitive-type-short)
  :out-type (primitive-type-char)
  :operation (loghead 16 x)
  :short "Narrowing conversion from @('short') to @('char') [JLS:5.1.3].")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-primitive-unary char-to-byte
  :in-type (primitive-type-char)
  :out-type (primitive-type-byte)
  :operation (logext 8 x)
  :short "Narrowing conversion from @('char') to @('byte') [JLS:5.1.3].")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-primitive-unary char-to-short
  :in-type (primitive-type-char)
  :out-type (primitive-type-short)
  :operation (logext 16 x)
  :short "Narrowing conversion from @('char') to @('short') [JLS:5.1.3].")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-primitive-unary int-to-byte
  :in-type (primitive-type-int)
  :out-type (primitive-type-byte)
  :operation (logext 8 x)
  :short "Narrowing conversion from @('int') to @('byte') [JLS:5.1.3].")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-primitive-unary int-to-short
  :in-type (primitive-type-int)
  :out-type (primitive-type-short)
  :operation (logext 16 x)
  :short "Narrowing conversion from @('int') to @('short') [JLS:5.1.3].")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-primitive-unary int-to-char
  :in-type (primitive-type-int)
  :out-type (primitive-type-char)
  :operation (loghead 16 x)
  :short "Narrowing conversion from @('int') to @('char') [JLS:5.1.3].")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-primitive-unary long-to-byte
  :in-type (primitive-type-long)
  :out-type (primitive-type-byte)
  :operation (logext 8 x)
  :short "Narrowing conversion from @('long') to @('byte') [JLS:5.1.3].")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-primitive-unary long-to-short
  :in-type (primitive-type-long)
  :out-type (primitive-type-short)
  :operation (logext 16 x)
  :short "Narrowing conversion from @('long') to @('short') [JLS:5.1.3].")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-primitive-unary long-to-char
  :in-type (primitive-type-long)
  :out-type (primitive-type-char)
  :operation (loghead 16 x)
  :short "Narrowing conversion from @('long') to @('char') [JLS:5.1.3].")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-primitive-unary long-to-int
  :in-type (primitive-type-long)
  :out-type (primitive-type-int)
  :operation (logext 32 x)
  :short "Narrowing conversion from @('long') to @('int') [JLS:5.1.3].")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-primitive-unary float-to-byte
  :in-type (primitive-type-float)
  :out-type (primitive-type-byte)
  :operation (float-to-byte-abs x)
  :short "Narrowing conversion from @('float') to @('byte') [JLS:5.1.3].")

(in-theory (disable (:e float-to-byte)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-primitive-unary float-to-short
  :in-type (primitive-type-float)
  :out-type (primitive-type-short)
  :operation (float-to-short-abs x)
  :short "Narrowing conversion from @('float') to @('short') [JLS:5.1.3].")

(in-theory (disable (:e float-to-short)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-primitive-unary float-to-char
  :in-type (primitive-type-float)
  :out-type (primitive-type-char)
  :operation (float-to-char-abs x)
  :short "Narrowing conversion from @('float') to @('char') [JLS:5.1.3].")

(in-theory (disable (:e float-to-char)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-primitive-unary float-to-int
  :in-type (primitive-type-float)
  :out-type (primitive-type-int)
  :operation (float-to-int-abs x)
  :short "Narrowing conversion from @('float') to @('int') [JLS:5.1.3].")

(in-theory (disable (:e float-to-int)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-primitive-unary float-to-long
  :in-type (primitive-type-float)
  :out-type (primitive-type-long)
  :operation (float-to-long-abs x)
  :short "Narrowing conversion from @('float') to @('long') [JLS:5.1.3].")

(in-theory (disable (:e float-to-long)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-primitive-unary double-to-byte
  :in-type (primitive-type-double)
  :out-type (primitive-type-byte)
  :operation (double-to-byte-abs x)
  :short "Narrowing conversion from @('double') to @('byte') [JLS:5.1.3].")

(in-theory (disable (:e double-to-byte)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-primitive-unary double-to-short
  :in-type (primitive-type-double)
  :out-type (primitive-type-short)
  :operation (double-to-short-abs x)
  :short "Narrowing conversion from @('double') to @('short') [JLS:5.1.3].")

(in-theory (disable (:e double-to-short)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-primitive-unary double-to-char
  :in-type (primitive-type-double)
  :out-type (primitive-type-char)
  :operation (double-to-char-abs x)
  :short "Narrowing conversion from @('double') to @('char') [JLS:5.1.3].")

(in-theory (disable (:e double-to-char)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-primitive-unary double-to-int
  :in-type (primitive-type-double)
  :out-type (primitive-type-int)
  :operation (double-to-int-abs x)
  :short "Narrowing conversion from @('double') to @('int') [JLS:5.1.3].")

(in-theory (disable (:e double-to-int)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-primitive-unary double-to-long
  :in-type (primitive-type-double)
  :out-type (primitive-type-long)
  :operation (double-to-long-abs x)
  :short "Narrowing conversion from @('double') to @('long') [JLS:5.1.3].")

(in-theory (disable (:e double-to-long)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-primitive-unary double-to-float
  :in-type (primitive-type-double)
  :out-type (primitive-type-float)
  :operation (double-to-float-abs x)
  :short "Narrowing conversion from @('double') to @('float') [JLS:5.1.3].")

(in-theory (disable (:e double-to-float)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ primitive-widening-narrowing-conversions
  :parents (primitive-conversions)
  :short "Java primitive widening and narrowing conversions [JLS:5.1.4]."
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-primitive-unary byte-to-char
  :in-type (primitive-type-byte)
  :out-type (primitive-type-char)
  :operation (loghead 16 x)
  :short "Widening and narrowing conversion
          from @('byte') to @('char') [JLS:5.1.3].")
