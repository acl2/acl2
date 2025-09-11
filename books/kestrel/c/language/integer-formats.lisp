; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2025 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "../pack")

(include-book "std/strings/case-conversion" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ integer-formats
  :parents (language)
  :short "C integer formats."
  :long
  (xdoc::topstring
   (xdoc::p
    "[C17] provides constraints on the formats of the integer types [C17:6.2.5],
     but not a complete definition of the formats (unlike Java).
     A general formalization of C should be parameterized over these formats;
     we plan to do that in this formalization of C.
     However, for now we define the formats, but we do so in a way that
     should make it easy to change and swap some aspects of the definitions.")
   (xdoc::p
    "[C17:6.2.6.2/2] allows padding bits, which we disallow for now.
     [C17:6.2.6.2/2] allows signed integers to be
     two's complement, ones' complement, or sign and magnitude;
     for now we assume two's complement.")
   (xdoc::p
    "The exact number of bits in a byte is also implementation-dependent
     [C17:5.2.4.2.1/1] [C17:6.2.6.1/3],
     so we introduce a nullary function for the number of bits in a byte,
     i.e. in a @('char') (unsigned, signed, or plain).
     We define it to be 8 for now, because that is the most frequent case.")
   (xdoc::p
    "We also introduce nullary functions for the number of bits that form
     (signed and unsigned)
     @('short')s, @('int')s, @('long'), and @('long long')s.
     Given the above current choice of no padding bits,
     these numbers of bits have to be multiples of the number of bits in a byte,
     because those integers have to take a whole number of bytes.
     Recall that each signed integer type
     takes the same storage as the corresponding unsigned integer type
     [C17:6.2.5/6].")
   (xdoc::p
    "We prove some theorems about the nullary functions.
     We disable the definitions of the nullary functions,
     including executable counterparts.
     This way, we reduce the dependencies from the exact definitions,
     and we define the integer values, conversions, and operations
     as independently from the exact sizes as possible.
     Thus, it may not be difficult to replace this file
     with another one with different definitions,
     or to replace the definitions with a parameterization.")
   (xdoc::p
    "The definitions that we pick here are consistent with @('gcc')
     on (at least some versions of) macOS and Linux, namely:
     @('char') is 8 bits,
     @('short') is 16 bits (2 bytes),
     @('int') is 32 bits (4 bytes),
     @('long') is 64 bits (8 bytes), and
     @('long long') is also 64 bits (8 bytes).
     These are all consistent with the ranges in [C17:5.2.4.2.1]:
     @('char') must be at least 8 bits,
     @('short') must be at least 16 bits,
     @('int') must be at least 16 bits,
     @('long') must be at least 32 bits, and
     @('long long') must be at least 64 bits.
     Furthermore, the ranges must be non-decreasing [C17:6.2.5/8].")
   (xdoc::p
    "For now we only define formats for
     the standard signed and unsigned integer types except @('_Bool').
     Note that the plain @('char') type is not covered yet;
     it is an integer type,
     but not a standard integer type in C's terminology."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ def-integer-bits (type bits minbits)
  (declare (xargs :guard (and (member-eq type '(char short int long llong))
                              (posp bits)
                              (posp minbits)
                              (>= bits minbits))))
  :short "Macro to generate the nullary functions, and some theorems about them,
          for the size in bits of the C integer types."

  (b* ((type-bits (pack type '-bits))
       (type-bits-bound (pack type-bits '-bound))
       (type-bits-multiple-of-char-bits (pack type
                                              '-bits-multiple-of-char-bits))
       (short-substring (if (eq type 'char)
                            "signed, unsigned, and plain"
                          "signed and unsigned")))

    `(define ,type-bits ()
       :returns (,type-bits posp :rule-classes :type-prescription)
       :short ,(str::cat "Size of "
                         short-substring
                         " @('"
                         (str::downcase-string (symbol-name type))
                         "') values, in bits.")
       ,bits
       ///

       ,@(and
          (not (eq type 'char))
          `((defrule ,type-bits-multiple-of-char-bits
              (integerp (/ (,type-bits) (char-bits)))
              :rule-classes :type-prescription
              :enable char-bits)))

       (in-theory (disable (:e ,type-bits)))

       (defret ,type-bits-bound
         (>= ,type-bits ,minbits)
         :rule-classes :linear))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Other than the definitions of the nullary functions,
; the theorems generated by the following code
; hold for all choices of values consistent with [C17].

(def-integer-bits char 8 8)

(def-integer-bits short 16 16)

(def-integer-bits int 32 16)

(def-integer-bits long 64 32)

(def-integer-bits llong 64 64)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ def-integer-bits-linear-rule (type1 rel type2 &key name disable)
  (declare (xargs :guard (and (member-eq type1 '(char short int long llong))
                              (member-eq type2 '(char short int long llong))
                              (member-eq rel '(= < > <= >=))
                              (symbolp name)
                              (booleanp disable))))
  :short "Macro to generate linear rules about
          the sizes in bits of C integer types."
  :long
  (xdoc::topstring
   (xdoc::p
    "Each theorem says that the size in bits of the first type
     has the specified relation with the size in bits of the second type.")
   (xdoc::p
    "Note that we also allow equalities, not just inequalities.
     Linear rules may use equalities in ACL2."))

  (b* ((type1-bits (pack type1 '-bits))
       (type2-bits (pack type2 '-bits))
       (name (or name (pack type1-bits '- rel '- type2-bits)))
       (type1-string (str::cat
                      "@('" (str::downcase-string (symbol-name type1)) "')"))
       (type2-string (str::cat
                      "@('" (str::downcase-string (symbol-name type2)) "')")))

    `(,(if disable 'defruled 'defrule) ,name
      :parents (,type1-bits ,type2-bits)
      :short ,(str::cat "Relation between "
                        type1-string
                        " and "
                        type2-string
                        " bit sizes.")
      (,rel (,type1-bits) (,type2-bits))
      :rule-classes ((:linear :trigger-terms ((,type1-bits) (,type2-bits))))
      :enable (,type1-bits ,type2-bits))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The theorems generated by the following code calls
; hold for all choices of values consistent with [C17].
; The generated rules are enabled.

(def-integer-bits-linear-rule char <= short)

(def-integer-bits-linear-rule short <= int)

(def-integer-bits-linear-rule int <= long)

(def-integer-bits-linear-rule long <= llong)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The theorems generated by the following code
; hold for some choices of values consistent with [C17].
; The code to generate the rules is the same for all choices,
; but the exact resulting rules depend on some choices.
; The rules are disabled, so it is clear when they are used,
; i.e. when there are dependencies on the choice of values.

(make-event
 (b* ((rel (if (= (char-bits) (short-bits)) '= '<)))
   `(def-integer-bits-linear-rule char ,rel short
      :name char-bits-vs-short-bits
      :disable t)))

(make-event
 (b* ((rel (if (= (short-bits) (int-bits)) '= '<)))
   `(def-integer-bits-linear-rule short ,rel int
      :name short-bits-vs-int-bits
      :disable t)))

(make-event
 (b* ((rel (if (= (int-bits) (long-bits)) '= '<)))
   `(def-integer-bits-linear-rule int ,rel long
      :name int-bits-vs-long-bits
      :disable t)))

(make-event
 (b* ((rel (if (= (long-bits) (llong-bits)) '= '<)))
   `(def-integer-bits-linear-rule long ,rel llong
      :name long-bits-vs-llong-bits
      :disable t)))
