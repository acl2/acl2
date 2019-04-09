; Std/basic - Recognizer of Unsigned 4-bit Bytes
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio <coglio@kestrel.edu>

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "xdoc/constructors" :dir :system)
(include-book "std/util/define" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define nibblep (x)
  :returns (yes/no booleanp)
  :parents (std/basic unsigned-byte-p signed-byte-p)
  :short "Recognize unsigned 4-bit bytes."
  :long
  (xdoc::topstring
   (xdoc::p
    "ACL2 has a flexible notion of `byte',
     which may be signed or unsigned,
     and consist of (almost) any number of bits:
     see @(tsee unsigned-byte-p) and @(tsee signed-byte-p).
     But very often the unqualified term `byte'
     refers to a sequence of exactly 8 bits,
     represented by natural numbers below 256,
     and the term `nibble' refers to half of such a byte,
     i.e. a sequence of 4 bits,
     represented by natural numbers below 16;
     this predicate caters to this common terminology."))
  (mbe :logic (unsigned-byte-p 4 x)
       :exec (and (integerp x)
                  (<= 0 x)
                  (< x 16)))
  :no-function t
  ///

  (defthm nibblep-compound-recognizer
    (implies (nibblep x)
             (and (integerp x)
                  (<= 0 x)))
    :rule-classes :compound-recognizer))
