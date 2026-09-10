; Rust Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "RUST$")

(include-book "centaur/fty/top" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/utilities/nfix" :dir :system))
(local (include-book "kestrel/utilities/ordinals" :dir :system))

(include-book "std/basic/controlled-configuration" :dir :system)
(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ unicode-characters
  :parents (syntax-for-tools)
  :short "Unicode scalar values, the characters of Rust source."
  :long
  (xdoc::topstring
   (xdoc::p
    "A Rust source file is a sequence of Unicode characters
     ["
    (xdoc::ahref
     "https://doc.rust-lang.org/1.87.0/reference/input-format.html"
     "Reference: Input format")
    "],
     i.e. of Unicode scalar values:
     code points excluding the surrogate range,
     which is what UTF-8 can encode.
     Rust's @('char') type has exactly these values as well.")
   (xdoc::p
    "We represent Unicode scalar values as ACL2 naturals.
     The lexer operates on lists of them;
     UTF-8 decoding of source bytes belongs to
     the file-reading layer, not here.
     (The lexical grammar's terminal set is defined separately,
     in the grammar book, over naturals;
     decoded source input always satisfies
     the predicates of this book.)"))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define uni-scalar-value-p (x)
  :returns (yes/no booleanp)
  :short "Recognize Unicode scalar values."
  :long
  (xdoc::topstring
   (xdoc::p
    "A Unicode scalar value is a code point
     (a natural number up to @('#x10ffff'))
     that is not a surrogate
     (the range @('#xd800') to @('#xdfff'),
     reserved for UTF-16 and not encodable in UTF-8)."))
  (and (natp x)
       (<= x #x10ffff)
       (not (and (<= #xd800 x)
                 (<= x #xdfff))))

  ///

  (defrule natp-when-uni-scalar-value-p
    (implies (uni-scalar-value-p x)
             (natp x))
    :rule-classes :compound-recognizer))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::deflist uni-scalar-value-listp (x)
  :short "Recognize lists of Unicode scalar values."
  (uni-scalar-value-p x)
  :true-listp t
  :elementp-of-nil nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule nat-listp-when-uni-scalar-value-listp
  (implies (uni-scalar-value-listp x)
           (nat-listp x))
  :induct t
  :enable (uni-scalar-value-listp nat-listp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-event (uni-scalar-value-p 0))
(assert-event (uni-scalar-value-p (char-code #\a)))
(assert-event (uni-scalar-value-p #x3bb)) ; GREEK SMALL LETTER LAMBDA
(assert-event (uni-scalar-value-p #xd7ff)) ; last before surrogates
(assert-event (not (uni-scalar-value-p #xd800))) ; high surrogate
(assert-event (not (uni-scalar-value-p #xdfff))) ; low surrogate
(assert-event (uni-scalar-value-p #xe000)) ; first after surrogates
(assert-event (uni-scalar-value-p #x10ffff)) ; maximum
(assert-event (not (uni-scalar-value-p #x110000)))
(assert-event (not (uni-scalar-value-p -1)))
(assert-event (not (uni-scalar-value-p "a")))
(assert-event (uni-scalar-value-listp (list #x66 #x6e #x2028)))
(assert-event (not (uni-scalar-value-listp (list #x66 #xd800))))
