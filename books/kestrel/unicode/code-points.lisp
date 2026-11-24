; Unicode Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "UNICODE")

(include-book "centaur/fty/top" :dir :system)
(include-book "kestrel/unicode-light/surrogates" :dir :system)
(include-book "kestrel/utilities/integers-from-to" :dir :system)
(include-book "std/lists/flatten" :dir :system)
(include-book "std/util/deffixer" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

(local (include-book "std/lists/top" :dir :system)) ; for more DEFLIST theorems

(include-book "std/basic/controlled-configuration" :dir :system)
(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ code-points
  :parents (unicode)
  :short "Unicode code points and scalar values."
  :long
  (xdoc::topstring
   (xdoc::p
    "The Unicode codespace is the range of integers
     from 0 to @('#x10FFFF') [Unicode, D9];
     a code point is any value in the codespace [Unicode, D10].
     The surrogate code points are
     those from @('#xD800') to @('#xDFFF') [Unicode, D71, D73];
     they are reserved for the UTF-16 encoding form.
     A Unicode scalar value is
     any code point that is not a surrogate [Unicode, D76].
     Scalar values are what the Unicode encoding forms,
     and UTF-8 in particular, encode.")
   (xdoc::p
    "We represent code points as ACL2 natural numbers,
     never as ACL2 characters,
     of which there are only 256.")
   (xdoc::p
    "Surrogates are code points, but they are not scalar values.
     The functions of this library that are defined on all code points,
     such as property lookups and normalization,
     accept surrogates:
     the Unicode Character Database assigns property values to them.
     Theorems say that scalar values are mapped to scalar values
     where that matters.")
   (xdoc::p
    "The recognizers of high and low surrogates
     are those of @('[books]/kestrel/unicode-light/surrogates').
     The book @('utf-8') in this directory
     relates the scalar values to the Unicode characters
     of the UTF-8 decoder and encoder in @('[books]/unicode')."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define code-point-p (x)
  :returns (yes/no booleanp)
  :short "Recognize Unicode code points."
  :long
  (xdoc::topstring
   (xdoc::p
    "A code point is a natural number not exceeding @('#x10FFFF')."))
  (and (natp x)
       (<= x #x10FFFF))

  ///

  (defrule natp-when-code-point-p
    (implies (code-point-p x)
             (natp x))
    :rule-classes :compound-recognizer)

  (defrule code-point-p-upper-bound
    (implies (code-point-p x)
             (<= x #x10FFFF))
    :rule-classes :forward-chaining)

  (defruled code-point-p-when-unsigned-byte-p-8
    (implies (unsigned-byte-p 8 x)
             (code-point-p x))
    :enable unsigned-byte-p))

;;;;;;;;;;;;;;;;;;;;

(std::deffixer code-point-fix
  :short "Fixer for @(tsee code-point-p)."
  :pred code-point-p
  :body-fix 0)

;;;;;;;;;;;;;;;;;;;;

(defsection code-point
  :short "Fixtype of Unicode code points."
  (fty::deffixtype code-point
    :pred code-point-p
    :fix code-point-fix
    :equiv code-point-equiv
    :define t))

;;;;;;;;;;;;;;;;;;;;

(fty::deflist code-point-list
  :short "Fixtype of lists of Unicode code points."
  :elt-type code-point
  :true-listp t
  :elementp-of-nil nil
  :pred code-point-listp

  ///

  (defruled nat-listp-when-code-point-listp
    (implies (code-point-listp x)
             (nat-listp x))
    :induct t
    :enable nat-listp))

;;;;;;;;;;;;;;;;;;;;

(fty::deflist code-point-list-list
  :short "Fixtype of lists of lists of code points."
  :elt-type code-point-list
  :true-listp t
  :elementp-of-nil t
  :pred code-point-list-listp

  ///

  (defrule code-point-listp-of-flatten
    (implies (code-point-list-listp x)
             (code-point-listp (acl2::flatten x)))
    :induct t
    :enable acl2::flatten)

  (defrule flatten-of-code-point-list-list-fix
    (equal (acl2::flatten (code-point-list-list-fix x))
           (code-point-list-fix (acl2::flatten x)))
    :induct t
    :enable (acl2::flatten code-point-list-list-fix)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define surrogate-p ((cp code-point-p))
  :returns (yes/no booleanp)
  :short "Check if a code point is a surrogate."
  :long
  (xdoc::topstring
   (xdoc::p
    "That is, a high surrogate or a low surrogate,
     as recognized by the functions of
     @('[books]/kestrel/unicode-light/surrogates').
     The surrogates are the code points
     from @('#xD800') to @('#xDFFF')."))
  (b* ((cp (code-point-fix cp)))
    (or (high-surrogatep cp)
        (low-surrogatep cp)))
  :guard-hints (("Goal" :in-theory (enable code-point-p)))

  ///

  (fty::deffixequiv surrogate-p)

  (defruled surrogate-p-alt-def
    (equal (surrogate-p cp)
           (b* ((cp (code-point-fix cp)))
             (and (<= #xD800 cp)
                  (<= cp #xDFFF))))
    :enable (acl2::high-surrogatep acl2::low-surrogatep)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define scalar-value-p (x)
  :returns (yes/no booleanp)
  :short "Recognize Unicode scalar values."
  :long
  (xdoc::topstring
   (xdoc::p
    "A scalar value is a code point that is not a surrogate."))
  (and (code-point-p x)
       (not (surrogate-p x)))

  ///

  (defrule code-point-p-when-scalar-value-p
    (implies (scalar-value-p x)
             (code-point-p x)))

  (defrule natp-when-scalar-value-p
    (implies (scalar-value-p x)
             (natp x))
    :rule-classes :compound-recognizer)

  (defruled scalar-value-p-alt-def
    (equal (scalar-value-p x)
           (and (natp x)
                (or (<= x #xD7FF)
                    (and (<= #xE000 x)
                         (<= x #x10FFFF)))))
    :enable (code-point-p surrogate-p-alt-def code-point-fix))

  (defruled scalar-value-p-when-unsigned-byte-p-8
    (implies (unsigned-byte-p 8 x)
             (scalar-value-p x))
    :enable (scalar-value-p-alt-def unsigned-byte-p)
    :disable scalar-value-p))

;;;;;;;;;;;;;;;;;;;;

(std::deffixer scalar-value-fix
  :short "Fixer for @(tsee scalar-value-p)."
  :pred scalar-value-p
  :body-fix 0)

;;;;;;;;;;;;;;;;;;;;

(defsection scalar-value
  :short "Fixtype of Unicode scalar values."
  (fty::deffixtype scalar-value
    :pred scalar-value-p
    :fix scalar-value-fix
    :equiv scalar-value-equiv
    :define t))

;;;;;;;;;;;;;;;;;;;;

(fty::deflist scalar-value-list
  :short "Fixtype of lists of Unicode scalar values."
  :elt-type scalar-value
  :true-listp t
  :elementp-of-nil nil
  :pred scalar-value-listp

  ///

  (defrule code-point-listp-when-scalar-value-listp
    (implies (scalar-value-listp x)
             (code-point-listp x))
    :induct t
    :enable code-point-listp))

;;;;;;;;;;;;;;;;;;;;

(fty::defoption scalar-value-option
  scalar-value
  :short "Fixtype of optional Unicode scalar values."
  :pred scalar-value-option-p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define all-code-points ()
  :returns (cps code-point-listp)
  :short "The list of all the code points."
  :long
  (xdoc::topstring
   (xdoc::p
    "There are 1,114,112 code points.
     A statement about all the code points
     that does not follow from the definitions alone,
     because it depends on the tables
     generated from the Unicode Character Database,
     can be proved by checking it,
     by evaluation, on each element of this list.
     The executable counterpart of this function is disabled
     so that the list does not end up in a formula
     unless a proof asks for it."))
  (integers-from-to 0 #x10FFFF)

  :prepwork
  ((defrulel code-point-listp-of-integers-from-to
     (implies (and (natp min)
                   (integerp max)
                   (<= max #x10FFFF))
              (code-point-listp (integers-from-to min max)))
     :induct t
     :enable (integers-from-to
              code-point-p
              natp
              ifix)))

  ///

  (in-theory (disable (:e all-code-points)))

  (defrule member-equal-of-all-code-points
    (iff (member-equal cp (all-code-points))
         (code-point-p cp))
    :enable (code-point-p natp)
    :disable ((:e integers-from-to))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define code-points-below-p ((cps code-point-listp) (bound natp))
  :returns (yes/no booleanp)
  :short "Check if all the code points of a list are below a bound."
  :long
  (xdoc::topstring
   (xdoc::p
    "With bound @('#x80'), this recognizes the lists of ASCII code points.
     Some theorems of this library say that
     an operation leaves such a list unchanged."))
  (or (endp cps)
      (and (< (code-point-fix (car cps)) (lnfix bound))
           (code-points-below-p (cdr cps) bound)))

  ///

  (defrule code-points-below-p-of-cons
    (equal (code-points-below-p (cons cp cps) bound)
           (and (< (code-point-fix cp) (nfix bound))
                (code-points-below-p cps bound))))

  (defrule code-points-below-p-of-nil
    (code-points-below-p nil bound))

  (defruled code-points-below-p-when-below-smaller
    (implies (and (code-points-below-p cps bound1)
                  (<= (nfix bound1) (nfix bound2)))
             (code-points-below-p cps bound2))
    :induct t))
