; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "centaur/fty/top" :dir :system)
(include-book "std/util/deffixer" :dir :system)

(include-book "std/basic/controlled-configuration" :dir :system)
(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ unicode-characters
  :parents (syntax-for-tools)
  :short "Unicode characters."
  :long
  (xdoc::topstring
   (xdoc::p
    "Although [C23] does not prescribe a specific character set,
     our syntax for tools uses Unicode, which is quite standard nowadays.")
   (xdoc::p
    "For now we do not need an elaborate model of Unicode characters,
     which would belong to a more general library anyways,
     but we define a few basic notion that are useful for our tools."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ucharp (x)
  :returns (yes/no booleanp)
  :short "Recognize Unicode characters."
  :long
  (xdoc::topstring
   (xdoc::p
    "More precisely, this recognizes Unicode scalar values,
     i.e. Unicode code points that are not high and low surrogates;
     also see our ABNF @(see grammar).
     Although code points, scalar values, and characters
     are distinct concepts in Unicode,
     for our purpose it is simpler to identify characters with scalar values,
     which justifies the name of this recognizer."))
  (and (integerp x)
       (or (integer-range-p 0 #xd7ff x)
           (integer-range-p #xe000 #x10ffff x)))

  ///

  (defruled natp-when-ucharp
    (implies (ucharp x)
             (natp x))
    :rule-classes (:rewrite :compound-recognizer))

  (defruled ucharp-lower-bound
    (implies (ucharp x)
             (>= x 0))
    :rule-classes :forward-chaining)

  (defruled ucharp-upper-bound
    (implies (ucharp x)
             (<= x #x10ffff))
    :rule-classes :forward-chaining))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::deffixer uchar-fix
  :short "Fixer for @(tsee ucharp)."
  :pred ucharp
  :body-fix 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection uchar
  :short "Fixtype of Unicode characters."
  (fty::deffixtype uchar
    :pred ucharp
    :fix uchar-fix
    :equiv uchar-equiv
    :define t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist uchar-list
  :short "Fixtype of lists of Unicode characters."
  :elt-type uchar
  :true-listp t
  :elementp-of-nil nil
  :pred uchar-listp)
