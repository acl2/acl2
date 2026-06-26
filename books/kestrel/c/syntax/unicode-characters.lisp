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
(include-book "std/typed-lists/unsigned-byte-listp" :dir :system)
(include-book "std/util/deffixer" :dir :system)

(local (include-book "std/lists/top" :dir :system)) ; for more DEFLIST theorems

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

(define unicharp (x)
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
       (or (and (<= 0 x)
                (<= x #xd7ff))
           (and (<= #xe000 x)
                (<= x #x10ffff))))

  ///

  (defruled unicharp-alt-def
    (equal (unicharp x)
           (and (integerp x)
                (<= 0 x)
                (<= x #x10ffff)
                (not (and (<= #xd800 x)
                          (<= x #xdfff))))))

  (defruled natp-when-unicharp
    (implies (unicharp x)
             (natp x))
    :rule-classes (:rewrite :compound-recognizer))

  (defruled integerp-when-unicharp
    (implies (unicharp x)
             (integerp x)))

  (defruled rationalp-when-unicharp
    (implies (unicharp x)
             (rationalp x)))

  (defruled acl2-numberp-when-unicharp
    (implies (unicharp x)
             (acl2-numberp x)))

  (defruled unicharp-lower-bound
    (implies (unicharp x)
             (>= x 0))
    :rule-classes :forward-chaining)

  (defruled unicharp-upper-bound
    (implies (unicharp x)
             (<= x #x10ffff))
    :rule-classes :forward-chaining)

  (defruled unicharp-when-unsigned-byte-p
    (implies (unsigned-byte-p 8 x)
             (unicharp x))
    :enable unsigned-byte-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled unicharp-of-char-code
  :short "The code of an ACL2 character is a Unicode character."
  (unicharp (char-code char))
  :enable unicharp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::deffixer unichar-fix
  :short "Fixer for @(tsee unicharp)."
  :pred unicharp
  :body-fix 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection unichar
  :short "Fixtype of Unicode characters."
  (fty::deffixtype unichar
    :pred unicharp
    :fix unichar-fix
    :equiv unichar-equiv
    :define t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption unichar-option
  unichar
  :short "Fixtype of optional Unicode characters."
  :pred unichar-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist unichar-list
  :short "Fixtype of lists of Unicode characters."
  :elt-type unichar
  :true-listp t
  :elementp-of-nil nil
  :pred unichar-listp

  ///

  (defruled unichar-listp-of-resize-list
    (implies (and (unichar-listp chars)
                  (unicharp default))
             (unichar-listp (resize-list chars length default)))
    :induct t
    :enable resize-list)

  (defruled nat-listp-when-unichar-listp
    (implies (unichar-listp x)
             (nat-listp x))
    :induct t
    :enable (unichar-listp nat-listp natp-when-unicharp))

  (defruled unichar-listp-when-unsigned-byte-listp-8
    (implies (unsigned-byte-listp 8 x)
             (unichar-listp x))
    :induct t
    :enable (unichar-listp unicharp-when-unsigned-byte-p)))
