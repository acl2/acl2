; Java Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

(include-book "kestrel/fty/defbytelist" :dir :system)
(include-book "kestrel/utilities/strings/strings-codes-fty" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ unicode-characters
  :parents (syntax)
  :short "Unicode characters in Java [JLS:3.1]."
  :long
  (xdoc::topstring
   (xdoc::p
    "The Unicode standard distinguishes among
     `characters', `code points', and `code units'.
     In Java, characters are essentially Unicode UTF-16 code units,
     i.e. unsigned 16-bit values.
     In our formalization, as in [JLS],
     we may use the terms `character', `code point', and `code unit'
     fairly interchangeably, when that causes no confusion."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defbyte unicode
  :short "Fixtype of Java Unicode characters."
  :long
  (xdoc::topstring
   (xdoc::p
    "This type models Java characters in the context of modeling Java's syntax.
     This is isomorphic, but distinct from, the type @(tsee char-value)
     that models Java characters in the context of modeling Java's semantics.
     The reason for having these two different types is that
     we want character values to be tagged when modeling semantics,
     while we want characters to be simple numbers when modeling syntax."))
  :size 16
  :pred unicodep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defbytelist unicode-list
  :short "Fixtype of true lists of Java Unicode characters."
  :long
  (xdoc::topstring
   (xdoc::p
    "Values of this type model Java strings,
     at a more essential and abstract level than
     instances of the class @('java.lang.String')."))
  :elt-type unicode
  :pred unicode-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defbyte ascii
  :short "Fixtype of ASCII characters."
  :long
  (xdoc::topstring
   (xdoc::p
    "The ASCII characters are the first 128 Unicode characters.")
   (xdoc::p
    "Since we model Java Unicode characters as unsigned 16-bit integers,
     we model ASCII characters as unsigned 7-bit integers."))
  :size 7
  :pred asciip)

(defsection ascii-ext
  :extension ascii

  (defrule unicodep-when-asciip
    (implies (asciip x)
             (unicodep x))
    :enable (asciip unicodep)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defbytelist ascii-list
  :short "Fixtype of true lists of ASCII characters."
  :long
  (xdoc::topstring
   (xdoc::p
    "Values of this type model Java strings
     (at a more essential and abstract level than
     instances of the class @('java.lang.String'))
     that consist of only ASCII characters."))
  :elt-type ascii
  :pred ascii-listp)

(defsection ascii-list-ext
  :extension ascii-list

  (defrule unicode-listp-when-ascii-listp
    (implies (ascii-listp x)
             (unicode-listp x))
    :enable (ascii-listp unicode-listp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define string=>unicode ((string stringp))
  :returns (unicode unicode-listp
                    :hints (("Goal"
                             :in-theory
                             (enable
                              unsigned-byte-listp-16-when-8
                              unicode-listp-rewrite-unsigned-byte-listp))))
  :short "Convert an ACL2 string to a Java Unicode character list."
  :long
  (xdoc::topstring
   (xdoc::p
    "The ACL2 characters are ISO-8859-1: see "
    (xdoc::seetopic "acl2::characters" "this topic")
    ", and the @('acl2.lisp') system souce file.")
   (xdoc::p
    "Since the ISO-8859-1 characters are the first 256 Unicode characters,
     and since we model Java Unicode characters as unsigned 16-bit integers,
     the library function @(tsee string=>nats) can be used
     to convert ACL2 strings to Java Unicode character lists.
     Here we define a wrapper of this function
     with an appropriate return type theorem.")
   (xdoc::p
    "See also @(tsee ascii=>string)."))
  (string=>nats string)
  :prepwork ((defruledl unsigned-byte-listp-16-when-8
               (implies (unsigned-byte-listp 8 x)
                        (unsigned-byte-listp 16 x))
               :enable unsigned-byte-listp))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ascii=>string ((ascii ascii-listp))
  :returns (string stringp)
  :short "Convert a Java ASCII character list to an ACL2 string."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the inverse of @(tsee string=>unicode)
     for the ASCII subset of Unicode.
     It converts lists of ASCII codes to Java strings,
     using the library function @(tsee nats=>string).")
   (xdoc::p
    "This function could be extended to the ISO-8859-1 subset of Unicode,
     but for now this is not needed in our Java formalization."))
  (b* ((ascii (mbe :logic (ascii-list-fix ascii) :exec ascii)))
    (nats=>string ascii))
  :guard-hints (("Goal" :in-theory (enable unsigned-byte-listp-8-when-7)))
  :prepwork ((defruledl unsigned-byte-listp-8-when-7
               (implies (unsigned-byte-listp 7 x)
                        (unsigned-byte-listp 8 x))
               :enable unsigned-byte-listp))
  :hooks (:fix)
  ///

  (defrule ascii=>string-of-string=>unicode
    (implies (ascii-listp (string=>unicode string))
             (equal (ascii=>string (string=>unicode string))
                    (str-fix string)))
    :enable string=>unicode)

  (defrule string=>unicode-of-ascii=>string
    (equal (string=>unicode (ascii=>string ascii))
           (ascii-list-fix ascii))
    :enable string=>unicode
    :prep-lemmas
    ((defrule lemma
       (implies (ascii-listp x)
                (unsigned-byte-listp 8 x))
       :enable unsigned-byte-listp-8-when-7)))

  (defruled equal-of-ascii=>string-to-equal-of-string=>unicode
    (implies (and (ascii-listp x)
                  (stringp y))
             (equal (equal (ascii=>string x) y)
                    (equal (string=>unicode y) x)))
    :disable ascii=>string)

  (defruled equal-of-string=>unicode-to-equal-of-ascii=>string
    (implies (and (ascii-listp x)
                  (stringp y))
             (equal (equal (string=>unicode x) y)
                    (equal (ascii=>string y) x)))
    :disable ascii=>string)

  (theory-invariant
   (incompatible (:rewrite
                  equal-of-ascii=>string-to-equal-of-string=>unicode)
                 (:rewrite
                  equal-of-string=>unicode-to-equal-of-ascii=>string))))
