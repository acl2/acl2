; Java Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

(include-book "kestrel/fty/defbytelist" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ unicode-characters
  :parents (language)
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
  :short "Java Unicode characters."
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
  :short "True lists of Java Unicode characters."
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
  :short "ASCII characters."
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
  :short "True lists of ASCII characters."
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
