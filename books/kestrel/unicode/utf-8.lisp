; Unicode Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "UNICODE")

(include-book "code-points")

(include-book "unicode/utf8-decode" :dir :system)

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection utf-8
  :parents (unicode)
  :short "Connection with the UTF-8 decoder and encoder
          of @('[books]/unicode')."
  :long
  (xdoc::topstring
   (xdoc::p
    "UTF-8 is the encoding form of the Unicode Standard
     that represents each scalar value by one to four bytes
     [Unicode, Section 3.9];
     UTF is short for Unicode Transformation Format.")
   (xdoc::p
    "This library does not have its own UTF-8 decoder and encoder:
     the library @(see acl2::unicode) has verified ones.
     That library calls `Unicode characters'
     what the Unicode Standard, and this library, call scalar values;
     its recognizers are @(tsee acl2::uchar?) and @(tsee acl2::ustring?).
     The theorems here say that they are the same
     as @(tsee scalar-value-p) and @(tsee scalar-value-listp),
     so that the result of decoding UTF-8
     can be passed to the functions of this library.")
   (xdoc::p
    "The first two theorems are disabled:
     enable them to rewrite the recognizers of that library
     to the ones of this library."))

  (defruled uchar?-is-scalar-value-p
    (equal (acl2::uchar? x)
           (scalar-value-p x))
    :enable (acl2::uchar? scalar-value-p-alt-def natp)
    :disable scalar-value-p)

  (defruled ustring?-is-scalar-value-listp
    (equal (acl2::ustring? x)
           (scalar-value-listp x))
    :induct t
    :enable (acl2::ustring? scalar-value-listp uchar?-is-scalar-value-p))

  (defrulel scalar-value-listp-when-ustring?
    (implies (acl2::ustring? x)
             (scalar-value-listp x))
    :enable ustring?-is-scalar-value-listp)

  (defrulel utf8-partition-when-utf8=>ustring-does-not-fail
    (implies (not (equal (acl2::utf8=>ustring bytes) 'acl2::fail))
             (mv-nth 0 (acl2::utf8-partition bytes)))
    :enable acl2::utf8=>ustring)

  (defrule scalar-value-listp-of-utf8=>ustring
    (implies (not (equal (acl2::utf8=>ustring bytes) 'acl2::fail))
             (scalar-value-listp (acl2::utf8=>ustring bytes)))))
