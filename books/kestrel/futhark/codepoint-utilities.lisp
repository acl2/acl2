; Futhark Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "FUTHARK")

(include-book "portcullis")
(include-book "kestrel/fty/nat-list-result" :dir :system)
(include-book "kestrel/fty/string-result" :dir :system)
(include-book "kestrel/utilities/strings/strings-codes" :dir :system)
(include-book "std/basic/defs" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "unicode/utf8-decode" :dir :system)
(include-book "unicode/utf8-encode" :dir :system)
(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ codepoint-utilities
  :parents (futhark)
  :short "Reusable Unicode code-point and UTF-8 utilities for Futhark books."
  :long
  (xdoc::topstring
   (xdoc::p
    "The parser books operate internally on lists of Unicode code points,
     represented as natural numbers.  ACL2 strings are byte strings, so public
     string entry points decode UTF-8 bytes to code points before parsing, and
     syntax abstraction and printing encode code points back to UTF-8 bytes.")
   (xdoc::p
    "This book contains utilities that are not specific to the Futhark IR
     grammar and can be reused by a future Futhark source-language front end."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ascii-digit-codepointp ((nat natp))
  :returns (yes/no booleanp)
  :short "Check if a code point is an ASCII digit."
  (b* ((nat (nfix nat)))
    (and (<= #x30 nat) (<= nat #x39))))

(define ascii-letter-codepointp ((nat natp))
  :returns (yes/no booleanp)
  :short "Check if a code point is an ASCII letter."
  (b* ((nat (nfix nat)))
    (or (and (<= #x41 nat) (<= nat #x5A))
        (and (<= #x61 nat) (<= nat #x7A)))))

(define unicode-scalar-codepointp ((nat natp))
  :returns (yes/no booleanp)
  :short "Check if a natural number is a Unicode scalar value."
  (b* ((nat (nfix nat)))
    (or (and (<= nat #xD7FF))
        (and (<= #xE000 nat) (<= nat #x10FFFF)))))

(define non-ascii-non-whitespace-codepointp ((nat natp))
  :returns (yes/no booleanp)
  :short "Check if a natural number is a non-ASCII, non-whitespace scalar."
  :long
  (xdoc::topstring
   (xdoc::p
    "This follows Remora's executable non-ASCII character class: Unicode
     scalar values above @('#x7F'), excluding non-ASCII whitespace code points
     and surrogates."))
  (b* ((nat (nfix nat)))
    (or (and (<= #x80 nat) (<= nat #x9F))
        (and (<= #xA1 nat) (<= nat #x167F))
        (and (<= #x1681 nat) (<= nat #x1FFF))
        (and (<= #x200B nat) (<= nat #x2027))
        (and (<= #x202A nat) (<= nat #x202E))
        (and (<= #x2030 nat) (<= nat #x205E))
        (and (<= #x2060 nat) (<= nat #x2FFF))
        (and (<= #x3001 nat) (<= nat #xD7FF))
        (and (<= #xE000 nat) (<= nat #x10FFFF)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define decode-utf8-string ((str stringp))
  :returns (codepoints acl2::nat-list-resultp)
  :short "Decode an ACL2 byte string as UTF-8 code points."
  (b* ((bytes (acl2::string=>nats (str-fix str)))
       ((unless (acl2::unsigned-byte-listp 8 bytes))
        (reserrf (cons :invalid-octets bytes)))
       (codepoints (acl2::utf8=>ustring bytes))
       ((unless (nat-listp codepoints))
        (reserrf (cons :invalid-utf-8 bytes))))
    codepoints))

(define string=>codepoints ((str stringp))
  :returns (codepoints nat-listp)
  :short "Decode an ACL2 UTF-8 byte string to code points; return nil on error."
  (b* ((codepoints (decode-utf8-string str))
       ((when (reserrp codepoints)) nil))
    codepoints))

(define codepoints=>string ((codepoints nat-listp))
  :returns (str acl2::string-resultp)
  :short "UTF-8 encode code points and pack the bytes into an ACL2 string."
  (b* ((codepoints (nat-list-fix codepoints)))
    (if (acl2::ustring? codepoints)
        (acl2::nats=>string (acl2::ustring=>utf8 codepoints))
      (reserrf (list :invalid-codepoints codepoints)))))
