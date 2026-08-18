; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Stephen Westfold

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "portcullis")

(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)
(include-book "unicode/utf8-decode" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection unicode-theorems
  :parents (identifier-syntax)
  :short "General theorems about UTF-8 encoding and decoding."
  :long
  (xdoc::topstring
   (xdoc::p
    "These theorems are about the functions of @('unicode/utf8-decode')
     only; they mention nothing specific to Remora.  They support the
     identifier extension theorems of @(see identifier-syntax), which
     lift code-point-level facts about identifiers to the byte level
     at which @(tsee valid-identifier-string-p) works.")
   (xdoc::p
    "Both rules are left disabled, like the theorems they support."))

  ;; A Unicode string's UTF-8 encoding partitions; this is one half of
  ;; the encode/decode round trip of unicode/utf8-decode.

  (defruled utf8-partition-of-ustring=>utf8
    (implies (acl2::ustring? x)
             (mv-nth 0 (acl2::utf8-partition (acl2::ustring=>utf8 x))))
    :induct (acl2::ustring=>utf8 x)
    :enable (acl2::utf8-partition acl2::ustring=>utf8 acl2::ustring?))

  ;; A successful decoding is exactly a successful partitioning; this is
  ;; how a hypothesis that a byte sequence decodes supplies the
  ;; hypothesis of the self-synchronization rule
  ;; UTF8=>USTRING-OF-APPEND-WHEN-UTF8-PARTITION.

  (defruled utf8-partition-when-decoding-succeeds
    (implies (nat-listp (acl2::utf8=>ustring bytes))
             (mv-nth 0 (acl2::utf8-partition bytes)))
    :enable acl2::utf8=>ustring))
