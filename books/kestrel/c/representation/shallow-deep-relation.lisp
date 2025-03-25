; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "integers")

(include-book "../language/values")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ shallow-deep-embedding-relation
  :parents (representation)
  :short "Relation between shallow and deep embedding of C."
  :long
  (xdoc::topstring
   (xdoc::p
    "For now we provide only a few theorems that relate
     notions from the shallow embedding
     with notions from the deep embedding.
     We plan to extend these at some point."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection integer-predicates-alternative-definitions
  :short "Alternative definitions of predicates for integer values."
  :long
  (xdoc::topstring
   (xdoc::p
    "These provide alternative definitions of predicates like @(tsee sintp)
     in terms of @(tsee valuep) and @(tsee value-kind)."))

  (defruled scharp-alt-def
    (equal (scharp x)
           (and (valuep x)
                (equal (value-kind x) :schar)))
    :enable (scharp valuep value-kind))

  (defruled ucharp-alt-def
    (equal (ucharp x)
           (and (valuep x)
                (equal (value-kind x) :uchar)))
    :enable (ucharp valuep value-kind))

  (defruled sshortp-alt-def
    (equal (sshortp x)
           (and (valuep x)
                (equal (value-kind x) :sshort)))
    :enable (sshortp valuep value-kind))

  (defruled ushortp-alt-def
    (equal (ushortp x)
           (and (valuep x)
                (equal (value-kind x) :ushort)))
    :enable (ushortp valuep value-kind))

  (defruled sintp-alt-def
    (equal (sintp x)
           (and (valuep x)
                (equal (value-kind x) :sint)))
    :enable (sintp valuep value-kind))

  (defruled uintp-alt-def
    (equal (uintp x)
           (and (valuep x)
                (equal (value-kind x) :uint)))
    :enable (uintp valuep value-kind))

  (defruled slongp-alt-def
    (equal (slongp x)
           (and (valuep x)
                (equal (value-kind x) :slong)))
    :enable (slongp valuep value-kind))

  (defruled ulongp-alt-def
    (equal (ulongp x)
           (and (valuep x)
                (equal (value-kind x) :ulong)))
    :enable (ulongp valuep value-kind))

  (defruled sllongp-alt-def
    (equal (sllongp x)
           (and (valuep x)
                (equal (value-kind x) :sllong)))
    :enable (sllongp valuep value-kind))

  (defruled ullongp-alt-def
    (equal (ullongp x)
           (and (valuep x)
                (equal (value-kind x) :ullong)))
    :enable (ullongp valuep value-kind)))
