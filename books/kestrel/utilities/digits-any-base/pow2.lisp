; Representation of Natural Numbers as Digits in Power-of-Two Bases
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/typed-lists/unsigned-byte-listp" :dir :system)
(include-book "core")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc digits-any-base-pow2
  :parents (digits-any-base)
  :short "Conversions between natural numbers
          and their representations as digits in power-of-two bases."
  :long
  (xdoc::topstring
   (xdoc::p
    "When the base is a (positive) power of 2,
     digits are <see topic='@(url unsigned-byte-p)'>unsigned bytes</see>
     of positive size (the exponent of the base).
     Thus, here we provide theorems about this connection.")))

(local (xdoc::set-default-parents digits-any-base-pow2))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection digit-pow2-unsigned-byte-equivalence
  :short "Equivalences between digits and bytes."
  :long
  (xdoc::topstring
   (xdoc::p
    "These rules are disabled by default.
     They can be selectively enabled for specific proofs as needed.")
   (xdoc::p
    "Note that the converse equalities
     would include @('(expt 2 n)') in their left-hand sides,
     which may rarely match,
     in particular when the base is a constant power of 2.
     We may add converse theorems with a generic base,
     a hypothesis that the base is a power of 2,
     and a logarithm in base 2 in the right hand side."))

  (defruled unsigned-byte-p-rewrite-dab-digitp
    (implies (posp n)
             (equal (unsigned-byte-p n x)
                    (dab-digitp (expt 2 n) x)))
    :enable dab-digitp)

  (defruled unsigned-byte-listp-rewrite-dab-digit-listp
    (implies (posp n)
             (equal (unsigned-byte-listp n x)
                    (dab-digit-listp (expt 2 n) x)))
    :enable (dab-digit-listp
             unsigned-byte-listp
             unsigned-byte-p-rewrite-dab-digitp)))
