; Representation of Natural Numbers as Digits in Power-of-Two Bases
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/utilities/fixbytes/instances" :dir :system)
(include-book "kestrel/utilities/digits-any-base" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc digits-any-base-pow2
  :parents (digits-any-base)
  :short "Conversions between natural numbers
          and their representations as digits in power-of-two bases."
  :long
  "<p>
   When the base is a (positive) power of 2,
   digits are <see topic='@(url unsigned-byte-p)'>unsigned bytes</see>
   of positive size (the exponent of the base).
   Thus, here we provide theorems about this connection.
   </p>")

(local (xdoc::set-default-parents digits-any-base-pow2))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection digit-byte-equivalence
  :short "Equivalences between digits and bytes."
  :long
  "<p>
   These rules are disabled by default.
   They can be selectively enabled for specific proofs as needed.
   </p>
   <p>
   Note that the converse equalities
   would include @('(expt 2 n)') in their left-hand sides,
   which may rarely match,
   in particular when the base is a constant power of 2.
   We may add converse theorems with a generic base,
   a hypothesis that the base is a power of 2,
   and a logarithm in base 2 in the right hand side.
   </p>"

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defthm-digit-byte-return-types-fn ((n posp))
  :returns (event pseudo-event-formp)
  :verify-guards nil
  :parents (defthm-digits-any-base-pow2-return-types)
  :short "Event form to introduce return type theorems for
          the conversions from natural numbers
          to digits in a specified power-of-2 base."
  :long
  "<p>
   The event form is a @(tsee defsection)
   with six theorems asserting that
   the conversions from natural numbers to digits in base @('(expt 2 n)')
   return true lists of unsigned bytes of size @('n').
   These are expressed using the fixtypes for true lists of unsigned bytes
   introduced via @(tsee defbyte).
   </p>"
  (b* ((ubyte<n> (packn (list 'ubyte n)))
       (ubyte<n>-listp (packn (list ubyte<n> '-listp)))
       (ubyte<n>-listp-of-nat=>bendian* (packn (list ubyte<n>-listp
                                                     '-of-nat=>bendian*)))
       (ubyte<n>-listp-of-nat=>bendian+ (packn (list ubyte<n>-listp
                                                     '-of-nat=>bendian+)))
       (ubyte<n>-listp-of-nat=>bendian (packn (list ubyte<n>-listp
                                                    '-of-nat=>bendian)))
       (ubyte<n>-listp-of-nat=>lendian* (packn (list ubyte<n>-listp
                                                     '-of-nat=>lendian*)))
       (ubyte<n>-listp-of-nat=>lendian+ (packn (list ubyte<n>-listp
                                                     '-of-nat=>lendian+)))
       (ubyte<n>-listp-of-nat=>lendian (packn (list ubyte<n>-listp
                                                    '-of-nat=>lendian)))
       (ubyte<n>-listp-rewrite-unsigned-byte-listp
        (packn (list ubyte<n>-listp '-rewrite-unsigned-byte-listp)))
       (digit-byte<n>-return-types (packn (list 'digit-byte
                                                n
                                                '-return-types)))
       (base (expt 2 n))
       (<n>-string (coerce (explode-nonnegative-integer n 10 nil) 'string)))
    `(defsection ,digit-byte<n>-return-types
       :parents (digits-any-base-pow2)
       :short ,(concatenate 'string
                            "Return type theorems for "
                            "conversions from natural numbers "
                            "to digits in base @($2^{"
                            <n>-string
                            "}$).")
       (defthm ,ubyte<n>-listp-of-nat=>bendian*
         (,ubyte<n>-listp (nat=>bendian* ,base x))
         :hints (("Goal"
                  :in-theory
                  (enable ,ubyte<n>-listp-rewrite-unsigned-byte-listp
                          unsigned-byte-listp-rewrite-dab-digit-listp))))
       (defthm ,ubyte<n>-listp-of-nat=>bendian+
         (,ubyte<n>-listp (nat=>bendian+ ,base x))
         :hints (("Goal"
                  :in-theory
                  (enable ,ubyte<n>-listp-rewrite-unsigned-byte-listp
                          unsigned-byte-listp-rewrite-dab-digit-listp))))
       (defthm ,ubyte<n>-listp-of-nat=>bendian
         (,ubyte<n>-listp (nat=>bendian ,base width x))
         :hints (("Goal"
                  :in-theory
                  (enable ,ubyte<n>-listp-rewrite-unsigned-byte-listp
                          unsigned-byte-listp-rewrite-dab-digit-listp))))
       (defthm ,ubyte<n>-listp-of-nat=>lendian*
         (,ubyte<n>-listp (nat=>lendian* ,base x))
         :hints (("Goal"
                  :in-theory
                  (enable ,ubyte<n>-listp-rewrite-unsigned-byte-listp
                          unsigned-byte-listp-rewrite-dab-digit-listp))))
       (defthm ,ubyte<n>-listp-of-nat=>lendian+
         (,ubyte<n>-listp (nat=>lendian+ ,base x))
         :hints (("Goal"
                  :in-theory
                  (enable ,ubyte<n>-listp-rewrite-unsigned-byte-listp
                          unsigned-byte-listp-rewrite-dab-digit-listp))))
       (defthm ,ubyte<n>-listp-of-nat=>lendian
         (,ubyte<n>-listp (nat=>lendian ,base width x))
         :hints (("Goal"
                  :in-theory
                  (enable ,ubyte<n>-listp-rewrite-unsigned-byte-listp
                          unsigned-byte-listp-rewrite-dab-digit-listp)))))))

(defsection defthm-digit-byte-return-types
  :short "Introduce return type theorems for
          the conversions from natural numbers
          to digits in the specified power-of-2 base."
  :long "@(def defthm-digit-byte-return-types)"
  (defmacro defthm-digit-byte-return-types (size)
    (declare (xargs :guard (posp size)))
    `(make-event (defthm-digit-byte-return-types-fn ,size))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm-digit-byte-return-types 1)
(defthm-digit-byte-return-types 2)
(defthm-digit-byte-return-types 3)
(defthm-digit-byte-return-types 4)
(defthm-digit-byte-return-types 8)
