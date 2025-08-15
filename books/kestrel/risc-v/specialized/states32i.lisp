; RISC-V Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2025 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "RISCV")

(include-book "features")

(include-book "../specification/states")

(include-book "kestrel/apt/isodata" :dir :system)
(include-book "kestrel/apt/parteval" :dir :system)
(include-book "kestrel/apt/simplify" :dir :system)
(include-book "kestrel/fty/deflist-of-len" :dir :system)
(include-book "std/util/defiso" :dir :system)

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrulel lnfix-when-natp
  (implies (natp x)
           (equal (lnfix x) x))
  :enable nfix)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ states32i
  :parents (specialized-states)
  :short "Specialized states for features with the RV32I base."
  :long
  (xdoc::topstring
   (xdoc::p
    "We define a recognizer for the valid states for the RV32I base.
     We introduce a fixtype that is isomorphic to that recognizer.
     We specialize the operations on states to operate on that fixtype.
     This is work in progress."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define stat-rv32i-p (x)
  :returns (yes/no booleanp)
  :short "Recognizer of states with base RV32I."
  :long
  (xdoc::topstring
   (xdoc::p
    "These only depend on the base,
     not on the M extension or the endianness."))
  (and (statp x)
       (stat-validp x (feat-rv32i-le)))

  ///

  (defruled stat-rv32i-p-alt-def-be
    (equal (stat-rv32i-p x)
           (and (statp x)
                (stat-validp x (feat-rv32i-be))))
    :enable (stat-validp
             (:e feat-rv32i-le)
             (:e feat-rv32i-be)))

  (defruled stat-rv32i-p-alt-def-m-le
    (equal (stat-rv32i-p x)
           (and (statp x)
                (stat-validp x (feat-rv32im-le))))
    :enable (stat-validp
             (:e feat-rv32i-le)
             (:e feat-rv32im-le)))

  (defruled stat-rv32i-p-alt-def-m-be
    (equal (stat-rv32i-p x)
           (and (statp x)
                (stat-validp x (feat-rv32im-be))))
    :enable (stat-validp
             (:e feat-rv32i-le)
             (:e feat-rv32im-be)))

  (defruled unsigned-byte-p-32-of-nth-of-stat-rv32i->xregs
    (implies (and (stat-validp stat (feat-rv32i-le))
                  (natp reg)
                  (< reg 32))
             (unsigned-byte-p 32 (nth (1- reg) (stat->xregs stat))))
    :enable (stat-validp nfix (:e feat-rv32i-le))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist-of-len xregs32i
  :short "Fixtype of the @('x') registers for the RV32I base."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a list of 31 unsigned 32-bit integers,
     according to @(tsee stat) and @(tsee stat-validp).
     Recall that @('x0') is always 0 and thus not explicitly modeled."))
  :list-type ubyte32-list
  :length 31
  :pred xregs32ip)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist-of-len memory32i
  :short "Fixtype of memories for the RV32I base."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a list of @($2^{32}$) unsigned 8-bit integers,
     according to @(tsee stat) and @(tsee stat-validp).
     Recall that we do not model restrictions on the address space yet."))
  :list-type ubyte8-list
  :length 4294967296 ; (expt 2 32)
  :pred memory32ip)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod stat32i
  :short "Fixtype of states for the RV32I base."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a specialization of @(tsee stat)
     according to @(tsee stat-validp)."))
  ((xregs xregs32i)
   (pc ubyte32)
   (memory memory32i)
   (error bool))
  :pred stat32ip

  ///

  (defrule len-of-stat32i->xregs
    (equal (len (stat32i->xregs stat))
           31))

  (defrule len-of-stat32i->memory
    (equal (len (stat32i->memory stat))
           4294967296)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define stat32i-from-stat ((stat stat-rv32i-p))
  :returns (stat32i stat32ip)
  :short "Convert from @(tsee stat-rv32i-p) to @(tsee stat32i)."
  (make-stat32i :xregs (stat->xregs stat)
                :pc (stat->pc stat)
                :memory (stat->memory stat)
                :error (stat->error stat))
  :guard-hints
  (("Goal"
    :in-theory (enable stat-rv32i-p
                       stat-validp
                       xregs32ip
                       acl2::ubyte32-listp-rewrite-unsigned-byte-listp
                       memory32ip
                       ubyte32p
                       (:e feat-rv32i-le)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define stat-from-stat32i ((stat32i stat32ip))
  :returns (stat stat-rv32i-p
                 :hints
                 (("Goal"
                   :in-theory
                   (enable stat-rv32i-p
                           stat-validp
                           acl2::unsigned-byte-listp-rewrite-ubyte32-listp
                           acl2::unsigned-byte-p-rewrite-ubyte32p
                           (:e feat-rv32i-le)))))
  :short "Convert from @(tsee stat32i) to @(tsee stat-rv32i-p)."
  (make-stat :xregs (stat32i->xregs stat32i)
             :pc (stat32i->pc stat32i)
             :memory (stat32i->memory stat32i)
             :error (stat32i->error stat32i)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection stat32i-iso
  :short "Isomorphism between @(tsee stat-rv32i-p) and @(tsee stat32i)."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @(tsee stat32i-from-stat) and @(tsee stat-from-stat32i) functions
     are the isomorphic conversions."))

  (acl2::defiso stat32i-iso
    stat-rv32i-p
    stat32ip
    stat32i-from-stat
    stat-from-stat32i
    :thm-names (:beta-of-alpha stat-from-stat32i-of-stat32i-from-stat
                :alpha-of-beta stat32i-from-stat-of-stat-from-stat32i
                :alpha-injective stat32i-from-stat-injective
                :beta-injective stat-from-stat32i-injective)
    :hints (:beta-of-alpha (("Goal" :in-theory (enable stat-from-stat32i
                                                       stat32i-from-stat
                                                       stat-rv32i-p
                                                       xregs32ip
                                                       memory32ip
                                                       (:e feat-rv32i-le))))
            :alpha-of-beta (("Goal" :in-theory (enable stat-from-stat32i
                                                       stat32i-from-stat))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection read32i-xreg-unsigned{0}
  :short "Partially evaluate @(tsee read-xreg-unsigned)
          for the RV32I base."
  :long
  (xdoc::topstring
   (xdoc::p
    "We pick @(tsee feat-rv32i-le),
     but we could have picked any of the variants for RV32I."))

  (apt::parteval read-xreg-unsigned
                 ((feat (feat-rv32i-le)))
                 :new-name read32i-xreg-unsigned{0}
                 :thm-enable nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection read32i-xreg-unsigned{1}
  :short "Simplify @(tsee read32i-xreg-unsigned{0}) after partial evaluation."
  :long
  (xdoc::topstring
   (xdoc::p
    "We assume the guard so that we can eliminate the fixers."))

  (apt::simplify read32i-xreg-unsigned{0}
    :new-name read32i-xreg-unsigned{1}
    :simplify-guard t
    :assumptions :guard
    :thm-enable nil
    :enable (unsigned-byte-p-32-of-nth-of-stat-rv32i->xregs
             (:e feat-rv32i-le))
    :disable (lnfix
              unsigned-byte-fix)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection read32i-xreg-unsigned{2}
  :short "Refine @(tsee read32i-xreg-unsigned{1})
          to use the isomorphic states @(tsee stat32i)."

  (apt::isodata read32i-xreg-unsigned{1}
                ((stat stat32i-iso))
                :undefined 0
                :new-name read32i-xreg-unsigned{2}
                :hints (("Goal" :in-theory (enable stat-rv32i-p
                                                   (:e feat-rv32i-le))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection read32i-xreg-unsigned
  :short "Simplify @(tsee read32i-xreg-unsigned{2})
          after the isomorphic state transformation."
  :long
  (xdoc::topstring
   (xdoc::p
    "We assume the guard so that we eliminate
     the outer @(tsee if) with @(tsee mbt) added by @(tsee apt::isodata).")
   (xdoc::p
    "We simplify the guard to eliminate @(tsee stat-validp) from it,
     which is implied by @(tsee stat32ip).")
   (xdoc::p
    "This is the final refinement for this function,
     so we use the name @('read32i-xreg-unsigned') without numeric index."))

  (apt::simplify read32i-xreg-unsigned{2}
    :new-name read32i-xreg-unsigned
    :assumptions :guard
    :simplify-guard t
    :thm-enable nil
    :enable (stat-from-stat32i
             stat-validp
             unsigned-byte-p-32-of-nth-of-stat-rv32i->xregs
             acl2::unsigned-byte-listp-rewrite-ubyte32-listp
             acl2::unsigned-byte-p-rewrite-ubyte32p))

  (defrule ubyte32p-of-read32i-xreg-unsigned
    (implies (and (natp reg)
                  (< reg 32))
             (ubyte32p (read32i-xreg-unsigned reg stat)))
    :enable (read32i-xreg-unsigned nfix)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled read-xreg-unsigned-to-read32i-xreg-unsigned
  :short "Rewriting of @(tsee read-xreg-unsigned)
          to @(tsee read32i-xreg-unsigned)."
  (implies (and (statp stat)
                (equal feat (feat-rv32i-le))
                (stat-validp stat feat)
                (natp reg)
                (< reg 32))
           (equal (read-xreg-unsigned reg stat feat)
                  (read32i-xreg-unsigned reg (stat32i-from-stat stat))))
  :enable (read-xreg-unsigned-becomes-read32i-xreg-unsigned{0}
           read32i-xreg-unsigned{0}-becomes-read32i-xreg-unsigned{1}
           read32i-xreg-unsigned{1}-to-read32i-xreg-unsigned{2}
           read32i-xreg-unsigned{2}-becomes-read32i-xreg-unsigned
           (:e feat-rv32i-le)
           stat-rv32i-p
           stat-from-stat32i-of-stat32i-from-stat))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection read32i-xreg-signed{0}
  :short "Partially evaluate @(tsee read-xreg-unsigned)
          for the RV32I base."
  :long
  (xdoc::topstring
   (xdoc::p
    "We pick @(tsee feat-rv32i-le),
     but we could have picked any of the variants for RV32I."))

  (apt::parteval read-xreg-signed
                 ((feat (feat-rv32i-le)))
                 :new-name read32i-xreg-signed{0}
                 :thm-enable nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection read32i-xreg-signed{1}
  :short "Simplify @(tsee read32i-xreg-signed{0}) after partial evaluation."
  :long
  (xdoc::topstring
   (xdoc::p
    "We assume the guard so that we can replace @('XLEN') with 32."))

  (apt::simplify read32i-xreg-signed{0}
    :new-name read32i-xreg-signed{1}
    :simplify-guard t
    :assumptions :guard
    :thm-enable nil
    :enable ((:e feat-rv32i-le))
    :disable (logext)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection read32i-xreg-signed{2}
  :short "Refine @(tsee read32i-xreg-signed{1})
          to use the isomorphic states @(tsee stat32i)."

  (apt::isodata read32i-xreg-signed{1}
                ((stat stat32i-iso))
                :undefined 0
                :new-name read32i-xreg-signed{2}
                :hints (("Goal" :in-theory (enable stat-rv32i-p
                                                   (:e feat-rv32i-le))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection read32i-xreg-signed{3}
  :short "Simplify the body of @(tsee read32i-xreg-signed{2})
          to call @(tsee read32i-xreg-unsigned)."
  :long
  (xdoc::topstring
   (xdoc::p
    "We use @(tsee read-xreg-unsigned-to-read32i-xreg-unsigned)
     to accomplish that rewriting.
     Note that this eliminates the isomorphic conversion."))

  (apt::simplify read32i-xreg-signed{2}
    :new-name read32i-xreg-signed{3}
    :assumptions :guard
    :thm-enable nil
    :enable (read-xreg-unsigned-to-read32i-xreg-unsigned
             stat32i-from-stat-of-stat-from-stat32i
             (:e feat-rv32i-le))
    :disable (logext)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection read32i-xreg-signed
  :short "Simplify the guard of @(tsee read32i-xreg-signed{3})
          to eliminate the isomorphic conversion."
  :long
  (xdoc::topstring
   (xdoc::p
    "We had to do this simplication separately from the previous one
     because the rules needed to do the rewritings interfere."))

  (apt::simplify read32i-xreg-signed{3}
    :new-name read32i-xreg-signed
    :assumptions :guard
    :simplify-guard t
    :simplify-body nil
    :thm-enable nil
    :enable (stat-from-stat32i
             stat-validp
             acl2::unsigned-byte-listp-rewrite-ubyte32-listp
             acl2::unsigned-byte-p-rewrite-ubyte32p)))
