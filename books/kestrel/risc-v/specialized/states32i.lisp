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

(include-book "kestrel/fty/deflist-of-len" :dir :system)
(include-book "std/util/defiso" :dir :system)

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

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
    :enable stat-validp)

  (defruled stat-rv32i-p-alt-def-m-le
    (equal (stat-rv32i-p x)
           (and (statp x)
                (stat-validp x (feat-rv32im-le))))
    :enable stat-validp)

  (defruled stat-rv32i-p-alt-def-m-be
    (equal (stat-rv32i-p x)
           (and (statp x)
                (stat-validp x (feat-rv32im-be))))
    :enable stat-validp))

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
  :pred stat32ip)

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
                       ubyte32p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define stat-from-stat32i ((stat32i stat32ip))
  :returns (stat stat-rv32i-p
                 :hints
                 (("Goal"
                   :in-theory
                   (enable stat-rv32i-p
                           stat-validp
                           acl2::unsigned-byte-listp-rewrite-ubyte32-listp
                           acl2::unsigned-byte-p-rewrite-ubyte32p))))
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
                                                       memory32ip)))
            :alpha-of-beta (("Goal" :in-theory (enable stat-from-stat32i
                                                       stat32i-from-stat))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; TODO: specialize and refine operations on states
