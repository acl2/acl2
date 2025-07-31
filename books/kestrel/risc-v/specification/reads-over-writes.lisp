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

(include-book "states")

(local (include-book "../library-extensions/logops-theorems"))

(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "ihs/logops-lemmas" :dir :system))
(local (include-book "kestrel/fty/ubyte8-ihs-theorems" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The following should be generalized to simpler rules (there are patterns).

(local
 (encapsulate
   ()

   (local (include-book "arithmetic-5/top" :dir :system))

   (defruled ubyte8p-of-logtail-8-of-ubyte16
     (implies (ubyte16p x)
              (ubyte8p (logtail 8 x)))
     :enable (ubyte16p
              ubyte8p
              logtail))

   (defruled ubyte8p-of-logtail-24-of-ubyte32
     (implies (ubyte32p x)
              (ubyte8p (logtail 24 x)))
     :enable (ubyte32p
              ubyte8p
              logtail))

   (defruled ubyte8p-of-logtail-56-of-ubyte64
     (implies (ubyte64p x)
              (ubyte8p (logtail 56 x)))
     :enable (ubyte64p
              ubyte8p
              logtail))

   (defruled loghead-plus-c-differs
     (implies (and (integerp x)
                   (posp c)
                   (< c (expt 2 (nfix n))))
              (not (equal (loghead n (+ c x))
                          (loghead n x))))
     :enable loghead)

   (defruled loghead-plus-c-differs-from-plus-d
     (implies (and (integerp x)
                   (posp c)
                   (posp d)
                   (< c (expt 2 (nfix n)))
                   (< d (expt 2 (nfix n)))
                   (not (equal c d)))
              (not (equal (loghead n (+ c x))
                          (loghead n (+ d x)))))
     :enable loghead)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ reads-over-writes
  :parents (specification)
  :short "Read-over-write theorems."
  :long
  (xdoc::topstring
   (xdoc::p
    "We prove typical theorems that rewrite
     read operations on states applied to write operations on states.
     These are useful for validating the specification of the operations,
     as well as for reasoning."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection read-xreg-of-write-xreg-theorems
  :short "Theorems about reads of registers over writes of registers."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are all disabled by default
     because they introduce case splits.
     We provide a ruleset to enable all of them."))

  ;; read-xreg-...-of-write-xreg:

  (defruled read-xreg-unsigned-of-write-xreg
    (equal (read-xreg-unsigned reg1
                               (write-xreg reg2 val stat feat)
                               feat)
           (if (and (equal (nfix reg1) (nfix reg2))
                    (not (equal (nfix reg1) 0)))
               (loghead (feat->xlen feat) val)
             (read-xreg-unsigned reg1 stat feat)))
    :enable (read-xreg-unsigned
             write-xreg
             nfix))

  (defruled read-xreg-signed-of-write-xreg
    (equal (read-xreg-signed reg1
                             (write-xreg reg2 val stat feat)
                             feat)
           (if (and (equal (nfix reg1) (nfix reg2))
                    (not (equal (nfix reg1) 0)))
               (logext (feat->xlen feat) val)
             (read-xreg-signed reg1 stat feat)))
    :enable (read-xreg-signed
             read-xreg-unsigned-of-write-xreg))

  (defruled read-xreg-unsigned32-of-write-xreg
    (implies (feat-64p feat)
             (equal (read-xreg-unsigned32 reg1
                                          (write-xreg reg2 val stat feat)
                                          feat)
                    (if (and (equal (nfix reg1) (nfix reg2))
                             (not (equal (nfix reg1) 0)))
                        (loghead 32 val)
                      (read-xreg-unsigned32 reg1 stat feat))))
    :use (:instance lemma (val (ifix val)))
    :prep-lemmas
    ((defruled lemma
       (implies (and (feat-64p feat)
                     (integerp val))
                (equal (read-xreg-unsigned32 reg1
                                             (write-xreg reg2 val stat feat)
                                             feat)
                       (if (and (equal (nfix reg1) (nfix reg2))
                                (not (equal (nfix reg1) 0)))
                           (loghead 32 val)
                         (read-xreg-unsigned32 reg1 stat feat))))
       :enable (read-xreg-unsigned32
                read-xreg-unsigned-of-write-xreg))))

  (defruled read-xreg-signed32-of-write-xreg
    (implies (feat-64p feat)
             (equal (read-xreg-signed32 reg1
                                        (write-xreg reg2 val stat feat)
                                        feat)
                    (if (and (equal (nfix reg1) (nfix reg2))
                             (not (equal (nfix reg1) 0)))
                        (logext 32 val)
                      (read-xreg-signed32 reg1 stat feat))))
    :enable (read-xreg-signed32
             read-xreg-unsigned-of-write-xreg))

  ;; read-xreg-...-of-write-xreg-32:

  (defruled read-xreg-unsigned-of-write-xreg-32
    (implies (feat-64p feat)
             (equal (read-xreg-unsigned reg1
                                        (write-xreg-32 reg2 val stat feat)
                                        feat)
                    (if (and (equal (nfix reg1) (nfix reg2))
                             (not (equal (nfix reg1) 0)))
                        (loghead 64 (logext 32 val))
                      (read-xreg-unsigned reg1 stat feat))))
    :enable (write-xreg-32
             read-xreg-unsigned-of-write-xreg))

  (defruled read-xreg-signed-of-write-xreg-32
    (implies (feat-64p feat)
             (equal (read-xreg-signed reg1
                                      (write-xreg-32 reg2 val stat feat)
                                      feat)
                    (if (and (equal (nfix reg1) (nfix reg2))
                             (not (equal (nfix reg1) 0)))
                        (logext 32 val)
                      (read-xreg-signed reg1 stat feat))))
    :enable (write-xreg-32
             read-xreg-signed-of-write-xreg))

  (defruled read-xreg-unsigned32-of-write-xreg-32
    (implies (feat-64p feat)
             (equal (read-xreg-unsigned32 reg1
                                          (write-xreg-32 reg2 val stat feat)
                                          feat)
                    (if (and (equal (nfix reg1) (nfix reg2))
                             (not (equal (nfix reg1) 0)))
                        (loghead 32 val)
                      (read-xreg-unsigned32 reg1 stat feat))))
    :use (:instance lemma (val (ifix val)))
    :prep-lemmas
    ((defruled lemma
       (implies (and (feat-64p feat)
                     (integerp val))
                (equal (read-xreg-unsigned32 reg1
                                             (write-xreg-32 reg2 val stat feat)
                                             feat)
                       (if (and (equal (nfix reg1) (nfix reg2))
                                (not (equal (nfix reg1) 0)))
                           (loghead 32 val)
                         (read-xreg-unsigned32 reg1 stat feat))))
       :enable (write-xreg-32
                read-xreg-unsigned32-of-write-xreg))))

  (defruled read-xreg-signed32-of-write-xreg-32
    (implies (feat-64p feat)
             (equal (read-xreg-signed32 reg1
                                        (write-xreg-32 reg2 val stat feat)
                                        feat)
                    (if (and (equal (nfix reg1) (nfix reg2))
                             (not (equal (nfix reg1) 0)))
                        (logext 32 val)
                      (read-xreg-signed32 reg1 stat feat))))
    :enable (write-xreg-32
             read-xreg-signed32-of-write-xreg))

  ;; ruleset of the above rules:

  (def-ruleset read-xreg-of-write-xreg
    '(read-xreg-unsigned-of-write-xreg
      read-xreg-signed-of-write-xreg
      read-xreg-unsigned32-of-write-xreg
      read-xreg-signed32-of-write-xreg
      read-xreg-unsigned-of-write-xreg-32
      read-xreg-signed-of-write-xreg-32
      read-xreg-unsigned32-of-write-xreg-32
      read-xreg-signed32-of-write-xreg-32)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection read-xreg-of-write-pc-theorems
  :short "Theorems about reads of registers over writes of program counter."
  :long
  (xdoc::topstring
   (xdoc::p
    "The writes of program counter include
     not only @(tsee write-pc) but also @(tsee inc4-pc).")
   (xdoc::p
    "These theorems are all enabled by default
     because they always clearly simplify the term."))

  ;; read-xreg-...-of-write-pc:

  (defrule read-xreg-unsigned-of-write-pc
    (equal (read-xreg-unsigned reg (write-pc pc stat feat) feat)
           (read-xreg-unsigned reg stat feat))
    :enable (read-xreg-unsigned
             write-pc))

  (defrule read-xreg-signed-of-write-pc
    (equal (read-xreg-signed reg (write-pc pc stat feat) feat)
           (read-xreg-signed reg stat feat))
    :enable read-xreg-signed)

  (defrule read-xreg-unsigned32-of-write-pc
    (equal (read-xreg-unsigned32 reg (write-pc pc stat feat) feat)
           (read-xreg-unsigned32 reg stat feat))
    :enable read-xreg-unsigned32)

  (defrule read-xreg-signed32-of-write-pc
    (equal (read-xreg-signed32 reg (write-pc pc stat feat) feat)
           (read-xreg-signed32 reg stat feat))
    :enable read-xreg-signed32)

  ;; read-xreg-...-of-inc4-pc:

  (defrule read-xreg-unsigned-of-inc4-pc
    (equal (read-xreg-unsigned reg (inc4-pc stat feat) feat)
           (read-xreg-unsigned reg stat feat))
    :enable inc4-pc)

  (defrule read-xreg-signed-of-inc4-pc
    (equal (read-xreg-signed reg (inc4-pc stat feat) feat)
           (read-xreg-signed reg stat feat))
    :enable inc4-pc)

  (defrule read-xreg-unsigned32-of-inc4-pc
    (equal (read-xreg-unsigned32 reg (inc4-pc stat feat) feat)
           (read-xreg-unsigned32 reg stat feat))
    :enable inc4-pc)

  (defrule read-xreg-signed32-of-inc4-pc
    (equal (read-xreg-signed32 reg (inc4-pc stat feat) feat)
           (read-xreg-signed32 reg stat feat))
    :enable inc4-pc))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection read-xreg-of-write-memory-theorems
  :short "Theorems about reads of registers over writes of memory."
  :long
  (xdoc::topstring
   (xdoc::p
    "These theorems are all enabled by default
     because they always clearly simplify the term."))

  ;; read-xreg-...-of-write-memory-unsigned8:

  (defrule read-xreg-unsigned-of-write-memory-unsigned8
    (equal (read-xreg-unsigned reg
                               (write-memory-unsigned8 addr val stat feat)
                               feat)
           (read-xreg-unsigned reg stat feat))
    :enable (read-xreg-unsigned
             write-memory-unsigned8))

  (defrule read-xreg-signed-of-write-memory-unsigned8
    (equal (read-xreg-signed reg
                             (write-memory-unsigned8 addr val stat feat)
                             feat)
           (read-xreg-signed reg stat feat))
    :enable read-xreg-signed)

  (defrule read-xreg-unsigned32-of-write-memory-unsigned8
    (equal (read-xreg-unsigned32 reg
                                 (write-memory-unsigned8 addr val stat feat)
                                 feat)
           (read-xreg-unsigned32 reg stat feat))
    :enable read-xreg-unsigned32)

  (defrule read-xreg-signed32-of-write-memory-unsigned8
    (equal (read-xreg-signed32 reg
                               (write-memory-unsigned8 addr val stat feat)
                               feat)
           (read-xreg-signed32 reg stat feat))
    :enable read-xreg-signed32)

  ;; read-xreg-...-of-write-memory-unsigned16:

  (defrule read-xreg-unsigned-of-write-memory-unsigned16
    (equal (read-xreg-unsigned reg
                               (write-memory-unsigned16 addr val stat feat)
                               feat)
           (read-xreg-unsigned reg stat feat))
    :enable write-memory-unsigned16)

  (defrule read-xreg-signed-of-write-memory-unsigned16
    (equal (read-xreg-signed reg
                             (write-memory-unsigned16 addr val stat feat)
                             feat)
           (read-xreg-signed reg stat feat))
    :enable write-memory-unsigned16)

  (defrule read-xreg-unsigned32-of-write-memory-unsigned16
    (equal (read-xreg-unsigned32 reg
                                 (write-memory-unsigned16 addr val stat feat)
                                 feat)
           (read-xreg-unsigned32 reg stat feat))
    :enable write-memory-unsigned16)

  (defrule read-xreg-signed32-of-write-memory-unsigned16
    (equal (read-xreg-signed32 reg
                               (write-memory-unsigned16 addr val stat feat)
                               feat)
           (read-xreg-signed32 reg stat feat))
    :enable write-memory-unsigned16)

  ;; read-xreg-...-of-write-memory-unsigned32:

  (defrule read-xreg-unsigned-of-write-memory-unsigned32
    (equal (read-xreg-unsigned reg
                               (write-memory-unsigned32 addr val stat feat)
                               feat)
           (read-xreg-unsigned reg stat feat))
    :enable write-memory-unsigned32)

  (defrule read-xreg-signed-of-write-memory-unsigned32
    (equal (read-xreg-signed reg
                             (write-memory-unsigned32 addr val stat feat)
                             feat)
           (read-xreg-signed reg stat feat))
    :enable write-memory-unsigned32)

  (defrule read-xreg-unsigned32-of-write-memory-unsigned32
    (equal (read-xreg-unsigned32 reg
                                 (write-memory-unsigned32 addr val stat feat)
                                 feat)
           (read-xreg-unsigned32 reg stat feat))
    :enable write-memory-unsigned32)

  (defrule read-xreg-signed32-of-write-memory-unsigned32
    (equal (read-xreg-signed32 reg
                               (write-memory-unsigned32 addr val stat feat)
                               feat)
           (read-xreg-signed32 reg stat feat))
    :enable write-memory-unsigned32)

  ;; read-xreg-...-of-write-memory-unsigned64:

  (defrule read-xreg-unsigned-of-write-memory-unsigned64
    (equal (read-xreg-unsigned reg
                               (write-memory-unsigned64 addr val stat feat)
                               feat)
           (read-xreg-unsigned reg stat feat))
    :enable write-memory-unsigned64)

  (defrule read-xreg-signed-of-write-memory-unsigned64
    (equal (read-xreg-signed reg
                             (write-memory-unsigned64 addr val stat feat)
                             feat)
           (read-xreg-signed reg stat feat))
    :enable write-memory-unsigned64)

  (defrule read-xreg-unsigned32-of-write-memory-unsigned64
    (equal (read-xreg-unsigned32 reg
                                 (write-memory-unsigned64 addr val stat feat)
                                 feat)
           (read-xreg-unsigned32 reg stat feat))
    :enable write-memory-unsigned64)

  (defrule read-xreg-signed32-of-write-memory-unsigned64
    (equal (read-xreg-signed32 reg
                               (write-memory-unsigned64 addr val stat feat)
                               feat)
           (read-xreg-signed32 reg stat feat))
    :enable write-memory-unsigned64))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection read-pc-of-write-xreg-theorems
  :short "Theorems about reads of program counter over writes of registers."
  :long
  (xdoc::topstring
   (xdoc::p
    "These theorems are all enabled by default
     because they always clearly simplify the term."))

  (defrule read-pc-of-write-xreg
    (equal (read-pc (write-xreg reg val stat feat) feat)
           (read-pc stat feat))
    :enable (read-pc
             write-xreg))

  (defrule read-pc-of-write-xreg-32
    (equal (read-pc (write-xreg-32 reg val stat feat) feat)
           (read-pc stat feat))
    :enable write-xreg-32))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection read-pc-of-write-pc-theorems
  :short "Theorems about
          reads of program counter over writes of program counter."
  :long
  (xdoc::topstring
   (xdoc::p
    "The writes of program counter include
     not only @(tsee write-pc) but also @(tsee inc4-pc).")
   (xdoc::p
    "The first theorem is enabled by default
     because the right side seems clearly always simpler.
     The second theorem is disabled by default
     because the right side still involves a call of @(tsee read-pc)."))

  (defrule read-pc-of-write-pc
    (equal (read-pc (write-pc pc stat feat) feat)
           (loghead (feat->xlen feat) (nfix pc)))
    :enable (read-pc
             write-pc
             nfix))

  (defruled read-pc-of-inc4-pc
    (equal (read-pc (inc4-pc stat feat) feat)
           (loghead (feat->xlen feat) (+ 4 (read-pc stat feat))))
    :enable (inc4-pc
             nfix)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection read-pc-of-write-memory-theorems
  :short "Theorems about reads of program counter over writes of memory."
  :long
  (xdoc::topstring
   (xdoc::p
    "These theorems are all enabled by default
     because they always clearly simplify the term."))

  (defrule read-pc-of-write-memory-unsigned8
    (equal (read-pc (write-memory-unsigned8 addr val stat feat) feat)
           (read-pc stat feat))
    :enable (read-pc
             write-memory-unsigned8))

  (defrule read-pc-of-write-memory-unsigned16
    (equal (read-pc (write-memory-unsigned16 addr val stat feat) feat)
           (read-pc stat feat))
    :enable write-memory-unsigned16)

  (defrule read-pc-of-write-memory-unsigned32
    (equal (read-pc (write-memory-unsigned32 addr val stat feat) feat)
           (read-pc stat feat))
    :enable write-memory-unsigned32)

  (defrule read-pc-of-write-memory-unsigned64
    (equal (read-pc (write-memory-unsigned64 addr val stat feat) feat)
           (read-pc stat feat))
    :enable write-memory-unsigned64))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection read-memory-of-write-xreg-theorems
  :short "Theorems about reads of memory over writes of registers."
  :long
  (xdoc::topstring
   (xdoc::p
    "These theorems are all enabled by default
     because they always clearly simplify the term."))

  ;; read-memory-...-of-write-xreg:

  (defrule read-memory-unsigned8-of-write-xreg
    (equal (read-memory-unsigned8 addr (write-xreg reg val stat feat) feat)
           (read-memory-unsigned8 addr stat feat))
    :enable (read-memory-unsigned8
             write-xreg))

  (defrule read-memory-unsigned16-of-write-xreg
    (equal (read-memory-unsigned16 addr (write-xreg reg val stat feat) feat)
           (read-memory-unsigned16 addr stat feat))
    :enable read-memory-unsigned16)

  (defrule read-memory-unsigned32-of-write-xreg
    (equal (read-memory-unsigned32 addr (write-xreg reg val stat feat) feat)
           (read-memory-unsigned32 addr stat feat))
    :enable read-memory-unsigned32)

  (defrule read-memory-unsigned64-of-write-xreg
    (equal (read-memory-unsigned64 addr (write-xreg reg val stat feat) feat)
           (read-memory-unsigned64 addr stat feat))
    :enable read-memory-unsigned64)

  ;; read-memory-...-of-write-xreg-32:

  (defrule read-memory-unsigned8-of-write-xreg-32
    (equal (read-memory-unsigned8 addr (write-xreg-32 reg val stat feat) feat)
           (read-memory-unsigned8 addr stat feat))
    :enable (read-memory-unsigned8
             write-xreg-32))

  (defrule read-memory-unsigned16-of-write-xreg-32
    (equal (read-memory-unsigned16 addr (write-xreg-32 reg val stat feat) feat)
           (read-memory-unsigned16 addr stat feat))
    :enable read-memory-unsigned16)

  (defrule read-memory-unsigned32-of-write-xreg-32
    (equal (read-memory-unsigned32 addr (write-xreg-32 reg val stat feat) feat)
           (read-memory-unsigned32 addr stat feat))
    :enable read-memory-unsigned32)

  (defrule read-memory-unsigned64-of-write-xreg-32
    (equal (read-memory-unsigned64 addr (write-xreg-32 reg val stat feat) feat)
           (read-memory-unsigned64 addr stat feat))
    :enable read-memory-unsigned64))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection read-memory-of-write-pc-theorems
  :short "Theorems about reads of memory over writes of program counter."
  :long
  (xdoc::topstring
   (xdoc::p
    "The writes of program counter include
     not only @(tsee write-pc) but also @(tsee inc4-pc).")
   (xdoc::p
    "These theorems are all enabled by default
     because they always clearly simplify the term."))

  (defrule read-memory-unsigned8-of-write-pc
    (equal (read-memory-unsigned8 addr (write-pc pc stat feat) feat)
           (read-memory-unsigned8 addr stat feat))
    :enable (read-memory-unsigned8
             write-pc))

  (defrule read-memory-unsigned16-of-write-pc
    (equal (read-memory-unsigned16 addr (write-pc pc stat feat) feat)
           (read-memory-unsigned16 addr stat feat))
    :enable read-memory-unsigned16)

  (defrule read-memory-unsigned32-of-write-pc
    (equal (read-memory-unsigned32 addr (write-pc pc stat feat) feat)
           (read-memory-unsigned32 addr stat feat))
    :enable read-memory-unsigned32)

  (defrule read-memory-unsigned64-of-write-pc
    (equal (read-memory-unsigned64 addr (write-pc pc stat feat) feat)
           (read-memory-unsigned64 addr stat feat))
    :enable read-memory-unsigned64)

  (defrule read-memory-unsigned8-of-inc4-pc
    (equal (read-memory-unsigned8 addr (inc4-pc stat feat) feat)
           (read-memory-unsigned8 addr stat feat))
    :enable inc4-pc)

  (defrule read-memory-unsigned16-of-inc4-pc
    (equal (read-memory-unsigned16 addr (inc4-pc stat feat) feat)
           (read-memory-unsigned16 addr stat feat))
    :enable inc4-pc)

  (defrule read-memory-unsigned32-of-inc4-pc
    (equal (read-memory-unsigned32 addr (inc4-pc stat feat) feat)
           (read-memory-unsigned32 addr stat feat))
    :enable inc4-pc)

  (defrule read-memory-unsigned64-of-inc4-pc
    (equal (read-memory-unsigned64 addr (inc4-pc stat feat) feat)
           (read-memory-unsigned64 addr stat feat))
    :enable inc4-pc))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection read-memory-of-write-memory-theorems
  :short "Theorems about reads of memory over writes of memory."
  :long
  (xdoc::topstring
   (xdoc::p
    "The theorem involving a single byte has a simple form.
     Theorems involving multiple bytes have more complex forms,
     because addresses may be disjoint or they may partially or totally overlap.
     We add a few theorems for now, but we plan to add the remaining ones.")
   (xdoc::p
    "We provide a ruleset with these theorems."))

  (defruled read-memory-unsigned8-pf-write-memory-unsigned8
    (implies (stat-validp stat feat)
             (equal (read-memory-unsigned8 addr1
                                           (write-memory-unsigned8
                                            addr2 val stat feat)
                                           feat)
                    (if (equal (loghead (feat->xlen feat) addr1)
                               (loghead (feat->xlen feat) addr2))
                        (ubyte8-fix val)
                      (read-memory-unsigned8 addr1 stat feat))))
    :enable (read-memory-unsigned8
             write-memory-unsigned8
             max
             nfix))

  (defruled read-memory-unsigned8-of-write-memory-unsigned16
    (implies (stat-validp stat feat)
             (equal (read-memory-unsigned8 addr1
                                           (write-memory-unsigned16
                                            addr2 val stat feat)
                                           feat)
                    (cond ((equal (loghead (feat->xlen feat) addr1)
                                  (loghead (feat->xlen feat) addr2))
                           (cond ((feat-little-endianp feat)
                                  (part-select (ubyte16-fix val)
                                               :low 0 :high 7))
                                 ((feat-big-endianp feat)
                                  (part-select (ubyte16-fix val)
                                               :low 8 :high 15))))
                          ((equal (loghead (feat->xlen feat) addr1)
                                  (loghead (feat->xlen feat) (1+ (ifix addr2))))
                           (cond ((feat-little-endianp feat)
                                  (part-select (ubyte16-fix val)
                                               :low 8 :high 15))
                                 ((feat-big-endianp feat)
                                  (part-select (ubyte16-fix val)
                                               :low 0 :high 7))))
                          (t (read-memory-unsigned8 addr1 stat feat)))))
    :use (:instance lemma (addr2 (ifix addr2)))
    :prep-lemmas
    ((defruled lemma
       (implies (and (stat-validp stat feat)
                     (integerp addr2))
                (equal (read-memory-unsigned8 addr1
                                              (write-memory-unsigned16
                                               addr2 val stat feat)
                                              feat)
                       (cond ((equal (loghead (feat->xlen feat) addr1)
                                     (loghead (feat->xlen feat) addr2))
                              (cond ((feat-little-endianp feat)
                                     (part-select (ubyte16-fix val)
                                                  :low 0 :high 7))
                                    ((feat-big-endianp feat)
                                     (part-select (ubyte16-fix val)
                                                  :low 8 :high 15))))
                             ((equal (loghead (feat->xlen feat) addr1)
                                     (loghead (feat->xlen feat) (1+ addr2)))
                              (cond ((feat-little-endianp feat)
                                     (part-select (ubyte16-fix val)
                                                  :low 8 :high 15))
                                    ((feat-big-endianp feat)
                                     (part-select (ubyte16-fix val)
                                                  :low 0 :high 7))))
                             (t (read-memory-unsigned8 addr1 stat feat)))))
       :cases ((feat-32p feat))
       :enable (read-memory-unsigned8
                write-memory-unsigned8
                write-memory-unsigned16
                loghead-upper-bound
                loghead-plus-c-differs
                ubyte8p-of-logtail-8-of-ubyte16
                max))))

  (defruled read-memory-unsigned8-of-write-memory-unsigned32
    (implies (stat-validp stat feat)
             (equal (read-memory-unsigned8 addr1
                                           (write-memory-unsigned32
                                            addr2 val stat feat)
                                           feat)
                    (cond ((equal (loghead (feat->xlen feat) addr1)
                                  (loghead (feat->xlen feat) addr2))
                           (cond ((feat-little-endianp feat)
                                  (part-select (ubyte32-fix val)
                                               :low 0 :high 7))
                                 ((feat-big-endianp feat)
                                  (part-select (ubyte32-fix val)
                                               :low 24 :high 31))))
                          ((equal (loghead (feat->xlen feat) addr1)
                                  (loghead (feat->xlen feat)
                                           (+ 1 (ifix addr2))))
                           (cond ((feat-little-endianp feat)
                                  (part-select (ubyte32-fix val)
                                               :low 8 :high 15))
                                 ((feat-big-endianp feat)
                                  (part-select (ubyte32-fix val)
                                               :low 16 :high 23))))
                          ((equal (loghead (feat->xlen feat) addr1)
                                  (loghead (feat->xlen feat)
                                           (+ 2 (ifix addr2))))
                           (cond ((feat-little-endianp feat)
                                  (part-select (ubyte32-fix val)
                                               :low 16 :high 23))
                                 ((feat-big-endianp feat)
                                  (part-select (ubyte32-fix val)
                                               :low 8 :high 15))))
                          ((equal (loghead (feat->xlen feat) addr1)
                                  (loghead (feat->xlen feat)
                                           (+ 3 (ifix addr2))))
                           (cond ((feat-little-endianp feat)
                                  (part-select (ubyte32-fix val)
                                               :low 24 :high 31))
                                 ((feat-big-endianp feat)
                                  (part-select (ubyte32-fix val)
                                               :low 0 :high 7))))
                          (t (read-memory-unsigned8 addr1 stat feat)))))
    :use (:instance lemma (addr2 (ifix addr2)))
    :prep-lemmas
    ((defruled lemma
       (implies (and (stat-validp stat feat)
                     (integerp addr2))
                (equal (read-memory-unsigned8 addr1
                                              (write-memory-unsigned32
                                               addr2 val stat feat)
                                              feat)
                       (cond ((equal (loghead (feat->xlen feat) addr1)
                                     (loghead (feat->xlen feat) addr2))
                              (cond ((feat-little-endianp feat)
                                     (part-select (ubyte32-fix val)
                                                  :low 0 :high 7))
                                    ((feat-big-endianp feat)
                                     (part-select (ubyte32-fix val)
                                                  :low 24 :high 31))))
                             ((equal (loghead (feat->xlen feat) addr1)
                                     (loghead (feat->xlen feat) (+ 1 addr2)))
                              (cond ((feat-little-endianp feat)
                                     (part-select (ubyte32-fix val)
                                                  :low 8 :high 15))
                                    ((feat-big-endianp feat)
                                     (part-select (ubyte32-fix val)
                                                  :low 16 :high 23))))
                             ((equal (loghead (feat->xlen feat) addr1)
                                     (loghead (feat->xlen feat) (+ 2 addr2)))
                              (cond ((feat-little-endianp feat)
                                     (part-select (ubyte32-fix val)
                                                  :low 16 :high 23))
                                    ((feat-big-endianp feat)
                                     (part-select (ubyte32-fix val)
                                                  :low 8 :high 15))))
                             ((equal (loghead (feat->xlen feat) addr1)
                                     (loghead (feat->xlen feat) (+ 3 addr2)))
                              (cond ((feat-little-endianp feat)
                                     (part-select (ubyte32-fix val)
                                                  :low 24 :high 31))
                                    ((feat-big-endianp feat)
                                     (part-select (ubyte32-fix val)
                                                  :low 0 :high 7))))
                             (t (read-memory-unsigned8 addr1 stat feat)))))
       :cases ((feat-32p feat))
       :enable (read-memory-unsigned8
                write-memory-unsigned8
                write-memory-unsigned32
                loghead-upper-bound
                loghead-plus-c-differs
                loghead-plus-c-differs-from-plus-d
                ubyte8p-of-logtail-24-of-ubyte32
                max))))

  (defruled read-memory-unsigned8-of-write-memory-unsigned64
    (implies (and (stat-validp stat feat)
                  (integerp addr2))
             (equal (read-memory-unsigned8 addr1
                                           (write-memory-unsigned64
                                            addr2 val stat feat)
                                           feat)
                    (cond ((equal (loghead (feat->xlen feat) addr1)
                                  (loghead (feat->xlen feat) addr2))
                           (cond ((feat-little-endianp feat)
                                  (part-select (ubyte64-fix val)
                                               :low 0 :high 7))
                                 ((feat-big-endianp feat)
                                  (part-select (ubyte64-fix val)
                                               :low 56 :high 63))))
                          ((equal (loghead (feat->xlen feat) addr1)
                                  (loghead (feat->xlen feat) (+ 1 addr2)))
                           (cond ((feat-little-endianp feat)
                                  (part-select (ubyte64-fix val)
                                               :low 8 :high 15))
                                 ((feat-big-endianp feat)
                                  (part-select (ubyte64-fix val)
                                               :low 48 :high 55))))
                          ((equal (loghead (feat->xlen feat) addr1)
                                  (loghead (feat->xlen feat) (+ 2 addr2)))
                           (cond ((feat-little-endianp feat)
                                  (part-select (ubyte64-fix val)
                                               :low 16 :high 23))
                                 ((feat-big-endianp feat)
                                  (part-select (ubyte64-fix val)
                                               :low 40 :high 47))))
                          ((equal (loghead (feat->xlen feat) addr1)
                                  (loghead (feat->xlen feat) (+ 3 addr2)))
                           (cond ((feat-little-endianp feat)
                                  (part-select (ubyte64-fix val)
                                               :low 24 :high 31))
                                 ((feat-big-endianp feat)
                                  (part-select (ubyte64-fix val)
                                               :low 32 :high 39))))
                          ((equal (loghead (feat->xlen feat) addr1)
                                  (loghead (feat->xlen feat) (+ 4 addr2)))
                           (cond ((feat-little-endianp feat)
                                  (part-select (ubyte64-fix val)
                                               :low 32 :high 39))
                                 ((feat-big-endianp feat)
                                  (part-select (ubyte64-fix val)
                                               :low 24 :high 31))))
                          ((equal (loghead (feat->xlen feat) addr1)
                                  (loghead (feat->xlen feat) (+ 5 addr2)))
                           (cond ((feat-little-endianp feat)
                                  (part-select (ubyte64-fix val)
                                               :low 40 :high 47))
                                 ((feat-big-endianp feat)
                                  (part-select (ubyte64-fix val)
                                               :low 16 :high 23))))
                          ((equal (loghead (feat->xlen feat) addr1)
                                  (loghead (feat->xlen feat) (+ 6 addr2)))
                           (cond ((feat-little-endianp feat)
                                  (part-select (ubyte64-fix val)
                                               :low 48 :high 55))
                                 ((feat-big-endianp feat)
                                  (part-select (ubyte64-fix val)
                                               :low 8 :high 15))))
                          ((equal (loghead (feat->xlen feat) addr1)
                                  (loghead (feat->xlen feat) (+ 7 addr2)))
                           (cond ((feat-little-endianp feat)
                                  (part-select (ubyte64-fix val)
                                               :low 56 :high 63))
                                 ((feat-big-endianp feat)
                                  (part-select (ubyte64-fix val)
                                               :low 0 :high 7))))
                          (t (read-memory-unsigned8 addr1 stat feat)))))
    :enable (read-memory-unsigned8
             write-memory-unsigned8
             write-memory-unsigned64
             loghead-upper-bound
             loghead-plus-c-differs
             loghead-plus-c-differs-from-plus-d
             ubyte8p-of-logtail-56-of-ubyte64
             max)
    :cases ((feat-32p feat)))

  (def-ruleset read-memory-of-write-memory
    '(read-memory-unsigned8-pf-write-memory-unsigned8
      read-memory-unsigned8-of-write-memory-unsigned16
      read-memory-unsigned8-of-write-memory-unsigned32
      read-memory-unsigned8-of-write-memory-unsigned64)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection read-instruction-of-write-xreg-theorems
  :short "Theorems about reads of instructions over writes of registers."
  :long
  (xdoc::topstring
   (xdoc::p
    "These theorems are all enabled by default
     because they always clearly simplify the term."))

  (defrule read-instruction-of-write-xreg
    (equal (read-instruction addr (write-xreg reg val stat feat) feat)
           (read-instruction addr stat feat))
    :enable read-instruction)

  (defrule read-instruction-of-write-xreg-32
    (equal (read-instruction addr (write-xreg-32 reg val stat feat) feat)
           (read-instruction addr stat feat))
    :enable read-instruction))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection read-instruction-of-write-pc-theorems
  :short "Theorems about reads of instructions over writes of program counter."
  :long
  (xdoc::topstring
   (xdoc::p
    "The writes of program counter include
     not only @(tsee write-pc) but also @(tsee inc4-pc).")
   (xdoc::p
    "These theorems are all enabled by default
     because they always clearly simplify the term."))

  (defrule read-instruction-of-write-pc
    (equal (read-instruction addr (write-pc pc stat feat) feat)
           (read-instruction addr stat feat))
    :enable read-instruction)

  (defrule read-instruction-of-inc4-pc
    (equal (read-instruction addr (inc4-pc stat feat) feat)
           (read-instruction addr stat feat))
    :enable inc4-pc))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc read-instruction-of-write-memory-theorems
  :short "Theorems about reads of instructions over writes of memory."
  :long
  (xdoc::topstring
   (xdoc::p
    "Reads of instructions are really reads of memory.
     For now we do not provide any specific theorems, but we plan to.
     Since instructions consist of 4 bytes,
     the formulation of these theorems is somewhat complex,
     since the 4 bytes may be disjoint from the memory writes,
     or they may partially or completely overlap.")))
