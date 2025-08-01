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

(include-book "../specification/states")

(include-book "std/util/defiso" :dir :system)

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ state-stobj
  :parents (optimized)
  :short "Refinement of the state to a stobj."
  :long
  (xdoc::topstring
   (xdoc::p
    "We refine the type @(tsee stat) of states to a stobj
     straightforwardly derived from the definition of @(tsee stat).
     This is not the most efficient refinement of the states,
     but it is a simple one to explore at the beginning;
     we will explore more complex and efficient stobjs later.")
   (xdoc::p
    "We introduce the stobj,
     and we define an isomorphism
     between the stobj type and the @(tsee stat) type.
     Then we refine the rest of the model to use the stobj representation;
     this is work in progress."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection stat1
  :short "State stobj."
  :long
  (xdoc::topstring
   (xdoc::p
    "This could be probably automatically generated
     from the @(tsee fty::defprod) that defines @(tsee stat).")
   (xdoc::p
    "The unconstrained @('xregs') and @('pc') of @('stat')
     are turned into unconstrained scalar fields of the stobj.
     The @('memory') list of bytes of @('stat')
     is turned into a resizable array of bytes in the stobj,
     initially of length 0 (the initial length does not matter here).
     The @('error') boolean of @('stat')
     is turned into a boolean field in the stobj.")
   (xdoc::p
    "We rename and disable the generated stobj functions.")
   (xdoc::p
    "We introduce a non-executable function
     to retrieve the whole memory array.
     This cannot be executable, because it violates stobj usage rules.")
   (xdoc::p
    "We introduce a function to build a stobj value
     from the values of its fields.
     The values it returns are unrelated to the live stobj.")
   (xdoc::p
    "We also introduce some equivalences between
     recognizers of stobj fields and recognizers of @(tsee stat) field types."))

  ;; stobj definition:

  (defstobj stat1
    (xregs)
    (pc)
    (memory :type (array (unsigned-byte 8) (0)) :initially 0 :resizable t)
    (error :type (satisfies booleanp))
    :renaming (;; field recognizers:
               (xregsp stat1-xregs-p)
               (acl2::pcp stat1-pc-p)
               (memoryp stat1-memory-p)
               (errorp stat1-error-p)
               ;; field readers:
               (xregs stat1->xregs)
               (acl2::pc stat1->pc)
               (memory-length stat1->memory-size)
               (memoryi stat1->memory-byte)
               (error stat1->error)
               ;; field writers:
               (update-xregs update-stat1->xregs)
               (acl2::update-pc update-stat1->pc)
               (resize-memory update-stat1->memory-size)
               (update-memoryi update-stat1->memory-byte)
               (update-error update-stat1->error)))

  (in-theory (disable stat1p
                      stat1-xregs-p
                      stat1-pc-p
                      stat1-memory-p
                      stat1-error-p
                      stat1->xregs
                      stat1->pc
                      stat1->memory-size
                      stat1->memory-byte
                      stat1->error
                      update-stat1->xregs
                      update-stat1->pc
                      update-stat1->memory-size
                      update-stat1->memory-byte
                      update-stat1->error))

  ;; auxiliary functions:

  (define stat1->memory ((stat1 stat1p))
    :returns (memory stat1-memory-p
                     :hyp (stat1p stat1)
                     :hints (("Goal" :in-theory (enable stat1p))))
    (nth 2 stat1)
    :guard-hints (("Goal" :in-theory (enable stat1p)))
    :non-executable t)

  (define make-stat1 ((xregs stat1-xregs-p)
                      (pc stat1-pc-p)
                      (memory stat1-memory-p)
                      (error stat1-error-p))
    :returns (stat1 stat1p
                    :hyp :guard
                    :hints (("Goal" :in-theory (enable stat1p length len))))
    (list xregs pc memory error))

  ;; equivalences for memory field recognizers:

  (defruled stat1-memory-p-to-ubyte8-listp
    (equal (stat1-memory-p x)
           (ubyte8-listp x))
    :induct t
    :enable (stat1-memory-p ubyte8-listp ubyte8p))

  (defruled ubyte8-listp-to-stat1-memory-p
    (equal (ubyte8-listp x)
           (stat1-memory-p x))
    :enable stat1-memory-p-to-ubyte8-listp)

  (theory-invariant (incompatible (:rewrite stat1-memory-p-to-ubyte8-listp)
                                  (:rewrite ubyte8-listp-to-stat1-memory-p)))

  ;; equivalences for error field recognizers:

  (defruled stat1-error-p-to-booleanp
    (equal (stat1-error-p x)
           (booleanp x))
    :enable stat1-error-p)

  (defruled booleanp-to-stat1-error-p
    (equal (booleanp x)
           (stat1-error-p x))
    :enable stat1-error-p-to-booleanp)

  (theory-invariant (incompatible (:rewrite stat1-error-p-to-booleanp)
                                  (:rewrite booleanp-to-stat1-error-p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define stat1-from-stat ((stat statp))
  :returns (stat1 stat1p
                  :hints
                  (("Goal"
                    :in-theory (enable stat1-error-p
                                       stat1-memory-p-to-ubyte8-listp))))
  :short "Turn a @(tsee stat) value into a @(tsee stat1) value."
  :long
  (xdoc::topstring
   (xdoc::p
    "A transformation that generates the stobj definition from @(tsee stat)
     could also generate this conversion function.")
   (xdoc::p
    "This is executable,
     but the values it returns are unrelated to the live stobj."))
  (make-stat1 (stat->xregs stat)
              (stat->pc stat)
              (stat->memory stat)
              (stat->error stat))
  :guard-hints (("Goal" :in-theory (enable stat1-memory-p-to-ubyte8-listp)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define stat-from-stat1 ((stat1 stat1p))
  :returns (stat statp)
  :short "Turn a @(tsee stat1) value into a @(tsee stat) value."
  :long
  (xdoc::topstring
   (xdoc::p
    "A transformation that generates the stobj definition from @(tsee stat)
     could also generate this conversion function.")
   (xdoc::p
    "This is not quite executable,
     because it calls the non-executable @('stat1->memory')."))
  (make-stat :xregs (stat1->xregs stat1)
             :pc (stat1->pc stat1)
             :memory (stat1->memory stat1)
             :error (stat1->error stat1))
  :guard-hints (("Goal" :in-theory (enable ubyte8-listp-to-stat1-memory-p
                                           stat1-error-p-to-booleanp
                                           stat1p
                                           stat1->error))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection stat1-iso
  :short "Isomorphism between @(tsee stat) and @(tsee stat1)."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @(tsee stat1-from-stat) and @(tsee stat-from-stat1) functions
     are the isomorphic conversions.")
   (xdoc::p
    "We prove a local lemma to prove @('stat1-from-stat-of-stat-from-stat1')."))

  (defrulel lemma
    (implies (and (true-listp x)
                  (equal (len x) 4)
                  (equal (nth 0 x) a)
                  (equal (nth 1 x) b)
                  (equal (nth 2 x) c)
                  (equal (nth 3 x) d))
             (equal (list a b c d) x))
    :prep-books ((include-book "std/lists/len" :dir :system)
                 (include-book "arithmetic/top" :dir :system))
    :prep-lemmas
    ((defrule lemma-lemma
       (equal (equal (cons a b) x)
              (and (consp x)
                   (equal a (car x))
                   (equal b (cdr x)))))))

  (acl2::defiso stat-stat1-iso
    statp
    stat1p
    stat1-from-stat
    stat-from-stat1
    :thm-names (:beta-of-alpha stat-from-stat1-of-stat1-from-stat
                :alpha-of-beta stat1-from-stat-of-stat-from-stat1
                :alpha-injective stat1-from-stat-injective
                :beta-injective stat-from-stat1-injective)
    :hints (:beta-of-alpha (("Goal"
                             :in-theory (enable stat1-from-stat
                                                stat-from-stat1
                                                make-stat1
                                                stat1->xregs
                                                stat1->pc
                                                stat1->memory
                                                stat1->error)))
            :alpha-of-beta (("Goal"
                             :in-theory (enable stat-from-stat1
                                                stat1-from-stat
                                                make-stat1
                                                stat1->xregs
                                                stat1->pc
                                                stat1->memory
                                                stat1->error
                                                stat1p
                                                length
                                                len
                                                ubyte8-listp-to-stat1-memory-p
                                                booleanp-to-stat1-error-p))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Given a DEFISO, we would like to use APT's ISODATA
; to refine the operations on states to operate on the stobj.
; But currently ISODATA does not support stobjs;
; so for now we manually simulate the desired effect of ISODATA.

(define stat1-validp (stat1 feat)
  :guard (and (stat1p stat1)
              (b* ((STAT (stat-from-stat1 stat1)))
                (AND (STATP STAT) (FEATP FEAT))))
  (and (mbt (stat1p stat1))
       (b* ((STAT (stat-from-stat1 stat1)))
         (LET* ((STAT.XREGS (STAT->XREGS STAT))
                (STAT.PC (STAT->PC STAT))
                (STAT.MEMORY (STAT->MEMORY STAT))
                (XLEN (FEAT->XLEN FEAT))
                (XNUM (FEAT->XNUM FEAT)))
               (AND (UNSIGNED-BYTE-LISTP XLEN STAT.XREGS)
                    (EQUAL (LEN STAT.XREGS) (+ -1 XNUM))
                    (UNSIGNED-BYTE-P XLEN STAT.PC)
                    (EQUAL (LEN STAT.MEMORY)
                           (EXPT 2 XLEN)))))))

(define read1-xreg-unsigned (reg stat1 feat)
  :guard (and (stat1p stat1)
              (b* ((STAT (stat-from-stat1 stat1)))
                (AND (NATP REG)
                     (STATP STAT)
                     (FEATP FEAT)
                     (STAT-VALIDP STAT FEAT)
                     (< (LNFIX REG) (FEAT->XNUM FEAT)))))
  (if (mbt (stat1p stat1))
      (b* ((STAT (stat-from-stat1 stat1)))
        (LET* ((REG (LNFIX REG)))
              (IF (= REG 0)
                  0
                  (UNSIGNED-BYTE-FIX (FEAT->XLEN FEAT)
                                     (NTH (+ -1 REG)
                                          (STAT->XREGS STAT))))))
    0)
  :guard-hints (("Goal" :in-theory (enable nfix))))

(define read1-xreg-signed (reg stat1 feat)
  :guard (and (stat1p stat1)
              (b* ((STAT (stat-from-stat1 stat1)))
                (AND (NATP REG)
                     (STATP STAT)
                     (FEATP FEAT)
                     (STAT-VALIDP STAT FEAT)
                     (< (LNFIX REG) (FEAT->XNUM FEAT)))))
  (if (mbt (stat1p stat1))
      (b* ((STAT (stat-from-stat1 stat1)))
        (LOGEXT (FEAT->XLEN FEAT)
                (READ-XREG-UNSIGNED REG STAT FEAT)))
    0))

(define read1-xreg-unsigned32 (reg stat1 feat)
  :guard (and (stat1p stat1)
              (b* ((STAT (stat-from-stat1 stat1)))
                (AND (NATP REG)
                     (STATP STAT)
                     (FEATP FEAT)
                     (FEAT-64P FEAT)
                     (STAT-VALIDP STAT FEAT)
                     (< (LNFIX REG) (FEAT->XNUM FEAT)))))
  (if (mbt (stat1p stat1))
      (b* ((STAT (stat-from-stat1 stat1)))
        (LOGHEAD 32 (READ-XREG-UNSIGNED REG STAT FEAT)))
    0))

(define read1-xreg-signed32 (reg stat1 feat)
  :guard (and (stat1p stat1)
              (b* ((STAT (stat-from-stat1 stat1)))
                (AND (NATP REG)
                     (STATP STAT)
                     (FEATP FEAT)
                     (FEAT-64P FEAT)
                     (STAT-VALIDP STAT FEAT)
                     (< (LNFIX REG) (FEAT->XNUM FEAT)))))
  (if (mbt (stat1p stat1))
      (b* ((STAT (stat-from-stat1 stat1)))
        (LOGEXT 32 (READ-XREG-UNSIGNED REG STAT FEAT)))
    0))

(define write1-xreg (reg val stat1 feat)
  :guard (and (stat1p stat1)
              (b* ((STAT (stat-from-stat1 stat1)))
                (AND (NATP REG)
                     (INTEGERP VAL)
                     (STATP STAT)
                     (FEATP FEAT)
                     (STAT-VALIDP STAT FEAT)
                     (< (LNFIX REG) (FEAT->XNUM FEAT)))))
  (if (mbt (stat1p stat1))
      (stat1-from-stat
       (b* ((STAT (stat-from-stat1 stat1)))
         (LET* ((REG (LNFIX REG)))
               (IF (= REG 0)
                   (STAT-FIX STAT)
                   (LET ((CHANGE-STAT STAT)
                         (STAT->XREGS (UPDATE-NTH (+ -1 REG)
                                                  (LOGHEAD (FEAT->XLEN FEAT) VAL)
                                                  (STAT->XREGS STAT))))
                        (STAT STAT->XREGS
                              (STAT->PC CHANGE-STAT)
                              (STAT->MEMORY CHANGE-STAT)
                              (STAT->ERROR CHANGE-STAT)))))))
    stat1)
  :non-executable t)

(define write1-xreg-32 (reg val stat1 feat)
  :guard (and (stat1p stat1)
              (b* ((STAT (stat-from-stat1 stat1)))
                (AND (NATP REG)
                     (INTEGERP VAL)
                     (STATP STAT)
                     (FEATP FEAT)
                     (FEAT-64P FEAT)
                     (STAT-VALIDP STAT FEAT)
                     (< (LNFIX REG) (FEAT->XNUM FEAT)))))
  (if (mbt (stat1p stat1))
      (stat1-from-stat
       (b* ((STAT (stat-from-stat1 stat1)))
         (WRITE-XREG REG (LOGEXT 32 VAL)
                     STAT FEAT)))
    stat1)
  :non-executable t
  :guard-hints (("Goal" :in-theory (disable logext))))

(define read1-pc (stat1 feat)
  :guard (and (stat1p stat1)
              (b* ((STAT (stat-from-stat1 stat1)))
                (AND (STATP STAT)
                     (FEATP FEAT)
                     (STAT-VALIDP STAT FEAT))))
  (if (mbt (stat1p stat1))
      (b* ((STAT (stat-from-stat1 stat1)))
        (UNSIGNED-BYTE-FIX (FEAT->XLEN FEAT)
                           (STAT->PC STAT)))
    0))

(define write1-pc (pc stat1 feat)
  :guard (and (stat1p stat1)
              (b* ((STAT (stat-from-stat1 stat1)))
                (AND (NATP PC)
                     (STATP STAT)
                     (FEATP FEAT)
                     (STAT-VALIDP STAT FEAT))))
  (if (mbt (stat1p stat1))
      (stat1-from-stat
       (b* ((STAT (stat-from-stat1 stat1)))
         (LET ((CHANGE-STAT STAT)
               (STAT->PC (LOGHEAD (FEAT->XLEN FEAT) (LNFIX PC))))
              (STAT (STAT->XREGS CHANGE-STAT)
                    STAT->PC (STAT->MEMORY CHANGE-STAT)
                    (STAT->ERROR CHANGE-STAT)))))
    stat1)
  :non-executable t)

(define inc1-4-pc (stat1 feat)
  :guard (and (stat1p stat1)
              (b* ((STAT (stat-from-stat1 stat1)))
                (AND (STATP STAT)
                     (FEATP FEAT)
                     (STAT-VALIDP STAT FEAT))))
  (if (mbt (stat1p stat1))
      (stat1-from-stat
       (b* ((STAT (stat-from-stat1 stat1)))
         (WRITE-PC (+ (READ-PC STAT FEAT) 4)
                   STAT FEAT)))
    stat1)
  :non-executable t)

(define read1-memory-unsigned8 (addr stat1 feat)
  :guard (and (stat1p stat1)
              (b* ((STAT (stat-from-stat1 stat1)))
                (AND (INTEGERP ADDR)
                     (STATP STAT)
                     (FEATP FEAT)
                     (STAT-VALIDP STAT FEAT))))
  (if (mbt (stat1p stat1))
      (b* ((STAT (stat-from-stat1 stat1)))
        (LET* ((ADDR (LOGHEAD (FEAT->XLEN FEAT) ADDR)))
              (UBYTE8-FIX (NTH ADDR (STAT->MEMORY STAT)))))
    0)
  :guard-hints (("Goal"
                 :use (:instance (:guard-theorem read-memory-unsigned8)
                                 (stat (stat-from-stat1 stat1))))))

(define read1-memory-unsigned16 (addr stat1 feat)
  :guard (and (stat1p stat1)
              (b* ((STAT (stat-from-stat1 stat1)))
                (AND (INTEGERP ADDR)
                     (STATP STAT)
                     (FEATP FEAT)
                     (STAT-VALIDP STAT FEAT))))
  (if (mbt (stat1p stat1))
      (b* ((STAT (stat-from-stat1 stat1)))
        (LET* ((B0 (READ-MEMORY-UNSIGNED8 ADDR STAT FEAT))
               (B1 (READ-MEMORY-UNSIGNED8 (+ (LIFIX ADDR) 1)
                                          STAT FEAT)))
              (COND ((FEAT-LITTLE-ENDIANP FEAT)
                     (LOGAPP 8 B0 (LOGAPP 8 B1 0)))
                    ((FEAT-BIG-ENDIANP FEAT)
                     (LOGAPP 8 B1 (LOGAPP 8 B0 0)))
                    (T (ACL2::IMPOSSIBLE-FN)))))
    0)
  :guard-hints (("Goal"
                 :use (:instance (:guard-theorem read-memory-unsigned16)
                                 (stat (stat-from-stat1 stat1))))))

(define read1-memory-unsigned32 (addr stat1 feat)
  :guard (and (stat1p stat1)
              (b* ((STAT (stat-from-stat1 stat1)))
                (AND (INTEGERP ADDR)
                     (STATP STAT)
                     (FEATP FEAT)
                     (STAT-VALIDP STAT FEAT))))
  (if (mbt (stat1p stat1))
      (b* ((STAT (stat-from-stat1 stat1)))
        (LET* ((B0 (READ-MEMORY-UNSIGNED8 ADDR STAT FEAT))
               (B1 (READ-MEMORY-UNSIGNED8 (+ (LIFIX ADDR) 1)
                                          STAT FEAT))
               (B2 (READ-MEMORY-UNSIGNED8 (+ (LIFIX ADDR) 2)
                                          STAT FEAT))
               (B3 (READ-MEMORY-UNSIGNED8 (+ (LIFIX ADDR) 3)
                                          STAT FEAT)))
              (COND ((FEAT-LITTLE-ENDIANP FEAT)
                     (LOGAPP 8 B0
                             (LOGAPP 8 B1 (LOGAPP 8 B2 (LOGAPP 8 B3 0)))))
                    ((FEAT-BIG-ENDIANP FEAT)
                     (LOGAPP 8 B3
                             (LOGAPP 8 B2 (LOGAPP 8 B1 (LOGAPP 8 B0 0)))))
                    (T (ACL2::IMPOSSIBLE-FN)))))
    0)
  :guard-hints (("Goal"
                 :use (:instance (:guard-theorem read-memory-unsigned32)
                                 (stat (stat-from-stat1 stat1))))))

(define read1-memory-unsigned64 (addr stat1 feat)
  :guard (and (stat1p stat1)
              (b* ((STAT (stat-from-stat1 stat1)))
                (AND (INTEGERP ADDR)
                     (STATP STAT)
                     (FEATP FEAT)
                     (STAT-VALIDP STAT FEAT))))
  (if (mbt (stat1p stat1))
      (b* ((STAT (stat-from-stat1 stat1)))
        (LET* ((B0 (READ-MEMORY-UNSIGNED8 ADDR STAT FEAT))
               (B1 (READ-MEMORY-UNSIGNED8 (+ (LIFIX ADDR) 1)
                                          STAT FEAT))
               (B2 (READ-MEMORY-UNSIGNED8 (+ (LIFIX ADDR) 2)
                                          STAT FEAT))
               (B3 (READ-MEMORY-UNSIGNED8 (+ (LIFIX ADDR) 3)
                                          STAT FEAT))
               (B4 (READ-MEMORY-UNSIGNED8 (+ (LIFIX ADDR) 4)
                                          STAT FEAT))
               (B5 (READ-MEMORY-UNSIGNED8 (+ (LIFIX ADDR) 5)
                                          STAT FEAT))
               (B6 (READ-MEMORY-UNSIGNED8 (+ (LIFIX ADDR) 6)
                                          STAT FEAT))
               (B7 (READ-MEMORY-UNSIGNED8 (+ (LIFIX ADDR) 7)
                                          STAT FEAT)))
              (COND
               ((FEAT-LITTLE-ENDIANP FEAT)
                (LOGAPP
                 8 B0
                 (LOGAPP
                  8 B1
                  (LOGAPP 8 B2
                          (LOGAPP 8 B3
                                  (LOGAPP 8 B4
                                          (LOGAPP 8
                                                  B5 (LOGAPP 8 B6
                                                             (LOGAPP 8 B7 0)))))))))
               ((FEAT-BIG-ENDIANP FEAT)
                (LOGAPP
                 8 B7
                 (LOGAPP
                  8 B6
                  (LOGAPP 8 B5
                          (LOGAPP 8 B4
                                  (LOGAPP 8 B3
                                          (LOGAPP 8
                                                  B2 (LOGAPP 8 B1
                                                             (LOGAPP 8 B0 0)))))))))
               (T (ACL2::IMPOSSIBLE-FN)))))
    0)
  :guard-hints (("Goal"
                 :use (:instance (:guard-theorem read-memory-unsigned64)
                                 (stat (stat-from-stat1 stat1))))))

(define write1-memory-unsigned8 (addr val stat1 feat)
  :guard (and (stat1p stat1)
              (b* ((STAT (stat-from-stat1 stat1)))
                (AND (INTEGERP ADDR)
                     (UBYTE8P VAL)
                     (STATP STAT)
                     (FEATP FEAT)
                     (STAT-VALIDP STAT FEAT))))
  (if (mbt (stat1p stat1))
      (stat1-from-stat
       (b* ((STAT (stat-from-stat1 stat1)))
         (LET* ((ADDR (LOGHEAD (FEAT->XLEN FEAT) ADDR)))
               (LET ((CHANGE-STAT STAT)
                     (STAT->MEMORY (UPDATE-NTH ADDR (UBYTE8-FIX VAL)
                                               (STAT->MEMORY STAT))))
                    (STAT (STAT->XREGS CHANGE-STAT)
                          (STAT->PC CHANGE-STAT)
                          STAT->MEMORY
                          (STAT->ERROR CHANGE-STAT))))))
    stat1)
  :non-executable t
  :guard-hints (("Goal"
                 :use (:instance (:guard-theorem write-memory-unsigned8)
                                 (stat (stat-from-stat1 stat1))))))

(define write1-memory-unsigned16 (addr val stat1 feat)
  :guard (and (stat1p stat1)
              (b* ((STAT (stat-from-stat1 stat1)))
                (AND (INTEGERP ADDR)
                     (UBYTE16P VAL)
                     (STATP STAT)
                     (FEATP FEAT)
                     (STAT-VALIDP STAT FEAT))))
  (if (mbt (stat1p stat1))
      (stat1-from-stat
       (b* ((STAT (stat-from-stat1 stat1)))
         (LET* ((VAL (UBYTE16-FIX VAL))
                (B0 (BITOPS::PART-SELECT-WIDTH-LOW VAL 8 0))
                (B1 (BITOPS::PART-SELECT-WIDTH-LOW VAL 8 8)))
               (MV-LET (1ST-BYTE 2ND-BYTE)
                 (IF (FEAT-LITTLE-ENDIANP FEAT)
                     (MV B0 B1)
                     (MV B1 B0))
                 (LET* ((STAT (WRITE-MEMORY-UNSIGNED8 ADDR 1ST-BYTE STAT FEAT))
                        (STAT (WRITE-MEMORY-UNSIGNED8 (+ (LIFIX ADDR) 1)
                                                      2ND-BYTE STAT FEAT)))
                       STAT)))))
    stat1)
  :non-executable t
  :guard-hints (("Goal"
                 :use (:instance (:guard-theorem write-memory-unsigned16)
                                 (stat (stat-from-stat1 stat1))))))

(define write1-memory-unsigned32 (addr val stat1 feat)
  :guard (and (stat1p stat1)
              (b* ((STAT (stat-from-stat1 stat1)))
                (AND (INTEGERP ADDR)
                     (UBYTE32P VAL)
                     (STATP STAT)
                     (FEATP FEAT)
                     (STAT-VALIDP STAT FEAT))))
  (if (mbt (stat1p stat1))
      (stat1-from-stat
       (b* ((STAT (stat-from-stat1 stat1)))
         (LET* ((VAL (UBYTE32-FIX VAL))
                (B0 (BITOPS::PART-SELECT-WIDTH-LOW VAL 8 0))
                (B1 (BITOPS::PART-SELECT-WIDTH-LOW VAL 8 8))
                (B2 (BITOPS::PART-SELECT-WIDTH-LOW VAL 8 16))
                (B3 (BITOPS::PART-SELECT-WIDTH-LOW VAL 8 24)))
               (MV-LET (1ST-BYTE 2ND-BYTE 3RD-BYTE 4TH-BYTE)
                 (IF (FEAT-LITTLE-ENDIANP FEAT)
                     (MV B0 B1 B2 B3)
                     (MV B3 B2 B1 B0))
                 (LET* ((STAT (WRITE-MEMORY-UNSIGNED8 ADDR 1ST-BYTE STAT FEAT))
                        (STAT (WRITE-MEMORY-UNSIGNED8 (+ (LIFIX ADDR) 1)
                                                      2ND-BYTE STAT FEAT))
                        (STAT (WRITE-MEMORY-UNSIGNED8 (+ (LIFIX ADDR) 2)
                                                      3RD-BYTE STAT FEAT))
                        (STAT (WRITE-MEMORY-UNSIGNED8 (+ (LIFIX ADDR) 3)
                                                      4TH-BYTE STAT FEAT)))
                       STAT)))))
    stat1)
  :non-executable t
  :guard-hints (("Goal"
                 :use (:instance (:guard-theorem write-memory-unsigned32)
                                 (stat (stat-from-stat1 stat1))))))

(define write1-memory-unsigned64 (addr val stat1 feat)
  :guard (and (stat1p stat1)
              (b* ((STAT (stat-from-stat1 stat1)))
                (AND (INTEGERP ADDR)
                     (UBYTE64P VAL)
                     (STATP STAT)
                     (FEATP FEAT)
                     (STAT-VALIDP STAT FEAT))))
  (if (mbt (stat1p stat1))
      (stat1-from-stat
       (b* ((STAT (stat-from-stat1 stat1)))
         (LET* ((VAL (UBYTE64-FIX VAL))
                (B0 (BITOPS::PART-SELECT-WIDTH-LOW VAL 8 0))
                (B1 (BITOPS::PART-SELECT-WIDTH-LOW VAL 8 8))
                (B2 (BITOPS::PART-SELECT-WIDTH-LOW VAL 8 16))
                (B3 (BITOPS::PART-SELECT-WIDTH-LOW VAL 8 24))
                (B4 (BITOPS::PART-SELECT-WIDTH-LOW VAL 8 32))
                (B5 (BITOPS::PART-SELECT-WIDTH-LOW VAL 8 40))
                (B6 (BITOPS::PART-SELECT-WIDTH-LOW VAL 8 48))
                (B7 (BITOPS::PART-SELECT-WIDTH-LOW VAL 8 56)))
               (MV-LET (1ST-BYTE 2ND-BYTE 3RD-BYTE 4TH-BYTE
                                 5TH-BYTE 6TH-BYTE 7TH-BYTE 8TH-BYTE)
                 (IF (FEAT-LITTLE-ENDIANP FEAT)
                     (MV B0 B1 B2 B3 B4 B5 B6 B7)
                     (MV B7 B6 B5 B4 B3 B2 B1 B0))
                 (LET* ((STAT (WRITE-MEMORY-UNSIGNED8 ADDR 1ST-BYTE STAT FEAT))
                        (STAT (WRITE-MEMORY-UNSIGNED8 (+ (LIFIX ADDR) 1)
                                                      2ND-BYTE STAT FEAT))
                        (STAT (WRITE-MEMORY-UNSIGNED8 (+ (LIFIX ADDR) 2)
                                                      3RD-BYTE STAT FEAT))
                        (STAT (WRITE-MEMORY-UNSIGNED8 (+ (LIFIX ADDR) 3)
                                                      4TH-BYTE STAT FEAT))
                        (STAT (WRITE-MEMORY-UNSIGNED8 (+ (LIFIX ADDR) 4)
                                                      5TH-BYTE STAT FEAT))
                        (STAT (WRITE-MEMORY-UNSIGNED8 (+ (LIFIX ADDR) 5)
                                                      6TH-BYTE STAT FEAT))
                        (STAT (WRITE-MEMORY-UNSIGNED8 (+ (LIFIX ADDR) 6)
                                                      7TH-BYTE STAT FEAT))
                        (STAT (WRITE-MEMORY-UNSIGNED8 (+ (LIFIX ADDR) 7)
                                                      8TH-BYTE STAT FEAT)))
                       STAT)))))
    stat1)
  :non-executable t
  :guard-hints (("Goal"
                 :use (:instance (:guard-theorem write-memory-unsigned64)
                                 (stat (stat-from-stat1 stat1))))))

(define read1-instruction (addr stat1 feat)
  :guard (and (stat1p stat1)
              (b* ((STAT (stat-from-stat1 stat1)))
                (AND (INTEGERP ADDR)
                     (STATP STAT)
                     (FEATP FEAT)
                     (STAT-VALIDP STAT FEAT))))
  (if (mbt (stat1p stat1))
      (b* ((STAT (stat-from-stat1 stat1)))
        (LET* ((ADDR (LOGHEAD (FEAT->XLEN FEAT) ADDR)))
              (AND (= (MOD ADDR 4) 0)
                   (LET* ((B0 (READ-MEMORY-UNSIGNED8 ADDR STAT FEAT))
                          (B1 (READ-MEMORY-UNSIGNED8 (+ ADDR 1)
                                                     STAT FEAT))
                          (B2 (READ-MEMORY-UNSIGNED8 (+ ADDR 2)
                                                     STAT FEAT))
                          (B3 (READ-MEMORY-UNSIGNED8 (+ ADDR 3)
                                                     STAT FEAT)))
                         (LOGAPP 8 B0
                                 (LOGAPP 8 B1 (LOGAPP 8 B2 (LOGAPP 8 B3 0))))))))
    0)
  :guard-hints (("Goal"
                 :use (:instance (:guard-theorem read-instruction)
                                 (stat (stat-from-stat1 stat1))))))

(define errorp1 (stat1 feat)
  :guard (and (stat1p stat1)
              (b* ((STAT (stat-from-stat1 stat1)))
                (AND (STATP STAT)
                     (FEATP FEAT)
                     (STAT-VALIDP STAT FEAT))))
  (declare (ignore feat))
  (if (mbt (stat1p stat1))
      (b* ((STAT (stat-from-stat1 stat1)))
        (STAT->ERROR STAT))
    nil))

(define error1 (stat1 feat)
  :guard (and (stat1p stat1)
              (b* ((STAT (stat-from-stat1 stat1)))
                (AND (STATP STAT)
                     (FEATP FEAT)
                     (STAT-VALIDP STAT FEAT))))
  (if (mbt (stat1p stat1))
      (stat1-from-stat
       (b* ((STAT (stat-from-stat1 stat1)))
         (LET ((CHANGE-STAT STAT) (STAT->ERROR T))
              (STAT (STAT->XREGS CHANGE-STAT)
                    (STAT->PC CHANGE-STAT)
                    (STAT->MEMORY CHANGE-STAT)
                    STAT->ERROR))))
    stat1)
  :non-executable t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; TODO: continue refining the above functions
