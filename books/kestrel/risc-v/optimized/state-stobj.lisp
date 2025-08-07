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

(include-book "kestrel/apt/isodata" :dir :system)
(include-book "std/util/defiso" :dir :system)

(acl2::controlled-configuration)

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

  (acl2::defiso stat1-iso
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

(defsection stat1-validp
  :short "Refine @(tsee stat-validp) to use the stobj states."

  (apt::isodata stat-validp
                ((stat stat1-iso))
                :undefined nil
                :new-name stat1-validp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection read1-xreg-unsigned
  :short "Refine @(tsee read-xreg-unsigned) to use the stobj states."

  (apt::isodata read-xreg-unsigned
                ((stat stat1-iso))
                :undefined 0
                :new-name read1-xreg-unsigned))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection read1-xreg-signed
  :short "Refine @(tsee read-xreg-signed) to use the stobj states."

  (apt::isodata read-xreg-signed
                ((stat stat1-iso))
                :undefined 0
                :new-name read1-xreg-signed))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection read1-xreg-unsigned32
  :short "Refine @(tsee read-xreg-unsigned32) to use the stobj states."

  (apt::isodata read-xreg-unsigned32
                ((stat stat1-iso))
                :undefined 0
                :new-name read1-xreg-unsigned32))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection read1-xreg-signed32
  :short "Refine @(tsee read-xreg-signed32) to use the stobj states."

  (apt::isodata read-xreg-signed32
                ((stat stat1-iso))
                :undefined 0
                :new-name read1-xreg-signed32))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection write1-xreg
  :short "Refine @(tsee write-xreg) to use the stobj states."

  (apt::isodata write-xreg
                ((stat stat1-iso))
                :undefined 0
                :new-name write1-xreg))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection write1-xreg-32
  :short "Refine @(tsee write-xreg-32) to use the stobj states."

  (apt::isodata write-xreg-32
                ((stat stat1-iso))
                :undefined 0
                :new-name write1-xreg-32))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection read1-pc
  :short "Refine @(tsee read-pc) to use the stobj states."

  (apt::isodata read-pc
                ((stat stat1-iso))
                :undefined 0
                :new-name read1-pc))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection write1-pc
  :short "Refine @(tsee write-pc) to use the stobj states."

  (apt::isodata write-pc
                ((stat stat1-iso))
                :undefined 0
                :new-name write1-pc))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection inc41-pc
  :short "Refine @(tsee inc4-pc) to use the stobj states."

  (apt::isodata inc4-pc
                ((stat stat1-iso))
                :undefined 0
                :new-name inc41-pc))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection read1-memory-unsigned8
  :short "Refine @(tsee read-memory-unsigned8) to use the stobj states."

  (apt::isodata read-memory-unsigned8
                ((stat stat1-iso))
                :undefined 0
                :new-name read1-memory-unsigned8))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection read1-memory-unsigned16
  :short "Refine @(tsee read-memory-unsigned16) to use the stobj states."

  (apt::isodata read-memory-unsigned16
                ((stat stat1-iso))
                :undefined 0
                :new-name read1-memory-unsigned16))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection read1-memory-unsigned32
  :short "Refine @(tsee read-memory-unsigned32) to use the stobj states."

  (apt::isodata read-memory-unsigned32
                ((stat stat1-iso))
                :undefined 0
                :new-name read1-memory-unsigned32))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection read1-memory-unsigned64
  :short "Refine @(tsee read-memory-unsigned64) to use the stobj states."

  (apt::isodata read-memory-unsigned64
                ((stat stat1-iso))
                :undefined 0
                :new-name read1-memory-unsigned64))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection write1-memory-unsigned8
  :short "Refine @(tsee write-memory-unsigned8) to use the stobj states."

  (apt::isodata write-memory-unsigned8
                ((stat stat1-iso))
                :undefined 0
                :new-name write1-memory-unsigned8))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection write1-memory-unsigned16
  :short "Refine @(tsee write-memory-unsigned16) to use the stobj states."

  (apt::isodata write-memory-unsigned16
                ((stat stat1-iso))
                :undefined 0
                :new-name write1-memory-unsigned16))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection write1-memory-unsigned32
  :short "Refine @(tsee write-memory-unsigned32) to use the stobj states."

  (apt::isodata write-memory-unsigned32
                ((stat stat1-iso))
                :undefined 0
                :new-name write1-memory-unsigned32))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection write1-memory-unsigned64
  :short "Refine @(tsee write-memory-unsigned64) to use the stobj states."

  (apt::isodata write-memory-unsigned64
                ((stat stat1-iso))
                :undefined 0
                :new-name write1-memory-unsigned64))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection read1-instruction
  :short "Refine @(tsee read-instruction) to use the stobj states."

  (apt::isodata read-instruction
                ((stat stat1-iso))
                :undefined 0
                :new-name read1-instruction))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection errorp1
  :short "Refine @(tsee errorp) to use the stobj states."

  (apt::isodata errorp
                ((stat stat1-iso))
                :undefined 0
                :new-name errorp1))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection error1
  :short "Refine @(tsee error) to use the stobj states."

  (apt::isodata error
                ((stat stat1-iso))
                :undefined 0
                :new-name error1))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; TODO: continue refining the above functions
