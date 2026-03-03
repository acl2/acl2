; AIR Library
; Model 0: Correctness
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (mccarthy@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "AIR-M0")

(include-book "pfcs-lifting")

(include-book "../language/input-output-semantics")

(include-book "projects/pfcs/lifting" :dir :system)

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "std/lists/last" :dir :system))
(local (include-book "std/lists/len" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/utilities/nfix" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Temporary: these will come from prime-fields-rules
(local (encapsulate nil
           (defthm pfield::fep-of-+-same
             (implies (and (integerp pfield::x)
                           (posp pfield::p))
                      (equal (pfield::fep (+ pfield::x pfield::p)
                                          pfield::p)
                             (and (< pfield::x 0)
                                  (>= pfield::p (- pfield::x)))))
             :hints (("Goal" :in-theory (enable natp pfield::fep))))
         (defthm pfield::add-of-add-combine-constants-2
           (implies (and (syntaxp (and (quotep pfield::y)
                                       (quotep pfield::x)))
                         (integerp pfield::x)
                         (integerp pfield::y)
                         (posp pfield::p))
                    (equal (pfield::add pfield::x
                                        (pfield::add pfield::y pfield::z pfield::p)
                                        pfield::p)
                           (pfield::add (+ pfield::x pfield::y)
                                        pfield::z pfield::p)))
           :hints (("Goal" :in-theory (enable pfield::add ifix fix))))
         (defthmd pfield::add-when-<
           (implies (and (< (+ pfield::x pfield::y) pfield::p)
                         (natp pfield::x)
                         (natp pfield::y)
                         (posp pfield::p))
                    (equal (pfield::add pfield::x pfield::y pfield::p)
                           (+ pfield::x pfield::y)))
           :hints (("Goal" :in-theory (enable pfield::add))))
         (defthm pfield::neg-of-+-2
           (implies (and (integerp pfield::x)
                         (integerp pfield::y))
                    (equal (pfield::neg (+ pfield::x pfield::y)
                                        pfield::p)
                           (pfield::add (pfield::neg pfield::x pfield::p)
                                        (pfield::neg pfield::y pfield::p)
                                        pfield::p)))
           :hints (("Goal" :in-theory (enable pfield::add
                                              pfield::neg fix acl2::pos-fix))))
         (defthm pfield::+-of-mod-of-+-of--1
           (implies (and (integerp pfield::x)
                         (posp pfield::y))
                    (equal (+ 1 (mod (+ -1 pfield::x) pfield::y))
                           (if (equal (mod pfield::x pfield::y) 0)
                               pfield::y
                             (mod pfield::x pfield::y))))
           :hints (("Goal" :in-theory (enable acl2::mod-sum-cases fix))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ correctness
  :parents (model-0)
  :short "Correctness of the compilation of programs to AIR constraints."
  :long
  (xdoc::topstring
   (xdoc::p
    "The AIR constraints are expressed as PFCS."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Construction of a trace from the field elements.

; We define a function to construct a trace from the field elements
; that represent the program counters, the accumulators, and the halted flags.
; There is no need to verify the guards of this function,
; because it is only used for logic purposes.
; We prove some theorems about this trace construction.

(defund trace-from-field (pcs accs hlts prog)
  (if (endp pcs)
      nil
    (cons (new-trace-row (vm-state (car pcs)
                                   (car accs)
                                   (bit->bool (car hlts)))
                         prog)
          (trace-from-field (cdr pcs) (cdr accs) (cdr hlts) prog))))

(defruled car-of-trace-from-field
  (implies (consp pcs)
           (equal (car (trace-from-field pcs accs hlts prog))
                  (new-trace-row (vm-state
                                  (car pcs)
                                  (car accs)
                                  (bit->bool (car hlts)))
                                 prog)))
  :enable trace-from-field)

(defruled last-of-trace-from-field
  (implies (and (consp pcs)
                (equal (len accs) (len pcs))
                (equal (len hlts) (len pcs)))
           (equal (car (last (trace-from-field pcs accs hlts prog)))
                  (new-trace-row (vm-state
                                  (car (last pcs))
                                  (car (last accs))
                                  (bit->bool (car (last hlts))))
                                 prog)))
  :induct t
  :enable (trace-from-field
           new-trace-row
           atom
           last
           consp-of-cdr-when-consp-of-cdr-and-same-len))

(defruled row-to-state-of-car-of-trace-from-field
  (implies (consp pcs)
           (equal (row-to-state (car (trace-from-field pcs accs hlts prog)))
                  (vm-state (car pcs)
                            (car accs)
                            (bit->bool (car hlts)))))
  :enable (car-of-trace-from-field
           row-to-state
           new-trace-row))

(defruled row-to-state-of-last-of-trace-from-field
  (implies (and (consp pcs)
                (equal (len accs) (len pcs))
                (equal (len hlts) (len pcs)))
           (equal (row-to-state
                   (car (last (trace-from-field pcs accs hlts prog))))
                  (vm-state (car (last pcs))
                            (car (last accs))
                            (bit->bool (car (last hlts))))))
  :enable (last-of-trace-from-field
           row-to-state
           new-trace-row))

(defrule trace-pcs-of-trace-from-field
  (equal (trace-pcs (trace-from-field pcs accs hlts prog))
         (nat-list-fix pcs))
  :induct t
  :enable (trace-from-field
           new-trace-row))

(defruled trace-from-field-of-trace-comps
  (implies (equal (trace-opcodes tr)
                  (fetch-list prog (trace-pcs tr)))
           (equal (trace-from-field (trace-pcs tr)
                                    (trace-accs tr)
                                    (bool-list->bit-list (trace-halteds tr))
                                    prog)
                  (trace-fix tr)))
  :induct t
  :enable (trace-from-field
           trace-pcs
           trace-accs
           trace-halteds
           bool-list->bit-list
           new-trace-row
           bool->bit))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Correctness of the predicates.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled pfcs-bit-pred-to-bitp
  :short "The bit constraints are equivalent to @(tsee bitp)."
  (implies (and (pfcs::primep prime)
                (pfield::fep x prime))
           (equal (pfcs-bit-pred x prime)
                  (bitp x)))
  :enable (pfcs-bit-pred))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled pfcs-byte-pred-to-<-256
  :short "The byte constraints are equivalent to being below 256."
  (implies (and (pfcs::primep prime)
                (pfield::fep x prime))
           (equal (pfcs-byte-pred x prime)
                  (< x 256)))
  :use (soundness completeness)

  :prep-lemmas

  ((defruled soundness
     (implies (and (pfcs::primep prime)
                   (pfield::fep x prime))
              (implies (pfcs-byte-pred x prime)
                       (< x 256)))
     :enable (pfcs-byte-pred
              pfcs-bit-pred-to-bitp
              pfield::add
              pfield::neg
              pfield::mul
              fix))

   (defruled completeness
     (implies (and (pfcs::primep prime)
                   (pfield::fep x prime))
              (implies (< x 256)
                       (pfcs-byte-pred x prime)))
     :use (:instance pfcs-byte-pred-suff
                     (x0 (mod x 2))
                     (x1 (mod (floor x 2) 2))
                     (x2 (mod (floor x 4) 2))
                     (x3 (mod (floor x 8) 2))
                     (x4 (mod (floor x 16) 2))
                     (x5 (mod (floor x 32) 2))
                     (x6 (mod (floor x 64) 2))
                     (x7 (mod (floor x 128) 2)))
     :enable pfcs-bit-pred-to-bitp
     :hints (`(:cases ,(cases 255)))
     :prep-lemmas
     ((defun cases (n)
        (if (zp n)
            nil
          (cons `(equal x ,n)
                (cases (1- n)))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled pfcs-initial-pred-to-pc=hlt=0
  :short "The first row constraints are equivalent to
          the program counter being 0."
  :long
  (xdoc::topstring
   (xdoc::p
    "I.e. execution starts at the beginning of the program,
     in a non-halted state."))
  (implies (and (pfcs::primep prime)
                (pfield::fep pc prime)
                (pfield::fep acc prime)
                (pfield::fep op prime)
                (pfield::fep hlt prime))
           (equal (pfcs-initial-pred pc acc op hlt prime)
                  (and (equal pc 0)
                       (equal hlt 0))))
  :enable pfcs-initial-pred)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled pfcs-final-pred-to-hlt=1
  :short "The last row constraints are equivalent to
          the halted flag being set."
  :long
  (xdoc::topstring
   (xdoc::p
    "I.e. the program has executed to completion."))
  (implies (and (pfcs::primep prime)
                (pfield::fep pc prime)
                (pfield::fep acc prime)
                (pfield::fep op prime)
                (pfield::fep hlt prime))
           (equal (pfcs-final-pred pc acc op hlt prime)
                  (equal hlt 1)))
  :enable pfcs-final-pred)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Helper lemmas for field arithmetic with -1 terms.
; These arise from the (pc_next - pc - 1) constraint in pc_transition.

(defruled add-of-neg-1-and-plus-1
  (implies (and (natp x)
                (< (1+ x) prime)
                (posp prime))
           (equal (pfield::add -1 (+ 1 x) prime)
                  x))
  :enable (pfield::add acl2::mod-when-< fix))

(defruled plus-1-of-add-neg-1
  (implies (and (natp x)
                (< x prime)
                (posp prime)
                (< (+ 1 (pfield::add -1 x prime)) prime))
           (equal (+ 1 (pfield::add -1 x prime))
                  x))
  :enable (pfield::add acl2::mod-when-< fix)
  :hints (("Goal" :cases ((equal x 0)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled pfcs-pc-transition-pred-to-def-of-next
  :short "The program counter transition constraints are equivalent to
           the definition of the next program counter."
  :long
  (xdoc::topstring
   (xdoc::p
    "The new program counter is one more than the old one,
      unless execution is halted or the opcode is HALT,
      in which case the program counter stays the same.")
   (xdoc::p
    "We need the hypothesis that, unless execution is halted,
      the program counter is at least two below the prime,
      otherwise incrementing the program counter yields 0.
      The hypothesis is satisfied when the program is not excessively large,
      so that it gets to the halted state before the program counter
      has had a chance to wrap around the prime.")
   (xdoc::p
    "The hypothesis that the prime is odd
      guarantees that the three opcodes can be distinguished.
      With more opcode, we would have a more general hypothesis saying that
      the prime is large enough to distinguish all of them."))
  (implies (and (pfcs::primep prime)
                (pfield::fep pc prime)
                (pfield::fep op prime)
                (pfield::fep hlt prime)
                (pfield::fep pc-next prime)
                (oddp prime)
                (or (equal hlt 1)
                    (equal op 2)
                    (< (1+ pc) prime))
                (member-equal op '(0 1 2))
                (bitp hlt))
           (equal (pfcs-pc-transition-pred pc op hlt pc-next prime)
                  (equal pc-next
                         (if (equal hlt 0)
                             (if (member-equal op '(0 1))
                                 (1+ pc)
                               pc)
                           pc))))
  :enable (pfcs-pc-transition-pred
           add-of-neg-1-and-plus-1
           plus-1-of-add-neg-1)
  :disable (pfield::mul-of-add-arg1
            pfield::mul-of-add-arg2))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled pfcs-acc-transition-pred-to-def-of-next
  :short "The accumulator transition constraints are equivalent to
          the definition of the next accumulator, under the assumption that
          the accumulator values are bytes."
  :long
  (xdoc::topstring
   (xdoc::p
    "The new accumulator is one more/less than the old one
     when execution is not halted and the opcode is INCR/DECR,
     and otherwise the same as the old one.")
   (xdoc::p
    "We need the hypothesis that the prime is over 510
     for two reasons:
     (1) all byte values (0-255) must be distinguishable in the field, and
     (2) the constraint arithmetic involves sums up to 510
     (e.g., @('acc + 255') for DECR),
     which must not wrap around in the field.")
   (xdoc::p
    "We also need the hypothesis that @('acc-next') is a byte (less than 256).
     This is because when acc = 255, acc-next could be 0 or 256,
     according to the current constraints.
     (This hypothesis will not be needed when we have added the
     the byte range (non-AIR) constraints to a more general model.)"))
  (implies (and (pfcs::primep prime)
                (pfield::fep acc prime)
                (pfield::fep op prime)
                (pfield::fep hlt prime)
                (pfield::fep acc-next prime)
                (> prime 510)
                (< acc 256)
                (< acc-next 256)
                (member-equal op '(0 1 2))
                (bitp hlt))
           (equal (pfcs-acc-transition-pred acc op hlt acc-next prime)
                  (equal acc-next
                         (if (equal hlt 0)
                             (case op
                               (0 (mod (1+ acc) 256))
                               (1 (mod (1- acc) 256))
                               (2 acc))
                           acc))))
  :enable (pfield::add-when-<
           fix
           pfcs-acc-transition-pred)
  :disable (pfield::mul-of-add-arg1
            pfield::mul-of-add-arg2))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled pfcs-halted-transition-pred-to-def-of-next
  :short "The halted flag transition constraints are equivalent to
         the definition of the next halted flag."
  :long
  (xdoc::topstring
   (xdoc::p
    "The cnew halted flag is the same as the old one,
      unless the opcode is HALT, in which case it is set to 1.")
   (xdoc::p
    "The hypothesis that the prime is odd
      guarantees that the three opcodes can be distinguished.
      With more opcode, we would have a more general hypothesis saying that
      the prime is large enough to distinguish all of them."))
  (implies (and (pfcs::primep prime)
                (pfield::fep op prime)
                (pfield::fep hlt prime)
                (pfield::fep hlt-next prime)
                (oddp prime)
                (member-equal op '(0 1 2))
                (bitp hlt))
           (equal (pfcs-halted-transition-pred op hlt hlt-next prime)
                  (equal hlt-next
                         (if (equal op 2)
                             1
                           hlt))))
  :enable (pfcs-halted-transition-pred)
  :disable (pfield::mul-of-add-arg1
            pfield::mul-of-add-arg2))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled pfcs-transition-pred-to-def-of-next
  :short "The transition constraints are equivalent to
          the definition of the next
          program counter, accumulator, and halted flag."
  :long
  (xdoc::topstring
   (xdoc::p
    "The new program counter, accumulator, and halted flag
     are computed from the old ones in the manner expressed
     by the three theorems used as rewrite rules here.")
   (xdoc::p
    "The three equalities in the right side of the conclusion of this theorem
     express execution on data encoded as field elements.
     The @('op-next') is actually not constrained here,
     but is included in the constraints to make them
     more clearly constraints on (all the components of) the transitions."))
  (implies (and (pfcs::primep prime)
                (pfield::fep pc prime)
                (pfield::fep acc prime)
                (pfield::fep op prime)
                (pfield::fep hlt prime)
                (pfield::fep pc-next prime)
                (pfield::fep acc-next prime)
                (pfield::fep op-next prime)
                (pfield::fep hlt-next prime)
                (> prime 510)
                (or (equal hlt 1)
                    (equal op 2)
                    (< (1+ pc) prime))
                (< acc 256)
                (< acc-next 256)
                (member-equal op '(0 1 2))
                (bitp hlt))
           (equal (pfcs-transition-pred
                   pc acc op hlt
                   pc-next acc-next op-next hlt-next
                   prime)
                  (and (equal pc-next
                              (if (equal hlt 0)
                                  (if (member-equal op '(0 1))
                                      (1+ pc)
                                    pc)
                                pc))
                       (equal acc-next
                              (if (equal hlt 0)
                                  (case op
                                    (0 (mod (1+ acc) 256))
                                    (1 (mod (1- acc) 256))
                                    (2 acc))
                                acc))
                       (equal hlt-next
                              (if (equal op 2)
                                  1
                                hlt)))))
  :enable (pfcs-transition-pred
           pfcs-pc-transition-pred-to-def-of-next
           pfcs-acc-transition-pred-to-def-of-next
           pfcs-halted-transition-pred-to-def-of-next))

;;;;;;;;;;;;;;;;;;;;

(defruled pfcs-transition-pred-to-step1
  :short "The transition constraints are equivalent to an execution step."
  :long
  (xdoc::topstring
   (xdoc::p
    "This extends @(tsee pfcs-transition-pred-to-def-of-next),
     which is solely in terms of field elements,
     to a property that about the program and its execution.")
   (xdoc::p
    "We use the @(tsee opcode-to-field) encoding function
     to relate the opcode constraint variables
     to opcodes fetched from the program.")
   (xdoc::p
    "We use the library function @(tsee bit->bool)
     as the decoding function of booleans from field elements,
     for the halted flag.")
   (xdoc::p
    "We assume that the program is well-formed,
     and not longer than the value of the prime,
     which guarantees that we can reliably encode program counters.")
   (xdoc::p
    "We assume restrictions on the starting values of
     program counter, accumulator, and halted flag.
     The right side of the conclusion includes
     the same restrictions on their next values.
     The one on the program counter depends on
     the property of well-formed programs that
     the last opcode is HALT:
     thus, if @('pc') is the largest value in the field,
     it must be the last opcode in the program
     because of the assumption that the program length
     does not exceed the prime,
     and therefore @('pc-next') does not change and stays in range."))
  (implies (and (pfcs::primep prime)
                (pfield::fep pc prime)
                (pfield::fep acc prime)
                (pfield::fep op prime)
                (pfield::fep hlt prime)
                (pfield::fep pc-next prime)
                (pfield::fep acc-next prime)
                (pfield::fep op-next prime)
                (pfield::fep hlt-next prime)
                (program-well-formed-p prog)
                (> prime 510)
                (<= (len prog) prime)
                (< pc (len prog))
                (< acc 256)
                (< acc-next 256)
                (bitp hlt)
                (equal op
                       (opcode-to-field (fetch prog pc)))
                (equal op-next
                       (opcode-to-field (fetch prog pc-next))))
           (equal (pfcs-transition-pred
                   pc acc op hlt
                   pc-next acc-next op-next hlt-next
                   prime)
                  (and (< pc-next (len prog))
                       (< acc-next 256)
                       (bitp hlt-next)
                       (equal (step1 (vm-state pc
                                               acc
                                               (bit->bool hlt))
                                     prog)
                              (vm-state pc-next
                                        acc-next
                                        (bit->bool hlt-next))))))
  :use pfcs-transition-pred-to-def-of-next
  :enable (step1
           fetch-is-halt-when-last
           opcode-to-field
           nfix
           ubyte8p
           unsigned-byte-p
           integer-range-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled pfcs-all-transitions-pred-to-trace
  :short "All the transition constraints are equivalent to
          the generation of the trace."
  :long
  (xdoc::topstring
   (xdoc::p
    "This makes use of @(tsee pfcs-transition-pred-to-step1),
     which applies to a single transition.
     If we generate a trace, via @(tsee generate-trace*),
     from the first program counter, accumulator, and halted flag
     of the lists of field elements,
     the rows of the rest of the trace match exactly
     the remaining field values."))
  (implies (and (pfcs::primep prime)
                (pfield::fe-listp pcs prime)
                (pfield::fe-listp accs prime)
                (pfield::fe-listp ops prime)
                (pfield::fe-listp hlts prime)
                (equal (len accs) (len pcs))
                (equal (len ops) (len pcs))
                (equal (len hlts) (len pcs))
                (program-well-formed-p prog)
                (> prime 510)
                (<= (len prog) prime)
                (or (endp pcs)
                    (< (car pcs) (len prog)))
                (all-< accs 256)
                (or (endp hlts)
                    (bitp (car hlts)))
                (equal ops
                       (opcode-list-to-field (fetch-list prog pcs))))
           (equal (pfcs-all-transitions-pred pcs accs ops hlts prime)
                  (and (all-< pcs (len prog))
                       (bit-listp hlts)
                       (or (endp pcs)
                           (equal (generate-trace*
                                   (vm-state (car pcs)
                                             (car accs)
                                             (bit->bool (car hlts)))
                                   prog
                                   (1- (len pcs)))
                                  (trace-from-field pcs accs hlts prog))))))
  :use (soundness completeness)

  :prep-lemmas

  ((defrule len-lemma
     (implies (consp (cdr x))
              (equal (+ -1 (len (cdr x)))
                     (+ -2 (len x)))))

   (defruled soundness
     (implies (and (pfcs::primep prime)
                   (pfield::fe-listp pcs prime)
                   (pfield::fe-listp accs prime)
                   (pfield::fe-listp ops prime)
                   (pfield::fe-listp hlts prime)
                   (equal (len accs) (len pcs))
                   (equal (len ops) (len pcs))
                   (equal (len hlts) (len pcs))
                   (program-well-formed-p prog)
                   (> prime 510)
                   (<= (len prog) prime)
                   (or (endp pcs)
                       (< (car pcs) (len prog)))
                   (all-< accs 256)
                   (or (endp hlts)
                       (bitp (car hlts)))
                   (equal ops (opcode-list-to-field (fetch-list prog pcs)))
                   (pfcs-all-transitions-pred pcs accs ops hlts prime))
              (and (all-< pcs (len prog))
                   (bit-listp hlts)
                   (or (endp pcs)
                       (equal (generate-trace*
                               (vm-state (car pcs)
                                         (car accs)
                                         (bit->bool (car hlts)))
                               prog
                               (1- (len pcs)))
                              (trace-from-field pcs accs hlts prog)))))
     :induct t
     :enable (pfcs-all-transitions-pred
              pfcs-transition-pred-to-step1
              generate-trace*
              trace-from-field
              consp-when-consp-and-same-len
              consp-of-cdr-when-consp-of-cdr-and-same-len
              consp-of-cddr-when-consp-of-cddr-and-same-len
              len-lemma
              all-<)
     :disable equal-of-vm-state)

   (defruled completeness
     (implies (and (pfcs::primep prime)
                   (pfield::fe-listp pcs prime)
                   (pfield::fe-listp accs prime)
                   (pfield::fe-listp ops prime)
                   (pfield::fe-listp hlts prime)
                   (equal (len accs) (len pcs))
                   (equal (len ops) (len pcs))
                   (equal (len hlts) (len pcs))
                   (program-well-formed-p prog)
                   (> prime 510)
                   (<= (len prog) prime)
                   (or (endp pcs)
                       (< (car pcs) (len prog)))
                   (or (endp accs)
                       (< (car accs) 256))
                   (or (endp hlts)
                       (bitp (car hlts)))
                   (equal ops (opcode-list-to-field (fetch-list prog pcs)))
                   (all-< pcs (len prog))
                   (all-< accs 256)
                   (bit-listp hlts)
                   (or (endp pcs)
                       (equal (generate-trace*
                               (vm-state (car pcs)
                                         (car accs)
                                         (bit->bool (car hlts)))
                               prog
                               (1- (len pcs)))
                              (trace-from-field pcs accs hlts prog))))
              (pfcs-all-transitions-pred pcs accs ops hlts prime))
     :induct t
     :enable (pfcs-all-transitions-pred
              pfcs-transition-pred-to-step1
              generate-trace*
              trace-from-field
              consp-when-consp-and-same-len
              consp-of-cdr-when-consp-of-cdr-and-same-len
              consp-of-cddr-when-consp-of-cddr-and-same-len
              len-lemma
              all-<)
     :disable equal-of-vm-state
     :hints ('(:use ((:instance row-to-state-of-car-of-generate-trace*
                                (st (step1 (vm-state (car pcs)
                                                     (car accs)
                                                     (equal 1 (car hlts)))
                                           prog))
                                (limit (+ -2 (len accs))))
                     (:instance row-to-state-of-car-of-trace-from-field
                                (pcs (cdr pcs))
                                (accs (cdr accs))
                                (hlts (cdr hlts)))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled pfcs-execution-pred-to-min-trace
  :short "The execution constraints are equivalent to
          the generation of the minimal trace."
  (implies (and (pfcs::primep prime)
                (pfield::fe-listp pcs prime)
                (pfield::fe-listp accs prime)
                (pfield::fe-listp ops prime)
                (pfield::fe-listp hlts prime)
                (equal (len accs) (len pcs))
                (equal (len ops) (len pcs))
                (equal (len hlts) (len pcs))
                (program-well-formed-p prog)
                (terminatesp prog (car accs))
                (equal (len pcs)
                       (1+ (min-termination-limit prog (car accs))))
                (all-< accs 256)
                (> prime 510)
                (<= (len prog) prime)
                (equal ops (opcode-list-to-field (fetch-list prog pcs))))
           (equal (pfcs-execution-pred pcs accs ops hlts prime)
                  (and (all-< pcs (len prog))
                       (bit-listp hlts)
                       (equal (generate-min-trace prog (car accs))
                              (trace-from-field pcs accs hlts prog))
                       (equal pcs (execution-path prog (car accs))))))
  :enable (pfcs-execution-pred
           pfcs-all-transitions-pred-to-trace
           pfcs-initial-pred-to-pc=hlt=0
           pfcs-final-pred-to-hlt=1
           consp-when-consp-and-same-len
           generate-min-trace-is-generate-trace*-of-min-termination-limit
           execution-path
           new-trace-row
           row-to-state)
  :use (car-of-trace-from-field
        last-of-trace-from-field
        (:instance row-to-state-of-car-of-generate-trace*
                   (st (vm-state 0 (car accs) nil))
                   (limit (1- (len accs))))
        (:instance last-row-of-generate-trace*-is-run
                   (st (vm-state 0 (car accs) nil))
                   (limit (1- (len accs))))
        (:instance halted-of-run-of-min-termination-limit
                   (input (car accs))))
  :disable halted-of-run-of-min-termination-limit
  :cases ((equal (min-termination-limit prog (car accs)) (1- (len accs))))
  :prep-lemmas
  ((defrule lemma
     (implies (program-well-formed-p prog)
              (consp prog))
     :enable (program-well-formed-p
              program-nonempty-p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled pfcs-path-pred-to-def-of-pcs
  :short "The execution path constraints are equivalent to
          the equality of the program counters to the path."
  (implies (and (pfcs::primep prime)
                (pfield::fe-listp pcs prime)
                (equal (len pcs) (len path))
                (nat-listp path)
                (all-< path prime))
           (equal (pfcs-path-pred path pcs prime)
                  (equal pcs path)))
  :induct t
  :enable pfcs-path-pred)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled pfcs-opcodes-pred-to-def-of-ops
  :short "The program opcode constraints are equivalent to
          each opcode field value encoding the corresponding program opcode."
  (implies (and (pfcs::primep prime)
                (oddp prime)
                (pfield::fe-listp ops prime)
                (equal (len ops) (len opcodes)))
           (equal (pfcs-opcodes-pred opcodes ops prime)
                  (equal ops (opcode-list-to-field opcodes))))
  :induct t
  :enable pfcs-opcodes-pred)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled pfcs-accumulators-pred-to-all-<-256
  :short "The accumulator constraints are equivalent to
          all the accumulator values being below 256."
  (implies (and (pfcs::primep prime)
                (pfield::fe-listp accs prime))
           (equal (pfcs-accumulators-pred accs prime)
                  (all-< accs 256)))
  :induct t
  :enable (pfcs-accumulators-pred
           pfcs-byte-pred-to-<-256))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled pfcs-table-pred-to-min-trace-and-path-and-opcodes-and-accumulators
  :short "The table constraints are equivalent to
          the generation of the minimal trace,
          the program counters being the executino path,
          and the opcode field values matching
          the corresponding program opcodes."
  :long
  (xdoc::topstring
   (xdoc::p
    "Given an input @('input0') for which the program terminates,
     then for every input in the initial accumulator that follows the same path,
     the table constraints are equivalent to
     the minimal trace for that input,
     the program counters being the ones in the path,
     and the opcode field values matching
     the corresponding program opcodes."))
  (implies (and (pfcs::primep prime)
                (pfield::fe-listp pcs prime)
                (pfield::fe-listp accs prime)
                (pfield::fe-listp ops prime)
                (pfield::fe-listp hlts prime)
                (equal (len accs) (len pcs))
                (equal (len ops) (len pcs))
                (equal (len hlts) (len pcs))
                (program-well-formed-p prog)
                (terminatesp prog input0)
                (equal path (execution-path prog input0))
                (equal opcodes (fetch-list prog path))
                (terminatesp prog (car accs))
                (equal (execution-path prog (car accs)) path)
                (equal (len pcs) (len path))
                (> prime 510)
                (<= (len prog) prime))
           (equal (pfcs-table-pred path opcodes pcs accs ops hlts prime)
                  (and (bit-listp hlts)
                       (equal (generate-min-trace prog (car accs))
                              (trace-from-field pcs accs hlts prog))
                       (equal pcs (execution-path prog (car accs)))
                       (equal ops (opcode-list-to-field opcodes))
                       (all-< accs 256))))
  :enable (pfcs-table-pred
           pfcs-execution-pred-to-min-trace
           pfcs-path-pred-to-def-of-pcs
           pfcs-opcodes-pred-to-def-of-ops
           pfcs-accumulators-pred-to-all-<-256
           all-<-of-prime-when-all-<-of-len-prog)
  :use ((:instance len-of-execution-path (input input0))
        (:instance len-of-execution-path (input (car accs))))
  :disable len-of-execution-path

  :prep-lemmas
  ((defrule all-<-of-prime-when-all-<-of-len-prog
     (implies (and (<= (len prog) prime)
                   (all-< pcs (len prog)))
              (all-< pcs prime))
     :induct t
     :enable all-<)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled pfcs-computation-pred-to-program-output
  :short "The computation constraints are equivalent to
          the input/output semantics of the program."
  :long
  (xdoc::topstring
   (xdoc::p
    "Given a program,
     and a specific input @('input0') on which the program terminates,
     then for every generic input @('input')
     on which the program also terminates
     and follows the same path as @('input0'),
     the computation constraints are satisfied exactly when
     the output matches the one returned by the program on @('input')."))
  (implies (and (program-well-formed-p prog)
                (terminatesp prog input0)
                (equal path (execution-path prog input0))
                (equal opcodes (fetch-list prog path))
                (terminatesp prog input)
                (equal (execution-path prog input) path)
                (pfcs::primep prime)
                (> prime 510)
                (<= (len prog) prime)
                (ubyte8p input)
                (ubyte8p output))
           (equal (pfcs-computation-pred path opcodes input output prime)
                  (equal (program-output prog input)
                         output)))
  :use (soundness completeness)

  :prep-lemmas

  ((defruled soundness
     (implies (and (program-well-formed-p prog)
                   (terminatesp prog input0)
                   (equal path (execution-path prog input0))
                   (equal opcodes (fetch-list prog path))
                   (terminatesp prog input)
                   (equal (execution-path prog input) path)
                   (pfcs::primep prime)
                   (> prime 510)
                   (<= (len prog) prime)
                   (ubyte8p input)
                   (ubyte8p output)
                   (pfcs-computation-pred path opcodes input output prime))
              (equal (program-output prog input)
                     output))
     :enable (pfcs-computation-pred
              pfcs-table-pred-to-min-trace-and-path-and-opcodes-and-accumulators
              program-output-as-generate-min-trace
              ubyte8p
              unsigned-byte-p
              integer-range-p
              row-to-state)
     :use (:instance row-to-state-of-last-of-trace-from-field
                     (pcs (execution-path prog input))
                     (accs (mv-nth 1
                                   (pfcs-computation-pred-witness
                                    (execution-path prog input)
                                    (fetch-list prog
                                                (execution-path prog input))
                                    input output prime)))
                     (hlts (mv-nth 3
                                   (pfcs-computation-pred-witness
                                    (execution-path prog input)
                                    (fetch-list prog
                                                (execution-path prog input))
                                    input output prime)))))

   (defruled completeness
     (implies (and (program-well-formed-p prog)
                   (terminatesp prog input0)
                   (equal path (execution-path prog input0))
                   (equal opcodes (fetch-list prog path))
                   (terminatesp prog input)
                   (equal (execution-path prog input) path)
                   (pfcs::primep prime)
                   (> prime 510)
                   (<= (len prog) prime)
                   (ubyte8p input)
                   (ubyte8p output)
                   (equal (program-output prog input)
                          output))
              (pfcs-computation-pred path opcodes input output prime))
     :enable (pfield::fe-listp-when-nat-listp-and-all-<-prime
              pfield::fe-listp-when-ubyte8-listp
              pfield::fe-listp-when-bit-listp
              program-output-as-generate-min-trace
              ubyte8p
              unsigned-byte-p
              integer-range-p
              pfcs-table-pred-to-min-trace-and-path-and-opcodes-and-accumulators
              trace-from-field-of-trace-comps
              execution-path
              last-of-trace-accs
              trace-opcodes-of-generate-min-trace)
     :disable len-of-trace-pcs
     :use ((:instance len-of-trace-pcs (x (generate-min-trace prog input)))
           (:instance len-of-trace-pcs (x (generate-min-trace prog input0)))
           (:instance pfcs-computation-pred-suff
                      (path (execution-path prog input0))
                      (opcodes (fetch-list prog (execution-path prog input0)))
                      (pcs (execution-path prog input0))
                      (ops (opcode-list-to-field
                            (fetch-list prog (execution-path prog input0))))
                      (accs (trace-accs (generate-min-trace prog input)))
                      (hlts (bool-list->bit-list
                             (trace-halteds (generate-min-trace prog input))))))

     :prep-lemmas
     ((defrule all-<-of-prime-when-all-<-of-len-prog
        (implies (and (<= (len prog) prime)
                      (all-< pcs (len prog)))
                 (all-< pcs prime))
        :induct t
        :enable all-<)))))
