;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")

;; ======================================================================

(include-book "x86-instructions"
              :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "centaur/bitops/signed-byte-p" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))

;; ======================================================================

(defsection x86-decoder
  :parents (machine)
  :short "Definitions of the x86 fetch, decode, and execute function
  and the top-level run function"
  )

;; ======================================================================

(define x86-step-unimplemented (message x86)
  :parents (x86-decoder)
  ;; "Message" can contain some specific error message and the
  ;; opcode(s).
  :returns (x86 x86p :hyp :guard)
  (b* ((ctx 'x86-step-unimplemented))
      (!!ms-fresh :message message)))

;; ======================================================================

;; Some unfinished utilities for generating the dispatch function from
;; implemented-opcodes-table:

(program)

(defun remove-all-opcode-entries (input-opcode alst)
  ;; (remove-all-opcode-entries 0 (table-alist 'implemented-opcodes-table (w state)))
  (if (endp alst)
      nil
    (let* ((entry   (car alst))
           (key     (car entry))
           (opcode  (car key)))
      (if (equal input-opcode opcode)
          (remove-all-opcode-entries input-opcode (cdr alst))
        (cons entry
              (remove-all-opcode-entries input-opcode (cdr alst)))))))


;; TO-DO@Shilpi: Account for :mod type (see RDRAND instruction for an
;; example).

;; extn: opcode extension
(defun construct-reg/misc-opcode-dispatch
  ;; (construct-reg/misc-opcode-dispatch 0 :reg (table-alist 'implemented-opcodes-table (w state)) (w state))
  ;; (construct-reg/misc-opcode-dispatch 1 :misc (table-alist 'implemented-opcodes-table (w state)) (w state))
  (input-opcode reg/misc alst world)
  (declare (ignorable world))
  (if (endp alst)
      (if (equal reg/misc :reg)
          ;; We use a case statement for :reg, hence the use of
          ;; otherwise as a kitchen sink branch.
          `((otherwise (x86-step-unimplemented (list (cons :opcode ,input-opcode) 'Kitchen-Sink) x86)))
        ;; We use a cond statement for :misc, hence the use of t as a
        ;; kitchen sink branch.
        `((t (x86-step-unimplemented (list (cons :opcode ,input-opcode) 'Kitchen-Sink) x86))))
    (let* ((entry      (car alst))
           (key        (car entry))
           (fn-details (cdr entry))
           (fn-name    (cdr fn-details))
           (opcode     (car key))
           (type       (cdr key)))
      (if (equal input-opcode opcode)
          (if (equal (car type) reg/misc)
              (b* ((type-val (cadr type))
                   (fn-call fn-name
                            ;; (cons fn-name (acl2::formals fn-name world))
                            ))
                  (cons (list type-val fn-call)
                        (construct-reg/misc-opcode-dispatch
                         input-opcode reg/misc (cdr alst) world)))
            (er hard 'construct-reg/misc-opcode-dispatch
                "Opcode ~x0 is expected to have type ~x1, but not all entries corresponding to ~x0 in implemented-opcodes-table have this type. E.g.: ~x2~%" opcode reg/misc entry))
        (construct-reg/misc-opcode-dispatch input-opcode reg/misc (cdr alst) world)))))

(defun construct-opcode-dispatch-fn (alst world state)
  (declare (xargs :stobjs (state)))
  ;; (construct-opcode-dispatch-fn (table-alist 'implemented-opcodes-table (w state)) (w state))

  ;; (3 simple)
  ;; (2 simple)
  ;; (1
  ;;  (cond ((equal modr/m 51)
  ;;         random)
  ;;        (t
  ;;         ...)))
  ;; (0
  ;;  (case reg
  ;;    (0 add)
  ;;    (1 sub)
  ;;    (2 adc)))

  (if (endp alst)
      nil
    (let* ((entry   (car alst))
           (key     (car entry))
           (fn-details (cdr entry))
           (fn-name    (cdr fn-details))
           (opcode  (car key))
           (type    (cdr key)))
      (cond ((equal (car type) :nil)
             (b* ((fn-call ;; (cons fn-name (acl2::formals fn-name world))
                   fn-name
                   ))
                 (cons
                  (list opcode fn-call)
                  (construct-opcode-dispatch-fn (cdr alst) world state))))
            ((equal (car type) :reg)
             (b*
              ((reg-case (construct-reg/misc-opcode-dispatch opcode :reg alst world))
               (alst (remove-all-opcode-entries opcode alst)))
              (cons (list opcode (append (list 'case 'reg) reg-case))
                    (construct-opcode-dispatch-fn alst world state))))
            ((equal (car type) :misc)
             (b*
              ((misc-case (construct-reg/misc-opcode-dispatch opcode :misc alst world))
               (alst (remove-all-opcode-entries opcode alst)))
              (cons (list opcode (append (list 'cond) misc-case))
                    (construct-opcode-dispatch-fn alst world state))))
            (t
             (er hard 'construct-opcode-dispatch-fn
                 "implemented-opcodes-table contains an invalid type field in the following entry:~% ~x0~%" entry))))))

(defmacro construct-opcode-dispatch ()
  `(construct-opcode-dispatch-fn
    (table-alist 'implemented-opcodes-table (w state)) (w state)
    state))

(logic)

;; ======================================================================

;; Opcode dispatch functions:

(defconst *top-level-op-list*

  ;; This constant will be used to construct the case statement for
  ;; opcode-execute.  Each element of the list below is a
  ;; three-element list --- the first element is the opcode, the
  ;; second is a string that contains some useful information about
  ;; that opcode, and the third is either another case statement if
  ;; there is an opcode-extension or it is a call to the function
  ;; implementing that instruction.

  `(
    (#x00
     "(ADD Eb Gb)"
     (x86-add/adc/sub/sbb/or/and/xor/cmp/test-E-G
      #.*OP-ADD* start-rip temp-rip prefixes rex-byte opcode modr/m sib x86))

    (#x01
     "(ADD Ev Gv)"
     (x86-add/adc/sub/sbb/or/and/xor/cmp/test-E-G
      #.*OP-ADD* start-rip temp-rip prefixes rex-byte opcode modr/m sib x86))

    (#x02
     "(ADD Gb Eb)"
     (x86-add/adc/sub/sbb/or/and/xor/cmp-G-E
      #.*OP-ADD* start-rip temp-rip prefixes rex-byte opcode modr/m sib x86))

    (#x03
     "(ADD Gv Ev)"
     (x86-add/adc/sub/sbb/or/and/xor/cmp-G-E
      #.*OP-ADD* start-rip temp-rip prefixes rex-byte opcode modr/m sib x86))

    (#x04
     "(ADD AL lb)"
     (x86-add/adc/sub/sbb/or/and/xor/cmp-test-rAX-I
      #.*OP-ADD* start-rip temp-rip prefixes rex-byte opcode modr/m sib x86))


    (#x05
     "(ADD rAX Iz)"
     (x86-add/adc/sub/sbb/or/and/xor/cmp-test-rAX-I
      #.*OP-ADD* start-rip temp-rip prefixes rex-byte opcode modr/m sib x86))


    (#x06
     "(PUSH ES)"
     (x86-step-unimplemented
      (cons (ms x86)
            (list start-rip temp-rip prefixes rex-byte opcode)) x86))


    (#x07
     "(POP ES)"
     (x86-step-unimplemented
      (cons (ms x86)
            (list start-rip temp-rip prefixes rex-byte opcode)) x86))


    (#x08
     "(OR Eb Gb)"
     (x86-add/adc/sub/sbb/or/and/xor/cmp/test-E-G
      #.*OP-OR* start-rip temp-rip prefixes rex-byte opcode modr/m sib x86))


    (#x09
     "(OR Ev Gv)"
     (x86-add/adc/sub/sbb/or/and/xor/cmp/test-E-G
      #.*OP-OR* start-rip temp-rip prefixes rex-byte opcode modr/m sib x86))


    (#x0A
     "(OR Gb Eb)"
     (x86-add/adc/sub/sbb/or/and/xor/cmp-G-E
      #.*OP-OR* start-rip temp-rip prefixes rex-byte opcode modr/m sib x86))


    (#x0B
     "(OR Gv Ev)"
     (x86-add/adc/sub/sbb/or/and/xor/cmp-G-E
      #.*OP-OR* start-rip temp-rip prefixes rex-byte opcode modr/m sib x86))


    (#x0C
     "(OR AL Ib)"
     (x86-add/adc/sub/sbb/or/and/xor/cmp-test-rAX-I
      #.*OP-OR* start-rip temp-rip prefixes rex-byte opcode modr/m sib x86))


    (#x0D
     "(OR rAX Iz)"
     (x86-add/adc/sub/sbb/or/and/xor/cmp-test-rAX-I
      #.*OP-OR* start-rip temp-rip prefixes rex-byte opcode modr/m sib x86))


    (#x0E
     "(PUSH CS)"
     (x86-step-unimplemented
      (cons (ms x86)
            (list start-rip temp-rip prefixes rex-byte opcode)) x86))


    (#x0F
     "Escape to secondary opcode map."
     (two-byte-opcode-decode-and-execute start-rip temp-rip prefixes rex-byte
                                         opcode x86))


    (#x10
     "(ADC Eb Gb)"
     (x86-add/adc/sub/sbb/or/and/xor/cmp/test-E-G
      #.*OP-ADC* start-rip temp-rip prefixes rex-byte opcode modr/m sib x86))


    (#x11
     "(ADC Ev Gv)"
     (x86-add/adc/sub/sbb/or/and/xor/cmp/test-E-G
      #.*OP-ADC* start-rip temp-rip prefixes rex-byte opcode modr/m sib x86))


    (#x12
     "(ADC Gb Eb)"
     (x86-add/adc/sub/sbb/or/and/xor/cmp-G-E
      #.*OP-ADC* start-rip temp-rip prefixes rex-byte opcode modr/m sib x86))


    (#x13
     "(ADC Gv Ev)"
     (x86-add/adc/sub/sbb/or/and/xor/cmp-G-E
      #.*OP-ADC* start-rip temp-rip prefixes rex-byte opcode modr/m sib x86))


    (#x14
     "(ADC AL Ib)"
     (x86-add/adc/sub/sbb/or/and/xor/cmp-test-rAX-I
      #.*OP-ADC* start-rip temp-rip prefixes rex-byte opcode modr/m sib x86))


    (#x15
     "(ADC rAX Iz)"
     (x86-add/adc/sub/sbb/or/and/xor/cmp-test-rAX-I
      #.*OP-ADC* start-rip temp-rip prefixes rex-byte opcode modr/m sib x86))


    (#x16
     "(PUSH SS)"
     (x86-step-unimplemented
      (cons (ms x86)
            (list start-rip temp-rip prefixes rex-byte opcode)) x86))


    (#x17
     "(POP SS)"
     (x86-step-unimplemented
      (cons (ms x86)
            (list start-rip temp-rip prefixes rex-byte opcode)) x86))


    (#x18
     "(SBB Eb Gb)"
     (x86-add/adc/sub/sbb/or/and/xor/cmp/test-E-G
      #.*OP-SBB* start-rip temp-rip prefixes rex-byte opcode modr/m sib x86))


    (#x19
     "(SBB Ev Gv)"
     (x86-add/adc/sub/sbb/or/and/xor/cmp/test-E-G
      #.*OP-SBB* start-rip temp-rip prefixes rex-byte opcode modr/m sib x86))


    (#x1A
     "(SBB Gb Eb)"
     (x86-add/adc/sub/sbb/or/and/xor/cmp-G-E
      #.*OP-SBB* start-rip temp-rip prefixes rex-byte opcode modr/m sib x86))


    (#x1B
     "(SBB Gv Ev)"
     (x86-add/adc/sub/sbb/or/and/xor/cmp-G-E
      #.*OP-SBB* start-rip temp-rip prefixes rex-byte opcode modr/m sib x86))


    (#x1C
     "(SBB AL Ib)"
     (x86-add/adc/sub/sbb/or/and/xor/cmp-test-rAX-I
      #.*OP-SBB* start-rip temp-rip prefixes rex-byte opcode modr/m sib x86))


    (#x1D
     "(SBB rAX Iz)"
     (x86-add/adc/sub/sbb/or/and/xor/cmp-test-rAX-I
      #.*OP-SBB* start-rip temp-rip prefixes rex-byte opcode modr/m sib x86))


    (#x1E
     "(PUSH DS)"
     (x86-step-unimplemented
      (cons (ms x86)
            (list start-rip temp-rip prefixes rex-byte opcode)) x86))


    (#x1F
     "(POP DS)"
     (x86-step-unimplemented
      (cons (ms x86)
            (list start-rip temp-rip prefixes rex-byte opcode)) x86))


    (#x20
     "(AND Eb Gb)"
     (x86-add/adc/sub/sbb/or/and/xor/cmp/test-E-G
      #.*OP-AND* start-rip temp-rip prefixes rex-byte opcode modr/m sib x86))


    (#x21
     "(AND Ev Gv)"
     (x86-add/adc/sub/sbb/or/and/xor/cmp/test-E-G
      #.*OP-AND* start-rip temp-rip prefixes rex-byte opcode modr/m sib x86))


    (#x22
     "(AND Gb Eb)"
     (x86-add/adc/sub/sbb/or/and/xor/cmp-G-E
      #.*OP-AND* start-rip temp-rip prefixes rex-byte opcode modr/m sib x86))


    (#x23
     "(AND Gv Ev)"
     (x86-add/adc/sub/sbb/or/and/xor/cmp-G-E
      #.*OP-AND* start-rip temp-rip prefixes rex-byte opcode modr/m sib x86))


    (#x24
     "(AND AL Ib)"
     (x86-add/adc/sub/sbb/or/and/xor/cmp-test-rAX-I
      #.*OP-AND* start-rip temp-rip prefixes rex-byte opcode modr/m sib x86))


    (#x25
     "(AND rAX Iz)"
     (x86-add/adc/sub/sbb/or/and/xor/cmp-test-rAX-I
      #.*OP-AND* start-rip temp-rip prefixes rex-byte opcode modr/m sib x86))


    (#x26
     "(SEG-ES-prefix)"
     (x86-step-unimplemented
      (list* (ms x86)
             "Null prefix in 64-bit mode"
             (list start-rip temp-rip prefixes rex-byte opcode)) x86))


    (#x27
     "(DAA)"
     (x86-step-unimplemented
      (cons (ms x86)
            (list start-rip temp-rip prefixes rex-byte opcode)) x86))


    (#x28
     "(SUB Eb Gb)"
     (x86-add/adc/sub/sbb/or/and/xor/cmp/test-E-G
      #.*OP-SUB* start-rip temp-rip prefixes rex-byte opcode modr/m sib x86))


    (#x29
     "(SUB Ev Gv)"
     (x86-add/adc/sub/sbb/or/and/xor/cmp/test-E-G
      #.*OP-SUB* start-rip temp-rip prefixes rex-byte opcode modr/m sib x86))


    (#x2A
     "(SUB Gb Eb)"
     (x86-add/adc/sub/sbb/or/and/xor/cmp-G-E
      #.*OP-SUB* start-rip temp-rip prefixes rex-byte opcode modr/m sib x86))


    (#x2B
     "(SUB Gv Ev)"
     (x86-add/adc/sub/sbb/or/and/xor/cmp-G-E
      #.*OP-SUB* start-rip temp-rip prefixes rex-byte opcode modr/m sib x86))


    (#x2C
     "(SUB AL Ib)"
     (x86-add/adc/sub/sbb/or/and/xor/cmp-test-rAX-I
      #.*OP-SUB* start-rip temp-rip prefixes rex-byte opcode modr/m sib x86))


    (#x2D
     "(SUB rAX Iz)"
     (x86-add/adc/sub/sbb/or/and/xor/cmp-test-rAX-I
      #.*OP-SUB* start-rip temp-rip prefixes rex-byte opcode modr/m sib x86))


    (#x2E
     "(SEG-CS-prefix)"
     (x86-step-unimplemented
      (list* (ms x86)
             "Null prefix in 64-bit mode"
             (list start-rip temp-rip prefixes rex-byte opcode)) x86))


    (#x2F
     "(DAS)"
     (x86-step-unimplemented
      (cons (ms x86)
            (list start-rip temp-rip prefixes rex-byte opcode)) x86))


    (#x30
     "(XOR Eb Gb)"
     (x86-add/adc/sub/sbb/or/and/xor/cmp/test-E-G
      #.*OP-XOR* start-rip temp-rip prefixes rex-byte opcode modr/m sib x86))


    (#x31
     "(XOR Ev Gv)"
     (x86-add/adc/sub/sbb/or/and/xor/cmp/test-E-G
      #.*OP-XOR* start-rip temp-rip prefixes rex-byte opcode modr/m sib x86))


    (#x32
     "(XOR Gb Eb)"
     (x86-add/adc/sub/sbb/or/and/xor/cmp-G-E
      #.*OP-XOR* start-rip temp-rip prefixes rex-byte opcode modr/m sib x86))


    (#x33
     "(XOR Gv Ev)"
     (x86-add/adc/sub/sbb/or/and/xor/cmp-G-E
      #.*OP-XOR* start-rip temp-rip prefixes rex-byte opcode modr/m sib x86))


    (#x34
     "(XOR AL Ib)"
     (x86-add/adc/sub/sbb/or/and/xor/cmp-test-rAX-I
      #.*OP-XOR* start-rip temp-rip prefixes rex-byte opcode modr/m sib x86))


    (#x35
     "(XOR rAX Iz)"
     (x86-add/adc/sub/sbb/or/and/xor/cmp-test-rAX-I
      #.*OP-SUB* start-rip temp-rip prefixes rex-byte opcode modr/m sib x86))


    (#x36
     "(SEG-SS-prefix)"
     (x86-step-unimplemented
      (list* (ms x86)
             "Null prefix in 64-bit mode"
             (list start-rip temp-rip prefixes rex-byte opcode)) x86))


    (#x37
     "(AAA)"
     (x86-step-unimplemented
      (cons (ms x86)
            (list start-rip temp-rip prefixes rex-byte opcode)) x86))


    (#x38
     "(CMP Eb Gb)"
     (x86-add/adc/sub/sbb/or/and/xor/cmp/test-E-G
      #.*OP-CMP* start-rip temp-rip prefixes rex-byte opcode modr/m sib x86))


    (#x39
     "(CMP Ev Gv)"
     (x86-add/adc/sub/sbb/or/and/xor/cmp/test-E-G
      #.*OP-CMP* start-rip temp-rip prefixes rex-byte opcode modr/m sib x86))


    (#x3A
     "(CMP Gb Eb)"
     (x86-add/adc/sub/sbb/or/and/xor/cmp-G-E
      #.*OP-CMP* start-rip temp-rip prefixes rex-byte opcode modr/m sib x86))


    (#x3B
     "(CMP Gv Ev)"
     (x86-add/adc/sub/sbb/or/and/xor/cmp-G-E
      #.*OP-CMP* start-rip temp-rip prefixes rex-byte opcode modr/m sib x86))


    (#x3C
     "(CMP AL Ib)"
     (x86-add/adc/sub/sbb/or/and/xor/cmp-test-rAX-I
      #.*OP-CMP* start-rip temp-rip prefixes rex-byte opcode modr/m sib x86))


    (#x3D
     "(CMP rAX Iz)"
     (x86-add/adc/sub/sbb/or/and/xor/cmp-test-rAX-I
      #.*OP-CMP* start-rip temp-rip prefixes rex-byte opcode modr/m sib x86))


    (#x3E
     "(SEG-DS-prefix)"
     (x86-step-unimplemented
      (list* (ms x86)
             "Null prefix in 64-bit mode"
             (list start-rip temp-rip prefixes rex-byte opcode)) x86))


    (#x3F
     "(AAS)"
     (x86-step-unimplemented
      (cons (ms x86)
            (list start-rip temp-rip prefixes rex-byte opcode)) x86))

    ((#x40 #x41 #x42 #x43
           #x44 #x45 #x46 #x47
           #x48 #x49 #x4A #x4B
           #x4C #x4D #x4E #x4F)
     "REX prefixes"
     (x86-step-unimplemented
      (list* (ms x86)
             "REX prefix in 64-bit mode"
             (list start-rip temp-rip prefixes rex-byte opcode)) x86))


    (#x50
     "(PUSH rAX/r8)"
     (x86-push-general-register start-rip temp-rip prefixes rex-byte opcode modr/m
                                sib x86))


    (#x51
     "(Push rCX/r9)"
     (x86-push-general-register start-rip temp-rip prefixes rex-byte opcode modr/m
                                sib x86))


    (#x52
     "(PUSH rDX/r10)"
     (x86-push-general-register start-rip temp-rip prefixes rex-byte opcode modr/m
                                sib x86))


    (#x53
     "(PUSH rBX/r11)"
     (x86-push-general-register start-rip temp-rip prefixes rex-byte opcode modr/m
                                sib x86))


    (#x54
     "(PUSH rSP/r12)"
     (x86-push-general-register start-rip temp-rip prefixes rex-byte opcode modr/m
                                sib x86))


    (#x55
     "(PUSH rBP/r13)"
     (x86-push-general-register start-rip temp-rip prefixes rex-byte opcode modr/m
                                sib x86))


    (#x56
     "(PUSH rSI/r14)"
     (x86-push-general-register start-rip temp-rip prefixes rex-byte opcode modr/m
                                sib x86))


    (#x57
     "(PUSH rDI/r15)"
     (x86-push-general-register start-rip temp-rip prefixes rex-byte opcode modr/m
                                sib x86))


    (#x58
     "(POP rAX/r8)"
     (x86-pop-general-register start-rip temp-rip prefixes rex-byte opcode modr/m
                               sib x86))


    (#x59
     "(POP rCX/r9)"
     (x86-pop-general-register start-rip temp-rip prefixes rex-byte opcode modr/m
                               sib x86))


    (#x5A
     "(POP rDX/r10)"
     (x86-pop-general-register start-rip temp-rip prefixes rex-byte opcode modr/m
                               sib x86))


    (#x5B
     "(POP rBX/r11)"
     (x86-pop-general-register start-rip temp-rip prefixes rex-byte opcode modr/m
                               sib x86))


    (#x5C
     "(POP rSP/r12)"
     (x86-pop-general-register start-rip temp-rip prefixes rex-byte opcode modr/m
                               sib x86))


    (#x5D
     "(POP rBP/r13)"
     (x86-pop-general-register start-rip temp-rip prefixes rex-byte opcode modr/m
                               sib x86))


    (#x5E
     "(POP rSI/r14)"
     (x86-pop-general-register start-rip temp-rip prefixes rex-byte opcode modr/m
                               sib x86))


    (#x5F
     "(POP rDI/r15)"
     (x86-pop-general-register start-rip temp-rip prefixes rex-byte opcode modr/m
                               sib x86))


    (#x60
     "(PUSHA) or (PUSHAD) Invalid in 64-bit mode."
     (x86-step-unimplemented
      (cons (ms x86)
            (list start-rip temp-rip prefixes rex-byte opcode)) x86))


    (#x61
     "(POPA) or (POPAD) Invalid in 64-bit mode."
     (x86-step-unimplemented
      (cons (ms x86)
            (list start-rip temp-rip prefixes rex-byte opcode)) x86))

    (#x62
     "(BOUND Gv Ma) Invalid in 64-bit mode."
     (x86-step-unimplemented
      (cons (ms x86)
            (list start-rip temp-rip prefixes rex-byte opcode)) x86))

    (#x63
     "(MOVSXD Gv Ev) and (ARPL Ew Gw).  However, the latter is invalid in
       64-bit mode."
     (x86-one-byte-movsxd start-rip temp-rip prefixes rex-byte opcode modr/m
                          sib x86))


    (#x64
     "(SEG-FS-prefix)"
     (x86-step-unimplemented
      (list* (ms x86)
             "Null prefix in 64-bit mode"
             (list start-rip temp-rip prefixes rex-byte opcode)) x86))


    (#x65
     "(SEG-GS-prefix)"
     (x86-step-unimplemented
      (list* (ms x86)
             "Null prefix in 64-bit mode"
             (list start-rip temp-rip prefixes rex-byte opcode)) x86))


    (#x66
     "(OPERAND-SIZE-prefix)"
     (x86-step-unimplemented
      (list* (ms x86)
             "Operand-Size Override Prefix in 64-bit mode"
             (list start-rip temp-rip prefixes rex-byte opcode)) x86))


    (#x67
     "(ADDRESS-SIZE-prefix)"
     (x86-step-unimplemented
      (list* (ms x86)
             "Address-Size Override Prefix in 64-bit mode"
             (list start-rip temp-rip prefixes rex-byte opcode)) x86))


    (#x68
     "(PUSH lz)"
     (x86-push-I start-rip temp-rip prefixes rex-byte opcode modr/m
                 sib x86))

    (#x69
     "(IMUL Gv Ev iz)"
     (x86-imul-Op/En-RMI start-rip temp-rip prefixes rex-byte opcode
                         modr/m sib x86))


    (#x6A
     "(PUSH lb)"
     (x86-push-I start-rip temp-rip prefixes rex-byte opcode modr/m
                 sib x86))

    (#x6B
     "(IMUL Gv Ev ib)"
     (x86-imul-Op/En-RMI start-rip temp-rip prefixes rex-byte opcode
                         modr/m sib x86))

    (#x6C
     "(INS Yb DX) or (INSB Yb DX)"
     (x86-step-unimplemented
      (cons (ms x86)
            (list start-rip temp-rip prefixes rex-byte opcode)) x86))



    (#x6D
     "(INS Yz DX) or (INSW Yz DX) or (INSD Yz DX)"
     (x86-step-unimplemented
      (cons (ms x86)
            (list start-rip temp-rip prefixes rex-byte opcode)) x86))

    (#x6E
     "(OUTS DX Xb) or (OUTSB DX Xb)"
     (x86-step-unimplemented
      (cons (ms x86)
            (list start-rip temp-rip prefixes rex-byte opcode)) x86))



    (#x6F
     "(OUTS DX Xz) or (OUTSW DX Xz) or (OUTSW DX Xz)"
     (x86-step-unimplemented
      (cons (ms x86)
            (list start-rip temp-rip prefixes rex-byte opcode)) x86))


    ((#x70 #x71 #x72 #x73 #x74 #x75 #x76 #x77 #x78 #x79 #x7A #x7B
           #x7C #x7D #x7E #x7F)
     "(Jcc Jb)"
     (x86-one-byte-jcc start-rip temp-rip prefixes rex-byte opcode modr/m
                       sib x86))

    (#x80
     "(GRP1 Eb Ib): Opcode-extension: Modr/m.reg
      0:(ADD Eb Ib); 1:(OR Eb Ib);  2:(ADC Eb Ib); 3:(SBB Eb Ib)
      4:(AND Eb Ib); 5:(SUB Eb Ib); 6:(XOR Eb Ib); 7:(CMP Eb Ib)"
     (case (mrm-reg ModR/M)
       (#x0
        (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
         #.*OP-ADD* start-rip temp-rip prefixes rex-byte opcode modr/m sib
         x86))

       (#x1
        (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
         #.*OP-OR* start-rip temp-rip prefixes rex-byte opcode modr/m sib
         x86))

       (#x2
        (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
         #.*OP-ADC* start-rip temp-rip prefixes rex-byte opcode modr/m sib
         x86))

       (#x3
        (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
         #.*OP-SBB* start-rip temp-rip prefixes rex-byte opcode modr/m sib
         x86))


       (#x4
        (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
         #.*OP-AND* start-rip temp-rip prefixes rex-byte opcode modr/m sib
         x86))


       (#x5
        (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
         #.*OP-SUB* start-rip temp-rip prefixes rex-byte opcode modr/m sib
         x86))


       (#x6
        (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
         #.*OP-XOR* start-rip temp-rip prefixes rex-byte opcode modr/m sib
         x86))


       (#x7
        (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
         #.*OP-CMP* start-rip temp-rip prefixes rex-byte opcode modr/m sib
         x86))

       (otherwise
        (x86-step-unimplemented (mrm-reg ModR/M) x86))
       ))


    (#x81
     "(GRP1 Ev Iv): Opcode-extension: Modr/m.reg
      0:(ADD Ev Iv); 1:(OR Ev Iv);  2:(ADC Ev Iv); 3:(SVV Ev Iv)
      4:(AND Ev Iv); 5:(SUV Ev Iv); 6:(XOR Ev Iv); 7:(CMP Ev Iv)"
     (case (mrm-reg ModR/M)

       (#x0
        (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
         #.*OP-ADD* start-rip temp-rip prefixes rex-byte opcode modr/m sib
         x86))


       (#x1
        (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
         #.*OP-OR* start-rip temp-rip prefixes rex-byte opcode modr/m sib
         x86))


       (#x2
        (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
         #.*OP-ADC* start-rip temp-rip prefixes rex-byte opcode modr/m sib
         x86))


       (#x3
        (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
         #.*OP-SBB* start-rip temp-rip prefixes rex-byte opcode modr/m sib
         x86))


       (#x4
        (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
         #.*OP-AND* start-rip temp-rip prefixes rex-byte opcode modr/m sib
         x86))


       (#x5
        (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
         #.*OP-SUB* start-rip temp-rip prefixes rex-byte opcode modr/m sib
         x86))


       (#x6
        (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
         #.*OP-XOR* start-rip temp-rip prefixes rex-byte opcode modr/m sib
         x86))


       (#x7
        (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
         #.*OP-CMP* start-rip temp-rip prefixes rex-byte opcode modr/m sib
         x86))

       (otherwise
        (x86-step-unimplemented (mrm-reg ModR/M) x86))
       ))


    (#x82
     "Invalid in 64-bit mode."
     (x86-step-unimplemented
      (list* (ms x86)
             "Invalid opcode in 64-bit mode"
             (list start-rip temp-rip prefixes rex-byte opcode))
      x86))


    (#x83
     "(GRP1 Ev Ib): Opcode-extension: Modr/m.reg
      0:(ADD Ev Ib); 1:(OR Ev Ib);  2:(ADC Ev Ib); 3:(SBB Ev Ib)
      4:(AND Ev Ib); 5:(SUB Ev Ib); 6:(XOR Ev Ib); 7:(CMP Ev Ib)"
     (case (mrm-reg ModR/M)

       (#x0
        (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
         #.*OP-ADD* start-rip temp-rip prefixes rex-byte opcode modr/m sib
         x86))


       (#x1
        (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
         #.*OP-OR* start-rip temp-rip prefixes rex-byte opcode modr/m sib
         x86))


       (#x2
        (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
         #.*OP-ADC* start-rip temp-rip prefixes rex-byte opcode modr/m sib
         x86))


       (#x3
        (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
         #.*OP-SBB* start-rip temp-rip prefixes rex-byte opcode modr/m sib
         x86))


       (#x4
        (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
         #.*OP-AND* start-rip temp-rip prefixes rex-byte opcode modr/m sib
         x86))


       (#x5
        (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
         #.*OP-SUB* start-rip temp-rip prefixes rex-byte opcode modr/m sib
         x86))


       (#x6
        (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
         #.*OP-XOR* start-rip temp-rip prefixes rex-byte opcode modr/m sib
         x86))


       (#x7
        (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
         #.*OP-CMP* start-rip temp-rip prefixes rex-byte opcode modr/m sib
         x86))

       (otherwise
        (x86-step-unimplemented (mrm-reg ModR/M) x86))
       ))


    (#x84
     "(TEST Eb Gb)"
     (x86-add/adc/sub/sbb/or/and/xor/cmp/test-E-G
      #.*OP-TEST* start-rip temp-rip prefixes rex-byte opcode modr/m sib
      x86))


    (#x85
     "(TEST Ev Gv)"
     (x86-add/adc/sub/sbb/or/and/xor/cmp/test-E-G
      #.*OP-TEST* start-rip temp-rip prefixes rex-byte opcode modr/m sib x86))

    ((#x86 #x87)
     "#x86: (XCHG Eb Gb) #x87: (XCHG Ev Gv)"
     (x86-xchg start-rip temp-rip prefixes rex-byte opcode modr/m sib
               x86))


    (#x88
     "(MOV Eb Gb)"
     (x86-mov-Op/En-MR start-rip temp-rip prefixes rex-byte opcode
                       modr/m sib x86))


    (#x89
     "(MOV Ev Gv)"
     (x86-mov-Op/En-MR start-rip temp-rip prefixes rex-byte opcode
                       modr/m sib x86))


    (#x8A
     "(MOV Gb Eb)"
     (x86-mov-Op/En-RM start-rip temp-rip prefixes rex-byte opcode
                       modr/m sib x86))


    (#x8B
     "(MOV Gv Ev)"
     (x86-mov-Op/En-RM start-rip temp-rip prefixes rex-byte opcode
                       modr/m sib x86))


    (#x8C
     "(MOV Ev Sw)  Special MOVE instruction for segment registers"
     (x86-step-unimplemented
      (cons (ms x86)
            (list start-rip temp-rip prefixes rex-byte opcode)) x86))



    (#x8D
     "(LEA Gv M)"
     (x86-lea start-rip temp-rip prefixes rex-byte opcode
              modr/m sib x86))


    (#x8E
     "(MOV Sw Ew)  Like #x8C.  Weird Ew/Ev difference with #8C"
     (x86-step-unimplemented
      (cons (ms x86)
            (list start-rip temp-rip prefixes rex-byte opcode)) x86))


    (#x8F
     "Group 1A: Opcode-extension: Modr/m.reg
      0:(POP Ev) Otherwise:XOP encoding (unimplemented)"
     (case (mrm-reg ModR/M)

       (#x0
        (x86-pop-Ev start-rip temp-rip prefixes rex-byte
                    opcode modr/m sib x86))

       (otherwise
        (x86-step-unimplemented
         (cons (ms x86)
               (list "XOP instructions have not been implemented yet."
                     start-rip temp-rip prefixes rex-byte opcode))
         x86))))


    (#x90
     "#x90:  (XCHG rAX/R8) or (NOP) or (PAUSE)"
     (x86-nop start-rip temp-rip prefixes rex-byte opcode
              modr/m sib x86))


    ((#x91 #x92 #x93 #x94 #x95 #x96 #x97)
     "#x91 -- #x97:  (XCHG .. ..)"
     (x86-xchg start-rip temp-rip prefixes rex-byte opcode modr/m sib
               x86))


    (#x98
     "(CWB) or (CWDE) or (CDQE)"
     (x86-cbw/cwd/cdqe start-rip temp-rip prefixes rex-byte opcode modr/m
                       sib x86))


    (#x99
     "(CWD) or (CDQ) or (CQO)"
     (x86-cwd/cdq/cqo start-rip temp-rip prefixes rex-byte opcode modr/m
                      sib x86))


    (#x9A
     "Invalid in 64-bit mode."
     (x86-step-unimplemented
      (list* (ms x86)
             (list start-rip temp-rip prefixes rex-byte opcode)) x86))


    (#x9B
     "(FWAIT) -- for our model, this can be a NOP."
     (x86-step-unimplemented
      (list* (ms x86)
             (list start-rip temp-rip prefixes rex-byte opcode)) x86))


    (#x9C
     "(PUSHF d64 Fv) or (PUSHD d64 Fv) or (PUSHQ d64 Fv)"
     (x86-pushf start-rip temp-rip prefixes rex-byte opcode modr/m sib
                x86))


    (#x9D
     "(POPF d64 Fv) or (POPD d64 Fv) or (POPQ d64 Fv)"
     (x86-popf start-rip temp-rip prefixes rex-byte opcode modr/m sib
               x86))


    (#x9E
     "(SAHF)"
     (x86-sahf start-rip temp-rip prefixes rex-byte opcode modr/m sib
               x86))


    (#x9F
     "(LAHF)"
     (x86-lahf start-rip temp-rip prefixes rex-byte opcode modr/m sib
               x86))


    ((#xA0 #xA1 #xA2 #xA3)
     "(MOVI b Rx)"
     (x86-step-unimplemented
      (list* (ms x86)
             "MOVI instructions not yet implemented."
             (list start-rip temp-rip prefixes rex-byte opcode)) x86))

    ((#xA4 #xA5)
     "MOVS; A4: (MOVSB Yb, Xb); A5: (MOVSW/D/Q Yv, Xv)"
     (x86-movs start-rip temp-rip prefixes rex-byte opcode modr/m sib
               x86))

    ((#xA6 #xA7)
     " CMPS; A6: (CMPSB Xb, Yb); A7: (CMPSW/D/Q Xv, Yv)"
     (x86-cmps start-rip temp-rip prefixes rex-byte opcode modr/m sib
               x86))


    (#xA8
     "(TEST AL Ib)"
     (x86-add/adc/sub/sbb/or/and/xor/cmp-test-rAX-I
      #.*OP-TEST* start-rip temp-rip prefixes rex-byte opcode modr/m sib
      x86))


    (#xA9
     "(TEST rAX Iz)"
     (x86-add/adc/sub/sbb/or/and/xor/cmp-test-rAX-I
      #.*OP-TEST* start-rip temp-rip prefixes rex-byte opcode modr/m sib
      x86))


    (#xAA
     "(STOSB Yb AL)"
     (x86-stos start-rip temp-rip prefixes rex-byte opcode modr/m sib
               x86))


    (#xAB
     "(STOSW Yv rAX) or (STOSD Yv rAX) or (STOSQ Yv rAX)"
     (x86-stos start-rip temp-rip prefixes rex-byte opcode modr/m sib
               x86))


    (#xAC
     "(LODSB AL, Xb)"
     (x86-step-unimplemented
      (list* (ms x86)
             "LODSB instruction not yet implemented."
             (list start-rip temp-rip prefixes rex-byte opcode)) x86))


    (#xAD
     "(LODSW rAX, Xv) or (LODSD rAX, Xv) or (LODSQ rAX, Xv)"
     (x86-step-unimplemented
      (list* (ms x86)
             "LODSW, LODSD, LODSQ instructions not yet implemented."
             (list start-rip temp-rip prefixes rex-byte opcode)) x86))


    (#xAE
     "(SCASB AL, Xb)"
     (x86-step-unimplemented
      (list* (ms x86)
             "SCASB instruction not yet implemented."
             (list start-rip temp-rip prefixes rex-byte opcode)) x86))


    (#xAF
     "(SCASW rAX, Xv) or (SCASD rAX, Xv) or (SCASQ rAX, Xv)"
     (x86-step-unimplemented
      (list* (ms x86)
             "SCASW, SCASD, SCASQ instructions not yet implemented."
             (list start-rip temp-rip prefixes rex-byte opcode)) x86))


    (#xB0
     "(MOV AL/R8L lb)"
     (x86-mov-Op/En-OI start-rip temp-rip prefixes rex-byte opcode
                       modr/m sib x86))


    (#xB1
     "(MOV CL/R9L lb)"
     (x86-mov-Op/En-OI start-rip temp-rip prefixes rex-byte opcode
                       modr/m sib x86))


    (#xB2
     "(MOV DL/R10L lb)"
     (x86-mov-Op/En-OI start-rip temp-rip prefixes rex-byte opcode
                       modr/m sib x86))


    (#xB3
     "(MOV BL/R11L lb)"
     (x86-mov-Op/En-OI start-rip temp-rip prefixes rex-byte opcode
                       modr/m sib x86))


    (#xB4
     "(MOV AH/R12L lb)"
     (x86-mov-Op/En-OI start-rip temp-rip prefixes rex-byte opcode
                       modr/m sib x86))


    (#xB5
     "(MOV CH/R13L lb)"
     (x86-mov-Op/En-OI start-rip temp-rip prefixes rex-byte opcode
                       modr/m sib x86))


    (#xB6
     "(MOV DH/R14L lb)"
     (x86-mov-Op/En-OI start-rip temp-rip prefixes rex-byte opcode
                       modr/m sib x86))


    (#xB7
     "(MOV BH/R15L lb)"
     (x86-mov-Op/En-OI start-rip temp-rip prefixes rex-byte opcode
                       modr/m sib x86))



    (#xB8
     "(MOV AL/R8L lb)"
     (x86-mov-Op/En-OI start-rip temp-rip prefixes rex-byte opcode
                       modr/m sib x86))


    (#xB9
     "(MOV CL/R9L lb)"
     (x86-mov-Op/En-OI start-rip temp-rip prefixes rex-byte opcode
                       modr/m sib x86))


    (#xBA
     "(MOV DL/R10L lb)"
     (x86-mov-Op/En-OI start-rip temp-rip prefixes rex-byte opcode
                       modr/m sib x86))


    (#xBB
     "(MOV BL/R11L lb)"
     (x86-mov-Op/En-OI start-rip temp-rip prefixes rex-byte opcode
                       modr/m sib x86))


    (#xBC
     "(MOV AH/R12L lb)"
     (x86-mov-Op/En-OI start-rip temp-rip prefixes rex-byte opcode
                       modr/m sib x86))


    (#xBD
     "(MOV CH/R13L lb)"
     (x86-mov-Op/En-OI start-rip temp-rip prefixes rex-byte opcode
                       modr/m sib x86))


    (#xBE
     "(MOV DH/R14L lb)"
     (x86-mov-Op/En-OI start-rip temp-rip prefixes rex-byte opcode
                       modr/m sib x86))


    (#xBF
     "(MOV BH/R15L lb)"
     (x86-mov-Op/En-OI start-rip temp-rip prefixes rex-byte opcode
                       modr/m sib x86))

    ((#xC0 #xC1)
     "Shift Group 2; C0: (GRP2 Eb Ib); C1: (GRP2 Ev Ib);
      Opcode-extension: Modr/m.reg
      0-5,7: sal/sar/shl/shr/rcl/rcr/rol/ror
      Otherwise: Unimplemented"
     (case (mrm-reg ModR/M)
       ((0 1 2 3 4 5 7)
        (x86-sal/sar/shl/shr/rcl/rcr/rol/ror start-rip temp-rip prefixes
                                             rex-byte opcode modr/m sib
                                             x86))
       (otherwise
        (x86-step-unimplemented
         (list* (ms x86)
                (list
                 "Instruction not implemented yet"
                 start-rip temp-rip prefixes rex-byte opcode)) x86))))

    (#xC2
     "(RETN lw)"
     (x86-ret start-rip temp-rip prefixes rex-byte opcode
              modr/m sib x86))


    (#xC3
     "(RETN)"
     (x86-ret start-rip temp-rip prefixes rex-byte opcode
              modr/m sib x86))


    ((#xC4 #xC5)
     "Escape to VEX opcode map"
     (x86-step-unimplemented
      (list* (ms x86)
             (list
              "VEX instructions have not been implemented yet"
              start-rip temp-rip prefixes rex-byte opcode)) x86))

    (#xC6
     "Group 11 - MOV: Opcode-extension: Modr/m.reg
     0:(MOV Eb Ib); Otherwise: <blank>"
     (case (mrm-reg ModR/M)

       (#x0
        (x86-mov-Op/En-MI start-rip temp-rip prefixes rex-byte opcode
                          modr/m sib x86))

       (otherwise
        (x86-step-unimplemented (cons (ms x86)
                                      (list start-rip temp-rip
                                            prefixes rex-byte
                                            opcode))
                                x86))))


    (#xC7
     "Group 1 - MOV: Opcode-extension: Modr/m.reg
      0:(MOV Ev Iz); Otherwise: <blank>"
     (case (mrm-reg ModR/M)

       (#x0
        (x86-mov-Op/En-MI start-rip temp-rip prefixes rex-byte opcode
                          modr/m sib x86))

       (otherwise
        (x86-step-unimplemented (cons (ms x86)
                                      (list start-rip temp-rip
                                            prefixes rex-byte
                                            opcode))
                                x86))))


    (#xC9
     "(LEAVE)"
     (x86-leave start-rip temp-rip prefixes rex-byte opcode modr/m sib
                x86))


    ((#xD0 #xD1 #xD2 #xD3)
     "Shift Group 2; Opcode-extension: Modr/m.reg
      0-5,7:sal/sar/shl/shr/rcl/rcr/rol/ror; Otherwise: unimplemented
      Opcodes: D0-D3
      D0: (GRP2 Eb 1);   D1: (GRP2 Ev, 1);
      D2: (GRP2 Eb, CL); D3: (GRP2 Ev, CL)"
     (case (mrm-reg ModR/M)
       ((0 1 2 3 4 5 7)
        (x86-sal/sar/shl/shr/rcl/rcr/rol/ror start-rip temp-rip prefixes
                                             rex-byte opcode modr/m sib
                                             x86))

       (otherwise
        (x86-step-unimplemented (cons (ms x86)
                                      (list start-rip temp-rip
                                            prefixes rex-byte
                                            opcode))
                                x86))))


    ((#xE0 #xE1 #xE2)
     "E0: (LOOPNE/NZ Jb); E1: (LOOPE/Z Jb); E2: (LOOP Jb)"
     (x86-loop start-rip temp-rip prefixes rex-byte opcode modr/m sib
               x86))


    (#xE3
     "(JrCXZ Jb)"
     (x86-jrcxz start-rip temp-rip prefixes rex-byte opcode modr/m sib
                x86))


    (#xE8
     "(CALL Jz)"
     (x86-call-E8-Op/En-M start-rip temp-rip prefixes rex-byte opcode
                          modr/m sib x86))


    (#xE9
     "(JMP near Jz)"
     (x86-near-jmp-Op/En-D start-rip temp-rip prefixes rex-byte opcode modr/m
                      sib x86))

    (#xEA
     "Undefined Opcode in 64-bit Mode (used to be direct far jump in other modes)"
     (x86-step-unimplemented (cons (ms x86)
                                   (list start-rip temp-rip
                                         prefixes rex-byte
                                         opcode))
                             x86))


    (#xEB
     "(JMP short Jb)"
     (x86-near-jmp-Op/En-D start-rip temp-rip prefixes rex-byte opcode modr/m
                      sib x86))


    (#xF4
     "(HLT)"
     (x86-hlt start-rip temp-rip prefixes rex-byte opcode modr/m sib
              x86))


    (#xF5
     "(CMC)"
     (x86-cmc/clc/stc/cld/std start-rip temp-rip prefixes rex-byte opcode
                              modr/m sib x86))


    (#xF6
     "(GRP3 Eb): Opcode-extension: Modr/m.reg
      0,1:(TEST Eb); 2,3:(NOT Eb); 4:(MUL Eb); 5:(IMUL Eb)
      6:(DIV Eb); 7:(IDIV Eb)"
     (case (mrm-reg ModR/M)

       ((#x0 #x1)
        (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
         #.*OP-TEST* start-rip temp-rip prefixes rex-byte opcode modr/m sib
         x86))


       ((#x2 #x3)
        (x86-not/neg-F6-F7 start-rip temp-rip prefixes rex-byte opcode
                           modr/m sib x86))


       (#x4
        (x86-mul start-rip temp-rip prefixes rex-byte opcode modr/m sib
                 x86))


       (#x5
        (x86-imul-Op/En-M start-rip temp-rip prefixes rex-byte opcode
                          modr/m sib x86))


       (#x6
        (x86-div start-rip temp-rip prefixes rex-byte opcode modr/m sib
                 x86))

       (#x7
        (x86-idiv start-rip temp-rip prefixes rex-byte opcode modr/m sib
                  x86))

       (otherwise
        (x86-step-unimplemented (cons (ms x86)
                                      (list start-rip temp-rip
                                            prefixes rex-byte
                                            opcode))
                                x86))))


    (#xF7
     "(GRP3 Ev): Opcode-extension: Modr/m.reg
      0,1:(TEST Ev); 2,3:(NOT Ev); 4:(MUL Ev); 5:(IMUL Ev)
      6:(DIV Ev); 7:(IDIV Ev)"
     (case (mrm-reg ModR/M)

       (#x0
        (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
         #.*OP-TEST* start-rip temp-rip prefixes rex-byte opcode modr/m sib
         x86))


       ((#x2 #x3)
        (x86-not/neg-F6-F7 start-rip temp-rip prefixes rex-byte opcode
                           modr/m sib x86))


       (#x4
        (x86-mul start-rip temp-rip prefixes rex-byte opcode modr/m sib
                 x86))


       (#x5
        (x86-imul-Op/En-M start-rip temp-rip prefixes rex-byte opcode
                          modr/m sib x86))


       (#x6
        (x86-div start-rip temp-rip prefixes rex-byte opcode modr/m sib
                 x86))

       (#x7
        (x86-idiv start-rip temp-rip prefixes rex-byte opcode modr/m sib
                  x86))

       (otherwise
        (x86-step-unimplemented (cons (ms x86)
                                      (list start-rip temp-rip
                                            prefixes rex-byte
                                            opcode))
                                x86))))

    ((#xF8 #xF9 #xFC #xFD)
     "F8: CLC; F9: STC; #xFC CLD; $xFD: STD"
     (x86-cmc/clc/stc/cld/std start-rip temp-rip prefixes rex-byte opcode
                              modr/m sib x86))


    (#xFE
     "(GRP4 INC/DEC Eb): Opcode-extension: Modr/m.reg
      0:(INC Eb); 1:(DEC Eb); Otherwise:unimplemented"
     (case (mrm-reg ModR/M)

       (#x0
        (x86-inc/dec-FE-FF start-rip temp-rip prefixes rex-byte
                           opcode modr/m sib x86))


       (#x1
        (x86-inc/dec-FE-FF start-rip temp-rip prefixes rex-byte
                           opcode modr/m sib x86))

       (otherwise
        (x86-step-unimplemented (cons (ms x86)
                                      (list start-rip temp-rip
                                            prefixes rex-byte
                                            opcode))
                                x86))))




    (#xFF
     "(GRP5 INC/DEC Ev): Opcode-extension: Modr/m.reg
      0:(INC Ev);   1:(DEC Ev); 2:(CALLN Ev);
      4:(JUMPN Ev);             6:(PUSH Ev);
      Otherwise:unimplemented"
     (case (mrm-reg ModR/M)

       (#x0
        (x86-inc/dec-FE-FF start-rip temp-rip prefixes rex-byte
                           opcode modr/m sib x86))


       (#x1
        (x86-inc/dec-FE-FF start-rip temp-rip prefixes rex-byte
                           opcode modr/m sib x86))



       (#x2
        (x86-call-FF/2-Op/En-M start-rip temp-rip prefixes rex-byte
                               opcode modr/m sib x86))


       (#x4
        (x86-near-jmp-Op/En-M start-rip temp-rip prefixes rex-byte opcode
                              modr/m sib x86))


       (#x5
        (x86-far-jmp-Op/En-D start-rip temp-rip prefixes rex-byte opcode
                             modr/m sib x86))


       (#x6
        (x86-push-Ev start-rip temp-rip prefixes rex-byte
                     opcode modr/m sib x86))


       (otherwise
        (x86-step-unimplemented (mrm-reg ModR/M) x86))))


    (otherwise
     "This branch should not be reached."
     (x86-step-unimplemented (cons (ms x86)
                                   (list start-rip temp-rip
                                         prefixes rex-byte
                                         opcode))
                             x86))))

(defconst *two-byte-op-list*

  ;; Shilpi to Cuong: I have commented out the cases where FP
  ;; instructions are used since their spec functions haven't been
  ;; ported over yet.  Also, check the args of these functions ---
  ;; some boolean values might need to be converted to integers (e.g.,
  ;; sp/dp field).

  ;; This constant will be used to construct the case statement for
  ;; opcode-execute.  Each element of the list below is a
  ;; three-element list --- the first element is the opcode, the
  ;; second is a string that contains some useful information about
  ;; that opcode, and the third is either another case/cond statement
  ;; if there is an opcode-extension or it is a call to the function
  ;; implementing that instruction.


  `((#x00
     "LLDT: 0F 00/2"
     (case (mrm-reg modr/m)
       (2
        (if (programmer-level-mode x86)
            (x86-step-unimplemented
             (cons (cons "LLDT is not implemented in Programmer-level Mode!"
                         (ms x86))
                   (list start-rip temp-rip prefixes rex-byte opcode))
             x86)
          (x86-lldt start-rip temp-rip prefixes rex-byte opcode
                    modr/m sib x86)))
       (t
        (x86-step-unimplemented
         (cons (ms x86)
               (list start-rip temp-rip prefixes rex-byte opcode))
         x86))))

    (#x01
     "LGDT: 0F 01/2
      LIDT: 0F 01/3"
     (case (mrm-reg modr/m)
       (2
        (if (programmer-level-mode x86)
            (x86-step-unimplemented
             (cons (cons "LGDT is not implemented in Programmer-level Mode!"
                         (ms x86))
                   (list start-rip temp-rip prefixes rex-byte opcode))
             x86)
          (x86-lgdt start-rip temp-rip prefixes rex-byte opcode
                    modr/m sib x86)))
       (3
        (if (programmer-level-mode x86)
            (x86-step-unimplemented
             (cons (cons "LIDT is not supported in Programmer-level Mode!"
                         (ms x86))
                   (list start-rip temp-rip prefixes rex-byte opcode))
             x86)
          (x86-lidt start-rip temp-rip prefixes rex-byte opcode
                    modr/m sib x86)))
       (t
        (x86-step-unimplemented
         (cons (ms x86)
               (list start-rip temp-rip prefixes rex-byte opcode))
         x86))))

    (#x05
     "(SYSCALL)"
     (if (programmer-level-mode x86)
         (x86-syscall-programmer-level-mode
          start-rip temp-rip prefixes rex-byte opcode modr/m sib x86)
       (x86-syscall
        start-rip temp-rip prefixes rex-byte opcode modr/m sib x86)))

    (#x07
     "(SYSRET)"
     (if (programmer-level-mode x86)
         (x86-step-unimplemented
          (cons (cons "SYSRET is not supported in Programmer-level Mode!"
                      (ms x86))
                (list start-rip temp-rip prefixes rex-byte opcode))
          x86)
       (x86-sysret
        start-rip temp-rip prefixes rex-byte opcode modr/m sib x86)))

    ;; (#x10
    ;;  "F2h: (MOVSD xmm1 xmm2/m64);
    ;;   F3h: (MOVSS xmm1 xmm2/m32);
    ;;   66h: (MOVUPD xmm1 xmm2/m128)"
    ;;  (cond
    ;;   ((eql #.*mandatory-f2h* (prefixes-slice :group-1-prefix prefixes))
    ;;    (x86-movss/movsd-Op/En-RM t start-rip temp-rip prefixes rex-byte
    ;;                              opcode modr/m sib x86))

    ;;   ((eql #.*mandatory-f3h* (prefixes-slice :group-1-prefix prefixes))
    ;;    (x86-movss/movsd-Op/En-RM nil start-rip temp-rip prefixes rex-byte
    ;;                              opcode modr/m sib x86))

    ;;   ((eql #.*mandatory-66h* (prefixes-slice :group-3-prefix prefixes))
    ;;    (x86-movups/movupd/movdqu-Op/En-RM start-rip temp-rip prefixes rex-byte
    ;;                                       opcode modr/m sib x86))
    ;;   (t
    ;;    (x86-step-unimplemented
    ;;     (list 'Mandatory-prefixes
    ;;           (ms x86)
    ;;           start-rip temp-rip prefixes rex-byte opcode)
    ;;     x86))))

    ;; (#x11
    ;;  "F2h: (MOVSD xmm2/m64 xmm1);
    ;;   F3h: (MOVSS xmm2/m32 xmm1);
    ;;   66h: (MOVUPD xmm2/m128 xmm1)"
    ;;  (cond

    ;;   ((eql #.*mandatory-f2h* (prefixes-slice :group-1-prefix prefixes))
    ;;    (x86-movss/movsd-Op/En-MR t start-rip temp-rip prefixes rex-byte
    ;;                              opcode modr/m sib x86))

    ;;   ((eql #.*mandatory-f3h* (prefixes-slice :group-1-prefix prefixes))
    ;;    (x86-movss/movsd-Op/En-MR nil start-rip temp-rip prefixes rex-byte
    ;;                              opcode modr/m sib x86))

    ;;   ((eql #.*mandatory-66h* (prefixes-slice :group-3-prefix prefixes))
    ;;    (x86-movups/movupd/movdqu-Op/En-MR start-rip temp-rip prefixes rex-byte
    ;;                                       opcode modr/m sib x86))
    ;;   (t
    ;;    (x86-step-unimplemented
    ;;     (list 'Mandatory-prefixes
    ;;           (ms x86)
    ;;           start-rip temp-rip prefixes rex-byte opcode)
    ;;     x86))))

    ;; (#x12
    ;;  "(MOVLPD xmm m64)"
    ;;  (cond
    ;;   ((eql #.*mandatory-66h* (prefixes-slice :group-3-prefix prefixes))
    ;;    (x86-movlps/movlpd-Op/En-RM start-rip temp-rip prefixes rex-byte opcode
    ;;                                modr/m sib x86))
    ;;   (t
    ;;    (x86-step-unimplemented
    ;;     (list 'Mandatory-prefixes
    ;;           (ms x86)
    ;;           start-rip temp-rip prefixes rex-byte opcode)
    ;;     x86))))

    ;; (#x13
    ;;  "(MOVLPD m64 xmm)"
    ;;  (cond
    ;;   ((eql #.*mandatory-66h* (prefixes-slice :group-3-prefix prefixes))
    ;;    (x86-movlps/movlpd-Op/En-MR start-rip temp-rip prefixes rex-byte opcode
    ;;                                modr/m sib x86))
    ;;   (t
    ;;    (x86-step-unimplemented
    ;;     (list 'Mandatory-prefixes
    ;;           (ms x86)
    ;;           start-rip temp-rip prefixes rex-byte opcode)
    ;;     x86))))

    ;; (#x14
    ;;  "66h: (UNPCKLPD xmm1 xmm2/m128)"
    ;;  (cond

    ;;   ((eql #.*mandatory-66h* (prefixes-slice :group-3-prefix prefixes))
    ;;    (x86-unpck?pd-Op/En-RM nil start-rip temp-rip prefixes rex-byte opcode
    ;;                           modr/m sib x86))

    ;;   (t
    ;;    (x86-step-unimplemented
    ;;     (list 'Mandatory-prefixes
    ;;           (ms x86)
    ;;           start-rip temp-rip prefixes rex-byte opcode)
    ;;     x86))))

    ;; (#x15
    ;;  "66h: (UNPCKHPD xmm1 xmm2/m128)"
    ;;  (cond

    ;;   ((eql #.*mandatory-66h* (prefixes-slice :group-3-prefix prefixes))
    ;;    (x86-unpck?pd-Op/En-RM t start-rip temp-rip prefixes rex-byte opcode
    ;;                           modr/m sib x86))

    ;;   (t
    ;;    (x86-step-unimplemented
    ;;     (list 'Mandatory-prefixes
    ;;           (ms x86)
    ;;           start-rip temp-rip prefixes rex-byte opcode)
    ;;     x86))))

    ;; (#x16
    ;;  "66h: (MOVHPD xmm m64)"
    ;;  (cond

    ;;   ((eql #.*mandatory-66h* (prefixes-slice :group-3-prefix prefixes))
    ;;    (x86-movhps/movhpd-Op/En-RM start-rip temp-rip prefixes rex-byte opcode
    ;;                                modr/m sib x86))

    ;;   (t
    ;;    (x86-step-unimplemented
    ;;     (list 'Mandatory-prefixes
    ;;           (ms x86)
    ;;           start-rip temp-rip prefixes rex-byte opcode)
    ;;     x86))))

    ;; (#x17
    ;;  "66h: (MOVHPD m64 xmm)"
    ;;  (cond

    ;;   ((eql #.*mandatory-66h* (prefixes-slice :group-3-prefix prefixes))
    ;;    (x86-movhps/movhpd-Op/En-MR start-rip temp-rip prefixes rex-byte opcode
    ;;                                modr/m sib x86))

    ;;   (t
    ;;    (x86-step-unimplemented
    ;;     (list 'Mandatory-prefixes
    ;;           (ms x86)
    ;;           start-rip temp-rip prefixes rex-byte opcode)
    ;;     x86))))


    ;; (#x28
    ;;  "66h: (MOVAPD xmm1 xmm2/m128)"
    ;;  (cond

    ;;   ((eql #.*mandatory-66h* (prefixes-slice :group-3-prefix prefixes))
    ;;    (x86-movaps/movapd-Op/En-RM start-rip temp-rip prefixes rex-byte opcode
    ;;                                modr/m sib x86))

    ;;   (t
    ;;    (x86-step-unimplemented
    ;;     (list 'Mandatory-prefixes
    ;;           (ms x86)
    ;;           start-rip temp-rip prefixes rex-byte opcode)
    ;;     x86))))

    ;; (#x29
    ;;  "66h: (MOVAPD xmm2/m128 xmm1)"
    ;;  (cond

    ;;   ((eql #.*mandatory-66h* (prefixes-slice :group-3-prefix prefixes))
    ;;    (x86-movaps/movapd-Op/En-MR start-rip temp-rip prefixes rex-byte opcode
    ;;                                modr/m sib x86))

    ;;   (t
    ;;    (x86-step-unimplemented
    ;;     (list 'Mandatory-prefixes
    ;;           (ms x86)
    ;;           start-rip temp-rip prefixes rex-byte opcode)
    ;;     x86))))

    ;; (#x2A
    ;;  "F2h: (CVTSI2SD xmm r/m);
    ;;   F3h: (CVTSI2SS xmm r/m)"
    ;;  (cond
    ;;   ((eql #.*mandatory-f2h* (prefixes-slice :group-1-prefix prefixes))
    ;;    (x86-cvtsi2s?-Op/En-RM t start-rip temp-rip prefixes rex-byte
    ;;                           opcode modr/m sib x86))

    ;;   ((eql #.*mandatory-f3h* (prefixes-slice :group-1-prefix prefixes))
    ;;    (x86-cvtsi2s?-Op/En-RM nil start-rip temp-rip prefixes rex-byte
    ;;                           opcode modr/m sib x86))

    ;;   (t
    ;;    (x86-step-unimplemented
    ;;     (list 'Mandatory-prefixes
    ;;           (ms x86)
    ;;           start-rip temp-rip prefixes rex-byte opcode)
    ;;     x86))))

    ;; (#x2C
    ;;  "F2h: (CVTTSD2SI reg xmm2/m64);
    ;;   F3h: (CVTTSS2SI reg xmm2/m32)"
    ;;  (cond

    ;;   ((eql #.*mandatory-f2h* (prefixes-slice :group-1-prefix prefixes))
    ;;    (x86-cvts?2si/cvtts?2si-Op/En-RM t t start-rip temp-rip prefixes rex-byte
    ;;                                     opcode modr/m sib x86))

    ;;   ((eql #.*mandatory-f3h* (prefixes-slice :group-1-prefix prefixes))
    ;;    (x86-cvts?2si/cvtts?2si-Op/En-RM nil t start-rip temp-rip prefixes rex-byte
    ;;                                     opcode modr/m sib x86))

    ;;   (t
    ;;    (x86-step-unimplemented
    ;;     (list 'Mandatory-prefixes
    ;;           (ms x86)
    ;;           start-rip temp-rip prefixes rex-byte opcode)
    ;;     x86))))

    ;; (#x2D
    ;;  "F2h: (CVTSD2SI reg xmm2/m64)
    ;;   F3h: (CVTSS2SI reg xmm2/m32)"
    ;;  (cond

    ;;   ((eql #.*mandatory-f2h* (prefixes-slice :group-1-prefix prefixes))
    ;;    (x86-cvts?2si/cvtts?2si-Op/En-RM t nil start-rip temp-rip prefixes rex-byte
    ;;                                     opcode modr/m sib x86))

    ;;   ((eql #.*mandatory-f3h* (prefixes-slice :group-1-prefix prefixes))
    ;;    (x86-cvts?2si/cvtts?2si-Op/En-RM nil nil start-rip temp-rip prefixes rex-byte
    ;;                                     opcode modr/m sib x86))

    ;;   (t
    ;;    (x86-step-unimplemented
    ;;     (list 'Mandatory-prefixes
    ;;           (ms x86)
    ;;           start-rip temp-rip prefixes rex-byte opcode)
    ;;     x86))))

    ;; (#x2E
    ;;  "66h: (UCOMISD xmm1 xmm2/m64)"
    ;;  (cond

    ;;   ((eql #.*mandatory-66h* (prefixes-slice :group-3-prefix prefixes))
    ;;    (x86-comis?/ucomis?-Op/En-RM
    ;;     t #.*OP-UCOMI* start-rip temp-rip prefixes rex-byte opcode modr/m
    ;;     sib x86))

    ;;   (t
    ;;    (x86-step-unimplemented
    ;;     (list 'Mandatory-prefixes
    ;;           (ms x86)
    ;;           start-rip temp-rip prefixes rex-byte opcode)
    ;;     x86))))

    ;; (#x2F
    ;;  "66h: (COMISD xmm1 xmm2/m64)"
    ;;  (cond

    ;;   ((eql #.*mandatory-66h* (prefixes-slice :group-3-prefix prefixes))
    ;;    (x86-comis?/ucomis?-Op/En-RM
    ;;     t #.*OP-COMI* start-rip temp-rip prefixes rex-byte opcode modr/m
    ;;     sib x86))

    ;;   (t
    ;;    (x86-step-unimplemented
    ;;     (list 'Mandatory-prefixes
    ;;           (ms x86)
    ;;           start-rip temp-rip prefixes rex-byte opcode)
    ;;     x86))))

    ;; ((#x40 #x41 #x42 #x43 #x44 #x45 #x46 #x47 #x48 #x49 #x4A
    ;;        #x4B #x4C #x4D #x4E #x4F)
    ;;  "(CMOVcc Gv, Ev)"
    ;;  (x86-cmovcc start-rip temp-rip prefixes rex-byte opcode modr/m
    ;;              sib x86))

    ;; (#x51
    ;;  "F2h: (SQRTSD xmm1 xmm2/m64);
    ;;   F3h: (SQRTSS xmm1 xmm2/m32)
    ;;   66h: (SQRTPD xmm1 xmm2/m128);"
    ;;  (cond

    ;;   ((eql #.*mandatory-f2h* (prefixes-slice :group-1-prefix prefixes))
    ;;    (x86-sqrts?-Op/En-RM
    ;;     t start-rip temp-rip prefixes rex-byte opcode modr/m sib x86))

    ;;   ((eql #.*mandatory-f3h* (prefixes-slice :group-1-prefix prefixes))
    ;;    (x86-sqrts?-Op/En-RM
    ;;     nil start-rip temp-rip prefixes rex-byte opcode modr/m
    ;;     sib x86))

    ;;   ((eql #.*mandatory-66h* (prefixes-slice :group-3-prefix prefixes))
    ;;    (x86-sqrtpd-Op/En-RM
    ;;     start-rip temp-rip prefixes rex-byte opcode modr/m
    ;;     sib x86))

    ;;   (t
    ;;    (x86-step-unimplemented
    ;;     (list 'Mandatory-prefixes
    ;;           (ms x86)
    ;;           start-rip temp-rip prefixes rex-byte opcode)
    ;;     x86))))

    ;; (#x54
    ;;  "66h: (ANDPD xmm1 xmm2/m128)"
    ;;  (cond

    ;;   ((eql #.*mandatory-66h* (prefixes-slice :group-3-prefix prefixes))
    ;;    (x86-andp?/andnp?/orp?/xorp?/pand/pandn/por/pxor-Op/En-RM
    ;;     #.*OP-AND* start-rip temp-rip prefixes rex-byte opcode modr/m
    ;;     sib x86))

    ;;   (t
    ;;    (x86-step-unimplemented
    ;;     (list 'Mandatory-prefixes
    ;;           (ms x86)
    ;;           start-rip temp-rip prefixes rex-byte opcode)
    ;;     x86))))

    ;; (#x55
    ;;  "66h: (ANDNPD xmm1 xmm2/m128)"
    ;;  (cond

    ;;   ((eql #.*mandatory-66h* (prefixes-slice :group-3-prefix prefixes))
    ;;    (x86-andp?/andnp?/orp?/xorp?/pand/pandn/por/pxor-Op/En-RM
    ;;     #.*OP-ANDN* start-rip temp-rip prefixes rex-byte opcode modr/m
    ;;     sib x86))

    ;;   (t
    ;;    (x86-step-unimplemented
    ;;     (list 'Mandatory-prefixes
    ;;           (ms x86)
    ;;           start-rip temp-rip prefixes rex-byte opcode)
    ;;     x86))))

    ;; (#x56
    ;;  "66h: (ORPD xmm1 xmm2/m128)"
    ;;  (cond

    ;;   ((eql #.*mandatory-66h* (prefixes-slice :group-3-prefix prefixes))
    ;;    (x86-andp?/andnp?/orp?/xorp?/pand/pandn/por/pxor-Op/En-RM
    ;;     #.*OP-OR* start-rip temp-rip prefixes rex-byte opcode modr/m
    ;;     sib x86))

    ;;   (t
    ;;    (x86-step-unimplemented
    ;;     (list 'Mandatory-prefixes
    ;;           (ms x86)
    ;;           start-rip temp-rip prefixes rex-byte opcode)
    ;;     x86))))

    ;; (#x57
    ;;  "66h: (XORPD xmm1 xmm2/m128)"
    ;;  (cond

    ;;   ((eql #.*mandatory-66h* (prefixes-slice :group-3-prefix prefixes))
    ;;    (x86-andp?/andnp?/orp?/xorp?/pand/pandn/por/pxor-Op/En-RM
    ;;     #.*OP-XOR* start-rip temp-rip prefixes rex-byte opcode modr/m
    ;;     sib x86))

    ;;   (t
    ;;    (x86-step-unimplemented
    ;;     (list 'Mandatory-prefixes
    ;;           (ms x86)
    ;;           start-rip temp-rip prefixes rex-byte opcode)
    ;;     x86))))

    ;; (#x58
    ;;  "F2h: (ADDSD xmm1 xmm2/m64);
    ;;   F3h: (ADDSS xmm1 xmm2/m32);
    ;;   66h: (ADDPD xmm1 xmm2/m128)"
    ;;  (cond

    ;;   ((eql #.*mandatory-f2h* (prefixes-slice :group-1-prefix prefixes))
    ;;    (x86-adds?/subs?/muls?/divs?/maxs?/mins?-Op/En-RM
    ;;     t #.*OP-ADD* start-rip temp-rip prefixes rex-byte opcode modr/m
    ;;     sib x86))

    ;;   ((eql #.*mandatory-f3h* (prefixes-slice :group-1-prefix prefixes))
    ;;    (x86-adds?/subs?/muls?/divs?/maxs?/mins?-Op/En-RM
    ;;     nil #.*OP-ADD* start-rip temp-rip prefixes rex-byte opcode modr/m
    ;;     sib x86))

    ;;   ((eql #.*mandatory-66h* (prefixes-slice :group-3-prefix prefixes))
    ;;    (x86-addpd/subpd/mulpd/divpd/maxpd/minpd-Op/En-RM
    ;;     #.*OP-ADD* start-rip temp-rip prefixes rex-byte opcode modr/m
    ;;     sib x86))

    ;;   (t
    ;;    (x86-step-unimplemented
    ;;     (list 'Mandatory-prefixes
    ;;           (ms x86)
    ;;           start-rip temp-rip prefixes rex-byte opcode)
    ;;     x86))))

    ;; (#x59
    ;;  "F2h: (MULSD xmm1 xmm2/m64);
    ;;   F3h: (MULSS xmm1 xmm2/m32)
    ;;   66h: (MULPD xmm1 xmm2/m128)"
    ;;  (cond

    ;;   ((eql #.*mandatory-f2h* (prefixes-slice :group-1-prefix prefixes))
    ;;    (x86-adds?/subs?/muls?/divs?/maxs?/mins?-Op/En-RM
    ;;     t #.*OP-MUL* start-rip temp-rip prefixes rex-byte opcode modr/m
    ;;     sib x86))

    ;;   ((eql #.*mandatory-f3h* (prefixes-slice :group-1-prefix prefixes))
    ;;    (x86-adds?/subs?/muls?/divs?/maxs?/mins?-Op/En-RM
    ;;     nil #.*OP-MUL* start-rip temp-rip prefixes rex-byte opcode modr/m
    ;;     sib x86))

    ;;   ((eql #.*mandatory-66h* (prefixes-slice :group-3-prefix prefixes))
    ;;    (x86-addpd/subpd/mulpd/divpd/maxpd/minpd-Op/En-RM
    ;;     #.*OP-MUL* start-rip temp-rip prefixes rex-byte opcode modr/m
    ;;     sib x86))

    ;;   (t
    ;;    (x86-step-unimplemented
    ;;     (list 'Mandatory-prefixes
    ;;           (ms x86)
    ;;           start-rip temp-rip prefixes rex-byte opcode)
    ;;     x86))))

    ;; (#x5A
    ;;  "F2h: (CVTSD2SS xmm1 xmm2/m64);
    ;;   F3h: (CVTSS2SD xmm1 xmm2/m32);
    ;;   66h: (CVTPD2PS xmm1 xmm2/m128)"
    ;;  (cond

    ;;   ((eql #.*mandatory-f2h* (prefixes-slice :group-1-prefix prefixes))
    ;;    (x86-cvts?2s?-Op/En-RM
    ;;     t start-rip temp-rip prefixes rex-byte opcode modr/m
    ;;     sib x86))

    ;;   ((eql #.*mandatory-f3h* (prefixes-slice :group-1-prefix prefixes))
    ;;    (x86-cvts?2s?-Op/En-RM
    ;;     nil start-rip temp-rip prefixes rex-byte opcode modr/m
    ;;     sib x86))

    ;;   ((eql #.*mandatory-66h* (prefixes-slice :group-3-prefix prefixes))
    ;;    (x86-cvtpd2ps-Op/En-RM
    ;;     start-rip temp-rip prefixes rex-byte opcode modr/m
    ;;     sib x86))

    ;;   (t
    ;;    (x86-step-unimplemented
    ;;     (list 'Mandatory-prefixes
    ;;           (ms x86)
    ;;           start-rip temp-rip prefixes rex-byte opcode)
    ;;     x86))))

    ;; (#x5C
    ;;  "F2h: (SUBSD xmm1 xmm2/m64);
    ;;   F3h: (SUBSS xmm1 xmm2/m32);
    ;;   66h: (SUBPD xmm1 xmm2/m128)"
    ;;  (cond

    ;;   ((eql #.*mandatory-f2h* (prefixes-slice :group-1-prefix prefixes))
    ;;    (x86-adds?/subs?/muls?/divs?/maxs?/mins?-Op/En-RM
    ;;     t #.*OP-SUB* start-rip temp-rip prefixes rex-byte opcode modr/m
    ;;     sib x86))

    ;;   ((eql #.*mandatory-f3h* (prefixes-slice :group-1-prefix prefixes))
    ;;    (x86-adds?/subs?/muls?/divs?/maxs?/mins?-Op/En-RM
    ;;     nil #.*OP-SUB* start-rip temp-rip prefixes rex-byte opcode modr/m
    ;;     sib x86))

    ;;   ((eql #.*mandatory-66h* (prefixes-slice :group-3-prefix prefixes))
    ;;    (x86-addpd/subpd/mulpd/divpd/maxpd/minpd-Op/En-RM
    ;;     #.*OP-SUB* start-rip temp-rip prefixes rex-byte opcode modr/m
    ;;     sib x86))

    ;;   (t
    ;;    (x86-step-unimplemented
    ;;     (list 'Mandatory-prefixes
    ;;           (ms x86)
    ;;           start-rip temp-rip prefixes rex-byte opcode)
    ;;     x86))))

    ;; (#x5D
    ;;  "F2h: (MINSD xmm1 xmm2/m64);
    ;;   F3h: (MINSS xmm1 xmm2/m32);
    ;;   66h: (MINPD xmm1 xmm2/m128)"
    ;;  (cond

    ;;   ((eql #.*mandatory-f2h* (prefixes-slice :group-1-prefix prefixes))
    ;;    (x86-adds?/subs?/muls?/divs?/maxs?/mins?-Op/En-RM
    ;;     t #.*OP-MIN* start-rip temp-rip prefixes rex-byte opcode modr/m
    ;;     sib x86))

    ;;   ((eql #.*mandatory-f3h* (prefixes-slice :group-1-prefix prefixes))
    ;;    (x86-adds?/subs?/muls?/divs?/maxs?/mins?-Op/En-RM
    ;;     nil #.*OP-MIN* start-rip temp-rip prefixes rex-byte opcode modr/m
    ;;     sib x86))

    ;;   ((eql #.*mandatory-66h* (prefixes-slice :group-3-prefix prefixes))
    ;;    (x86-addpd/subpd/mulpd/divpd/maxpd/minpd-Op/En-RM
    ;;     #.*OP-MIN* start-rip temp-rip prefixes rex-byte opcode modr/m
    ;;     sib x86))

    ;;   (t
    ;;    (x86-step-unimplemented
    ;;     (list 'Mandatory-prefixes
    ;;           (ms x86)
    ;;           start-rip temp-rip prefixes rex-byte opcode)
    ;;     x86))))

    ;; (#x5E
    ;;  "F2h: (DIVSD xmm1 xmm2/m64);
    ;;   F3h: (DIVSS xmm1 xmm2/m32);
    ;;   66h: (DIVPD xmm1 xmm2/m128)"
    ;;  (cond

    ;;   ((eql #.*mandatory-f2h* (prefixes-slice :group-1-prefix prefixes))
    ;;    (x86-adds?/subs?/muls?/divs?/maxs?/mins?-Op/En-RM
    ;;     t #.*OP-DIV* start-rip temp-rip prefixes rex-byte opcode modr/m
    ;;     sib x86))

    ;;   ((eql #.*mandatory-f3h* (prefixes-slice :group-1-prefix prefixes))
    ;;    (x86-adds?/subs?/muls?/divs?/maxs?/mins?-Op/En-RM
    ;;     nil #.*OP-DIV* start-rip temp-rip prefixes rex-byte opcode modr/m
    ;;     sib x86))

    ;;   ((eql #.*mandatory-66h* (prefixes-slice :group-3-prefix prefixes))
    ;;    (x86-addpd/subpd/mulpd/divpd/maxpd/minpd-Op/En-RM
    ;;     #.*OP-DIV* start-rip temp-rip prefixes rex-byte opcode modr/m
    ;;     sib x86))

    ;;   (t
    ;;    (x86-step-unimplemented
    ;;     (list 'Mandatory-prefixes
    ;;           (ms x86)
    ;;           start-rip temp-rip prefixes rex-byte opcode)
    ;;     x86))))

    ;; (#x5F
    ;;  "F2h: (MAXSD xmm1 xmm2/m64);
    ;;   F3h: (MAXSS xmm1 xmm2/m32);
    ;;   66h: (MAXPD xmm1 xmm2/m128)"
    ;;  (cond

    ;;   ((eql #.*mandatory-f2h* (prefixes-slice :group-1-prefix prefixes))
    ;;    (x86-adds?/subs?/muls?/divs?/maxs?/mins?-Op/En-RM
    ;;     t #.*OP-MAX* start-rip temp-rip prefixes rex-byte opcode modr/m
    ;;     sib x86))

    ;;   ((eql #.*mandatory-f3h* (prefixes-slice :group-1-prefix prefixes))
    ;;    (x86-adds?/subs?/muls?/divs?/maxs?/mins?-Op/En-RM
    ;;     nil #.*OP-MAX* start-rip temp-rip prefixes rex-byte opcode modr/m
    ;;     sib x86))

    ;;   ((eql #.*mandatory-66h* (prefixes-slice :group-3-prefix prefixes))
    ;;    (x86-addpd/subpd/mulpd/divpd/maxpd/minpd-Op/En-RM
    ;;     #.*OP-MAX* start-rip temp-rip prefixes rex-byte opcode modr/m
    ;;     sib x86))

    ;;   (t
    ;;    (x86-step-unimplemented
    ;;     (list 'Mandatory-prefixes
    ;;           (ms x86)
    ;;           start-rip temp-rip prefixes rex-byte opcode)
    ;;     x86))))

    ;; (#x6F
    ;;  "F3h: (MOVDQU xmm1 xmm2/m128)"
    ;;  (cond

    ;;   ((eql #.*mandatory-f3h* (prefixes-slice :group-1-prefix prefixes))

    ;;    (x86-movups/movupd/movdqu-Op/En-RM start-rip temp-rip prefixes rex-byte
    ;;                                       opcode modr/m sib x86))

    ;;   (t
    ;;    (x86-step-unimplemented
    ;;     (list 'Mandatory-prefixes
    ;;           (ms x86)
    ;;           start-rip temp-rip prefixes rex-byte opcode)
    ;;     x86))))

    ;; (#x74
    ;;  "66h: (PCMPEQB xmm1 xmm2/m128)"
    ;;  (cond

    ;;   ((eql #.*mandatory-66h* (prefixes-slice :group-3-prefix prefixes))
    ;;    (x86-pcmpeqb-Op/En-RM
    ;;     start-rip temp-rip prefixes rex-byte opcode modr/m
    ;;     sib x86))

    ;;   (t
    ;;    (x86-step-unimplemented
    ;;     (list 'Mandatory-prefixes
    ;;           (ms x86)
    ;;           start-rip temp-rip prefixes rex-byte opcode)
    ;;     x86))))

    ;; (#x7F
    ;;  "F3h: (MOVDQU xmm2/m128 xmm1)"
    ;;  (cond

    ;;   ((eql #.*mandatory-f3h* (prefixes-slice :group-1-prefix prefixes))

    ;;    (x86-movups/movupd/movdqu-Op/En-MR start-rip temp-rip prefixes rex-byte
    ;;                                       opcode modr/m sib x86))

    ;;   (t
    ;;    (x86-step-unimplemented
    ;;     (list 'Mandatory-prefixes
    ;;           (ms x86)
    ;;           start-rip temp-rip prefixes rex-byte opcode)
    ;;     x86))))


    ((#x80 #x81 #x82 #x83 #x84 #x85 #x86 #x87 #x88 #x89 #x8A
           #x8B #x8C #x8D #x8E #x8F)
     "(Jcc Jz)"
     (x86-two-byte-jcc start-rip temp-rip prefixes rex-byte opcode
                       modr/m sib x86))


    ((#x90 #x91 #x92 #x93 #x94 #x95 #x96 #x97 #x98 #x99 #x9A
           #x9B #x9C #x9D #x9E #x9F)
     "(SETcc Eb)"
     (x86-setcc start-rip temp-rip prefixes rex-byte opcode
                modr/m sib x86))

    (#x1F
     "(NOP)"
     (case (mrm-reg modr/m)
       (0
        (x86-two-byte-nop start-rip temp-rip prefixes rex-byte opcode
                          modr/m sib x86))
       (t
        (x86-step-unimplemented
         (cons (ms x86)
               (list start-rip temp-rip prefixes rex-byte opcode))
         x86))))

    (#xA0
     "(Push FS)"
     (x86-push-segment-register start-rip temp-rip prefixes rex-byte opcode
                                modr/m sib x86))

    (#xA3
     "(BT Ev Gv)"
     (x86-bt-0f-a3 start-rip temp-rip prefixes rex-byte opcode
                   modr/m sib x86))

    (#xA8
     "(Push GS)"
     (x86-push-segment-register start-rip temp-rip prefixes rex-byte opcode
                                modr/m sib x86))

    (#xAF
     "(IMUL Gv Ev)"
     (x86-imul-Op/En-RM start-rip temp-rip prefixes rex-byte opcode
                        modr/m sib x86))

    ((#xB0 #xB1)
     "B0: (CMPXCHG Eb Gb); B1: (CMPXCHG Ev Gv)"
     (x86-cmpxchg start-rip temp-rip prefixes rex-byte opcode modr/m sib
                  x86))

    ((#xB6 #xB7)
     "B6: (MOVZX Gv Eb); B7: (MOVZX Gv Ew)"
     (x86-movzx start-rip temp-rip prefixes rex-byte opcode modr/m sib
                x86))

    (#xBA
     "Group 8: Opcode-extension: Modr/m.reg
      4:(BT Ev, Ib); Otherwise: unimplemented"
     (case (mrm-reg modr/m)
       (4
        (x86-bt-0f-ba start-rip temp-rip prefixes rex-byte opcode
                      modr/m sib x86))
       (otherwise
        (x86-step-unimplemented
         (cons (ms x86)
               (list start-rip temp-rip prefixes rex-byte opcode))
         x86))))

    ((#xBE #xBF)
     "BE:(MOVSXD Gv Eb); BF:(MOVSXD Gv Ew)"
     (x86-two-byte-movsxd start-rip temp-rip prefixes rex-byte opcode
                          modr/m sib x86))



    (#xC2
     "F2h: (CMPSD xmm1 xmm2/m64 imm8);
      F3h: (CMPSS xmm1 xmm2/m32 imm8);
      66h: (CMPPD xmm1 xmm2/m128 imm8)"
     (cond

      ((eql #.*mandatory-f2h* (prefixes-slice :group-1-prefix prefixes))
       (x86-cmpss/cmpsd-Op/En-RMI #.*OP-DP* start-rip temp-rip prefixes rex-byte opcode
                                  modr/m sib x86))

      ((eql #.*mandatory-f3h* (prefixes-slice :group-1-prefix prefixes))
       (x86-cmpss/cmpsd-Op/En-RMI #.*OP-SP* start-rip temp-rip prefixes rex-byte
                                  opcode modr/m sib x86))

      ;; ((eql #.*mandatory-66h* (prefixes-slice :group-3-prefix prefixes))
      ;;  (x86-cmppd-Op/En-RMI start-rip temp-rip prefixes rex-byte opcode modr/m
      ;;                       sib x86))

      (t
       (x86-step-unimplemented
        (list 'Mandatory-prefixes
              (ms x86)
              start-rip temp-rip prefixes rex-byte opcode)
        x86))))

    ;; (#xC6
    ;;  "66h: (SHUFPD xmm1 xmm2/m128 imm8)"
    ;;  (cond

    ;;   ((eql #.*mandatory-66h* (prefixes-slice :group-3-prefix prefixes))
    ;;    (x86-shufpd-Op/En-RMI start-rip temp-rip prefixes rex-byte opcode modr/m
    ;;                          sib x86))

    ;;   (t
    ;;    (x86-step-unimplemented
    ;;     (list 'Mandatory-prefixes
    ;;           (ms x86)
    ;;           start-rip temp-rip prefixes rex-byte opcode)
    ;;     x86))))

    (#xC7
     "Group 9: Opcode-extension: ModR/M.reg and ModR/M.mod
      Mod:3 Reg:6: RDRAND"
     (case (mrm-reg modr/m)
       (6
        (case (mrm-mod modr/m)
          (3
           (x86-rdrand start-rip temp-rip prefixes rex-byte opcode
                       modr/m sib x86))
          (otherwise
           (x86-step-unimplemented
            (cons (ms x86)
                  (list start-rip temp-rip prefixes rex-byte opcode))
            x86))))
       (otherwise
        (x86-step-unimplemented
         (cons (ms x86)
               (list start-rip temp-rip prefixes rex-byte opcode))
         x86))))

    ;; (#xD7
    ;;  "66h: (PMOVMSKB reg xmm)"
    ;;  (cond

    ;;   ((eql #.*mandatory-66h* (prefixes-slice :group-3-prefix prefixes))
    ;;    (x86-pmovmskb-Op/En-RM start-rip temp-rip prefixes rex-byte opcode modr/m
    ;;                           sib x86))

    ;;   (t
    ;;    (x86-step-unimplemented
    ;;     (list 'Mandatory-prefixes
    ;;           (ms x86)
    ;;           start-rip temp-rip prefixes rex-byte opcode)
    ;;     x86))))

    ;; (#xDB
    ;;  "66h: (PAND xmm1 xmm2/m128)"
    ;;  (cond

    ;;   ((eql #.*mandatory-66h* (prefixes-slice :group-3-prefix prefixes))
    ;;    (x86-andp?/andnp?/orp?/xorp?/pand/pandn/por/pxor-Op/En-RM
    ;;     #.*OP-AND* start-rip temp-rip prefixes rex-byte opcode modr/m
    ;;     sib x86))

    ;;   (t
    ;;    (x86-step-unimplemented
    ;;     (list 'Mandatory-prefixes
    ;;           (ms x86)
    ;;           start-rip temp-rip prefixes rex-byte opcode)
    ;;     x86))))

    ;; (#xDF
    ;;  "66h: (PANDN xmm1 xmm2/m128)"
    ;;  (cond

    ;;   ((eql #.*mandatory-66h* (prefixes-slice :group-3-prefix prefixes))
    ;;    (x86-andp?/andnp?/orp?/xorp?/pand/pandn/por/pxor-Op/En-RM
    ;;     #.*OP-ANDN* start-rip temp-rip prefixes rex-byte opcode modr/m
    ;;     sib x86))

    ;;   (t
    ;;    (x86-step-unimplemented
    ;;     (list 'Mandatory-prefixes
    ;;           (ms x86)
    ;;           start-rip temp-rip prefixes rex-byte opcode)
    ;;     x86))))

    ;; (#xEB
    ;;  "66h: (POR xmm1 xmm2/m128)"
    ;;  (cond

    ;;   ((eql #.*mandatory-66h* (prefixes-slice :group-3-prefix prefixes))
    ;;    (x86-andp?/andnp?/orp?/xorp?/pand/pandn/por/pxor-Op/En-RM
    ;;     #.*OP-OR* start-rip temp-rip prefixes rex-byte opcode modr/m
    ;;     sib x86))

    ;;   (t
    ;;    (x86-step-unimplemented
    ;;     (list 'Mandatory-prefixes
    ;;           (ms x86)
    ;;           start-rip temp-rip prefixes rex-byte opcode)
    ;;     x86))))

    ;; (#xEF
    ;;  "66h: (PXOR xmm1 xmm2/m128)"
    ;;  (cond

    ;;   ((eql #.*mandatory-66h* (prefixes-slice :group-3-prefix prefixes))
    ;;    (x86-andp?/andnp?/orp?/xorp?/pand/pandn/por/pxor-Op/En-RM
    ;;     #.*OP-XOR* start-rip temp-rip prefixes rex-byte opcode modr/m
    ;;     sib x86))

    ;;   (t
    ;;    (x86-step-unimplemented
    ;;     (list 'Mandatory-prefixes
    ;;           (ms x86)
    ;;           start-rip temp-rip prefixes rex-byte opcode)
    ;;     x86))))

    (otherwise
     "Unimplemented"
     (x86-step-unimplemented
      (cons (ms x86)
            (list start-rip temp-rip prefixes rex-byte opcode))
      x86))))

(defun create-case-stmt-1 (top-level-op-list acc)
  (cond ((endp top-level-op-list)
         acc)
        (t
         (let* ((case-branch (car top-level-op-list))
                (opcode/s (car case-branch))
                (func-call-or-another-case (caddr case-branch)))
           (create-case-stmt-1 (cdr top-level-op-list)
                               (cons (list opcode/s
                                           func-call-or-another-case)
                                     acc))))))

(defun create-case-stmt (top-level-op-list)
  (append (list 'case 'opcode)
          (reverse (create-case-stmt-1 top-level-op-list nil))))


(defun create-two-byte-opcode-decode-and-execute-fn ()

  `(define two-byte-opcode-decode-and-execute
     ((start-rip   :type (signed-byte #.*max-linear-address-size*))
      (temp-rip    :type (signed-byte #.*max-linear-address-size*))
      (prefixes    :type (unsigned-byte 43))
      (rex-byte    :type (unsigned-byte 8))
      (escape-byte :type (unsigned-byte 8))
      x86)

     :ignore-ok t
     :guard (equal escape-byte #x0F)
     :parents (x86-decoder)
     :short "Decoder and dispatch function for two-byte opcodes"
     :long "<p>Source: Intel Manual, Volume 2, Appendix A-2</p>"

     (b* ((ctx 'two-byte-opcode-decode-and-execute)
          ;; (64-bit-mod (64-bit-modep x86))
          ;; (machine 'x86)

          ((mv flg0 (the (unsigned-byte 8) opcode) x86)
           (rm08 temp-rip :x x86))
          ((when flg0)
           (!!ms-fresh :opcode-byte-access-error flg0))

          ((the (signed-byte 49) temp-rip)
           (1+ temp-rip))
          ((when (mbe :logic (not (canonical-address-p temp-rip))
                      :exec (<= #.*2^47*
                                (the (signed-byte
                                      #.*max-linear-address-size+1*)
                                  temp-rip))))
           (!!ms-fresh :non-canonical-address-encountered temp-rip))

          (modr/m? (x86-two-byte-opcode-ModR/M-p opcode))
          ((mv flg1 (the (unsigned-byte 8) modr/m) x86)
           (if modr/m?
               (rm08 temp-rip :x x86)
             (mv nil 0 x86)))
          ((when flg1)
           (!!ms-fresh :modr/m-byte-read-error flg1))

          ((the (signed-byte 49) temp-rip)
           (if modr/m? (1+ temp-rip) temp-rip))

          ((when (mbe :logic (not (canonical-address-p temp-rip))
                      :exec (<= #.*2^47*
                                (the (signed-byte
                                      #.*max-linear-address-size+1*)
                                  temp-rip))))
           (!!ms-fresh :temp-rip-too-large temp-rip))

          (sib? (and modr/m?
                     (x86-decode-SIB-p modr/m)))
          ((mv flg2 (the (unsigned-byte 8) sib) x86)
           (if sib?
               (rm08 temp-rip :x x86)
             (mv nil 0 x86)))
          ((when flg2)
           (!!ms-fresh :sib-byte-read-error flg2))

          ((the (signed-byte 49) temp-rip)
           (if sib? (1+ temp-rip) temp-rip))

          ((when (mbe :logic (not (canonical-address-p temp-rip))
                      :exec (<= #.*2^47*
                                (the (signed-byte
                                      #.*max-linear-address-size+1*)
                                  temp-rip))))
           (!!ms-fresh :virtual-address-error temp-rip)))

         ,(create-case-stmt *two-byte-op-list*))

     ///

     (defthm x86p-two-byte-opcode-decode-and-execute
       (implies (and (canonical-address-p temp-rip)
                     (x86p x86))
                (x86p (two-byte-opcode-decode-and-execute
                       start-rip temp-rip prefixes rex-byte escape-byte x86))))))

(make-event (create-two-byte-opcode-decode-and-execute-fn))

(defun create-opcode-execute-fn ()

  `(define opcode-execute

     ((start-rip :type (signed-byte   #.*max-linear-address-size*))
      (temp-rip  :type (signed-byte   #.*max-linear-address-size*))
      (prefixes  :type (unsigned-byte 43))
      (rex-byte  :type (unsigned-byte 8))
      (opcode    :type (unsigned-byte 8))
      (modr/m    :type (unsigned-byte 8))
      (sib       :type (unsigned-byte 8))
      x86)

     :parents (x86-decoder)
     ;; The following arg will avoid binding __function__ to
     ;; opcode-execute. The automatic __function__ binding that comes
     ;; with define causes stack overflows during the guard proof of
     ;; this function.
     :no-function t
     :short "Top-level dispatch function."
     :long "<p>@('opcode-execute') is the doorway to all the opcode
     maps.</p>"
     :guard-hints (("Goal"
                    :do-not '(preprocess)
                    :in-theory (e/d () (unsigned-byte-p signed-byte-p))))

     ,(create-case-stmt *top-level-op-list*)

     ///

     (defthm x86p-opcode-execute
       (implies (and (x86p x86)
                     (canonical-address-p temp-rip))
                (x86p (opcode-execute
                       start-rip temp-rip prefixes rex-byte opcode
                       modr/m sib x86))))))

(make-event (create-opcode-execute-fn))

;; ======================================================================

(define get-prefixes
  ((start-rip :type (signed-byte   #.*max-linear-address-size*))
   (prefixes  :type (unsigned-byte 43))
   (cnt       :type (integer 0 5))
   x86)

  :guard-hints (("Goal" :in-theory
                 (e/d ()
                      (negative-logand-to-positive-logand-with-integerp-x
                       signed-byte-p))))
  :measure (nfix cnt)

  :parents (x86-decoder)

  :long "<p>@('get-prefixes') fetches the prefixes of an instruction
  and also returns the first byte following the last prefix.
  @('start-rip') points to the first byte of an instruction,
  potentially a legacy prefix.</p>

  <p>Note that the initial value of @('cnt') should be 5 so that if 4
  prefixes are encountered, the next byte can also be fetched and
  stored in the accumulated return value, the @('prefixes')
  argument.</p>

  <p>Important note:</p>

  <p>From <a
  href='http://wiki.osdev.org/X86-64_Instruction_Encoding#Legacy_Prefixes'>OSDev
  Wiki</a>:</p>

     <p><em>When there are two or more prefixes from a single group,
     the behavior is undefined. Some processors ignore the subsequent
     prefixes from the same group, or use only the last prefix
     specified for any group.</em></p>

  <p>From Intel Manual, page 22-20 Vol. 3B, September 2013:</p>

     <p><em>The Intel386 processor sets a limit of 15 bytes on
     instruction length. The only way to violate this limit is by
     putting redundant prefixes before an instruction. A
     general-protection exception is generated if the limit on
     instruction length is violated.</em></p>

  <p>If we encounter two or more prefixes from a single prefix group,
  we halt our interpreter.  However, we can tolerate redundant
  prefixes.</p>"


  :prepwork

  ((defthm loghead-ash-0
     (implies (and (natp i)
                   (natp j)
                   (natp x)
                   (<= i j))
              (equal (loghead i (ash x j))
                     0))
     :hints (("Goal"
              :in-theory (e/d* (acl2::ihsext-inductions
                                acl2::ihsext-recursive-redefs)
                               ()))))

   (local
    (defthm signed-byte-p-48-fwd-chain
      (implies (signed-byte-p 48 start-rip)
               (equal (signed-byte-p 48 (1+ start-rip))
                      (< (1+ start-rip) *2^47*)))))

   (local
    (encapsulate
     ()
     (local (include-book "arithmetic-5/top" :dir :system))

     (defthm negative-logand-to-positive-logand-with-n43p-x
       (implies (and (< n 0)
                     (syntaxp (quotep n))
                     (equal m 43)
                     (integerp n)
                     (n43p x))
                (equal (logand n x)
                       (logand (logand (1- (ash 1 m)) n) x)))))))


  (if (mbe :logic (zp cnt)
           :exec (eql cnt 0))
      ;; Error, too many prefix bytes
      (mv nil prefixes x86)

    (b* ((ctx 'get-prefixes)
         ((mv flg (the (unsigned-byte 8) byte) x86)
          (rm08 start-rip :x x86))
         ((when flg)
          (mv (cons ctx flg) byte x86))

         (prefix-byte-group-code
          (the (integer 0 4) (get-one-byte-prefix-array-code byte))))

        (if (mbe :logic (zp prefix-byte-group-code)
                 :exec  (eql 0 prefix-byte-group-code))

            ;; Storing the number of prefixes seen and the first byte
            ;; following the prefixes in "prefixes"...
            (let ((prefixes
                   (!prefixes-slice :next-byte byte prefixes)))
              (mv nil (!prefixes-slice :num-prefixes (- 5 cnt) prefixes)
                  x86))

          (case prefix-byte-group-code
            (1 (let ((prefix-1?
                      (prefixes-slice :group-1-prefix prefixes)))
                 (if (or (eql 0 (the (unsigned-byte 8) prefix-1?))
                         ;; Redundant Prefix Okay
                         (eql byte prefix-1?))
                     (let ((next-rip (the (signed-byte
                                           #.*max-linear-address-size+1*)
                                       (1+ start-rip))))
                       (if (mbe :logic (canonical-address-p next-rip)
                                :exec
                                (< (the (signed-byte
                                         #.*max-linear-address-size+1*)
                                     next-rip)
                                   #.*2^47*))
                           ;; Storing the group 1 prefix and going on...
                           (get-prefixes next-rip
                                         (the (unsigned-byte 43)
                                           (!prefixes-slice :group-1-prefix
                                                            byte
                                                            prefixes))
                                         (the (integer 0 5) (1- cnt)) x86)
                         (mv (cons 'non-canonical-address next-rip) prefixes x86)))
                   ;; We do not tolerate more than one prefix from a prefix group.
                   (mv t prefixes x86))))

            (2 (let ((prefix-2?
                      (prefixes-slice :group-2-prefix prefixes)))
                 (if (or (eql 0 (the (unsigned-byte 8) prefix-2?))
                         ;; Redundant Prefixes Okay
                         (eql byte (the (unsigned-byte 8) prefix-2?)))
                     (let ((next-rip (the (signed-byte
                                           #.*max-linear-address-size+1*)
                                       (1+ start-rip))))
                       (if (mbe :logic (canonical-address-p next-rip)
                                :exec
                                (< (the (signed-byte
                                         #.*max-linear-address-size+1*)
                                     next-rip)
                                   #.*2^47*))
                           ;; Storing the group 2 prefix and going on...
                           (get-prefixes next-rip
                                         (!prefixes-slice :group-2-prefix
                                                          byte
                                                          prefixes)
                                         (the (integer 0 5) (1- cnt)) x86)
                         (mv (cons 'non-canonical-address next-rip)
                             prefixes x86)))
                   ;; We do not tolerate more than one prefix from a prefix group.
                   (mv t prefixes x86))))

            (3 (let ((prefix-3?
                      (prefixes-slice :group-3-prefix prefixes)))
                 (if (or (eql 0 (the (unsigned-byte 8) prefix-3?))
                         ;; Redundant Prefix Okay
                         (eql byte (the (unsigned-byte 8) prefix-3?)))

                     (let ((next-rip (the (signed-byte
                                           #.*max-linear-address-size+1*)
                                       (1+ start-rip))))
                       (if (mbe :logic (canonical-address-p next-rip)
                                :exec
                                (< (the (signed-byte
                                         #.*max-linear-address-size+1*)
                                     next-rip)
                                   #.*2^47*))
                           ;; Storing the group 3 prefix and going on...
                           (get-prefixes next-rip
                                         (!prefixes-slice :group-3-prefix
                                                          byte
                                                          prefixes)
                                         (the (integer 0 5) (1- cnt)) x86)
                         (mv (cons 'non-canonical-address next-rip)
                             prefixes x86)))
                   ;; We do not tolerate more than one prefix from a prefix group.
                   (mv t prefixes x86))))

            (4 (let ((prefix-4?
                      (prefixes-slice :group-4-prefix prefixes)))
                 (if (or (eql 0 (the (unsigned-byte 8) prefix-4?))
                         ;; Redundant Prefix Okay
                         (eql byte (the (unsigned-byte 8) prefix-4?)))
                     (let ((next-rip (the (signed-byte
                                           #.*max-linear-address-size+1*)
                                       (1+ start-rip))))
                       (if (mbe :logic (canonical-address-p next-rip)
                                :exec
                                (< (the (signed-byte
                                         #.*max-linear-address-size+1*)
                                     next-rip)
                                   #.*2^47*))
                           ;; Storing the group 4 prefix and going on...
                           (get-prefixes next-rip
                                         (!prefixes-slice :group-4-prefix
                                                          byte
                                                          prefixes)
                                         (the (integer 0 5) (1- cnt)) x86)
                         (mv (cons 'non-canonical-address next-rip)
                             prefixes x86)))
                   ;; We do not tolerate more than one prefix from a prefix group.
                   (mv t prefixes x86))))

            (otherwise
             (mv t prefixes x86))))))

  ///


  (defthm natp-get-prefixes
    (implies (forced-and (natp prefixes)
                         (canonical-address-p start-rip)
                         (x86p x86))
             (natp (mv-nth 1 (get-prefixes start-rip prefixes cnt x86))))
    :hints (("Goal" :in-theory (e/d () (force (force)))))
    :rule-classes :type-prescription)

  (defthm-usb n43p-get-prefixes
    :hyp (and (n43p prefixes)
              (canonical-address-p start-rip)
              (x86p x86))
    :bound 43
    :concl (mv-nth 1 (get-prefixes start-rip prefixes cnt x86))
    :hints (("Goal" :in-theory (e/d ()
                                    (signed-byte-p force (force)))))
    :gen-linear t)

  (defthm x86p-get-prefixes
    (implies (forced-and (x86p x86)
                         (canonical-address-p start-rip))
             (x86p (mv-nth 2 (get-prefixes start-rip prefixes cnt x86))))
    :hints (("Goal" :in-theory (e/d ()
                                    (signed-byte-p force (force))))))

  (local (in-theory (e/d  (rm08 rvm08)
                          (force
                           (force)
                           signed-byte-p-48-fwd-chain
                           signed-byte-p
                           bitops::logior-equal-0
                           acl2::zp-open
                           not
                           (:congruence acl2::int-equiv-implies-equal-logand-2)
                           (:congruence acl2::int-equiv-implies-equal-loghead-2)))))


  (defthm num-prefixes-get-prefixes-bound
    (implies (and (<= cnt 5)
                  (x86p x86)
                  (canonical-address-p start-rip)
                  (n43p prefixes)
                  (< (part-select prefixes :low 0 :high 2) 5))
             (<
              (prefixes-slice
               :num-prefixes
               (mv-nth 1 (get-prefixes start-rip prefixes cnt x86)))
              5))
    :hints (("Goal"
             :induct (get-prefixes start-rip prefixes cnt x86)
             :in-theory (e/d (get-prefixes)
                             (signed-byte-p
                              (force) force
                              canonical-address-p
                              not acl2::zp-open))))
    :rule-classes :linear)

  (defthm get-prefixes-opener-lemma-1
    (implies (zp cnt)
             (equal (get-prefixes start-rip prefixes cnt x86)
                    (mv nil prefixes x86)))
    :hints (("Goal" :in-theory (e/d (get-prefixes) ()))))

  (defthm get-prefixes-opener-lemma-2
    ;; This lemma would be used for those instructions which do not have
    ;; any prefix byte.
    (implies (and (canonical-address-p start-rip)
                  (programmer-level-mode x86)
                  (not (zp cnt))
                  ;; Important: I can eliminate the hyp (not flg)
                  ;; since flg will always be nil when we are in
                  ;; programmer-level mode and if start-rip is
                  ;; canonical.  However, (not flg) somehow helps in
                  ;; simplifying the ancestors' path when this rule is
                  ;; being considered, thereby increasing its
                  ;; applicability.
                  (let* ((flg (mv-nth 0 (rm08 start-rip :x x86)))
                         (prefix-byte-group-code
                          (get-one-byte-prefix-array-code
                           (mv-nth 1 (rm08 start-rip :x x86)))))
                    (and (not flg) ;; No error in reading a byte
                         (zp prefix-byte-group-code))))
             (equal (get-prefixes start-rip prefixes cnt x86)
                    (let ((prefixes
                           (!prefixes-slice :next-byte
                                            (mv-nth 1 (rm08 start-rip :x x86))
                                            prefixes)))
                      (mv nil (!prefixes-slice :num-prefixes (- 5 cnt) prefixes)
                          x86)))))

  (defthm get-prefixes-opener-lemma-3
    (implies (and (canonical-address-p (1+ start-rip))
                  (programmer-level-mode x86)
                  (not (zp cnt))
                  (equal (prefixes-slice :group-1-prefix prefixes) 0)
                  (let* ((flg (mv-nth 0 (rm08 start-rip :x x86)))
                         (prefix-byte-group-code
                          (get-one-byte-prefix-array-code
                           (mv-nth 1 (rm08 start-rip :x x86)))))
                    (and (not flg) ;; No error in reading a byte
                         (equal prefix-byte-group-code 1))))
             (equal (get-prefixes start-rip prefixes cnt x86)
                    (get-prefixes (1+ start-rip)
                                  (!prefixes-slice :group-1-prefix
                                                   (mv-nth 1 (rm08 start-rip :x x86))
                                                   prefixes)
                                  (1- cnt) x86))))

  (defthm get-prefixes-opener-lemma-4
    (implies (and (canonical-address-p (1+ start-rip))
                  (programmer-level-mode x86)
                  (not (zp cnt))
                  (equal (prefixes-slice :group-2-prefix prefixes) 0)
                  (let* ((flg (mv-nth 0 (rm08 start-rip :x x86)))
                         (prefix-byte-group-code
                          (get-one-byte-prefix-array-code
                           (mv-nth 1 (rm08 start-rip :x x86)))))
                    (and (not flg) ;; No error in reading a byte
                         (equal prefix-byte-group-code 2))))
             (equal (get-prefixes start-rip prefixes cnt x86)
                    (get-prefixes (1+ start-rip)
                                  (!prefixes-slice :group-2-prefix
                                                   (mv-nth 1 (rm08 start-rip :x x86))
                                                   prefixes)
                                  (1- cnt) x86))))

  (defthm get-prefixes-opener-lemma-5
    (implies (and (canonical-address-p (1+ start-rip))
                  (programmer-level-mode x86)
                  (not (zp cnt))
                  (equal (prefixes-slice :group-3-prefix prefixes) 0)
                  (let* ((flg (mv-nth 0 (rm08 start-rip :x x86)))
                         (prefix-byte-group-code
                          (get-one-byte-prefix-array-code
                           (mv-nth 1 (rm08 start-rip :x x86)))))
                    (and (not flg) ;; No error in reading a byte
                         (equal prefix-byte-group-code 3))))
             (equal (get-prefixes start-rip prefixes cnt x86)
                    (get-prefixes (1+ start-rip)
                                  (!prefixes-slice :group-3-prefix
                                                   (mv-nth 1 (rm08 start-rip :x x86))
                                                   prefixes)
                                  (1- cnt) x86))))

  (defthm get-prefixes-opener-lemma-6
    (implies (and (canonical-address-p (1+ start-rip))
                  (programmer-level-mode x86)
                  (not (zp cnt))
                  (equal (prefixes-slice :group-4-prefix prefixes) 0)
                  (let* ((flg (mv-nth 0 (rm08 start-rip :x x86)))
                         (prefix-byte-group-code
                          (get-one-byte-prefix-array-code
                           (mv-nth 1 (rm08 start-rip :x x86)))))
                    (and (not flg) ;; No error in reading a byte
                         (equal prefix-byte-group-code 4))))
             (equal (get-prefixes start-rip prefixes cnt x86)
                    (get-prefixes (1+ start-rip)
                                  (!prefixes-slice :group-4-prefix
                                                   (mv-nth 1 (rm08 start-rip :x x86))
                                                   prefixes)
                                  (1- cnt) x86))))

  (defthm get-prefixes-opener-lemma-7
    (implies (and (x86p x86)
                  (programmer-level-mode x86)
                  (not (mv-nth 0 (get-prefixes start-rip prefixes cnt x86))))
             (equal (mv-nth 2 (get-prefixes start-rip prefixes cnt x86))
                    x86))
    :hints (("Goal" :in-theory
             (union-theories
              '(get-prefixes
                rm08-does-not-affect-state-in-programmer-level-mode)
              (theory 'minimal-theory)))))

  )

;; ======================================================================

(define x86-fetch-decode-execute (x86)

  :parents (x86-decoder)
  :short "Top-level step function"

  :long "<p> @('x86-fetch-decode-execute') is the step function of our
x86 interpreter.  It fetches one instruction by looking up the memory
address indicated by the instruction pointer @('rip'), decodes that
instruction, and dispatches control to the appropriate instruction
semantic function.</p>"

  (b* ((ctx 'x86-fetch-decode-execute)
       ;; (64-bit-mode (64-bit-modep x86))
       ;; (machine 'x86)

       ;; We don't want our interpreter to take a step if the machine
       ;; is in a bad state.  Such checks are made in x86-run but I am
       ;; duplicating them here in case this function is being used at
       ;; the top-level.
       ((when (or (ms x86) (fault x86))) x86)

       (start-rip (the (signed-byte #.*max-linear-address-size*) (rip x86)))

       ((mv flg0 (the (unsigned-byte 43) prefixes) x86)
        (get-prefixes start-rip 0 5 x86))
       ;; Among other errors, if get-prefixes detects a non-canonical
       ;; address while attempting to fetch prefixes, flg0 will be
       ;; non-nil.
       ((when flg0)
        (!!ms-fresh :memory-error-in-reading-prefixes flg0))

       ((the (unsigned-byte 8) opcode/rex/escape-byte)
        (prefixes-slice :next-byte prefixes))

       ((the (unsigned-byte 4) prefix-length) (prefixes-slice :num-prefixes prefixes))
       ((the (signed-byte 49) temp-rip)
        (if (equal 0 prefix-length)
            (+ 1 start-rip)
          (+ 1 prefix-length start-rip)))

       ((when (mbe :logic (not (canonical-address-p temp-rip))
                   :exec (<= #.*2^47*
                             (the (signed-byte
                                   #.*max-linear-address-size+1*)
                               temp-rip))))
        (!!ms-fresh :non-canonical-address-encountered temp-rip))

       ;; If opcode/rex/escape-byte is a rex byte, it is filed away in
       ;; "rex-byte".
       ((the (unsigned-byte 8) rex-byte)
        (if (and ;; 64-bit-mode
             (equal (the (unsigned-byte 4)
                      (ash opcode/rex/escape-byte -4))
                    4))
            opcode/rex/escape-byte
          0))

       ((mv flg1 (the (unsigned-byte 8) opcode/escape-byte) x86)
        (if (equal 0 rex-byte)
            (mv nil opcode/rex/escape-byte x86)
          (rm08 temp-rip :x x86)))
       ((when flg1)
        (!!ms-fresh :opcode/escape-byte-read-error flg1))

       ((mv flg2 (the (signed-byte 49) temp-rip))
        (if (equal rex-byte 0)
            ;; We know temp-rip is canonical from the previous check.
            (mv nil temp-rip)
          (let ((temp-rip (the (signed-byte
                                #.*max-linear-address-size+1*) (1+ temp-rip))))
            ;; We need to check whether (1+ temp-rip) is canonical or
            ;; not.
            (if (mbe :logic (canonical-address-p temp-rip)
                     :exec (< (the (signed-byte
                                    #.*max-linear-address-size+1*)
                                temp-rip)
                              #.*2^47*))
                (mv nil temp-rip)
              (mv t temp-rip)))))

       ((when flg2)
        (!!ms-fresh :non-canonical-address-encountered temp-rip))

       ;; Possible values of opcode/escape-byte:

       ;; 1. An opcode of the primary opcode map:  this function
       ;;    prefetches the ModR/M and SIB bytes for these opcodes.
       ;;    The function "opcode-execute" case-splits on this byte
       ;;    and calls the appropriate step function.

       ;; 2. #x0F -- two-byte opcode indicator: modr/m? is set to NIL
       ;;    (see *onebyte-has-modrm-lst* in constants.lisp).  No
       ;;    ModR/M and SIB bytes are prefetched by this function for
       ;;    the two-byte opcode map.  Inside "opcode-execute", we
       ;;    call "two-byte-opcode-decode-and-execute", where we fetch
       ;;    the ModR/M and SIB bytes for these opcodes.

       ;; 3. #x8F: Depending on the value of ModR/M.reg,
       ;;    "opcode-execute" either calls the one-byte POP
       ;;    instruction or escapes to the XOP opcode map.

       ;; 4. #xC4, #xC5: Escape to the VEX opcode map.  Note that in
       ;;    this case, the ModR/M and SIB bytes will be prefetched by
       ;;    this function, and TEMP-RIP will be incremented
       ;;    accordingly.

       ;; The opcode/escape-byte should not contain any of the prefix
       ;; bytes -- by this point, all prefix bytes are processed.

       ;; Note that modr/m? will be nil for #x0F (see *onebyte-has-modrm-lst*
       ;; in constants.lisp) and temp-rip will not be incremented beyond this
       ;; point in this function for two-byte opcodes.

       ;; The modr/m and sib byte prefetching in this function is "biased"
       ;; towards the primary opcode map.  two-byte-opcode-decode-and-execute
       ;; does its own prefetching.  We made this choice to take advantage of
       ;; the fact that the most frequently encountered instructions are from
       ;; the primary opcode map.  Another reason is that the instruction
       ;; encoding syntax is clearer to understand; this is a nice way of
       ;; seeing how one opcode map escapes into the other.

       (modr/m? (x86-one-byte-opcode-ModR/M-p opcode/escape-byte))
       ((mv flg3 (the (unsigned-byte 8) modr/m) x86)
        (if modr/m?
            (rm08 temp-rip :x x86)
          (mv nil 0 x86)))
       ((when flg3)
        (!!ms-fresh :modr/m-byte-read-error flg2))

       ((mv flg4 (the (signed-byte 49) temp-rip))
        (if modr/m?
            (let ((temp-rip (the (signed-byte
                                  #.*max-linear-address-size+1*) (1+ temp-rip))))
              ;; We need to check whether (1+ temp-rip) is
              ;; canonical or not.
              (if (mbe :logic (canonical-address-p temp-rip)
                       :exec (< (the (signed-byte
                                      #.*max-linear-address-size+1*)
                                  temp-rip)
                                #.*2^47*))
                  (mv nil temp-rip)
                (mv t temp-rip)))
          ;; We know from the previous check that temp-rip is
          ;; canonical.
          (mv nil temp-rip)))

       ((when flg4)
        (!!ms-fresh :non-canonical-address-encountered temp-rip))

       (sib? (and modr/m? (x86-decode-SIB-p modr/m)))

       ((mv flg5 (the (unsigned-byte 8) sib) x86)
        (if sib?
            (rm08 temp-rip :x x86)
          (mv nil 0 x86)))
       ((when flg5)
        (!!ms-fresh :sib-byte-read-error flg3))

       ((mv flg6 (the (signed-byte 49) temp-rip))
        (if sib?
            (let ((temp-rip
                   (the (signed-byte #.*max-linear-address-size+2*)
                     (1+ temp-rip))))
              ;; We need to check whether (1+ temp-rip) is canonical.
              (if (mbe :logic (canonical-address-p temp-rip)
                       :exec (< (the (signed-byte
                                      #.*max-linear-address-size+2*)
                                  temp-rip)
                                #.*2^47*))
                  (mv nil temp-rip)
                (mv t temp-rip)))
          ;; We know from the previous check that temp-rip is
          ;; canonical.
          (mv nil temp-rip)))

       ((when flg6)
        (!!ms-fresh :virtual-address-error temp-rip)))

      (opcode-execute start-rip temp-rip prefixes rex-byte
                      opcode/escape-byte modr/m sib x86))

  ///

  (defthm x86p-x86-fetch-decode-execute
    (implies (x86p x86)
             (x86p (x86-fetch-decode-execute x86))))

  (defthm x86-fetch-decode-execute-opener
    (implies
     (and (equal start-rip (rip x86))
          (equal prefixes (mv-nth 1 (get-prefixes start-rip 0 5 x86)))
          (equal opcode/rex/escape-byte
                 (prefixes-slice :next-byte prefixes))
          (equal prefix-length (prefixes-slice :num-prefixes prefixes))
          (equal temp-rip0 (if (equal prefix-length 0)
                               (+ 1 start-rip)
                             (+ prefix-length start-rip 1)))
          (equal rex-byte (if (equal (ash opcode/rex/escape-byte -4)
                                     4)
                              opcode/rex/escape-byte 0))
          (equal opcode/escape-byte (if (equal rex-byte 0)
                                        opcode/rex/escape-byte
                                      (mv-nth 1 (rm08 temp-rip0 :x x86))))
          (equal temp-rip1 (if (equal rex-byte 0)
                               temp-rip0 (1+ temp-rip0)))
          (equal modr/m? (x86-one-byte-opcode-modr/m-p opcode/escape-byte))
          (equal modr/m (if modr/m?
                            (mv-nth 1 (rm08 temp-rip1 :x x86))
                          0))
          (equal temp-rip2 (if modr/m? (1+ temp-rip1) temp-rip1))
          (equal sib? (and modr/m? (x86-decode-sib-p modr/m)))
          (equal sib (if sib? (mv-nth 1 (rm08 temp-rip2 :x x86)) 0))
          (equal temp-rip3 (if sib? (1+ temp-rip2) temp-rip2))

          (x86p x86)
          (not (ms x86))
          (not (fault x86))
          ;; The following hypothesis is necessary because we do not
          ;; have RoW/WoW theorems for rm* and wm* functions yet.
          (programmer-level-mode x86)
          (not (mv-nth 0 (get-prefixes start-rip 0 5 x86)))
          (canonical-address-p temp-rip0)
          (not (mv-nth 0 (rm08 temp-rip0 :x x86)))
          (if (equal rex-byte 0)
              t
            (canonical-address-p temp-rip1))
          (if modr/m?
              (and (canonical-address-p temp-rip2)
                   (not (mv-nth 0 (rm08 temp-rip1 :x x86))))
            t)
          (if sib?
              (and (canonical-address-p temp-rip3)
                   (not (mv-nth 0 (rm08 temp-rip2 :x x86))))
            t))
     (equal (x86-fetch-decode-execute x86)
            (opcode-execute start-rip temp-rip3 prefixes rex-byte
                            opcode/escape-byte modr/m sib x86)))
    :hints (("Goal" :in-theory (e/d (rm08 rvm08)
                                    (signed-byte-p)))))

  (defthmd ms-fault-and-x86-fetch-decode-and-execute
    (implies (and (x86p x86)
                  (or (ms x86) (fault x86)))
             (equal (x86-fetch-decode-execute x86) x86)))
  )

;; ======================================================================

;; Running the interpreter:

;; Schedule: (in the M1 style)

(defun binary-clk+ (i j)
  (+ (nfix i) (nfix j)))

(defthm clk+-associative
  (implies (binary-clk+ (binary-clk+ i j) k)
           (binary-clk+ i (binary-clk+ j k))))

(defmacro clk+ (&rest args)
  (if (endp args)
      0
    (if (endp (cdr args))
        (car args)
      `(binary-clk+ ,(car args)
                    (clk+ ,@(cdr args))))))

(define x86-run
  ;; I fixed n to a fixnum for efficiency.  Also, executing more than
  ;; 2^59 instructions in one go seems kind of daunting.
  ((n :type (unsigned-byte 59))
   x86)

  :parents (x86-decoder)
  :short "Top-level specification function for the x86 ISA model"
  :long "<p>@('x86-run') returns the x86 state obtained by executing
  @('n') instructions or until it halts, whatever comes first.  It
  simply called the step function @(see x86-fetch-decode-execute)
  recursively.</p>"

  :returns (x86 x86p :hyp (x86p x86))

  (cond ((fault x86)
         x86)
        ((ms x86)
         x86)
        ((mbe :logic (zp n)
              :exec (equal 0 n))
         x86)
        (t (let* ((x86 (x86-fetch-decode-execute x86))
                  (n (the (unsigned-byte 59) (1- n))))
             (x86-run n x86))))


  ///

  (defthmd x86-run-and-x86-fetch-decode-and-execute-commutative
    ;; x86-fetch-decode-execute and x86-run can commute.
    (implies (and (natp k)
                  (x86p x86)
                  (not (ms x86))
                  (not (fault x86)))
             (equal (x86-run k (x86-fetch-decode-execute x86))
                    (x86-fetch-decode-execute (x86-run k x86))))
    :hints (("Goal" :in-theory (e/d
                                (ms-fault-and-x86-fetch-decode-and-execute) ()))))


  ;; Some opener theorems for x86-run:

  (defthm x86-run-halted
    (implies (or (ms x86) (fault x86))
             (equal (x86-run n x86) x86)))

  (defthm x86-run-opener-not-ms-not-fault-zp-n
    (implies (and (syntaxp (quotep n))
                  (zp n))
             (equal (x86-run n x86) x86)))

  (defthm x86-run-opener-not-ms-not-zp-n
    (implies (and (not (ms x86))
                  (not (fault x86))
                  (syntaxp (quotep n))
                  (not (zp n)))
             (equal (x86-run n x86)
                    (x86-run (1- n) (x86-fetch-decode-execute x86)))))

  ;; To enable compositional reasoning, we prove the following two
  ;; theorems:

  (defthm x86-run-plus
    (implies (and (natp n1)
                  (natp n2)
                  (syntaxp (quotep n1)))
             (equal (x86-run (clk+ n1 n2) x86)
                    (x86-run n2 (x86-run n1 x86)))))

  (encapsulate
   ()

   (local (include-book "arithmetic/top" :dir :system))

   (defthmd x86-run-plus-1
     (implies (and (natp n1)
                   (natp n2)
                   (syntaxp (quotep n1)))
              (equal (x86-run (clk+ n1 n2) x86)
                     (x86-run n1 (x86-run n2 x86)))))

   ))

(in-theory (disable binary-clk+))

;; ======================================================================

(define x86-run-steps1
  ((n :type (unsigned-byte 59))
   (n0 :type (unsigned-byte 59))
   x86)

  :enabled t
  :guard (and (natp n)
              (natp n0)
              (<= n n0))

  (let* ((diff (the (unsigned-byte 59) (- n0 n))))

    (cond ((ms x86)
           (mv diff x86))
          ((fault x86)
           (mv diff x86))
          ((zp n)
           (let* ((ctx 'x86-run)
                  (x86 (!!ms-fresh :timeout t)))
             (mv diff x86)))
          (t (let* ((x86 (x86-fetch-decode-execute x86))
                    (n-1 (the (unsigned-byte 59) (1- n))))
               (x86-run-steps1 n-1 n0 x86))))))

(define x86-run-steps
  ((n :type (unsigned-byte 59))
   x86)

  :parents (x86-decoder)
  :short "An alternative to @(see x86-run)"
  :long "<p> @('x86-run-steps') returns two values --- number of steps
  taken by the machine before it comes to a halt and the x86 state.
  Note that the number of steps will always be less than or equal to
  @('n').</p>"

  (x86-run-steps1 n n x86)

  ///

  (defthm x86-run-steps1-is-x86-run-ms
    (implies (ms x86)
             (equal (mv-nth 1 (x86-run-steps1 n n0 x86))
                    (x86-run n x86))))

  (defthm x86-run-steps1-is-x86-run-zp-n
    (implies (and (not (ms x86))
                  (not (fault x86))
                  (zp n))
             (equal (mv-nth 1 (x86-run-steps1 n n0 x86))
                    (!ms (list (list* 'x86-run
                                      :rip (rip x86)
                                      '(:timeout t)))
                         (x86-run n x86))))
    :hints (("Goal" :expand (x86-run n x86))))

  (defthm x86-run-steps1-open
    (implies (and (not (ms x86))
                  (not (fault x86))
                  (not (zp n)))
             (equal (mv-nth 1 (x86-run-steps1 n n0 x86))
                    (mv-nth 1 (x86-run-steps1 (1- n) n0
                                              (x86-fetch-decode-execute x86)))))))

(in-theory (disable x86-run-steps1))

;; ======================================================================
