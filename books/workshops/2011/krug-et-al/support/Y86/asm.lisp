
;  y86-asm.lisp                           Warren A. Hunt, Jr.

; This is an assember for the y86 interpreter, that includes the
; IADDL and the LEAVE instructions.

; A y86 assembler file is proper list of instructions, symbols, and
; assember directives.  The assembler keeps <asm-addr> (an address)
; where the next assembler directive or instruction will take effect,
; and then the <asm-addr> is altered as necessary.  For instance, if a
; NOP instruction is found, the byte #x00 will be inserted into an
; evolving memory image and <asm-addr> will be increase by 1 (byte).

; <label>       ; Name for specific <asm-addr>

; (pos <n>)     ; Set <asm-addr> to <n>
; (align <n>)   ; <asm-addr> set to (+ <asm-addr> (MOD <asm-addr> <n>))
; (space <n>)   ; <asm-addr> set to (+ <asm-addr> <n>)

; (byte <n>)    ; Write byte <n> to <asm-addr>
; (data <n>)    ; Write 32-bit <n> to  <asm-addr>

; (nop)
; (halt)

; (rrmovl <reg-id-or-n04p> <reg-id-or-n04p>)
; (irmovl <n32p> <reg-id-or-n04p>)
; (rmmovl <reg-id-or-n04p> <n32p> (<reg-id-or-n04p>))
; (mrmovl <n32p> (<reg-id-or-n04p>) <reg-id-or-n04p>)

; (addl   <reg-id-or-n04p> <reg-id-or-n04p>)
; (subl   <reg-id-or-n04p> <reg-id-or-n04p>)
; (andl   <reg-id-or-n04p> <reg-id-or-n04p>)
; (xorl   <reg-id-or-n04p> <reg-id-or-n04p>)
; (adcl   <reg-id-or-n04p> <reg-id-or-n04p>)
; (cmpl   <reg-id-or-n04p> <reg-id-or-n04p>)
; (orl    <reg-id-or-n04p> <reg-id-or-n04p>)
; (sall   <reg-id-or-n04p> <reg-id-or-n04p>)
; (shrl   <reg-id-or-n04p> <reg-id-or-n04p>)

; (jmp    <label-or-n32p>)
; (jle    <label-or-n32p>)
; (jl     <label-or-n32p>)
; (je     <label-or-n32p>)
; (jne    <label-or-n32p>)
; (jge    <label-or-n32p>)
; (jg     <label-or-n32p>)
; (jb     <label-or-n32p>)
; (jbe    <label-or-n32p>)

; (call   <label-or-n32p>)
; (ret)

; (pushl  <reg-id-or-n04p>)
; (popl   <reg-id-or-n04p>)

; (iaddl  <label-or-n32p> <reg-id-or-n04p>)
; (leave)

(in-package "ACL2")

(include-book "../Memory/memory")

;; This made no sense before - was some amalgamation of instruction
;; value and arity

;; These values aren't actually used anywhere right now, but they seem
;; potentially useful to keep around
(defconst *Arity*
  '((pos      1)
    (align    1)
    (space    1)
    (byte     1)
    (data     1)
    (nop      0)
    (halt     0)
    (rrmovl   2)
    (irmovl   2)
    (rmmovl   3)
    (mrmovl   3)
    (addl     2)
    (subl     2)
    (andl     2)
    (xorl     2)
    (adcl     2) ; new
    (cmpl     2) ; new
    (orl      2) ; new
    (sall     2) ; new
    (shrl     2) ; new
    (jmp      1)
    (jle      1)
    (jl       1)
    (je       1)
    (jne      1)
    (jge      1)
    (jg       1)
    (jb       1) ; new
    (jbe      1) ; new
    (call     1)
    (ret      0)
    (pushl    1)
    (popl     1)
    (iaddl    2)
    (leave    0)))


; Instruction values.

(defconst *Instructions*
  '((nop      0)
    (halt     1)
    (rrmovl   2)
    (irmovl   3)
    (rmmovl   4)
    (mrmovl   5)
    (addl     6 0)
    (subl     6 1)
    (andl     6 2)
    (xorl     6 3)
    (adcl     6 4) ; new
    (cmpl     6 5) ; new
    (orl      6 6) ; new
    (sall     6 7) ; new
    (shrl     6 8) ; new
    (jmp      7 0)
    (jle      7 1)
    (jl       7 2)
    (je       7 3)
    (jne      7 4)
    (jge      7 5)
    (jg       7 6)
    (jb       7 7) ; new
    (jbe      7 8) ; new
    (call     8)
    (ret      9)
    (pushl   10)
    (popl    11)
    (iaddl   12)
    (leave   13)))

; Convert register name to register number; otherwise, return NIL.

(defun reg-id (reg)
  (if (symbolp reg)
      (case reg
        (:eax 0)
        (%eax 0)
        (:ecx 1)
        (%ecx 1)
        (:edx 2)
        (%edx 2)
        (:ebx 3)
        (%ebx 3)
        (:esp 4)
        (%esp 4)
        (:ebp 5)
        (%ebp 5)
        (:esi 6)
        (%esi 6)
        (:edi 7)
        (%edi 7)

        (:imme1 8)  ; new
        (%imme1 8)  ; new
        (:imme2 9)  ; new
        (%imme2 9)  ; new
        (:valu1 10) ; new
        (%valu1 10) ; new
        (:valu2 11) ; new
        (%valu2 11) ; new

        (otherwise nil))
    (if (and (integerp reg)
             (<= 0 reg)
             (<= reg 11))
        reg
      nil)))

(defun y86-prog (program)
  (if (atom program)
      (or (null program)
          (cw "Last CDR of program not NIL.~%"))
    (let ((label-or-instruction (car program))
          (rest-program (cdr program)))
      (if (atom label-or-instruction)
          (and (symbolp label-or-instruction)
               (y86-prog rest-program))
        (let ((instruction (car label-or-instruction))
              (args (cdr label-or-instruction)))
          (and (symbolp instruction)
               (true-listp args)
               (case instruction
                 (pos
                  (and (or (and (consp args)
                                (null (cdr args)))
                           (cw "Format:  (POS <memory-address>).~%~p0~%"
                               label-or-instruction))
                       (or (n32p (car args))
                           (cw "POS: ~p0 must be 0..2^32-1.~%~p1~%"
                               (car args) label-or-instruction))))
                 (align
                  (and (or (and (consp args)
                                (null (cdr args)))
                           (cw "Format:  (ALIGN <size>).~%~p0~%"
                               label-or-instruction))
                       (or (and (n32p (car args))
                                (< 0 (car args)))
                           (cw "ALIGN: ~p0 must be 1..2^32-1.~%~p1~%"
                               (car args) label-or-instruction))))
                 (byte
                  (and (or (and (consp args)
                                (null (cdr args)))
                           (cw "Format:  (BYTE <byte>).~%~p0~%"
                               label-or-instruction))
                       (or (n08p (car args))
                           (cw "BYTE: ~p0 must be 0..255.~%~p1~%"
                               (car args) label-or-instruction))))
                 (data
                  (and (or (and (consp args)
                                (null (cdr args)))
                           (cw "Format:  (DATA <32-bit-word>).~%~p0~%"
                               label-or-instruction))
                       (or (n32p (car args))
                           (symbolp (car args))
                           (cw "DATA: ~p0 must symbol or be 0..2^32-1.~%~p1~%"
                               (car args) label-or-instruction))))
                 (space
                  (and (or (and (consp args)
                                (null (cdr args)))
                           (cw "Format:  (SPACE <32-bit-word>).~%~p0~%"
                               label-or-instruction))
                       (or (n32p (car args))
                           (cw "SPACE: ~p0 must be 0..2^32-1.~%~p1~%"
                               (car args) label-or-instruction))))
                 (nop
                  (and (or (null args)
                           (cw "Format is: (NOP).~%~p0~%"
                               label-or-instruction))))
                 (halt
                  (and (or (null args)
                           (cw "Format is: (HALT).~%~p0~%"
                               label-or-instruction))))
                 (rrmovl
                  (and (or (and (consp args)
                                (consp (cdr args))
                                (null (cddr args)))
                           (cw "Format is:  (RRMOVL <reg-a> <reg-b>).~%~p0~%"
                               label-or-instruction))
                       (or (reg-id (car args))
                           (cw "RRMOVL: ~p0 isn't a register ID.~%~p1~%"
                               (car args) label-or-instruction))
                       (or (reg-id (cadr args))
                           (cw "RRMOVL: ~p0 isn't a register ID.~%~p1~%"
                               (cadr args) label-or-instruction))))
                 (irmovl
                  (and (or (and (consp args)
                                (consp (cdr args))
                                (null (cddr args)))
                           (cw "Format is:  (IRMOVL <imm> <reg-b>).~%~p0~%"
                               label-or-instruction))
                       (or (integerp (car args))
                           ;; Used to be stricter, but we now use n32 to
                           ;; fix before writing.
                           ;; (n32p (car args))
                           (symbolp (car args))
                           (cw "IRMOVL: ~p0 must be a label or 0..2^32-1.~%~p1~%"
                               (car args) label-or-instruction))
                       (or (reg-id (cadr args))
                           (cw "IRMOVL: <reg-b> isn't a register ID.~%~p0~%"
                               label-or-instruction))))
                 (rmmovl
                  (and (or (and (consp args)
                                (consp (cdr args))
                                (consp (cddr args))
                                (null (cdddr args))
                                (consp (caddr args))
                                (null (cdr (caddr args))))
                           (cw "Format:  (RMMOVL <reg-a> <displacement> (<reg-b>))~%~p0~%"
                               label-or-instruction))
                       (or (reg-id (car args))
                           (cw "RMMOVL: ~p0 isn't a register ID.~%~p1~%"
                               (car args) label-or-instruction))
                       (or (integerp (cadr args))
                           ;; Used to be stricter, but we now use n32 to
                           ;; fix before writing.
                           ;; (n32p (cadr args))
                           (cw "RMMOVL: ~p0 must be 0..2^32-1.~%~p1~%"
                               (cadr args) label-or-instruction))
                       (or (reg-id (car (caddr args)))
                           (cw "RMMOVL: ~p0 isn't a register ID.~%~p1~%"
                               (caddr args) label-or-instruction))))
                 (mrmovl
                  (and (or (and (consp args)
                                (consp (cdr args))
                                (consp (cddr args))
                                (null (cdddr args))
                                (consp (cadr args))
                                (null (cdr (cadr args))))
                           (cw "Format:  (MRMOVL <displacement> (<reg-a>) <reg-b>)~%~p0~%"
                               label-or-instruction))
                       (or (integerp (car args))
                           ;; Used to be stricter, but we now use n32 to
                           ;; fix before writing.
                           ;; (n32p (car args))
                           (cw "MRMOVL: ~p0 must be 0..2^32-1.~%~p1~%"
                               (cadr args) label-or-instruction))
                       (or (reg-id (car (cadr args)))
                           (cw "MRMOVL: ~p0 isn't a register ID.~%~p1~%"
                               (car (cadr args)) label-or-instruction))
                       (or (reg-id (caddr args))
                           (cw "MRMOVL: ~p0 isn't a register ID.~%~p1~%"
                               (caddr args) label-or-instruction))))
                 ((addl subl andl xorl
                   adcl cmpl orl sall shrl) ; new
                  (and (or (and (consp args)
                                (consp (cdr args))
                                (null (cddr args)))
                           (cw "Format:  (<OP> <reg-a> <reg-b>).~%~p0~%"
                               label-or-instruction))
                       (or (reg-id (car args))
                           (cw "<OP>: ~p0 isn't a register ID.~%~p1~%"
                               (car args) label-or-instruction))
                       (or (reg-id (cadr args))
                           (cw "<OP>: ~p0 isn't a register ID.~%~p1~%"
                               (cadr args) label-or-instruction))))
                 ((jmp jle jl je jne jge jg
                   jb jbe) ; new
                  (and (or (and (consp args)
                                (null (cdr args)))
                           (cw "Format (<Jump-OP> <destination>).~%~p0~%"
                               label-or-instruction))
                       (or (symbolp (car args))
                           (n32p    (car args))
                           (cw "<Jump-OP>: ~p0 must be a label or 0..2^32-1.~%~p1~%"
                               (car args) label-or-instruction))))
                 (call
                  (and (or (and (consp args)
                                (null (cdr args)))
                           (cw "Format (CALL <destination>).~%~p0~%"
                               label-or-instruction))
                       (or (symbolp (car args))
                           (n32p    (car args))
                           (cw "CALL: ~p0 must be a label or 0..2^32-1.~%~p1~%"
                               (car args) label-or-instruction))))
                 (ret
                  (and (or (null args)
                           (cw "Format is: (RET).~%~p0~%"
                               label-or-instruction))))
                 (pushl
                  (and (or (and (consp args)
                                (null (cdr args)))
                           (cw "Format (PUSHL <reg-id>).~%~p0~%"
                               label-or-instruction))
                       (or (reg-id (car args))
                           (cw "PUSHL: ~p0 isn't a register ID.~%~p1~%"
                               (car args) label-or-instruction))))
                 (popl
                  (and (or (and (consp args)
                                (null (cdr args)))
                           (cw "Format (POPL <reg-id>).~%~p0~%"
                               label-or-instruction))
                       (or (reg-id (car args))
                           (cw "POPL: ~p0 isn't a register ID.~%~p1~%"
                               (car args) label-or-instruction))))
                 (iaddl
                  (and (or (and (consp args)
                                (consp (cdr args))
                                (null (cddr args)))
                           (cw "Format is:  (IADDL <imm> <reg-b>).~%~p0~%"
                               label-or-instruction))
                       (or (n32p (car args))
                           (symbolp (car args))
                           (cw "IADDL: ~p0 must be a label or 0..2^32-1.~%~p1~%"
                               (car args) label-or-instruction))
                       (or (reg-id (cadr args))
                           (cw "IADDL: <reg-b> isn't a register ID.~%~p0~%"
                               label-or-instruction))))
                 (leave
                  (and (or (null args)
                           (cw "Format is: (LEAVE).~%~p0~%"
                               label-or-instruction))))
                 (otherwise (cw "~p0 is an unrecognized directive or instruction.~%"
                                instruction)))
               (y86-prog rest-program)))))))

(defun add-label-address-pair (symbol n32p-number symbol-table-alist)
  (acons symbol n32p-number symbol-table-alist))

(defun align-to-mod-n (count mod-amount)
  (let* ((align-to (nfix mod-amount))
         (over-by  (nfix (mod count align-to))))
    (if (zp over-by)
        count
      (n32+ (nfix (- align-to over-by)) count))))

; Produce a symbol table for a Y86 program.

(defun y86-symbol-table (program count symbol-table-alist)
  (if (atom program)
      symbol-table-alist
    (let ((label-or-instruction (car program))
          (rest-program (cdr program)))
      (if (atom label-or-instruction)
          (y86-symbol-table rest-program count
                            (add-label-address-pair label-or-instruction
                                                    count
                                                    symbol-table-alist))
        (let ((instruction (car label-or-instruction))
              (args (cdr label-or-instruction)))
          (case instruction
            (pos
             (y86-symbol-table rest-program
                               (car args)
                               symbol-table-alist))
            (align
             (y86-symbol-table rest-program
                               (align-to-mod-n count (car args))
                               symbol-table-alist))
            (byte
             (y86-symbol-table rest-program (n32+ count 1) symbol-table-alist))
            (data
             (y86-symbol-table rest-program (n32+ count 4) symbol-table-alist))
            (space
             (y86-symbol-table rest-program (n32+ count (car args))
                               symbol-table-alist))
            (nop
             (y86-symbol-table rest-program (n32+ count 1) symbol-table-alist))
            (halt
             (y86-symbol-table rest-program (n32+ count 1) symbol-table-alist))
            (rrmovl
             (y86-symbol-table rest-program (n32+ count 2) symbol-table-alist))
            (irmovl
             (y86-symbol-table rest-program (n32+ count 6) symbol-table-alist))
            (rmmovl
             (y86-symbol-table rest-program (n32+ count 6) symbol-table-alist))
            (mrmovl
             (y86-symbol-table rest-program (n32+ count 6) symbol-table-alist))
            ((addl subl andl xorl
              adcl cmpl orl sall shrl)
             (y86-symbol-table rest-program (n32+ count 2) symbol-table-alist))
            ((jmp jle jl je jne jge jg
              jb jbe)
             (y86-symbol-table rest-program (n32+ count 5) symbol-table-alist))
            (call
             (y86-symbol-table rest-program (n32+ count 5) symbol-table-alist))
            (ret
             (y86-symbol-table rest-program (n32+ count 1) symbol-table-alist))
            (pushl
             (y86-symbol-table rest-program (n32+ count 2) symbol-table-alist))
            (popl
             (y86-symbol-table rest-program (n32+ count 2) symbol-table-alist))
            (iaddl
             (y86-symbol-table rest-program (n32+ count 6) symbol-table-alist))
            (leave
             (y86-symbol-table rest-program (n32+ count 1) symbol-table-alist))
            (otherwise (cw "~p0 is an unrecognized directive or instruction.~%"
                                instruction))))))))

(defun label-address (label symbol-table-alist)
  (let* ((pair (assoc-equal label symbol-table-alist))
         (addr (if (consp pair) (cdr pair) 0)))
    addr))

; Create various instructions...

;;; Note that count should really be address, and program-bytes should
;;; be isa-st.

(defun write-data (count immediate symbol-table-alist program-bytes)
  (w32 count
       (if (symbolp immediate)
           (label-address immediate symbol-table-alist)
         immediate)
       program-bytes))

(defun write-nop (count program-bytes)
  (w08 count
       (n04-n04-to-n08
        (cadr (assoc 'nop *Instructions*))
        0)
       program-bytes))

(defun write-halt (count program-bytes)
  (w08 count
       (n04-n04-to-n08
        (cadr (assoc 'halt *Instructions*))
        0)
       program-bytes))

(defun write-rrmovl (count RegA RegB program-bytes)
    (let* ((pbytes (w08 count
                        (n04-n04-to-n08
                         (cadr (assoc 'rrmovl *Instructions*))
                         0)
                        program-bytes))
           (RegA-id (reg-id RegA))
           (RegB-id (reg-id RegB))
           (reg-specifier (n04-n04-to-n08 RegA-id RegB-id))
           (pbytes (w08 (n32+ count 1) reg-specifier pbytes)))
    pbytes))

(defun write-irmovl (count immediate RegB symbol-table-alist program-bytes)
    (let* ((pbytes (w08 count
                        (n04-n04-to-n08
                         (cadr (assoc 'irmovl *Instructions*))
                         0)
                        program-bytes))
           (RegB-id (reg-id RegB))
           (reg-specifier (n04-n04-to-n08 8 RegB-id))
           (pbytes (w08 (n32+ count 1) reg-specifier pbytes))
           (label-addr (if (symbolp immediate)
                           (label-address immediate symbol-table-alist)
                         (n32 immediate)))
           (pbytes (w32 (n32+ count 2) label-addr pbytes)))
    pbytes))

(defun write-rmmovl (count RegA displacement RegB program-bytes)
    (let* ((pbytes (w08 count
                        (n04-n04-to-n08
                         (cadr (assoc 'rmmovl *Instructions*))
                         0)
                        program-bytes))
           (RegA-id (reg-id RegA))
           (RegB-id (reg-id RegB))
           (reg-specifier (n04-n04-to-n08 RegA-id RegB-id))
           (pbytes (w08 (n32+ count 1) reg-specifier pbytes))
           (pbytes (w32 (n32+ count 2) (n32 displacement) pbytes)))
    pbytes))


(defun write-mrmovl (count displacement RegB RegA program-bytes)
    (let* ((pbytes (w08 count
                        (n04-n04-to-n08
                         (cadr (assoc 'mrmovl *Instructions*))
                         0)
                        program-bytes))
           (RegA-id (reg-id RegA))
           (RegB-id (reg-id RegB))
           (reg-specifier (n04-n04-to-n08 RegA-id RegB-id))
           (pbytes (w08 (n32+ count 1) reg-specifier pbytes))
           (pbytes (w32 (n32+ count 2) (n32 displacement) pbytes)))
    pbytes))

(defun write-op (count instruction RegA RegB program-bytes)
    (let* ((pbytes (w08 count
                        (n04-n04-to-n08
                         (cadr (assoc instruction *Instructions*))
                         (caddr (assoc instruction *Instructions*)))
                        program-bytes))
           (RegA-id (reg-id RegA))
           (RegB-id (reg-id RegB))
           (reg-specifier (n04-n04-to-n08 RegA-id RegB-id))
           (pbytes (w08 (n32+ count 1) reg-specifier pbytes)))
    pbytes))

;;; we make jumps relative, rather than absolute as before
(defun write-jmp (count instruction label symbol-table-alist program-bytes)
    (let* ((pbytes (w08 count
                        (n04-n04-to-n08
                         (cadr (assoc instruction *Instructions*))
                         (caddr (assoc instruction *Instructions*)))
                        program-bytes))
           (label-addr (if (symbolp label)
                           (label-address label symbol-table-alist)
                         label))
           (pbytes (w32 (n32+ count 1) (n32+ label-addr (- count)) pbytes)))
    pbytes))

;;; we make calls relative, rather than absolute as before
(defun write-call (count label symbol-table-alist program-bytes)
  (let* ((pbytes (w08 count
                      (n04-n04-to-n08
                       (cadr (assoc 'call *Instructions*))
                       0)
                      program-bytes))
         (label-addr (if (symbolp label)
                         (label-address label symbol-table-alist)
                       label))
         (pbytes (w32 (n32+ count 1) (n32+ label-addr (- count)) pbytes)))
    pbytes))

(defun write-ret (count program-bytes)
  (w08 count
       (n04-n04-to-n08
        (cadr (assoc 'ret *Instructions*))
        0)
       program-bytes))

(defun write-pushl (count RegA program-bytes)
    (let* ((pbytes (w08 count
                        (n04-n04-to-n08
                         (cadr (assoc 'pushl *Instructions*))
                         0)
                        program-bytes))
           (RegA-id (reg-id RegA))
           (reg-specifier (n04-n04-to-n08 RegA-id 8))
           (pbytes (w08 (n32+ count 1) reg-specifier pbytes)))
    pbytes))

(defun write-popl (count RegA program-bytes)
    (let* ((pbytes (w08 count
                        (n04-n04-to-n08
                         (cadr (assoc 'popl *Instructions*))
                         0)
                        program-bytes))
           (RegA-id (reg-id RegA))
           (reg-specifier (n04-n04-to-n08 RegA-id 8))
           (pbytes (w08 (n32+ count 1) reg-specifier pbytes)))
    pbytes))

(defun write-iaddl (count immediate RegB symbol-table-alist program-bytes)
    (let* ((pbytes (w08 count
                        (n04-n04-to-n08
                         (cadr (assoc 'iaddl *Instructions*))
                         0)
                        program-bytes))
           (RegB-id (reg-id RegB))
           (reg-specifier (n04-n04-to-n08 8 RegB-id))
           (pbytes (w08 (n32+ count 1) reg-specifier pbytes))
           (label-addr (if (symbolp immediate)
                           (label-address immediate symbol-table-alist)
                         immediate))
           (pbytes (w32 (n32+ count 2) label-addr pbytes)))
    pbytes))

(defun write-leave (count program-bytes)
  (w08 count
       (n04-n04-to-n08
        (cadr (assoc 'leave *Instructions*))
        0)
       program-bytes))

; Y86 assembler.

(defun y86-asm (program count symbol-table-alist program-bytes)
  (if (atom program)
      program-bytes
    (let ((label-or-instruction (car program))
          (rest-program (cdr program)))
      (if (atom label-or-instruction)
          (y86-asm rest-program count symbol-table-alist program-bytes)
        (let ((instruction (car label-or-instruction))
              (args (cdr label-or-instruction)))
          (case instruction
            (pos
             (y86-asm rest-program (car args)
                      symbol-table-alist program-bytes))
            (align
             (y86-asm rest-program
                      (align-to-mod-n count (car args))
                      symbol-table-alist program-bytes))
            (data
             (y86-asm rest-program (n32+ count 4)
                      symbol-table-alist
                      (write-data count (car args)
                                  symbol-table-alist
                                  program-bytes)))
            (byte
             (y86-asm rest-program (n32+ count 1)
                      symbol-table-alist
                      (write-data count (car args)
                                  symbol-table-alist
                                  program-bytes)))
            (space
             (y86-asm rest-program (n32+ count (car args))
                      symbol-table-alist
                      program-bytes))
            (nop
             (y86-asm rest-program (n32+ count 1) symbol-table-alist
                      (write-nop count program-bytes)))
            (halt
             (y86-asm rest-program (n32+ count 1) symbol-table-alist
                      (write-halt count program-bytes)))
            (rrmovl
             (y86-asm rest-program (n32+ count 2) symbol-table-alist
                      (write-rrmovl count
                                    (car args)
                                    (cadr args)
                                    program-bytes)))

            (irmovl
             (y86-asm rest-program (n32+ count 6) symbol-table-alist
                      (write-irmovl count
                                    (car args)
                                    (cadr args)
                                    symbol-table-alist
                                    program-bytes)))

            (rmmovl
             (y86-asm rest-program (n32+ count 6) symbol-table-alist
                      (write-rmmovl count
                                    (car args)
                                    (cadr args)
                                    (car (caddr args))
                                    program-bytes)))

            (mrmovl
             (y86-asm rest-program (n32+ count 6) symbol-table-alist
                      (write-mrmovl count
                                    (car args)
                                    (car (cadr args))
                                    (caddr args)
                                    program-bytes)))

            ((addl subl andl xorl
              adcl cmpl orl sall shrl) ; new
             (y86-asm rest-program (n32+ count 2) symbol-table-alist
                      (write-op count instruction (car args) (cadr args)
                                program-bytes)))
            ((jmp jle jl je jne jge jg
              jb jbe) ; new
             (y86-asm rest-program (n32+ count 5) symbol-table-alist
                      (write-jmp count instruction (car args)
                                 symbol-table-alist program-bytes)))

            (call
             (y86-asm rest-program (n32+ count 5) symbol-table-alist
                      (write-call count
                                  (car args)
                                  symbol-table-alist program-bytes)))

            (ret
             (y86-asm rest-program (n32+ count 1) symbol-table-alist
                      (write-ret count program-bytes)))
            (pushl
             (y86-asm rest-program (n32+ count 2) symbol-table-alist
                      (write-pushl count (car args) program-bytes)))
            (popl
             (y86-asm rest-program (n32+ count 2) symbol-table-alist
                      (write-popl count (car args) program-bytes)))
            (iaddl
             (y86-asm rest-program (n32+ count 6) symbol-table-alist
                      (write-iaddl count
                                    (car args)
                                    (cadr args)
                                    symbol-table-alist
                                    program-bytes)))
            (leave
             (y86-asm rest-program (n32+ count 1) symbol-table-alist
                      (write-leave count program-bytes)))
            (otherwise (cw "~p0 is an unrecognized directive or instruction.~%"
                                instruction))))))))

