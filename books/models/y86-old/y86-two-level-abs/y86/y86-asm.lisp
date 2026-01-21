
;  y86-asm.lisp                           Warren A. Hunt, Jr.

(in-package "ACL2")

; !!!  During GUARD proof, CW commands repeated executed and that
; !!!  output is printed to the user.

(include-book "std/util/bstar" :dir :system)

(include-book "../common/misc-events")
(include-book "../common/operations")
(include-book "../common/constants")

; This is an assember for the Y86 simulator, that includes the IADDL
; and the LEAVE instructions.

; Input to our Y86 assembler is given as a proper list containing
; instructions, symbols (labels), and assember directives.

; This is a two-pass assembler.  The first pass reads the entire input
; and returns a fast association list with symbols (labels) paired
; with their memory address.  The second pass creates an association
; list pairing memory byte-addresses with their contents; the actual
; Y86 memory (STOBJ) image is initialized using this association list.

; The assembler maintains a memory address <asm-addr> where the next
; assembler directive or instruction will take effect, and then the
; <asm-addr> is altered as necessary.  For example, if a NOP
; instruction is found, the byte #x10 will be inserted into an
; evolving memory image at address <asm-addr> and then, <asm-addr>
; will be increase by 1 (byte).  Blank space is one or more spaces
; newlines and/or tabs, and assmebler directives can be spaced and
; formated as desired.

; The assembler includes directives that associate a label with the
; current valud of <asm-addr>, that change <asm-addr>, and that create
; specific data to be placed in the memory.

;   <label>       ; Name for specific <asm-addr>

;   (pos   <n>)   ; Set <asm-addr> to <n>
;   (align <n>)   ; <asm-addr> set to (+ <asm-addr>
;                                      (MOD <asm-addr> (expt 2 <n>)))
;   (space <n>)   ; <asm-addr> set to (+ <asm-addr> <n>)

; Write sequence of bytes, words starting at address <asm-addr>, and
; advance <asm-addr> by the number of bytes required for the data.

;   (byte  <a> <b> <c> ...)  ; Write byte(s)        <a> <b> <c> ...
;   (dword <a> <b> <c> ...)  ; Write 32-bit word(s) <a> <b> <c> ...
;   (char  #\a #\b #\c ...)  ; Write character(s)   #\a #\b #\c ...
;   (string    "abc...def")  ; Write string as sequence of characters

; Y86 control, NOP instructions

;   (halt)
;   (nop)

; Y86 move instructions

; (rrmovl <reg-id-or-n03p> <reg-id-or-n03p>)
; (cmovle <reg-id-or-n03p> <reg-id-or-n03p>)
; (cmovl  <reg-id-or-n03p> <reg-id-or-n03p>)
; (cmove  <reg-id-or-n03p> <reg-id-or-n03p>)
; (cmovne <reg-id-or-n03p> <reg-id-or-n03p>)
; (cmovge <reg-id-or-n03p> <reg-id-or-n03p>)
; (cmovg  <reg-id-or-n03p> <reg-id-or-n03p>)

; (irmovl <label-or-n32p> <reg-id-or-n03p>)
; (rmmovl <reg-id-or-n03p> <label-or-n32p> (<reg-id-or-n03p>))
; (mrmovl <label-or-n32p> (<reg-id-or-n03p>) <reg-id-or-n03p>)

; Y86 logical/arithmetic instructions

; (addl  <reg-id-or-n03p> <reg-id-or-n03p>)
; (subl  <reg-id-or-n03p> <reg-id-or-n03p>)
; (andl  <reg-id-or-n03p> <reg-id-or-n03p>)
; (xorl  <reg-id-or-n03p> <reg-id-or-n03p>)
; (iaddl <label-or-n32p>  <reg-id-or-n03p>)

; Y86 flow of control instructions

; (jmp <label-or-n32p>)
; (jle <label-or-n32p>)
; (jl  <label-or-n32p>)
; (je  <label-or-n32p>)
; (jne <label-or-n32p>)
; (jge <label-or-n32p>)
; (jg  <label-or-n32p>)

; (call <label-or-n32p>)
; (ret)
; (leave)

; Y86 stack instructions

; (pushl <reg-id-or-n03p>)
; (popl  <reg-id-or-n03p>)


(defun symbol-or-n32-listp (lst)
  (declare (xargs :guard t))
  (if (atom lst)
      (null lst)
    (and (or (symbolp (car lst))
             (n32p (car lst)))
         (symbol-or-n32-listp (cdr lst)))))

; Evolving memory image produced by the assembler is kept in a "fast"
; association list.  Below we define functions to read and write the
; evolving, byte-addressed memory image.

(defun n32p-n08p-alistp (alst)
  (declare (xargs :guard t))
  (if (atom alst)
      t
    (if (atom (car alst))
        nil
      (let ((symbol (caar alst))
            (val    (cdar alst))
            (rest   (cdr  alst)))
        (and (n32p symbol)
             (n08p val)
             (n32p-n08p-alistp rest))))))

(defund r08 (address memory)
  (declare (xargs :guard (and (n32p address)
                              (n32p-n08p-alistp memory))))
  (let ((addr-byte (hons-get address memory)))
    (if (atom addr-byte)
        (or (cw "r08: no value found at address ~p0.~%" address) 0)
      (nfix (cdr addr-byte)))))

(defund r16 (address memory)
  (declare (xargs :guard (and (n32p address)
                              (n32p-n08p-alistp memory))))
  (let ((byte0 (r08 address memory))
        (byte1 (r08 (n32+ address 1) memory)))
    (n16+ (ash byte1 8) byte0)))

(defund r32 (address memory)
  (declare (xargs :guard (and (n32p address)
                              (n32p-n08p-alistp memory))))
  (let ((byte0 (r08 address memory))
        (byte1 (r08 (n32+ address 1) memory))
        (byte2 (r08 (n32+ address 2) memory))
        (byte3 (r08 (n32+ address 3) memory)))
    (n32+ (ash byte3 24)
          (n32+ (ash byte2 16)
                (n32+ (ash byte1 8) byte0)))))

(defun w08 (address value memory)
  (declare (xargs :guard (and (n32p address)
                              (n08p value)
                              (n32p-n08p-alistp memory))))
  (hons-acons address value memory))

(defthm n32p-n08p-alistp-w08
  (implies (and (n32p address)
                (n08p value)
                (n32p-n08p-alistp memory))
           (n32p-n08p-alistp (w08 address value memory))))

(in-theory (disable w08))

(defun w16 (address value memory)
  (declare (xargs :guard (and (n32p address)
                              (n16p value)
                              (n32p-n08p-alistp memory))))
  (let ((byte0 (n08 value))
        (byte1 (n08 (ash value -8))))
    (let* ((memory (hons-acons       address    byte0 memory))
           (memory (hons-acons (n32+ address 1) byte1 memory)))
      memory)))

(defthm n32p-n08p-alistp-w16
  (implies (and (n32p address)
                (n16p value)
                (n32p-n08p-alistp memory))
           (n32p-n08p-alistp (w16 address value memory))))

(in-theory (disable w16))

(defun w32 (address value memory)
  (declare (xargs :guard (and (n32p address)
                              (n32p value)
                              (n32p-n08p-alistp memory))))
  (let ((byte0 (n08 value))
        (byte1 (n08 (ash value -8)))
        (byte2 (n08 (ash value -16)))
        (byte3 (n08 (ash value -24))))
    (let* ((memory (hons-acons       address    byte0 memory))
           (memory (hons-acons (n32+ address 1) byte1 memory))
           (memory (hons-acons (n32+ address 2) byte2 memory))
           (memory (hons-acons (n32+ address 3) byte3 memory)))
      memory)))

(defthm n32p-n08p-alistp-w32
  (implies (and (n32p address)
                (n32p value)
                (n32p-n08p-alistp memory))
           (n32p-n08p-alistp (w32 address value memory))))

(in-theory (disable w32))

; Convert register name to register number; otherwise, return NIL.

(defun reg-id (reg)
  (declare (xargs :guard t))
  (and (symbolp reg) (rtn reg)))

(defthm natp-reg-id
  (or (null (reg-id x))
      (and (integerp (reg-id x))
           (<= 0 (reg-id x))))
  :rule-classes :type-prescription)

(defthm reg-id-<-8
  (implies (reg-id x)
           (< (reg-id x) 8))
  :rule-classes :linear)

(in-theory (disable reg-id))


; (defthm n08p-char-code
;   (n08p (char-code x)))

; Syntactic recognizers for the assembler.

;; (defun n32-symbol-listp (x)
;;   (declare (xargs :guard t))
;;   (if (atom x)
;;       (null x)
;;     (and (or (n32p (car x))
;;              (symbolp (car x)))
;;          (n32-symbol-listp (cdr x)))))


; Symbol table recognizer

(defun symbol-n32p-alistp (alst)
  (declare (xargs :guard t))
  (if (atom alst)
      t
    (if (atom (car alst))
        nil
      (let ((symbol (caar alst))
            (val    (cdar alst))
            (rest   (cdr  alst)))
        (and (symbolp symbol)
             (n32p val)
             (symbol-n32p-alistp rest))))))

(defun add-label-address-pair (sym addr symbol-table-alist)
  (declare (xargs :guard (and (symbolp sym)
                              (n32p addr)
                              (symbol-n32p-alistp symbol-table-alist))))
  (hons-acons sym addr symbol-table-alist))

(defthm symbol-alist-add-label-address-pair
  (implies (and (symbolp sym)
                (n32p addr)
                (symbol-n32p-alistp symbol-table-alist))
           (symbol-n32p-alistp
            (add-label-address-pair sym addr symbol-table-alist))))

(in-theory (disable add-label-address-pair))

; !!! Get some help from Robert.

(defun align-to-mod-n (count mod-amount)
  (declare (xargs :guard (and (n32p count)
                              (n32p mod-amount)
                              (not (eql mod-amount 0)))
                  :guard-debug t
                  :guard-hints (("Goal" :in-theory (e/d () (mod))))
                  ))
  (let* ((over-by (n32 (mod count mod-amount))))
    (if (= over-by 0)
        count
      (n32+ (n32 (- mod-amount over-by)) count))))

(defthm natp-align-to-mod-n
  (implies (n32p count)
           (and (integerp (align-to-mod-n count mod-amount))
                (<= 0 (align-to-mod-n count mod-amount))))
  :rule-classes :type-prescription)

(defthm align-to-mod-n-<-4294967296
  (implies (n32p count)
           (< (align-to-mod-n count mod-amount) 4294967296))
  :rule-classes :linear)

(in-theory (disable align-to-mod-n))

; Database of information for assembler.

(defconst *Arity*
  '((pos      1)
    (align    1)
    (space    1)
    (byte     1)
    (dword    1)
    (char     1)
    (string   1)
    (nop      0)
    (halt     0)
    (rrmovl   2)
    (cmovle   2)
    (cmovl    2)
    (cmove    2)
    (cmovne   2)
    (cmovge   2)
    (cmovg    2)
    (irmovl   2)
    (rmmovl   3)
    (mrmovl   3)
    (addl     2)
    (subl     2)
    (andl     2)
    (xorl     2)
    (jmp      1)
    (jle      1)
    (jl       1)
    (je       1)
    (jne      1)
    (jge      1)
    (jg       1)
    (call     1)
    (ret      0)
    (pushl    1)
    (popl     1)
    (iaddl    2)
    (leave    0)
    (noop     0)
    ))


; Instruction values.

(defconst *Instructions*
  '((halt     0)
    (nop      1)
    (rrmovl   2)
    (cmovle   2 1)
    (cmovl    2 2)
    (cmove    2 3)
    (cmovne   2 4)
    (cmovge   2 5)
    (cmovg    2 6)
    (irmovl   3)
    (rmmovl   4)
    (mrmovl   5)
    (addl     6 0)
    (subl     6 1)
    (andl     6 2)
    (xorl     6 3)
    (jmp      7 0)
    (jle      7 1)
    (jl       7 2)
    (je       7 3)
    (jne      7 4)
    (jge      7 5)
    (jg       7 6)
    (call     8)
    (ret      9)
    (pushl   10)
    (popl    11)
    (iaddl   12)
    (leave   13)
    (noop    15) ;; Second NOP instruction
    ))

; !!!  During GUARD proof, CW commands repeated executed and that
; !!!  output is printed to the user.

(defun n08-listp (x)
  (declare (xargs :guard t))
  (if (atom x)
      (null x)
    (and (n08p (car x))
         (n08-listp (cdr x)))))

(defun y86-prog (program)
  (declare (xargs :guard t))
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
                           (cw "Format:  (POS <memory-address>).~%"))
                       (or (n32p (car args))
                           (cw "POS: ~p0 must be 0..2^32-1.~%" (car args)))))
                 (align
                  (and (or (and (consp args)
                                (null (cdr args)))
                           (cw "Format:  (ALIGN <size>).~%"))
                       (or (and (n32p (car args))
                                (< 1 (car args)))
                           (cw "ALIGN: ~p0 must be 2..2^32-1.~%" (car args)))))
                 (byte
                  (or (n08-listp args)
                      (cw "Format:  (BYTE <byte0> <byte1> ...).~%")
                      (cw "BYTE: ~p0 must be 0..255 ....~%" args)))
                 (dword
                  (or (symbol-or-n32-listp args)
                      (cw "Format:  (DWORD <symbol-or-32-bit-word> ...).~%")
                      (cw "DWORD: ~p0 must be <symbol> or 0..2^32-1 ...~%" args)))
                 (char
                  (or (character-listp args)
                      (cw "Format:  (CHAR <char0> <char1> ...).~%")
                      (cw "CHAR: ~p0 must be <char> ...~%" args)))
                 (string
                  (and (or (and (consp args)
                                (null (cdr args)))
                           (cw "Format:  (STRING \"<string>\".~%"))
                       (or (stringp (car args))
                           (cw "STRING: ~p0 must be a string.~%" (car args)))))
                 (space
                  (and (or (and (consp args)
                                (null (cdr args)))
                           (cw "Format:  (SPACE <32-bit-word>).~%"))
                       (or (n32p (car args))
                           (cw "SPACE: ~p0 must be 0..2^32-1.~%" (car args)))))
                 (nop
                  (and (or (null args)
                           (cw "Format is: (NOP).~%"))))
                 (halt
                  (and (or (null args)
                           (cw "Format is: (HALT).~%"))))
                 (rrmovl
                  (and (or (and (consp args)
                                (consp (cdr args))
                                (null (cddr args)))
                           (cw "Format is:  (RRMOVL <reg-a> <reg-b>).~%"))
                       (or (reg-id (car args))
                           (cw "RRMOVL: ~p0 isn't a register ID.~%" (car args)))
                       (or (reg-id (cadr args))
                           (cw "RRMOVL: ~p0 isn't a register ID.~%" (cadr args)))))
                 ((cmovle cmovl cmove cmovne cmovge cmovg)
                  (and (or (and (consp args)
                                (consp (cdr args))
                                (null (cddr args)))
                           (cw "Format is:  (CMOVL? <reg-a> <reg-b>).~%"))
                       (or (reg-id (car args))
                           (cw "CMOVL?: ~p0 isn't a register ID.~%" (car args)))
                       (or (reg-id (cadr args))
                           (cw "CMOVL?: ~p0 isn't a register ID.~%" (cadr args)))))
                 (irmovl
                  (and (or (and (consp args)
                                (consp (cdr args))
                                (null (cddr args)))
                           (cw "Format is:  (IRMOVL <imm> <reg-b>).~%"))
                       (or (symbolp (car args))
                           (n32p (car args))
                           (cw "IRMOVL: ~p0 must be a label or 0..2^32-1.~%"
                               (car args)))
                       (or (reg-id (cadr args))
                           (cw "IRMOVL: <reg-b> isn't a register ID.~%"))))
                 (rmmovl
                  (and (or (and (consp args)
                                (consp (cdr args))
                                (consp (cddr args))
                                (null (cdddr args))
                                (consp (caddr args))
                                (null (cdr (caddr args))))
                           (cw "Format:  (RMMOVL <reg-a> <displacement> (<reg-b>))"))
                       (or (reg-id (car args))
                           (cw "RMMOVL: ~p0 isn't a register ID.~%" (car args)))
                       (or (symbolp (cadr args))
                           (n32p (cadr args))
                           (cw "RMMOVL: ~p0 must be a label or 0..2^32-1.~%"
                               (cadr args)))
                       (or (reg-id (car (caddr args)))
                           (cw "RMMOVL: ~p0 isn't a register ID.~%" (caddr args)))))
                 (mrmovl
                  (and (or (and (consp args)
                                (consp (cdr args))
                                (consp (cddr args))
                                (null (cdddr args))
                                (consp (cadr args))
                                (null (cdr (cadr args))))
                           (cw "Format:  (MRMOVL <displacement> (<reg-a>) <reg-b>)"))
                       (or (symbolp (car args))
                           (n32p (car args))
                           (cw "MRMOVL: ~p0 must be a label or 0..2^32-1.~%"
                               (cadr args)))
                       (or (reg-id (car (cadr args)))
                           (cw "MRMOVL: ~p0 isn't a register ID.~%"
                               (car (cadr args))))
                       (or (reg-id (caddr args))
                           (cw "MRMOVL: ~p0 isn't a register ID.~%" (caddr args)))))
                 ((addl subl andl xorl)
                  (and (or (and (consp args)
                                (consp (cdr args))
                                (null (cddr args)))
                           (cw "Format:  (<OP> <reg-a> <reg-b>).~%"))
                       (or (reg-id (car args))
                           (cw "<OP>: ~p0 isn't a register ID.~%" (car args)))
                       (or (reg-id (cadr args))
                           (cw "<OP>: ~p0 isn't a register ID.~%" (cadr args)))))
                 ((jmp jle jl je jne jge jg)
                  (and (or (and (consp args)
                                (null (cdr args)))
                           (cw "Format (<Jump-OP> <destination>).~%"))
                       (or (symbolp (car args))
                           (n32p    (car args))
                           (cw "<Jump-OP>: ~p0 must be a label or 0..2^32-1.~%"
                               (car args)))))
                 (call
                  (and (or (and (consp args)
                                (null (cdr args)))
                           (cw "Format (CALL <destination>).~%"))
                       (or (symbolp (car args))
                           (n32p    (car args))
                           (cw "CALL: ~p0 must be a label or 0..2^32-1.~%"
                               (car args)))))
                 (ret
                  (and (or (null args)
                           (cw "Format is: (RET).~%"))))
                 (pushl
                  (and (or (and (consp args)
                                (null (cdr args)))
                           (cw "Format (PUSHL <reg-id>).~%"))
                       (or (reg-id (car args))
                           (cw "PUSHL: ~p0 isn't a register ID.~%" (car args)))))
                 (popl
                  (and (or (and (consp args)
                                (null (cdr args)))
                           (cw "Format (POPL <reg-id>).~%"))
                       (or (reg-id (car args))
                           (cw "POPL: ~p0 isn't a register ID.~%" (car args)))))
                 (iaddl
                  (and (or (and (consp args)
                                (consp (cdr args))
                                (null (cddr args)))
                           (cw "Format is:  (IADDL <imm> <reg-b>).~%"))
                       (or (symbolp (car args))
                           (n32p (car args))
                           (cw "IADDL: ~p0 must be a label or 0..2^32-1.~%"
                               (car args)))
                       (or (reg-id (cadr args))
                           (cw "IADDL: <reg-b> isn't a register ID.~%"))))
                 (leave
                  (and (or (null args)
                           (cw "Format is: (LEAVE).~%"))))
                 (noop
                  (and (or (null args)
                           (cw "Format is: (NOOP).~%"))))
                 (otherwise (cw "~p0 is an unrecognized directive or instruction.~%"
                                instruction)))
               (y86-prog rest-program)))))))


; Produce a symbol table for a Y86 program.

(defun y86-symbol-table (program count symbol-table-alist)
  (declare (xargs :guard (and (y86-prog program)
                              (n32p count)
                              (symbol-n32p-alistp symbol-table-alist))))
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
             (y86-symbol-table rest-program
                               (n32+ count (len args))
                               symbol-table-alist))
            (dword
             (y86-symbol-table rest-program
                               (n32+ count (* 4 (len args)))
                               symbol-table-alist))
            (char
             (y86-symbol-table rest-program
                               (n32+ count (len args))
                               symbol-table-alist))
            (string
             (y86-symbol-table rest-program
                               (n32+ count (length (car args)))
                               symbol-table-alist))
            (space
             (y86-symbol-table rest-program (n32+ count (car args))
                               symbol-table-alist))
            (nop
             (y86-symbol-table rest-program (n32+ count 1) symbol-table-alist))
            (halt
             (y86-symbol-table rest-program (n32+ count 1) symbol-table-alist))
            (rrmovl
             (y86-symbol-table rest-program (n32+ count 2) symbol-table-alist))
            ((cmovle cmovl cmove cmovne cmovge cmovg)
             (y86-symbol-table rest-program (n32+ count 2) symbol-table-alist))
            (irmovl
             (y86-symbol-table rest-program (n32+ count 6) symbol-table-alist))
            (rmmovl
             (y86-symbol-table rest-program (n32+ count 6) symbol-table-alist))
            (mrmovl
             (y86-symbol-table rest-program (n32+ count 6) symbol-table-alist))
            ((addl subl andl xorl)
             (y86-symbol-table rest-program (n32+ count 2) symbol-table-alist))
            ((jmp jle jl je jne jge jg)
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
            (noop
             (y86-symbol-table rest-program (n32+ count 1) symbol-table-alist))
            (otherwise symbol-table-alist)))))))

(defun label-address (label symbol-table-alist)
  (declare (xargs :guard (and (symbolp label)
                              (symbol-n32p-alistp symbol-table-alist))))
  (let* ((pair (hons-get label symbol-table-alist))
         (addr (if (consp pair)
                   (cdr pair)
                 (or (cw "Label ~p0 was not found in the symbol table.~%"
                         label)
                     0))))
    addr))

(defthm symbol-n32p-alistp-label-address
  (implies (symbol-n32p-alistp symbol-table-alist)
           (and (integerp (label-address label symbol-table-alist))
                (n32p (label-address label symbol-table-alist)))))

(in-theory (disable label-address))

; Create various instructions...

(defun n04-n04-to-n08 (x y)
  (declare (xargs :guard (and (n04p x) (n04p y))))
  (n08 (logior y (ash x 4))))

(defthm natp-n04-n04-to-n08
  (and (integerp (n04-n04-to-n08 x y))
       (<= 0 (n04-n04-to-n08 x y)))
  :rule-classes :type-prescription)

(defthm n04-n04-to-n08-<-256
  (< (n04-n04-to-n08 x y) 256)
  :rule-classes :linear)

(in-theory (disable n04-n04-to-n08))


(defun write-bytes (count byte-list program-bytes)
  (declare (xargs :guard (and (n32p count)
                              (n08-listp byte-list)
                              (n32p-n08p-alistp program-bytes))
                  :verify-guards nil))
  (if (atom byte-list)
      program-bytes
    (w08 count
         (car byte-list)
         (write-bytes (n32+ count 1)
                      (cdr byte-list)
                      program-bytes))))

(defthm n32p-n08p-alistp-write-bytes
  (implies (and (n32p count)
                (n08-listp byte-list)
                (n32p-n08p-alistp program-bytes))
           (n32p-n08p-alistp (write-bytes count byte-list program-bytes))))

(verify-guards write-bytes)
(in-theory (disable write-bytes))


(defun write-dwords (count dword-list symbol-table-alist program-bytes)
  (declare (xargs :guard (and (n32p count)
                              (symbol-or-n32-listp dword-list)
                              (symbol-n32p-alistp symbol-table-alist)
                              (n32p-n08p-alistp program-bytes))
                  :verify-guards nil))
  (if (atom dword-list)
      program-bytes
    (w32 count
         (if (symbolp (car dword-list))
             (label-address (car dword-list) symbol-table-alist)
           (car dword-list))
         (write-dwords (n32+ count 4)
                       (cdr dword-list)
                       symbol-table-alist
                       program-bytes))))

(defthm n32p-n08p-alistp-write-dwords
  (implies (and (n32p count)
                (symbol-or-n32-listp dword-list)
                (symbol-n32p-alistp symbol-table-alist)
                (n32p-n08p-alistp program-bytes))
           (n32p-n08p-alistp
            (write-dwords count dword-list symbol-table-alist program-bytes))))

(verify-guards write-dwords)
(in-theory (disable write-dwords))


(defun write-chars (count char-list program-bytes)
  (declare (xargs :guard (and (n32p count)
                              (character-listp char-list)
                              (n32p-n08p-alistp program-bytes))
                  :verify-guards nil))
  (if (atom char-list)
      program-bytes
    (w08 count
         (char-code (car char-list))
         (write-chars (n32+ count 1)
                      (cdr char-list)
                      program-bytes))))

(defthm n32p-n08p-alistp-write-chars
  (implies (and (n32p count)
                (character-listp char-list)
                (n32p-n08p-alistp program-bytes))
           (n32p-n08p-alistp (write-chars count char-list program-bytes))))

(verify-guards write-chars)
(in-theory (disable write-chars))


(defun write-str (count str program-bytes)
  (declare (xargs :guard (and (n32p count)
                              (stringp str)
                              (n32p-n08p-alistp program-bytes))))
  (write-chars count (coerce str 'list) program-bytes))

(defthm n32p-n08p-alistp-write-str
  (implies (and (n32p count)
                (stringp str)
                (n32p-n08p-alistp program-bytes))
           (n32p-n08p-alistp (write-str count str program-bytes))))

(in-theory (disable write-str))


(defun write-nop (count program-bytes)
  (declare (xargs :guard (and (n32p count)
                              (n32p-n08p-alistp program-bytes))))
  (w08 count
       (n04-n04-to-n08
        (cadr (assoc 'nop *Instructions*))
        0)
       program-bytes))

(defthm n32p-n08p-alistp-write-nop
  (implies (and (n32p count)
                (n32p-n08p-alistp program-bytes))
           (n32p-n08p-alistp (write-nop count program-bytes))))

(in-theory (disable write-nop))


(defun write-halt (count program-bytes)
  (declare (xargs :guard (and (n32p count)
                              (n32p-n08p-alistp program-bytes))))
  (w08 count
       (n04-n04-to-n08
        (cadr (assoc 'halt *Instructions*))
        0)
       program-bytes))

(defthm n32p-n08p-alistp-write-halt
  (implies (and (n32p count)
                (n32p-n08p-alistp program-bytes))
           (n32p-n08p-alistp (write-halt count program-bytes))))

(in-theory (disable write-nop))


(defun write-rrmovl (count RegA RegB program-bytes)
  (declare (xargs :guard (and (n32p count)
                              (reg-id RegA)
                              (reg-id RegB)
                              (n32p-n08p-alistp program-bytes))))
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

(defthm n32p-n08p-alistp-write-rrmovl
  (implies (and (n32p count)
                (reg-id RegA)
                (reg-id RegB)
                (n32p-n08p-alistp program-bytes))
           (n32p-n08p-alistp
            (write-rrmovl count RegA RegB program-bytes))))

(in-theory (disable write-rrmovl))


(defun write-cmovl (count RegA RegB program-bytes)
  (declare (xargs :guard (and (n32p count)
                              (reg-id RegA)
                              (reg-id RegB)
                              (n32p-n08p-alistp program-bytes))))
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

(defthm n32p-n08p-alistp-write-cmovl
  (implies (and (n32p count)
                (reg-id RegA)
                (reg-id RegB)
                (n32p-n08p-alistp program-bytes))
           (n32p-n08p-alistp
            (write-cmovl count RegA RegB program-bytes))))

(in-theory (disable write-cmovl))


(defun write-irmovl (count immediate RegB symbol-table-alist program-bytes)
  (declare (xargs :guard (and (n32p count)
                              (or (symbolp immediate)
                                  (n32p immediate))
                              (reg-id RegB)
                              (symbol-n32p-alistp symbol-table-alist)
                              (n32p-n08p-alistp program-bytes))))
  (let* ((pbytes (w08 count
                      (n04-n04-to-n08
                       (cadr (assoc 'irmovl *Instructions*))
                       0)
                      program-bytes))
         (RegB-id (reg-id RegB))
         (reg-specifier (n04-n04-to-n08 15 RegB-id))
         (pbytes (w08 (n32+ count 1) reg-specifier pbytes))
         (label-addr (if (symbolp immediate)
                         (label-address immediate symbol-table-alist)
                       immediate))
         (pbytes (w32 (n32+ count 2) label-addr pbytes)))
    pbytes))

(defthm n32p-n08p-alistp-write-irmovl
  (implies (and (n32p count)
                (or (symbolp immediate)
                    (n32p immediate))
                (reg-id RegB)
                (symbol-n32p-alistp symbol-table-alist)
                (n32p-n08p-alistp program-bytes))
           (n32p-n08p-alistp
            (write-irmovl count immediate RegB symbol-table-alist program-bytes))))

(in-theory (disable write-irmovl))


(defun write-rmmovl (count RegA displacement RegB symbol-table-alist program-bytes)
  (declare (xargs :guard (and (n32p count)
                              (reg-id RegA)
                              (or (symbolp displacement)
                                  (n32p displacement))
                              (reg-id RegB)
                              (symbol-n32p-alistp symbol-table-alist)
                              (n32p-n08p-alistp program-bytes))))
  (let* ((pbytes (w08 count
                      (n04-n04-to-n08
                       (cadr (assoc 'rmmovl *Instructions*))
                       0)
                      program-bytes))
         (RegA-id (reg-id RegA))
         (RegB-id (reg-id RegB))
         (reg-specifier (n04-n04-to-n08 RegA-id RegB-id))
         (pbytes (w08 (n32+ count 1) reg-specifier pbytes))
         (displace (if (symbolp displacement)
                       (label-address displacement symbol-table-alist)
                     displacement))
         (pbytes (w32 (n32+ count 2) displace pbytes)))
    pbytes))

(defthm n32p-n08p-alistp-write-rmmovl
  (implies (and (n32p count)
                (reg-id RegA)
                (or (symbolp displacement)
                    (n32p displacement))
                (reg-id RegB)
                (symbol-n32p-alistp symbol-table-alist)
                (n32p-n08p-alistp program-bytes))
           (n32p-n08p-alistp
            (write-rmmovl count RegA displacement RegB
                          symbol-table-alist program-bytes))))

(in-theory (disable write-rmmovl))


(defun write-mrmovl (count displacement RegA RegB symbol-table-alist program-bytes)
  (declare (xargs :guard (and (n32p count)
                              (or (symbolp displacement)
                                  (n32p displacement))
                              (reg-id RegA)
                              (reg-id RegB)
                              (symbol-n32p-alistp symbol-table-alist)
                              (n32p-n08p-alistp program-bytes))))
  (let* ((pbytes (w08 count
                      (n04-n04-to-n08
                       (cadr (assoc 'mrmovl *Instructions*))
                       0)
                      program-bytes))
         (RegA-id (reg-id RegA))
         (RegB-id (reg-id RegB))
         (reg-specifier (n04-n04-to-n08 RegA-id RegB-id))
         (pbytes (w08 (n32+ count 1) reg-specifier pbytes))
         (displace (if (symbolp displacement)
                       (label-address displacement symbol-table-alist)
                     displacement))
         (pbytes (w32 (n32+ count 2) displace pbytes)))
    pbytes))

(defthm n32p-n08p-alistp-write-mrmovl
  (implies (and (n32p count)
                (or (symbolp displacement)
                    (n32p displacement))
                (reg-id RegA)
                (reg-id RegB)
                (symbol-n32p-alistp symbol-table-alist)
                (n32p-n08p-alistp program-bytes))
           (n32p-n08p-alistp
            (write-mrmovl count displacement RegA RegB
                          symbol-table-alist program-bytes))))

(in-theory (disable write-mrmovl))


(defun write-op (count instruction RegA RegB program-bytes)
  (declare (xargs :guard (and (n32p count)
                              (or (equal instruction 'xorl)
                                  (equal instruction 'andl)
                                  (equal instruction 'addl)
                                  (equal instruction 'subl))
                              (reg-id RegA)
                              (reg-id RegB)
                              (n32p-n08p-alistp program-bytes))))
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

(defthm n32p-n08p-alistp-write-op
  (implies (and (n32p count)
                (reg-id RegA)
                (reg-id RegB)
                (symbol-n32p-alistp symbol-table-alist)
                (n32p-n08p-alistp program-bytes))
           (n32p-n08p-alistp
            (write-op count instruction RegA RegB program-bytes))))

(in-theory (disable write-op))


(defun write-jmp (count instruction label symbol-table-alist program-bytes)
  (declare (xargs :guard (and (n32p count)
                              (symbolp instruction)
                              (or (equal instruction 'jmp)
                                  (equal instruction 'jle)
                                  (equal instruction 'jl)
                                  (equal instruction 'je)
                                  (equal instruction 'jne)
                                  (equal instruction 'jge)
                                  (equal instruction 'jg))
                              (or (symbolp label)
                                  (n32p label))
                              (symbol-n32p-alistp symbol-table-alist)
                              (n32p-n08p-alistp program-bytes))))
  (let* ((pbytes (w08 count
                      (n04-n04-to-n08
                       (cadr (assoc instruction *Instructions*))
                       (caddr (assoc instruction *Instructions*)))
                      program-bytes))
         (label-addr (if (symbolp label)
                         (label-address label symbol-table-alist)
                       label))
         (pbytes (w32 (n32+ count 1) label-addr pbytes)))
    pbytes))

(defthm n32p-n08p-alistp-write-jmp
  (implies (and (n32p count)
                (or (symbolp label)
                    (n32p label))
                (symbol-n32p-alistp symbol-table-alist)
                (n32p-n08p-alistp program-bytes))
           (n32p-n08p-alistp
            (write-jmp count instruction label symbol-table-alist program-bytes))))

(in-theory (disable write-jmp))


(defun write-call (count label symbol-table-alist program-bytes)
  (declare (xargs :guard (and (n32p count)
                              (or (symbolp label)
                                  (n32p label))
                              (symbol-n32p-alistp symbol-table-alist)
                              (n32p-n08p-alistp program-bytes))))
  (let* ((pbytes (w08 count
                      (n04-n04-to-n08
                       (cadr (assoc 'call *Instructions*))
                       0)
                      program-bytes))
         (label-addr (if (symbolp label)
                         (label-address label symbol-table-alist)
                       label))
         (pbytes (w32 (n32+ count 1) label-addr pbytes)))
    pbytes))

(defthm n32p-n08p-alistp-write-call
  (implies (and (n32p count)
                (or (symbolp label)
                    (n32p label))
                (symbol-n32p-alistp symbol-table-alist)
                (n32p-n08p-alistp program-bytes))
           (n32p-n08p-alistp
            (write-call count label symbol-table-alist program-bytes))))

(in-theory (disable write-call))


(defun write-ret (count program-bytes)
  (declare (xargs :guard (and (n32p count)
                              (n32p-n08p-alistp program-bytes))))
  (w08 count
       (n04-n04-to-n08
        (cadr (assoc 'ret *Instructions*))
        0)
       program-bytes))

(defthm n32p-n08p-alistp-write-ret
  (implies (and (n32p count)
                (n32p-n08p-alistp program-bytes))
           (n32p-n08p-alistp
            (write-ret count program-bytes))))

(in-theory (disable write-ret))


(defun write-pushl (count RegA program-bytes)
  (declare (xargs :guard (and (n32p count)
                              (reg-id RegA)
                              (n32p-n08p-alistp program-bytes))))
  (let* ((pbytes (w08 count
                      (n04-n04-to-n08
                       (cadr (assoc 'pushl *Instructions*))
                       0)
                      program-bytes))
         (RegA-id (reg-id RegA))
         (reg-specifier (n04-n04-to-n08 RegA-id 15))
         (pbytes (w08 (n32+ count 1) reg-specifier pbytes)))
    pbytes))

(defthm n32p-n08p-alistp-write-pushl
  (implies (and (n32p count)
                (reg-id RegA)
                (n32p-n08p-alistp program-bytes))
           (n32p-n08p-alistp
            (write-pushl count RegA program-bytes))))

(in-theory (disable write-pushl))


(defun write-popl (count RegA program-bytes)
  (declare (xargs :guard (and (n32p count)
                              (reg-id RegA)
                              (n32p-n08p-alistp program-bytes))))
  (let* ((pbytes (w08 count
                      (n04-n04-to-n08
                       (cadr (assoc 'popl *Instructions*))
                       0)
                      program-bytes))
         (RegA-id (reg-id RegA))
         (reg-specifier (n04-n04-to-n08 RegA-id 15))
         (pbytes (w08 (n32+ count 1) reg-specifier pbytes)))
    pbytes))

(defthm n32p-n08p-alistp-write-popl
  (implies (and (n32p count)
                (reg-id RegA)
                (n32p-n08p-alistp program-bytes))
           (n32p-n08p-alistp
            (write-popl count RegA program-bytes))))

(in-theory (disable write-popl))


(defun write-iaddl (count immediate RegB symbol-table-alist program-bytes)
  (declare (xargs :guard (and (n32p count)
                              (or (symbolp immediate)
                                  (n32p immediate))
                              (reg-id RegB)
                              (symbol-n32p-alistp symbol-table-alist)
                              (n32p-n08p-alistp program-bytes))))
  (let* ((pbytes (w08 count
                      (n04-n04-to-n08
                       (cadr (assoc 'iaddl *Instructions*))
                       0)
                      program-bytes))
         (RegB-id (reg-id RegB))
         (reg-specifier (n04-n04-to-n08 15 RegB-id))
         (pbytes (w08 (n32+ count 1) reg-specifier pbytes))
         (label-addr (if (symbolp immediate)
                         (label-address immediate symbol-table-alist)
                       immediate))
         (pbytes (w32 (n32+ count 2) label-addr pbytes)))
    pbytes))

(defthm n32p-n08p-alistp-write-iaddl
  (implies (and (n32p count)
                (or (symbolp immediate)
                    (n32p immediate))
                (reg-id RegB)
                (symbol-n32p-alistp symbol-table-alist)
                (n32p-n08p-alistp program-bytes))
           (n32p-n08p-alistp
            (write-iaddl count immediate RegB symbol-table-alist program-bytes))))

(in-theory (disable write-iaddl))


(defun write-leave (count program-bytes)
  (declare (xargs :guard (and (n32p count)
                              (n32p-n08p-alistp program-bytes))))
  (w08 count
       (n04-n04-to-n08
        (cadr (assoc 'leave *Instructions*))
        0)
       program-bytes))

(defthm n32p-n08p-alistp-write-leave
  (implies (and (n32p count)
                (n32p-n08p-alistp program-bytes))
           (n32p-n08p-alistp
            (write-leave count program-bytes))))

(in-theory (disable write-leave))

(defun write-noop (count program-bytes)
  (declare (xargs :guard (and (n32p count)
                              (n32p-n08p-alistp program-bytes))))
  (w08 count
       (n04-n04-to-n08
        (cadr (assoc 'noop *Instructions*))
        0)
       program-bytes))

(defthm n32p-n08p-alistp-write-noop
  (implies (and (n32p count)
                (n32p-n08p-alistp program-bytes))
           (n32p-n08p-alistp
            (write-noop count program-bytes))))

(in-theory (disable write-noop))


; Y86 assembler.

(defund y86-asm (program count symbol-table-alist program-bytes)
  (declare (xargs :guard (and (y86-prog program)
                              (n32p count)
                              (symbol-n32p-alistp symbol-table-alist)
                              (n32p-n08p-alistp program-bytes))
                  ;; Guard debug can slow things tremendously.
                  ;; :guard-debug nil
                  :guard-hints
                  (("Goal" :do-not '(preprocess)))))
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
            (byte
             (y86-asm rest-program (n32+ count (len args))
                      symbol-table-alist
                      (write-bytes count args
                                   program-bytes)))
            (dword
             (y86-asm rest-program (n32+ count (* 4 (len args)))
                      symbol-table-alist
                      (write-dwords count args
                                    symbol-table-alist program-bytes)))
            (char
             (y86-asm rest-program (n32+ count (len args))
                      symbol-table-alist
                      (write-chars count args program-bytes)))
            (string
             (y86-asm rest-program (n32+ count (length (car args)))
                      symbol-table-alist
                      (write-str count (car args) program-bytes)))
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

            ((cmovle cmovl cmove cmovne cmovge cmovg)
             (y86-asm rest-program (n32+ count 2) symbol-table-alist
                      (write-cmovl count
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
                                    symbol-table-alist
                                    program-bytes)))
            (mrmovl
             (y86-asm rest-program (n32+ count 6) symbol-table-alist
                      (write-mrmovl count
                                    (car args)
                                    (car (cadr args))
                                    (caddr args)
                                    symbol-table-alist
                                    program-bytes)))

            ((addl subl andl xorl)
             (y86-asm rest-program (n32+ count 2) symbol-table-alist
                      (write-op count instruction (car args) (cadr args)
                                program-bytes)))

            ((jmp jle jl je jne jge jg)
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
            (noop
             (y86-asm rest-program (n32+ count 1) symbol-table-alist
                      (write-noop count program-bytes)))
            (otherwise program-bytes)))))))
