(in-package "X86ISA")

(include-book "../decoding-and-spec-utils"
	      :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))

;; ======================================================================
;; INSTRUCTION: OUT
;; ======================================================================

(skip-proofs (defun read-cstr-from-memory1 (addr x86 acc)
  (declare (xargs :stobjs (x86)))
  (b* (((mv flg byt x86) (rml08 addr :r x86))
       ((when flg) (mv nil x86))
       ((when (equal byt 0)) (mv acc x86)))
      (read-cstr-from-memory1 (1+ addr) x86 (cons (code-char byt) acc)))))

(defmacro read-cstr-from-memory (addr x86)
  `(b* (((mv bytes x86) (read-cstr-from-memory1 ,addr ,x86 nil)))
       (mv (coerce (reverse bytes) 'string) x86)))

(skip-proofs (defun modelcall-printk (x86)
  (declare (xargs :stobjs (x86)))
  (b* (((mv str x86) (read-cstr-from-memory (rgfi *rbx* x86) x86))
       (- (cw str)))
      x86)))

;; This isn't actually implemented because we don't have
;; any port I/O peripherals modeled. Instead, we use this
;; instruction to perform what are essentially modelcalls (i.e. calls
;; from the software running on the model into the model).
(skip-proofs (def-inst x86-out

  ;; Op/En: I
  ;; E6 ib

  :parents (one-byte-opcodes)

  :guard-hints (("Goal" :in-theory (e/d (riml08 riml32) ())))

  :returns (x86 x86p :hyp (x86p x86))

  :body


  (b* (((mv flg port-number x86) (rme-size-opt proc-mode 1 temp-rip #.*cs* :x nil x86))
       ((when flg) (!!ms-fresh :rme-size-error flg))
       ((mv flg (the (signed-byte #.*max-linear-address-size*) temp-rip))
        (add-to-*ip proc-mode temp-rip 1 x86))
       ((when flg) (!!ms-fresh :increment-error flg))
       (x86 (case port-number
                  (1 (modelcall-printk x86))
                  (otherwise (!!ms-fresh :unhandled-port port-number)))))
      (write-*ip proc-mode temp-rip x86))))
