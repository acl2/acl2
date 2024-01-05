(in-package "X86ISA")

(include-book "../decoding-and-spec-utils"
	      :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))
(local (include-book "centaur/bitops/ihs-extensions" :dir :system))

;; ======================================================================
;; INSTRUCTION: OUT
;; ======================================================================

(define read-cstr-from-memory1 ((addr :type (signed-byte #.*max-linear-address-size*))
                                x86
                                (acc character-listp))
  :measure (nfix (- *max-linear-address-space* addr))
  :returns (mv (char-list character-listp :hyp (character-listp acc))
               (x86 x86p :hyp (x86p x86)))
  (b* (((mv flg byt x86) (rml08 addr :r x86))
       ((when flg) (mv nil x86))
       ((when (equal byt 0)) (mv acc x86))
       (addr+1 (1+ addr))
       ((unless (canonical-address-p addr+1)) (mv nil x86)))
      (read-cstr-from-memory1 (1+ addr) x86 (cons (code-char byt) acc))))

(defmacro read-cstr-from-memory (addr x86)
  `(b* (((mv bytes x86) (read-cstr-from-memory1 ,addr ,x86 nil)))
       (mv (coerce (reverse bytes) 'string) x86)))

(define modelcall-printk (x86)
  :returns (x86 x86p :hyp (x86p x86))
  :prepwork
  ((local (defthm character-listp-reverse-of-character-listp
                  (implies (character-listp x)
                           (character-listp (reverse x))))))
  (b* ((addr (rgfi *rbx* x86))
       ((unless (canonical-address-p addr)) x86)
       ((mv str x86) (read-cstr-from-memory addr x86))
       (- (cw str)))
      x86))

;; This isn't actually implemented because we don't have
;; any port I/O peripherals modeled. Instead, we use this
;; instruction to perform what are essentially modelcalls (i.e. calls
;; from the software running on the model into the model).
(def-inst x86-out

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
              (write-*ip proc-mode temp-rip x86)))
