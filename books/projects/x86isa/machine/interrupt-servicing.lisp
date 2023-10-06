(in-package "X86ISA")

(include-book "state")
(include-book "decoding-and-spec-utils")
(include-book "load-segment-reg")

(defconst *pg-interrupt-vector* 14)

(skip-proofs (defun push-stack-val (size val x86)
   (declare (xargs :stobjs (x86)))
   (b* ((ctx 'push-stack-val)
        (proc-mode (x86-operation-mode x86))
        (check-alignment? (alignment-checking-enabled-p x86))
        (rsp (read-*sp proc-mode x86))
        ((mv flg new-rsp) (add-to-*sp proc-mode rsp (- size) x86))
        ((when flg) (!!fault-fresh :ss 0 :call flg)) ;; #SS(0)
        ((mv flg x86) (wime-size-opt proc-mode size new-rsp #.*ss* val check-alignment? x86))
        ((when flg) (!!ms-fresh :stack-writing-error flg))
        (x86 (write-*sp proc-mode new-rsp x86)))
       x86)))

(skip-proofs (defmacro push-stack-vals (stack-vals x86)
               (b* (((unless stack-vals) x86)
                    ((list size val) (car stack-vals)))
                   `(b* ((x86 (push-stack-val ,size ,val ,x86)))
                        (push-stack-vals ,(cdr stack-vals) x86)))))

(skip-proofs (defun get-idt-gate-descriptor (int-vec x86)
               (declare (xargs :stobjs (x86)))
               (b* ((idtr (stri *idtr* x86))
                    (limit (1+ (gdtr/idtrBits->limit idtr)))
                    (table-offset (* 16 int-vec))
                    ((unless (< table-offset limit)) (mv t 0 x86))
                    ((the (signed-byte 64) table-addr) (i64 (gdtr/idtrBits->base-addr idtr)))
                    (gate-addr (+ table-addr table-offset))
                    ((mv flg gate-descriptor x86) (rml128 gate-addr :r x86))
                    ((when flg) (mv t 0 x86)))
                   (mv nil gate-descriptor x86))))

(skip-proofs (defun setup-interrupt-handler1 (int-vec x86)
               (declare (xargs :stobjs (x86)))
               (b* ((proc-mode (x86-operation-mode x86))
                    ;; Only 64-bit mode is supported for now
                    ((unless (equal proc-mode #.*64-bit-mode*)) (mv t x86))

                    ;; This hack sets the cpl to 0 while we try to find the gate descriptor. This is needed because when this is triggered by user space, we may not be able to find the gate descriptor
                    (cs (seg-visiblei *cs* x86))
                    (x86 (!seg-visiblei *cs* (!segment-selectorBits->rpl 0 cs) x86))
                    ((mv err idt-gate-descriptor x86) (get-idt-gate-descriptor int-vec x86))
                    (x86 (!seg-visiblei *cs* cs x86))
                    ((when err) (mv t x86))

                    ;; Found entry, but it isn't marked present
                    ((unless (and (equal (interrupt/trap-gate-descriptorBits->p idt-gate-descriptor) 1)
                                  ;; Found the entry, but it uses the interrupt stack table in the task state segment
                                  (equal (interrupt/trap-gate-descriptorBits->ist idt-gate-descriptor) 0))) (mv t x86))

                    ;; TODO check DPL for handling INT instruction

                    ;; Push relevant values onto the stack
                    (selector (interrupt/trap-gate-descriptorBits->selector idt-gate-descriptor))
                    (old-rsp (read-*sp proc-mode x86))
                    (new-privilege (segment-selectorBits->rpl selector))
                    ;; Moving to more privilege
                    (old-ss (seg-visiblei *ss* x86))
                    (old-cs (seg-visiblei *cs* x86))
                    ((mv flg new-rsp x86) (if (< new-privilege (cpl x86))
                               (b* ((tss-addr (ssr-hidden-basei *tr* x86))
                                    ;; TODO check limit
                                    (new-rsp-addr (i64 (+ tss-addr
                                                          4
                                                          (* 8 new-privilege))))
                                    ;; Use the same hack as above to perform a privileged memory read regardless of the cpl
                                    (cs (seg-visiblei *cs* x86))
                                    (x86 (!seg-visiblei *cs* (!segment-selectorBits->rpl 0 cs) x86))
                                    ((mv flg new-rsp x86) (rml64 new-rsp-addr :r x86))
                                    (new-rsp (i64 new-rsp))
                                    (x86 (!seg-visiblei *cs* cs x86))
                                    ((when flg) (mv t 0 x86))
                                    (x86 (load-segment-reg *ss* 0 x86))) ;; load the null selector
                                   (mv nil new-rsp x86))
                               (mv nil old-rsp x86) ;; No stack switch
                               ))
                    ((when flg) (mv t x86))
                    (x86 (!rgfi *rsp* new-rsp x86))

                    (old-rip (read-*ip proc-mode x86))
                    (x86 (load-segment-reg *cs* selector x86))
                    (x86 (push-stack-vals ((8 old-ss)
                                           (8 old-rsp)
                                           (8 (rflags x86))
                                           (8 old-cs)
                                           (8 old-rip)) x86))

                    ;; Jump to the appropriate code
                    (offset (i64 (logapp 32
                                         (logapp 16
                                                 (interrupt/trap-gate-descriptorBits->offset15-0 idt-gate-descriptor)
                                                 (interrupt/trap-gate-descriptorBits->offset31-16 idt-gate-descriptor))
                                         (interrupt/trap-gate-descriptorBits->offset63-32 idt-gate-descriptor))))
                    (x86 (write-*ip proc-mode offset x86)))
                   (mv nil x86))))

(skip-proofs (defmacro setup-interrupt-handler (int-vec additional-stack x86)
               `(b* (((mv err x86) (setup-interrupt-handler1 ,int-vec ,x86))
                     ((when err) (mv err x86))
                     (x86 (push-stack-vals ,additional-stack x86)))
                    (mv err x86))))

;; Attempt to handle a page fault
(skip-proofs (defun handle-page-fault (flt x86)
               (declare (xargs :stobjs (x86)))
               (b* (((list & err-no addr) flt)
                    ;; (- (cw "handling page fault; err-no: ~x4; rip: ~x0; rcx: ~x1; rdi: ~x2; rsi: ~x3; addr: ~x5~%" (rip x86) (rgfi *rcx* x86) (rgfi *rsi* x86) (rgfi *rdi* x86) err-no addr))
                    ;; Addresses are signed but ctr registers are unsigned
                    (x86 (!ctri *cr2* (n64 addr) x86)))
                   (setup-interrupt-handler *pg-interrupt-vector* ((8 err-no)) x86))))

(skip-proofs (defun handle-general-interrupt (flt x86)
               (declare (xargs :stobjs (x86)))
               (b* (((list & vec) flt)
                    ;; (- (cw "vec: ~x0; handling general interrupt;~%" vec))
                    )
                   (setup-interrupt-handler vec () x86))))

(skip-proofs (defun handle-faults (x86)
               (declare (xargs :stobjs (x86)))
               (b* ((flts (fault x86))
                    ;; If there are no faults, we're done
                    ((unless flts) x86)
                    ;; Pick out the fault to handle
                    (flt (car flts))
                    (flt-type (car flt))
                    ;; Handle the fault
                    ((mv err x86) (case flt-type
                                    (:page-fault (handle-page-fault flt x86))
                                    (:interrupt (handle-general-interrupt flt x86))
                                    (otherwise (mv t x86))))
                    ;; If we couldn't setup the handler, we're done
                    ((when err) x86)
                    ;; Remove this fault because we dealt with it
                    ;; with it
                    (x86 (!fault (cdr flts) x86))
                    ;; Clear ms (assuming if it is not nil that is because of the fault)
                    (x86 (!ms nil x86)))
                   ;; We only handle a single fault per execution
                   x86)))

(skip-proofs (defun service-interrupts (x86)
               (declare (xargs :stobjs (x86)))
               (handle-faults x86)))
