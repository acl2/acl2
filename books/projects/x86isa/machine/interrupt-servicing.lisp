(in-package "X86ISA")

(local (include-book "arithmetic-5/top" :dir :system))

(include-book "state")
(include-book "decoding-and-spec-utils")

(defconst *pg-interrupt-vector* 14)

(define push-stack-val ((size :type (member 1 2 4 8))
                        (val (unsigned-byte-p (* 8 size) val))
                        x86)
  :returns (x86 x86p :hyp (x86p x86))
  (b* ((ctx 'push-stack-val)
       (proc-mode (x86-operation-mode x86))
       (check-alignment? (alignment-checking-enabled-p x86))
       (rsp (read-*sp proc-mode x86))
       ((mv flg new-rsp) (add-to-*sp proc-mode rsp (- size) x86))
       ((when flg) (!!fault-fresh :ss 0 :call flg)) ;; #SS(0)
       ((mv flg x86) (wme-size-opt proc-mode size new-rsp #.*ss* val check-alignment? x86))
       ((when flg) (!!ms-fresh :stack-writing-error flg))
       (x86 (write-*sp proc-mode new-rsp x86)))
      x86))

(defmacro push-stack-vals (stack-vals x86)
  (b* (((unless stack-vals) x86)
       ((list size val) (car stack-vals)))
      `(b* ((x86 (push-stack-val ,size ,val ,x86)))
           (push-stack-vals ,(cdr stack-vals) x86))))

(define get-idt-gate-descriptor ((int-vec :type (unsigned-byte 8))
                                 x86)
  :returns (mv (flg booleanp)
               (gate-descriptor interrupt/trap-gate-descriptorBits-p)
               (x86 x86p :hyp (x86p x86)))
  (b* ((idtr (stri *idtr* x86))
       (limit (1+ (gdtr/idtrBits->limit idtr)))
       (table-offset (* 16 int-vec))
       ((unless (< table-offset limit)) (mv t 0 x86))
       ((the (signed-byte 64) table-addr) (i64 (gdtr/idtrBits->base-addr idtr)))
       (gate-addr (+ table-addr table-offset))
       ;; TODO What should we do when the gate address is not canonical?
       ((unless (canonical-address-p gate-addr)) (mv t 0 x86))
       ((mv flg gate-descriptor x86) (rml128 gate-addr :r x86))
       ((when flg) (mv t 0 x86)))
      (mv nil gate-descriptor x86)))

(define setup-interrupt-handler1 ((int-vec :type (unsigned-byte 8))
                                  x86)
  :guard-hints (("Goal" :in-theory (enable !rflagsBits->tf !rflagsBits->rf !rflagsBits->intf)))
  :returns (mv (flg booleanp)
               (x86 x86p :hyp (x86p x86)))
  ;; I initially did this guard proof when I was still early in learning the
  ;; ACL2 prover. I used arithmetic-5. I hindsight, bitops probably would be
  ;; better and make this clearner.
  :prepwork
  ((local (defthm rflags-stuff
                  (and (not (negp (xr :rflags i x86)))
                       (unsigned-byte-p 64 (xr :rflags i x86)))
                  :hints (("Goal" :use (:instance elem-p-of-xr-rflags (x86$a x86))
                           :in-theory (disable elem-p-of-xr-rflags)))))
   (local (defthm unsigned-byte-p-64-of-xr-rflags
                  (unsigned-byte-p 64 (xr :rflags i x86))
                  :hints (("Goal" :use (:instance elem-p-of-xr-rflags (i i) (x86$a x86)) :in-theory (disable elem-p-of-xr-rflags)))))
   (local (defthm integerp-ssr-hidden-base
                  (integerp (xr :ssr-hidden-base i x86))
                  :hints (("Goal" :use (:instance elem-p-of-xr-ssr-hidden-base (i i) (x86$a x86)))))))

  (b* ((proc-mode (x86-operation-mode x86))
       ;; Only 64-bit mode is supported for now
       ((unless (equal proc-mode #.*64-bit-mode*)) (mv t x86))

       (prev-implicit-supervisor-access (implicit-supervisor-access x86))
       (x86 (!implicit-supervisor-access t x86))
       ((mv err idt-gate-descriptor x86) (get-idt-gate-descriptor int-vec x86))
       (x86 (!implicit-supervisor-access prev-implicit-supervisor-access x86))
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
                                    ;; TODO what to do if new-rsp-addr is not canonical?
                                    ((unless (canonical-address-p new-rsp-addr)) (mv t 0 x86))

                                    (prev-implicit-supervisor-access (implicit-supervisor-access x86))
                                    (x86 (!implicit-supervisor-access t x86))
                                    ((mv flg new-rsp x86) (rml64 new-rsp-addr :r x86))
                                    (new-rsp (i64 new-rsp))
                                    (x86 (!implicit-supervisor-access prev-implicit-supervisor-access x86))
                                    ((when flg) (mv t 0 x86))

                                    ;; load the null selector
                                    ((mv flg descriptor x86) (get-segment-descriptor #.*ss* 0 x86))
                                    ((when flg) (mv t 0 x86))
                                    (x86 (load-segment-reg #.*ss* 0 descriptor x86)))
                                   (mv nil new-rsp x86))
                               (mv nil old-rsp x86) ;; No stack switch
                               ))
       ((when flg) (mv t x86))
       (x86 (!rgfi *rsp* new-rsp x86))

       (old-rip (read-*ip proc-mode x86))
       ((mv flg descriptor x86) (get-segment-descriptor #.*cs* selector x86))
       ((when flg) (mv t x86))
       (x86 (load-segment-reg #.*cs* selector descriptor x86))
       (x86 (push-stack-vals ((8 old-ss)
                              (8 (n64 old-rsp))
                              (8 (rflags x86))
                              (8 old-cs)
                              (8 (n64 old-rip))) x86))

       (new-rflags (!rflagsBits->tf 0 (!rflagsBits->rf 0 (rflags x86))))
       ;; If this is an interrupt gate (as opposed to a trap gate), we need to
       ;; additionally clear the interrupt flag
       (new-rflags (if (equal (interrupt/trap-gate-descriptorBits->type idt-gate-descriptor) #b1110)
                     (!rflagsBits->intf 0 (rflags x86))
                     new-rflags))
       (x86 (!rflags new-rflags x86))

       ;; Jump to the appropriate code
       (offset (i64 (logapp 32
                            (logapp 16
                                    (interrupt/trap-gate-descriptorBits->offset15-0 idt-gate-descriptor)
                                    (interrupt/trap-gate-descriptorBits->offset31-16 idt-gate-descriptor))
                            (interrupt/trap-gate-descriptorBits->offset63-32 idt-gate-descriptor))))
       ((unless (canonical-address-p offset)) (mv t x86))
       (x86 (write-*ip proc-mode offset x86)))
      (mv nil x86)))

(defmacro setup-interrupt-handler (int-vec additional-stack x86)
  `(b* (((mv err x86) (setup-interrupt-handler1 ,int-vec ,x86))
        ((when err) (mv err x86))
        (x86 (push-stack-vals ,additional-stack x86)))
       (mv err x86)))

(define page-fault-p (x)
  :enabled t
  (and (true-listp x)
       (equal (len x) 3)
       (equal (car x) :page-fault)
       (unsigned-byte-p 64 (cadr x))
       (signed-byte-p #.*max-linear-address-size* (caddr x))))

;; Attempt to handle a page fault
(define handle-page-fault ((flt page-fault-p)
                           x86)
  :returns (mv (flg booleanp)
               (x86 x86p :hyp (x86p x86)))
  (b* (((list & err-no addr) flt)
       ;; (- (cw "handling page fault; err-no: ~x4; rip: ~x0; rcx: ~x1; rdi: ~x2; rsi: ~x3; addr: ~x5~%" (rip x86) (rgfi *rcx* x86) (rgfi *rsi* x86) (rgfi *rdi* x86) err-no addr))
       ;; Addresses are signed but ctr registers are unsigned
       (x86 (!ctri *cr2* (n64 addr) x86)))
      (setup-interrupt-handler *pg-interrupt-vector* ((8 err-no)) x86)))

(define general-interrupt-p (x)
  :enabled t
  (and (true-listp x)
       (equal (len x) 2)
       (equal (car x) :interrupt)
       (unsigned-byte-p 8 (cadr x))))

(define handle-general-interrupt ((flt general-interrupt-p)
                                 x86)
  :returns (mv (flg booleanp)
               (x86 x86p :hyp (x86p x86)))
  (b* (((list & vec) flt)
       ;; (- (cw "vec: ~x0; handling general interrupt;~%" vec))
       )
      (setup-interrupt-handler vec () x86)))

(define handle-faults (x86)
  :returns (x86 x86p :hyp (x86p x86))
  :guard (fault x86)
  (b* ((flts (fault x86))
       ;; If there are no faults, we're done
       ((unless (consp flts)) x86)
       ;; Pick out the fault to handle
       (flt (car flts))
       ;; Handle the fault
       ((mv err x86) (cond ((page-fault-p flt) (handle-page-fault flt x86))
                           ((general-interrupt-p flt) (handle-general-interrupt flt x86))
                           (t (mv t x86))))
       ;; If we couldn't setup the handler, we're done
       ((when err) x86)
       ;; Remove this fault because we dealt with it
       ;; with it
       (x86 (!fault (cdr flts) x86))
       ;; Clear ms (assuming if it is not nil that is because of the fault)
       (x86 (!ms nil x86)))
      ;; We only handle a single fault per execution
      x86)
  ///
  (defthm x86-unchanged-handle-faults-no-fault
          (implies (not (fault x86))
                   (equal (handle-faults x86)
                          x86))))
