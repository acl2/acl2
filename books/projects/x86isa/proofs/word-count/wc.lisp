;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

;;  There are a lot of similar-looking theorems here that I plan to
;; generate and prove automatically in the future.

(in-package "X86ISA")

(include-book "programmer-level-mode/programmer-level-memory-utils" :dir :proof-utils :ttags :all)
(include-book "programmer-level-mode/environment-utils" :dir :proof-utils :ttags :all)
(include-book "centaur/gl/gl" :dir :system)
;; Including the WC program binary and other misc. stuff:
(include-book "wc-addr-byte")

(set-irrelevant-formals-ok t)

(include-book "centaur/bitops/ihs-extensions" :dir :system)
(local (include-book "centaur/bitops/signed-byte-p" :dir :system))
(local (in-theory (e/d () (wb-remove-duplicate-writes
                           byte-ify-and-combine-bytes))))

;; ======================================================================

;; Accessor functions for nc, nl, and nw:

;; Inside the loop:

(defun-nx word-state (x86 next-x86)
  (mv-nth 1 (rb (create-canonical-address-list 4 (+ -8 (xr :rgf *rbp* x86)))
                :r next-x86)))

(defun-nx nc (x86 next-x86)
  (mv-nth 1 (rb (create-canonical-address-list 4 (+ -12 (xr :rgf *rbp* x86)))
                :r next-x86)))

(defun-nx nw (x86 next-x86)
  (mv-nth 1 (rb (create-canonical-address-list 4 (+ -16 (xr :rgf *rbp* x86)))
                :r next-x86)))

(defun-nx nl (x86 next-x86)
  (mv-nth 1 (rb (create-canonical-address-list 4 (+ -20 (xr :rgf *rbp* x86)))
                :r next-x86)))

;; In the Main sub-routine (after return from GC):

(defun-nx program-nc (x86 next-x86)
  (mv-nth 1 (rb (create-canonical-address-list 4 (+ -20 (xr :rgf *rsp* x86)))
                :r next-x86)))

(defun-nx program-nw (x86 next-x86)
  (mv-nth 1 (rb (create-canonical-address-list 4 (+ -24 (xr :rgf *rsp* x86)))
                :r next-x86)))

(defun-nx program-nl (x86 next-x86)
  (mv-nth 1 (rb (create-canonical-address-list 4 (+ -28 (xr :rgf *rsp* x86)))
                :r next-x86)))

;;======================================================================

;; Assumptions about the environment:

(defund eof-terminatedp (bl)
  (declare (xargs :guard (and (byte-listp bl)
                              (consp bl))))
  (equal (last bl) (list *eof*)))

(defun-nx env-assumptions (x86)
  (let* ((obj-fd-field (read-x86-file-des 0 x86))
         (obj-mode (cdr (assoc :mode obj-fd-field)))
         (obj-offset (cdr (assoc :offset obj-fd-field)))
         (obj-name (cdr (assoc :name obj-fd-field)))
         (obj-contents-field (read-x86-file-contents obj-name x86))
         (obj-contents (cdr (assoc :contents obj-contents-field)))
         (bytes-of-obj (string-to-bytes obj-contents)))
    (and
     ;; ------------------------------
     ;; Assumptions about the environment.
     ;; ------------------------------
     ;; Standard input:
     ;; Descriptors:
     (file-descriptor-fieldp obj-fd-field)
     (equal (logand #b11 obj-mode) *O_RDONLY*)
     ;; Contents:
     (file-contents-fieldp obj-contents-field)
     (< 0 (len bytes-of-obj))
     ;; The following should take care of preventing the error when
     ;; (< (len bytes-of-obj) obj-offset) in syscall-read-logic.
     (< obj-offset (len bytes-of-obj))
     (eof-terminatedp bytes-of-obj))))

;; ======================================================================

;; Clock functions and pre-conditions:

(defun gc-clk-main-before-call ()
  10)

(defun gc-clk ()
  18)

(defun gc-clk-eof ()
  ;; Call instruction + GC procedure
  (clk+ 4 (gc-clk)))

(defun gc-clk-no-eof ()
  ;; Call instruction + GC procedure
  (clk+ 3 (gc-clk)))

(defun gc-clk-newline ()
  (clk+ 10 (gc-clk-no-eof)))

(defun gc-clk-space ()
  (clk+ 7 (gc-clk-no-eof)))

(defun gc-clk-tab ()
  (clk+ 11 (gc-clk-no-eof)))

(defun gc-clk-otherwise-out ()
  (clk+ 13 (gc-clk-no-eof)))

(defun gc-clk-otherwise-in ()
  (clk+ 11 (gc-clk-no-eof)))

(encapsulate
 ()

 (local (include-book "std/lists/take" :dir :system))

 (local (in-theory (disable take)))

 (defun get-char (offset str-bytes)
   (declare (xargs :guard (and (byte-listp str-bytes)
                               (natp offset))))
   (car (grab-bytes
         (take 1 (nthcdr offset str-bytes)))))

 (local (in-theory (enable eof-terminatedp)))

 (local (include-book "std/lists/nthcdr" :dir :system))

 (defun loop-clk (word-state offset str-bytes)
   ;; Begins at #x400545 (call GC)

   (declare (xargs :measure
                   (len (nthcdr offset str-bytes))))

   (if (and (eof-terminatedp str-bytes)
            (< offset (len str-bytes))
            (natp offset))

       (let ((char (get-char offset str-bytes)))

         (if (equal char #.*eof*)

             (gc-clk-eof)

           (b* (((mv word-state loop-steps)
                 (case char ;; #x40050b to #x400545
                   (#.*newline*
                    ;; (40050b, 0f, 13, 15, 19, 1d, 1f, 23, 2b, 32, 45)
                    (mv 0 ;; #x40052b
                        (gc-clk-newline)))
                   (#.*space*
                    ;; (40050b, 0f, 13, 19, 1d, 2b, 32, 45)
                    (mv 0 ;; #x40052b
                        (gc-clk-space)))
                   (#.*tab*
                    ;; (40050b, 0f, 13, 19, 1d, 1f, 23, 25, 29, 2b, 32, 45)
                    (mv 0 ;; #x40052b
                        (gc-clk-tab)))
                   (t
                    ;; (40050b, 0f, 13, 19, 1d, 1f, 23, 25, 29, 34, 38,
                    ;; (if word-state != 0, (45) else (3a, 41, 45)))
                    (if (equal word-state #.*out*)
                        (mv 1 (gc-clk-otherwise-out)) ;; #x40053a
                      (mv word-state (gc-clk-otherwise-in)))))))

               (clk+ loop-steps
                     (loop-clk word-state (1+ offset) str-bytes)))))

     0))

 ) ;; End of encapsulate

(defun clock (str-bytes x86)
  (declare (xargs :stobjs (x86)
                  :verify-guards nil))

  (if (eof-terminatedp str-bytes)

      (clk+ (gc-clk-main-before-call)
            (loop-clk
             ;; Initial state = 0
             0
             ;; Initial offset
             (cdr (assoc-equal :offset (read-x86-file-des 0 x86)))
             str-bytes))
    0))

(defthm natp-loop-clk
  (natp (loop-clk word-state offset str-bytes))
  :rule-classes (:type-prescription :rewrite))

(defthm natp-clock
  (natp (clock str-bytes x86))
  :rule-classes (:type-prescription :rewrite))

(in-theory (e/d* () (gc-clk-main-before-call
                    (gc-clk-main-before-call)
                    gc-clk
                    (gc-clk)
                    gc-clk-eof
                    (gc-clk-eof)
                    gc-clk-no-eof
                    (gc-clk-no-eof)
                    gc-clk-newline
                    (gc-clk-newline)
                    gc-clk-space
                    (gc-clk-space)
                    gc-clk-tab
                    (gc-clk-tab)
                    gc-clk-otherwise-out
                    (gc-clk-otherwise-out)
                    gc-clk-otherwise-in
                    (gc-clk-otherwise-in)
                    loop-clk
                    clock)))

(defun-nx input (x86)
  (string-to-bytes
   (cdr (assoc-equal
         :contents
         (read-x86-file-contents
          (cdr
           (assoc-equal :name (read-x86-file-des 0 x86)))
          x86)))))

(defun-nx offset (x86)
  (cdr (assoc-equal :offset (read-x86-file-des 0 x86))))

(defun-nx preconditions (addr x86)

  ;; Note: addr is the address of the first instruction in the GC
  ;; subroutine, which is also the first instruction of this program.

  (and (x86p x86)
       (xr :programmer-level-mode 0 x86)
       ;; I don't care about alignment checks for this proof.
       (not (alignment-checking-enabled-p x86))
       (equal (xr :os-info 0 x86) :linux)
       (env-assumptions x86)
       (canonical-address-p (xr :rgf *rsp* x86))
       ;; (equal (xr :rip 0 x86) (+ (len *gc*) addr))
       (equal addr (- (xr :rip 0 x86) (len *gc*)))
       (canonical-address-p addr)
       (canonical-address-p (+ (1- (len *wc*)) addr))
       ;; The following accounts for the rsp constraints of GC as
       ;; well.
       (canonical-address-p (+ 8 (xr :rgf *rsp* x86)))
       (canonical-address-p (+ (- (+ 48 8 #x20 8)) (xr :rgf *rsp* x86)))
       ;; 104 =  (+ 48 8 #x20 8) + 8
       (disjoint-p
        ;; IMPORTANT:
        ;; Convention: Keep the program addresses as the first
        ;; argument.
        (create-canonical-address-list
         (len *wc*) addr)
        (create-canonical-address-list
         104 (+ (- (+ 48 8 #x20 8)) (xr :rgf *rsp* x86))))
       (equal (xr :ms 0 x86) nil)
       (equal (xr :fault 0 x86) nil)
       ;; Enabling the SYSCALL instruction.
       (equal (ia32_efer-slice :ia32_efer-sce (xr :msr *ia32_efer-idx* x86)) 1)
       (equal (ia32_efer-slice :ia32_efer-lma (xr :msr *ia32_efer-idx* x86)) 1)
       (program-at (create-canonical-address-list
                    (len *wc*) addr) *wc* x86)))

(defthm preconditions-forward-chain-addresses-info
  (implies (preconditions addr x86)
           (and (canonical-address-p (xr :rgf *rsp* x86))
                ;; (equal (xr :rip 0 x86) (+ (len *gc*) addr))
                (equal addr (- (xr :rip 0 x86) (len *gc*)))
                (canonical-address-p addr)
                (canonical-address-p (+ (1- (len *wc*)) addr))
                ;; The following accounts for the rsp constraints of GC as
                ;; well.
                (canonical-address-p (+ 8 (xr :rgf *rsp* x86)))
                (canonical-address-p (+ (- (+ 48 8 #x20 8)) (xr :rgf *rsp* x86)))
                ;; 104 =  (+ 48 8 #x20 8) + 8
                (disjoint-p
                 ;; IMPORTANT:
                 ;; Convention: Keep the program addresses as the first
                 ;; argument.
                 (create-canonical-address-list
                  (len *wc*) addr)
                 (create-canonical-address-list
                  104 (+ (- (+ 48 8 #x20 8)) (xr :rgf *rsp* x86))))
                (program-at (create-canonical-address-list
                             (len *wc*) addr) *wc* x86)))
  :rule-classes :forward-chaining)

(defthm preconditions-fwd-chaining-essentials
  (implies (preconditions addr x86)
           (and (x86p x86)
                (xr :programmer-level-mode 0 x86)
                (not (alignment-checking-enabled-p x86))
                (equal (xr :os-info 0 x86) :linux)
                (env-assumptions x86)
                (equal (xr :ms 0 x86) nil)
                (equal (xr :fault 0 x86) nil)
                ;; Enabling the SYSCALL instruction.
                (equal (ia32_efer-slice :ia32_efer-sce (xr :msr *ia32_efer-idx* x86)) 1)
                (equal (ia32_efer-slice :ia32_efer-lma (xr :msr *ia32_efer-idx* x86)) 1)))
  :rule-classes :forward-chaining)

(defun-nx loop-preconditions (addr x86)
  ;; Note: addr is the address of the first instruction in the GC
  ;; subroutine.
  (and (x86p x86)
       (xr :programmer-level-mode 0 x86)
       (not (alignment-checking-enabled-p x86))
       (equal (xr :os-info 0 x86) :linux)
       (env-assumptions x86)
       (canonical-address-p (xr :rgf *rsp* x86))
       ;; Address of the call instruction in the main sub-routine
       ;; 95: Position of the call instruction in the main sub-routine
       ;; (equal (xr :rip 0 x86) (+ (1- (+ (len *gc*) 95)) addr))
       (equal addr (- (xr :rip 0 x86) (1- (+ (len *gc*) 95))))
       (canonical-address-p addr)
       (canonical-address-p (+ (1- (len *wc*)) addr))
       (canonical-address-p (+ #x20 (xr :rgf *rsp* x86)))
       (canonical-address-p (+ (- (+ 8 #x20 8)) (xr :rgf *rsp* x86)))
       ;; (+ 8 #x20 8 #x20) = 80
       (disjoint-p
        ;; IMPORTANT: Keep the program addresses as the first
        ;; argument.
        (create-canonical-address-list
         (len *wc*) addr)
        (create-canonical-address-list
         80 (+ (- (+ 8 #x20 8)) (xr :rgf *rsp* x86))))
       ;; IMPORTANT: Why doesn't the following hyp work?
       ;; (equal (xr :rgf *rbp* x86) (- (+ (xr :rgf *rsp* x86) 40) 8))
       ;; See loop-preconditions-weird-rbp-rsp.
       (canonical-address-p (xr :rgf *rbp* x86))
       (equal (xr :rgf *rsp* x86)
              (- (xr :rgf *rbp* x86) 32))
       (equal (xr :ms 0 x86) nil)
       (equal (xr :fault 0 x86) nil)
       ;; Enabling the SYSCALL instruction.
       (equal (ia32_efer-slice :ia32_efer-sce (xr :msr *ia32_efer-idx* x86)) 1)
       (equal (ia32_efer-slice :ia32_efer-lma (xr :msr *ia32_efer-idx* x86)) 1)
       (program-at (create-canonical-address-list (len *wc*) addr) *wc* x86)))

(defthm loop-preconditions-weird-rbp-rsp
  (implies (equal (xr :rgf *rbp* x86)
                  (+ (xr :rgf *rsp* x86) 32))
           (equal (xr :rgf *rbp* x86)
                  (+ (xr :rgf *rsp* x86) 32)))
  :rule-classes ((:rewrite :backchain-limit-lst (1))))

(defthmd weirder-rule
  (implies (loop-preconditions addr x86)
           (equal (xr :rgf *rbp* x86)
                  (+ (xr :rgf *rsp* x86) 32))))

(defthm loop-preconditions-forward-chain-addresses-info
  (implies (loop-preconditions addr x86)
           (and (canonical-address-p (xr :rgf *rsp* x86))
                ;; Address of the call instruction in the main sub-routine
                ;; 95: Position of the call instruction in the main sub-routine
                ;; (equal (xr :rip 0 x86) (+ (1- (+ (len *gc*) 95)) addr))
                (equal addr (- (xr :rip 0 x86) (1- (+ (len *gc*) 95))))
                (canonical-address-p addr)
                (canonical-address-p (+ (1- (len *wc*)) addr))
                (canonical-address-p (+ #x20 (xr :rgf *rsp* x86)))
                (canonical-address-p (+ (- (+ 8 #x20 8)) (xr :rgf *rsp* x86)))
                ;; (+ 8 #x20 8 #x20) = 80
                (disjoint-p
                 ;; IMPORTANT: Keep the program addresses as the first
                 ;; argument.
                 (create-canonical-address-list
                  (len *wc*) addr)
                 (create-canonical-address-list
                  80 (+ (- (+ 8 #x20 8)) (xr :rgf *rsp* x86))))
                ;; IMPORTANT: Why doesn't the following hyp work?
                ;; (equal (xr :rgf *rbp* x86) (- (+ (xr :rgf *rsp* x86) 40) 8))
                (canonical-address-p (xr :rgf *rbp* x86))
                (equal (xr :rgf *rsp* x86)
                       (- (xr :rgf *rbp* x86) 32))
                (program-at (create-canonical-address-list
                             (len *wc*) addr) *wc* x86)))
  :rule-classes ((:forward-chaining :trigger-terms ((loop-preconditions addr x86)))))

(defthm loop-preconditions-fwd-chaining-essentials
  (implies (loop-preconditions addr x86)
           (and (x86p x86)
                (xr :programmer-level-mode 0 x86)
                (not (alignment-checking-enabled-p x86))
                (equal (xr :os-info 0 x86) :linux)
                (env-assumptions x86)
                (equal (xr :rgf *rsp* x86)
                       (- (xr :rgf *rbp* x86) 32))
                (equal (xr :ms 0 x86) nil)
                (equal (xr :fault 0 x86) nil)
                ;; Enabling the SYSCALL instruction.
                (equal (ia32_efer-slice :ia32_efer-sce (xr :msr *ia32_efer-idx* x86)) 1)
                (equal (ia32_efer-slice :ia32_efer-lma (xr :msr *ia32_efer-idx* x86)) 1)))
  :rule-classes ((:forward-chaining :trigger-terms ((loop-preconditions addr x86)))))

(in-theory (e/d* () (preconditions loop-preconditions)))

;; ======================================================================

;; Code effects theorems:

(local (include-book "arithmetic/top" :dir :system))

;;======================================================================
;; Main: before the call to the GC procedure:
;;======================================================================

;;**********************************************************************
;; Main
;;**********************************************************************

(in-theory (e/d* (subset-p) (env-assumptions i64p)))

(defthm effects-to-gc-no-call

  ;; push %rbp
  ;; mov %rsp,%rbp
  ;; sub $0x20,%rsp
  ;; movl $0x0,-0x8(%rbp)
  ;; movl $0x0,-0xc(%rbp)
  ;; mov -0xc(%rbp),%eax
  ;; mov %eax,-0x10(%rbp)
  ;; mov -0x10(%rbp),%eax
  ;; mov %eax,-0x14(%rbp)
  ;; jmp 400545 <main+0x5e>

  (implies (and (bind-free '((addr . addr)) (addr))
                (preconditions addr x86))
           (equal (x86-run (gc-clk-main-before-call) x86)
                  (XW
                   :RGF *RAX* 0
                   (XW
                    :RGF *RSP* (+ -40 (XR :RGF *RSP* X86))
                    (XW
                     :RGF *RBP* (+ -8 (XR :RGF *RSP* X86))
                     (XW
                      :RIP 0 (+ 94 (XR :RIP 0 X86))
                      (MV-NTH
                       1
                       (WB
                        (APPEND
                         (CREATE-ADDR-BYTES-ALIST
                          (CREATE-CANONICAL-ADDRESS-LIST 8 (+ -8 (XR :RGF *RSP* X86)))
                          (BYTE-IFY 8 (LOGHEAD 64 (XR :RGF *RBP* X86))))
                         (CREATE-ADDR-BYTES-ALIST
                          (CREATE-CANONICAL-ADDRESS-LIST 4 (+ -16 (XR :RGF *RSP* X86)))
                          '(0 0 0 0))
                         (CREATE-ADDR-BYTES-ALIST
                          (CREATE-CANONICAL-ADDRESS-LIST 4 (+ -20 (XR :RGF *RSP* X86)))
                          '(0 0 0 0))
                         (CREATE-ADDR-BYTES-ALIST
                          (CREATE-CANONICAL-ADDRESS-LIST 4 (+ -24 (XR :RGF *RSP* X86)))
                          '(0 0 0 0))
                         (CREATE-ADDR-BYTES-ALIST
                          (CREATE-CANONICAL-ADDRESS-LIST 4 (+ -28 (XR :RGF *RSP* X86)))
                          '(0 0 0 0)))
                        (!FLGI
                         *CF*
                         (LOGHEAD 1
                                  (BOOL->BIT (< (LOGHEAD 64 (+ -8 (XR :RGF *RSP* X86)))
                                                32)))
                         (!FLGI
                          *PF*
                          (LOGIOR
                           (PF-SPEC64 (LOGHEAD 64 (+ -40 (XR :RGF *RSP* X86))))
                           (LOGHEAD
                            -1
                            (LOGTAIL 2
                                     (BOOL->BIT (< (LOGHEAD 64 (+ -8 (XR :RGF *RSP* X86)))
                                                   32)))))
                          (!FLGI
                           *AF*
                           (LOGIOR
                            (SUB-AF-SPEC64 (LOGHEAD 64 (+ -8 (XR :RGF *RSP* X86)))
                                           32)
                            (LOGHEAD
                             -3
                             (LOGTAIL 4
                                      (BOOL->BIT (< (LOGHEAD 64 (+ -8 (XR :RGF *RSP* X86)))
                                                    32)))))
                           (!FLGI
                            *ZF*
                            (LOGIOR
                             (ZF-SPEC (LOGHEAD 64 (+ -40 (XR :RGF *RSP* X86))))
                             (LOGHEAD
                              -5
                              (LOGTAIL 6
                                       (BOOL->BIT (< (LOGHEAD 64 (+ -8 (XR :RGF *RSP* X86)))
                                                     32)))))
                            (!FLGI
                             *SF*
                             (LOGIOR
                              (SF-SPEC64 (LOGHEAD 64 (+ -40 (XR :RGF *RSP* X86))))
                              (LOGHEAD
                               -6
                               (LOGTAIL 7
                                        (BOOL->BIT (< (LOGHEAD 64 (+ -8 (XR :RGF *RSP* X86)))
                                                      32)))))
                             (!FLGI
                              *OF*
                              (LOGIOR
                               (OF-SPEC64 (+ -40 (XR :RGF *RSP* X86)))
                               (LOGHEAD
                                -10
                                (LOGTAIL
                                 11
                                 (BOOL->BIT (< (LOGHEAD 64 (+ -8 (XR :RGF *RSP* X86)))
                                               32)))))
                              X86))))))))))))))
  :hints (("Goal"
           :in-theory (e/d* (preconditions
                             gc-clk-main-before-call

                             instruction-decoding-and-spec-rules

                             gpr-add-spec-4
                             gpr-add-spec-8
                             gpr-sub-spec-8
                             jcc/cmovcc/setcc-spec
                             imul-spec
                             imul-spec-32
                             gpr-sub-spec-4

                             top-level-opcode-execute
                             !rgfi-size
                             x86-operand-to-reg/mem
                             wr64
                             wr32
                             rr32
                             rr64
                             rm32
                             rm64
                             wm32
                             wm64
                             rr32
                             x86-operand-from-modr/m-and-sib-bytes
                             rim-size
                             rim32
                             n32-to-i32
                             n64-to-i64
                             rim08
                             two-byte-opcode-decode-and-execute
                             x86-effective-addr
                             subset-p
                             ;; Flags
                             write-user-rflags)

                            (wb-remove-duplicate-writes
                             force (force))))))

;; ----------------------------------------------------------------------
;; Main: before the call to the GC procedure: Projection Theorems:
;; ----------------------------------------------------------------------

(defthmd effects-to-gc-rsp-projection
  (implies (and (bind-free '((addr . addr)) (addr))
                (preconditions addr x86))
           (equal (xr :rgf *rsp* (x86-run (gc-clk-main-before-call) x86))
                  (+ -40 (xr :rgf *rsp* x86)))))

(defthmd effects-to-gc-rbp-projection
  (implies (and (bind-free '((addr . addr)) (addr))
                (preconditions addr x86))
           (equal (xr :rgf *rbp* (x86-run (gc-clk-main-before-call) x86))
                  (+ -8 (xr :rgf *rsp* x86)))))

(defthmd x86p-effects-to-gc
  (implies (and (bind-free '((addr . addr)) (addr))
                (preconditions addr x86))
           (x86p (x86-run (gc-clk-main-before-call) x86))))

(defthmd effects-to-gc-msri-projection
  (implies (and (bind-free '((addr . addr)) (addr))
                (preconditions addr x86))
           (and
            (equal (ia32_efer-slice
                    :ia32_efer-sce
                    (xr :msr *ia32_efer-idx*
                          (x86-run (gc-clk-main-before-call) x86)))
                   1)
            (equal (ia32_efer-slice
                    :ia32_efer-lma
                    (xr :msr *ia32_efer-idx*
                          (x86-run (gc-clk-main-before-call) x86)))
                   1)))
  :hints (("Goal" :in-theory (e/d ()
                                  (preconditions-fwd-chaining-essentials))
           :use ((:instance preconditions-fwd-chaining-essentials)))))

(defthmd effects-to-gc-ms-projection
  (implies (and (bind-free '((addr . addr)) (addr))
                (preconditions addr x86))
           (equal (xr :ms 0 (x86-run (gc-clk-main-before-call) x86)) nil)))

(defthmd effects-to-gc-fault-projection
  (implies (and (bind-free '((addr . addr)) (addr))
                (preconditions addr x86))
           (equal (xr :fault 0 (x86-run (gc-clk-main-before-call) x86)) nil)))

(defthmd effects-to-gc-rip-projection
  (implies (and (bind-free '((addr . addr)) (addr))
                (preconditions addr x86))
           (equal (xr :rip 0 (x86-run (gc-clk-main-before-call) x86))
                  (+ 94 (xr :rip 0 x86)))))

(defthmd effects-to-gc-program-projection
  (implies (and (preconditions addr x86)
                (equal len-wc (len *wc*)))
           (program-at (create-canonical-address-list len-wc addr)
                       *wc* (x86-run (gc-clk-main-before-call) x86))))

(defthmd effects-to-gc-env-assumptions-projection
  (implies (preconditions addr x86)
           (env-assumptions (x86-run (gc-clk-main-before-call) x86)))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (e/d* (env-assumptions) ())
           :use ((:instance preconditions-fwd-chaining-essentials)))))

(defthmd effects-to-gc-programmer-level-mode-projection
  (implies (and (bind-free '((addr . addr)) (addr))
                (preconditions addr x86))
           (equal (xr :programmer-level-mode 0 (x86-run (gc-clk-main-before-call) x86))
                  (xr :programmer-level-mode 0 x86))))

(defthmd effects-to-gc-alignment-checking-enabled-p-projection
  (implies (and (bind-free '((addr . addr)) (addr))
                (preconditions addr x86))
           (equal (alignment-checking-enabled-p (x86-run (gc-clk-main-before-call) x86))
                  (alignment-checking-enabled-p x86))))

(defthmd effects-to-gc-os-info-projection
  (implies (and (bind-free '((addr . addr)) (addr))
                (preconditions addr x86))
           (equal (xr :os-info 0 (x86-run (gc-clk-main-before-call) x86))
                  (xr :os-info 0 x86))))

(defthmd effects-to-gc-input-projection
  (implies (and (bind-free '((addr . addr)) (addr))
                (preconditions addr x86))
           (equal (input (x86-run (gc-clk-main-before-call) x86))
                  (input x86))))

(defthmd effects-to-gc-offset-projection
  (implies (and (bind-free '((addr . addr)) (addr))
                (preconditions addr x86))
           (equal (offset (x86-run (gc-clk-main-before-call) x86))
                  (offset x86))))

(defthm loop-preconditions-effects-to-gc
  (implies (preconditions addr x86)
           (loop-preconditions addr (x86-run (gc-clk-main-before-call) x86)))
  :hints (("Goal" :in-theory (e/d* (effects-to-gc-rbp-projection
                                    effects-to-gc-rsp-projection
                                    x86p-effects-to-gc
                                    effects-to-gc-msri-projection
                                    effects-to-gc-rip-projection
                                    effects-to-gc-ms-projection
                                    effects-to-gc-fault-projection
                                    effects-to-gc-env-assumptions-projection
                                    (len)
                                    effects-to-gc-programmer-level-mode-projection
                                    effects-to-gc-alignment-checking-enabled-p-projection
                                    effects-to-gc-os-info-projection
                                    loop-preconditions-fwd-chaining-essentials
                                    loop-preconditions-forward-chain-addresses-info
                                    preconditions-fwd-chaining-essentials
                                    preconditions-forward-chain-addresses-info
                                    effects-to-gc-programmer-level-mode-projection
                                    effects-to-gc-program-projection
                                    subset-p-two-create-canonical-address-lists-general
                                    )
                                   (effects-to-gc-no-call))
           :expand (loop-preconditions addr (x86-run (gc-clk-main-before-call) x86)))))

;; ----------------------------------------------------------------------
;; Main: before the call to the GC procedure: Delta-Variable Theorems:
;; ----------------------------------------------------------------------

(defthm effects-to-gc-variables-state
  (implies (and (bind-free '((addr . addr)) (addr))
                (preconditions addr x86))
           (equal (mv-nth 1 (rb
                             (create-canonical-address-list 4 (+ -16 (xr :rgf *rsp* x86)))
                             :r
                             (x86-run (gc-clk-main-before-call) x86)))
                  (byte-ify 4 0)))
  :hints (("Goal" :in-theory (e/d* () ()))))

(defthmd effects-to-gc-variables-nc
  (implies (and (bind-free '((addr . addr)) (addr))
                (preconditions addr x86))
           (equal (mv-nth 1 (rb
                             (create-canonical-address-list 4 (+ -20 (xr :rgf *rsp* x86)))
                             :r
                             (x86-run (gc-clk-main-before-call) x86)))
                  (byte-ify 4 0))))

(defthmd effects-to-gc-variables-nw
  (implies (and (bind-free '((addr . addr)) (addr))
                (preconditions addr x86))
           (equal (mv-nth 1 (rb
                             (create-canonical-address-list 4 (+ -24 (xr :rgf *rsp* x86)))
                             :r
                             (x86-run (gc-clk-main-before-call) x86)))
                  (byte-ify 4 0))))

(defthmd effects-to-gc-variables-nl
  (implies (and (bind-free '((addr . addr)) (addr))
                (preconditions addr x86))
           (equal (mv-nth 1 (rb
                             (create-canonical-address-list 4 (+ -28 (xr :rgf *rsp* x86)))
                             :r
                             (x86-run (gc-clk-main-before-call) x86)))
                  (byte-ify 4 0))))

;;======================================================================
;; --------------------------------------------------------------------
;;======================================================================

;; Now follow some theorems about env-assumptions before we reason
;; about the GC function.  Note that these theorems are specific to
;; our chosen model of the file system in the environment field; they
;; say something about the conditions that need to be true in order to
;; have the system calls return the correct answer (i.e., not -1).
;; See machine/x86-syscalls.lisp for details.

;; env-assumptions:

(encapsulate
 ()

 (local (in-theory (e/d* (take nthcdr) ())))

 (local
  (encapsulate
   ()

   (local (include-book "std/lists/take" :dir :system))

   (local
    (defthm len-grab-bytes-when-string-non-empty-helper-1
      (implies (and (byte-listp bytes-of-obj)
                    (< obj-offset (len bytes-of-obj))
                    (< 0 (len bytes-of-obj)))
               (and (byte-listp (nthcdr obj-offset bytes-of-obj))
                    (< 0 (len (nthcdr obj-offset bytes-of-obj)))))))

   (local
    (defthm len-grab-bytes-when-string-non-empty-helper-2
      (implies (and (byte-listp bytes-of-obj)
                    (< obj-offset (len bytes-of-obj))
                    (< 0 (len bytes-of-obj)))
               (byte-listp (take 1 (nthcdr obj-offset
                                           bytes-of-obj))))
      :hints (("Goal" :in-theory (e/d* () (take-byte-listp))
               :use ((:instance take-byte-listp
                                (xs (nthcdr obj-offset bytes-of-obj))
                                (n 1)))))))

   (defthmd len-grab-bytes-when-string-non-empty
     (implies (and (byte-listp bytes-of-obj)
                   (< obj-offset (len bytes-of-obj))
                   (< 0 (len bytes-of-obj)))
              (and (nthcdr obj-offset bytes-of-obj)
                   (< 0 (len (nthcdr obj-offset bytes-of-obj)))
                   (byte-listp (nthcdr obj-offset bytes-of-obj))
                   (take 1 (nthcdr obj-offset bytes-of-obj))
                   (true-listp (take 1 (nthcdr obj-offset bytes-of-obj)))
                   (byte-listp (take 1 (nthcdr obj-offset bytes-of-obj)))

                   (grab-bytes (take 1 (nthcdr obj-offset bytes-of-obj)))
                   (equal (len (grab-bytes (take 1 (nthcdr obj-offset bytes-of-obj)))) 1)
                   (byte-listp (grab-bytes (take 1 (nthcdr obj-offset bytes-of-obj))))
                   (true-listp (grab-bytes (take 1 (nthcdr obj-offset bytes-of-obj))))
                   (unsigned-byte-p 8 (car (grab-bytes (take 1 (nthcdr obj-offset bytes-of-obj)))))))
     :hints (("Goal" :in-theory (e/d* (grab-bytes
                                       unsigned-byte-p)
                                      (len-grab-bytes-when-string-non-empty-helper-2))
              :use ((:instance len-grab-bytes-when-string-non-empty-helper-2)))))

   )) ;; End of local encapsulate

 (defthm byte-listp-of-bytes-of-obj-from-environment-assumptions
   (b* ((file-des-field (read-x86-file-des 0 x86))
        (obj-name (cdr (assoc :name file-des-field)))
        (obj-contents-field (read-x86-file-contents obj-name x86))
        (obj-contents (cdr (assoc :contents obj-contents-field)))
        (bytes-of-obj (string-to-bytes obj-contents)))
       (implies
        ;; (and (file-descriptor-fieldp file-des-field)
        ;;      (file-contents-fieldp obj-contents-field))
        (and (env-assumptions x86)
             (x86p x86))
        (byte-listp bytes-of-obj)))
   :hints (("Goal" :in-theory (e/d* (len-grab-bytes-when-string-non-empty env-assumptions)
                                    (take nthcdr)))))


 (defthm byte-listp-and-consp-of-take-from-environment-assumptions
   (b* ((file-des-field (read-x86-file-des 0 x86))
        (obj-offset (cdr (assoc :offset file-des-field)))
        (obj-name (cdr (assoc :name file-des-field)))
        (obj-contents-field (read-x86-file-contents obj-name x86))
        (obj-contents (cdr (assoc :contents obj-contents-field)))
        (bytes-of-obj (string-to-bytes obj-contents)))
       (implies
        ;; (and (file-descriptor-fieldp file-des-field)
        ;;      (file-contents-fieldp obj-contents-field))
        (and (env-assumptions x86)
             (x86p x86))
        (and (byte-listp (take 1 (nthcdr obj-offset bytes-of-obj)))
             (consp (take 1 (nthcdr obj-offset bytes-of-obj))))))
   :hints (("Goal" :in-theory (e/d* (env-assumptions)
                                    (take nthcdr)))))

 (defthm byte-listp-of-grab-bytes-from-environment-assumptions
   (b* ((file-des-field (read-x86-file-des 0 x86))
        (obj-offset (cdr (assoc :offset file-des-field)))
        (obj-name (cdr (assoc :name file-des-field)))
        (obj-contents-field (read-x86-file-contents obj-name x86))
        (obj-contents (cdr (assoc :contents obj-contents-field)))
        (bytes-of-obj (string-to-bytes obj-contents)))
       (implies
        ;; (and (file-descriptor-fieldp file-des-field)
        ;;      (file-contents-fieldp obj-contents-field))
        (and (env-assumptions x86)
             (x86p x86))
        (byte-listp (grab-bytes (take 1 (nthcdr obj-offset bytes-of-obj))))))
   :hints (("Goal" :in-theory (e/d* (len-grab-bytes-when-string-non-empty env-assumptions)
                                    (take nthcdr)))))

 (defthm non-nil-grab-bytes-of-take-1-from-environment-assumptions
   (b* ((file-des-field (read-x86-file-des 0 x86))
        (obj-offset (cdr (assoc :offset file-des-field)))
        (obj-name (cdr (assoc :name file-des-field)))
        (obj-contents-field (read-x86-file-contents obj-name x86))
        (obj-contents (cdr (assoc :contents obj-contents-field)))
        (bytes-of-obj (string-to-bytes obj-contents)))
       (implies
        ;; (and (file-descriptor-fieldp file-des-field)
        ;;      (file-contents-fieldp obj-contents-field)
        ;;      (< obj-offset (len bytes-of-obj)))
        (and (env-assumptions x86)
             (x86p x86))
        (and (nthcdr obj-offset bytes-of-obj)
             (grab-bytes (take 1 (nthcdr obj-offset bytes-of-obj))))))
   :hints (("Goal" :in-theory (e/d* (len-grab-bytes-when-string-non-empty env-assumptions)
                                    (take nthcdr acl2::take-of-1 acl2::take-of-zero)))))

 (defthm len-of-grab-bytes-take-1-from-environment-assumptions
   (b* ((file-des-field (read-x86-file-des 0 x86))
        (obj-offset (cdr (assoc :offset file-des-field)))
        (obj-name (cdr (assoc :name file-des-field)))
        (obj-contents-field (read-x86-file-contents obj-name x86))
        (obj-contents (cdr (assoc :contents obj-contents-field)))
        (bytes-of-obj (string-to-bytes obj-contents)))
       (implies
        ;; (and (file-descriptor-fieldp file-des-field)
        ;;      (file-contents-fieldp obj-contents-field)
        ;;      (< obj-offset (len bytes-of-obj)))
        (and (env-assumptions x86)
             (x86p x86))
        (equal (len (grab-bytes (take 1 (nthcdr obj-offset bytes-of-obj)))) 1)))
   :hints (("Goal" :in-theory (e/d* (len-grab-bytes-when-string-non-empty env-assumptions)
                                    (take nthcdr acl2::take-of-zero acl2::take-of-1)))))

 (defthm n08p-of-car-grab-bytes-from-environment-assumptions
   (b* ((file-des-field (read-x86-file-des 0 x86))
        (obj-offset (cdr (assoc :offset file-des-field)))
        (obj-name (cdr (assoc :name file-des-field)))
        (obj-contents-field (read-x86-file-contents obj-name x86))
        (obj-contents (cdr (assoc :contents obj-contents-field)))
        (bytes-of-obj (string-to-bytes obj-contents)))
       (implies
        ;; (and (file-descriptor-fieldp file-des-field)
        ;;      (file-contents-fieldp obj-contents-field)
        ;;      (< obj-offset (len bytes-of-obj)))
        (and (env-assumptions x86)
             (x86p x86))
        (unsigned-byte-p 8 (car (grab-bytes (take 1 (nthcdr obj-offset bytes-of-obj)))))))
   :hints (("Goal" :in-theory (e/d* (len-grab-bytes-when-string-non-empty env-assumptions)
                                    (take nthcdr acl2::take-of-1 acl2::take-of-zero)))))

 (defthm len-of-nthcdr-of-object-from-environment-assumptions
   (implies (and (file-descriptor-fieldp (read-x86-file-des 0 x86))
                 (equal obj-offset (cdr (assoc :offset (read-x86-file-des 0 x86))))
                 (equal obj-name (cdr (assoc :name (read-x86-file-des 0 x86))))
                 (equal obj-contents-field (read-x86-file-contents obj-name x86))
                 (file-contents-fieldp obj-contents-field)
                 (equal obj-contents (cdr (assoc :contents obj-contents-field)))
                 (equal bytes-of-obj (string-to-bytes obj-contents))
                 (< obj-offset (len bytes-of-obj)))
            (< 0 (len (nthcdr obj-offset bytes-of-obj))))
   :hints (("Goal" :in-theory (e/d* (len-grab-bytes-when-string-non-empty env-assumptions)
                                    (take nthcdr acl2::take-of-zero acl2::take-of-1))))
   :rule-classes (:linear :rewrite))

 ) ;; End of encapsulate

(local (in-theory (e/d* () (acl2::take-of-1 acl2::take-of-zero take nthcdr))))

(encapsulate
 ()

 (local (include-book "std/lists/last" :dir :system))

 (defthm last-is-eof-but-first-is-not-eof-=>-at-least-two-elements
   (implies
    (and (equal (last bl) (list *eof*))
         (natp i)
         (< i (len bl))
         (not (equal (car (grab-bytes (take 1 (nthcdr i bl))))
                     *eof*))
         (< 0 (len bl))
         (byte-listp bl))
    (< (+ 1 i) (len bl)))
   :hints (("Goal" :induct (nthcdr i bl)
            :in-theory (e/d* (nthcdr) ()))))

 ) ;; End of encapsulate

;;**********************************************************************
;; Call to GC + GC Procedure
;;**********************************************************************

(defthm effects-call-gc
  ;;  callq <gc>
  ;;  push %rbp
  ;;  mov %rsp,%rbp
  ;;  push %rbx
  ;;  lea -0x9(%rbp),%rax
  ;;  mov %rax,-0x20(%rbp)
  ;;  mov $0x0,%rax
  ;;  xor %rdi,%rdi
  ;;  mov -0x20(%rbp),%rsi
  ;;  mov $0x1,%rdx
  ;;  syscall
  ;;  mov %eax,%ebx
  ;;  mov %ebx,-0x10(%rbp)
  ;;  movzbl -0x9(%rbp),%eax
  ;;  movzbl %al,%eax
  ;;  pop %rbx
  ;;  pop %rbp
  ;;  retq

  (implies ;; Doesn't have the rbp binding of loop-preconditions
   (and (x86p x86)
        (xr :programmer-level-mode 0 x86)
        (not (alignment-checking-enabled-p x86))
        (equal (xr :os-info 0 x86) :linux)
        (env-assumptions x86)
        (canonical-address-p (xr :rgf *rsp* x86))
        ;; Address of the call instruction in the main sub-routine
        ;; 95: Position of the call instruction in the main sub-routine
        ;; (equal (xr :rip 0 x86) (+ (1- (+ (len *gc*) 95)) addr))
        (equal addr (- (xr :rip 0 x86) (1- (+ (len *gc*) 95))))
        (canonical-address-p addr)
        (canonical-address-p (+ (1- (len *wc*)) addr))
        (canonical-address-p (+ #x20 (xr :rgf *rsp* x86)))
        (canonical-address-p (+ (- (+ 8 #x20 8)) (xr :rgf *rsp* x86)))
        ;; (+ 8 #x20 8 #x20) = 80
        (disjoint-p
         ;; IMPORTANT: Keep the program addresses as the first
         ;; argument.
         (create-canonical-address-list (len *wc*) addr)
         (create-canonical-address-list 80 (+ (- (+ 8 #x20 8)) (xr :rgf *rsp* x86))))
        (equal (xr :ms 0 x86) nil)
        (equal (xr :fault 0 x86) nil)
        ;; Enabling the SYSCALL instruction.
        (equal (ia32_efer-slice :ia32_efer-sce (xr :msr *ia32_efer-idx* x86)) 1)
        (equal (ia32_efer-slice :ia32_efer-lma (xr :msr *ia32_efer-idx* x86)) 1)
        (program-at (create-canonical-address-list (len *wc*) addr) *wc* x86))
   (equal (x86-run (gc-clk) x86)
          (XW
           :RGF *RAX*
           (LOGHEAD
            32
            (CDR
             (ASSOC-EQUAL
              (+ -25 (XR :RGF *RSP* X86))
              (ACL2::REV
               (CREATE-ADDR-BYTES-ALIST
                (LIST (+ -25 (XR :RGF *RSP* X86)))
                (GRAB-BYTES
                 (TAKE
                  1
                  (NTHCDR
                   (CDR (ASSOC-EQUAL :OFFSET (READ-X86-FILE-DES 0 X86)))
                   (STRING-TO-BYTES
                    (CDR
                     (ASSOC-EQUAL
                      :CONTENTS
                      (READ-X86-FILE-CONTENTS
                       (CDR (ASSOC-EQUAL :NAME (READ-X86-FILE-DES 0 X86)))
                       X86))))))))))))
           (XW
            :RGF *RCX* (+ -109 (XR :RIP 0 X86))
            (XW
             :RGF *RDX* 1
             (XW
              :RGF *RBX* (XR :RGF *RBX* X86)
              (XW
               :RGF *RSP* (XR :RGF *RSP* X86)
               (XW
                :RGF *RBP* (XR :RGF *RBP* X86)
                (XW
                 :RGF *RSI* (+ -25 (XR :RGF *RSP* X86))
                 (XW
                  :RGF *RDI* 0
                  (XW
                   :RGF *R11*
                   (LOGIOR
                    256
                    (LOGAND
                     -257
                     (LOGEXT
                      64
                      (XR
                       :RFLAGS 0
                       (!FLGI-UNDEFINED
                        4
                        (!FLGI
                         *CF* 0
                         (!FLGI
                          *PF* 1
                          (!FLGI
                           *AF*
                           (BITOPS::LOGSQUASH
                            -3
                            (LOGHEAD 1
                                     (BOOL->BIT (LOGBITP 4 (XR :RFLAGS 0 X86)))))
                           (!FLGI *ZF* 1
                                  (!FLGI *SF* 0 (!FLGI *OF* 0 X86)))))))))))
                   (XW
                    :RIP 0 (+ 5 (XR :RIP 0 X86))
                    (MV-NTH
                     1
                     (WB
                      (APPEND
                       (CREATE-ADDR-BYTES-ALIST
                        (CREATE-CANONICAL-ADDRESS-LIST 8 (+ -8 (XR :RGF *RSP* X86)))
                        (BYTE-IFY 8 (+ 5 (XR :RIP 0 X86))))
                       (CREATE-ADDR-BYTES-ALIST
                        (CREATE-CANONICAL-ADDRESS-LIST 8 (+ -16 (XR :RGF *RSP* X86)))
                        (BYTE-IFY 8 (LOGHEAD 64 (XR :RGF *RBP* X86))))
                       (CREATE-ADDR-BYTES-ALIST
                        (CREATE-CANONICAL-ADDRESS-LIST 8 (+ -24 (XR :RGF *RSP* X86)))
                        (BYTE-IFY 8 (LOGHEAD 64 (XR :RGF *RBX* X86))))
                       (CREATE-ADDR-BYTES-ALIST
                        (CREATE-CANONICAL-ADDRESS-LIST 8 (+ -48 (XR :RGF *RSP* X86)))
                        (BYTE-IFY 8
                                  (LOGHEAD 64 (+ -25 (XR :RGF *RSP* X86)))))
                       (CREATE-ADDR-BYTES-ALIST
                        (LIST (+ -25 (XR :RGF *RSP* X86)))
                        (GRAB-BYTES
                         (TAKE
                          1
                          (NTHCDR
                           (CDR (ASSOC-EQUAL :OFFSET (READ-X86-FILE-DES 0 X86)))
                           (STRING-TO-BYTES
                            (CDR
                             (ASSOC-EQUAL
                              :CONTENTS
                              (READ-X86-FILE-CONTENTS
                               (CDR (ASSOC-EQUAL :NAME (READ-X86-FILE-DES 0 X86)))
                               X86))))))))
                       (CREATE-ADDR-BYTES-ALIST
                        (CREATE-CANONICAL-ADDRESS-LIST 4 (+ -32 (XR :RGF *RSP* X86)))
                        '(1 0 0 0)))
                      (!FLGI
                       *RF* 0
                       (!FLGI
                        *VM* 0
                        (WRITE-X86-FILE-DES
                         0
                         (PUT-ASSOC-EQUAL
                          :OFFSET
                          (+ 1
                             (CDR (ASSOC-EQUAL :OFFSET (READ-X86-FILE-DES 0 X86))))
                          (READ-X86-FILE-DES 0 X86))
                         (!FLGI-UNDEFINED
                          4
                          (!FLGI
                           *CF* 0
                           (!FLGI
                            *PF* 1
                            (!FLGI
                             *AF*
                             (BITOPS::LOGSQUASH
                              -3
                              (LOGHEAD 1
                                       (BOOL->BIT (LOGBITP 4 (XR :RFLAGS 0 X86)))))
                             (!FLGI *ZF* 1
                                    (!FLGI *SF* 0
                                           (!FLGI *OF* 0 X86))))))))))))))))))))))))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (e/d* (
                             syscall-read
                             syscall-read-logic
                             x86-syscall-read
                             syscall-write
                             syscall-write-logic
                             x86-syscall-write
                             env-assumptions
                             gc-clk

                             instruction-decoding-and-spec-rules

                             gpr-add-spec-4
                             gpr-add-spec-8
                             gpr-sub-spec-8
                             gpr-xor-spec-8
                             jcc/cmovcc/setcc-spec
                             imul-spec
                             imul-spec-32
                             gpr-sub-spec-4

                             top-level-opcode-execute
                             !rgfi-size
                             x86-operand-to-reg/mem
                             wr64
                             wr32
                             rr32
                             rr64
                             rm32
                             rm64
                             wm32
                             wm64
                             write-canonical-address-to-memory
                             rr32
                             x86-operand-from-modr/m-and-sib-bytes
                             rim-size
                             rim32
                             n32-to-i32
                             n64-to-i64
                             rim08
                             rim64
                             two-byte-opcode-decode-and-execute
                             x86-effective-addr
                             subset-p
                             rr08
                             rr16
                             rr32
                             rr64
                             ;; Flags
                             write-user-rflags)

                            (wb-remove-duplicate-writes
                             force (force))))))

;; ----------------------------------------------------------------------
;; Call GC + GC Procedure: Projection Theorems:
;; ----------------------------------------------------------------------

(defthmd effects-call-gc-ms-projection
  (implies (and (x86p x86) ;; Doesn't have the rbp binding of loop-preconditions
                (xr :programmer-level-mode 0 x86)
                (not (alignment-checking-enabled-p x86))
                (equal (xr :os-info 0 x86) :linux)
                (env-assumptions x86)
                (canonical-address-p (xr :rgf *rsp* x86))
                ;; Address of the call instruction in the main sub-routine
                ;; 95: Position of the call instruction in the main sub-routine
                ;; (equal (xr :rip 0 x86) (+ (1- (+ (len *gc*) 95)) addr))
                (equal addr (- (xr :rip 0 x86) (1- (+ (len *gc*) 95))))
                (canonical-address-p addr)
                (canonical-address-p (+ (1- (len *wc*)) addr))
                (canonical-address-p (+ #x20 (xr :rgf *rsp* x86)))
                (canonical-address-p (+ (- (+ 8 #x20 8)) (xr :rgf *rsp* x86)))
                ;; (+ 8 #x20 8 #x20) = 80
                (disjoint-p
                 ;; IMPORTANT: Keep the program addresses as the first
                 ;; argument.
                 (create-canonical-address-list (len *wc*) addr)
                 (create-canonical-address-list 80 (+ (- (+ 8 #x20 8)) (xr :rgf *rsp* x86))))
                (equal (xr :ms 0 x86) nil)
                (equal (xr :fault 0 x86) nil)
                ;; Enabling the SYSCALL instruction.
                (equal (ia32_efer-slice :ia32_efer-sce (xr :msr *ia32_efer-idx* x86)) 1)
                (equal (ia32_efer-slice :ia32_efer-lma (xr :msr *ia32_efer-idx* x86)) 1)
                (program-at (create-canonical-address-list (len *wc*) addr) *wc* x86))

           (equal (xr :ms 0 (x86-run (gc-clk) x86)) nil)))

(defthmd effects-call-gc-fault-projection
  (implies
   (and (x86p x86) ;; Doesn't have the rbp binding of loop-preconditions
        (xr :programmer-level-mode 0 x86)
        (not (alignment-checking-enabled-p x86))
        (equal (xr :os-info 0 x86) :linux)
        (env-assumptions x86)
        (canonical-address-p (xr :rgf *rsp* x86))
        ;; Address of the call instruction in the main sub-routine
        ;; 95: Position of the call instruction in the main sub-routine
        ;; (equal (xr :rip 0 x86) (+ (1- (+ (len *gc*) 95)) addr))
        (equal addr (- (xr :rip 0 x86) (1- (+ (len *gc*) 95))))
        (canonical-address-p addr)
        (canonical-address-p (+ (1- (len *wc*)) addr))
        (canonical-address-p (+ #x20 (xr :rgf *rsp* x86)))
        (canonical-address-p (+ (- (+ 8 #x20 8)) (xr :rgf *rsp* x86)))
        ;; (+ 8 #x20 8 #x20) = 80
        (disjoint-p
         ;; IMPORTANT: Keep the program addresses as the first
         ;; argument.
         (create-canonical-address-list (len *wc*) addr)
         (create-canonical-address-list 80 (+ (- (+ 8 #x20 8)) (xr :rgf *rsp* x86))))
        (equal (xr :ms 0 x86) nil)
        (equal (xr :fault 0 x86) nil)
        ;; Enabling the SYSCALL instruction.
        (equal (ia32_efer-slice :ia32_efer-sce (xr :msr *ia32_efer-idx* x86)) 1)
        (equal (ia32_efer-slice :ia32_efer-lma (xr :msr *ia32_efer-idx* x86)) 1)
        (program-at (create-canonical-address-list (len *wc*) addr) *wc* x86))
   (equal (xr :fault 0 (x86-run (gc-clk) x86)) nil)))

;; ======================================================================
;; Effect theorems for the different branches in code:

;;**********************************************************************
;; EOF encountered
;;**********************************************************************

(encapsulate
 ()
 (local (include-book "std/lists/nthcdr" :dir :system))

 (defthm assoc-equal-of-rev-of-alist
   (implies (equal (len val) 1)
            (equal (cdr (assoc-equal key (acl2::rev (create-addr-bytes-alist (list key) val))))
                   (car val)))))

(defthmd effects-eof-encountered-1

  ;;  callq <gc>
  ;;
  ;;  mov %eax,-0x4(%rbp)
  ;;  cmpl $0x23,-0x4(%rbp)
  ;;  jne 40050b <main+0x24>
  ;;  mov $0x0,%eax

  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (equal (get-char (offset x86) (input x86)) *eof*))
           (equal (x86-run (clk+ 4 (gc-clk)) x86)
                  (XW
                   :RGF *RAX* 0
                   (XW
                    :RGF *RCX* (+ -109 (XR :RIP 0 X86))
                    (XW
                     :RGF *RDX* 1
                     (XW
                      :RGF *RBX* (XR :RGF *RBX* X86)
                      (XW
                       :RGF *RSP* (XR :RGF *RSP* X86)
                       (XW
                        :RGF *RBP* (+ 32 (XR :RGF *RSP* X86))
                        (XW
                         :RGF *RSI* (+ -25 (XR :RGF *RSP* X86))
                         (XW
                          :RGF *RDI* 0
                          (XW
                           :RGF *R11*
                           (LOGIOR
                            256
                            (LOGAND
                             -257
                             (LOGEXT
                              64
                              (XR
                               :RFLAGS 0
                               (!FLGI-UNDEFINED
                                4
                                (!FLGI
                                 *CF* 0
                                 (!FLGI
                                  *PF* 1
                                  (!FLGI
                                   *AF*
                                   (BITOPS::LOGSQUASH
                                    -3
                                    (LOGHEAD 1
                                             (BOOL->BIT (LOGBITP 4 (XR :RFLAGS 0 X86)))))
                                   (!FLGI *ZF* 1
                                          (!FLGI *SF* 0 (!FLGI *OF* 0 X86)))))))))))
                           (XW
                            :RIP 0 (+ 19 (XR :RIP 0 X86))
                            (MV-NTH
                             1
                             (WB
                              (APPEND
                               (CREATE-ADDR-BYTES-ALIST
                                (CREATE-CANONICAL-ADDRESS-LIST 8 (+ -8 (XR :RGF *RSP* X86)))
                                (BYTE-IFY 8 (+ 5 (XR :RIP 0 X86))))
                               (CREATE-ADDR-BYTES-ALIST
                                (CREATE-CANONICAL-ADDRESS-LIST 8 (+ -16 (XR :RGF *RSP* X86)))
                                (BYTE-IFY 8
                                          (LOGHEAD 64 (+ 32 (XR :RGF *RSP* X86)))))
                               (CREATE-ADDR-BYTES-ALIST
                                (CREATE-CANONICAL-ADDRESS-LIST 8 (+ -24 (XR :RGF *RSP* X86)))
                                (BYTE-IFY 8 (LOGHEAD 64 (XR :RGF *RBX* X86))))
                               (CREATE-ADDR-BYTES-ALIST
                                (CREATE-CANONICAL-ADDRESS-LIST 8 (+ -48 (XR :RGF *RSP* X86)))
                                (BYTE-IFY 8
                                          (LOGHEAD 64 (+ -25 (XR :RGF *RSP* X86)))))
                               (CREATE-ADDR-BYTES-ALIST
                                (LIST (+ -25 (XR :RGF *RSP* X86)))
                                (GRAB-BYTES
                                 (TAKE
                                  1
                                  (NTHCDR
                                   (CDR (ASSOC-EQUAL :OFFSET (READ-X86-FILE-DES 0 X86)))
                                   (STRING-TO-BYTES
                                    (CDR
                                     (ASSOC-EQUAL
                                      :CONTENTS
                                      (READ-X86-FILE-CONTENTS
                                       (CDR (ASSOC-EQUAL :NAME (READ-X86-FILE-DES 0 X86)))
                                       X86))))))))
                               (CREATE-ADDR-BYTES-ALIST
                                (CREATE-CANONICAL-ADDRESS-LIST 4 (+ -32 (XR :RGF *RSP* X86)))
                                '(1 0 0 0))
                               (CREATE-ADDR-BYTES-ALIST
                                (CREATE-CANONICAL-ADDRESS-LIST 4 (+ 28 (XR :RGF *RSP* X86)))
                                '(35 0 0 0)))
                              (!FLGI
                               *CF* 0
                               (!FLGI
                                *PF* 1
                                (!FLGI
                                 *AF* 0
                                 (!FLGI
                                  *ZF* 1
                                  (!FLGI
                                   *SF* 0
                                   (!FLGI
                                    *OF* 0
                                    (!FLGI
                                     *RF* 0
                                     (!FLGI
                                      *VM* 0
                                      (WRITE-X86-FILE-DES
                                       0
                                       (PUT-ASSOC-EQUAL
                                        :OFFSET
                                        (+
                                         1
                                         (CDR
                                          (ASSOC-EQUAL :OFFSET (READ-X86-FILE-DES 0 X86))))
                                        (READ-X86-FILE-DES 0 X86))
                                       (!FLGI-UNDEFINED
                                        4
                                        (!FLGI
                                         *CF* 0
                                         (!FLGI
                                          *PF* 1
                                          (!FLGI
                                           *AF*
                                           (BITOPS::LOGSQUASH
                                            -3
                                            (LOGHEAD
                                             1
                                             (BOOL->BIT (LOGBITP 4 (XR :RFLAGS 0 X86)))))
                                           (!FLGI
                                            *ZF* 1
                                            (!FLGI
                                             *SF* 0
                                             (!FLGI *OF* 0 X86))))))))))))))))))))))))))))))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (e/d* (top-level-opcode-execute
                             instruction-decoding-and-spec-rules

                             gpr-sub-spec-4
                             jcc/cmovcc/setcc-spec

                             write-user-rflags
                             !rgfi-size
                             x86-operand-to-reg/mem
                             wr64
                             wr32
                             rr08
                             rr32
                             rr64
                             x86-operand-from-modr/m-and-sib-bytes
                             rim-size
                             rim08
                             rm32
                             wm-size
                             wm32
                             two-byte-opcode-decode-and-execute
                             x86-effective-addr
                             x86-run-plus-1
                             effects-call-gc-ms-projection
                             effects-call-gc-fault-projection
                             loop-preconditions)
                            (x86-run-plus)))))

(defthm effects-eof-encountered

  ;;   callq <gc>
  ;;
  ;;   mov %eax,-0x4(%rbp)
  ;;   cmpl $0x23,-0x4(%rbp)
  ;;   jne 40050b <main+0x24>
  ;;   mov $0x0,%eax

  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (equal (get-char (offset x86) (input x86)) *eof*))
           (equal (x86-run (gc-clk-eof) x86)
                  (XW
                   :RGF *RAX* 0
                   (XW
                    :RGF *RCX* (+ -109 (XR :RIP 0 X86))
                    (XW
                     :RGF *RDX* 1
                     (XW
                      :RGF *RBX* (XR :RGF *RBX* X86)
                      (XW
                       :RGF *RSP* (XR :RGF *RSP* X86)
                       (XW
                        :RGF *RBP* (+ 32 (XR :RGF *RSP* X86))
                        (XW
                         :RGF *RSI* (+ -25 (XR :RGF *RSP* X86))
                         (XW
                          :RGF *RDI* 0
                          (XW
                           :RGF *R11*
                           (LOGIOR
                            256
                            (LOGAND
                             -257
                             (LOGEXT
                              64
                              (XR
                               :RFLAGS 0
                               (!FLGI-UNDEFINED
                                4
                                (!FLGI
                                 *CF* 0
                                 (!FLGI
                                  *PF* 1
                                  (!FLGI
                                   *AF*
                                   (BITOPS::LOGSQUASH
                                    -3
                                    (LOGHEAD 1
                                             (BOOL->BIT (LOGBITP 4 (XR :RFLAGS 0 X86)))))
                                   (!FLGI *ZF* 1
                                          (!FLGI *SF* 0 (!FLGI *OF* 0 X86)))))))))))
                           (XW
                            :RIP 0 (+ 19 (XR :RIP 0 X86))
                            (MV-NTH
                             1
                             (WB
                              (APPEND
                               (CREATE-ADDR-BYTES-ALIST
                                (CREATE-CANONICAL-ADDRESS-LIST 8 (+ -8 (XR :RGF *RSP* X86)))
                                (BYTE-IFY 8 (+ 5 (XR :RIP 0 X86))))
                               (CREATE-ADDR-BYTES-ALIST
                                (CREATE-CANONICAL-ADDRESS-LIST 8 (+ -16 (XR :RGF *RSP* X86)))
                                (BYTE-IFY 8
                                          (LOGHEAD 64 (+ 32 (XR :RGF *RSP* X86)))))
                               (CREATE-ADDR-BYTES-ALIST
                                (CREATE-CANONICAL-ADDRESS-LIST 8 (+ -24 (XR :RGF *RSP* X86)))
                                (BYTE-IFY 8 (LOGHEAD 64 (XR :RGF *RBX* X86))))
                               (CREATE-ADDR-BYTES-ALIST
                                (CREATE-CANONICAL-ADDRESS-LIST 8 (+ -48 (XR :RGF *RSP* X86)))
                                (BYTE-IFY 8
                                          (LOGHEAD 64 (+ -25 (XR :RGF *RSP* X86)))))
                               (CREATE-ADDR-BYTES-ALIST
                                (LIST (+ -25 (XR :RGF *RSP* X86)))
                                (GRAB-BYTES
                                 (TAKE
                                  1
                                  (NTHCDR
                                   (CDR (ASSOC-EQUAL :OFFSET (READ-X86-FILE-DES 0 X86)))
                                   (STRING-TO-BYTES
                                    (CDR
                                     (ASSOC-EQUAL
                                      :CONTENTS
                                      (READ-X86-FILE-CONTENTS
                                       (CDR (ASSOC-EQUAL :NAME (READ-X86-FILE-DES 0 X86)))
                                       X86))))))))
                               (CREATE-ADDR-BYTES-ALIST
                                (CREATE-CANONICAL-ADDRESS-LIST 4 (+ -32 (XR :RGF *RSP* X86)))
                                '(1 0 0 0))
                               (CREATE-ADDR-BYTES-ALIST
                                (CREATE-CANONICAL-ADDRESS-LIST 4 (+ 28 (XR :RGF *RSP* X86)))
                                '(35 0 0 0)))
                              (!FLGI
                               *CF* 0
                               (!FLGI
                                *PF* 1
                                (!FLGI
                                 *AF* 0
                                 (!FLGI
                                  *ZF* 1
                                  (!FLGI
                                   *SF* 0
                                   (!FLGI
                                    *OF* 0
                                    (!FLGI
                                     *RF* 0
                                     (!FLGI
                                      *VM* 0
                                      (WRITE-X86-FILE-DES
                                       0
                                       (PUT-ASSOC-EQUAL
                                        :OFFSET
                                        (+
                                         1
                                         (CDR
                                          (ASSOC-EQUAL :OFFSET (READ-X86-FILE-DES 0 X86))))
                                        (READ-X86-FILE-DES 0 X86))
                                       (!FLGI-UNDEFINED
                                        4
                                        (!FLGI
                                         *CF* 0
                                         (!FLGI
                                          *PF* 1
                                          (!FLGI
                                           *AF*
                                           (BITOPS::LOGSQUASH
                                            -3
                                            (LOGHEAD
                                             1
                                             (BOOL->BIT (LOGBITP 4 (XR :RFLAGS 0 X86)))))
                                           (!FLGI
                                            *ZF* 1
                                            (!FLGI
                                             *SF* 0
                                             (!FLGI *OF* 0 X86))))))))))))))))))))))))))))))
  :hints (("Goal" :do-not '(preprocess)
           :expand (gc-clk-eof)
           :in-theory (union-theories
                       '(gc-clk-eof
                         effects-eof-encountered-1)
                       (theory 'minimal-theory)))))

;;----------------------------------------------------------------------
;; EOF Encountered: Projection Theorems:
;;----------------------------------------------------------------------

(defthmd effects-eof-encountered-rsp-projection
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (equal (get-char (offset x86) (input x86)) *eof*))
           (equal (xr :rgf *rsp* (x86-run (gc-clk-eof) x86))
                  (xr :rgf *rsp* x86))))

(defthmd effects-eof-encountered-rbp-projection
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (equal (get-char (offset x86) (input x86)) *eof*))
           (equal (xr :rgf *rbp* (x86-run (gc-clk-eof) x86))
                  (xr :rgf *rbp* x86))))

(defthmd x86p-effects-eof-encountered
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (equal (get-char (offset x86) (input x86)) *eof*))
           (x86p (x86-run (gc-clk-eof) x86)))
  :hints (("Goal" :in-theory (e/d* (loop-preconditions) ()))))

(defthmd effects-eof-encountered-msri-projection
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (equal (get-char (offset x86) (input x86)) *eof*))
           (and (equal (ia32_efer-slice :ia32_efer-sce (xr :msr *ia32_efer-idx* (x86-run (gc-clk-eof) x86))) 1)
                (equal (ia32_efer-slice :ia32_efer-lma (xr :msr *ia32_efer-idx* (x86-run (gc-clk-eof) x86))) 1)))
  :hints (("Goal" :use ((:instance loop-preconditions-fwd-chaining-essentials)))))

(defthmd effects-eof-encountered-rip-projection
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (equal (get-char (offset x86) (input x86)) *eof*))
           (equal (xr :rip 0 (x86-run (gc-clk-eof) x86)) (+ 164 addr))))

(defthmd effects-eof-encountered-env-stdin-des-projection
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (equal (get-char (offset x86) (input x86)) *eof*))
           (and (equal (cdr (assoc-equal
                             :name
                             (read-x86-file-des 0 (x86-run (gc-clk-eof) x86))))
                       (cdr (assoc-equal
                             :name
                             (read-x86-file-des 0 x86))))
                (equal (cdr (assoc-equal
                             :offset
                             (read-x86-file-des 0 (x86-run (gc-clk-eof) x86))))
                       (+ 1
                          (cdr (assoc-equal
                                :offset
                                (read-x86-file-des 0 x86)))))))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (e/d* (env-assumptions) ())
           :use ((:instance loop-preconditions-fwd-chaining-essentials)))))

(defthmd effects-eof-encountered-env-stdin-contents-projection
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (equal (get-char (offset x86) (input x86)) *eof*))
           (equal
            (read-x86-file-contents
             (cdr (assoc-equal :name (read-x86-file-des 0 x86)))
             (x86-run (gc-clk-eof) x86))
            (read-x86-file-contents
             (cdr (assoc-equal :name (read-x86-file-des 0 x86)))
             x86)))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (e/d* (env-assumptions) ())
           :use ((:instance loop-preconditions-fwd-chaining-essentials)))))

(defthmd effects-eof-encountered-ms-projection
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (equal (get-char (offset x86) (input x86)) *eof*))
           (equal (xr :ms 0 (x86-run (gc-clk-eof) x86)) nil)))

(defthmd effects-eof-encountered-fault-projection
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (equal (get-char (offset x86) (input x86)) *eof*))
           (equal (xr :fault 0 (x86-run (gc-clk-eof) x86)) nil)))

;;----------------------------------------------------------------------
;; EOF Encountered: Delta Variable Theorems:
;;----------------------------------------------------------------------

(defthmd effects-eof-encountered-variables-state
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (equal (get-char (offset x86) (input x86)) *eof*))
           (equal (word-state x86 (x86-run (gc-clk-eof) x86))
                  (word-state x86 x86)))
  :hints (("Goal" :in-theory (e/d*
                              (loop-preconditions-weird-rbp-rsp)
                              ()))))

(defthmd effects-eof-encountered-variables-nc
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (equal (get-char (offset x86) (input x86)) *eof*))
           (equal (nc x86 (x86-run (gc-clk-eof) x86))
                  (nc x86 x86)))
  :hints (("Goal" :in-theory (e/d*
                              (loop-preconditions-weird-rbp-rsp)
                              ()))))

(defthmd effects-eof-encountered-variables-nw
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (equal (get-char (offset x86) (input x86)) *eof*))
           (equal (nw x86 (x86-run (gc-clk-eof) x86))
                  (nw x86 x86)))
  :hints (("Goal" :in-theory (e/d*
                              (loop-preconditions-weird-rbp-rsp)
                              ()))))

(defthmd effects-eof-encountered-variables-nl
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (equal (get-char (offset x86) (input x86)) *eof*))
           (equal (nl x86 (x86-run (gc-clk-eof) x86))
                  (nl x86 x86)))
  :hints (("Goal" :in-theory (e/d*
                              (loop-preconditions-weird-rbp-rsp)
                              ()))))

;;**********************************************************************
;; EOF Not Encountered (prelim to other branches)
;;**********************************************************************

(encapsulate
 ()

 (local (include-book "arithmetic-5/top" :dir :system))

 (defthm effects-eof-not-encountered-prelim-helper
   (implies (and (not (equal char 35))
                 (unsigned-byte-p 8 char))
            (equal (equal (loghead 32 (+ -35 (logext 32 char))) 0) nil))
   :hints (("Goal" :in-theory (e/d* (loghead)
                                    ())))))

(defthm effects-eof-not-encountered-prelim

  ;;  callq <gc>
  ;;
  ;;  mov %eax,-0x4(%rbp)
  ;;  cmpl $0x23,-0x4(%rbp)
  ;;  jne 40050b <main+0x24>

  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (not (equal (get-char (offset x86) (input x86)) *eof*)))
           (equal (x86-run (gc-clk-no-eof) x86)
                  (XW
                   :RGF *RAX*
                   (LOGHEAD
                    32
                    (CAR
                     (GRAB-BYTES
                      (TAKE
                       1
                       (NTHCDR
                        (CDR (ASSOC-EQUAL :OFFSET (READ-X86-FILE-DES 0 X86)))
                        (STRING-TO-BYTES
                         (CDR
                          (ASSOC-EQUAL
                           :CONTENTS (READ-X86-FILE-CONTENTS
                                      (CDR (ASSOC-EQUAL :NAME (READ-X86-FILE-DES 0 X86)))
                                      X86)))))))))
                   (XW
                    :RGF *RCX* (+ -109 (XR :RIP 0 X86))
                    (XW
                     :RGF *RDX* 1
                     (XW
                      :RGF *RBX* (XR :RGF *RBX* X86)
                      (XW
                       :RGF *RSP* (XR :RGF *RSP* X86)
                       (XW
                        :RGF *RBP* (+ 32 (XR :RGF *RSP* X86))
                        (XW
                         :RGF *RSI* (+ -25 (XR :RGF *RSP* X86))
                         (XW
                          :RGF *RDI* 0
                          (XW
                           :RGF *R11*
                           (LOGIOR
                            256
                            (LOGAND
                             -257
                             (LOGEXT
                              64
                              (XR
                               :RFLAGS 0
                               (!FLGI-UNDEFINED
                                4
                                (!FLGI
                                 *CF* 0
                                 (!FLGI
                                  *PF* 1
                                  (!FLGI
                                   *AF*
                                   (BITOPS::LOGSQUASH
                                    -3
                                    (LOGHEAD 1
                                             (BOOL->BIT (LOGBITP 4 (XR :RFLAGS 0 X86)))))
                                   (!FLGI *ZF* 1
                                          (!FLGI *SF* 0 (!FLGI *OF* 0 X86)))))))))))
                           (XW
                            :RIP 0 (+ -58 (XR :RIP 0 X86))
                            (MV-NTH
                             1
                             (WB
                              (APPEND
                               (CREATE-ADDR-BYTES-ALIST
                                (CREATE-CANONICAL-ADDRESS-LIST 8 (+ -8 (XR :RGF *RSP* X86)))
                                (BYTE-IFY 8 (+ 5 (XR :RIP 0 X86))))
                               (CREATE-ADDR-BYTES-ALIST
                                (CREATE-CANONICAL-ADDRESS-LIST 8 (+ -16 (XR :RGF *RSP* X86)))
                                (BYTE-IFY 8
                                          (LOGHEAD 64 (+ 32 (XR :RGF *RSP* X86)))))
                               (CREATE-ADDR-BYTES-ALIST
                                (CREATE-CANONICAL-ADDRESS-LIST 8 (+ -24 (XR :RGF *RSP* X86)))
                                (BYTE-IFY 8 (LOGHEAD 64 (XR :RGF *RBX* X86))))
                               (CREATE-ADDR-BYTES-ALIST
                                (CREATE-CANONICAL-ADDRESS-LIST 8 (+ -48 (XR :RGF *RSP* X86)))
                                (BYTE-IFY 8
                                          (LOGHEAD 64 (+ -25 (XR :RGF *RSP* X86)))))
                               (CREATE-ADDR-BYTES-ALIST
                                (LIST (+ -25 (XR :RGF *RSP* X86)))
                                (GRAB-BYTES
                                 (TAKE
                                  1
                                  (NTHCDR
                                   (CDR (ASSOC-EQUAL :OFFSET (READ-X86-FILE-DES 0 X86)))
                                   (STRING-TO-BYTES
                                    (CDR
                                     (ASSOC-EQUAL
                                      :CONTENTS
                                      (READ-X86-FILE-CONTENTS
                                       (CDR (ASSOC-EQUAL :NAME (READ-X86-FILE-DES 0 X86)))
                                       X86))))))))
                               (CREATE-ADDR-BYTES-ALIST
                                (CREATE-CANONICAL-ADDRESS-LIST 4 (+ -32 (XR :RGF *RSP* X86)))
                                '(1 0 0 0))
                               (CREATE-ADDR-BYTES-ALIST
                                (CREATE-CANONICAL-ADDRESS-LIST 4 (+ 28 (XR :RGF *RSP* X86)))
                                (BYTE-IFY
                                 4
                                 (LOGHEAD
                                  32
                                  (CAR
                                   (GRAB-BYTES
                                    (TAKE
                                     1
                                     (NTHCDR
                                      (CDR (ASSOC-EQUAL :OFFSET (READ-X86-FILE-DES 0 X86)))
                                      (STRING-TO-BYTES
                                       (CDR
                                        (ASSOC-EQUAL
                                         :CONTENTS
                                         (READ-X86-FILE-CONTENTS
                                          (CDR (ASSOC-EQUAL :NAME (READ-X86-FILE-DES 0 X86)))
                                          X86))))))))))))
                              (!FLGI
                               *CF*
                               (LOGHEAD
                                1
                                (BOOL->BIT
                                 (<
                                  (LOGHEAD
                                   32
                                   (CAR
                                    (GRAB-BYTES
                                     (TAKE
                                      1
                                      (NTHCDR
                                       (CDR (ASSOC-EQUAL :OFFSET (READ-X86-FILE-DES 0 X86)))
                                       (STRING-TO-BYTES
                                        (CDR
                                         (ASSOC-EQUAL
                                          :CONTENTS
                                          (READ-X86-FILE-CONTENTS
                                           (CDR
                                            (ASSOC-EQUAL :NAME (READ-X86-FILE-DES 0 X86)))
                                           X86)))))))))
                                  35)))
                               (!FLGI
                                *PF*
                                (LOGIOR
                                 (PF-SPEC32
                                  (LOGHEAD
                                   32
                                   (+
                                    -35
                                    (LOGEXT
                                     32
                                     (CAR
                                      (GRAB-BYTES
                                       (TAKE
                                        1
                                        (NTHCDR
                                         (CDR
                                          (ASSOC-EQUAL :OFFSET (READ-X86-FILE-DES 0 X86)))
                                         (STRING-TO-BYTES
                                          (CDR
                                           (ASSOC-EQUAL
                                            :CONTENTS
                                            (READ-X86-FILE-CONTENTS
                                             (CDR
                                              (ASSOC-EQUAL :NAME (READ-X86-FILE-DES 0 X86)))
                                             X86))))))))))))
                                 (LOGHEAD
                                  -1
                                  (LOGTAIL
                                   2
                                   (BOOL->BIT
                                    (<
                                     (LOGHEAD
                                      32
                                      (CAR
                                       (GRAB-BYTES
                                        (TAKE
                                         1
                                         (NTHCDR
                                          (CDR
                                           (ASSOC-EQUAL :OFFSET (READ-X86-FILE-DES 0 X86)))
                                          (STRING-TO-BYTES
                                           (CDR
                                            (ASSOC-EQUAL
                                             :CONTENTS
                                             (READ-X86-FILE-CONTENTS
                                              (CDR
                                               (ASSOC-EQUAL :NAME (READ-X86-FILE-DES 0 X86)))
                                              X86)))))))))
                                     35)))))
                                (!FLGI
                                 *AF*
                                 (LOGIOR
                                  (SUB-AF-SPEC32
                                   (LOGHEAD
                                    32
                                    (CAR
                                     (GRAB-BYTES
                                      (TAKE
                                       1
                                       (NTHCDR
                                        (CDR (ASSOC-EQUAL :OFFSET (READ-X86-FILE-DES 0 X86)))
                                        (STRING-TO-BYTES
                                         (CDR
                                          (ASSOC-EQUAL
                                           :CONTENTS
                                           (READ-X86-FILE-CONTENTS
                                            (CDR
                                             (ASSOC-EQUAL :NAME (READ-X86-FILE-DES 0 X86)))
                                            X86)))))))))
                                   35)
                                  (LOGHEAD
                                   -3
                                   (LOGTAIL
                                    4
                                    (BOOL->BIT
                                     (<
                                      (LOGHEAD
                                       32
                                       (CAR
                                        (GRAB-BYTES
                                         (TAKE
                                          1
                                          (NTHCDR
                                           (CDR
                                            (ASSOC-EQUAL :OFFSET (READ-X86-FILE-DES 0 X86)))
                                           (STRING-TO-BYTES
                                            (CDR
                                             (ASSOC-EQUAL
                                              :CONTENTS
                                              (READ-X86-FILE-CONTENTS
                                               (CDR (ASSOC-EQUAL
                                                     :NAME (READ-X86-FILE-DES 0 X86)))
                                               X86)))))))))
                                      35)))))
                                 (!FLGI
                                  *ZF* 0
                                  (!FLGI
                                   *SF*
                                   (LOGIOR
                                    (SF-SPEC32
                                     (LOGHEAD
                                      32
                                      (+
                                       -35
                                       (LOGEXT
                                        32
                                        (CAR
                                         (GRAB-BYTES
                                          (TAKE
                                           1
                                           (NTHCDR
                                            (CDR
                                             (ASSOC-EQUAL :OFFSET (READ-X86-FILE-DES 0 X86)))
                                            (STRING-TO-BYTES
                                             (CDR
                                              (ASSOC-EQUAL
                                               :CONTENTS
                                               (READ-X86-FILE-CONTENTS
                                                (CDR (ASSOC-EQUAL
                                                      :NAME (READ-X86-FILE-DES 0 X86)))
                                                X86))))))))))))
                                    (LOGHEAD
                                     -6
                                     (LOGTAIL
                                      7
                                      (BOOL->BIT
                                       (<
                                        (LOGHEAD
                                         32
                                         (CAR
                                          (GRAB-BYTES
                                           (TAKE
                                            1
                                            (NTHCDR
                                             (CDR (ASSOC-EQUAL
                                                   :OFFSET (READ-X86-FILE-DES 0 X86)))
                                             (STRING-TO-BYTES
                                              (CDR
                                               (ASSOC-EQUAL
                                                :CONTENTS
                                                (READ-X86-FILE-CONTENTS
                                                 (CDR (ASSOC-EQUAL
                                                       :NAME (READ-X86-FILE-DES 0 X86)))
                                                 X86)))))))))
                                        35)))))
                                   (!FLGI
                                    *OF*
                                    (LOGIOR
                                     (OF-SPEC32
                                      (+
                                       -35
                                       (LOGEXT
                                        32
                                        (CAR
                                         (GRAB-BYTES
                                          (TAKE
                                           1
                                           (NTHCDR
                                            (CDR
                                             (ASSOC-EQUAL :OFFSET (READ-X86-FILE-DES 0 X86)))
                                            (STRING-TO-BYTES
                                             (CDR
                                              (ASSOC-EQUAL
                                               :CONTENTS
                                               (READ-X86-FILE-CONTENTS
                                                (CDR (ASSOC-EQUAL
                                                      :NAME (READ-X86-FILE-DES 0 X86)))
                                                X86)))))))))))
                                     (LOGHEAD
                                      -10
                                      (LOGTAIL
                                       11
                                       (BOOL->BIT
                                        (<
                                         (LOGHEAD
                                          32
                                          (CAR
                                           (GRAB-BYTES
                                            (TAKE
                                             1
                                             (NTHCDR
                                              (CDR (ASSOC-EQUAL
                                                    :OFFSET (READ-X86-FILE-DES 0 X86)))
                                              (STRING-TO-BYTES
                                               (CDR
                                                (ASSOC-EQUAL
                                                 :CONTENTS
                                                 (READ-X86-FILE-CONTENTS
                                                  (CDR (ASSOC-EQUAL
                                                        :NAME (READ-X86-FILE-DES 0 X86)))
                                                  X86)))))))))
                                         35)))))
                                    (!FLGI
                                     *RF* 0
                                     (!FLGI
                                      *VM* 0
                                      (WRITE-X86-FILE-DES
                                       0
                                       (PUT-ASSOC-EQUAL
                                        :OFFSET
                                        (+
                                         1
                                         (CDR
                                          (ASSOC-EQUAL :OFFSET (READ-X86-FILE-DES 0 X86))))
                                        (READ-X86-FILE-DES 0 X86))
                                       (!FLGI-UNDEFINED
                                        4
                                        (!FLGI
                                         *CF* 0
                                         (!FLGI
                                          *PF* 1
                                          (!FLGI
                                           *AF*
                                           (BITOPS::LOGSQUASH
                                            -3
                                            (LOGHEAD
                                             1
                                             (BOOL->BIT (LOGBITP 4 (XR :RFLAGS 0 X86)))))
                                           (!FLGI
                                            *ZF* 1
                                            (!FLGI
                                             *SF* 0
                                             (!FLGI *OF* 0 X86))))))))))))))))))))))))))))))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (e/d* (top-level-opcode-execute
                             instruction-decoding-and-spec-rules

                             gpr-sub-spec-4
                             jcc/cmovcc/setcc-spec

                             write-user-rflags
                             !rgfi-size
                             x86-operand-to-reg/mem
                             wr64
                             wr32
                             rr08
                             rr32
                             rr64
                             x86-operand-from-modr/m-and-sib-bytes
                             rim-size
                             rim08
                             rm32
                             wm-size
                             wm32
                             two-byte-opcode-decode-and-execute
                             x86-effective-addr
                             x86-run-plus-1
                             loop-preconditions

                             gc-clk-no-eof)
                            (x86-run-plus)))))

;;----------------------------------------------------------------------
;; EOF Not Encountered: Projection Theorems:
;;----------------------------------------------------------------------

(defthmd effects-eof-not-encountered-prelim-rip-projection
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (not (equal (get-char (offset x86) (input x86)) *eof*)))
           (equal (xr :rip 0 (x86-run (gc-clk-no-eof) x86)) (+ 87 addr))))

(defthmd effects-eof-not-encountered-prelim-ms-projection
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (not (equal (get-char (offset x86) (input x86)) *eof*)))
           (equal (xr :ms 0 (x86-run (gc-clk-no-eof) x86)) nil)))

(defthmd effects-eof-not-encountered-prelim-fault-projection
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (not (equal (get-char (offset x86) (input x86)) *eof*)))
           (equal (xr :fault 0 (x86-run (gc-clk-no-eof) x86)) nil)))

(defthmd effects-eof-not-encountered-prelim-msri-projection
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (not (equal (get-char (offset x86) (input x86)) *eof*)))
           (and (equal (ia32_efer-slice :ia32_efer-sce (xr :msr *ia32_efer-idx* (x86-run (gc-clk-no-eof) x86))) 1)
                (equal (ia32_efer-slice :ia32_efer-lma (xr :msr *ia32_efer-idx* (x86-run (gc-clk-no-eof) x86))) 1)))
  :hints (("Goal" :use ((:instance loop-preconditions-fwd-chaining-essentials)))))

(defthmd effects-eof-not-encountered-prelim-rsp-projection
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (not (equal (get-char (offset x86) (input x86)) *eof*)))
           (equal (xr :rgf *rsp* (x86-run (gc-clk-no-eof) x86))
                  (xr :rgf *rsp* x86))))

(defthmd effects-eof-not-encountered-prelim-rbp-projection
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (not (equal (get-char (offset x86) (input x86)) *eof*)))
           (equal (xr :rgf *rbp* (x86-run (gc-clk-no-eof) x86))
                  (xr :rgf *rbp* x86))))

(defthmd effects-eof-not-encountered-prelim-x86p-projection
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (not (equal (get-char (offset x86) (input x86)) *eof*)))
           (x86p (x86-run (gc-clk-no-eof) x86)))
  :hints (("Goal" :in-theory (e/d* (loop-preconditions) ()))))

(defthmd effects-eof-not-encountered-prelim-program-projection
  (implies (and (loop-preconditions addr x86)
                (equal len-wc (len *wc*))
                (not (equal (get-char (offset x86) (input x86)) *eof*)))
           (program-at (create-canonical-address-list len-wc addr)
                       *wc* (x86-run (gc-clk-no-eof) x86))))

(defthmd effects-eof-not-encountered-prelim-env-assumptions-projection
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (not (equal (get-char (offset x86) (input x86)) *eof*)))
           (env-assumptions (x86-run (gc-clk-no-eof) x86)))
  :hints (("Goal" :in-theory
           ;; Needed for
           ;; last-is-eof-but-first-is-not-eof-=>-at-least-two-elements
           ;; to fire...
           (e/d* (env-assumptions
                 eof-terminatedp)
                ())
           :use ((:instance
                  loop-preconditions-fwd-chaining-essentials)))))

(defthmd effects-eof-not-encountered-prelim-gc-byte-projection
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (not (equal (get-char (offset x86) (input x86))
                            *eof*)))
           (equal (mv-nth 1 (rb (create-canonical-address-list 4 (+ -4 (xr :rgf *rbp* x86)))
                                :r (x86-run (gc-clk-no-eof) x86)))
                  (byte-ify
                   4
                   (loghead
                    32
                    (car
                     (grab-bytes
                      (take
                       1
                       (nthcdr
                        (cdr (assoc-equal :offset (read-x86-file-des 0 x86)))
                        (string-to-bytes
                         (cdr
                          (assoc-equal
                           :contents (read-x86-file-contents
                                      (cdr (assoc-equal :name (read-x86-file-des 0 x86)))
                                      x86))))))))))))
  :hints (("Goal" :use ((:instance loop-preconditions-fwd-chaining-essentials)))))

(defthmd effects-eof-not-encountered-prelim-gc-byte-projection-size
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (not (equal (get-char (offset x86) (input x86))
                            *eof*)))
           (unsigned-byte-p
            8
            (combine-bytes
             (mv-nth 1 (rb (create-canonical-address-list 4 (+ -4 (xr :rgf *rbp* x86)))
                           :r (x86-run (gc-clk-no-eof) x86))))))
  :hints (("Goal"
           :use ((:instance effects-eof-not-encountered-prelim-gc-byte-projection)
                 (:instance n08p-of-car-grab-bytes-from-environment-assumptions))
           :in-theory (e/d* (remove-loghead-from-byte-ify
                             combine-bytes-and-byte-ify-inequality-lemma)
                            (effects-eof-not-encountered-prelim
                             n08p-of-car-grab-bytes-from-environment-assumptions)))))

(defthmd effects-eof-not-encountered-prelim-word-state-projection
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (not (equal (get-char (offset x86) (input x86))
                            *eof*)))
           (equal (word-state x86 (x86-run (gc-clk-no-eof) x86))
                  (word-state x86 x86))))

(defthmd effects-eof-not-encountered-prelim-nc-projection
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (not (equal (get-char (offset x86) (input x86)) *eof*)))
           (equal (nc x86 (x86-run (gc-clk-no-eof) x86))
                  (nc x86 x86))))

(defthmd effects-eof-not-encountered-prelim-nw-projection
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (not (equal (get-char (offset x86) (input x86)) *eof*)))
           (equal (nw x86 (x86-run (gc-clk-no-eof) x86))
                  (nw x86 x86))))

(defthmd effects-eof-not-encountered-prelim-nl-projection
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (not (equal (get-char (offset x86) (input x86)) *eof*)))
           (equal (nl x86 (x86-run (gc-clk-no-eof) x86))
                  (nl x86 x86))))

(defthmd effects-eof-not-encountered-prelim-programmer-level-mode-projection
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (not (equal (get-char (offset x86) (input x86)) *eof*)))
           (equal (xr :programmer-level-mode 0 (x86-run (gc-clk-no-eof) x86))
                  (xr :programmer-level-mode 0 x86))))

(defthmd effects-eof-not-encountered-prelim-alignment-checking-enabled-p-projection
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (not (equal (get-char (offset x86) (input x86)) *eof*)))
           (equal (alignment-checking-enabled-p (x86-run (gc-clk-no-eof) x86))
                  (alignment-checking-enabled-p x86))))

(defthmd effects-eof-not-encountered-prelim-os-info-projection
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (not (equal (get-char (offset x86) (input x86)) *eof*)))
           (equal (xr :os-info 0 (x86-run (gc-clk-no-eof) x86))
                  (xr :os-info 0 x86))))

(defthmd effects-eof-not-encountered-prelim-for-composition
  (implies (and (loop-preconditions addr x86)
                (not (equal (get-char (offset x86) (input x86)) *eof*)))
           (and (x86p (x86-run (gc-clk-no-eof) x86))
                (equal (xr :programmer-level-mode 0 (x86-run (gc-clk-no-eof) x86))
                       (xr :programmer-level-mode 0 x86))
                (equal (alignment-checking-enabled-p (x86-run (gc-clk-no-eof) x86))
                       (alignment-checking-enabled-p x86))
                (equal (xr :os-info 0 (x86-run (gc-clk-no-eof) x86))
                       (xr :os-info 0 x86))
                (equal (xr :rgf *rsp* (x86-run (gc-clk-no-eof) x86))
                       (xr :rgf *rsp* x86))
                (equal (xr :rgf *rbp* (x86-run (gc-clk-no-eof) x86))
                       (+ 32 (xr :rgf *rsp* x86)))
                (equal (xr :rip 0 (x86-run (gc-clk-no-eof) x86)) (+ 87 addr))
                (equal (xr :ms 0 (x86-run (gc-clk-no-eof) x86)) nil)
                (equal (xr :fault 0 (x86-run (gc-clk-no-eof) x86)) nil)
                (equal (ia32_efer-slice :ia32_efer-sce (xr :msr *ia32_efer-idx* (x86-run (gc-clk-no-eof) x86))) 1)
                (equal (ia32_efer-slice :ia32_efer-lma (xr :msr *ia32_efer-idx* (x86-run (gc-clk-no-eof) x86))) 1)
                (program-at (create-canonical-address-list (len *wc*) addr)
                            *wc* (x86-run (gc-clk-no-eof) x86))
                (equal (mv-nth 1 (rb (create-canonical-address-list 4 (+ -4 (xr :rgf *rbp* x86)))
                                     :r
                                     (x86-run (gc-clk-no-eof) x86)))
                       (byte-ify
                        4
                        (loghead
                         32
                         (car
                          (grab-bytes
                           (take
                            1
                            (nthcdr
                             (cdr (assoc-equal :offset (read-x86-file-des 0 x86)))
                             (string-to-bytes
                              (cdr
                               (assoc-equal
                                :contents (read-x86-file-contents
                                           (cdr (assoc-equal :name (read-x86-file-des 0 x86)))
                                           x86)))))))))))))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (union-theories
                       '(subset-p
                         effects-eof-not-encountered-prelim-programmer-level-mode-projection
                         effects-eof-not-encountered-prelim-alignment-checking-enabled-p-projection
                         effects-eof-not-encountered-prelim-rip-projection
                         effects-eof-not-encountered-prelim-fault-projection
                         effects-eof-not-encountered-prelim-ms-projection
                         effects-eof-not-encountered-prelim-msri-projection
                         effects-eof-not-encountered-prelim-rsp-projection
                         effects-eof-not-encountered-prelim-rbp-projection
                         effects-eof-not-encountered-prelim-x86p-projection
                         effects-eof-not-encountered-prelim-program-projection
                         effects-eof-not-encountered-prelim-gc-byte-projection
                         effects-eof-not-encountered-prelim-word-state-projection
                         effects-eof-not-encountered-prelim-os-info-projection
                         loop-preconditions-forward-chain-addresses-info)
                       (theory 'minimal-theory)))))

;;**********************************************************************
;; Newline Encountered
;;**********************************************************************

;; First, a dumb run-plus helper theorem:

(defthmd dumb-run-plus-thm
  (implies (and (x86p x86)
                (or (equal x 10)
                    (equal x 7)
                    (equal x 11)
                    (equal x 13)))
           (equal (x86-run (binary-clk+ x (gc-clk-no-eof)) x86)
                  (x86-run x (x86-run (gc-clk-no-eof) x86))))
  :hints (("Goal" :in-theory (e/d* (x86-run-plus-1)
                                   (x86-run-plus)))))


(defthmd programmer-level-mode-permissions-dont-matter
  ;; [Shilpi]: This thing won't be true once I incorporate the
  ;; memory-permissions map into the programmer-level mode, unless I make sure
  ;; that the memory regions in question are both read and execute enabled.

  (implies (and (xr :programmer-level-mode 0 x86)
                (x86p x86))
           (equal (mv-nth 1 (rb addresses :x x86))
                  (mv-nth 1 (rb addresses :r x86))))
  :hints (("Goal" :in-theory (e/d* (rb rm08)
                                   (rb-1-accumulator-thm)))
          ("Subgoal *1/5"
           :use ((:instance rb-1-accumulator-thm
                            (acc (list (mv-nth 1 (rvm08 (car addresses) x86))))
                            (addresses (cdr addresses))
                            (r-w-x :r))
                 (:instance rb-1-accumulator-thm
                            (acc (list (mv-nth 1 (rvm08 (car addresses) x86))))
                            (addresses (cdr addresses))
                            (r-w-x :x))))))

(defthmd effects-newline-encountered-limited

  ;;  callq <gc>
  ;;
  ;;  addl $0x1,-0x10(%rbp)
  ;;  callq <gc>

  (implies
   (and (x86p x86-new)
        (xr :programmer-level-mode 0 x86-new)
        (not (alignment-checking-enabled-p x86-new))
        (env-assumptions x86-new)
        (canonical-address-p (xr :rgf *rsp* x86-new))

        ;; Points to the "addl $0x1,-0xc(%rbp)" instruction in main
        (equal addr (- (xr :rip 0 x86-new) (+ 37 (1- (len *gc*)))))

        (canonical-address-p addr)
        (canonical-address-p (+ (1- (len *wc*)) addr))
        (canonical-address-p (+ #x20 (xr :rgf *rsp* x86-new)))
        (canonical-address-p (+ (- (+ 8 #x20 8)) (xr :rgf *rsp* x86-new)))
        ;; (+ 8 #x20 8 #x20) = 80
        (disjoint-p
         ;; IMPORTANT: Keep the program addresses as the first
         ;; argument.
         (create-canonical-address-list
          (len *wc*) addr)
         (create-canonical-address-list
          80 (+ (- (+ 8 #x20 8)) (xr :rgf *rsp* x86-new))))


        ;; IMPORTANT: Why doesn't the following hyp work?
        ;; (equal (xr :rgf *rbp* x86-new) (- (+ (xr :rgf *rsp* x86-new) 40) 8))
        (canonical-address-p (xr :rgf *rbp* x86-new))
        (equal (xr :rgf *rsp* x86-new)
               (- (xr :rgf *rbp* x86-new) 32))
        (equal (xr :ms 0 x86-new) nil)
        (equal (xr :fault 0 x86-new) nil)
        ;; Enabling the SYSCALL instruction.
        (equal (ia32_efer-slice :ia32_efer-sce (xr :msr *ia32_efer-idx* x86-new)) 1)
        (equal (ia32_efer-slice :ia32_efer-lma (xr :msr *ia32_efer-idx* x86-new)) 1)
        (program-at (create-canonical-address-list
                     (len *wc*) addr) *wc* x86-new)

        (equal (mv-nth 1 (rb (create-canonical-address-list 4 (+ -4 (xr :rgf *rbp* x86-new))) :x x86-new))
               (byte-ify 4 *newline*)))
   (equal (x86-run 10 x86-new)
          (XW
           :RIP 0 (+ 58 (XR :RIP 0 X86-NEW))
           (MV-NTH
            1
            (WB
             (APPEND
              (CREATE-ADDR-BYTES-ALIST
               (CREATE-CANONICAL-ADDRESS-LIST 4 (+ 20 (XR :RGF *RSP* X86-NEW)))
               (BYTE-IFY
                4
                (LOGHEAD
                 32
                 (+
                  1
                  (COMBINE-BYTES
                   (MV-NTH
                    1
                    (RB
                     (CREATE-CANONICAL-ADDRESS-LIST 4 (+ 20 (XR :RGF *RSP* X86-NEW)))
                     :X X86-NEW)))))))
              (CREATE-ADDR-BYTES-ALIST
               (CREATE-CANONICAL-ADDRESS-LIST 4 (+ 12 (XR :RGF *RSP* X86-NEW)))
               (BYTE-IFY
                4
                (LOGHEAD
                 32
                 (+
                  1
                  (COMBINE-BYTES
                   (MV-NTH
                    1
                    (RB
                     (CREATE-CANONICAL-ADDRESS-LIST 4 (+ 12 (XR :RGF *RSP* X86-NEW)))
                     :X X86-NEW)))))))
              (CREATE-ADDR-BYTES-ALIST
               (CREATE-CANONICAL-ADDRESS-LIST 4 (+ 24 (XR :RGF *RSP* X86-NEW)))
               '(0 0 0 0)))
             (!FLGI *CF* 0
                    (!FLGI *PF* 1
                           (!FLGI *AF* 0
                                  (!FLGI *ZF* 1
                                         (!FLGI *SF* 0 (!FLGI *OF* 0 X86-NEW)))))))))))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (e/d* (top-level-opcode-execute
                             instruction-decoding-and-spec-rules

                             gpr-sub-spec-4
                             gpr-add-spec-4
                             jcc/cmovcc/setcc-spec

                             write-user-rflags
                             !rgfi-size
                             x86-operand-to-reg/mem
                             wr64
                             wr32
                             rr08
                             rr32
                             rr64
                             x86-operand-from-modr/m-and-sib-bytes
                             write-canonical-address-to-memory
                             rim-size
                             rim08
                             rim32
                             rm32
                             wm-size
                             wm32
                             wm64
                             two-byte-opcode-decode-and-execute
                             x86-effective-addr
                             x86-run-plus-1)
                            (x86-run-plus)))))

(defthmd effects-newline-encountered-1

  ;;  callq <gc>
  ;;
  ;;  addl $0x1,-0x10(%rbp)
  ;;  callq <gc>

  (implies (and (loop-preconditions addr x86)
                (equal (get-char (offset x86) (input x86)) *newline*)
                (equal x86-new (x86-run (gc-clk-no-eof) x86)))
           (equal (x86-run 10 x86-new)
                  (XW
                   :RIP 0 (+ 58 (XR :RIP 0 X86-NEW))
                   (MV-NTH
                    1
                    (WB
                     (APPEND
                      (CREATE-ADDR-BYTES-ALIST
                       (CREATE-CANONICAL-ADDRESS-LIST 4 (+ 20 (XR :RGF *RSP* X86-NEW)))
                       (BYTE-IFY
                        4
                        (LOGHEAD
                         32
                         (+
                          1
                          (COMBINE-BYTES
                           (MV-NTH
                            1
                            (RB
                             (CREATE-CANONICAL-ADDRESS-LIST 4 (+ 20 (XR :RGF *RSP* X86-NEW)))
                             :X X86-NEW)))))))
                      (CREATE-ADDR-BYTES-ALIST
                       (CREATE-CANONICAL-ADDRESS-LIST 4 (+ 12 (XR :RGF *RSP* X86-NEW)))
                       (BYTE-IFY
                        4
                        (LOGHEAD
                         32
                         (+
                          1
                          (COMBINE-BYTES
                           (MV-NTH
                            1
                            (RB
                             (CREATE-CANONICAL-ADDRESS-LIST 4 (+ 12 (XR :RGF *RSP* X86-NEW)))
                             :X X86-NEW)))))))
                      (CREATE-ADDR-BYTES-ALIST
                       (CREATE-CANONICAL-ADDRESS-LIST 4 (+ 24 (XR :RGF *RSP* X86-NEW)))
                       '(0 0 0 0)))
                     (!FLGI *CF* 0
                            (!FLGI *PF* 1
                                   (!FLGI *AF* 0
                                          (!FLGI *ZF* 1
                                                 (!FLGI *SF* 0 (!FLGI *OF* 0 X86-NEW)))))))))))
  :hints (("Goal" :in-theory
           (union-theories '(loop-preconditions
                             input
                             get-char
                             offset
                             rgfi-is-i64p
                             (len) (loghead)
                             programmer-level-mode-permissions-dont-matter)
                           (theory 'minimal-theory))
           :use ((:instance effects-newline-encountered-limited
                            (x86-new (x86-run (gc-clk-no-eof) x86)))
                 (:instance effects-eof-not-encountered-prelim-env-assumptions-projection)
                 (:instance effects-eof-not-encountered-prelim-rbp-projection)
                 (:instance effects-eof-not-encountered-prelim-for-composition)))))

(defthm effects-newline-encountered

  ;;  callq <gc>
  ;;
  ;;  addl $0x1,-0x10(%rbp)
  ;;  callq <gc>

  (implies (and (loop-preconditions addr x86)
                (equal (get-char (offset x86) (input x86)) *newline*))
           (equal (x86-run (gc-clk-newline) x86)
                  (XW
                   :RIP 0 (+ 58 (XR :RIP 0 (X86-RUN (GC-CLK-NO-EOF) X86)))
                   (MV-NTH
                    1
                    (WB
                     (APPEND
                      (CREATE-ADDR-BYTES-ALIST
                       (CREATE-CANONICAL-ADDRESS-LIST
                        4 (+ 20 (XR :RGF *RSP* (X86-RUN (GC-CLK-NO-EOF) X86))))
                       (BYTE-IFY
                        4
                        (LOGHEAD
                         32
                         (+
                          1
                          (COMBINE-BYTES
                           (MV-NTH
                            1
                            (RB
                             (CREATE-CANONICAL-ADDRESS-LIST
                              4 (+ 20 (XR :RGF *RSP* (X86-RUN (GC-CLK-NO-EOF) X86))))
                             :X (X86-RUN (GC-CLK-NO-EOF) X86))))))))
                      (CREATE-ADDR-BYTES-ALIST
                       (CREATE-CANONICAL-ADDRESS-LIST
                        4 (+ 12 (XR :RGF *RSP* (X86-RUN (GC-CLK-NO-EOF) X86))))
                       (BYTE-IFY
                        4
                        (LOGHEAD
                         32
                         (+
                          1
                          (COMBINE-BYTES
                           (MV-NTH
                            1
                            (RB
                             (CREATE-CANONICAL-ADDRESS-LIST
                              4 (+ 12 (XR :RGF *RSP* (X86-RUN (GC-CLK-NO-EOF) X86))))
                             :X (X86-RUN (GC-CLK-NO-EOF) X86))))))))
                      (CREATE-ADDR-BYTES-ALIST
                       (CREATE-CANONICAL-ADDRESS-LIST
                        4 (+ 24 (XR :RGF *RSP* (X86-RUN (GC-CLK-NO-EOF) X86))))
                       '(0 0 0 0)))
                     (!FLGI *CF* 0
                            (!FLGI *PF* 1
                                   (!FLGI *AF* 0
                                          (!FLGI *ZF* 1
                                                 (!FLGI *SF* 0
                                                        (!FLGI *OF* 0 (X86-RUN (GC-CLK-NO-EOF) X86))))))))))))
  :hints (("Goal" :do-not '(preprocess)
           :expand (gc-clk-newline)
           :in-theory (union-theories
                       '(gc-clk-newline
                         loop-preconditions
                         input
                         get-char
                         offset
                         dumb-run-plus-thm)
                       (theory 'minimal-theory))
           :use ((:instance effects-newline-encountered-1
                            (x86-new (x86-run (gc-clk-no-eof) x86)))))))

;;----------------------------------------------------------------------
;; Newline Encountered: Projection Theorems:
;;----------------------------------------------------------------------

(defthmd effects-newline-encountered-rbp-projection
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (equal (get-char (offset x86) (input x86)) *newline*))
           (equal (xr :rgf *rbp* (x86-run (gc-clk-newline) x86))
                  (xr :rgf *rbp* x86))))

(defthmd effects-newline-encountered-rsp-projection
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (equal (get-char (offset x86) (input x86)) *newline*))
           (equal (xr :rgf *rsp* (x86-run (gc-clk-newline) x86))
                  (xr :rgf *rsp* x86))))

(defthmd x86p-effects-newline-encountered
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (equal (get-char (offset x86) (input x86)) *newline*))
           (x86p (x86-run (gc-clk-newline) x86)))
  :hints (("Goal" :in-theory (e/d* (loop-preconditions) ()))))

(defthmd effects-newline-encountered-msri-projection
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (equal (get-char (offset x86) (input x86)) *newline*))
           (and (equal (ia32_efer-slice :ia32_efer-sce (xr :msr *ia32_efer-idx* (x86-run (gc-clk-newline) x86))) 1)
                (equal (ia32_efer-slice :ia32_efer-lma (xr :msr *ia32_efer-idx* (x86-run (gc-clk-newline) x86))) 1)))
  :hints (("Goal" :use ((:instance loop-preconditions-fwd-chaining-essentials)))))

(defthmd effects-newline-encountered-rip-projection
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (equal (get-char (offset x86) (input x86)) *newline*))
           (equal (xr :rip 0 (x86-run (gc-clk-newline) x86)) (+ 145 addr))))

(defthmd effects-newline-encountered-ms-projection
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (equal (get-char (offset x86) (input x86)) *newline*))
           (equal (xr :ms 0 (x86-run (gc-clk-newline) x86)) nil)))

(defthmd effects-newline-encountered-fault-projection
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (equal (get-char (offset x86) (input x86)) *newline*))
           (equal (xr :fault 0 (x86-run (gc-clk-newline) x86)) nil)))

(defthmd effects-newline-encountered-program-projection
  (implies (and (loop-preconditions addr x86)
                (equal len-wc (len *wc*))
                (equal (get-char (offset x86) (input x86)) *newline*))
           (program-at (create-canonical-address-list len-wc addr)
                       *wc* (x86-run (gc-clk-newline) x86))))

(defthmd effects-newline-encountered-env-assumptions-projection
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (equal (get-char (offset x86) (input x86)) *newline*))
           (env-assumptions (x86-run (gc-clk-newline) x86)))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (e/d*
                       (effects-eof-not-encountered-prelim-env-assumptions-projection
                        effects-eof-not-encountered-prelim-programmer-level-mode-projection
                        effects-eof-not-encountered-prelim-x86p-projection)
                       ()))
          ("Goal''" :in-theory (e/d* (env-assumptions eof-terminatedp) ())
           :use ((:instance loop-preconditions-fwd-chaining-essentials)))))

(defthmd effects-newline-encountered-programmer-level-mode-projection
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (equal (get-char (offset x86) (input x86)) *newline*))
           (equal (xr :programmer-level-mode 0 (x86-run (gc-clk-newline) x86))
                  (xr :programmer-level-mode 0 x86))))

(defthmd effects-newline-encountered-alignment-checking-enabled-p-projection
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (equal (get-char (offset x86) (input x86)) *newline*))
           (equal (alignment-checking-enabled-p (x86-run (gc-clk-newline) x86))
                  (alignment-checking-enabled-p x86))))

(defthmd effects-newline-encountered-os-info-projection
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (equal (get-char (offset x86) (input x86)) *newline*))
           (equal (xr :os-info 0 (x86-run (gc-clk-newline) x86))
                  (xr :os-info 0 x86))))

(defthm loop-preconditions-newline-encountered
  (implies (and (loop-preconditions addr x86)
                (equal (get-char (offset x86) (input x86)) *newline*))
           (loop-preconditions addr (x86-run (gc-clk-newline) x86)))
  :hints (("Goal" :in-theory '(effects-newline-encountered-rbp-projection
                               effects-newline-encountered-rsp-projection
                               x86p-effects-newline-encountered
                               effects-newline-encountered-msri-projection
                               effects-newline-encountered-rip-projection
                               effects-newline-encountered-ms-projection
                               effects-newline-encountered-fault-projection
                               effects-newline-encountered-env-assumptions-projection
                               effects-newline-encountered-alignment-checking-enabled-p-projection
                               (len)
                               loop-preconditions-fwd-chaining-essentials
                               loop-preconditions-forward-chain-addresses-info
                               effects-newline-encountered-programmer-level-mode-projection
                               effects-newline-encountered-os-info-projection
                               effects-newline-encountered-program-projection)
           :expand (loop-preconditions addr (x86-run (gc-clk-newline) x86)))))

(defthmd effects-newline-encountered-input-projection
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (equal (get-char (offset x86) (input x86)) *newline*))
           (equal (input (x86-run (gc-clk-newline) x86))
                  (input x86))))

(defthmd effects-newline-encountered-offset-projection
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (equal (get-char (offset x86) (input x86)) *newline*))
           (equal (offset (x86-run (gc-clk-newline) x86))
                  (+ 1 (offset x86)))))

;;----------------------------------------------------------------------
;; Newline Encountered: Delta Variable Theorems:
;;----------------------------------------------------------------------

(defthmd effects-newline-encountered-variables-state
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (equal (get-char (offset x86) (input x86)) *newline*))
           (equal (combine-bytes (word-state x86 (x86-run (gc-clk-newline) x86)))
                  *out*)))

(defthmd effects-newline-encountered-variables-state-in-terms-of-next-x86
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (equal (get-char (offset x86) (input x86)) *newline*))
           (equal (word-state (x86-run (gc-clk-newline) x86) xxx)
                  (word-state x86 xxx)))
  :hints (("Goal" :in-theory
           '(effects-newline-encountered-rbp-projection
             word-state))))

(defthmd effects-newline-encountered-variables-nc
  (implies (and (loop-preconditions addr x86)
                (equal (get-char (offset x86) (input x86)) *newline*))
           (equal (combine-bytes (nc x86 (x86-run (gc-clk-newline) x86)))
                  (loghead 32 (+ 1 (combine-bytes (nc x86 x86))))))
  :hints (("Goal" :in-theory (e/d*
                              (programmer-level-mode-permissions-dont-matter)
                              (force (force))))))

(defthmd effects-newline-encountered-variables-nc-in-terms-of-next-x86
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (equal (get-char (offset x86) (input x86)) *newline*))
           (equal (nc (x86-run (gc-clk-newline) x86) xxx)
                  (nc x86 xxx)))
  :hints (("Goal" :in-theory
           '(effects-newline-encountered-rbp-projection
             nc))))

(defthmd effects-newline-encountered-variables-nw
  (implies (and (loop-preconditions addr x86)
                (equal (get-char (offset x86) (input x86)) *newline*))
           (equal (nw x86 (x86-run (gc-clk-newline) x86))
                  (nw x86 x86))))

(defthmd effects-newline-encountered-variables-nw-in-terms-of-next-x86
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (equal (get-char (offset x86) (input x86)) *newline*))
           (equal (nw (x86-run (gc-clk-newline) x86) xxx)
                  (nw x86 xxx)))
  :hints (("Goal" :in-theory
           '(effects-newline-encountered-rbp-projection
             nw))))

(defthmd effects-newline-encountered-variables-nl
  (implies (and (loop-preconditions addr x86)
                (equal (get-char (offset x86) (input x86)) *newline*))
           (equal (combine-bytes (nl x86 (x86-run (gc-clk-newline) x86)))
                  (loghead 32 (+ 1 (combine-bytes (nl x86 x86))))))
  :hints (("Goal" :in-theory (e/d*
                              (programmer-level-mode-permissions-dont-matter)
                              (force (force))))))

(defthmd effects-newline-encountered-variables-nl-in-terms-of-next-x86
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (equal (get-char (offset x86) (input x86)) *newline*))
           (equal (nl (x86-run (gc-clk-newline) x86) xxx)
                  (nl x86 xxx)))
  :hints (("Goal" :in-theory
           '(effects-newline-encountered-rbp-projection
             nl))))

;;**********************************************************************
;; Space Encountered
;;**********************************************************************

(defthmd effects-space-encountered-limited

  ;;  callq <gc>
  ;;
  ;;  addl $0x1,-0x10(%rbp)
  ;;  callq <gc>

  (implies
   (and (x86p x86-new)
        (xr :programmer-level-mode 0 x86-new)
        (not (alignment-checking-enabled-p x86-new))
        (env-assumptions x86-new)
        (canonical-address-p (xr :rgf *rsp* x86-new))

        ;; Points to the "addl $0x1,-0xc(%rbp)" instruction in main
        (equal addr (- (xr :rip 0 x86-new) (+ 37 (1- (len *gc*)))))

        (canonical-address-p addr)
        (canonical-address-p (+ (1- (len *wc*)) addr))
        (canonical-address-p (+ #x20 (xr :rgf *rsp* x86-new)))
        (canonical-address-p (+ (- (+ 8 #x20 8)) (xr :rgf *rsp* x86-new)))
        ;; (+ 8 #x20 8 #x20) = 80
        (disjoint-p
         ;; IMPORTANT: Keep the program addresses as the first
         ;; argument.
         (create-canonical-address-list
          (len *wc*) addr)
         (create-canonical-address-list
          80 (+ (- (+ 8 #x20 8)) (xr :rgf *rsp* x86-new))))


        ;; IMPORTANT: Why doesn't the following hyp work?
        ;; (equal (xr :rgf *rbp* x86-new) (- (+ (xr :rgf *rsp* x86-new) 40) 8))
        (canonical-address-p (xr :rgf *rbp* x86-new))
        (equal (xr :rgf *rsp* x86-new)
               (- (xr :rgf *rbp* x86-new) 32))
        (equal (xr :ms 0 x86-new) nil)
        (equal (xr :fault 0 x86-new) nil)
        ;; Enabling the SYSCALL instruction.
        (equal (ia32_efer-slice :ia32_efer-sce (xr :msr *ia32_efer-idx* x86-new)) 1)
        (equal (ia32_efer-slice :ia32_efer-lma (xr :msr *ia32_efer-idx* x86-new)) 1)
        (program-at (create-canonical-address-list
                     (len *wc*) addr) *wc* x86-new)

        (equal (mv-nth 1 (rb (create-canonical-address-list 4 (+ -4 (xr :rgf *rbp* x86-new))) :x x86-new))
               (byte-ify 4 *space*)))
   (equal (x86-run 7 x86-new)
          (XW
           :RIP 0 (+ 58 (XR :RIP 0 X86-NEW))
           (MV-NTH
            1
            (WB
             (APPEND
              (CREATE-ADDR-BYTES-ALIST
               (CREATE-CANONICAL-ADDRESS-LIST 4 (+ 20 (XR :RGF *RSP* X86-NEW)))
               (BYTE-IFY
                4
                (LOGHEAD
                 32
                 (+
                  1
                  (COMBINE-BYTES
                   (MV-NTH
                    1
                    (RB
                     (CREATE-CANONICAL-ADDRESS-LIST 4 (+ 20 (XR :RGF *RSP* X86-NEW)))
                     :X X86-NEW)))))))
              (CREATE-ADDR-BYTES-ALIST
               (CREATE-CANONICAL-ADDRESS-LIST 4 (+ 24 (XR :RGF *RSP* X86-NEW)))
               '(0 0 0 0)))
             (!FLGI *CF* 0
                    (!FLGI *PF* 1
                           (!FLGI *AF* 0
                                  (!FLGI *ZF* 1
                                         (!FLGI *SF* 0 (!FLGI *OF* 0 X86-NEW)))))))))))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (e/d* (top-level-opcode-execute
                             instruction-decoding-and-spec-rules

                             gpr-sub-spec-4
                             gpr-add-spec-4
                             jcc/cmovcc/setcc-spec

                             write-user-rflags
                             !rgfi-size
                             x86-operand-to-reg/mem
                             wr64
                             wr32
                             rr08
                             rr32
                             rr64
                             x86-operand-from-modr/m-and-sib-bytes
                             write-canonical-address-to-memory
                             rim-size
                             rim08
                             rim32
                             rm32
                             wm-size
                             wm32
                             wm64
                             two-byte-opcode-decode-and-execute
                             x86-effective-addr
                             x86-run-plus-1)
                            (x86-run-plus)))))

(defthmd effects-space-encountered-1

  ;;  callq <gc>
  ;;
  ;;  addl $0x1,-0x10(%rbp)
  ;;  callq <gc>

  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (equal (get-char (offset x86) (input x86)) *space*)
                (equal x86-new (x86-run (gc-clk-no-eof) x86)))
           (equal (x86-run 7 x86-new)
                  (XW
                   :RIP 0 (+ 58 (XR :RIP 0 X86-NEW))
                   (MV-NTH
                    1
                    (WB
                     (APPEND
                      (CREATE-ADDR-BYTES-ALIST
                       (CREATE-CANONICAL-ADDRESS-LIST 4 (+ 20 (XR :RGF *RSP* X86-NEW)))
                       (BYTE-IFY
                        4
                        (LOGHEAD
                         32
                         (+
                          1
                          (COMBINE-BYTES
                           (MV-NTH
                            1
                            (RB
                             (CREATE-CANONICAL-ADDRESS-LIST 4 (+ 20 (XR :RGF *RSP* X86-NEW)))
                             :X X86-NEW)))))))
                      (CREATE-ADDR-BYTES-ALIST
                       (CREATE-CANONICAL-ADDRESS-LIST 4 (+ 24 (XR :RGF *RSP* X86-NEW)))
                       '(0 0 0 0)))
                     (!FLGI *CF* 0
                            (!FLGI *PF* 1
                                   (!FLGI *AF* 0
                                          (!FLGI *ZF* 1
                                                 (!FLGI *SF* 0 (!FLGI *OF* 0 X86-NEW)))))))))))
  :hints (("Goal" :in-theory
           (union-theories '(loop-preconditions
                             input
                             get-char
                             offset
                             rgfi-is-i64p
                             (len) (loghead)
                             programmer-level-mode-permissions-dont-matter)
                           (theory 'minimal-theory))
           :use ((:instance effects-eof-not-encountered-prelim-for-composition
                            (x86 x86))
                 (:instance
                  effects-eof-not-encountered-prelim-env-assumptions-projection
                  (x86 x86))
                 (:instance
                  effects-eof-not-encountered-prelim-rbp-projection
                  (x86 x86))
                 (:instance effects-space-encountered-limited
                            (x86-new (x86-run (gc-clk-no-eof) x86)))))))

(defthm effects-space-encountered

  ;;  callq <gc>
  ;;
  ;;  addl $0x1,-0x10(%rbp)
  ;;  callq <gc>

  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (equal (get-char (offset x86) (input x86)) *space*))
           (equal (x86-run (gc-clk-space) x86)
                  (XW
                   :RIP 0 (+ 58 (XR :RIP 0 (X86-RUN (GC-CLK-NO-EOF) X86)))
                   (MV-NTH
                    1
                    (WB
                     (APPEND
                      (CREATE-ADDR-BYTES-ALIST
                       (CREATE-CANONICAL-ADDRESS-LIST
                        4 (+ 20 (XR :RGF *RSP* (X86-RUN (GC-CLK-NO-EOF) X86))))
                       (BYTE-IFY
                        4
                        (LOGHEAD
                         32
                         (+
                          1
                          (COMBINE-BYTES
                           (MV-NTH
                            1
                            (RB
                             (CREATE-CANONICAL-ADDRESS-LIST
                              4 (+ 20 (XR :RGF *RSP* (X86-RUN (GC-CLK-NO-EOF) X86))))
                             :X (X86-RUN (GC-CLK-NO-EOF) X86))))))))
                      (CREATE-ADDR-BYTES-ALIST
                       (CREATE-CANONICAL-ADDRESS-LIST
                        4 (+ 24 (XR :RGF *RSP* (X86-RUN (GC-CLK-NO-EOF) X86))))
                       '(0 0 0 0)))
                     (!FLGI *CF* 0
                            (!FLGI *PF* 1
                                   (!FLGI *AF* 0
                                          (!FLGI *ZF* 1
                                                 (!FLGI *SF* 0
                                                        (!FLGI *OF* 0 (X86-RUN (GC-CLK-NO-EOF) X86))))))))))))
  :hints (("Goal" :do-not '(preprocess)
           :expand (gc-clk-space)
           :in-theory (union-theories
                       '(gc-clk-space
                         loop-preconditions
                         input
                         get-char
                         offset
                         dumb-run-plus-thm)
                       (theory 'minimal-theory))
           :use ((:instance effects-space-encountered-1
                            (x86-new (x86-run (gc-clk-no-eof) x86)))))))

;;----------------------------------------------------------------------
;; Space Encountered: Projection Theorems:
;;----------------------------------------------------------------------

(defthmd effects-space-encountered-rbp-projection
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (equal (get-char (offset x86) (input x86)) *space*))
           (equal (xr :rgf *rbp* (x86-run (gc-clk-space) x86))
                  (xr :rgf *rbp* x86))))

(defthmd effects-space-encountered-rsp-projection
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (equal (get-char (offset x86) (input x86)) *space*))
           (equal (xr :rgf *rsp* (x86-run (gc-clk-space) x86))
                  (xr :rgf *rsp* x86))))

(defthmd x86p-effects-space-encountered
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (equal (get-char (offset x86) (input x86)) *space*))
           (x86p (x86-run (gc-clk-space) x86)))
  :hints (("Goal" :in-theory (e/d* (loop-preconditions) ()))))

(defthmd effects-space-encountered-msri-projection
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (equal (get-char (offset x86) (input x86)) *space*))
           (and
            (equal (ia32_efer-slice :ia32_efer-sce (xr :msr *ia32_efer-idx* (x86-run (gc-clk-space) x86))) 1)
            (equal (ia32_efer-slice :ia32_efer-lma (xr :msr *ia32_efer-idx* (x86-run (gc-clk-space) x86))) 1)))
  :hints (("Goal" :use ((:instance loop-preconditions-fwd-chaining-essentials)))))

(defthmd effects-space-encountered-rip-projection
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (equal (get-char (offset x86) (input x86)) *space*))
           (equal (xr :rip 0 (x86-run (gc-clk-space) x86)) (+ 145 addr))))

(defthmd effects-space-encountered-ms-projection
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (equal (get-char (offset x86) (input x86)) *space*))
           (equal (xr :ms 0 (x86-run (gc-clk-space) x86)) nil)))

(defthmd effects-space-encountered-fault-projection
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (equal (get-char (offset x86) (input x86)) *space*))
           (equal (xr :fault 0 (x86-run (gc-clk-space) x86)) nil)))

(defthmd effects-space-encountered-program-projection
  (implies (and (loop-preconditions addr x86)
                (equal len-wc (len *wc*))
                (equal (get-char (offset x86) (input x86)) *space*))
           (program-at (create-canonical-address-list len-wc addr)
                       *wc*
                       (x86-run (gc-clk-space) x86)))
  :hints (("Goal" :in-theory (e/d*
                              (effects-eof-not-encountered-prelim-programmer-level-mode-projection
                               effects-eof-not-encountered-prelim-program-projection
                               effects-eof-not-encountered-prelim-x86p-projection
                               loop-preconditions-weird-rbp-rsp)
                              ()))))

(defthmd effects-space-encountered-env-assumptions-projection
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (equal (get-char (offset x86) (input x86)) *space*))
           (env-assumptions (x86-run (gc-clk-space) x86)))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (e/d*
                       (effects-eof-not-encountered-prelim-env-assumptions-projection
                        effects-eof-not-encountered-prelim-programmer-level-mode-projection
                        effects-eof-not-encountered-prelim-x86p-projection)
                       ()))
          ("Goal''" :in-theory (e/d* (env-assumptions eof-terminatedp) ())
           :use ((:instance
                  loop-preconditions-fwd-chaining-essentials)))))

(defthmd effects-space-encountered-programmer-level-mode-projection
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (equal (get-char (offset x86) (input x86)) *space*))
           (equal (xr :programmer-level-mode 0 (x86-run (gc-clk-space) x86))
                  (xr :programmer-level-mode 0 x86))))

(defthmd effects-space-encountered-alignment-checking-enabled-p-projection
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (equal (get-char (offset x86) (input x86)) *space*))
           (equal (alignment-checking-enabled-p (x86-run (gc-clk-space) x86))
                  (alignment-checking-enabled-p x86))))

(defthmd effects-space-encountered-os-info-projection
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (equal (get-char (offset x86) (input x86)) *space*))
           (equal (xr :os-info 0 (x86-run (gc-clk-space) x86))
                  (xr :os-info 0 x86))))

(defthm loop-preconditions-space-encountered
  (implies (and (loop-preconditions addr x86)
                (equal (get-char (offset x86) (input x86)) *space*))
           (loop-preconditions addr (x86-run (gc-clk-space) x86)))
  :hints (("Goal" :in-theory '(effects-space-encountered-rbp-projection
                               effects-space-encountered-rsp-projection
                               x86p-effects-space-encountered
                               effects-space-encountered-msri-projection
                               effects-space-encountered-rip-projection
                               effects-space-encountered-ms-projection
                               effects-space-encountered-fault-projection
                               effects-space-encountered-env-assumptions-projection
                               (len)
                               loop-preconditions-fwd-chaining-essentials
                               effects-space-encountered-alignment-checking-enabled-p-projection
                               loop-preconditions-forward-chain-addresses-info
                               effects-space-encountered-programmer-level-mode-projection
                               effects-space-encountered-os-info-projection
                               effects-space-encountered-program-projection)
           :expand (loop-preconditions addr (x86-run (gc-clk-space) x86)))))

(defthmd effects-space-encountered-input-projection
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (equal (get-char (offset x86) (input x86)) *space*))
           (equal (input (x86-run (gc-clk-space) x86))
                  (input x86))))

(defthmd effects-space-encountered-offset-projection
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (equal (get-char (offset x86) (input x86)) *space*))
           (equal (offset (x86-run (gc-clk-space) x86))
                  (+ 1 (offset x86)))))

;;----------------------------------------------------------------------
;; Space Encountered: Delta Variable Theorems:
;;----------------------------------------------------------------------

(defthmd effects-space-encountered-variables-state
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (equal (get-char (offset x86) (input x86)) *space*))
           (equal (combine-bytes (word-state x86 (x86-run (gc-clk-space) x86)))
                  *out*)))

(defthmd effects-space-encountered-variables-state-in-terms-of-next-x86
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (equal (get-char (offset x86) (input x86)) *space*))
           (equal (word-state (x86-run (gc-clk-space) x86) xxx)
                  (word-state x86 xxx)))
  :hints (("Goal" :in-theory '(effects-space-encountered-rbp-projection
                               word-state))))

(defthmd effects-space-encountered-variables-nc
  (implies (and (loop-preconditions addr x86)
                (equal (get-char (offset x86) (input x86)) *space*))
           (equal (combine-bytes (nc x86 (x86-run (gc-clk-space) x86)))
                  (loghead 32 (+ 1 (combine-bytes (nc x86 x86))))))
  :hints (("Goal" :in-theory (e/d*
                              (programmer-level-mode-permissions-dont-matter)
                              (force (force))))))

(defthmd effects-space-encountered-variables-nc-in-terms-of-next-x86
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (equal (get-char (offset x86) (input x86)) *space*))
           (equal (nc (x86-run (gc-clk-space) x86) xxx)
                  (nc x86 xxx)))
  :hints (("Goal" :in-theory '(effects-space-encountered-rbp-projection
                               nc))))

(defthmd effects-space-encountered-variables-nw
  (implies (and (loop-preconditions addr x86)
                (equal (get-char (offset x86) (input x86)) *space*))
           (equal (nw x86 (x86-run (gc-clk-space) x86))
                  (nw x86 x86))))

(defthmd effects-space-encountered-variables-nw-in-terms-of-next-x86
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (equal (get-char (offset x86) (input x86)) *space*))
           (equal (nw (x86-run (gc-clk-space) x86) xxx)
                  (nw x86 xxx)))
  :hints (("Goal" :in-theory '(effects-space-encountered-rbp-projection
                               nw))))

(defthmd effects-space-encountered-variables-nl
  (implies (and (loop-preconditions addr x86)
                (equal (get-char (offset x86) (input x86)) *space*))
           (equal (nl x86 (x86-run (gc-clk-space) x86))
                  (nl x86 x86))))

(defthmd effects-space-encountered-variables-nl-in-terms-of-next-x86
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (equal (get-char (offset x86) (input x86)) *space*))
           (equal (nl (x86-run (gc-clk-space) x86) xxx)
                  (nl x86 xxx)))
  :hints (("Goal" :in-theory '(effects-space-encountered-rbp-projection
                               nl))))

;;**********************************************************************
;; Tab Encountered
;;**********************************************************************

(defthmd effects-tab-encountered-limited

  ;;  callq <gc>
  ;;
  ;;  addl $0x1,-0x10(%rbp)
  ;;  callq <gc>

  (implies
   (and (x86p x86-new)
        (xr :programmer-level-mode 0 x86-new)
        (not (alignment-checking-enabled-p x86-new))
        (env-assumptions x86-new)
        (canonical-address-p (xr :rgf *rsp* x86-new))

        ;; Points to the "addl $0x1,-0xc(%rbp)" instruction in main
        (equal addr (- (xr :rip 0 x86-new) (+ 37 (1- (len *gc*)))))

        (canonical-address-p addr)
        (canonical-address-p (+ (1- (len *wc*)) addr))
        (canonical-address-p (+ #x20 (xr :rgf *rsp* x86-new)))
        (canonical-address-p (+ (- (+ 8 #x20 8)) (xr :rgf *rsp* x86-new)))
        ;; (+ 8 #x20 8 #x20) = 80
        (disjoint-p
         ;; IMPORTANT: Keep the program addresses as the first
         ;; argument.
         (create-canonical-address-list
          (len *wc*) addr)
         (create-canonical-address-list
          80 (+ (- (+ 8 #x20 8)) (xr :rgf *rsp* x86-new))))


        ;; IMPORTANT: Why doesn't the following hyp work?
        ;; (equal (xr :rgf *rbp* x86-new) (- (+ (xr :rgf *rsp* x86-new) 40) 8))
        (canonical-address-p (xr :rgf *rbp* x86-new))
        (equal (xr :rgf *rsp* x86-new)
               (- (xr :rgf *rbp* x86-new) 32))
        (equal (xr :ms 0 x86-new) nil)
        (equal (xr :fault 0 x86-new) nil)
        ;; Enabling the SYSCALL instruction.
        (equal (ia32_efer-slice :ia32_efer-sce (xr :msr *ia32_efer-idx* x86-new)) 1)
        (equal (ia32_efer-slice :ia32_efer-lma (xr :msr *ia32_efer-idx* x86-new)) 1)
        (program-at (create-canonical-address-list
                     (len *wc*) addr) *wc* x86-new)

        (equal (mv-nth 1 (rb (create-canonical-address-list 4 (+ -4 (xr :rgf *rbp* x86-new))) :x x86-new))
               (byte-ify 4 *tab*)))
   (equal (x86-run 11 x86-new)
          (XW
           :RIP 0 (+ 58 (XR :RIP 0 X86-NEW))
           (MV-NTH
            1
            (WB
             (APPEND
              (CREATE-ADDR-BYTES-ALIST
               (CREATE-CANONICAL-ADDRESS-LIST 4 (+ 20 (XR :RGF *RSP* X86-NEW)))
               (BYTE-IFY
                4
                (LOGHEAD
                 32
                 (+
                  1
                  (COMBINE-BYTES
                   (MV-NTH
                    1
                    (RB
                     (CREATE-CANONICAL-ADDRESS-LIST 4 (+ 20 (XR :RGF *RSP* X86-NEW)))
                     :X X86-NEW)))))))
              (CREATE-ADDR-BYTES-ALIST
               (CREATE-CANONICAL-ADDRESS-LIST 4 (+ 24 (XR :RGF *RSP* X86-NEW)))
               '(0 0 0 0)))
             (!FLGI *CF* 0
                    (!FLGI *PF* 1
                           (!FLGI *AF* 0
                                  (!FLGI *ZF* 1
                                         (!FLGI *SF* 0 (!FLGI *OF* 0 X86-NEW)))))))))))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (e/d* (top-level-opcode-execute
                             instruction-decoding-and-spec-rules

                             gpr-sub-spec-4
                             gpr-add-spec-4
                             jcc/cmovcc/setcc-spec

                             write-user-rflags
                             !rgfi-size
                             x86-operand-to-reg/mem
                             wr64
                             wr32
                             rr08
                             rr32
                             rr64
                             x86-operand-from-modr/m-and-sib-bytes
                             write-canonical-address-to-memory
                             rim-size
                             rim08
                             rim32
                             rm32
                             wm-size
                             wm32
                             wm64
                             two-byte-opcode-decode-and-execute
                             x86-effective-addr
                             x86-run-plus-1)
                            (x86-run-plus)))))

(defthmd effects-tab-encountered-1

  ;;  callq <gc>
  ;;
  ;;  addl $0x1,-0x10(%rbp)
  ;;  callq <gc>

  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (equal (get-char (offset x86) (input x86)) *tab*)
                (equal x86-new (x86-run (gc-clk-no-eof) x86)))
           (equal (x86-run 11 x86-new)
                  (XW
                   :RIP 0 (+ 58 (XR :RIP 0 X86-NEW))
                   (MV-NTH
                    1
                    (WB
                     (APPEND
                      (CREATE-ADDR-BYTES-ALIST
                       (CREATE-CANONICAL-ADDRESS-LIST 4 (+ 20 (XR :RGF *RSP* X86-NEW)))
                       (BYTE-IFY
                        4
                        (LOGHEAD
                         32
                         (+
                          1
                          (COMBINE-BYTES
                           (MV-NTH
                            1
                            (RB
                             (CREATE-CANONICAL-ADDRESS-LIST 4 (+ 20 (XR :RGF *RSP* X86-NEW)))
                             :X X86-NEW)))))))
                      (CREATE-ADDR-BYTES-ALIST
                       (CREATE-CANONICAL-ADDRESS-LIST 4 (+ 24 (XR :RGF *RSP* X86-NEW)))
                       '(0 0 0 0)))
                     (!FLGI *CF* 0
                            (!FLGI *PF* 1
                                   (!FLGI *AF* 0
                                          (!FLGI *ZF* 1
                                                 (!FLGI *SF* 0 (!FLGI *OF* 0 X86-NEW)))))))))))
  :hints (("Goal" :in-theory
           (union-theories '(loop-preconditions
                             input
                             get-char
                             offset
                             rgfi-is-i64p
                             (len) (loghead)
                             programmer-level-mode-permissions-dont-matter)
                           (theory 'minimal-theory))
           :use ((:instance effects-eof-not-encountered-prelim-for-composition
                            (x86 x86))
                 (:instance
                  effects-eof-not-encountered-prelim-env-assumptions-projection
                  (x86 x86))
                 (:instance
                  effects-eof-not-encountered-prelim-rbp-projection
                  (x86 x86))
                 (:instance effects-tab-encountered-limited
                            (x86-new (x86-run (gc-clk-no-eof) x86)))))))

(defthm effects-tab-encountered

  ;;  callq <gc>
  ;;
  ;;  addl $0x1,-0x10(%rbp)
  ;;  callq <gc>

  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (equal (get-char (offset x86) (input x86)) *tab*))
           (equal (x86-run (gc-clk-tab) x86)
                  (XW
                   :RIP 0 (+ 58 (XR :RIP 0 (X86-RUN (GC-CLK-NO-EOF) X86)))
                   (MV-NTH
                    1
                    (WB
                     (APPEND
                      (CREATE-ADDR-BYTES-ALIST
                       (CREATE-CANONICAL-ADDRESS-LIST
                        4 (+ 20 (XR :RGF *RSP* (X86-RUN (GC-CLK-NO-EOF) X86))))
                       (BYTE-IFY
                        4
                        (LOGHEAD
                         32
                         (+
                          1
                          (COMBINE-BYTES
                           (MV-NTH
                            1
                            (RB
                             (CREATE-CANONICAL-ADDRESS-LIST
                              4 (+ 20 (XR :RGF *RSP* (X86-RUN (GC-CLK-NO-EOF) X86))))
                             :X (X86-RUN (GC-CLK-NO-EOF) X86))))))))
                      (CREATE-ADDR-BYTES-ALIST
                       (CREATE-CANONICAL-ADDRESS-LIST
                        4 (+ 24 (XR :RGF *RSP* (X86-RUN (GC-CLK-NO-EOF) X86))))
                       '(0 0 0 0)))
                     (!FLGI *CF* 0
                            (!FLGI *PF* 1
                                   (!FLGI *AF* 0
                                          (!FLGI *ZF* 1
                                                 (!FLGI *SF* 0
                                                        (!FLGI *OF* 0 (X86-RUN (GC-CLK-NO-EOF) X86))))))))))))
  :hints (("Goal" :do-not '(preprocess)
           :expand (gc-clk-tab)
           :in-theory (union-theories
                       '(gc-clk-tab
                         loop-preconditions
                         input
                         get-char
                         offset
                         dumb-run-plus-thm)
                       (theory 'minimal-theory))
           :use ((:instance effects-tab-encountered-1
                            (x86-new (x86-run (gc-clk-no-eof)
                                              x86)))))))

;;----------------------------------------------------------------------
;; Tab Encountered: Projection Theorems:
;;----------------------------------------------------------------------

(defthmd effects-tab-encountered-rbp-projection
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (equal (get-char (offset x86) (input x86)) *tab*))
           (equal (xr :rgf *rbp* (x86-run (gc-clk-tab) x86))
                  (xr :rgf *rbp* x86))))

(defthmd effects-tab-encountered-rsp-projection
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (equal (get-char (offset x86) (input x86)) *tab*))
           (equal (xr :rgf *rsp* (x86-run (gc-clk-tab) x86))
                  (xr :rgf *rsp* x86))))

(defthmd x86p-effects-tab-encountered
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (equal (get-char (offset x86) (input x86)) *tab*))
           (x86p (x86-run (gc-clk-tab) x86)))
  :hints (("Goal" :in-theory (e/d* (loop-preconditions) ()))))

(defthmd effects-tab-encountered-msri-projection
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (equal (get-char (offset x86) (input x86)) *tab*))
           (and (equal (ia32_efer-slice :ia32_efer-sce (xr :msr *ia32_efer-idx* (x86-run (gc-clk-tab) x86))) 1)
                (equal (ia32_efer-slice :ia32_efer-lma (xr :msr *ia32_efer-idx* (x86-run (gc-clk-tab) x86))) 1)))
  :hints (("Goal" :use ((:instance loop-preconditions-fwd-chaining-essentials)))))

(defthmd effects-tab-encountered-rip-projection
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (equal (get-char (offset x86) (input x86)) *tab*))
           (equal (xr :rip 0 (x86-run (gc-clk-tab) x86)) (+ 145 addr))))

(defthmd effects-tab-encountered-ms-projection
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (equal (get-char (offset x86) (input x86)) *tab*))
           (equal (xr :ms 0 (x86-run (gc-clk-tab) x86)) nil)))

(defthmd effects-tab-encountered-fault-projection
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (equal (get-char (offset x86) (input x86)) *tab*))
           (equal (xr :fault 0 (x86-run (gc-clk-tab) x86)) nil)))

(defthmd effects-tab-encountered-program-projection
  (implies (and (loop-preconditions addr x86)
                (equal len-wc (len *wc*))
                (equal (get-char (offset x86) (input x86)) *tab*))
           (program-at (create-canonical-address-list
                        len-wc addr)
                       *wc*
                       (x86-run (gc-clk-tab) x86)))
  :hints (("Goal" :in-theory (e/d*
                              (effects-eof-not-encountered-prelim-programmer-level-mode-projection
                               effects-eof-not-encountered-prelim-program-projection
                               effects-eof-not-encountered-prelim-x86p-projection
                               loop-preconditions-weird-rbp-rsp)
                              ()))))

(defthmd effects-tab-encountered-env-assumptions-projection
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (equal (get-char (offset x86) (input x86)) *tab*))
           (env-assumptions (x86-run (gc-clk-tab) x86)))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (e/d*
                       (effects-eof-not-encountered-prelim-env-assumptions-projection
                        effects-eof-not-encountered-prelim-programmer-level-mode-projection
                        effects-eof-not-encountered-prelim-x86p-projection)
                       ()))
          ("Goal''" :in-theory (e/d* (env-assumptions eof-terminatedp) ())
           :use ((:instance
                  loop-preconditions-fwd-chaining-essentials)))))

(defthmd effects-tab-encountered-programmer-level-mode-projection
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (equal (get-char (offset x86) (input x86)) *tab*))
           (equal (xr :programmer-level-mode 0 (x86-run (gc-clk-tab) x86))
                  (xr :programmer-level-mode 0 x86))))

(defthmd effects-tab-encountered-alignment-checking-enabled-p-projection
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (equal (get-char (offset x86) (input x86)) *tab*))
           (equal (alignment-checking-enabled-p (x86-run (gc-clk-tab) x86))
                  (alignment-checking-enabled-p x86))))

(defthmd effects-tab-encountered-os-info-projection
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (equal (get-char (offset x86) (input x86)) *tab*))
           (equal (xr :os-info 0 (x86-run (gc-clk-tab) x86))
                  (xr :os-info 0 x86))))

(defthm loop-preconditions-tab-encountered
  (implies (and (loop-preconditions addr x86)
                (equal (get-char (offset x86) (input x86)) *tab*))
           (loop-preconditions addr (x86-run (gc-clk-tab) x86)))
  :hints (("Goal" :in-theory '(effects-tab-encountered-rbp-projection
                               effects-tab-encountered-alignment-checking-enabled-p-projection
                               effects-tab-encountered-rsp-projection
                               x86p-effects-tab-encountered
                               effects-tab-encountered-msri-projection
                               effects-tab-encountered-rip-projection
                               effects-tab-encountered-ms-projection
                               effects-tab-encountered-fault-projection
                               effects-tab-encountered-env-assumptions-projection
                               (len)
                               loop-preconditions-fwd-chaining-essentials
                               loop-preconditions-forward-chain-addresses-info
                               effects-tab-encountered-programmer-level-mode-projection
                               effects-tab-encountered-os-info-projection
                               effects-tab-encountered-program-projection)
           :expand (loop-preconditions addr (x86-run (gc-clk-tab) x86)))))

(defthmd effects-tab-encountered-input-projection
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (equal (get-char (offset x86) (input x86)) *tab*))
           (equal (input (x86-run (gc-clk-tab) x86))
                  (input x86))))

(defthmd effects-tab-encountered-offset-projection
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (equal (get-char (offset x86) (input x86)) *tab*))
           (equal (offset (x86-run (gc-clk-tab) x86))
                  (+ 1 (offset x86)))))

;;----------------------------------------------------------------------
;; Tab Encountered: Delta Variable Theorems:
;;----------------------------------------------------------------------

(defthmd effects-tab-encountered-variables-state
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (equal (get-char (offset x86) (input x86)) *tab*))
           (equal (combine-bytes (word-state x86 (x86-run (gc-clk-tab) x86)))
                  *out*)))

(defthmd effects-tab-encountered-variables-state-in-terms-of-next-x86
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (equal (get-char (offset x86) (input x86)) *tab*))
           (equal (word-state (x86-run (gc-clk-tab) x86) xxx)
                  (word-state x86 xxx)))
  :hints (("Goal" :in-theory '(effects-tab-encountered-rbp-projection
                               word-state))))

(defthmd effects-tab-encountered-variables-nc
  (implies (and (loop-preconditions addr x86)
                (equal (get-char (offset x86) (input x86)) *tab*))
           (equal (combine-bytes (nc x86 (x86-run (gc-clk-tab) x86)))
                  (loghead 32 (+ 1 (combine-bytes (nc x86 x86))))))
  :hints (("Goal" :in-theory (e/d*
                              (programmer-level-mode-permissions-dont-matter)
                              (force (force))))))

(defthmd effects-tab-encountered-variables-nc-in-terms-of-next-x86
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (equal (get-char (offset x86) (input x86)) *tab*))
           (equal (nc (x86-run (gc-clk-tab) x86) xxx)
                  (nc x86 xxx)))
  :hints (("Goal" :in-theory '(effects-tab-encountered-rbp-projection
                               nc))))

(defthmd effects-tab-encountered-variables-nw
  (implies (and (loop-preconditions addr x86)
                (equal (get-char (offset x86) (input x86)) *tab*))
           (equal (nw x86 (x86-run (gc-clk-tab) x86))
                  (nw x86 x86))))

(defthmd effects-tab-encountered-variables-nw-in-terms-of-next-x86
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (equal (get-char (offset x86) (input x86)) *tab*))
           (equal (nw (x86-run (gc-clk-tab) x86) xxx)
                  (nw x86 xxx)))
  :hints (("Goal" :in-theory '(effects-tab-encountered-rbp-projection
                               nw))))

(defthmd effects-tab-encountered-variables-nl
  (implies (and (loop-preconditions addr x86)
                (equal (get-char (offset x86) (input x86)) *tab*))
           (equal (nl x86 (x86-run (gc-clk-tab) x86))
                  (nl x86 x86))))

(defthmd effects-tab-encountered-variables-nl-in-terms-of-next-x86
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (equal (get-char (offset x86) (input x86)) *tab*))
           (equal (nl (x86-run (gc-clk-tab) x86) xxx)
                  (nl x86 xxx)))
  :hints (("Goal" :in-theory '(effects-tab-encountered-rbp-projection
                               nl))))

;;**********************************************************************
;; Other Char Encountered: (State = Out)
;;**********************************************************************

(encapsulate
 ()

 (local (include-book "arithmetic-5/top" :dir :system))

 (defthm effects-newline-not-encountered-helper-1
   (implies (and (not (equal char *newline*)) ;; 10
                 (unsigned-byte-p 8 char))
            (equal (equal (loghead 32 (+ -10 (logext 32 char))) 0) nil))
   :hints (("Goal" :in-theory (e/d* (loghead) ()))))

 (defthm effects-newline-not-encountered-helper-2
   (implies (and (not (equal char *newline*)) ;; 10
                 (unsigned-byte-p 32 char))
            (equal (equal (loghead 32 (+ -10 char)) 0) nil))
   :hints (("Goal" :in-theory (e/d* (loghead) ()))))

 (defthm effects-space-not-encountered-helper-1
   (implies (and (not (equal char *space*)) ;; 32
                 (unsigned-byte-p 8 char))
            (equal (equal (loghead 32 (+ -32 (logext 32 char))) 0) nil))
   :hints (("Goal" :in-theory (e/d* (loghead) ()))))

 (defthm effects-space-not-encountered-helper-2
   (implies (and (not (equal char *space*)) ;; 32
                 (unsigned-byte-p 32 char))
            (equal (equal (loghead 32 (+ -32 char)) 0) nil))
   :hints (("Goal" :in-theory (e/d* (loghead) ()))))

 (defthm effects-tab-not-encountered-helper-1
   (implies (and (not (equal char *tab*)) ;; 9
                 (unsigned-byte-p 8 char))
            (equal (equal (loghead 32 (+ -9 (logext 32 char))) 0) nil))
   :hints (("Goal" :in-theory (e/d* (loghead) ()))))

 (defthm effects-tab-not-encountered-helper-2
   (implies (and (not (equal char *tab*)) ;; 9
                 (unsigned-byte-p 32 char))
            (equal (equal (loghead 32 (+ -9 char)) 0) nil))
   :hints (("Goal" :in-theory (e/d* (loghead) ())))))

(defthmd effects-other-char-encountered-state-out-limited
  ;;  callq <gc>
  ;;
  ;;  addl $0x1,-0x10(%rbp)
  ;;  callq <gc>

  (implies
   (and (x86p x86-new)
        (xr :programmer-level-mode 0 x86-new)
        (not (alignment-checking-enabled-p x86-new))
        (env-assumptions x86-new)
        (canonical-address-p (xr :rgf *rsp* x86-new))

        ;; Points to the "addl $0x1,-0xc(%rbp)" instruction in main
        (equal addr (- (xr :rip 0 x86-new) (+ 37 (1- (len *gc*)))))

        (canonical-address-p addr)
        (canonical-address-p (+ (1- (len *wc*)) addr))
        (canonical-address-p (+ #x20 (xr :rgf *rsp* x86-new)))
        (canonical-address-p (+ (- (+ 8 #x20 8)) (xr :rgf *rsp* x86-new)))
        ;; (+ 8 #x20 8 #x20) = 80
        (disjoint-p
         ;; IMPORTANT: Keep the program addresses as the first
         ;; argument.
         (create-canonical-address-list
          (len *wc*) addr)
         (create-canonical-address-list
          80 (+ (- (+ 8 #x20 8)) (xr :rgf *rsp* x86-new))))


        ;; IMPORTANT: Why doesn't the following hyp work?
        ;; (equal (xr :rgf *rbp* x86-new) (- (+ (xr :rgf *rsp* x86-new) 40) 8))
        (canonical-address-p (xr :rgf *rbp* x86-new))
        (equal (xr :rgf *rsp* x86-new)
               (- (xr :rgf *rbp* x86-new) 32))
        (equal (xr :ms 0 x86-new) nil)
        (equal (xr :fault 0 x86-new) nil)
        ;; Enabling the SYSCALL instruction.
        (equal (ia32_efer-slice :ia32_efer-sce (xr :msr *ia32_efer-idx* x86-new)) 1)
        (equal (ia32_efer-slice :ia32_efer-lma (xr :msr *ia32_efer-idx* x86-new)) 1)
        (program-at (create-canonical-address-list (len *wc*) addr) *wc* x86-new)

        ;; Other theorems say the following in terms of byte-ify, not combine-bytes...
        ;; (not (equal (mv-nth 1 (rb (create-canonical-address-list 4 (+ -4 (xr :rgf *rbp* x86-new))) :x x86-new))
        ;;             (byte-ify 4 *eof*)))
        ;; (not (equal (mv-nth 1 (rb (create-canonical-address-list 4 (+ -4 (xr :rgf *rbp* x86-new))) :x x86-new))
        ;;             (byte-ify 4 *newline*)))
        ;; (not (equal (mv-nth 1 (rb (create-canonical-address-list 4 (+ -4 (xr :rgf *rbp* x86-new))) :x x86-new))
        ;;             (byte-ify 4 *space*)))
        ;; (not (equal (mv-nth 1 (rb (create-canonical-address-list 4 (+ -4 (xr :rgf *rbp* x86-new))) :x x86-new))
        ;;             (byte-ify 4 *tab*)))
        ;; (equal (mv-nth 1 (rb (create-canonical-address-list 4 (+ -8 (xr :rgf *rbp* x86-new))) :x x86-new))
        ;;        (byte-ify 4 *out*))

        (not (equal (combine-bytes
                     (mv-nth 1 (rb (create-canonical-address-list 4 (+ -4 (xr :rgf *rbp* x86-new))) :x x86-new)))
                    *eof*))
        (not (equal (combine-bytes
                     (mv-nth 1 (rb (create-canonical-address-list 4 (+ -4 (xr :rgf *rbp* x86-new))) :x x86-new)))
                    *newline*))
        (not (equal (combine-bytes
                     (mv-nth 1 (rb (create-canonical-address-list 4 (+ -4 (xr :rgf *rbp* x86-new))) :x x86-new)))
                    *space*))
        (not (equal (combine-bytes
                     (mv-nth 1 (rb (create-canonical-address-list 4 (+ -4 (xr :rgf *rbp* x86-new))) :x x86-new)))
                    *tab*))
        (equal (combine-bytes
                (mv-nth 1 (rb (create-canonical-address-list 4 (+ -8 (xr :rgf *rbp* x86-new))) :x x86-new)))
               *out*)
        ;; Character read in is a byte.
        (unsigned-byte-p
         8
         (combine-bytes
          (mv-nth 1 (rb (create-canonical-address-list 4 (+ -4 (xr :rgf *rbp* x86-new))) :x x86-new)))))
   (equal (x86-run 13 x86-new)
          (XW
           :RIP 0 (+ 58 (XR :RIP 0 X86-NEW))
           (MV-NTH
            1
            (WB
             (APPEND
              (CREATE-ADDR-BYTES-ALIST
               (CREATE-CANONICAL-ADDRESS-LIST 4 (+ 20 (XR :RGF *RSP* X86-NEW)))
               (BYTE-IFY
                4
                (LOGHEAD
                 32
                 (+
                  1
                  (COMBINE-BYTES
                   (MV-NTH
                    1
                    (RB
                     (CREATE-CANONICAL-ADDRESS-LIST 4 (+ 20 (XR :RGF *RSP* X86-NEW)))
                     :X X86-NEW)))))))
              (CREATE-ADDR-BYTES-ALIST
               (CREATE-CANONICAL-ADDRESS-LIST 4 (+ 24 (XR :RGF *RSP* X86-NEW)))
               (BYTE-IFY 4 1))
              (CREATE-ADDR-BYTES-ALIST
               (CREATE-CANONICAL-ADDRESS-LIST 4 (+ 16 (XR :RGF *RSP* X86-NEW)))
               (BYTE-IFY
                4
                (LOGHEAD
                 32
                 (+
                  1
                  (COMBINE-BYTES
                   (MV-NTH
                    1
                    (RB
                     (CREATE-CANONICAL-ADDRESS-LIST 4 (+ 16 (XR :RGF *RSP* X86-NEW)))
                     :X X86-NEW))))))))
             (!FLGI
              *CF*
              (CF-SPEC32
               (+
                1
                (COMBINE-BYTES
                 (MV-NTH
                  1
                  (RB
                   (CREATE-CANONICAL-ADDRESS-LIST 4 (+ 16 (XR :RGF *RSP* X86-NEW)))
                   :X X86-NEW)))))
              (!FLGI
               *PF*
               (PF-SPEC32
                (LOGHEAD
                 32
                 (+
                  1
                  (COMBINE-BYTES
                   (MV-NTH
                    1
                    (RB
                     (CREATE-CANONICAL-ADDRESS-LIST 4 (+ 16 (XR :RGF *RSP* X86-NEW)))
                     :X X86-NEW))))))
               (!FLGI
                *AF*
                (ADD-AF-SPEC32
                 (COMBINE-BYTES
                  (MV-NTH
                   1
                   (RB
                    (CREATE-CANONICAL-ADDRESS-LIST 4 (+ 16 (XR :RGF *RSP* X86-NEW)))
                    :X X86-NEW)))
                 1)
                (!FLGI
                 *ZF*
                 (ZF-SPEC
                  (LOGHEAD
                   32
                   (+
                    1
                    (COMBINE-BYTES (MV-NTH 1
                                           (RB (CREATE-CANONICAL-ADDRESS-LIST
                                                4 (+ 16 (XR :RGF *RSP* X86-NEW)))
                                               :X X86-NEW))))))
                 (!FLGI
                  *SF*
                  (SF-SPEC32
                   (LOGHEAD
                    32
                    (+ 1
                       (COMBINE-BYTES
                        (MV-NTH 1
                                (RB (CREATE-CANONICAL-ADDRESS-LIST
                                     4 (+ 16 (XR :RGF *RSP* X86-NEW)))
                                    :X X86-NEW))))))
                  (!FLGI
                   *OF*
                   (OF-SPEC32
                    (+
                     1
                     (LOGEXT 32
                             (COMBINE-BYTES
                              (MV-NTH 1
                                      (RB (CREATE-CANONICAL-ADDRESS-LIST
                                           4 (+ 16 (XR :RGF *RSP* X86-NEW)))
                                          :X X86-NEW))))))
                   X86-NEW)))))))))))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (e/d* (top-level-opcode-execute
                             instruction-decoding-and-spec-rules

                             gpr-sub-spec-4
                             gpr-add-spec-4
                             jcc/cmovcc/setcc-spec

                             write-user-rflags
                             !rgfi-size
                             x86-operand-to-reg/mem
                             wr64
                             wr32
                             rr08
                             rr32
                             rr64
                             x86-operand-from-modr/m-and-sib-bytes
                             write-canonical-address-to-memory
                             rim-size
                             rim08
                             rim32
                             rm32
                             wm-size
                             wm32
                             wm64
                             two-byte-opcode-decode-and-execute
                             x86-effective-addr
                             x86-run-plus-1)
                            (x86-run-plus
                             byte-ify
                             (byte-ify))))))

(local
 (defthm combine-bytes-with-byte-ify-4-inequality-lemma
   (implies (and (not (equal (car (grab-bytes xs)) val))
                 (byte-listp xs)
                 (consp xs))
            (equal (equal (combine-bytes (byte-ify 4 (car (grab-bytes xs)))) val) nil))
   :hints (("Goal" :in-theory (e/d* (grab-bytes) ())))))

(defthmd effects-other-char-encountered-state-out-1

  ;;  callq <gc>
  ;;
  ;;  addl $0x1,-0x10(%rbp)
  ;;  callq <gc>

  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (not (equal (get-char (offset x86) (input x86)) *eof*))
                (not (equal (get-char (offset x86) (input x86)) *newline*))
                (not (equal (get-char (offset x86) (input x86)) *space*))
                (not (equal (get-char (offset x86) (input x86)) *tab*))
                ;; (equal (word-state x86-new x86-new) (byte-ify 4 *out*))
                (equal (combine-bytes (word-state x86-new x86-new)) *out*)
                (equal x86-new (x86-run (gc-clk-no-eof) x86)))
           (equal (x86-run 13 x86-new)
                  (XW
                   :RIP 0 (+ 58 (XR :RIP 0 (X86-RUN (GC-CLK-NO-EOF) X86)))
                   (MV-NTH
                    1
                    (WB
                     (APPEND
                      (CREATE-ADDR-BYTES-ALIST
                       (CREATE-CANONICAL-ADDRESS-LIST 4 (+ 20 (XR :RGF *RSP* (X86-RUN (GC-CLK-NO-EOF) X86))))
                       (BYTE-IFY
                        4
                        (LOGHEAD
                         32
                         (+
                          1
                          (COMBINE-BYTES
                           (MV-NTH
                            1
                            (RB
                             (CREATE-CANONICAL-ADDRESS-LIST 4 (+ 20 (XR :RGF *RSP* (X86-RUN (GC-CLK-NO-EOF) X86))))
                             :X (X86-RUN (GC-CLK-NO-EOF) X86))))))))
                      (CREATE-ADDR-BYTES-ALIST
                       (CREATE-CANONICAL-ADDRESS-LIST 4 (+ 24 (XR :RGF *RSP* (X86-RUN (GC-CLK-NO-EOF) X86))))
                       (BYTE-IFY 4 1))
                      (CREATE-ADDR-BYTES-ALIST
                       (CREATE-CANONICAL-ADDRESS-LIST 4 (+ 16 (XR :RGF *RSP* (X86-RUN (GC-CLK-NO-EOF) X86))))
                       (BYTE-IFY
                        4
                        (LOGHEAD
                         32
                         (+
                          1
                          (COMBINE-BYTES
                           (MV-NTH
                            1
                            (RB
                             (CREATE-CANONICAL-ADDRESS-LIST 4 (+ 16 (XR :RGF *RSP* (X86-RUN (GC-CLK-NO-EOF) X86))))
                             :X (X86-RUN (GC-CLK-NO-EOF) X86)))))))))
                     (!FLGI
                      *CF*
                      (CF-SPEC32
                       (+
                        1
                        (COMBINE-BYTES
                         (MV-NTH
                          1
                          (RB
                           (CREATE-CANONICAL-ADDRESS-LIST 4 (+ 16 (XR :RGF *RSP* (X86-RUN (GC-CLK-NO-EOF) X86))))
                           :X (X86-RUN (GC-CLK-NO-EOF) X86))))))
                      (!FLGI
                       *PF*
                       (PF-SPEC32
                        (LOGHEAD
                         32
                         (+
                          1
                          (COMBINE-BYTES
                           (MV-NTH
                            1
                            (RB
                             (CREATE-CANONICAL-ADDRESS-LIST 4 (+ 16 (XR :RGF *RSP* (X86-RUN (GC-CLK-NO-EOF) X86))))
                             :X (X86-RUN (GC-CLK-NO-EOF) X86)))))))
                       (!FLGI
                        *AF*
                        (ADD-AF-SPEC32
                         (COMBINE-BYTES
                          (MV-NTH
                           1
                           (RB
                            (CREATE-CANONICAL-ADDRESS-LIST 4 (+ 16 (XR :RGF *RSP* (X86-RUN (GC-CLK-NO-EOF) X86))))
                            :X (X86-RUN (GC-CLK-NO-EOF) X86))))
                         1)
                        (!FLGI
                         *ZF*
                         (ZF-SPEC
                          (LOGHEAD
                           32
                           (+
                            1
                            (COMBINE-BYTES (MV-NTH 1
                                                   (RB (CREATE-CANONICAL-ADDRESS-LIST
                                                        4 (+ 16 (XR :RGF *RSP* (X86-RUN (GC-CLK-NO-EOF) X86))))
                                                       :X (X86-RUN (GC-CLK-NO-EOF) X86)))))))
                         (!FLGI
                          *SF*
                          (SF-SPEC32
                           (LOGHEAD
                            32
                            (+ 1
                               (COMBINE-BYTES
                                (MV-NTH 1
                                        (RB (CREATE-CANONICAL-ADDRESS-LIST
                                             4 (+ 16 (XR :RGF *RSP* (X86-RUN (GC-CLK-NO-EOF) X86))))
                                            :X (X86-RUN (GC-CLK-NO-EOF) X86)))))))
                          (!FLGI
                           *OF*
                           (OF-SPEC32
                            (+
                             1
                             (LOGEXT 32
                                     (COMBINE-BYTES
                                      (MV-NTH 1
                                              (RB (CREATE-CANONICAL-ADDRESS-LIST
                                                   4 (+ 16 (XR :RGF *RSP* (X86-RUN (GC-CLK-NO-EOF) X86))))
                                                  :X (X86-RUN (GC-CLK-NO-EOF) X86)))))))
                           (X86-RUN (GC-CLK-NO-EOF) X86))))))))))))
  :hints (("Goal" :in-theory
           (union-theories '(loop-preconditions
                             input
                             get-char
                             offset
                             rgfi-is-i64p
                             (len) (loghead) (byte-ify)
                             (logior) (ash)
                             programmer-level-mode-permissions-dont-matter
                             combine-bytes
                             word-state
                             remove-loghead-from-byte-ify
                             combine-bytes-and-byte-ify-inequality-lemma
                             byte-listp-and-consp-of-take-from-environment-assumptions
                             combine-bytes-with-byte-ify-4-inequality-lemma)
                           (theory 'minimal-theory))
           :use ((:instance effects-eof-not-encountered-prelim-for-composition
                            (x86 x86))
                 (:instance effects-eof-not-encountered-prelim-gc-byte-projection-size
                            (x86 x86))
                 (:instance effects-eof-not-encountered-prelim-env-assumptions-projection
                            (x86 x86))
                 (:instance effects-eof-not-encountered-prelim-rbp-projection
                            (x86 x86))
                 (:instance effects-other-char-encountered-state-out-limited
                            (x86-new (x86-run (gc-clk-no-eof) x86)))))))

(defthm effects-other-char-encountered-state-out

  ;;  callq <gc>
  ;;
  ;;  addl $0x1,-0x10(%rbp)
  ;;  callq <gc>

  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (not (equal (get-char (offset x86) (input x86)) *eof*))
                (not (equal (get-char (offset x86) (input x86)) *newline*))
                (not (equal (get-char (offset x86) (input x86)) *space*))
                (not (equal (get-char (offset x86) (input x86)) *tab*))
                ;; (equal (word-state x86 x86) (byte-ify 4 *out*))
                (equal (combine-bytes (word-state x86 x86)) *out*))
           (equal (x86-run (gc-clk-otherwise-out) x86)
                  (XW
                   :RIP 0 (+ 58 (XR :RIP 0 (X86-RUN (GC-CLK-NO-EOF) X86)))
                   (MV-NTH
                    1
                    (WB
                     (APPEND
                      (CREATE-ADDR-BYTES-ALIST
                       (CREATE-CANONICAL-ADDRESS-LIST 4 (+ 20 (XR :RGF *RSP* (X86-RUN (GC-CLK-NO-EOF) X86))))
                       (BYTE-IFY
                        4
                        (LOGHEAD
                         32
                         (+
                          1
                          (COMBINE-BYTES
                           (MV-NTH
                            1
                            (RB
                             (CREATE-CANONICAL-ADDRESS-LIST 4 (+ 20 (XR :RGF *RSP* (X86-RUN (GC-CLK-NO-EOF) X86))))
                             :X (X86-RUN (GC-CLK-NO-EOF) X86))))))))
                      (CREATE-ADDR-BYTES-ALIST
                       (CREATE-CANONICAL-ADDRESS-LIST 4 (+ 24 (XR :RGF *RSP* (X86-RUN (GC-CLK-NO-EOF) X86))))
                       (BYTE-IFY 4 1))
                      (CREATE-ADDR-BYTES-ALIST
                       (CREATE-CANONICAL-ADDRESS-LIST 4 (+ 16 (XR :RGF *RSP* (X86-RUN (GC-CLK-NO-EOF) X86))))
                       (BYTE-IFY
                        4
                        (LOGHEAD
                         32
                         (+
                          1
                          (COMBINE-BYTES
                           (MV-NTH
                            1
                            (RB
                             (CREATE-CANONICAL-ADDRESS-LIST 4 (+ 16 (XR :RGF *RSP* (X86-RUN (GC-CLK-NO-EOF) X86))))
                             :X (X86-RUN (GC-CLK-NO-EOF) X86)))))))))
                     (!FLGI
                      *CF*
                      (CF-SPEC32
                       (+
                        1
                        (COMBINE-BYTES
                         (MV-NTH
                          1
                          (RB
                           (CREATE-CANONICAL-ADDRESS-LIST 4 (+ 16 (XR :RGF *RSP* (X86-RUN (GC-CLK-NO-EOF) X86))))
                           :X (X86-RUN (GC-CLK-NO-EOF) X86))))))
                      (!FLGI
                       *PF*
                       (PF-SPEC32
                        (LOGHEAD
                         32
                         (+
                          1
                          (COMBINE-BYTES
                           (MV-NTH
                            1
                            (RB
                             (CREATE-CANONICAL-ADDRESS-LIST 4 (+ 16 (XR :RGF *RSP* (X86-RUN (GC-CLK-NO-EOF) X86))))
                             :X (X86-RUN (GC-CLK-NO-EOF) X86)))))))
                       (!FLGI
                        *AF*
                        (ADD-AF-SPEC32
                         (COMBINE-BYTES
                          (MV-NTH
                           1
                           (RB
                            (CREATE-CANONICAL-ADDRESS-LIST 4 (+ 16 (XR :RGF *RSP* (X86-RUN (GC-CLK-NO-EOF) X86))))
                            :X (X86-RUN (GC-CLK-NO-EOF) X86))))
                         1)
                        (!FLGI
                         *ZF*
                         (ZF-SPEC
                          (LOGHEAD
                           32
                           (+
                            1
                            (COMBINE-BYTES (MV-NTH 1
                                                   (RB (CREATE-CANONICAL-ADDRESS-LIST
                                                        4 (+ 16 (XR :RGF *RSP* (X86-RUN (GC-CLK-NO-EOF) X86))))
                                                       :X (X86-RUN (GC-CLK-NO-EOF) X86)))))))
                         (!FLGI
                          *SF*
                          (SF-SPEC32
                           (LOGHEAD
                            32
                            (+ 1
                               (COMBINE-BYTES
                                (MV-NTH 1
                                        (RB (CREATE-CANONICAL-ADDRESS-LIST
                                             4 (+ 16 (XR :RGF *RSP* (X86-RUN (GC-CLK-NO-EOF) X86))))
                                            :X (X86-RUN (GC-CLK-NO-EOF) X86)))))))
                          (!FLGI
                           *OF*
                           (OF-SPEC32
                            (+
                             1
                             (LOGEXT 32
                                     (COMBINE-BYTES
                                      (MV-NTH 1
                                              (RB (CREATE-CANONICAL-ADDRESS-LIST
                                                   4 (+ 16 (XR :RGF *RSP* (X86-RUN (GC-CLK-NO-EOF) X86))))
                                                  :X (X86-RUN (GC-CLK-NO-EOF) X86)))))))
                           (X86-RUN (GC-CLK-NO-EOF) X86))))))))))))
  :hints (("Goal"
           :in-theory (union-theories
                       '(programmer-level-mode-permissions-dont-matter
                         word-state
                         gc-clk-otherwise-out
                         dumb-run-plus-thm
                         (byte-ify)
                         remove-loghead-from-byte-ify
                         combine-bytes-and-byte-ify-inequality-lemma
                         byte-listp-and-consp-of-take-from-environment-assumptions
                         combine-bytes-with-byte-ify-4-inequality-lemma
                         (:forward-chaining loop-preconditions-fwd-chaining-essentials)
                         (:forward-chaining loop-preconditions-forward-chain-addresses-info))
                       (theory 'minimal-theory))
           :use ((:instance effects-other-char-encountered-state-out-1
                            (x86-new (x86-run (gc-clk-no-eof) x86)))
                 (:instance loop-preconditions-weird-rbp-rsp)
                 (:instance loop-preconditions-fwd-chaining-essentials)
                 (:instance effects-eof-not-encountered-prelim-word-state-projection)
                 (:instance effects-eof-not-encountered-prelim-rbp-projection)))))

;;----------------------------------------------------------------------
;; Other Char Encountered (State = OUT): Projection Theorems:
;;----------------------------------------------------------------------

(defthmd effects-other-char-encountered-state-out-rbp-projection
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (not (equal (get-char (offset x86) (input x86)) *eof*))
                (not (equal (get-char (offset x86) (input x86)) *newline*))
                (not (equal (get-char (offset x86) (input x86)) *space*))
                (not (equal (get-char (offset x86) (input x86)) *tab*))
                (equal (combine-bytes (word-state x86 x86)) *out*))
           (equal (xr :rgf *rbp* (x86-run (gc-clk-otherwise-out) x86))
                  (xr :rgf *rbp* x86)))
  :hints (("Goal" :in-theory (e/d* ()
                                   (word-state
                                    loop-preconditions-forward-chain-addresses-info)))))

(defthmd effects-other-char-encountered-state-out-rsp-projection
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (not (equal (get-char (offset x86) (input x86)) *eof*))
                (not (equal (get-char (offset x86) (input x86)) *newline*))
                (not (equal (get-char (offset x86) (input x86)) *space*))
                (not (equal (get-char (offset x86) (input x86)) *tab*))
                (equal (combine-bytes (word-state x86 x86)) *out*))
           (equal (xr :rgf *rsp* (x86-run (gc-clk-otherwise-out) x86))
                  (xr :rgf *rsp* x86)))
  :hints (("Goal" :in-theory (e/d* ()
                                  (word-state
                                   loop-preconditions-forward-chain-addresses-info)))))

(defthmd x86p-effects-other-char-encountered-state-out
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (not (equal (get-char (offset x86) (input x86)) *eof*))
                (not (equal (get-char (offset x86) (input x86)) *newline*))
                (not (equal (get-char (offset x86) (input x86)) *space*))
                (not (equal (get-char (offset x86) (input x86)) *tab*))
                (equal (combine-bytes (word-state x86 x86)) *out*))
           (x86p (x86-run (gc-clk-otherwise-out) x86)))
  :hints (("Goal" :in-theory (e/d* (loop-preconditions)
                                   (word-state
                                    loop-preconditions-forward-chain-addresses-info)))))

(defthmd effects-other-char-encountered-state-out-msri-projection
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (not (equal (get-char (offset x86) (input x86)) *eof*))
                (not (equal (get-char (offset x86) (input x86)) *newline*))
                (not (equal (get-char (offset x86) (input x86)) *space*))
                (not (equal (get-char (offset x86) (input x86)) *tab*))
                (equal (combine-bytes (word-state x86 x86)) *out*))
           (and (equal (ia32_efer-slice :ia32_efer-sce
                                        (xr :msr *ia32_efer-idx* (x86-run (gc-clk-otherwise-out) x86))) 1)
                (equal (ia32_efer-slice :ia32_efer-lma
                                        (xr :msr *ia32_efer-idx* (x86-run (gc-clk-otherwise-out) x86))) 1)))
  :hints (("Goal"
           :in-theory (e/d* () (word-state combine-bytes))
           :use ((:instance loop-preconditions-fwd-chaining-essentials)))))

(defthmd effects-other-char-encountered-state-out-rip-projection
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (not (equal (get-char (offset x86) (input x86)) *eof*))
                (not (equal (get-char (offset x86) (input x86)) *newline*))
                (not (equal (get-char (offset x86) (input x86)) *space*))
                (not (equal (get-char (offset x86) (input x86)) *tab*))
                (equal (combine-bytes (word-state x86 x86)) *out*))
           (equal (xr :rip 0 (x86-run (gc-clk-otherwise-out) x86)) (+ 145 addr)))
  :hints (("Goal" :in-theory (e/d* () (word-state subset-p)))))

(defthmd effects-other-char-encountered-state-out-ms-projection
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (not (equal (get-char (offset x86) (input x86)) *eof*))
                (not (equal (get-char (offset x86) (input x86)) *newline*))
                (not (equal (get-char (offset x86) (input x86)) *space*))
                (not (equal (get-char (offset x86) (input x86)) *tab*))
                (equal (combine-bytes (word-state x86 x86)) *out*))
           (equal (xr :ms 0 (x86-run (gc-clk-otherwise-out) x86)) nil))
  :hints (("Goal" :in-theory (e/d* ()
                                  (word-state
                                   subset-p
                                   loop-preconditions-forward-chain-addresses-info)))))

(defthmd effects-other-char-encountered-state-out-fault-projection
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (not (equal (get-char (offset x86) (input x86)) *eof*))
                (not (equal (get-char (offset x86) (input x86)) *newline*))
                (not (equal (get-char (offset x86) (input x86)) *space*))
                (not (equal (get-char (offset x86) (input x86)) *tab*))
                (equal (combine-bytes (word-state x86 x86)) *out*))
           (equal (xr :fault 0 (x86-run (gc-clk-otherwise-out) x86)) nil))
  :hints (("Goal" :in-theory (e/d* () (word-state subset-p)))))

(defthmd effects-other-char-encountered-state-out-program-projection
  (implies (and (loop-preconditions addr x86)
                (not (equal (get-char (offset x86) (input x86)) *eof*))
                (not (equal (get-char (offset x86) (input x86)) *newline*))
                (not (equal (get-char (offset x86) (input x86)) *space*))
                (not (equal (get-char (offset x86) (input x86)) *tab*))
                (equal (combine-bytes (word-state x86 x86)) *out*)
                (equal len-wc (len *wc*)))
           (program-at (create-canonical-address-list len-wc addr)
                       *wc* (x86-run (gc-clk-otherwise-out) x86)))
  :hints (("Goal" :in-theory (e/d*
                              (effects-eof-not-encountered-prelim-programmer-level-mode-projection
                               effects-eof-not-encountered-prelim-program-projection
                               effects-eof-not-encountered-prelim-x86p-projection
                               loop-preconditions-weird-rbp-rsp)
                              (word-state))
           :use ((:instance loop-preconditions-fwd-chaining-essentials)))))

(defthmd effects-other-char-encountered-state-out-env-assumptions-projection
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (not (equal (get-char (offset x86) (input x86)) *eof*))
                (not (equal (get-char (offset x86) (input x86)) *newline*))
                (not (equal (get-char (offset x86) (input x86)) *space*))
                (not (equal (get-char (offset x86) (input x86)) *tab*))
                (equal (combine-bytes (word-state x86 x86)) *out*))
           (env-assumptions (x86-run (gc-clk-otherwise-out) x86)))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (e/d*
                       (effects-eof-not-encountered-prelim-env-assumptions-projection
                        effects-eof-not-encountered-prelim-programmer-level-mode-projection
                        effects-eof-not-encountered-prelim-x86p-projection)
                       (word-state
                        subset-p)))
          ("Goal''" :in-theory (e/d* (env-assumptions eof-terminatedp)
                                     (word-state subset-p))
           :use ((:instance loop-preconditions-fwd-chaining-essentials)))))

(defthmd effects-other-char-encountered-state-out-programmer-level-mode-projection
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (not (equal (get-char (offset x86) (input x86)) *eof*))
                (not (equal (get-char (offset x86) (input x86)) *newline*))
                (not (equal (get-char (offset x86) (input x86)) *space*))
                (not (equal (get-char (offset x86) (input x86)) *tab*))
                (equal (combine-bytes (word-state x86 x86)) *out*))
           (equal (xr :programmer-level-mode 0 (x86-run (gc-clk-otherwise-out) x86))
                  (xr :programmer-level-mode 0 x86)))
  :hints (("Goal" :in-theory (e/d* () (word-state subset-p)))))

(defthmd effects-other-char-encountered-state-out-alignment-checking-enabled-p-projection
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (not (equal (get-char (offset x86) (input x86)) *eof*))
                (not (equal (get-char (offset x86) (input x86)) *newline*))
                (not (equal (get-char (offset x86) (input x86)) *space*))
                (not (equal (get-char (offset x86) (input x86)) *tab*))
                (equal (combine-bytes (word-state x86 x86)) *out*))
           (equal (alignment-checking-enabled-p (x86-run (gc-clk-otherwise-out) x86))
                  (alignment-checking-enabled-p x86)))
  :hints (("Goal" :in-theory (e/d* () (word-state subset-p)))))

(defthmd effects-other-char-encountered-state-out-os-info-projection
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (not (equal (get-char (offset x86) (input x86)) *eof*))
                (not (equal (get-char (offset x86) (input x86)) *newline*))
                (not (equal (get-char (offset x86) (input x86)) *space*))
                (not (equal (get-char (offset x86) (input x86)) *tab*))
                (equal (combine-bytes (word-state x86 x86)) *out*))
           (equal (xr :os-info 0 (x86-run (gc-clk-otherwise-out) x86))
                  (xr :os-info 0 x86)))
  :hints (("Goal" :in-theory (e/d* () (word-state subset-p)))))

(defthm loop-preconditions-other-char-encountered-state-out
  (implies (and (loop-preconditions addr x86)
                (not (equal (get-char (offset x86) (input x86)) *eof*))
                (not (equal (get-char (offset x86) (input x86)) *newline*))
                (not (equal (get-char (offset x86) (input x86)) *space*))
                (not (equal (get-char (offset x86) (input x86)) *tab*))
                (equal (combine-bytes (word-state x86 x86)) *out*))
           (loop-preconditions addr (x86-run (gc-clk-otherwise-out) x86)))
  :hints (("Goal" :in-theory '(effects-other-char-encountered-state-out-rbp-projection
                               effects-other-char-encountered-state-out-rsp-projection
                               x86p-effects-other-char-encountered-state-out
                               effects-other-char-encountered-state-out-msri-projection
                               effects-other-char-encountered-state-out-rip-projection
                               effects-other-char-encountered-state-out-ms-projection
                               effects-other-char-encountered-state-out-fault-projection
                               effects-other-char-encountered-state-out-env-assumptions-projection
                               (len)
                               loop-preconditions-fwd-chaining-essentials
                               loop-preconditions-forward-chain-addresses-info
                               effects-other-char-encountered-state-out-programmer-level-mode-projection
                               effects-other-char-encountered-state-out-alignment-checking-enabled-p-projection
                               effects-other-char-encountered-state-out-os-info-projection
                               effects-other-char-encountered-state-out-program-projection)
           :expand (loop-preconditions addr (x86-run (gc-clk-otherwise-out) x86)))))

(defthmd effects-other-char-encountered-state-out-input-projection
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (not (equal (get-char (offset x86) (input x86)) *eof*))
                (not (equal (get-char (offset x86) (input x86)) *newline*))
                (not (equal (get-char (offset x86) (input x86)) *space*))
                (not (equal (get-char (offset x86) (input x86)) *tab*))
                (equal (combine-bytes (word-state x86 x86)) *out*))
           (equal (input (x86-run (gc-clk-otherwise-out) x86))
                  (input x86)))
  :hints (("Goal" :in-theory (e/d* () (word-state subset-p)))))

(defthmd effects-other-char-encountered-state-out-offset-projection
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (not (equal (get-char (offset x86) (input x86)) *eof*))
                (not (equal (get-char (offset x86) (input x86)) *newline*))
                (not (equal (get-char (offset x86) (input x86)) *space*))
                (not (equal (get-char (offset x86) (input x86)) *tab*))
                (equal (combine-bytes (word-state x86 x86)) *out*))
           (equal (offset (x86-run (gc-clk-otherwise-out) x86))
                  (+ 1 (offset x86))))
  :hints (("Goal" :in-theory (e/d* () (word-state subset-p)))))

;;----------------------------------------------------------------------
;; Other Char Encountered (State = OUT): Delta Variable Theorems:
;;----------------------------------------------------------------------

(defthmd effects-other-char-encountered-state-out-variables-state
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (not (equal (get-char (offset x86) (input x86)) *eof*))
                (not (equal (get-char (offset x86) (input x86)) *newline*))
                (not (equal (get-char (offset x86) (input x86)) *space*))
                (not (equal (get-char (offset x86) (input x86)) *tab*))
                (equal (combine-bytes (word-state x86 x86)) *out*))
           (equal (combine-bytes (word-state x86 (x86-run (gc-clk-otherwise-out) x86)))
                  *in*))
  :hints (("Goal"
           :use ((:instance effects-other-char-encountered-state-out-rbp-projection)
                 (:instance effects-other-char-encountered-state-out)))))

(defthmd effects-other-char-encountered-state-out-variables-state-in-terms-of-next-x86
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (not (equal (get-char (offset x86) (input x86)) *eof*))
                (not (equal (get-char (offset x86) (input x86)) *newline*))
                (not (equal (get-char (offset x86) (input x86)) *space*))
                (not (equal (get-char (offset x86) (input x86)) *tab*))
                (equal (combine-bytes (word-state x86 x86)) *out*))
           (equal (word-state (x86-run (gc-clk-otherwise-out) x86) xxx)
                  (word-state x86 xxx)))
  :hints (("Goal" :in-theory
           '(effects-other-char-encountered-state-out-rbp-projection
             effects-other-char-encountered-state-out-variables-state
             word-state))))

(defthmd effects-other-char-encountered-state-out-variables-nc
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (not (equal (get-char (offset x86) (input x86)) *eof*))
                (not (equal (get-char (offset x86) (input x86)) *newline*))
                (not (equal (get-char (offset x86) (input x86)) *space*))
                (not (equal (get-char (offset x86) (input x86)) *tab*))
                (equal (combine-bytes (word-state x86 x86)) *out*))
           (equal (combine-bytes (nc x86 (x86-run (gc-clk-otherwise-out) x86)))
                  (loghead 32 (+ 1 (combine-bytes (nc x86 x86))))))
  :hints (("Goal" :in-theory (e/d* (programmer-level-mode-permissions-dont-matter)
                                   (force (force)))
           :use ((:instance effects-other-char-encountered-state-out)
                 (:instance loop-preconditions-fwd-chaining-essentials)))))

(defthmd effects-other-char-encountered-state-out-variables-nc-in-terms-of-next-x86
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (not (equal (get-char (offset x86) (input x86)) *eof*))
                (not (equal (get-char (offset x86) (input x86)) *newline*))
                (not (equal (get-char (offset x86) (input x86)) *space*))
                (not (equal (get-char (offset x86) (input x86)) *tab*))
                (equal (combine-bytes (word-state x86 x86)) *out*))
           (equal (nc (x86-run (gc-clk-otherwise-out) x86) xxx)
                  (nc x86 xxx)))
  :hints (("Goal" :in-theory
           '(effects-other-char-encountered-state-out-rbp-projection
             effects-other-char-encountered-state-out-variables-state
             nc))))

(defthmd effects-other-char-encountered-state-out-variables-nw
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (not (equal (get-char (offset x86) (input x86)) *eof*))
                (not (equal (get-char (offset x86) (input x86)) *newline*))
                (not (equal (get-char (offset x86) (input x86)) *space*))
                (not (equal (get-char (offset x86) (input x86)) *tab*))
                (equal (combine-bytes (word-state x86 x86)) *out*))
           (equal (combine-bytes (nw x86 (x86-run (gc-clk-otherwise-out) x86)))
                  (loghead 32 (+ 1 (combine-bytes (nw x86 x86))))))
  :hints (("Goal" :in-theory (e/d* (programmer-level-mode-permissions-dont-matter)
                                   (force (force)))
           :use ((:instance effects-other-char-encountered-state-out)
                 (:instance loop-preconditions-fwd-chaining-essentials)))))

(defthmd effects-other-char-encountered-state-out-variables-nw-in-terms-of-next-x86
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (not (equal (get-char (offset x86) (input x86)) *eof*))
                (not (equal (get-char (offset x86) (input x86)) *newline*))
                (not (equal (get-char (offset x86) (input x86)) *space*))
                (not (equal (get-char (offset x86) (input x86)) *tab*))
                (equal (combine-bytes (word-state x86 x86)) *out*))
           (equal (nw (x86-run (gc-clk-otherwise-out) x86) xxx)
                  (nw x86 xxx)))
  :hints (("Goal" :in-theory
           '(effects-other-char-encountered-state-out-rbp-projection
             effects-other-char-encountered-state-out-variables-state
             nw))))

(defthmd effects-other-char-encountered-state-out-variables-nl
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (not (equal (get-char (offset x86) (input x86)) *eof*))
                (not (equal (get-char (offset x86) (input x86)) *newline*))
                (not (equal (get-char (offset x86) (input x86)) *space*))
                (not (equal (get-char (offset x86) (input x86)) *tab*))
                (equal (combine-bytes (word-state x86 x86)) *out*))
           (equal (nl x86 (x86-run (gc-clk-otherwise-out) x86))
                  (nl x86 x86)))
  :hints (("Goal" :in-theory (e/d* (programmer-level-mode-permissions-dont-matter)
                                   (force (force)))
           :use ((:instance effects-other-char-encountered-state-out)
                 (:instance loop-preconditions-fwd-chaining-essentials)))))

(defthmd effects-other-char-encountered-state-out-variables-nl-in-terms-of-next-x86
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (not (equal (get-char (offset x86) (input x86)) *eof*))
                (not (equal (get-char (offset x86) (input x86)) *newline*))
                (not (equal (get-char (offset x86) (input x86)) *space*))
                (not (equal (get-char (offset x86) (input x86)) *tab*))
                (equal (combine-bytes (word-state x86 x86)) *out*))
           (equal (nl (x86-run (gc-clk-otherwise-out) x86) xxx)
                  (nl x86 xxx)))
  :hints (("Goal" :in-theory
           '(effects-other-char-encountered-state-out-rbp-projection
             effects-other-char-encountered-state-out-variables-state
             nl))))

;;**********************************************************************
;; Other Char Encountered (State = IN)
;;**********************************************************************

(defthmd effects-other-char-encountered-state-in-limited
  ;;  callq <gc>
  ;;
  ;;  addl $0x1,-0x10(%rbp)
  ;;  callq <gc>

  (implies
   (and (x86p x86-new)
        (xr :programmer-level-mode 0 x86-new)
        (not (alignment-checking-enabled-p x86-new))
        (env-assumptions x86-new)
        (canonical-address-p (xr :rgf *rsp* x86-new))
        ;; Points to the "addl $0x1,-0xc(%rbp)" instruction in main
        (equal addr (- (xr :rip 0 x86-new) (+ 37 (1- (len *gc*)))))
        (canonical-address-p addr)
        (canonical-address-p (+ (1- (len *wc*)) addr))
        (canonical-address-p (+ #x20 (xr :rgf *rsp* x86-new)))
        (canonical-address-p (+ (- (+ 8 #x20 8)) (xr :rgf *rsp* x86-new)))
        ;; (+ 8 #x20 8 #x20) = 80
        (disjoint-p
         ;; IMPORTANT: Keep the program addresses as the first
         ;; argument.
         (create-canonical-address-list (len *wc*) addr)
         (create-canonical-address-list 80 (+ (- (+ 8 #x20 8)) (xr :rgf *rsp* x86-new))))
        ;; IMPORTANT: Why doesn't the following hyp work?
        ;; (equal (xr :rgf *rbp* x86-new) (- (+ (xr :rgf *rsp* x86-new) 40) 8))
        (canonical-address-p (xr :rgf *rbp* x86-new))
        (equal (xr :rgf *rsp* x86-new) (- (xr :rgf *rbp* x86-new) 32))
        (equal (xr :ms 0 x86-new) nil)
        (equal (xr :fault 0 x86-new) nil)
        ;; Enabling the SYSCALL instruction.
        (equal (ia32_efer-slice :ia32_efer-sce (xr :msr *ia32_efer-idx* x86-new)) 1)
        (equal (ia32_efer-slice :ia32_efer-lma (xr :msr *ia32_efer-idx* x86-new)) 1)
        (program-at (create-canonical-address-list (len *wc*) addr) *wc* x86-new)

        (not (equal (combine-bytes
                     (mv-nth 1 (rb (create-canonical-address-list 4 (+ -4 (xr :rgf *rbp* x86-new))) :x x86-new)))
                    *eof*))
        (not (equal (combine-bytes
                     (mv-nth 1 (rb (create-canonical-address-list 4 (+ -4 (xr :rgf *rbp* x86-new))) :x x86-new)))
                    *newline*))
        (not (equal (combine-bytes
                     (mv-nth 1 (rb (create-canonical-address-list 4 (+ -4 (xr :rgf *rbp* x86-new))) :x x86-new)))
                    *space*))
        (not (equal (combine-bytes
                     (mv-nth 1 (rb (create-canonical-address-list 4 (+ -4 (xr :rgf *rbp* x86-new))) :x x86-new)))
                    *tab*))
        (not (equal (combine-bytes
                     (mv-nth 1 (rb (create-canonical-address-list 4 (+ -8 (xr :rgf *rbp* x86-new))) :x x86-new)))
                    *out*))
        ;; Character read in is a byte.
        (unsigned-byte-p
         8
         (combine-bytes
          (mv-nth 1 (rb (create-canonical-address-list 4 (+ -4 (xr :rgf *rbp* x86-new))) :x x86-new)))))
   (equal (x86-run 11 x86-new)
          (XW
           :RIP 0 (+ 58 (XR :RIP 0 X86-NEW))
           (MV-NTH
            1
            (WB
             (CREATE-ADDR-BYTES-ALIST
              (CREATE-CANONICAL-ADDRESS-LIST 4 (+ 20 (XR :RGF *RSP* X86-NEW)))
              (BYTE-IFY
               4
               (LOGHEAD
                32
                (+
                 1
                 (COMBINE-BYTES
                  (MV-NTH
                   1
                   (RB
                    (CREATE-CANONICAL-ADDRESS-LIST 4 (+ 20 (XR :RGF *RSP* X86-NEW)))
                    :X X86-NEW)))))))
             (!FLGI
              *CF*
              (LOGHEAD
               1
               (BOOL->BIT
                (<
                 (COMBINE-BYTES
                  (MV-NTH
                   1
                   (RB
                    (CREATE-CANONICAL-ADDRESS-LIST 4 (+ 24 (XR :RGF *RSP* X86-NEW)))
                    :X X86-NEW)))
                 0)))
              (!FLGI
               *PF*
               (LOGIOR
                (PF-SPEC32
                 (COMBINE-BYTES
                  (MV-NTH
                   1
                   (RB
                    (CREATE-CANONICAL-ADDRESS-LIST 4 (+ 24 (XR :RGF *RSP* X86-NEW)))
                    :X X86-NEW))))
                (LOGHEAD
                 -1
                 (LOGTAIL
                  2
                  (BOOL->BIT
                   (<
                    (COMBINE-BYTES (MV-NTH 1
                                           (RB (CREATE-CANONICAL-ADDRESS-LIST
                                                4 (+ 24 (XR :RGF *RSP* X86-NEW)))
                                               :X X86-NEW)))
                    0)))))
               (!FLGI
                *AF*
                (LOGIOR
                 (SUB-AF-SPEC32
                  (COMBINE-BYTES
                   (MV-NTH
                    1
                    (RB
                     (CREATE-CANONICAL-ADDRESS-LIST 4 (+ 24 (XR :RGF *RSP* X86-NEW)))
                     :X X86-NEW)))
                  0)
                 (LOGHEAD
                  -3
                  (LOGTAIL
                   4
                   (BOOL->BIT
                    (< (COMBINE-BYTES
                        (MV-NTH 1
                                (RB (CREATE-CANONICAL-ADDRESS-LIST
                                     4 (+ 24 (XR :RGF *RSP* X86-NEW)))
                                    :X X86-NEW)))
                       0)))))
                (!FLGI
                 *ZF* 0
                 (!FLGI
                  *SF*
                  (LOGIOR
                   (SF-SPEC32
                    (COMBINE-BYTES (MV-NTH 1
                                           (RB (CREATE-CANONICAL-ADDRESS-LIST
                                                4 (+ 24 (XR :RGF *RSP* X86-NEW)))
                                               :X X86-NEW))))
                   (LOGHEAD
                    -6
                    (LOGTAIL
                     7
                     (BOOL->BIT
                      (< (COMBINE-BYTES
                          (MV-NTH 1
                                  (RB (CREATE-CANONICAL-ADDRESS-LIST
                                       4 (+ 24 (XR :RGF *RSP* X86-NEW)))
                                      :X X86-NEW)))
                         0)))))
                  (!FLGI
                   *OF*
                   (LOGIOR
                    (OF-SPEC32
                     (LOGEXT 32
                             (COMBINE-BYTES
                              (MV-NTH 1
                                      (RB (CREATE-CANONICAL-ADDRESS-LIST
                                           4 (+ 24 (XR :RGF *RSP* X86-NEW)))
                                          :X X86-NEW)))))
                    (LOGHEAD
                     -10
                     (LOGTAIL
                      11
                      (BOOL->BIT
                       (< (COMBINE-BYTES
                           (MV-NTH 1
                                   (RB (CREATE-CANONICAL-ADDRESS-LIST
                                        4 (+ 24 (XR :RGF *RSP* X86-NEW)))
                                       :X X86-NEW)))
                          0)))))
                   X86-NEW)))))))))))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (e/d* (top-level-opcode-execute
                             instruction-decoding-and-spec-rules

                             gpr-sub-spec-4
                             gpr-add-spec-4
                             jcc/cmovcc/setcc-spec
                             !rgfi-size
                             x86-operand-to-reg/mem
                             wr64
                             wr32
                             rr08
                             rr32
                             rr64
                             x86-operand-from-modr/m-and-sib-bytes
                             write-canonical-address-to-memory
                             rim-size
                             rim08
                             rim32
                             rm32
                             wm-size
                             wm32
                             wm64
                             two-byte-opcode-decode-and-execute
                             x86-effective-addr
                             x86-run-plus-1
                             remove-loghead-from-combine-bytes)
                            (x86-run-plus
                             byte-ify
                             (byte-ify))))))

(local
 (defthmd combine-bytes-and-byte-ify-inequality-lemma-for-n=4
   (implies (and (not (equal bytes (byte-ify 4 val)))
                 (byte-listp bytes)
                 (equal (len bytes) 4))
            (equal (equal (combine-bytes bytes) val) nil))
   :hints (("Goal" :in-theory (e/d (combine-bytes byte-ify) ())))))

(defthmd effects-other-char-encountered-state-in-1

  ;;  callq <gc>
  ;;
  ;;  addl $0x1,-0x10(%rbp)
  ;;  callq <gc>

  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (not (equal (get-char (offset x86) (input x86)) *eof*))
                (not (equal (get-char (offset x86) (input x86)) *newline*))
                (not (equal (get-char (offset x86) (input x86)) *space*))
                (not (equal (get-char (offset x86) (input x86)) *tab*))
                ;; (not (equal (word-state x86-new x86-new) (byte-ify 4 *out*)))
                (not (equal (combine-bytes (word-state x86-new x86-new)) *out*))
                (equal x86-new (x86-run (gc-clk-no-eof) x86)))
           (equal (x86-run 11 x86-new)
                  (XW
                   :RIP 0 (+ 58 (XR :RIP 0 X86-NEW))
                   (MV-NTH
                    1
                    (WB
                     (CREATE-ADDR-BYTES-ALIST
                      (CREATE-CANONICAL-ADDRESS-LIST 4 (+ 20 (XR :RGF *RSP* X86-NEW)))
                      (BYTE-IFY
                       4
                       (LOGHEAD
                        32
                        (+
                         1
                         (COMBINE-BYTES
                          (MV-NTH
                           1
                           (RB
                            (CREATE-CANONICAL-ADDRESS-LIST 4 (+ 20 (XR :RGF *RSP* X86-NEW)))
                            :X X86-NEW)))))))
                     (!FLGI
                      *CF*
                      (LOGHEAD
                       1
                       (BOOL->BIT
                        (<
                         (COMBINE-BYTES
                          (MV-NTH
                           1
                           (RB
                            (CREATE-CANONICAL-ADDRESS-LIST 4 (+ 24 (XR :RGF *RSP* X86-NEW)))
                            :X X86-NEW)))
                         0)))
                      (!FLGI
                       *PF*
                       (LOGIOR
                        (PF-SPEC32
                         (COMBINE-BYTES
                          (MV-NTH
                           1
                           (RB
                            (CREATE-CANONICAL-ADDRESS-LIST 4 (+ 24 (XR :RGF *RSP* X86-NEW)))
                            :X X86-NEW))))
                        (LOGHEAD
                         -1
                         (LOGTAIL
                          2
                          (BOOL->BIT
                           (<
                            (COMBINE-BYTES (MV-NTH 1
                                                   (RB (CREATE-CANONICAL-ADDRESS-LIST
                                                        4 (+ 24 (XR :RGF *RSP* X86-NEW)))
                                                       :X X86-NEW)))
                            0)))))
                       (!FLGI
                        *AF*
                        (LOGIOR
                         (SUB-AF-SPEC32
                          (COMBINE-BYTES
                           (MV-NTH
                            1
                            (RB
                             (CREATE-CANONICAL-ADDRESS-LIST 4 (+ 24 (XR :RGF *RSP* X86-NEW)))
                             :X X86-NEW)))
                          0)
                         (LOGHEAD
                          -3
                          (LOGTAIL
                           4
                           (BOOL->BIT
                            (< (COMBINE-BYTES
                                (MV-NTH 1
                                        (RB (CREATE-CANONICAL-ADDRESS-LIST
                                             4 (+ 24 (XR :RGF *RSP* X86-NEW)))
                                            :X X86-NEW)))
                               0)))))
                        (!FLGI
                         *ZF* 0
                         (!FLGI
                          *SF*
                          (LOGIOR
                           (SF-SPEC32
                            (COMBINE-BYTES (MV-NTH 1
                                                   (RB (CREATE-CANONICAL-ADDRESS-LIST
                                                        4 (+ 24 (XR :RGF *RSP* X86-NEW)))
                                                       :X X86-NEW))))
                           (LOGHEAD
                            -6
                            (LOGTAIL
                             7
                             (BOOL->BIT
                              (< (COMBINE-BYTES
                                  (MV-NTH 1
                                          (RB (CREATE-CANONICAL-ADDRESS-LIST
                                               4 (+ 24 (XR :RGF *RSP* X86-NEW)))
                                              :X X86-NEW)))
                                 0)))))
                          (!FLGI
                           *OF*
                           (LOGIOR
                            (OF-SPEC32
                             (LOGEXT 32
                                     (COMBINE-BYTES
                                      (MV-NTH 1
                                              (RB (CREATE-CANONICAL-ADDRESS-LIST
                                                   4 (+ 24 (XR :RGF *RSP* X86-NEW)))
                                                  :X X86-NEW)))))
                            (LOGHEAD
                             -10
                             (LOGTAIL
                              11
                              (BOOL->BIT
                               (< (COMBINE-BYTES
                                   (MV-NTH 1
                                           (RB (CREATE-CANONICAL-ADDRESS-LIST
                                                4 (+ 24 (XR :RGF *RSP* X86-NEW)))
                                               :X X86-NEW)))
                                  0)))))
                           X86-NEW)))))))))))
  :hints (("Goal" :in-theory
           (union-theories '(loop-preconditions
                             input
                             get-char
                             offset
                             rgfi-is-i64p
                             (len) (loghead) (byte-ify)
                             (logior) (ash) (natp)
                             programmer-level-mode-permissions-dont-matter
                             combine-bytes
                             word-state
                             remove-loghead-from-byte-ify
                             combine-bytes-and-byte-ify-inequality-lemma
                             byte-listp-and-consp-of-take-from-environment-assumptions
                             rb-returns-byte-listp
                             len-of-rb-in-programmer-level-mode
                             combine-bytes-and-byte-ify-inequality-lemma-for-n=4
                             canonical-address-p-addr-byte-alistp
                             member-p-canonical-address-p
                             member-p-canonical-address-p-canonical-address-listp
                             canonical-address-p-limits-thm-0
                             canonical-address-p-limits-thm-1
                             canonical-address-p-limits-thm-2
                             combine-bytes-with-byte-ify-4-inequality-lemma)
                           (theory 'minimal-theory))
           :use ((:instance effects-eof-not-encountered-prelim-for-composition (x86 x86))
                 (:instance effects-eof-not-encountered-prelim-gc-byte-projection-size (x86 x86))
                 (:instance effects-eof-not-encountered-prelim-env-assumptions-projection (x86 x86))
                 (:instance effects-eof-not-encountered-prelim-rbp-projection (x86 x86))
                 (:instance effects-eof-not-encountered-prelim-programmer-level-mode-projection (x86 x86))
                 (:instance effects-other-char-encountered-state-in-limited
                            (x86-new (x86-run (gc-clk-no-eof) x86)))))))

(defthm effects-other-char-encountered-state-in

  ;;  callq <gc>
  ;;
  ;;  addl $0x1,-0x10(%rbp)
  ;;  callq <gc>

  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (not (equal (get-char (offset x86) (input x86)) *eof*))
                (not (equal (get-char (offset x86) (input x86)) *newline*))
                (not (equal (get-char (offset x86) (input x86)) *space*))
                (not (equal (get-char (offset x86) (input x86)) *tab*))
                (not (equal (combine-bytes (word-state x86 x86)) *out*)))
           (equal (x86-run (gc-clk-otherwise-in) x86)
                  (XW
                   :RIP 0 (+ 58 (XR :RIP 0 (X86-RUN (GC-CLK-NO-EOF) X86)))
                   (MV-NTH
                    1
                    (WB
                     (CREATE-ADDR-BYTES-ALIST
                      (CREATE-CANONICAL-ADDRESS-LIST
                       4 (+ 20 (XR :RGF *RSP* (X86-RUN (GC-CLK-NO-EOF) X86))))
                      (BYTE-IFY
                       4
                       (LOGHEAD
                        32
                        (+
                         1
                         (COMBINE-BYTES
                          (MV-NTH
                           1
                           (RB
                            (CREATE-CANONICAL-ADDRESS-LIST
                             4 (+ 20 (XR :RGF *RSP* (X86-RUN (GC-CLK-NO-EOF) X86))))
                            :X (X86-RUN (GC-CLK-NO-EOF) X86))))))))
                     (!FLGI
                      *CF*
                      (LOGHEAD
                       1
                       (BOOL->BIT
                        (<
                         (COMBINE-BYTES
                          (MV-NTH
                           1
                           (RB
                            (CREATE-CANONICAL-ADDRESS-LIST
                             4 (+ 24 (XR :RGF *RSP* (X86-RUN (GC-CLK-NO-EOF) X86))))
                            :X (X86-RUN (GC-CLK-NO-EOF) X86))))
                         0)))
                      (!FLGI
                       *PF*
                       (LOGIOR
                        (PF-SPEC32
                         (COMBINE-BYTES
                          (MV-NTH
                           1
                           (RB
                            (CREATE-CANONICAL-ADDRESS-LIST
                             4 (+ 24 (XR :RGF *RSP* (X86-RUN (GC-CLK-NO-EOF) X86))))
                            :X (X86-RUN (GC-CLK-NO-EOF) X86)))))
                        (LOGHEAD
                         -1
                         (LOGTAIL
                          2
                          (BOOL->BIT
                           (<
                            (COMBINE-BYTES
                             (MV-NTH 1
                                     (RB (CREATE-CANONICAL-ADDRESS-LIST
                                          4 (+ 24 (XR :RGF *RSP* (X86-RUN (GC-CLK-NO-EOF) X86))))
                                         :X (X86-RUN (GC-CLK-NO-EOF) X86))))
                            0)))))
                       (!FLGI
                        *AF*
                        (LOGIOR
                         (SUB-AF-SPEC32
                          (COMBINE-BYTES
                           (MV-NTH
                            1
                            (RB
                             (CREATE-CANONICAL-ADDRESS-LIST
                              4 (+ 24 (XR :RGF *RSP* (X86-RUN (GC-CLK-NO-EOF) X86))))
                             :X (X86-RUN (GC-CLK-NO-EOF) X86))))
                          0)
                         (LOGHEAD
                          -3
                          (LOGTAIL
                           4
                           (BOOL->BIT
                            (< (COMBINE-BYTES
                                (MV-NTH 1
                                        (RB (CREATE-CANONICAL-ADDRESS-LIST
                                             4 (+ 24 (XR :RGF *RSP* (X86-RUN (GC-CLK-NO-EOF) X86))))
                                            :X (X86-RUN (GC-CLK-NO-EOF) X86))))
                               0)))))
                        (!FLGI
                         *ZF* 0
                         (!FLGI
                          *SF*
                          (LOGIOR
                           (SF-SPEC32
                            (COMBINE-BYTES
                             (MV-NTH 1
                                     (RB (CREATE-CANONICAL-ADDRESS-LIST
                                          4 (+ 24 (XR :RGF *RSP* (X86-RUN (GC-CLK-NO-EOF) X86))))
                                         :X (X86-RUN (GC-CLK-NO-EOF) X86)))))
                           (LOGHEAD
                            -6
                            (LOGTAIL
                             7
                             (BOOL->BIT
                              (< (COMBINE-BYTES
                                  (MV-NTH 1
                                          (RB (CREATE-CANONICAL-ADDRESS-LIST
                                               4 (+ 24 (XR :RGF *RSP* (X86-RUN (GC-CLK-NO-EOF) X86))))
                                              :X (X86-RUN (GC-CLK-NO-EOF) X86))))
                                 0)))))
                          (!FLGI
                           *OF*
                           (LOGIOR
                            (OF-SPEC32
                             (LOGEXT 32
                                     (COMBINE-BYTES
                                      (MV-NTH 1
                                              (RB (CREATE-CANONICAL-ADDRESS-LIST
                                                   4 (+ 24 (XR :RGF *RSP* (X86-RUN (GC-CLK-NO-EOF) X86))))
                                                  :X (X86-RUN (GC-CLK-NO-EOF) X86))))))
                            (LOGHEAD
                             -10
                             (LOGTAIL
                              11
                              (BOOL->BIT
                               (< (COMBINE-BYTES
                                   (MV-NTH 1
                                           (RB (CREATE-CANONICAL-ADDRESS-LIST
                                                4 (+ 24 (XR :RGF *RSP* (X86-RUN (GC-CLK-NO-EOF) X86))))
                                               :X (X86-RUN (GC-CLK-NO-EOF) X86))))
                                  0)))))
                           (X86-RUN (GC-CLK-NO-EOF) X86))))))))))))
  :hints (("Goal"
           :in-theory (union-theories
                       '(programmer-level-mode-permissions-dont-matter
                         word-state
                         gc-clk-otherwise-in
                         dumb-run-plus-thm
                         (:forward-chaining
                          loop-preconditions-fwd-chaining-essentials)
                         (:forward-chaining loop-preconditions-forward-chain-addresses-info))
                       (theory 'minimal-theory))
           :use ((:instance effects-other-char-encountered-state-in-1
                            (x86-new (x86-run (gc-clk-no-eof) x86)))
                 (:instance loop-preconditions-weird-rbp-rsp)
                 (:instance loop-preconditions-fwd-chaining-essentials)
                 (:instance effects-eof-not-encountered-prelim-word-state-projection)
                 (:instance effects-eof-not-encountered-prelim-rbp-projection)))))

;;----------------------------------------------------------------------
;; Other Char Encountered (State = IN): Projection Theorems:
;;----------------------------------------------------------------------

(defthmd effects-other-char-encountered-state-in-rbp-projection
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (not (equal (get-char (offset x86) (input x86)) *eof*))
                (not (equal (get-char (offset x86) (input x86)) *newline*))
                (not (equal (get-char (offset x86) (input x86)) *space*))
                (not (equal (get-char (offset x86) (input x86)) *tab*))
                (not (equal (combine-bytes (word-state x86 x86)) *out*)))
           (equal (xr :rgf *rbp* (x86-run (gc-clk-otherwise-in) x86))
                  (xr :rgf *rbp* x86)))
  :hints (("Goal" :in-theory (e/d* ()
                                   (word-state
                                    loop-preconditions-forward-chain-addresses-info)))))

(defthmd effects-other-char-encountered-state-in-rsp-projection
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (not (equal (get-char (offset x86) (input x86)) *eof*))
                (not (equal (get-char (offset x86) (input x86)) *newline*))
                (not (equal (get-char (offset x86) (input x86)) *space*))
                (not (equal (get-char (offset x86) (input x86)) *tab*))
                (not (equal (combine-bytes (word-state x86 x86)) *out*)))
           (equal (xr :rgf *rsp* (x86-run (gc-clk-otherwise-in) x86))
                  (xr :rgf *rsp* x86)))
  :hints (("Goal" :in-theory (e/d* ()
                                   (word-state
                                    loop-preconditions-forward-chain-addresses-info)))))

(defthmd effects-other-char-encountered-state-in-rsp-projection-new
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (not (equal (get-char (offset x86) (input x86)) *eof*))
                (not (equal (get-char (offset x86) (input x86)) *newline*))
                (not (equal (get-char (offset x86) (input x86)) *space*))
                (not (equal (get-char (offset x86) (input x86)) *tab*))
                (not (equal (combine-bytes (word-state x86 x86)) *out*)))
           (equal (xr :rgf *rsp* (x86-run (gc-clk-otherwise-in) x86))
                  (xr :rgf *rsp* x86)))
  :hints (("Goal" :use ((:instance effects-other-char-encountered-state-in-rsp-projection)))))

(defthmd x86p-effects-other-char-encountered-state-in
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (not (equal (get-char (offset x86) (input x86)) *eof*))
                (not (equal (get-char (offset x86) (input x86)) *newline*))
                (not (equal (get-char (offset x86) (input x86)) *space*))
                (not (equal (get-char (offset x86) (input x86)) *tab*))
                (not (equal (combine-bytes (word-state x86 x86)) *out*)))
           (x86p (x86-run (gc-clk-otherwise-in) x86)))
  :hints (("Goal" :in-theory (e/d* (loop-preconditions)
                                   (word-state
                                    loop-preconditions-forward-chain-addresses-info)))))

(defthmd effects-other-char-encountered-state-in-msri-projection
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (not (equal (get-char (offset x86) (input x86)) *eof*))
                (not (equal (get-char (offset x86) (input x86)) *newline*))
                (not (equal (get-char (offset x86) (input x86)) *space*))
                (not (equal (get-char (offset x86) (input x86)) *tab*))
                (not (equal (combine-bytes (word-state x86 x86)) *out*)))
           (and (equal (ia32_efer-slice :ia32_efer-sce (xr :msr *ia32_efer-idx*
                                                           (x86-run (gc-clk-otherwise-in) x86))) 1)
                (equal (ia32_efer-slice :ia32_efer-lma (xr :msr *ia32_efer-idx*
                                                           (x86-run (gc-clk-otherwise-in) x86))) 1)))
  :hints (("Goal" :in-theory (e/d* () (combine-bytes word-state))
           :use ((:instance loop-preconditions-fwd-chaining-essentials)))))

(defthmd effects-other-char-encountered-state-in-rip-projection
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (not (equal (get-char (offset x86) (input x86)) *eof*))
                (not (equal (get-char (offset x86) (input x86)) *newline*))
                (not (equal (get-char (offset x86) (input x86)) *space*))
                (not (equal (get-char (offset x86) (input x86)) *tab*))
                (not (equal (combine-bytes (word-state x86 x86)) *out*)))
           (equal (xr :rip 0 (x86-run (gc-clk-otherwise-in) x86))
                  (+ 145 addr)))
  :hints (("Goal" :in-theory (e/d* () (word-state subset-p)))))

(defthmd effects-other-char-encountered-state-in-ms-projection
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (not (equal (get-char (offset x86) (input x86)) *eof*))
                (not (equal (get-char (offset x86) (input x86)) *newline*))
                (not (equal (get-char (offset x86) (input x86)) *space*))
                (not (equal (get-char (offset x86) (input x86)) *tab*))
                (not (equal (combine-bytes (word-state x86 x86)) *out*)))
           (equal (xr :ms 0 (x86-run (gc-clk-otherwise-in) x86)) nil))
  :hints (("Goal" :in-theory (e/d* ()
                                   (word-state
                                    loop-preconditions-forward-chain-addresses-info)))))

(defthmd effects-other-char-encountered-state-in-fault-projection
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (not (equal (get-char (offset x86) (input x86)) *eof*))
                (not (equal (get-char (offset x86) (input x86)) *newline*))
                (not (equal (get-char (offset x86) (input x86)) *space*))
                (not (equal (get-char (offset x86) (input x86)) *tab*))
                (not (equal (combine-bytes (word-state x86 x86)) *out*)))
           (equal (xr :fault 0 (x86-run (gc-clk-otherwise-in) x86)) nil))
  :hints (("Goal" :in-theory (e/d* ()
                                   (word-state
                                    loop-preconditions-forward-chain-addresses-info)))))

(defthmd effects-other-char-encountered-state-in-program-projection
  (implies (and (loop-preconditions addr x86) (equal len-wc (len *wc*))
                (not (equal (get-char (offset x86) (input x86)) *eof*))
                (not (equal (get-char (offset x86) (input x86)) *newline*))
                (not (equal (get-char (offset x86) (input x86)) *space*))
                (not (equal (get-char (offset x86) (input x86)) *tab*))
                (not (equal (combine-bytes (word-state x86 x86)) *out*)))
           (program-at (create-canonical-address-list len-wc
                                                      addr)
                       *wc* (x86-run (gc-clk-otherwise-in) x86)))
  :hints (("Goal" :in-theory (e/d*
                              (effects-eof-not-encountered-prelim-programmer-level-mode-projection
                               effects-eof-not-encountered-prelim-program-projection
                               effects-eof-not-encountered-prelim-x86p-projection
                               loop-preconditions-weird-rbp-rsp)
                              (word-state))
           :use ((:instance loop-preconditions-fwd-chaining-essentials)))))

(defthmd effects-other-char-encountered-state-in-env-assumptions-projection
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (not (equal (get-char (offset x86) (input x86)) *eof*))
                (not (equal (get-char (offset x86) (input x86)) *newline*))
                (not (equal (get-char (offset x86) (input x86)) *space*))
                (not (equal (get-char (offset x86) (input x86)) *tab*))
                (not (equal (combine-bytes (word-state x86 x86)) *out*)))
           (env-assumptions (x86-run (gc-clk-otherwise-in) x86)))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (e/d*
                       (effects-eof-not-encountered-prelim-env-assumptions-projection
                        effects-eof-not-encountered-prelim-programmer-level-mode-projection
                        effects-eof-not-encountered-prelim-x86p-projection)
                       (word-state
                        subset-p)))
          ("Goal''" :in-theory (e/d* (env-assumptions eof-terminatedp)
                                     (word-state
                                      subset-p))
           :use ((:instance
                  loop-preconditions-fwd-chaining-essentials)))))

(defthmd effects-other-char-encountered-state-in-programmer-level-mode-projection
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (not (equal (get-char (offset x86) (input x86)) *eof*))
                (not (equal (get-char (offset x86) (input x86)) *newline*))
                (not (equal (get-char (offset x86) (input x86)) *space*))
                (not (equal (get-char (offset x86) (input x86)) *tab*))
                (not (equal (combine-bytes (word-state x86 x86)) *out*)))
           (equal (xr :programmer-level-mode 0 (x86-run (gc-clk-otherwise-in) x86))
                  (xr :programmer-level-mode 0 x86)))
  :hints (("Goal" :in-theory (e/d* ()
                                  (word-state
                                   loop-preconditions-forward-chain-addresses-info)))))

(defthmd effects-other-char-encountered-state-in-alignment-checking-enabled-p-projection
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (not (equal (get-char (offset x86) (input x86)) *eof*))
                (not (equal (get-char (offset x86) (input x86)) *newline*))
                (not (equal (get-char (offset x86) (input x86)) *space*))
                (not (equal (get-char (offset x86) (input x86)) *tab*))
                (not (equal (combine-bytes (word-state x86 x86)) *out*)))
           (equal (alignment-checking-enabled-p (x86-run (gc-clk-otherwise-in) x86))
                  (alignment-checking-enabled-p x86)))
  :hints (("Goal" :in-theory (e/d* ()
                                   (word-state
                                    loop-preconditions-forward-chain-addresses-info)))))

(defthmd effects-other-char-encountered-state-in-os-info-projection
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (not (equal (get-char (offset x86) (input x86)) *eof*))
                (not (equal (get-char (offset x86) (input x86)) *newline*))
                (not (equal (get-char (offset x86) (input x86)) *space*))
                (not (equal (get-char (offset x86) (input x86)) *tab*))
                (not (equal (combine-bytes (word-state x86 x86)) *out*)))
           (equal (xr :os-info 0 (x86-run (gc-clk-otherwise-in) x86))
                  (xr :os-info 0 x86)))
  :hints (("Goal" :in-theory (e/d* () (word-state loop-preconditions-forward-chain-addresses-info)))))

(defthm loop-preconditions-other-char-encountered-state-in-pre
  (implies (and (loop-preconditions addr x86)
                (not (equal (get-char (offset x86) (input x86)) *eof*))
                (not (equal (get-char (offset x86) (input x86)) *newline*))
                (not (equal (get-char (offset x86) (input x86)) *space*))
                (not (equal (get-char (offset x86) (input x86)) *tab*))
                (not (equal (combine-bytes (word-state x86 x86)) *out*)))
           (loop-preconditions addr (x86-run (gc-clk-otherwise-in) x86)))
  :hints (("Goal" :in-theory '(effects-other-char-encountered-state-in-rbp-projection
                               effects-other-char-encountered-state-in-rsp-projection
                               x86p-effects-other-char-encountered-state-in
                               effects-other-char-encountered-state-in-msri-projection
                               effects-other-char-encountered-state-in-rip-projection
                               effects-other-char-encountered-state-in-ms-projection
                               effects-other-char-encountered-state-in-fault-projection
                               effects-other-char-encountered-state-in-env-assumptions-projection
                               (len)
                               loop-preconditions-fwd-chaining-essentials
                               loop-preconditions-forward-chain-addresses-info
                               effects-other-char-encountered-state-in-programmer-level-mode-projection
                               effects-other-char-encountered-state-in-alignment-checking-enabled-p-projection
                               effects-other-char-encountered-state-in-os-info-projection
                               effects-other-char-encountered-state-in-program-projection)
           :expand (loop-preconditions addr (x86-run (gc-clk-otherwise-in) x86)))))

(defthmd effects-other-char-encountered-state-in-input-projection-pre
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (not (equal (get-char (offset x86) (input x86)) *eof*))
                (not (equal (get-char (offset x86) (input x86)) *newline*))
                (not (equal (get-char (offset x86) (input x86)) *space*))
                (not (equal (get-char (offset x86) (input x86)) *tab*))
                (not (equal (combine-bytes (word-state x86 x86)) *out*)))
           (equal (input (x86-run (gc-clk-otherwise-in) x86))
                  (input x86)))
  :hints (("Goal" :in-theory (e/d* ()
                                   (word-state
                                    loop-preconditions-forward-chain-addresses-info)))))

(defthmd effects-other-char-encountered-state-in-offset-projection-pre
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (not (equal (get-char (offset x86) (input x86)) *eof*))
                (not (equal (get-char (offset x86) (input x86)) *newline*))
                (not (equal (get-char (offset x86) (input x86)) *space*))
                (not (equal (get-char (offset x86) (input x86)) *tab*))
                (not (equal (combine-bytes (word-state x86 x86)) *out*)))
           (equal (offset (x86-run (gc-clk-otherwise-in) x86))
                  (+ 1 (offset x86))))
  :hints (("Goal" :in-theory (e/d* ()
                                   (word-state
                                    loop-preconditions-forward-chain-addresses-info)))))

(defthm loop-preconditions-other-char-encountered-state-in
  (implies (and (loop-preconditions addr x86)
                (not (equal (get-char (offset x86) (input x86)) *eof*))
                (not (equal (get-char (offset x86) (input x86)) *newline*))
                (not (equal (get-char (offset x86) (input x86)) *space*))
                (not (equal (get-char (offset x86) (input x86)) *tab*))
                (not (equal (combine-bytes (word-state x86 x86)) *out*)))
           (loop-preconditions addr (x86-run (gc-clk-otherwise-in) x86)))
  :hints (("Goal":use ((:instance loop-preconditions-other-char-encountered-state-in-pre)))))

(defthmd effects-other-char-encountered-state-in-input-projection
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (not (equal (get-char (offset x86) (input x86)) *eof*))
                (not (equal (get-char (offset x86) (input x86)) *newline*))
                (not (equal (get-char (offset x86) (input x86)) *space*))
                (not (equal (get-char (offset x86) (input x86)) *tab*))
                (not (equal (combine-bytes (word-state x86 x86)) *out*)))
           (equal (input (x86-run (gc-clk-otherwise-in) x86))
                  (input x86)))
  :hints (("Goal" :use ((:instance effects-other-char-encountered-state-in-input-projection-pre)))))

(defthmd effects-other-char-encountered-state-in-offset-projection
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (not (equal (get-char (offset x86) (input x86)) *eof*))
                (not (equal (get-char (offset x86) (input x86)) *newline*))
                (not (equal (get-char (offset x86) (input x86)) *space*))
                (not (equal (get-char (offset x86) (input x86)) *tab*))
                (not (equal (combine-bytes (word-state x86 x86)) *out*)))
           (equal (offset (x86-run (gc-clk-otherwise-in) x86))
                  (+ 1 (offset x86))))
  :hints (("Goal" :use ((:instance effects-other-char-encountered-state-in-offset-projection-pre)))))

;;----------------------------------------------------------------------
;; Other Char Encountered (State = IN): Delta Variable Theorems:
;;----------------------------------------------------------------------

(defthmd effects-other-char-encountered-state-in-variables-state
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (not (equal (get-char (offset x86) (input x86)) *eof*))
                (not (equal (get-char (offset x86) (input x86)) *newline*))
                (not (equal (get-char (offset x86) (input x86)) *space*))
                (not (equal (get-char (offset x86) (input x86)) *tab*))
                (not (equal (combine-bytes (word-state x86 x86)) *out*)))
           (equal (word-state x86 (x86-run (gc-clk-otherwise-in) x86))
                  (word-state x86 x86)))
  :hints (("Goal"
           :use ((:instance effects-other-char-encountered-state-in)
                 (:instance loop-preconditions-fwd-chaining-essentials)))))

(defthmd effects-other-char-encountered-state-in-variables-state-in-terms-of-next-x86
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (not (equal (get-char (offset x86) (input x86)) *eof*))
                (not (equal (get-char (offset x86) (input x86)) *newline*))
                (not (equal (get-char (offset x86) (input x86)) *space*))
                (not (equal (get-char (offset x86) (input x86)) *tab*))
                (not (equal (combine-bytes (word-state x86 x86)) *out*)))
           (equal (word-state (x86-run (gc-clk-otherwise-in) x86) xxx)
                  (word-state x86 xxx)))
  :hints (("Goal" :use ((:instance effects-other-char-encountered-state-in-rbp-projection)))))

(defthmd effects-other-char-encountered-state-in-variables-nc
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (not (equal (get-char (offset x86) (input x86)) *eof*))
                (not (equal (get-char (offset x86) (input x86)) *newline*))
                (not (equal (get-char (offset x86) (input x86)) *space*))
                (not (equal (get-char (offset x86) (input x86)) *tab*))
                (not (equal (combine-bytes (word-state x86 x86)) *out*)))
           (equal (combine-bytes (nc x86 (x86-run (gc-clk-otherwise-in) x86)))
                  (loghead 32 (+ 1 (combine-bytes (nc x86 x86))))))
  :hints (("Goal" :in-theory (e/d* (programmer-level-mode-permissions-dont-matter)
                                   (force (force)))
           :use ((:instance effects-other-char-encountered-state-in)
                 (:instance loop-preconditions-fwd-chaining-essentials)))))

(defthmd effects-other-char-encountered-state-in-variables-nc-in-terms-of-next-x86
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (not (equal (get-char (offset x86) (input x86)) *eof*))
                (not (equal (get-char (offset x86) (input x86)) *newline*))
                (not (equal (get-char (offset x86) (input x86)) *space*))
                (not (equal (get-char (offset x86) (input x86)) *tab*))
                (not (equal (combine-bytes (word-state x86 x86)) *out*)))
           (equal (nc (x86-run (gc-clk-otherwise-in) x86) xxx)
                  (nc x86 xxx)))
  :hints (("Goal" :use ((:instance effects-other-char-encountered-state-in-rbp-projection)))))

(defthmd effects-other-char-encountered-state-in-variables-nw
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (not (equal (get-char (offset x86) (input x86)) *eof*))
                (not (equal (get-char (offset x86) (input x86)) *newline*))
                (not (equal (get-char (offset x86) (input x86)) *space*))
                (not (equal (get-char (offset x86) (input x86)) *tab*))
                (not (equal (combine-bytes (word-state x86 x86)) *out*)))
           (equal (nw x86 (x86-run (gc-clk-otherwise-in) x86))
                  (nw x86 x86)))
  :hints (("Goal" :use ((:instance effects-other-char-encountered-state-in)
                        (:instance loop-preconditions-fwd-chaining-essentials)))))

(defthmd effects-other-char-encountered-state-in-variables-nw-in-terms-of-next-x86
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (not (equal (get-char (offset x86) (input x86)) *eof*))
                (not (equal (get-char (offset x86) (input x86)) *newline*))
                (not (equal (get-char (offset x86) (input x86)) *space*))
                (not (equal (get-char (offset x86) (input x86)) *tab*))
                (not (equal (combine-bytes (word-state x86 x86)) *out*)))
           (equal (nw (x86-run (gc-clk-otherwise-in) x86) xxx)
                  (nw x86 xxx)))
  :hints (("Goal" :use ((:instance effects-other-char-encountered-state-in-rbp-projection)))))

(defthmd effects-other-char-encountered-state-in-variables-nl
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (not (equal (get-char (offset x86) (input x86)) *eof*))
                (not (equal (get-char (offset x86) (input x86)) *newline*))
                (not (equal (get-char (offset x86) (input x86)) *space*))
                (not (equal (get-char (offset x86) (input x86)) *tab*))
                (not (equal (combine-bytes (word-state x86 x86)) *out*)))
           (equal (nl x86 (x86-run (gc-clk-otherwise-in) x86))
                  (nl x86 x86)))
  :hints (("Goal" :use ((:instance effects-other-char-encountered-state-in)
                        (:instance loop-preconditions-fwd-chaining-essentials)))))

(defthmd effects-other-char-encountered-state-in-variables-nl-in-terms-of-next-x86
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (not (equal (get-char (offset x86) (input x86)) *eof*))
                (not (equal (get-char (offset x86) (input x86)) *newline*))
                (not (equal (get-char (offset x86) (input x86)) *space*))
                (not (equal (get-char (offset x86) (input x86)) *tab*))
                (not (equal (combine-bytes (word-state x86 x86)) *out*)))
           (equal (nl (x86-run (gc-clk-otherwise-in) x86) xxx)
                  (nl x86 xxx)))
  :hints (("Goal" :use ((:instance effects-other-char-encountered-state-in-rbp-projection)))))

;; ======================================================================
;; ======================================================================

(in-theory (disable word-state nc nw nl))

;;**********************************************************************
;; Loop Effects:
;;**********************************************************************

(encapsulate
 ()

 (local (include-book "std/lists/nthcdr" :dir :system))

 (defun loop-effects-hint (word-state offset str-bytes x86)
   (declare (xargs :stobjs (x86)
                   :measure (len (nthcdr offset str-bytes))
                   :verify-guards nil))

   (if (and (eof-terminatedp str-bytes)
            (< offset (len str-bytes))
            (natp offset))

       (let ((char (get-char offset str-bytes)))

         (if (equal char #.*eof*)

             (let ((x86 (x86-run (gc-clk-eof) x86)))
               x86)

           (b* (((mv word-state x86)
                 (case char
                   (#.*newline*
                    (b* ((x86 (x86-run (gc-clk-newline) x86)))
                        (mv 0 x86)))
                   (#.*space*
                    (b* ((x86 (x86-run (gc-clk-space) x86)))
                        (mv 0 x86)))
                   (#.*tab*
                    (b* ((x86 (x86-run (gc-clk-tab) x86)))
                        (mv 0 x86)))
                   (t
                    (if (equal word-state #.*out*)
                        (b* ((x86 (x86-run (gc-clk-otherwise-out) x86)))
                            (mv 1 x86))
                      (b* ((x86 (x86-run (gc-clk-otherwise-in) x86)))
                          (mv word-state x86)))))))

               (loop-effects-hint word-state (1+ offset) str-bytes x86))))

     x86))

 ) ;; End of encapsulate

(encapsulate
 ()

 (local (include-book "std/lists/nthcdr" :dir :system))

 (local (include-book "std/lists/take" :dir :system))

 (local (include-book "std/lists/last" :dir :system))

 (local (in-theory (e/d* (acl2::take-of-1 acl2::take-of-zero take nthcdr) ())))

 (local
  (defthm |Subgoal *1/4.5|
    (IMPLIES (AND (EOF-TERMINATEDP STR-BYTES)
                  (< OFFSET (LEN STR-BYTES))
                  (NATP OFFSET)
                  (EQUAL (CAR (GRAB-BYTES (LIST (NTH OFFSET STR-BYTES))))
                         10)
                  (EQUAL (LOOP-EFFECTS-HINT 0 (+ 1 OFFSET)
                                            STR-BYTES
                                            (X86-RUN (GC-CLK-NEWLINE) X86))
                         (X86-RUN (LOOP-CLK 0 (+ 1 OFFSET) STR-BYTES)
                                  (X86-RUN (GC-CLK-NEWLINE) X86))))
             (EQUAL (LOOP-EFFECTS-HINT 0 (+ 1 OFFSET)
                                       STR-BYTES
                                       (X86-RUN (GC-CLK-NEWLINE) X86))
                    (X86-RUN (BINARY-CLK+ (GC-CLK-NEWLINE)
                                          (LOOP-CLK 0 (+ 1 OFFSET) STR-BYTES))
                             X86)))
    :hints (("Goal" :in-theory (e/d* (GC-CLK-NEWLINE
                                      (GC-CLK-NEWLINE)
                                      GC-CLK-NO-EOF
                                      (GC-CLK-NO-EOF)
                                      GC-CLK
                                      (GC-CLK)))))))

 (local
  (defthm |Subgoal *1/4.4|
    (IMPLIES (AND (EOF-TERMINATEDP STR-BYTES)
                  (< OFFSET (LEN STR-BYTES))
                  (NATP OFFSET)
                  (NOT (EQUAL (CAR (GRAB-BYTES (LIST (NTH OFFSET STR-BYTES))))
                              35))
                  (NOT (EQUAL (CAR (GRAB-BYTES (LIST (NTH OFFSET STR-BYTES))))
                              10))
                  (NOT (EQUAL (CAR (GRAB-BYTES (LIST (NTH OFFSET STR-BYTES))))
                              32))
                  (NOT (EQUAL (CAR (GRAB-BYTES (LIST (NTH OFFSET STR-BYTES))))
                              9))
                  (NOT (EQUAL WORD-STATE 0))
                  (EQUAL (LOOP-EFFECTS-HINT WORD-STATE (+ 1 OFFSET)
                                            STR-BYTES
                                            (X86-RUN (GC-CLK-OTHERWISE-IN) X86))
                         (X86-RUN (LOOP-CLK WORD-STATE (+ 1 OFFSET)
                                            STR-BYTES)
                                  (X86-RUN (GC-CLK-OTHERWISE-IN) X86))))
             (EQUAL (LOOP-EFFECTS-HINT WORD-STATE (+ 1 OFFSET)
                                       STR-BYTES
                                       (X86-RUN (GC-CLK-OTHERWISE-IN) X86))
                    (X86-RUN (BINARY-CLK+ (GC-CLK-OTHERWISE-IN)
                                          (LOOP-CLK WORD-STATE (+ 1 OFFSET)
                                                    STR-BYTES))
                             X86)))
    :hints (("Goal" :in-theory (e/d* (GC-CLK-OTHERWISE-IN
                                      (GC-CLK-OTHERWISE-IN)
                                      GC-CLK-NO-EOF
                                      (GC-CLK-NO-EOF)
                                      GC-CLK
                                      (GC-CLK)))))))

 (local
  (defthm |Subgoal *1/4.3'|
    (IMPLIES (AND (EOF-TERMINATEDP STR-BYTES)
                  (< OFFSET (LEN STR-BYTES))
                  (NATP OFFSET)
                  (NOT (EQUAL (CAR (GRAB-BYTES (LIST (NTH OFFSET STR-BYTES))))
                              35))
                  (NOT (EQUAL (CAR (GRAB-BYTES (LIST (NTH OFFSET STR-BYTES))))
                              10))
                  (NOT (EQUAL (CAR (GRAB-BYTES (LIST (NTH OFFSET STR-BYTES))))
                              32))
                  (NOT (EQUAL (CAR (GRAB-BYTES (LIST (NTH OFFSET STR-BYTES))))
                              9))
                  (EQUAL (LOOP-EFFECTS-HINT 1 (+ 1 OFFSET)
                                            STR-BYTES
                                            (X86-RUN (GC-CLK-OTHERWISE-OUT) X86))
                         (X86-RUN (LOOP-CLK 1 (+ 1 OFFSET) STR-BYTES)
                                  (X86-RUN (GC-CLK-OTHERWISE-OUT) X86))))
             (EQUAL (LOOP-EFFECTS-HINT 1 (+ 1 OFFSET)
                                       STR-BYTES
                                       (X86-RUN (GC-CLK-OTHERWISE-OUT) X86))
                    (X86-RUN (BINARY-CLK+ (GC-CLK-OTHERWISE-OUT)
                                          (LOOP-CLK 1 (+ 1 OFFSET) STR-BYTES))
                             X86)))
    :hints (("Goal" :in-theory (e/d* (GC-CLK-OTHERWISE-OUT
                                      (GC-CLK-OTHERWISE-OUT)
                                      GC-CLK-NO-EOF
                                      (GC-CLK-NO-EOF)
                                      GC-CLK
                                      (GC-CLK)))))))

 (local
  (defthm |Subgoal *1/4.2|
    (IMPLIES (AND (EOF-TERMINATEDP STR-BYTES)
                  (< OFFSET (LEN STR-BYTES))
                  (NATP OFFSET)
                  (EQUAL (CAR (GRAB-BYTES (LIST (NTH OFFSET STR-BYTES))))
                         9)
                  (EQUAL (LOOP-EFFECTS-HINT 0 (+ 1 OFFSET)
                                            STR-BYTES (X86-RUN (GC-CLK-TAB) X86))
                         (X86-RUN (LOOP-CLK 0 (+ 1 OFFSET) STR-BYTES)
                                  (X86-RUN (GC-CLK-TAB) X86))))
             (EQUAL (LOOP-EFFECTS-HINT 0 (+ 1 OFFSET)
                                       STR-BYTES (X86-RUN (GC-CLK-TAB) X86))
                    (X86-RUN (BINARY-CLK+ (GC-CLK-TAB)
                                          (LOOP-CLK 0 (+ 1 OFFSET) STR-BYTES))
                             X86)))
    :hints (("Goal" :in-theory (e/d* (GC-CLK-TAB
                                      (GC-CLK-TAB)
                                      GC-CLK-NO-EOF
                                      (GC-CLK-NO-EOF)
                                      GC-CLK
                                      (GC-CLK)))))))

 (local
  (defthm |Subgoal *1/4''|
    (IMPLIES
     (AND (EOF-TERMINATEDP STR-BYTES)
          (< OFFSET (LEN STR-BYTES))
          (NATP OFFSET)
          (EQUAL (CAR (GRAB-BYTES (LIST (NTH OFFSET STR-BYTES))))
                 32)
          (EQUAL (LOOP-EFFECTS-HINT 0 (+ 1 OFFSET)
                                    STR-BYTES (X86-RUN (GC-CLK-SPACE) X86))
                 (X86-RUN (LOOP-CLK 0 (+ 1 OFFSET) STR-BYTES)
                          (X86-RUN (GC-CLK-SPACE) X86))))
     (EQUAL (LOOP-EFFECTS-HINT 0 (+ 1 OFFSET)
                               STR-BYTES (X86-RUN (GC-CLK-SPACE) X86))
            (X86-RUN (BINARY-CLK+ (GC-CLK-SPACE)
                                  (LOOP-CLK 0 (+ 1 OFFSET) STR-BYTES))
                     X86)))
    :hints (("Goal" :in-theory (e/d* (GC-CLK-SPACE
                                      (GC-CLK-SPACE)
                                      GC-CLK-NO-EOF
                                      (GC-CLK-NO-EOF)
                                      GC-CLK
                                      (GC-CLK)))))))

 (local
  (defthm |Subgoal *1/2.5''|
    (IMPLIES
     (AND
      (EQUAL (LEN STR-BYTES) (+ 1 OFFSET))
      (EOF-TERMINATEDP STR-BYTES)
      (< OFFSET (LEN STR-BYTES))
      (NATP OFFSET)
      (NOT (EQUAL (CAR (GRAB-BYTES (LIST (NTH OFFSET STR-BYTES))))
                  35))
      (<= (LEN STR-BYTES) (LEN STR-BYTES))
      (NOT (EQUAL (CAR (GRAB-BYTES (ACL2::LIST-FIX (NTHCDR OFFSET STR-BYTES))))
                  35))
      (NOT (EQUAL (CAR (GRAB-BYTES (ACL2::LIST-FIX (NTHCDR OFFSET STR-BYTES))))
                  10))
      (NOT (EQUAL (CAR (GRAB-BYTES (ACL2::LIST-FIX (NTHCDR OFFSET STR-BYTES))))
                  32))
      (NOT (EQUAL (CAR (GRAB-BYTES (ACL2::LIST-FIX (NTHCDR OFFSET STR-BYTES))))
                  9)))
     (EQUAL (X86-RUN (GC-CLK-OTHERWISE-OUT) X86)
            (X86-RUN (BINARY-CLK+ (GC-CLK-OTHERWISE-OUT) 0)
                     X86)))
    :hints (("Goal" :in-theory (e/d* (BINARY-CLK+)
                                     ())))))


 (local
  (defthm |Subgoal *1/2.4''|
    (IMPLIES
     (AND
      (EQUAL (LEN STR-BYTES) (+ 1 OFFSET))
      (EOF-TERMINATEDP STR-BYTES)
      (< OFFSET (LEN STR-BYTES))
      (NATP OFFSET)
      (NOT (EQUAL (CAR (GRAB-BYTES (LIST (NTH OFFSET STR-BYTES))))
                  35))
      (<= (LEN STR-BYTES) (LEN STR-BYTES))
      (NOT (EQUAL (CAR (GRAB-BYTES (ACL2::LIST-FIX (NTHCDR OFFSET STR-BYTES))))
                  35))
      (NOT (EQUAL (CAR (GRAB-BYTES (ACL2::LIST-FIX (NTHCDR OFFSET STR-BYTES))))
                  10))
      (NOT (EQUAL (CAR (GRAB-BYTES (ACL2::LIST-FIX (NTHCDR OFFSET STR-BYTES))))
                  32))
      (NOT (EQUAL (CAR (GRAB-BYTES (ACL2::LIST-FIX (NTHCDR OFFSET STR-BYTES))))
                  9))
      (NOT (EQUAL WORD-STATE 0)))
     (EQUAL (X86-RUN (GC-CLK-OTHERWISE-IN) X86)
            (X86-RUN (BINARY-CLK+ (GC-CLK-OTHERWISE-IN) 0)
                     X86)))
    :hints (("Goal" :in-theory (e/d* (BINARY-CLK+)
                                     ())))))

 (local
  (defthm |Subgoal *1/2.3''|
    (IMPLIES
     (AND (EQUAL (LEN STR-BYTES) (+ 1 OFFSET))
          (EOF-TERMINATEDP STR-BYTES)
          (< OFFSET (LEN STR-BYTES))
          (NATP OFFSET)
          (NOT (EQUAL (CAR (GRAB-BYTES (LIST (NTH OFFSET STR-BYTES))))
                      35))
          (<= (LEN STR-BYTES) (LEN STR-BYTES))
          (EQUAL (CAR (GRAB-BYTES (ACL2::LIST-FIX (NTHCDR OFFSET STR-BYTES))))
                 32))
     (EQUAL (X86-RUN (GC-CLK-SPACE) X86)
            (X86-RUN (BINARY-CLK+ (GC-CLK-SPACE) 0)
                     X86)))
    :hints (("Goal" :in-theory (e/d* (BINARY-CLK+)
                                     ())))))

 (local
  (defthm |Subgoal *1/2.2''|
    (IMPLIES
     (AND (EQUAL (LEN STR-BYTES) (+ 1 OFFSET))
          (EOF-TERMINATEDP STR-BYTES)
          (< OFFSET (LEN STR-BYTES))
          (NATP OFFSET)
          (NOT (EQUAL (CAR (GRAB-BYTES (LIST (NTH OFFSET STR-BYTES))))
                      35))
          (<= (LEN STR-BYTES) (LEN STR-BYTES))
          (EQUAL (CAR (GRAB-BYTES (ACL2::LIST-FIX (NTHCDR OFFSET STR-BYTES))))
                 10))
     (EQUAL (X86-RUN (GC-CLK-NEWLINE) X86)
            (X86-RUN (BINARY-CLK+ (GC-CLK-NEWLINE) 0)
                     X86)))
    :hints (("Goal" :in-theory (e/d* (BINARY-CLK+)
                                     ())))))

 (local
  (defthm |Subgoal *1/2.1''|
    (IMPLIES
     (AND (EQUAL (LEN STR-BYTES) (+ 1 OFFSET))
          (EOF-TERMINATEDP STR-BYTES)
          (< OFFSET (LEN STR-BYTES))
          (NATP OFFSET)
          (NOT (EQUAL (CAR (GRAB-BYTES (LIST (NTH OFFSET STR-BYTES))))
                      35))
          (<= (LEN STR-BYTES) (LEN STR-BYTES))
          (EQUAL (CAR (GRAB-BYTES (ACL2::LIST-FIX (NTHCDR OFFSET STR-BYTES))))
                 9))
     (EQUAL (X86-RUN (GC-CLK-TAB) X86)
            (X86-RUN (BINARY-CLK+ (GC-CLK-TAB) 0)
                     X86)))
    :hints (("Goal" :in-theory (e/d* (BINARY-CLK+)
                                     ())))))

 (defthm loop-effects-hint-and-loop-clk
   (implies (and (eof-terminatedp str-bytes)
                 (< offset (len str-bytes))
                 (natp offset))
            (equal (loop-effects-hint word-state offset str-bytes x86)
                   (x86-run (loop-clk word-state offset str-bytes) x86)))
   :hints (("Goal" :in-theory (e/d* (loop-clk) ()))))

 ) ;; End of encapsulate

(defthm effects-loop
  ;; Begins at (call GC)
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (equal old-word-state (combine-bytes (word-state x86 x86)))
                (equal offset (offset x86))
                (equal str-bytes (input x86)))
           (equal (x86-run (loop-clk old-word-state offset str-bytes) x86)
                  (loop-effects-hint old-word-state offset str-bytes x86)))
  :hints (("Goal"
           :use ((:instance loop-effects-hint-and-loop-clk
                            (str-bytes (string-to-bytes
                                        (cdr (assoc :contents
                                                    (read-x86-file-contents
                                                     (cdr (assoc :name (read-x86-file-des 0 x86))) x86)))))
                            (offset (cdr (assoc-equal :offset (read-x86-file-des 0 x86))))
                            (word-state (combine-bytes (word-state x86 x86)))
                            (x86 x86)))
           :in-theory (e/d* (loop-preconditions
                             env-assumptions)
                            (loop-effects-hint-and-loop-clk
                             rb-in-terms-of-rb-subset-p
                             combine-bytes-rb-in-terms-of-rb-subset-p)))))

;; ======================================================================
;; ======================================================================

;;**********************************************************************
;; Behavior and Intention
;;**********************************************************************

;; Intention:

(encapsulate
 ()

 (local (include-book "std/lists/nthcdr" :dir :system))

 (defun nc-algo (offset str-bytes nc)
   (declare (xargs :measure
                   (len (nthcdr offset str-bytes))))

   (if (and (eof-terminatedp str-bytes)
            (< offset (len str-bytes))
            (natp offset))

       (b* ((c (get-char offset str-bytes))
            ((when (equal c *eof*)) nc)
            (new-nc (loghead 32 (1+ nc))))
           (nc-algo (1+ offset) str-bytes new-nc))

     nc))

 (defun nl-algo (offset str-bytes nl)
   (declare (xargs :measure
                   (len (nthcdr offset str-bytes))))

   (if (and (eof-terminatedp str-bytes)
            (< offset (len str-bytes))
            (natp offset))

       (b* ((c (get-char offset str-bytes))
            ((when (equal c *eof*)) nl)
            (new-nl (if (equal c *newline*)
                        (loghead 32 (1+ nl))
                      nl)))
           (nl-algo (1+ offset) str-bytes new-nl))

     nl))

 (defun nw-algo (offset str-bytes word-state nw)
   (declare (xargs :measure
                   (len (nthcdr offset str-bytes))))

   (if (and (eof-terminatedp str-bytes)
            (< offset (len str-bytes))
            (natp offset))

       (b* ((c (get-char offset str-bytes))
            ((when (equal c *eof*)) nw)

            ((mv new-nw new-word-state)
             (if (equal c *newline*)
                 (mv nw *out*)
               (if (equal c *space*)
                   (mv nw *out*)
                 (if (equal c *tab*)
                     (mv nw *out*)
                   (if (equal word-state *out*)
                       (mv (loghead 32 (1+ nw)) *in*)
                     (mv nw word-state)))))))

           (nw-algo (1+ offset) str-bytes new-word-state new-nw))

     nw))

 ) ;; End of encapsulate

(deftheory effects-loop-rules

  '(
    ;; Needed to resolve hyps of the form
    ;; (equal (word-state x86 ...) (byte-ify 4 *out*))
    ;; with
    ;; (equal (combine-bytes (word-state x86 ...)) *out*)
    combine-bytes

    ;; EOF Encountered:
    effects-eof-encountered-rsp-projection
    effects-eof-encountered-rbp-projection
    x86p-effects-eof-encountered
    effects-eof-encountered-msri-projection
    effects-eof-encountered-rip-projection
    effects-eof-encountered-env-stdin-des-projection
    effects-eof-encountered-env-stdin-contents-projection
    effects-eof-encountered-ms-projection
    effects-eof-encountered-fault-projection

    ;; loop-preconditions as loop invariant when EOF is not encountered...
    loop-preconditions-newline-encountered
    effects-newline-encountered-input-projection
    effects-newline-encountered-offset-projection
    loop-preconditions-space-encountered
    effects-space-encountered-input-projection
    effects-space-encountered-offset-projection
    loop-preconditions-tab-encountered
    effects-tab-encountered-input-projection
    effects-tab-encountered-offset-projection
    loop-preconditions-other-char-encountered-state-out
    effects-other-char-encountered-state-out-input-projection
    effects-other-char-encountered-state-out-offset-projection
    loop-preconditions-other-char-encountered-state-in
    effects-other-char-encountered-state-in-input-projection
    effects-other-char-encountered-state-in-offset-projection


    ;; Delta-variable theorems:

    effects-eof-encountered-variables-state
    effects-eof-encountered-variables-nc
    effects-eof-encountered-variables-nl
    effects-eof-encountered-variables-nw

    effects-newline-encountered-variables-state
    effects-newline-encountered-variables-nc
    effects-newline-encountered-variables-nl
    effects-newline-encountered-variables-nw
    effects-newline-encountered-variables-state-in-terms-of-next-x86
    effects-newline-encountered-variables-nc-in-terms-of-next-x86
    effects-newline-encountered-variables-nw-in-terms-of-next-x86
    effects-newline-encountered-variables-nl-in-terms-of-next-x86

    effects-space-encountered-variables-state
    effects-space-encountered-variables-nc
    effects-space-encountered-variables-nl
    effects-space-encountered-variables-nw
    effects-space-encountered-variables-state-in-terms-of-next-x86
    effects-space-encountered-variables-nc-in-terms-of-next-x86
    effects-space-encountered-variables-nw-in-terms-of-next-x86
    effects-space-encountered-variables-nl-in-terms-of-next-x86

    effects-tab-encountered-variables-state
    effects-tab-encountered-variables-nc
    effects-tab-encountered-variables-nl
    effects-tab-encountered-variables-nw
    effects-tab-encountered-variables-state-in-terms-of-next-x86
    effects-tab-encountered-variables-nc-in-terms-of-next-x86
    effects-tab-encountered-variables-nw-in-terms-of-next-x86
    effects-tab-encountered-variables-nl-in-terms-of-next-x86


    effects-other-char-encountered-state-out-variables-state
    effects-other-char-encountered-state-out-variables-nc
    effects-other-char-encountered-state-out-variables-nw
    effects-other-char-encountered-state-out-variables-nl
    effects-other-char-encountered-state-out-variables-state-in-terms-of-next-x86
    effects-other-char-encountered-state-out-variables-nc-in-terms-of-next-x86
    effects-other-char-encountered-state-out-variables-nw-in-terms-of-next-x86
    effects-other-char-encountered-state-out-variables-nl-in-terms-of-next-x86

    effects-other-char-encountered-state-in-variables-state
    effects-other-char-encountered-state-in-variables-nc
    effects-other-char-encountered-state-in-variables-nw
    effects-other-char-encountered-state-in-variables-nl
    effects-other-char-encountered-state-in-variables-state-in-terms-of-next-x86
    effects-other-char-encountered-state-in-variables-nc-in-terms-of-next-x86
    effects-other-char-encountered-state-in-variables-nw-in-terms-of-next-x86
    effects-other-char-encountered-state-in-variables-nl-in-terms-of-next-x86

    ))

(defthm effects-loop-nc
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (equal offset (offset x86))
                (equal str-bytes (input x86))
                (equal old-word-state (combine-bytes (word-state x86 x86)))
                (equal old-nc (combine-bytes (nc x86 x86))))
           (equal (combine-bytes
                   (nc x86 (loop-effects-hint old-word-state offset str-bytes x86)))
                  (nc-algo offset str-bytes old-nc)))
  :hints (("Goal"
           :induct (cons (nc-algo offset str-bytes old-nc)
                         (loop-effects-hint old-word-state offset str-bytes x86))
           :in-theory (union-theories
                       '(effects-loop-rules
                         nc-algo
                         loop-effects-hint)
                       (theory 'minimal-theory)))))


(defthm effects-loop-nl
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (equal offset (offset x86))
                (equal str-bytes (input x86))
                (equal old-word-state (combine-bytes (word-state x86 x86)))
                (equal old-nl (combine-bytes (nl x86 x86))))
           (equal (combine-bytes
                   (nl x86
                       (loop-effects-hint old-word-state offset str-bytes x86)))
                  (nl-algo offset str-bytes old-nl)))
  :hints (("Goal"
           :induct (cons (nl-algo offset str-bytes old-nl)
                         (loop-effects-hint old-word-state offset
                                            str-bytes x86))
           :in-theory (union-theories
                       '(effects-loop-rules
                         nl-algo
                         loop-effects-hint)
                       (theory 'minimal-theory)))))

(encapsulate
 ()

 (local (include-book "std/lists/nthcdr" :dir :system))

 (defun-nx nw-hint (x86 word-state offset str-bytes nw)
   (declare (xargs :measure (len (nthcdr offset str-bytes))))

   (if (and (eof-terminatedp str-bytes)
            (< offset (len str-bytes))
            (natp offset))

       (let ((char (get-char offset str-bytes)))

         (if (equal char #.*eof*)

             (let ((x86 (x86-run (gc-clk-eof) x86)))
               (mv nw word-state x86))

           (b* (((mv word-state x86 nw)
                 (if (equal char *newline*)
                     (b* ((x86 (x86-run (gc-clk-newline) x86)))
                         (mv 0 x86 nw))
                   (if (equal char *space*)
                       (b* ((x86 (x86-run (gc-clk-space) x86)))
                           (mv 0 x86 nw))
                     (if (equal char *tab*)
                         (b* ((x86 (x86-run (gc-clk-tab) x86)))
                             (mv 0 x86 nw))
                       (if (equal word-state #.*out*)
                           (b* ((x86 (x86-run (gc-clk-otherwise-out) x86)))
                               (mv 1 x86 (loghead 32 (1+ nw))))
                         (b* ((x86 (x86-run (gc-clk-otherwise-in) x86)))
                             (mv word-state x86 nw))))))))

               (nw-hint x86 word-state (1+ offset) str-bytes nw))))

     (mv nw word-state x86)))

 ) ;; End of encapsulate

(defthm effects-loop-nw
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (equal offset (offset x86))
                (equal str-bytes (input x86))
                (equal old-word-state
                       (combine-bytes (word-state x86 x86)))
                (equal old-nw
                       (combine-bytes (nw x86 x86))))
           (equal (combine-bytes
                   (nw x86
                       (loop-effects-hint old-word-state offset str-bytes x86)))
                  (nw-algo offset str-bytes old-word-state old-nw)))
  :hints (("Goal"
           :induct
           (nw-hint x86 old-word-state offset str-bytes old-nw)
           :in-theory (union-theories
                       '(effects-loop-rules
                         nw-algo nw-hint
                         loop-effects-hint)
                       (theory 'minimal-theory)))))

;;**********************************************************************
;; Loop behavior in terms of nc, nw, and nl
;;**********************************************************************

(defthm loop-behavior-nc
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (equal offset (offset x86))
                (equal str-bytes (input x86))
                (equal old-word-state
                       (combine-bytes (word-state x86 x86)))
                (equal old-nc
                       (combine-bytes (nc x86 x86))))
           (equal (combine-bytes
                   (nc
                    x86
                    (x86-run (loop-clk old-word-state offset str-bytes) x86)))
                  (nc-algo offset str-bytes old-nc)))
  :hints (("Goal" :in-theory (union-theories
                              '(effects-loop
                                effects-loop-nc)
                              (theory 'minimal-theory)))))

(defthm loop-behavior-nw
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (equal offset (offset x86))
                (equal str-bytes (input x86))
                (equal old-word-state
                       (combine-bytes (word-state x86 x86)))
                (equal old-nw
                       (combine-bytes (nw x86 x86))))
           (equal (combine-bytes
                   (nw
                    x86
                    (x86-run (loop-clk old-word-state offset str-bytes) x86)))
                  (nw-algo offset str-bytes old-word-state old-nw)))
  :hints (("Goal" :in-theory (union-theories
                              '(effects-loop
                                effects-loop-nw)
                              (theory 'minimal-theory)))))

(defthm loop-behavior-nl
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (equal offset (offset x86))
                (equal str-bytes (input x86))
                (equal old-word-state
                       (combine-bytes (word-state x86 x86)))
                (equal old-nl
                       (combine-bytes (nl x86 x86))))
           (equal (combine-bytes
                   (nl
                    x86
                    (x86-run (loop-clk old-word-state offset str-bytes) x86)))
                  (nl-algo offset str-bytes old-nl)))
  :hints (("Goal" :in-theory (union-theories
                              '(effects-loop
                                effects-loop-nl)
                              (theory 'minimal-theory)))))

;;**********************************************************************
;; Program Correctness
;;**********************************************************************

(deftheory main-and-gc-composition-rules
  '(x86p-effects-to-gc

    effects-to-gc-rsp-projection
    effects-to-gc-rbp-projection
    effects-to-gc-msri-projection
    effects-to-gc-ms-projection
    effects-to-gc-fault-projection
    effects-to-gc-rip-projection
    effects-to-gc-program-projection
    effects-to-gc-env-assumptions-projection

    effects-to-gc-variables-state
    effects-to-gc-variables-nc
    effects-to-gc-variables-nl
    effects-to-gc-variables-nw))

(defthm effects-wc-1
  (implies (and (bind-free '((addr . addr)) (addr))
                (preconditions addr x86)
                (equal offset (offset x86))
                (equal str-bytes (input x86)))
           (equal (x86-run (clock str-bytes x86) x86)
                  (x86-run (loop-clk 0 offset str-bytes)
                           (x86-run (gc-clk-main-before-call) x86))))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (union-theories
                       '(preconditions
                         offset
                         input
                         get-char
                         rgfi-is-i64p
                         effects-to-gc-no-call
                         effects-loop
                         clock
                         gc-clk-main-before-call
                         (len))
                       (theory 'minimal-theory)))
          ("Subgoal 4" :in-theory (union-theories
                                   '(natp
                                     natp-loop-clk)
                                   (theory 'minimal-theory))
           :use ((:instance x86-run-plus
                            (n1 10)
                            (n2
                             (loop-clk
                              0
                              (cdr (assoc-equal :offset (read-x86-file-des 0 x86)))
                              (string-to-bytes
                               (cdr
                                (assoc-equal
                                 :contents (read-x86-file-contents
                                            (cdr (assoc-equal :name (read-x86-file-des 0 x86)))
                                            x86)))))))))
          ("Subgoal 3" :in-theory (union-theories
                                   '(x86-run-opener-not-ms-not-fault-zp-n
                                     env-assumptions)
                                   (theory 'minimal-theory)))
          ("Subgoal 2" :in-theory (union-theories
                                   '(natp
                                     natp-loop-clk)
                                   (theory 'minimal-theory))
           :use ((:instance x86-run-plus
                            (n1 10)
                            (n2
                             (loop-clk
                              0
                              (cdr (assoc-equal :offset (read-x86-file-des 0 x86)))
                              (string-to-bytes
                               (cdr
                                (assoc-equal
                                 :contents (read-x86-file-contents
                                            (cdr (assoc-equal :name (read-x86-file-des 0 x86)))
                                            x86)))))))))
          ("Subgoal 1" :in-theory (union-theories
                                   '(x86-run-opener-not-ms-not-fault-zp-n
                                     env-assumptions)
                                   (theory 'minimal-theory)))))

(defthm effects-wc-2
  (implies (and (bind-free '((addr . addr)) (addr))
                (preconditions addr x86)
                (equal offset (offset x86))
                (equal str-bytes (input x86)))
           (equal (x86-run (loop-clk 0 offset str-bytes) (x86-run (gc-clk-main-before-call) x86))
                  (loop-effects-hint 0 offset str-bytes (x86-run (gc-clk-main-before-call) x86))))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (union-theories
                       '(main-and-gc-composition-rules
                         combine-bytes
                         (logior)
                         (ash)
                         preconditions-fwd-chaining-essentials
                         loop-preconditions-fwd-chaining-essentials
                         rgfi-is-i64p
                         word-state
                         effects-to-gc-rbp-projection
                         (len) (byte-ify)
                         effects-to-gc-programmer-level-mode-projection
                         effects-to-gc-input-projection
                         effects-to-gc-offset-projection
                         loop-preconditions-effects-to-gc
                         acl2::fold-consts-in-+)
                       (theory 'minimal-theory))
           :use ((:instance effects-loop
                            (x86 (x86-run (gc-clk-main-before-call) x86))
                            (offset (offset (x86-run (gc-clk-main-before-call) x86)))
                            (str-bytes (input (x86-run (gc-clk-main-before-call) x86)))
                            (old-word-state 0))
                 (:instance effects-to-gc-variables-state)))))

(defthm effects-wc
  (implies (and (bind-free '((addr . addr)) (addr))
                (preconditions addr x86)
                (equal offset (offset x86))
                (equal str-bytes (input x86)))
           (equal (x86-run (clock str-bytes x86) x86)
                  (loop-effects-hint 0 offset str-bytes
                                     (x86-run (gc-clk-main-before-call) x86))))

  :hints (("Goal" :do-not '(preprocess)
           :in-theory (union-theories
                       '(effects-wc-1
                         effects-wc-2)
                       (theory 'minimal-theory)))))

(defthm wc-effects-nc
  (implies (and (bind-free '((addr . addr)) (addr))
                (preconditions addr x86)
                (equal offset (offset x86))
                (equal str-bytes (input x86)))
           (equal (combine-bytes
                   (program-nc
                    x86
                    (loop-effects-hint 0 offset str-bytes
                                       (x86-run (gc-clk-main-before-call) x86))))
                  (nc-algo offset str-bytes 0)))
  :hints (("Goal"
           :in-theory (union-theories
                       '(rgfi-is-i64p
                         combine-bytes
                         (logior)
                         (ash)
                         main-and-gc-composition-rules
                         nc
                         program-nc
                         word-state
                         acl2::fold-consts-in-+
                         effects-to-gc-variables-state
                         effects-to-gc-variables-nc
                         x86p-effects-to-gc
                         (len) (byte-ify)
                         preconditions-fwd-chaining-essentials
                         effects-to-gc-input-projection
                         effects-to-gc-offset-projection
                         effects-to-gc-programmer-level-mode-projection
                         loop-preconditions-effects-to-gc)
                       (theory 'minimal-theory))
           :use ((:instance effects-loop-nc
                            (x86 (x86-run (gc-clk-main-before-call) x86))
                            (old-word-state 0)
                            (old-nc 0))
                 (:instance effects-to-gc-variables-nc)
                 (:instance effects-to-gc-variables-state)))))

(defthm wc-effects-nw
  (implies (and (bind-free '((addr . addr)) (addr))
                (preconditions addr x86)
                (equal offset (offset x86))
                (equal str-bytes (input x86)))
           (equal (combine-bytes
                   (program-nw
                    x86
                    (loop-effects-hint 0 offset str-bytes
                                       (x86-run (gc-clk-main-before-call) x86))))
                  (nw-algo offset str-bytes 0 0)))
  :hints (("Goal"
           :in-theory (union-theories
                       '(rgfi-is-i64p
                         combine-bytes
                         (logior)
                         (ash) (byte-ify)
                         main-and-gc-composition-rules
                         nw
                         program-nw
                         word-state
                         acl2::fold-consts-in-+
                         effects-to-gc-variables-state
                         effects-to-gc-variables-nc
                         x86p-effects-to-gc
                         (len)
                         preconditions-fwd-chaining-essentials
                         effects-to-gc-input-projection
                         effects-to-gc-offset-projection
                         effects-to-gc-programmer-level-mode-projection
                         loop-preconditions-effects-to-gc)
                       (theory 'minimal-theory))
           :use ((:instance effects-loop-nw
                            (x86 (x86-run (gc-clk-main-before-call) x86))
                            (old-word-state 0)
                            (old-nw 0))
                 (:instance effects-to-gc-variables-state)
                 (:instance effects-to-gc-variables-nw)))))

(defthm wc-effects-nl
  (implies (and (bind-free '((addr . addr)) (addr))
                (preconditions addr x86)
                (equal offset (offset x86))
                (equal str-bytes (input x86)))
           (equal (combine-bytes
                   (program-nl
                    x86
                    (loop-effects-hint 0 offset str-bytes
                                       (x86-run (gc-clk-main-before-call) x86))))
                  (nl-algo offset str-bytes 0)))
  :hints (("Goal"
           :in-theory (union-theories
                       '(rgfi-is-i64p
                         combine-bytes
                         (logior)
                         (ash) (byte-ify)
                         main-and-gc-composition-rules
                         nl
                         program-nl
                         word-state
                         acl2::fold-consts-in-+
                         effects-to-gc-variables-state
                         effects-to-gc-variables-nc
                         x86p-effects-to-gc
                         (len)
                         preconditions-fwd-chaining-essentials
                         effects-to-gc-input-projection
                         effects-to-gc-offset-projection
                         effects-to-gc-programmer-level-mode-projection
                         loop-preconditions-effects-to-gc)
                       (theory 'minimal-theory))
           :use ((:instance effects-loop-nl
                            (x86 (x86-run (gc-clk-main-before-call) x86))
                            (old-word-state 0)
                            (old-nl 0))
                 (:instance effects-to-gc-variables-state)
                 (:instance effects-to-gc-variables-nl)))))


;; **********************************************************************

;; RIP and MS of the halt state:

(defthm rip-effects-loop
  ;; Begins at (call GC)
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (equal old-word-state
                       (combine-bytes (word-state x86 x86)))
                (equal offset (offset x86))
                (equal str-bytes (input x86)))
           (equal (xr :rip 0 (loop-effects-hint old-word-state offset str-bytes x86))
                  (+ 164 addr)))

  :hints (("Goal"
           :induct (loop-effects-hint old-word-state offset str-bytes x86)
           :in-theory (union-theories
                       '(effects-loop-rules
                         rgfi-is-i64p
                         loop-effects-hint
                         (len))
                       (theory 'minimal-theory)))
          ("Subgoal *1/3"
           :in-theory (union-theories
                       '(env-assumptions
                         eof-terminatedp
                         input
                         offset
                         file-descriptor-fieldp)
                       (theory 'minimal-theory))
           :use ((:instance loop-preconditions-fwd-chaining-essentials)))))

(defthm rip-loop-clk
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (equal word-state (combine-bytes (word-state x86 x86)))
                (equal offset (offset x86))
                (equal str-bytes (input x86)))
           (equal (xr :rip 0 (x86-run (loop-clk word-state offset str-bytes) x86))
                  (+ 164 addr)))
  :hints (("Goal"
           :in-theory (union-theories
                       '(rip-effects-loop
                         effects-loop
                         word-state)
                       (theory 'minimal-theory)))))

(defthm rip-clock
  (implies (and (preconditions addr x86)
                (equal offset (offset x86))
                (equal str-bytes (input x86)))
           (equal (xr :rip 0 (x86-run (clock str-bytes x86) x86))
                  (+ 164 addr)))
  :hints (("Goal"
           :in-theory (union-theories
                       '(effects-wc
                         combine-bytes
                         (logior)
                         (ash)
                         preconditions-fwd-chaining-essentials
                         effects-to-gc-rsp-projection
                         x86p-effects-to-gc
                         effects-to-gc-msri-projection
                         effects-to-gc-ms-projection
                         effects-to-gc-fault-projection
                         effects-to-gc-rip-projection
                         effects-to-gc-program-projection
                         effects-to-gc-env-assumptions-projection
                         word-state
                         (len) (byte-ify)
                         acl2::fold-consts-in-+
                         effects-to-gc-rbp-projection
                         effects-to-gc-input-projection
                         effects-to-gc-offset-projection
                         effects-to-gc-programmer-level-mode-projection
                         loop-preconditions-effects-to-gc
                         rip-effects-loop)
                       (theory 'minimal-theory))
           :use ((:instance effects-to-gc-variables-state)))))


(defthm ms-effects-loop
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (equal old-word-state
                       (combine-bytes (word-state x86 x86)))
                (equal offset (offset x86))
                (equal str-bytes (input x86)))
           (equal (xr :ms 0 (loop-effects-hint old-word-state offset str-bytes x86))
                  nil))
  :hints (("Goal"
           :induct (loop-effects-hint old-word-state offset str-bytes
                                      x86)
           :in-theory (union-theories
                       '(effects-loop-rules
                         rgfi-is-i64p
                         loop-effects-hint
                         (len))
                       (theory 'minimal-theory)))
          ("Subgoal *1/3"
           :in-theory (union-theories
                       '(env-assumptions
                         eof-terminatedp
                         input
                         offset
                         file-descriptor-fieldp)
                       (theory 'minimal-theory))
           :use ((:instance loop-preconditions-fwd-chaining-essentials)))))

(defthm ms-loop-clk
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (equal word-state
                       (combine-bytes (word-state x86 x86)))
                (equal offset (offset x86))
                (equal str-bytes (input x86)))
           (equal (xr :ms 0 (x86-run (loop-clk word-state offset str-bytes) x86))
                  nil))
  :hints (("Goal"
           :in-theory (union-theories
                       '(ms-effects-loop
                         effects-loop
                         word-state)
                       (theory 'minimal-theory)))))

(defthm ms-clock
  (implies (and (bind-free '((addr . addr)) (addr))
                (preconditions addr x86)
                (equal offset (offset x86))
                (equal str-bytes (input x86)))
           (equal (xr :ms 0 (x86-run (clock str-bytes x86) x86))
                  nil))
  :hints (("Goal"
           :in-theory (union-theories
                       '(effects-wc
                         combine-bytes
                         (logior)
                         (ash)
                         preconditions-fwd-chaining-essentials
                         effects-to-gc-rsp-projection
                         x86p-effects-to-gc
                         effects-to-gc-msri-projection
                         effects-to-gc-ms-projection
                         effects-to-gc-fault-projection
                         effects-to-gc-rip-projection
                         effects-to-gc-program-projection
                         effects-to-gc-env-assumptions-projection
                         word-state
                         (len) (byte-ify)
                         acl2::fold-consts-in-+
                         effects-to-gc-rbp-projection
                         effects-to-gc-input-projection
                         effects-to-gc-offset-projection
                         effects-to-gc-programmer-level-mode-projection
                         ms-effects-loop
                         loop-preconditions-effects-to-gc)
                       (theory 'minimal-theory))
           :use ((:instance effects-to-gc-variables-state)))))

;;**********************************************************************
;; Correctness Theorems
;;**********************************************************************

(defun nc-spec (offset str-bytes)
  (nc-algo offset str-bytes 0))

(defun nl-spec (offset str-bytes)
  (nl-algo offset str-bytes 0))

(defun nw-spec (offset str-bytes)
  (nw-algo offset str-bytes 0 0))

(defthm wc-nc
  (implies (and (preconditions addr x86)
                (equal offset (offset x86))
                (equal str-bytes (input x86)))
           (and (equal (combine-bytes
                        (program-nc
                         x86
                         (x86-run (clock str-bytes x86) x86)))
                       (nc-spec offset str-bytes))
                (equal (xr :rip 0 (x86-run (clock str-bytes x86) x86))
                       (+ 164 addr))
                (equal (xr :ms 0 (x86-run (clock str-bytes x86) x86))
                       nil)))
  :hints (("Goal"
           :in-theory (union-theories
                       '(effects-wc
                         nc-spec
                         wc-effects-nc)
                       (theory 'minimal-theory))
           :use ((:instance rip-clock)
                 (:instance ms-clock)))))

(defthm wc-nl
  (implies (and (preconditions addr x86)
                (equal offset (offset x86))
                (equal str-bytes (input x86)))
           (and (equal (combine-bytes
                        (program-nl
                         x86
                         (x86-run (clock str-bytes x86) x86)))
                       (nl-spec offset str-bytes))
                (equal (xr :rip 0 (x86-run (clock str-bytes x86) x86))
                       (+ 164 addr))
                (equal (xr :ms 0 (x86-run (clock str-bytes x86) x86))
                       nil)))
  :hints (("Goal"
           :in-theory (union-theories
                       '(effects-wc
                         nl-spec
                         wc-effects-nl)
                       (theory 'minimal-theory))
           :use ((:instance rip-clock)
                 (:instance ms-clock)))))

(defthm wc-nw
  (implies (and (preconditions addr x86)
                (equal offset (offset x86))
                (equal str-bytes (input x86)))
           (and (equal (combine-bytes
                        (program-nw
                         x86
                         (x86-run (clock str-bytes x86) x86)))
                       (nw-spec offset str-bytes))
                (equal (xr :rip 0 (x86-run (clock str-bytes x86) x86))
                       (+ 164 addr))
                (equal (xr :ms 0 (x86-run (clock str-bytes x86) x86))
                       nil)))
  :hints (("Goal"
           :in-theory (union-theories
                       '(effects-wc
                         nw-spec
                         wc-effects-nw)
                       (theory 'minimal-theory))
           :use ((:instance rip-clock)
                 (:instance ms-clock)))))

;;**********************************************************************
;;**********************************************************************

;; Memory Analysis:

(defthmd memory-analysis-effects-to-gc-no-call
  (implies (and (bind-free '((addr . addr)) (addr))
                (preconditions addr x86)
                (canonical-address-listp addresses)
                (disjoint-p
                 ;; Rest of the Memory
                 addresses
                 ;; Program Stack Space
                 (create-canonical-address-list 104 (+ (- (+ 48 8 #x20 8)) (xr :rgf *rsp* x86)))))
           (equal (mv-nth 1 (rb addresses r-w-x
                                (x86-run (gc-clk-main-before-call) x86)))
                  (mv-nth 1 (rb addresses r-w-x x86))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d* ()
                            (wb-remove-duplicate-writes force (force))))))

(defthmd memory-analysis-effects-call-gc
  (implies (and (x86p x86)
                (xr :programmer-level-mode 0 x86)
                (not (alignment-checking-enabled-p x86))
                (equal (xr :os-info 0 x86) :linux)
                (env-assumptions x86)
                (canonical-address-p (xr :rgf *rsp* x86))
                ;; Address of the call instruction in the main sub-routine
                ;; 95: Position of the call instruction in the main sub-routine
                ;; (equal (xr :rip 0 x86) (+ (1- (+ (len *gc*) 95)) addr))
                (equal addr (- (xr :rip 0 x86) (1- (+ (len *gc*) 95))))
                (canonical-address-p addr)
                (canonical-address-p (+ (1- (len *wc*)) addr))
                (canonical-address-p (+ #x20 (xr :rgf *rsp* x86)))
                (canonical-address-p (+ (- (+ 8 #x20 8)) (xr :rgf *rsp* x86)))
                ;; (+ 8 #x20 8 #x20) = 80
                (disjoint-p
                 ;; IMPORTANT: Keep the program addresses as the first
                 ;; argument.
                 (create-canonical-address-list
                  (len *wc*) addr)
                 (create-canonical-address-list
                  80 (+ (- (+ 8 #x20 8)) (xr :rgf *rsp* x86))))
                (equal (xr :ms 0 x86) nil)
                (equal (xr :fault 0 x86) nil)
                ;; Enabling the SYSCALL instruction.
                (equal (ia32_efer-slice :ia32_efer-sce (xr :msr *ia32_efer-idx* x86)) 1)
                (equal (ia32_efer-slice :ia32_efer-lma (xr :msr *ia32_efer-idx* x86)) 1)
                (program-at (create-canonical-address-list (len *wc*) addr) *wc* x86)
                (canonical-address-listp addresses)
                (disjoint-p
                 ;; Rest of the Memory
                 addresses
                 ;; Program Stack Space
                 (create-canonical-address-list
                  80 (+ (- (+ 8 #x20 8)) (xr :rgf *rsp* x86)))))
           (equal (mv-nth 1 (rb addresses r-w-x (x86-run (gc-clk) x86)))
                  (mv-nth 1 (rb addresses r-w-x x86))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d* ()
                            (wb-remove-duplicate-writes
                             force (force))))))


(defthm not-member-p-canonical-address-listp-when-disjoint-p-new
  ;; [Shilpi]: generalize...
  (implies (and (disjoint-p xs (create-canonical-address-list m addr))
                (member-p e (create-canonical-address-list m addr)))
           (equal (member-p e xs)
                  nil)))

(defthmd memory-analysis-effects-eof-encountered
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (equal (get-char (offset x86) (input x86)) *eof*)
                (canonical-address-listp addresses)
                (disjoint-p
                 ;; Rest of the Memory
                 addresses
                 ;; Program Stack Space
                 (create-canonical-address-list 80 (+ (- (+ 8 32 8)) (xr :rgf *rsp* x86)))))
           (equal (mv-nth 1 (rb addresses r-w-x (x86-run (gc-clk-eof) x86)))
                  (mv-nth 1 (rb addresses r-w-x x86))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d* ()
                            (wb-remove-duplicate-writes
                             force (force))))))

(defthmd memory-analysis-effects-newline-encountered
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (equal (get-char (offset x86) (input x86)) *newline*)
                (canonical-address-listp addresses)
                (disjoint-p
                 ;; Rest of the Memory
                 addresses
                 ;; Program Stack Space
                 (create-canonical-address-list
                  80 (+ (- (+ 8 32 8)) (xr :rgf *rsp* x86)))))
           (equal (mv-nth 1 (rb addresses r-w-x (x86-run (gc-clk-newline) x86)))
                  (mv-nth 1 (rb addresses r-w-x x86))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d* ()
                            (wb-remove-duplicate-writes
                             force (force))))))

(defthmd memory-analysis-effects-space-encountered
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (equal (get-char (offset x86) (input x86)) *space*)
                (canonical-address-listp addresses)
                (disjoint-p
                 ;; Rest of the Memory
                 addresses
                 ;; Program Stack Space
                 (create-canonical-address-list
                  80 (+ (- (+ 8 32 8)) (xr :rgf *rsp* x86)))))
           (equal (mv-nth 1 (rb addresses r-w-x (x86-run (gc-clk-space) x86)))
                  (mv-nth 1 (rb addresses r-w-x x86))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d* ()
                            (wb-remove-duplicate-writes
                             force (force))))))

(defthmd memory-analysis-effects-tab-encountered
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (equal (get-char (offset x86) (input x86)) *tab*)
                (canonical-address-listp addresses)
                (disjoint-p
                 ;; Rest of the Memory
                 addresses
                 ;; Program Stack Space
                 (create-canonical-address-list
                  80 (+ (- (+ 8 32 8)) (xr :rgf *rsp* x86)))))
           (equal (mv-nth 1 (rb addresses r-w-x
                                (x86-run (gc-clk-tab) x86)))
                  (mv-nth 1 (rb addresses r-w-x x86))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d* ()
                            (wb-remove-duplicate-writes
                             force (force))))))

(defthmd memory-analysis-effects-other-char-encountered-state-out
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (not (equal (get-char (offset x86) (input x86)) *eof*))
                (not (equal (get-char (offset x86) (input x86)) *newline*))
                (not (equal (get-char (offset x86) (input x86)) *space*))
                (not (equal (get-char (offset x86) (input x86)) *tab*))
                (equal (combine-bytes (word-state x86 x86)) *out*)

                (canonical-address-listp addresses)
                (disjoint-p
                 ;; Rest of the Memory
                 addresses
                 ;; Program Stack Space
                 (create-canonical-address-list
                  80 (+ (- (+ 8 32 8)) (xr :rgf *rsp* x86)))))
           (equal (mv-nth 1 (rb addresses r-w-x (x86-run (gc-clk-otherwise-out) x86)))
                  (mv-nth 1 (rb addresses r-w-x x86))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d* ()
                            (wb-remove-duplicate-writes
                             force (force))))))

(defthmd memory-analysis-effects-other-char-encountered-state-in
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (not (equal (get-char (offset x86) (input x86)) *eof*))
                (not (equal (get-char (offset x86) (input x86)) *newline*))
                (not (equal (get-char (offset x86) (input x86)) *space*))
                (not (equal (get-char (offset x86) (input x86)) *tab*))
                (not (equal (combine-bytes (word-state x86 x86)) *out*))

                (canonical-address-listp addresses)
                (disjoint-p
                 ;; Rest of the Memory
                 addresses
                 ;; Program Stack Space
                 (create-canonical-address-list
                  80 (+ (- (+ 8 32 8)) (xr :rgf *rsp* x86)))))
           (equal (mv-nth 1 (rb addresses r-w-x (x86-run (gc-clk-otherwise-in) x86)))
                  (mv-nth 1 (rb addresses r-w-x x86))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d* ()
                            (wb-remove-duplicate-writes
                             force (force))))))

(defthmd memory-analysis-loop
  (implies (and (bind-free '((addr . addr)) (addr))
                (loop-preconditions addr x86)
                (equal offset (offset x86))
                (equal str-bytes (input x86))
                (equal old-word-state
                       (combine-bytes (word-state x86 x86)))
                (canonical-address-listp addresses)
                (disjoint-p
                 ;; Rest of the Memory
                 addresses
                 ;; Program Stack Space
                 (create-canonical-address-list
                  80 (+ (- (+ 8 32 8)) (xr :rgf *rsp* x86)))))
           (equal (mv-nth 1 (rb addresses r-w-x (loop-effects-hint old-word-state offset str-bytes x86)))
                  (mv-nth 1 (rb addresses r-w-x x86))))
  :hints (("Goal"
           :expand (loop-effects-hint (combine-bytes (word-state x86 x86)) (offset x86) (input x86) x86)
           :in-theory (union-theories
                       '(memory-analysis-effects-to-gc-no-call
                         memory-analysis-effects-call-gc
                         memory-analysis-effects-eof-encountered
                         memory-analysis-effects-newline-encountered
                         memory-analysis-effects-space-encountered
                         memory-analysis-effects-tab-encountered
                         memory-analysis-effects-other-char-encountered-state-out
                         memory-analysis-effects-other-char-encountered-state-in

                         loop-effects-hint

                         effects-loop-rules

                         loop-preconditions-fwd-chaining-essentials
                         loop-preconditions-forward-chain-addresses-info

                         effects-to-gc-rsp-projection
                         effects-eof-encountered-rsp-projection
                         effects-eof-not-encountered-prelim-rsp-projection
                         effects-newline-encountered-rsp-projection
                         effects-space-encountered-rsp-projection
                         effects-tab-encountered-rsp-projection
                         effects-other-char-encountered-state-out-rsp-projection
                         effects-other-char-encountered-state-in-rsp-projection-new)
                       (theory 'minimal-theory)))))

(defthmd memory-analysis-loop-and-program-connection
  (implies (and (bind-free '((addr . addr)) (addr))
                (preconditions addr x86)
                (equal offset (offset x86))
                (equal str-bytes (input x86))

                (canonical-address-listp addresses)
                (disjoint-p
                 ;; Rest of the Memory
                 addresses
                 ;; Program Stack Space
                 (create-canonical-address-list
                  104 (+ (- (+ 48 8 #x20 8)) (xr :rgf *rsp* x86)))))
           (equal (mv-nth 1 (rb addresses r-w-x (loop-effects-hint 0 offset str-bytes (x86-run (gc-clk-main-before-call) x86))))
                  (mv-nth 1 (rb addresses r-w-x x86))))
  :hints
  (("Goal"
    :in-theory
    (union-theories
     '(rgfi-is-i64p combine-bytes (logior)
                    member-p-canonical-address-listp
                    not-member-p-canonical-address-listp
                    (byte-ify)
                    (ash)
                    main-and-gc-composition-rules
                    nw program-nw
                    word-state acl2::fold-consts-in-+
                    effects-to-gc-variables-state
                    effects-to-gc-variables-nc
                    x86p-effects-to-gc (len)
                    preconditions-fwd-chaining-essentials
                    effects-to-gc-input-projection
                    effects-to-gc-offset-projection
                    effects-to-gc-programmer-level-mode-projection
                    loop-preconditions-effects-to-gc
                    subset-p
                    subset-p-two-create-canonical-address-lists-general)
     (theory 'minimal-theory))
    :use ((:instance memory-analysis-loop
                     (x86 (x86-run (gc-clk-main-before-call) x86))
                     (old-word-state 0))
          (:instance effects-to-gc-variables-state)
          (:instance memory-analysis-effects-to-gc-no-call)
          (:instance disjoint-p-subset-p
                     (a addresses)
                     (b (create-canonical-address-list 80 (+ -88 (xr :rgf *rsp* x86))))
                     (x addresses)
                     (y (create-canonical-address-list 104 (+ -96 (xr :rgf *rsp* x86)))))
          (:instance effects-to-gc-variables-nw)))
   ("Subgoal 2"
    :in-theory (e/d (subset-p) ())
    :use ((:instance disjoint-p-subset-p
                     (a addresses)
                     (b (create-canonical-address-list 80 (+ -88 (xr :rgf *rsp* x86))))
                     (x addresses)
                     (y (create-canonical-address-list 104 (+ -96 (xr :rgf *rsp* x86)))))))
   ("Subgoal 1"
    :in-theory (e/d (subset-p) ())
    :use ((:instance disjoint-p-subset-p
                     (a addresses)
                     (b (create-canonical-address-list 80 (+ -88 (xr :rgf *rsp* x86))))
                     (x addresses)
                     (y (create-canonical-address-list 104 (+ -96 (xr :rgf *rsp* x86)))))))))

(defthmd memory-analysis-program
  (implies (and (bind-free '((addr . addr)) (addr))
                (preconditions addr x86)
                (equal offset (offset x86))
                (equal str-bytes (input x86))

                (canonical-address-listp addresses)
                (disjoint-p
                 ;; Rest of the Memory
                 addresses
                 ;; Program Stack Space
                 (create-canonical-address-list
                  104 (+ (- (+ 48 8 #x20 8)) (xr :rgf *rsp* x86)))))
           (equal (mv-nth 1 (rb addresses r-w-x (x86-run (clock str-bytes x86) x86)))
                  (mv-nth 1 (rb addresses r-w-x x86))))
  :hints (("Goal" :in-theory (union-theories
                              '(memory-analysis-loop
                                memory-analysis-effects-to-gc-no-call
                                memory-analysis-loop-and-program-connection
                                effects-wc)
                              (theory 'minimal-theory)))))

;; ======================================================================
;; ======================================================================
