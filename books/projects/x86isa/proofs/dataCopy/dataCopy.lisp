;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")

(include-book "programmer-level-memory-utils" :dir :proof-utils :ttags :all)
(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "centaur/bitops/signed-byte-p" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))

;; ======================================================================

;; Here is the sub-routine:
;; void copyData (int* src, int* dst, int n) {

;;   int* dstEnd = dst + n;

;;   while (dst != dstEnd)
;;     *dst++ = *src++;

;; }

;; O1 optimization:
;; 0000000100000ed0 <_copyData>:
;;    100000ed0:	55                      push   %rbp
;;    100000ed1:	48 89 e5                mov    %rsp,%rbp
;;    100000ed4:	85 d2                   test   %edx,%edx
;;    100000ed6:	74 1a                   je     100000ef2 <_copyData+0x22>
;;    100000ed8:	48 63 c2                movslq %edx,%rax
;;    100000edb:	48 c1 e0 02             shl    $0x2,%rax
;;    100000edf:	90                      nop
;;    100000ee0:	8b 0f                   mov    (%rdi),%ecx
;;    100000ee2:	48 83 c7 04             add    $0x4,%rdi
;;    100000ee6:	89 0e                   mov    %ecx,(%rsi)
;;    100000ee8:	48 83 c6 04             add    $0x4,%rsi
;;    100000eec:	48 83 c0 fc             add    $0xfffffffffffffffc,%rax
;;    100000ef0:	75 ee                   jne    100000ee0 <_copyData+0x10>
;;    100000ef2:	5d                      pop    %rbp
;;    100000ef3:	c3                      retq

(defconst *copyData* ;; 15 instructions
  '(
    #x55                ;; push   %rbp                          1
    #x48 #x89 #xe5      ;; mov    %rsp,%rbp			2
    #x85 #xd2           ;; test   %edx,%edx			3
    #x74 #x1a           ;; je     100000ef2 <_copyData+0x22>	4
    #x48 #x63 #xc2      ;; movslq %edx,%rax			5
    #x48 #xc1 #xe0 #x02 ;; shl    $0x2,%rax			6
    #x90                ;; nop                                  7
    #x8b #x0f           ;; mov    (%rdi),%ecx			8
    #x48 #x83 #xc7 #x04 ;; add    $0x4,%rdi			9
    #x89 #x0e           ;; mov    %ecx,(%rsi)                  10
    #x48 #x83 #xc6 #x04 ;; add    $0x4,%rsi                    11
    #x48 #x83 #xc0 #xfc ;; add    $0xfffffffffffffffc,%rax     12
    #x75 #xee           ;; jne    100000ee0 <_copyData+0x10>   13
    #x5d                ;; pop    %rbp                         14
    #xc3                ;; retq                                15
    ))

;; Some important registers:

;; RDX: n
;; RSI: Destination address
;; RDI: Source address

;; ======================================================================

(defun-nx preconditions (n addr x86)
  (and (x86p x86)
       (xr :programmer-level-mode 0 x86)
       (equal (xr :ms 0 x86) nil)
       (equal (xr :fault 0 x86) nil)
       ;; We are poised to run the copyData sub-routine.
       (equal (xr :rip 0 x86) addr)
       (unsigned-byte-p 32 n)
       (equal (xr :rgf *rdx* x86) n)
       ;; All the stack addresses are canonical.
       (canonical-address-p (xr :rgf *rsp* x86))
       (canonical-address-p (+ -8 (xr :rgf *rsp* x86)))
       ;; All the destination addresses are canonical.
       (canonical-address-p (xr :rgf *rsi* x86))
       (canonical-address-p (+ (ash n 2) (xr :rgf *rsi* x86)))
       ;; All the source addresses are canonical.
       (canonical-address-p (xr :rgf *rdi* x86))
       (canonical-address-p (+ (ash n 2) (xr :rgf *rdi* x86)))
       ;; Memory locations of interest are disjoint.
       (disjoint-p
        ;; Program addresses
        (create-canonical-address-list (len *copyData*) addr)
        ;; Destination addresses
        (create-canonical-address-list (ash n 2) (xr :rgf *rsi* x86)))
       (disjoint-p
        ;; Program addresses
        (create-canonical-address-list (len *copyData*) addr)
        ;; Stack
        (create-canonical-address-list 8 (+ -8 (xr :rgf *rsp* x86))))
       (disjoint-p
        ;; Source Addresses
        (create-canonical-address-list (ash n 2) (xr :rgf *rdi* x86))
        ;; Stack
        (create-canonical-address-list 8 (+ -8 (xr :rgf *rsp* x86))))
       (disjoint-p
        ;; Destination Addresses
        (create-canonical-address-list (ash n 2) (xr :rgf *rsi* x86))
        ;; Stack
        (create-canonical-address-list 8 (+ -8 (xr :rgf *rsp* x86))))
       ;; Program is located at addr.
       ;; All program addresses are canonical.
       (canonical-address-p addr)
       (canonical-address-p (+ -1 (len *copyData*) addr))
       (program-at (create-canonical-address-list (len *copyData*) addr)
                   *copyData* x86)))

;; ======================================================================

;; Effects theorem:

(defthm effects-copyData-n=0
  (implies (preconditions 0 addr x86)
           (equal (x86-run 4 x86)
                  (XW
                   :RGF *RSP* (+ -8 (XR :RGF *RSP* X86))
                   (XW
                    :RGF *RBP* (+ -8 (XR :RGF *RSP* X86))
                    (XW
                     :RIP 0 (+ 34 (XR :RIP 0 X86))
                     (MV-NTH
                      1
                      (WB
                       (CREATE-ADDR-BYTES-ALIST
                        (CREATE-CANONICAL-ADDRESS-LIST 8 (+ -8 (XR :RGF *RSP* X86)))
                        (BYTE-IFY 8 (LOGHEAD 64 (XR :RGF *RBP* X86))))
                       (WRITE-USER-RFLAGS
                        (LOGIOR
                         4
                         (LOGAND 4294967290
                                 (LOGIOR 64
                                         (LOGAND 4294965054
                                                 (BITOPS::LOGSQUASH 1 (XR :RFLAGS 0 X86))))))
                        16 X86))))))))
  :hints (("Goal" :in-theory (e/d* (instruction-decoding-and-spec-rules

                                    gpr-and-spec-4
                                    jcc/cmovcc/setcc-spec
                                    sal/shl-spec-64

                                    opcode-execute
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
                                    ;; write-user-rflags
                                    ;; !flgi-undefined
                                    ;; !flgi
                                    ;; flgi
                                    )

                                   (wb-remove-duplicate-writes
                                    create-canonical-address-list
                                    force (force))))))

(defthm greater-logbitp-of-unsigned-byte-p
  ;; From word-count/wc.lisp
  (implies (and (unsigned-byte-p n x)
                (natp m)
                (< n m))
           (equal (logbitp m x) nil))
  :hints (("Goal" :in-theory (e/d* (ihsext-inductions
                                    ihsext-recursive-redefs
                                    unsigned-byte-p)
                                   ())))
  :rule-classes ((:rewrite)
                 (:rewrite :corollary
                           (implies (and (< x (expt 2 m))
                                         (natp x)
                                         (natp m))
                                    (equal (logbitp m x) nil)))))

#||


(i-am-here)

(local
 (encapsulate
  ()

  (local (include-book "arithmetic-3/top" :dir :system))

  (defthm ash-n-2-bound
    (implies (and (< 0 n)
                  (integerp n))
             (<= 4 (ash n 2)))
    :hints (("Goal" :in-theory (e/d* (ash) ())))
    :rule-classes (:rewrite :linear))))

;; (defun loghead-logext-of-non-zero-induct (m n x)
;;   (if (or (zp m)
;;           (zp n))
;;       (list m n x)
;;     (loghead-logext-of-non-zero-induct (1- m) (1- n) (logcdr x))))

;; (defthm loghead-logext-of-non-zero
;;   (implies (and (unsigned-byte-p n rdx)
;;                 (< 0 rdx)
;;                 (natp m)
;;                 (<= n m))
;;            (equal (equal (loghead m (logext n rdx)) 0)
;;                   nil))
;;   :hints (("Goal"
;;            :induct (loghead-logext-of-non-zero-induct m n rdx)
;;            :in-theory (e/d* (ihsext-recursive-redefs
;;                              ihsext-inductions)
;;                             ()))))

;; (defthm ash-non-zero
;;   (implies (and (not (equal x 0))
;;                 (integerp x)
;;                 (natp n))
;;            (equal (equal (ash x n) 0) nil))
;;   :hints (("Goal" :in-theory (e/d* (ihsext-inductions
;;                                     ihsext-recursive-redefs)
;;                                    ()))))

;; (defthm ash-loghead-logext-of-non-zero
;;   (implies (and (unsigned-byte-p n rdx)
;;                 (< 0 rdx)
;;                 (natp m)
;;                 (<= n m)
;;                 (natp p))
;;            (equal (equal (ash (loghead m (logext n rdx)) p) 0)
;;                   nil)))

(defthm canonical-address-p-limits-thm-0-free-var-problem ;; UGH
  ;; This isn't a very helpful rule --- it has rdx as a free-var too.
  (implies (and (syntaxp (quotep n))
                (canonical-address-p (+ rdi (ash rdx 2)))
                (canonical-address-p rdi)
                (integerp rdx)
                (natp n)
                (< n (ash rdx 2))
                (< 0 rdx))
           (canonical-address-p (+ n rdi)))
  :hints (("Goal" :in-theory (e/d* () (canonical-address-p-limits-thm-0))
           :use ((:instance canonical-address-p-limits-thm-0
                            (i (ash rdx 2))
                            (addr rdi)
                            (k n))))))

(acl2::why rb-wb-disjoint)

(acl2::why disjoint-p-subset-p)

(defthm foo
  ;; I'm having trouble with these annoying kind of hyps, because of ash.
  ;; And ugh, free variables. See bar for the core of this problem.
  ;; This is after we know
  ;; (DISJOINT-P (CREATE-CANONICAL-ADDRESS-LIST (ASH (XR :RGF *RDX* X86) 2)
  ;;                                            (XR :RGF *RDI* X86))
  ;;             (CREATE-CANONICAL-ADDRESS-LIST 8 (+ -8 (XR :RGF *RSP* X86))))
  ;; See rule disjoint-p-subset-p.
  ;; Can't establish
  ;; (subset-p (create-canonical-address-list 4 (xr :rgf *rdi* x86))
  ;;           (create-canonical-address-list (ash (xr :rgf *rdx* x86) 2) (xr :rgf *rdi* x86)))
  ;; See subset-p-two-create-canonical-address-lists.
  (implies (and (preconditions n addr x86)
                (posp n))
           (disjoint-p
            (create-canonical-address-list 4 (xr :rgf *rdi* x86))
            (create-canonical-address-list 8 (+ -8 (xr :rgf *rsp* x86))))))

(defthm bar
  ;; See subset-p-two-create-canonical-address-lists and
  ;; canonical-address-p-limits-thm-1.
  (implies (and (preconditions n addr x86)
                (posp n))
           (subset-p
            (create-canonical-address-list 4 (xr :rgf *rdi* x86))
            (create-canonical-address-list (ash (xr :rgf *rdx* x86) 2) (xr :rgf *rdi* x86)))))

(defthm effects-copyData-n!=0-helper
  (implies (and (preconditions n addr x86)
                (posp n))
           (equal (MV-NTH
                   '1
                   (RB
                    (CONS (BINARY-+ '24 (XR ':RIP '0 X86))
                          'NIL)
                    ':X
                    (MV-NTH
                     '1
                     (WB
                      (BINARY-APPEND
                       (CREATE-ADDR-BYTES-ALIST
                        (CREATE-CANONICAL-ADDRESS-LIST '8
                                                       (BINARY-+ '-8 (XR ':RGF '4 X86)))
                        (BYTE-IFY '8
                                  (ACL2::LOGHEAD$INLINE '64
                                                        (XR ':RGF '5 X86))))
                       (CREATE-ADDR-BYTES-ALIST
                        (CREATE-CANONICAL-ADDRESS-LIST '4
                                                       (XR ':RGF '6 X86))
                        (BYTE-IFY
                         '4
                         (COMBINE-BYTES
                          (MV-NTH
                           '1
                           (RB
                            (CREATE-CANONICAL-ADDRESS-LIST '4
                                                           (XR ':RGF '7 X86))
                            ':X
                            (MV-NTH
                             '1
                             (WB
                              (CREATE-ADDR-BYTES-ALIST
                               (CREATE-CANONICAL-ADDRESS-LIST
                                '8
                                (BINARY-+ '-8 (XR ':RGF '4 X86)))
                               (BYTE-IFY '8
                                         (ACL2::LOGHEAD$INLINE '64
                                                               (XR ':RGF '5 X86))))
                              (WRITE-USER-RFLAGS$INLINE
                               (BINARY-LOGIOR
                                (ACL2::LOGHEAD$INLINE
                                 '1
                                 (ACL2::BOOL->BIT$INLINE (LOGBITP '31 (XR ':RGF '2 X86))))
                                (BINARY-LOGIOR
                                 (ACL2::LOGHEAD$INLINE
                                  '32
                                  (ASH
                                   (PF-SPEC64$INLINE
                                    (ACL2::LOGHEAD$INLINE
                                     '64
                                     (ASH
                                      (ACL2::LOGHEAD$INLINE '64
                                                            (LOGEXT '32 (XR ':RGF '2 X86)))
                                      '2)))
                                   '2))
                                 (BINARY-LOGAND
                                  '4294967226
                                  (BINARY-LOGIOR
                                   (ACL2::LOGHEAD$INLINE
                                    '32
                                    (ASH
                                     (SF-SPEC64$INLINE
                                      (ACL2::LOGHEAD$INLINE
                                       '64
                                       (ASH (ACL2::LOGHEAD$INLINE
                                             '64
                                             (LOGEXT '32 (XR ':RGF '2 X86)))
                                            '2)))
                                     '7))
                                   (BINARY-LOGAND
                                    '4294967166
                                    (BITOPS::LOGSQUASH$INLINE
                                     '1
                                     (XR
                                      ':RFLAGS
                                      '0
                                      (WRITE-USER-RFLAGS$INLINE
                                       (BINARY-LOGIOR
                                        (ACL2::LOGHEAD$INLINE
                                         '32
                                         (ASH (PF-SPEC32$INLINE (XR ':RGF '2 X86))
                                              '2))
                                        (BINARY-LOGAND
                                         '4294967226
                                         (BINARY-LOGIOR
                                          (BINARY-LOGAND
                                           '4294965118
                                           (BITOPS::LOGSQUASH$INLINE '1
                                                                     (XR ':RFLAGS '0 X86)))
                                          (ACL2::LOGHEAD$INLINE
                                           '32
                                           (ASH (SF-SPEC32$INLINE (XR ':RGF '2 X86))
                                                '7)))))
                                       '16
                                       X86))))))))
                               '2064
                               (WRITE-USER-RFLAGS$INLINE
                                (BINARY-LOGIOR
                                 (ACL2::LOGHEAD$INLINE
                                  '32
                                  (ASH (PF-SPEC32$INLINE (XR ':RGF '2 X86))
                                       '2))
                                 (BINARY-LOGAND
                                  '4294967226
                                  (BINARY-LOGIOR
                                   (BINARY-LOGAND
                                    '4294965118
                                    (BITOPS::LOGSQUASH$INLINE '1
                                                              (XR ':RFLAGS '0 X86)))
                                   (ACL2::LOGHEAD$INLINE
                                    '32
                                    (ASH (SF-SPEC32$INLINE (XR ':RGF '2 X86))
                                         '7)))))
                                '16
                                X86))))))))))
                      x86))))
                  (MV-NTH
                   '1
                   (RB
                    (CONS (BINARY-+ '24 (XR ':RIP '0 X86))
                          'NIL)
                    ':X
                    x86))))
  :hints (("Goal" :in-theory (e/d* (instruction-decoding-and-spec-rules

                                    gpr-and-spec-4
                                    jcc/cmovcc/setcc-spec
                                    sal/shl-spec
                                    sal/shl-spec-64

                                    opcode-execute
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
                                    signed-byte-p
                                    ;; Flags
                                    zf-spec
                                    ;; write-user-rflags
                                    ;; !flgi-undefined
                                    ;; !flgi
                                    ;; flgi
                                    )
                                   (wb-remove-duplicate-writes
                                    create-canonical-address-list
                                    force (force))))))

(defthm effects-copyData-n!=0
  (implies (and (preconditions n addr x86)
                (posp n))
           (equal (x86-run 12 x86)
                  xxxx))
  :hints (("Goal" :in-theory (e/d* (instruction-decoding-and-spec-rules

                                    gpr-and-spec-4
                                    jcc/cmovcc/setcc-spec
                                    sal/shl-spec
                                    sal/shl-spec-64

                                    opcode-execute
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
                                    signed-byte-p
                                    ;; Flags
                                    zf-spec
                                    ;; write-user-rflags
                                    ;; !flgi-undefined
                                    ;; !flgi
                                    ;; flgi
                                    )
                                   (wb-remove-duplicate-writes
                                    create-canonical-address-list
                                    force (force))))))

||#
