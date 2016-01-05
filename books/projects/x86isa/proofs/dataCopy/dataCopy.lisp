;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")

(include-book "programmer-level-mode/programmer-level-memory-utils" :dir :proof-utils :ttags :all)
(include-book "centaur/bitops/ihs-extensions" :dir :system)

(local (include-book "centaur/bitops/signed-byte-p" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))

(local (in-theory (e/d* (rb-rb-subset) ())))

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
    #x74 #x1a           ;; je     100000ef2 <_copyData+0x22>	4   (jump if ZF = 1)
    #x48 #x63 #xc2      ;; movslq %edx,%rax			5
    #x48 #xc1 #xe0 #x02 ;; shl    $0x2,%rax			6
    #x90                ;; nop                                  7
    #x8b #x0f           ;; mov    (%rdi),%ecx			8
    #x48 #x83 #xc7 #x04 ;; add    $0x4,%rdi			9
    #x89 #x0e           ;; mov    %ecx,(%rsi)                  10
    #x48 #x83 #xc6 #x04 ;; add    $0x4,%rsi                    11
    #x48 #x83 #xc0 #xfc ;; add    $0xfffffffffffffffc,%rax     12
    #x75 #xee           ;; jne    100000ee0 <_copyData+0x10>   13   (jump if ZF = 0)
    #x5d                ;; pop    %rbp                         14
    #xc3                ;; retq                                15
    ))

;; Some important registers:

;; RDX: n
;; RSI: Destination address
;; RDI: Source address

;; ======================================================================


;; Some GL Theorems:

(encapsulate
 ()
 (local (include-book "centaur/gl/gl" :dir :system))

 (def-gl-export loop-clk-measure-helper
   :hyp (and (signed-byte-p 64 m)
             (<= 4 m))
   :concl (< (loghead 64 (+ #xfffffffffffffffc m)) m)
   :g-bindings (gl::auto-bindings (:int m 64))
   :rule-classes :linear)

 (def-gl-export effects-copyData-loop-helper-1
   :hyp (and (<= 4 m)
             (unsigned-byte-p 33 m))
   :concl (equal (logext 64 (+ #xfffffffffffffffc m))
                 (loghead 64 (+ #xfffffffffffffffc m)))
   :g-bindings (gl::auto-bindings (:nat m 33)))

 (def-gl-export effects-copyData-loop-helper-2
   :hyp (and (<= 4 m)
             (unsigned-byte-p 33 m))
   :concl (and (unsigned-byte-p 33 (loghead 64 (+ #xfffffffffffffffc m)))
               (signed-byte-p   64 (loghead 64 (+ #xfffffffffffffffc m))))
   :g-bindings (gl::auto-bindings (:nat m 33)))

 (def-gl-export effects-copyData-loop-helper-5
   :hyp (and (< 4 m)
             (equal (mod m 4) 0)
             (unsigned-byte-p 33 m))
   :concl (equal (mod (loghead 64 (+ #xfffffffffffffffc m)) 4) 0)
   :g-bindings (gl::auto-bindings (:nat m 33)))

 (def-gl-export effects-copyData-loop-helper-6
   :hyp (canonical-address-p src/dst)
   :concl (equal (logext 64 (+ 4 (loghead 64 src/dst)))
                 (+ 4 src/dst))
   :g-bindings (gl::auto-bindings (:int src/dst 64)))

 (def-gl-export effects-copyData-loop-helper-7
   :hyp (and (canonical-address-p src/dst)
             (canonical-address-p (+ m src/dst))
             (< 4 m)
             (equal (mod m 4) 0)
             (unsigned-byte-p 33 m))
   :concl (canonical-address-p (+ 4 src/dst (loghead 64 (+ #xfffffffffffffffc m))))
   :g-bindings (gl::auto-bindings (:mix (:int m 64)
                                        (:int src/dst 64))))

 (def-gl-export effects-copyData-loop-helper-9
   :hyp (and (< 4 m)
             (unsigned-byte-p 33 m))
   :concl (not (equal (loghead 64 (+ #xfffffffffffffffc m)) 0))
   :g-bindings (gl::auto-bindings (:nat m 33))
   :rule-classes (:forward-chaining :rewrite))

 (def-gl-export loop-clk-measure-helper-alt
   :hyp (and (unsigned-byte-p 33 m)
             (<= 4 m))
   :concl (equal (< m (+ 4 (loghead 64 (+ #xfffffffffffffffc m)))) nil)
   :g-bindings (gl::auto-bindings (:int m 64)))

 (def-gl-export next-lower-bound-for-m
   :hyp (and (equal (mod m 4) 0)
             (< 4 m)
             (unsigned-byte-p 33 m))
   :concl (< 7 m)
   :g-bindings (gl::auto-bindings (:nat m 33))
   :rule-classes :forward-chaining)

 (def-gl-export effects-copyData-loop-helper-11
   :hyp (and (< 4 m)
             (equal (mod m 4) 0)
             (unsigned-byte-p 33 m))
   :concl (equal (loghead 64 (+ #xfffffffffffffffc m))
                 (+ -4 m))
   :g-bindings (gl::auto-bindings (:nat m 33)))

 (def-gl-export effects-copyData-loop-helper-13
   :hyp (and (equal (mod k 4) 0)
             (unsigned-byte-p 33 k))
   :concl (equal (mod (+ 4 k) 4) 0)
   :g-bindings (gl::auto-bindings (:nat k 33)))

 (def-gl-export effects-copyData-loop-helper-14
   :hyp (and (< 4 m)
             (equal (mod m 4) 0)
             (unsigned-byte-p 33 m))
   :concl (equal (mod (+ -4 m) 4) 0)
   :g-bindings (gl::auto-bindings (:nat m 33)))

 (def-gl-export effects-copyData-loop-helper-15
   :hyp (and (equal (loghead 2 m) 0)
             (canonical-address-p m))
   :concl (equal (loghead 2 (+ 4 m)) 0)
   :g-bindings (gl::auto-bindings (:int m 48)))

 (def-gl-export effects-copyData-loop-helper-16
   :hyp (and (equal (loghead 3 m) 0)
             (canonical-address-p m))
   :concl (equal (loghead 3 (+ 8 m)) 0)
   :g-bindings (gl::auto-bindings (:int m 48)))

 (in-theory (e/d ()
                 (effects-copyData-loop-helper-11
                  effects-copyData-loop-helper-14))))

;; ======================================================================

(defun-nx source-bytes (k src-addr x86)
  (mv-nth 1 (rb (create-canonical-address-list k (+ (- k) src-addr))
                :x x86)))

(defun-nx destination-bytes (k dst-addr x86)
  (mv-nth 1 (rb (create-canonical-address-list k (+ (- k) dst-addr))
                :x x86)))

(defun-nx loop-invariant (k m addr x86)
  ;; The initial value of m is (ash n 2), where n is the same n as defined in
  ;; preconditions later in this book.

  ;; k: number of bytes already copied (in previous loop iterations)
  ;;    this will increase by 4 in every iteration
  ;; m: number of bytes to be copied
  ;;    this will decrease by 4 in every iteration

  (and (x86p x86)
       (xr :programmer-level-mode 0 x86)
       (equal (xr :ms 0 x86) nil)
       (equal (xr :fault 0 x86) nil)
       (unsigned-byte-p 33 m)
       (equal (mod m 4) 0)
       (unsigned-byte-p 33 k)
       (equal (mod k 4) 0)
       (unsigned-byte-p 33 (+ m k))
       (equal (xr :rgf *rax* x86) m)
       ;; Stack addresses are canonical.
       (canonical-address-p (xr :rgf *rsp* x86))
       (canonical-address-p (+ 8 (xr :rgf *rsp* x86)))
       ;; Return address of the copyData sub-routine is canonical.
       (canonical-address-p
        (logext
         64
         (combine-bytes
          (mv-nth 1
                  (rb (create-canonical-address-list 8 (+ 8 (xr :rgf *rsp* x86)))
                      :r x86)))))
       ;; All the destination addresses are canonical.
       (canonical-address-p (+ (- k) (xr :rgf *rsi* x86)))
       (canonical-address-p (+ m (xr :rgf *rsi* x86)))
       ;; All the source addresses are canonical.
       (canonical-address-p (+ (- k) (xr :rgf *rdi* x86)))
       (canonical-address-p (+ m (xr :rgf *rdi* x86)))
       ;; Alignment Checking
       (if (alignment-checking-enabled-p x86)
           ;; rsi and rdi point to doublewords (four bytes), so their
           ;; natural boundary will be addresses divisible by 4.
           (and (equal (loghead 2 (xr :rgf *rsi* x86)) 0)
                (equal (loghead 2 (xr :rgf *rdi* x86)) 0))
         t)
       ;; Memory locations of interest are disjoint.
       (disjoint-p
        ;; Program addresses
        (create-canonical-address-list (len *copyData*) addr)
        ;; Destination addresses
        (create-canonical-address-list (+ m k) (+ (- k) (xr :rgf *rsi* x86))))
       (disjoint-p
        ;; Return Address
        (create-canonical-address-list 8 (+ 8 (xr :rgf *rsp* x86)))
        ;; Destination Addresses
        (create-canonical-address-list (+ m k) (+ (- k) (xr :rgf *rsi* x86))))
       ;; We could modify the following pre-condition to say the following:
       ;; either the source and destination addresses are completely disjoint
       ;; or they are equal. However, the equality of the source and
       ;; destination isn't what we are interested in for this program and so I
       ;; choose to leave that out.
       (disjoint-p
        ;; Source Addresses
        (create-canonical-address-list (+ m k) (+ (- k) (xr :rgf *rdi* x86)))
        ;; Destination Addresses
        (create-canonical-address-list (+ m k) (+ (- k) (xr :rgf *rsi* x86))))
       ;; Program is located at addr.
       ;; All program addresses are canonical.
       (canonical-address-p addr)
       (canonical-address-p (+ (len *copyData*) addr))
       (program-at (create-canonical-address-list (len *copyData*) addr)
                   *copyData* x86)
       ;; Values copied in the previous iterations of the loop are unaltered.
       ;; dst[(+ -k dst-addr) to dst-addr]  =  src[(+ -k src-addr) to src-addr]
       (equal (destination-bytes k (xr :rgf *rsi* x86) x86)
              (source-bytes      k (xr :rgf *rdi* x86) x86))))

(defun-nx loop-preconditions (k m addr src-addr dst-addr x86)
  (and (loop-invariant k m addr x86)
       ;; At the beginning of every iteration, we have some bytes left to be
       ;; copied.
       (posp m)
       (equal (xr :rgf *rdi* x86) src-addr)
       (equal (xr :rgf *rsi* x86) dst-addr)
       (equal addr (+ -16 (xr :rip 0 x86)))))

(defthm loop-preconditions-fwd-chain-to-its-body
  (implies (loop-preconditions k m addr src-addr dst-addr x86)
           (and (x86p x86)
                (xr :programmer-level-mode 0 x86)
                (equal (xr :ms 0 x86) nil)
                (equal (xr :fault 0 x86) nil)
                (unsigned-byte-p 33 m)
                (equal (mod m 4) 0)
                (unsigned-byte-p 33 k)
                (equal (mod k 4) 0)
                (unsigned-byte-p 33 (+ m k))
                (equal (xr :rgf *rax* x86) m)
                ;; Stack address is canonical.
                (canonical-address-p (xr :rgf *rsp* x86))
                (canonical-address-p (+ 8 (xr :rgf *rsp* x86)))
                ;; Return address of the copyData sub-routine is canonical.
                (canonical-address-p
                 (logext
                  64
                  (combine-bytes
                   (mv-nth 1
                           (rb (create-canonical-address-list 8 (+ 8 (xr :rgf *rsp* x86)))
                               :r x86)))))
                ;; All the destination addresses are canonical.
                (canonical-address-p (+ (- k) (xr :rgf *rsi* x86)))
                (canonical-address-p (+ m (xr :rgf *rsi* x86)))
                ;; All the source addresses are canonical.
                (canonical-address-p (+ (- k) (xr :rgf *rdi* x86)))
                (canonical-address-p (+ m (xr :rgf *rdi* x86)))
                ;; Alignment Checking
                (if (alignment-checking-enabled-p x86)
                    (and (equal (loghead 2 (xr :rgf *rsi* x86)) 0)
                         (equal (loghead 2 (xr :rgf *rdi* x86)) 0))
                  t)
                ;; Memory locations of interest are disjoint.
                (disjoint-p
                 ;; Program addresses
                 (create-canonical-address-list (len *copyData*) addr)
                 ;; Destination addresses
                 (create-canonical-address-list (+ m k) (+ (- k) (xr :rgf *rsi* x86))))
                (disjoint-p
                 ;; Return Addresses
                 (create-canonical-address-list 8 (+ 8 (xr :rgf *rsp* x86)))
                 ;; Destination Addresses
                 (create-canonical-address-list (+ m k) (+ (- k) (xr :rgf *rsi* x86))))
                (disjoint-p
                 ;; Source Addresses
                 (create-canonical-address-list (+ m k) (+ (- k) (xr :rgf *rdi* x86)))
                 ;; Destination Addresses
                 (create-canonical-address-list (+ m k) (+ (- k) (xr :rgf *rsi* x86))))
                ;; Program is located at addr.
                ;; All program addresses are canonical.
                (canonical-address-p addr)
                (canonical-address-p (+ (len *copyData*) addr))
                (program-at (create-canonical-address-list (len *copyData*) addr)
                            *copyData* x86)
                ;; Values copied in the previous iterations of the loop are unaltered.
                ;; dst[(+ -k dst-addr) to dst-addr]  =  src[(+ -k src-addr) to src-addr]
                (equal (destination-bytes k (xr :rgf *rsi* x86) x86)
                       (source-bytes      k (xr :rgf *rdi* x86) x86))
                (posp m)
                (equal (xr :rgf *rdi* x86) src-addr)
                (equal (xr :rgf *rsi* x86) dst-addr)
                (equal addr (+ -16 (xr :rip 0 x86)))))
  :rule-classes :forward-chaining)

;; ======================================================================

;; Clock functions:

(defun pre-clk (n)
  (if (zp n) 4 7))

(defun loop-clk-base () 6)
(defun loop-clk-recur () 6)

(defun loop-clk (m)
  ;; I use m to refer to (ash n 2).
  (if (signed-byte-p 64 m)
      (let ((new-m (loghead 64 (+ #xfffffffffffffffc m))))
        (if (<= m 4)
            (loop-clk-base)
          (clk+ (loop-clk-recur) (loop-clk new-m))))
    0))

(defun post-clk () 2)

(defun clk (n)
  (if (zp n)
      (pre-clk n)
    (clk+ (pre-clk n)
          (loop-clk (ash n 2)))))

(defun program-clk (n)
  (clk+ (clk n) (post-clk)))

;; ======================================================================

;; Effects theorem:

(encapsulate
 ()

 (local (include-book "arithmetic-3/top" :dir :system))

 (defthm ash-n-2-bound
   (implies (and (< 0 n)
                 (integerp n))
            (<= 4 (ash n 2)))
   :hints (("Goal" :in-theory (e/d* (ash) ())))
   :rule-classes (:rewrite :linear)))

(encapsulate
 ()

 (local (include-book "ihs/quotient-remainder-lemmas" :dir :system))

 (defthm mod-thm-1
   (implies (and (equal (mod m 4) 0)
                 (posp m))
            (<= 4 m))
   :rule-classes (:forward-chaining))

 (defthm mod-thm-2
   (implies (natp n)
            (equal (mod (ash n 2) 4) 0))
   :hints (("Goal" :in-theory (e/d* (ash) ())))))

(defthmd effects-copyData-loop-base
  (implies
   (and (equal m 4)
        (loop-preconditions k m addr src-addr dst-addr x86))
   (equal (x86-run (loop-clk-base) x86)
          (XW
           :RGF *RAX* 0
           (XW
            :RGF *RCX*
            (COMBINE-BYTES
             (MV-NTH 1
                     (RB (CREATE-CANONICAL-ADDRESS-LIST 4 (XR :RGF *RDI* X86))
                         :X X86)))
            (XW
             :RGF *RSI* (+ 4 (XR :RGF *RSI* X86))
             (XW
              :RGF *RDI* (+ 4 (XR :RGF *RDI* X86))
              (XW
               :RIP 0 (+ 18 (XR :RIP 0 X86))
               (MV-NTH
                1
                (WB
                 (CREATE-ADDR-BYTES-ALIST
                  (CREATE-CANONICAL-ADDRESS-LIST 4 (XR :RGF *RSI* X86))
                  (BYTE-IFY
                   4
                   (COMBINE-BYTES
                    (MV-NTH 1
                            (RB (CREATE-CANONICAL-ADDRESS-LIST 4 (XR :RGF *RDI* X86))
                                :X X86)))))
                 (WRITE-USER-RFLAGS
                  (LOGIOR
                   (LOGHEAD 32
                            (CF-SPEC64 (+ #xfffffffffffffffc
                                          (XR :RGF *RAX* X86))))
                   (LOGHEAD 32
                            (ASH (PF-SPEC64 (LOGHEAD 64
                                                     (+ #xfffffffffffffffc
                                                        (XR :RGF *RAX* X86))))
                                 2))
                   (LOGAND
                    4294967290
                    (LOGIOR
                     (LOGHEAD 32
                              (ASH (ADD-AF-SPEC64 (XR :RGF *RAX* X86)
                                                  #xfffffffffffffffc)
                                   4))
                     (LOGAND
                      4294967278
                      (LOGIOR
                       (LOGHEAD 32
                                (ASH (ZF-SPEC (LOGHEAD 64
                                                       (+ #xfffffffffffffffc
                                                          (XR :RGF *RAX* X86))))
                                     6))
                       (LOGAND
                        4294967230
                        (LOGIOR
                         (LOGHEAD 32
                                  (ASH (SF-SPEC64 (LOGHEAD 64
                                                           (+ #xfffffffffffffffc
                                                              (XR :RGF *RAX* X86))))
                                       7))
                         (LOGAND
                          4294967166
                          (LOGIOR
                           (LOGHEAD 32
                                    (ASH (OF-SPEC64 (+ -4 (XR :RGF *RAX* X86)))
                                         11))
                           (LOGAND
                            4294965246
                            (LOGIOR
                             (BITOPS::LOGSQUASH
                              1
                              (LOGHEAD
                               32
                               (CF-SPEC64 (+ 4 (LOGHEAD 64 (XR :RGF *RSI* X86))))))
                             (BITOPS::LOGSQUASH
                              1
                              (LOGHEAD
                               32
                               (ASH
                                (PF-SPEC64
                                 (LOGHEAD 64
                                          (+ 4 (LOGHEAD 64 (XR :RGF *RSI* X86)))))
                                2)))
                             (LOGAND
                              4294967290
                              (LOGIOR
                               (BITOPS::LOGSQUASH
                                1
                                (LOGHEAD
                                 32
                                 (ASH (ADD-AF-SPEC64 (LOGHEAD 64 (XR :RGF *RSI* X86))
                                                     4)
                                      4)))
                               (LOGAND
                                4294967278
                                (LOGIOR
                                 (BITOPS::LOGSQUASH
                                  1
                                  (LOGHEAD
                                   32
                                   (ASH
                                    (ZF-SPEC
                                     (LOGHEAD
                                      64
                                      (+ 4 (LOGHEAD 64 (XR :RGF *RSI* X86)))))
                                    6)))
                                 (LOGAND
                                  4294967230
                                  (LOGIOR
                                   (BITOPS::LOGSQUASH
                                    1
                                    (LOGHEAD
                                     32
                                     (ASH
                                      (SF-SPEC64
                                       (LOGHEAD
                                        64
                                        (+ 4 (LOGHEAD 64 (XR :RGF *RSI* X86)))))
                                      7)))
                                   (LOGAND
                                    4294967166
                                    (LOGIOR
                                     (BITOPS::LOGSQUASH
                                      1
                                      (LOGHEAD
                                       32
                                       (ASH (OF-SPEC64 (+ 4 (XR :RGF *RSI* X86)))
                                            11)))
                                     (LOGAND
                                      4294965246
                                      (LOGIOR
                                       (BITOPS::LOGSQUASH
                                        1
                                        (LOGHEAD
                                         32
                                         (CF-SPEC64
                                          (+ 4 (LOGHEAD 64 (XR :RGF *RDI* X86))))))
                                       (BITOPS::LOGSQUASH
                                        1
                                        (LOGHEAD
                                         32
                                         (ASH
                                          (PF-SPEC64
                                           (LOGHEAD
                                            64
                                            (+ 4 (LOGHEAD 64 (XR :RGF *RDI* X86)))))
                                          2)))
                                       (LOGAND
                                        4294967290
                                        (LOGIOR
                                         (BITOPS::LOGSQUASH
                                          1
                                          (LOGHEAD
                                           32
                                           (ASH (ADD-AF-SPEC64
                                                 (LOGHEAD 64 (XR :RGF *RDI* X86))
                                                 4)
                                                4)))
                                         (LOGAND
                                          4294967278
                                          (LOGIOR
                                           (BITOPS::LOGSQUASH
                                            1
                                            (LOGHEAD
                                             32
                                             (ASH
                                              (ZF-SPEC
                                               (LOGHEAD
                                                64
                                                (+
                                                 4
                                                 (LOGHEAD 64 (XR :RGF *RDI* X86)))))
                                              6)))
                                           (LOGAND
                                            4294967230
                                            (LOGIOR
                                             (BITOPS::LOGSQUASH
                                              1
                                              (LOGHEAD
                                               32
                                               (ASH
                                                (SF-SPEC64
                                                 (LOGHEAD
                                                  64
                                                  (+ 4
                                                     (LOGHEAD
                                                      64 (XR :RGF *RDI* X86)))))
                                                7)))
                                             (LOGAND
                                              4294967166
                                              (LOGIOR
                                               (LOGAND 4294965246
                                                       (BITOPS::LOGSQUASH
                                                        1 (XR :RFLAGS 0 X86)))
                                               (BITOPS::LOGSQUASH
                                                1
                                                (LOGHEAD
                                                 32
                                                 (ASH
                                                  (OF-SPEC64
                                                   (+ 4 (XR :RGF *RDI* X86)))
                                                  11))))))))))))))))))))))))))))))))
                  0 X86))))))))))
  :hints (("Goal"
           :in-theory (e/d* (instruction-decoding-and-spec-rules

                             gpr-and-spec-4
                             gpr-add-spec-8
                             jcc/cmovcc/setcc-spec
                             sal/shl-spec
                             sal/shl-spec-64

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
                             signed-byte-p)
                            (wb-remove-duplicate-writes
                             create-canonical-address-list)))))

(defthm effects-copyData-loop-base-destination-address-projection-original
  ;; dst[(+ -k dst-addr) to dst-addr] in (x86-run (loop-clk-base) x86) =
  ;; dst[(+ -k src-addr) to src-addr] in x86
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (<= m 4))
           (equal (destination-bytes k dst-addr (x86-run (loop-clk-base) x86))
                  (source-bytes k dst-addr x86)))
  :hints (("Goal" :use ((:instance effects-copydata-loop-base))
           :in-theory (e/d* ()
                            (loop-clk-base
                             rb-rb-split-reads
                             take-and-rb
                             (loop-clk-base)
                             force (force))))))

(defthm effects-copyData-loop-base-destination-address-projection-copied
  ;; dst[(dst-addr) to (dst-addr + 4)] in (x86-run (loop-clk-base) x86) =
  ;; src[(src-addr) to (src-addr + 4)] in x86
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (<= m 4))
           (equal (destination-bytes 4 (+ 4 dst-addr) (x86-run (loop-clk-base) x86))
                  (source-bytes 4 (+ 4 src-addr) x86)))
  :hints (("Goal" :use ((:instance effects-copydata-loop-base))
           :in-theory (e/d* ()
                            (loop-clk-base
                             rb-rb-split-reads
                             take-and-rb
                             (loop-clk-base)
                             force (force))))))

(defthm effects-copyData-loop-base-destination-address-projection
  ;; dst[(+ -k dst-addr) to (dst-addr + 4)] in (x86-run (loop-clk-base) x86) =
  ;; src[(+ -k src-addr) to (src-addr + 4)] in x86
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (<= m 4))
           (equal (destination-bytes (+ 4 k) (+ 4 dst-addr) (x86-run (loop-clk-base) x86))
                  (source-bytes (+ 4 k) (+ 4 src-addr) x86)))
  :hints (("Goal" :use ((:instance effects-copydata-loop-base)
                        (:instance effects-copyData-loop-base-destination-address-projection-copied)
                        (:instance effects-copyData-loop-base-destination-address-projection-original)
                        (:instance rb-rb-split-reads
                                   (k k)
                                   (j 4)
                                   (r-w-x :x)
                                   (addr (+ (- k) (xr :rgf *rsi* x86)))
                                   (x86 (x86-run (loop-clk-base) x86)))
                        (:instance rb-rb-split-reads
                                   (k k)
                                   (j 4)
                                   (r-w-x :x)
                                   (addr (+ (- k) (xr :rgf *rdi* x86)))
                                   (x86 (x86-run (loop-clk-base) x86))))
           :in-theory (e/d* ()
                            (loop-clk-base
                             effects-copyData-loop-base-destination-address-projection-copied
                             effects-copyData-loop-base-destination-address-projection-original
                             rb-rb-split-reads
                             take-and-rb
                             (loop-clk-base)
                             force (force))))))

(defthm effects-copyData-loop-base-source-address-projection-original
  ;; src[(+ -k src-addr) to src-addr] in (x86-run (loop-clk-base) x86) =
  ;; src[(+ -k src-addr) to src-addr] in x86
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (<= m 4))
           (equal (source-bytes k src-addr (x86-run (loop-clk-base) x86))
                  (source-bytes k src-addr x86)))
  :hints (("Goal" :use ((:instance effects-copydata-loop-base))
           :in-theory (e/d* ()
                            (loop-clk-base
                             rb-rb-split-reads
                             take-and-rb
                             (loop-clk-base)
                             force (force))))))

(defthm effects-copyData-loop-base-source-address-projection-copied
  ;; src[(src-addr) to (src-addr + 4)] in (x86-run (loop-clk-base) x86) =
  ;; src[(src-addr) to (src-addr + 4)] in x86
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (<= m 4))
           (equal (source-bytes 4 (+ 4 src-addr) (x86-run (loop-clk-base) x86))
                  (source-bytes 4 (+ 4 src-addr) x86)))
  :hints (("Goal" :use ((:instance effects-copydata-loop-base))
           :in-theory (e/d* ()
                            (loop-clk-base
                             rb-rb-split-reads
                             take-and-rb
                             (loop-clk-base)
                             force (force))))))

(defthm effects-copyData-loop-base-source-address-projection
  ;; src[(+ -k src-addr) to (src-addr + 4)] in (x86-run (loop-clk-base) x86) =
  ;; src[(+ -k src-addr) to (src-addr + 4)] in x86
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (<= m 4))
           (equal (source-bytes (+ 4 k) (+ 4 src-addr) (x86-run (loop-clk-base) x86))
                  (source-bytes (+ 4 k) (+ 4 src-addr) x86)))
  :hints (("Goal" :use ((:instance effects-copydata-loop-base)
                        (:instance effects-copyData-loop-base-source-address-projection-copied)
                        (:instance effects-copyData-loop-base-source-address-projection-original)
                        (:instance rb-rb-split-reads
                                   (k k)
                                   (j 4)
                                   (r-w-x :x)
                                   (addr (+ (- k) (xr :rgf *rdi* x86)))
                                   (x86 (x86-run (loop-clk-base) x86)))
                        (:instance rb-rb-split-reads
                                   (k k)
                                   (j 4)
                                   (r-w-x :x)
                                   (addr (+ (- k) (xr :rgf *rdi* x86)))
                                   (x86 (x86-run (loop-clk-base) x86))))
           :in-theory (e/d* ()
                            (loop-clk-base
                             effects-copyData-loop-base-source-address-projection-copied
                             effects-copyData-loop-base-source-address-projection-original
                             rb-rb-split-reads
                             take-and-rb
                             (loop-clk-base)
                             force (force))))))

(defthm effects-copyData-loop-base-alignment-checking-enabled-p
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (<= m 4))
           (equal (alignment-checking-enabled-p (x86-run (loop-clk-base) x86))
                  (alignment-checking-enabled-p x86)))
  :hints (("Goal"
           :use ((:instance effects-copydata-loop-base))
           :in-theory (e/d* (alignment-checking-enabled-p)
                            (loop-clk-base
                             (loop-clk-base)
                             force (force))))))

(defthm effects-copyData-loop-base-programmer-level-mode-projection
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (<= m 4))
           (equal (xr :programmer-level-mode 0 (x86-run (loop-clk-base) x86))
                  (xr :programmer-level-mode 0 x86)))
  :hints (("Goal"
           :use ((:instance effects-copydata-loop-base))
           :in-theory (e/d* ()
                            (loop-clk-base
                             (loop-clk-base)
                             force (force))))))

(defthm effects-copyData-loop-base-rsi-projection
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (<= m 4))
           (equal (xr :rgf *rsi* (x86-run (loop-clk-base) x86))
                  (+ 4 (xr :rgf *rsi* x86))))
  :hints (("Goal" :use ((:instance effects-copydata-loop-base))
           :in-theory (e/d* ()
                            (loop-clk-base
                             (loop-clk-base)
                             force (force))))))

(defthm effects-copyData-loop-base-rdi-projection
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (<= m 4))
           (equal (xr :rgf *rdi* (x86-run (loop-clk-base) x86))
                  (+ 4 (xr :rgf *rdi* x86))))
  :hints (("Goal" :use ((:instance effects-copydata-loop-base))
           :in-theory (e/d* ()
                            (loop-clk-base
                             (loop-clk-base)
                             force (force))))))

(defthm effects-copyData-loop-base-rsp-projection
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (<= m 4))
           (equal (xr :rgf *rsp* (x86-run (loop-clk-base) x86))
                  (xr :rgf *rsp* x86)))
  :hints (("Goal" :use ((:instance effects-copydata-loop-base))
           :in-theory (e/d* ()
                            (loop-clk-base
                             (loop-clk-base)
                             force (force))))))

(defthm effects-copyData-loop-base-fault-projection
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (<= m 4))
           (equal (xr :fault 0 (x86-run (loop-clk-base) x86))
                  (xr :fault 0 x86)))
  :hints (("Goal" :use ((:instance effects-copydata-loop-base))
           :in-theory (e/d* ()
                            (loop-clk-base
                             (loop-clk-base)
                             force (force))))))

(defthm effects-copyData-loop-base-ms-projection
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (<= m 4))
           (equal (xr :ms 0 (x86-run (loop-clk-base) x86))
                  (xr :ms 0 x86)))
  :hints (("Goal" :use ((:instance effects-copydata-loop-base))
           :in-theory (e/d* ()
                            (loop-clk-base
                             (loop-clk-base)
                             force (force))))))

(defthm effects-copyData-loop-base-rip-projection
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (<= m 4))
           (equal (xr :rip 0 (x86-run (loop-clk-base) x86))
                  (+ 18 (xr :rip 0 x86))))
  :hints (("Goal" :use ((:instance effects-copydata-loop-base))
           :in-theory (e/d* ()
                            (loop-clk-base
                             (loop-clk-base)
                             force (force))))))

(defthm effects-copyData-loop-base-return-address-projection
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (<= m 4))
           (equal (mv-nth 1
                          (rb (create-canonical-address-list 8 (+ 8 (xr :rgf *rsp* x86)))
                              :r (x86-run (loop-clk-base) x86)))
                  (mv-nth 1
                          (rb (create-canonical-address-list 8 (+ 8 (xr :rgf *rsp* x86)))
                              :r x86))))
  :hints (("Goal" :use ((:instance effects-copyData-loop-base)
                        (:instance loop-preconditions-fwd-chain-to-its-body))
           :in-theory (e/d* ()
                            (loop-clk-base
                             loop-preconditions-fwd-chain-to-its-body
                             loop-preconditions
                             effects-copyData-loop-base
                             (loop-clk-base)
                             force (force))))))

(defthm effects-copyData-loop-base-program-at-projection
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (equal prog-len (len *copydata*))
                (<= m 4))
           (equal (program-at (create-canonical-address-list prog-len addr)
                              *copyData* (x86-run (loop-clk-base) x86))
                  (program-at (create-canonical-address-list prog-len addr)
                              *copyData* x86)))
  :hints (("Goal" :use ((:instance effects-copydata-loop-base))
           :in-theory (e/d* ()
                            (loop-clk-base
                             (loop-clk-base)
                             force (force))))))

(defthmd effects-copyData-loop-recur
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (< 4 m))
           (equal (x86-run (loop-clk-recur) x86)
                  (XW
                   :RGF *RAX*
                   (LOGHEAD 64
                            (+ #xfffffffffffffffc
                               (XR :RGF *RAX* X86)))
                   (XW
                    :RGF *RCX*
                    (COMBINE-BYTES
                     (MV-NTH 1
                             (RB (CREATE-CANONICAL-ADDRESS-LIST 4 (XR :RGF *RDI* X86))
                                 :X X86)))
                    (XW
                     :RGF *RSI* (+ 4 (XR :RGF *RSI* X86))
                     (XW
                      :RGF *RDI* (+ 4 (XR :RGF *RDI* X86))
                      (XW
                       :RIP 0 (XR :RIP 0 X86)
                       (MV-NTH
                        1
                        (WB
                         (CREATE-ADDR-BYTES-ALIST
                          (CREATE-CANONICAL-ADDRESS-LIST 4 (XR :RGF *RSI* X86))
                          (BYTE-IFY
                           4
                           (COMBINE-BYTES
                            (MV-NTH 1
                                    (RB (CREATE-CANONICAL-ADDRESS-LIST 4 (XR :RGF *RDI* X86))
                                        :X X86)))))
                         (WRITE-USER-RFLAGS
                          (LOGIOR
                           (LOGHEAD 32
                                    (CF-SPEC64 (+ #xfffffffffffffffc
                                                  (XR :RGF *RAX* X86))))
                           (LOGHEAD 32
                                    (ASH (PF-SPEC64 (LOGHEAD 64
                                                             (+ #xfffffffffffffffc
                                                                (XR :RGF *RAX* X86))))
                                         2))
                           (LOGAND
                            4294967290
                            (LOGIOR
                             (LOGHEAD 32
                                      (ASH (ADD-AF-SPEC64 (XR :RGF *RAX* X86)
                                                          #xfffffffffffffffc)
                                           4))
                             (LOGAND
                              4294967278
                              (LOGIOR
                               (LOGHEAD 32
                                        (ASH (ZF-SPEC (LOGHEAD 64
                                                               (+ #xfffffffffffffffc
                                                                  (XR :RGF *RAX* X86))))
                                             6))
                               (LOGAND
                                4294967230
                                (LOGIOR
                                 (LOGHEAD 32
                                          (ASH (SF-SPEC64 (LOGHEAD 64
                                                                   (+ #xfffffffffffffffc
                                                                      (XR :RGF *RAX* X86))))
                                               7))
                                 (LOGAND
                                  4294967166
                                  (LOGIOR
                                   (LOGHEAD 32
                                            (ASH (OF-SPEC64 (+ -4 (XR :RGF *RAX* X86)))
                                                 11))
                                   (LOGAND
                                    4294965246
                                    (LOGIOR
                                     (BITOPS::LOGSQUASH
                                      1
                                      (LOGHEAD
                                       32
                                       (CF-SPEC64 (+ 4 (LOGHEAD 64 (XR :RGF *RSI* X86))))))
                                     (BITOPS::LOGSQUASH
                                      1
                                      (LOGHEAD
                                       32
                                       (ASH
                                        (PF-SPEC64
                                         (LOGHEAD 64
                                                  (+ 4 (LOGHEAD 64 (XR :RGF *RSI* X86)))))
                                        2)))
                                     (LOGAND
                                      4294967290
                                      (LOGIOR
                                       (BITOPS::LOGSQUASH
                                        1
                                        (LOGHEAD
                                         32
                                         (ASH (ADD-AF-SPEC64 (LOGHEAD 64 (XR :RGF *RSI* X86))
                                                             4)
                                              4)))
                                       (LOGAND
                                        4294967278
                                        (LOGIOR
                                         (BITOPS::LOGSQUASH
                                          1
                                          (LOGHEAD
                                           32
                                           (ASH
                                            (ZF-SPEC
                                             (LOGHEAD
                                              64
                                              (+ 4 (LOGHEAD 64 (XR :RGF *RSI* X86)))))
                                            6)))
                                         (LOGAND
                                          4294967230
                                          (LOGIOR
                                           (BITOPS::LOGSQUASH
                                            1
                                            (LOGHEAD
                                             32
                                             (ASH
                                              (SF-SPEC64
                                               (LOGHEAD
                                                64
                                                (+ 4 (LOGHEAD 64 (XR :RGF *RSI* X86)))))
                                              7)))
                                           (LOGAND
                                            4294967166
                                            (LOGIOR
                                             (BITOPS::LOGSQUASH
                                              1
                                              (LOGHEAD
                                               32
                                               (ASH (OF-SPEC64 (+ 4 (XR :RGF *RSI* X86)))
                                                    11)))
                                             (LOGAND
                                              4294965246
                                              (LOGIOR
                                               (BITOPS::LOGSQUASH
                                                1
                                                (LOGHEAD
                                                 32
                                                 (CF-SPEC64
                                                  (+ 4 (LOGHEAD 64 (XR :RGF *RDI* X86))))))
                                               (BITOPS::LOGSQUASH
                                                1
                                                (LOGHEAD
                                                 32
                                                 (ASH
                                                  (PF-SPEC64
                                                   (LOGHEAD
                                                    64
                                                    (+ 4 (LOGHEAD 64 (XR :RGF *RDI* X86)))))
                                                  2)))
                                               (LOGAND
                                                4294967290
                                                (LOGIOR
                                                 (BITOPS::LOGSQUASH
                                                  1
                                                  (LOGHEAD
                                                   32
                                                   (ASH (ADD-AF-SPEC64
                                                         (LOGHEAD 64 (XR :RGF *RDI* X86))
                                                         4)
                                                        4)))
                                                 (LOGAND
                                                  4294967278
                                                  (LOGIOR
                                                   (BITOPS::LOGSQUASH
                                                    1
                                                    (LOGHEAD
                                                     32
                                                     (ASH
                                                      (ZF-SPEC
                                                       (LOGHEAD
                                                        64
                                                        (+
                                                         4
                                                         (LOGHEAD 64 (XR :RGF *RDI* X86)))))
                                                      6)))
                                                   (LOGAND
                                                    4294967230
                                                    (LOGIOR
                                                     (BITOPS::LOGSQUASH
                                                      1
                                                      (LOGHEAD
                                                       32
                                                       (ASH
                                                        (SF-SPEC64
                                                         (LOGHEAD
                                                          64
                                                          (+ 4
                                                             (LOGHEAD
                                                              64 (XR :RGF *RDI* X86)))))
                                                        7)))
                                                     (LOGAND
                                                      4294967166
                                                      (LOGIOR
                                                       (LOGAND 4294965246
                                                               (BITOPS::LOGSQUASH
                                                                1 (XR :RFLAGS 0 X86)))
                                                       (BITOPS::LOGSQUASH
                                                        1
                                                        (LOGHEAD
                                                         32
                                                         (ASH
                                                          (OF-SPEC64
                                                           (+ 4 (XR :RGF *RDI* X86)))
                                                          11))))))))))))))))))))))))))))))))
                          0 X86))))))))))
  :hints (("Goal"
           :in-theory (e/d* (instruction-decoding-and-spec-rules

                             gpr-and-spec-4
                             gpr-add-spec-8
                             jcc/cmovcc/setcc-spec
                             sal/shl-spec
                             sal/shl-spec-64

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
                             signed-byte-p)
                            (wb-remove-duplicate-writes
                             create-canonical-address-list)))))

(defthm effects-copyData-loop-recur-destination-address-projection-original
  ;; dst[(+ -k dst-addr) to dst-addr] in (x86-run (loop-clk-recur) x86) =
  ;; dst[(+ -k src-addr) to src-addr] in x86
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (< 4 m))
           (equal (destination-bytes k dst-addr (x86-run (loop-clk-recur) x86))
                  (source-bytes k dst-addr x86)))
  :hints (("Goal" :use ((:instance effects-copydata-loop-recur))
           :in-theory (e/d* ()
                            (loop-clk-recur
                             rb-rb-split-reads
                             take-and-rb
                             (loop-clk-recur)
                             force (force))))))

(defthm effects-copyData-loop-recur-destination-address-projection-copied
  ;; dst[(dst-addr) to (dst-addr + 4)] in (x86-run (loop-clk-recur) x86) =
  ;; src[(src-addr) to (src-addr + 4)] in x86
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (< 4 m))
           (equal (destination-bytes 4 (+ 4 dst-addr) (x86-run (loop-clk-recur) x86))
                  (source-bytes 4 (+ 4 src-addr) x86)))
  :hints (("Goal" :use ((:instance effects-copydata-loop-recur))
           :in-theory (e/d* ()
                            (loop-clk-recur
                             rb-rb-split-reads
                             take-and-rb
                             (loop-clk-recur)
                             force (force))))))

(defthm effects-copyData-loop-recur-destination-address-projection
  ;; TO-DO: Ugh, subgoal hints...
  ;; dst[(+ -k dst-addr) to (dst-addr + 4)] in (x86-run (loop-clk-recur) x86) =
  ;; src[(+ -k src-addr) to (src-addr + 4)] in x86
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (< 4 m))
           (equal (destination-bytes (+ 4 k) (+ 4 dst-addr) (x86-run (loop-clk-recur) x86))
                  (source-bytes (+ 4 k) (+ 4 src-addr) x86)))
  :hints (("Goal" :use ((:instance effects-copydata-loop-recur)
                        (:instance effects-copyData-loop-recur-destination-address-projection-copied)
                        (:instance effects-copyData-loop-recur-destination-address-projection-original)
                        (:instance rb-rb-split-reads
                                   (k k)
                                   (j 4)
                                   (r-w-x :x)
                                   (addr (+ (- k) (xr :rgf *rsi* x86)))
                                   (x86 (x86-run (loop-clk-recur) x86))))
           :in-theory (e/d* ()
                            (loop-clk-recur
                             effects-copyData-loop-recur-destination-address-projection-copied
                             effects-copyData-loop-recur-destination-address-projection-original
                             rb-rb-split-reads
                             take-and-rb
                             acl2::take-of-append
                             (loop-clk-recur)
                             force (force))))
          ("Subgoal 7" :use ((:instance rb-rb-split-reads
                                        (k k)
                                        (j 4)
                                        (r-w-x :x)
                                        (addr (+ (- k) (xr :rgf *rdi* x86)))
                                        (x86 x86)))
           :in-theory (e/d* ()
                            (loop-clk-recur
                             effects-copyData-loop-recur-destination-address-projection-copied
                             effects-copyData-loop-recur-destination-address-projection-original
                             rb-rb-split-reads
                             take-and-rb
                             acl2::take-of-append
                             (loop-clk-recur)
                             force (force))))
          ("Subgoal 5" :use ((:instance rb-rb-split-reads
                                        (k k)
                                        (j 4)
                                        (r-w-x :x)
                                        (addr (+ (- k) (xr :rgf *rdi* x86)))
                                        (x86 x86)))
           :in-theory (e/d* ()
                            (loop-clk-recur
                             effects-copyData-loop-recur-destination-address-projection-copied
                             effects-copyData-loop-recur-destination-address-projection-original
                             rb-rb-split-reads
                             take-and-rb
                             acl2::take-of-append
                             (loop-clk-recur)
                             force (force))))
          ("Subgoal 2" :use ((:instance rb-rb-split-reads
                                        (k k)
                                        (j 4)
                                        (r-w-x :x)
                                        (addr (+ (- k) (xr :rgf *rdi* x86)))
                                        (x86 x86)))
           :in-theory (e/d* ()
                            (loop-clk-recur
                             effects-copyData-loop-recur-destination-address-projection-copied
                             effects-copyData-loop-recur-destination-address-projection-original
                             rb-rb-split-reads
                             take-and-rb
                             acl2::take-of-append
                             (loop-clk-recur)
                             force (force))))
          ("Subgoal 1" :use ((:instance rb-rb-split-reads
                                        (k k)
                                        (j 4)
                                        (r-w-x :x)
                                        (addr (+ (- k) (xr :rgf *rdi* x86)))
                                        (x86 x86)))
           :in-theory (e/d* ()
                            (loop-clk-recur
                             effects-copyData-loop-recur-destination-address-projection-copied
                             effects-copyData-loop-recur-destination-address-projection-original
                             rb-rb-split-reads
                             take-and-rb
                             acl2::take-of-append
                             (loop-clk-recur)
                             force (force))))))

(defthm effects-copyData-loop-recur-source-address-projection-original
  ;; src[(+ -k src-addr) to src-addr] in (x86-run (loop-clk-recur) x86) =
  ;; src[(+ -k src-addr) to src-addr] in x86
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (< 4 m))
           (equal (source-bytes k src-addr (x86-run (loop-clk-recur) x86))
                  (source-bytes k src-addr x86)))
  :hints (("Goal" :use ((:instance effects-copydata-loop-recur))
           :in-theory (e/d* ()
                            (loop-clk-recur
                             rb-rb-split-reads
                             take-and-rb
                             (loop-clk-recur)
                             force (force))))))

(defthm effects-copyData-loop-recur-source-address-projection-copied
  ;; src[(src-addr) to (src-addr + 4)] in (x86-run (loop-clk-recur) x86) =
  ;; src[(src-addr) to (src-addr + 4)] in x86
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (< 4 m))
           (equal (source-bytes 4 (+ 4 src-addr) (x86-run (loop-clk-recur) x86))
                  (source-bytes 4 (+ 4 src-addr) x86)))
  :hints (("Goal" :use ((:instance effects-copydata-loop-recur))
           :in-theory (e/d* ()
                            (loop-clk-recur
                             rb-rb-split-reads
                             take-and-rb
                             (loop-clk-recur)
                             force (force))))))

(defthm effects-copyData-loop-recur-source-address-projection
  ;; src[(+ -k src-addr) to (src-addr + 4)] in (x86-run (loop-clk-recur) x86) =
  ;; src[(+ -k src-addr) to (src-addr + 4)] in x86
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (< 4 m))
           (equal (source-bytes (+ 4 k) (+ 4 src-addr) (x86-run (loop-clk-recur) x86))
                  (source-bytes (+ 4 k) (+ 4 src-addr) x86)))
  :hints (("Goal" :use ((:instance effects-copydata-loop-recur)
                        (:instance effects-copyData-loop-recur-source-address-projection-copied)
                        (:instance effects-copyData-loop-recur-source-address-projection-original)
                        (:instance rb-rb-split-reads
                                   (k k)
                                   (j 4)
                                   (r-w-x :x)
                                   (addr (+ (- k) (xr :rgf *rdi* x86)))
                                   (x86 (x86-run (loop-clk-recur) x86))))
           :in-theory (e/d* ()
                            (loop-clk-recur
                             effects-copyData-loop-recur-source-address-projection-copied
                             effects-copyData-loop-recur-source-address-projection-original
                             rb-rb-split-reads
                             take-and-rb
                             acl2::take-of-append
                             (loop-clk-recur)
                             force (force))))
          ("Subgoal 1" :use ((:instance rb-rb-split-reads
                                        (k k)
                                        (j 4)
                                        (r-w-x :x)
                                        (addr (+ (- k) (xr :rgf *rdi* x86)))
                                        (x86 x86)))
           :in-theory (e/d* ()
                            (loop-clk-recur
                             effects-copyData-loop-recur-source-address-projection-copied
                             effects-copyData-loop-recur-source-address-projection-original
                             rb-rb-split-reads
                             take-and-rb
                             acl2::take-of-append
                             (loop-clk-recur)
                             force (force))))))

(defthm effects-copyData-loop-recur-programmer-level-mode-projection
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (< 4 m))
           (equal (xr :programmer-level-mode 0 (x86-run (loop-clk-recur) x86))
                  (xr :programmer-level-mode 0 x86)))
  :hints (("Goal" :use ((:instance effects-copyData-loop-recur))
           :in-theory (e/d* ()
                            (loop-clk-recur
                             (loop-clk-recur)
                             force (force))))))

(defthm effects-copyData-loop-recur-alignment-checking-enabled-p-projection
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (< 4 m))
           (equal (alignment-checking-enabled-p (x86-run (loop-clk-recur) x86))
                  (alignment-checking-enabled-p x86)))
  :hints (("Goal" :use ((:instance effects-copyData-loop-recur))
           :in-theory (e/d* (alignment-checking-enabled-p)
                            (loop-clk-recur
                             (loop-clk-recur)
                             force (force))))))

(defthm effects-copyData-loop-recur-ms-projection
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (< 4 m))
           (equal (xr :ms 0 (x86-run (loop-clk-recur) x86))
                  (xr :ms 0 x86)))
  :hints (("Goal" :use ((:instance effects-copyData-loop-recur))
           :in-theory (e/d* ()
                            (loop-clk-recur
                             (loop-clk-recur)
                             force (force))))))

(defthm effects-copyData-loop-recur-fault-projection
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (< 4 m))
           (equal (xr :fault 0 (x86-run (loop-clk-recur) x86))
                  (xr :fault 0 x86)))
  :hints (("Goal" :use ((:instance effects-copyData-loop-recur))
           :in-theory (e/d* ()
                            (loop-clk-recur
                             (loop-clk-recur)
                             force (force))))))

(defthm effects-copyData-loop-recur-program-at-projection
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (< 4 m)
                (equal prog-len (len *copydata*)))
           (equal (program-at (create-canonical-address-list prog-len addr)
                              *copyData* (x86-run (loop-clk-recur) x86))
                  (program-at (create-canonical-address-list prog-len addr)
                              *copyData* x86)))
  :hints (("Goal"
           :use ((:instance effects-copyData-loop-recur))
           :in-theory (e/d* ()
                            (loop-clk-recur
                             (loop-clk-recur)
                             force (force))))))

(defthm effects-copyData-loop-recur-rsp-projection
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (< 4 m))
           (equal (xr :rgf *rsp* (x86-run (loop-clk-recur) x86))
                  (xr :rgf *rsp* x86)))
  :hints (("Goal" :use ((:instance effects-copyData-loop-recur))
           :in-theory (e/d* ()
                            (loop-clk-recur
                             (loop-clk-recur)
                             force (force))))))

(defthm effects-copyData-loop-recur-rsi-projection
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (< 4 m))
           (equal (xr :rgf *rsi* (x86-run (loop-clk-recur) x86))
                  (+ 4 (xr :rgf *rsi* x86))))
  :hints (("Goal" :use ((:instance effects-copyData-loop-recur))
           :in-theory (e/d* ()
                            (loop-clk-recur
                             (loop-clk-recur)
                             force (force))))))

(defthm effects-copyData-loop-recur-rdi-projection
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (< 4 m))
           (equal (xr :rgf *rdi* (x86-run (loop-clk-recur) x86))
                  (+ 4 (xr :rgf *rdi* x86))))
  :hints (("Goal"
           :use ((:instance effects-copyData-loop-recur))
           :in-theory (e/d* ()
                            (loop-clk-recur
                             (loop-clk-recur)
                             force (force))))))

(defthm effects-copyData-loop-recur-rax-projection
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (< 4 m))
           (equal (xr :rgf *rax* (x86-run (loop-clk-recur) x86))
                  (loghead 64 (+ #xfffffffffffffffc (xr :rgf *rax* x86)))))
  :hints (("Goal"
           :use ((:instance effects-copyData-loop-recur))
           :in-theory (e/d* ()
                            (loop-clk-recur
                             (loop-clk-recur)
                             force (force))))))

(defthm effects-copyData-loop-recur-rip-projection
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (< 4 m))
           (equal (xr :rip 0 (x86-run (loop-clk-recur) x86))
                  (xr :rip 0 x86)))
  :hints (("Goal"
           :use ((:instance effects-copyData-loop-recur))
           :in-theory (e/d* ()
                            (loop-clk-recur
                             (loop-clk-recur)
                             force (force))))))

(defthm effects-copyData-loop-recur-x86p-projection
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (< 4 m))
           (x86p (x86-run (loop-clk-recur) x86)))
  :hints (("Goal" :in-theory (e/d* ()
                                   (loop-clk-recur
                                    (loop-clk-recur)
                                    force (force))))))

(defthm effects-copyData-loop-recur-return-address-projection
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (< 4 m))
           (equal (mv-nth 1
                          (rb (create-canonical-address-list 8 (+ 8 (xr :rgf *rsp* x86)))
                              :r (x86-run (loop-clk-recur) x86)))
                  (mv-nth 1
                          (rb (create-canonical-address-list 8 (+ 8 (xr :rgf *rsp* x86)))
                              :r x86))))
  :hints (("Goal" :use ((:instance effects-copyData-loop-recur)
                        (:instance loop-preconditions-fwd-chain-to-its-body))
           :in-theory (e/d* ()
                            (loop-clk-recur
                             loop-preconditions-fwd-chain-to-its-body
                             loop-preconditions
                             effects-copyData-loop-recur
                             (loop-clk-recur)
                             force (force))))))

(defthm effects-copyData-loop-recur-implies-loop-preconditions
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (< 4 m))
           (loop-preconditions (+ 4 k)
                               (loghead 64 (+ #xfffffffffffffffc m))
                               addr (+ 4 src-addr)
                               (+ 4 dst-addr)
                               (x86-run (loop-clk-recur) x86)))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance loop-preconditions-fwd-chain-to-its-body))
           :expand (loop-preconditions (+ 4 k)
                                       (+ -4 (xr :rgf *rax* x86))
                                       (+ -16 (xr :rip 0 x86))
                                       (+ 4 (xr :rgf *rdi* x86))
                                       (+ 4 (xr :rgf *rsi* x86))
                                       (x86-run (loop-clk-recur) x86))
           :in-theory (e/d* (unsigned-byte-p
                             effects-copyData-loop-helper-11
                             effects-copyData-loop-helper-14)
                            (loop-clk-recur
                             rb-rb-split-reads
                             take-and-rb
                             destination-bytes
                             source-bytes
                             loop-preconditions
                             loop-preconditions-fwd-chain-to-its-body
                             (loop-clk-recur)
                             force (force))))))

(defun-nx loop-state (k m src-addr dst-addr x86)

  (if (signed-byte-p 64 m) ;; This should always be true.

      (if (<= m 4)

          (x86-run (loop-clk-base) x86)

        (b* ((new-m (loghead 64 (+ #xfffffffffffffffc m)))
             (new-k (+ 4 k))
             (new-src-addr (+ 4 src-addr))
             (new-dst-addr (+ 4 dst-addr))
             (x86 (x86-run (loop-clk-recur) x86)))
            (loop-state new-k new-m new-src-addr new-dst-addr x86)))
    x86))

(defthmd x86-run-plus-for-loop-clk-recur-1
  (equal (x86-run (loop-clk (loghead 64 (+ #xfffffffffffffffc m)))
                  (x86-run (loop-clk-recur) x86))
         (x86-run (binary-clk+ (loop-clk-recur)
                               (loop-clk (loghead 64 (+ #xfffffffffffffffc m))))
                  x86))
  :hints (("Goal" :in-theory (e/d* () (x86-run-plus (loop-clk-recur) loop-clk-recur))
           :use ((:instance x86-run-plus
                            (n2 (loop-clk (loghead 64 (+ #xfffffffffffffffc m))))
                            (n1 (loop-clk-recur)))))))

(defthm effects-copyData-loop
  (implies (loop-preconditions k m addr src-addr dst-addr x86)
           (equal (x86-run (loop-clk m) x86)
                  (loop-state k m src-addr dst-addr x86)))
  :hints (("Goal"
           :induct (cons (loop-state k m src-addr dst-addr x86) (loop-clk m))
           :in-theory (e/d* (instruction-decoding-and-spec-rules

                             gpr-and-spec-4
                             gpr-add-spec-8
                             jcc/cmovcc/setcc-spec
                             sal/shl-spec
                             sal/shl-spec-64

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
                             signed-byte-p

                             x86-run-plus-for-loop-clk-recur-1)
                            (loop-clk-base
                             (loop-clk-base)
                             (:type-prescription loop-clk-base)
                             loop-clk-recur
                             (loop-clk-recur)
                             (:type-prescription loop-clk-recur)
                             ;; [Shilpi]: Note that the executable-counterpart
                             ;; of loop-clk needs to be disabled, else
                             ;; (loop-clk-base) will be rewritten to 6,
                             ;; irrespective of whether loop-clk-base is
                             ;; completely disabled.
                             (loop-clk)
                             loop-preconditions
                             wb-remove-duplicate-writes
                             create-canonical-address-list
                             effects-copyData-loop-recur
                             effects-copyData-loop-base
                             force (force))))))

(defthm effects-copyData-loop-recur-source-address-projection-full-helper
  ;; src[src-addr to (src-addr + m)] in (x86-run (loop-clk-recur) x86) =
  ;; src[src-addr to (src-addr + m)] in x86
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (< 4 m))
           (equal (source-bytes m (+ m src-addr) (x86-run (loop-clk-recur) x86))
                  (source-bytes m (+ m src-addr) x86)))
  :hints (("Goal" :use ((:instance effects-copydata-loop-recur))
           :in-theory (e/d* ()
                            (loop-clk-recur
                             rb-rb-split-reads
                             take-and-rb
                             acl2::take-of-append
                             (loop-clk-recur)
                             force (force))))))

(defthm effects-copyData-loop-recur-source-address-projection-full
  ;; src[(+ -k src-addr) to (src-addr + m)] in (x86-run (loop-clk-recur) x86) =
  ;; src[(+ -k src-addr) to (src-addr + m)] in x86
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (< 4 m))
           (equal (source-bytes (+ m k) (+ m src-addr) (x86-run (loop-clk-recur) x86))
                  (source-bytes (+ m k) (+ m src-addr) x86)))
  :hints (("Goal" :use ((:instance effects-copydata-loop-recur)
                        (:instance effects-copyData-loop-recur-source-address-projection-copied)
                        (:instance effects-copyData-loop-recur-source-address-projection-original)
                        (:instance effects-copyData-loop-recur-source-address-projection-full-helper)
                        (:instance rb-rb-split-reads
                                   (k k)
                                   (j m)
                                   (r-w-x :x)
                                   (addr (+ (- k) (xr :rgf *rdi* x86)))
                                   (x86 (x86-run (loop-clk-recur) x86)))
                        (:instance rb-rb-split-reads
                                   (k k)
                                   (j (xr :rgf *rax* x86))
                                   (r-w-x :x)
                                   (addr (+ (- k) (xr :rgf *rdi* x86)))
                                   (x86 x86)))
           :in-theory (e/d* ()
                            (loop-clk-recur
                             effects-copyData-loop-recur-source-address-projection-full-helper
                             effects-copyData-loop-recur-source-address-projection-copied
                             effects-copyData-loop-recur-source-address-projection-original
                             rb-rb-split-reads
                             take-and-rb
                             acl2::take-of-append
                             (loop-clk-recur)
                             force (force))))))

(defthmd source-array-and-loop-state
  ;; src[(+ -k src-addr) to (src-addr + m)] in (loop-state k m src-addr dst-addr x86) =
  ;; src[(+ -k src-addr) to (src-addr + m)] in x86
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (natp k))
           (equal (source-bytes (+ k m) (+ m src-addr) (loop-state k m src-addr dst-addr x86))
                  (source-bytes (+ k m) (+ m src-addr) x86)))
  :hints (("Goal"
           :hands-off (x86-run)
           :in-theory (e/d* ()
                            (loop-preconditions
                             loop-invariant
                             source-bytes
                             source-bytes
                             loop-clk-recur
                             (loop-clk-recur)
                             loop-clk-base
                             (loop-clk-base)
                             create-canonical-address-list)))
          ("Subgoal *1/3"
           :use ((:instance effects-copyData-loop-recur-source-address-projection-full))
           :hands-off (x86-run)
           :in-theory (e/d* (effects-copyData-loop-helper-11)
                            (loop-preconditions
                             effects-copyData-loop-recur-source-address-projection-full
                             loop-invariant
                             destination-bytes
                             source-bytes
                             loop-clk-recur
                             (loop-clk-recur)
                             loop-clk-base
                             (loop-clk-base)
                             create-canonical-address-list)))))

(defthmd source-array-and-x86-state-after-loop-clk
  ;; src[(+ -k src-addr) to (src-addr + m)] in (loop-state k m src-addr src-addr x86) =
  ;; src[(+ -k src-addr) to (src-addr + m)] in x86
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (natp k))
           (equal (source-bytes (+ k m) (+ m src-addr) (x86-run (loop-clk m) x86))
                  (source-bytes (+ k m) (+ m src-addr) x86)))
  :hints (("Goal"
           :use ((:instance effects-copyData-loop)
                 (:instance source-array-and-loop-state))
           :hands-off (x86-run)
           :in-theory (e/d* ()
                            (effects-copyData-loop
                             loop-preconditions
                             effects-copyData-loop-recur-source-address-projection-full
                             loop-invariant
                             destination-bytes
                             source-bytes
                             loop-clk-recur
                             (loop-clk-recur)
                             loop-clk-base
                             (loop-clk-base)
                             loop-clk
                             (loop-clk)
                             create-canonical-address-list)))))

(defthm loop-leaves-m-bytes-of-source-unmodified
  ;; src[ src-addr to (src-addr + m) ] in (loop-state 0 m src-addr src-addr x86) =
  ;; src[ src-addr to (src-addr + m) ] in x86
  (implies (loop-preconditions 0 m addr src-addr dst-addr x86)
           (equal (source-bytes m (+ m src-addr) (x86-run (loop-clk m) x86))
                  (source-bytes m (+ m src-addr) x86)))
  :hints (("Goal"
           :use ((:instance source-array-and-x86-state-after-loop-clk
                            (k 0)))
           :hands-off (x86-run)
           :in-theory (e/d* ()
                            (loop-clk-recur
                             (loop-clk-recur)
                             loop-clk-base
                             destination-bytes
                             source-bytes
                             (loop-clk-base)
                             loop-preconditions
                             effects-copyData-loop
                             effects-copyData-loop-base
                             effects-copyData-loop-recur
                             force (force))))))

(defthmd destination-array-and-loop-state
  ;; dst[(+ -k dst-addr) to (dst-addr + m)] in (loop-state k m src-addr dst-addr x86) =
  ;; src[(+ -k src-addr) to (src-addr + m)] in x86
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (natp k))
           (equal (destination-bytes (+ k m) (+ m dst-addr) (loop-state k m src-addr dst-addr x86))
                  (source-bytes (+ k m) (+ m src-addr) x86)))
  :hints (("Goal"
           :hands-off (x86-run)
           :in-theory (e/d* ()
                            (loop-preconditions
                             loop-invariant
                             destination-bytes
                             source-bytes
                             loop-clk-recur
                             (loop-clk-recur)
                             loop-clk-base
                             (loop-clk-base)
                             create-canonical-address-list)))
          ("Subgoal *1/3"
           :use ((:instance effects-copyData-loop-recur-source-address-projection-full))
           :hands-off (x86-run)
           :in-theory (e/d* (effects-copyData-loop-helper-11)
                            (loop-preconditions
                             effects-copyData-loop-recur-source-address-projection-full
                             loop-invariant
                             destination-bytes
                             source-bytes
                             loop-clk-recur
                             (loop-clk-recur)
                             loop-clk-base
                             (loop-clk-base)
                             create-canonical-address-list)))))

(defthmd destination-array-and-x86-state-after-loop-clk
  ;; dst[(+ -k dst-addr) to (dst-addr + m)] in (loop-state k m src-addr dst-addr x86) =
  ;; src[(+ -k src-addr) to (src-addr + m)] in x86
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (natp k))
           (equal (destination-bytes (+ k m) (+ m dst-addr) (x86-run (loop-clk m) x86))
                  (source-bytes (+ k m) (+ m src-addr) x86)))
  :hints (("Goal"
           :use ((:instance effects-copyData-loop)
                 (:instance destination-array-and-loop-state))
           :hands-off (x86-run)
           :in-theory (e/d* ()
                            (effects-copyData-loop
                             loop-preconditions
                             effects-copyData-loop-recur-source-address-projection-full
                             loop-invariant
                             destination-bytes
                             source-bytes
                             loop-clk-recur
                             (loop-clk-recur)
                             loop-clk-base
                             (loop-clk-base)
                             loop-clk
                             (loop-clk)
                             create-canonical-address-list)))))

(defthm loop-copies-m-bytes-from-source-to-destination
  ;; dst[ dst-addr to (dst-addr + m) ] in (loop-state 0 m src-addr dst-addr x86) =
  ;; src[ src-addr to (src-addr + m) ] in x86
  (implies (loop-preconditions 0 m addr src-addr dst-addr x86)
           (equal (destination-bytes m (+ m dst-addr) (x86-run (loop-clk m) x86))
                  (source-bytes m (+ m src-addr) x86)))
  :hints (("Goal"
           :use ((:instance destination-array-and-x86-state-after-loop-clk
                            (k 0)))
           :hands-off (x86-run)
           :in-theory (e/d* ()
                            (loop-clk-recur
                             destination-array-and-loop-state
                             (loop-clk-recur)
                             loop-clk-base
                             destination-bytes
                             source-bytes
                             (loop-clk-base)
                             loop-preconditions
                             effects-copyData-loop
                             effects-copyData-loop-base
                             effects-copyData-loop-recur
                             force (force))))))

;; ======================================================================

(defun-nx preconditions (n addr x86)
  (and (x86p x86)
       (xr :programmer-level-mode 0 x86)
       (equal (xr :ms 0 x86) nil)
       (equal (xr :fault 0 x86) nil)
       ;; We are poised to run the copyData sub-routine.
       (equal (xr :rip 0 x86) addr)
       ;; n is n31p instead of n32p because in the C program, it's datatype is
       ;; "int" as opposed to "unsigned int". I could have used (signed-byte-p
       ;; 32 n) here, but I don't want to think about what will happen if
       ;; negative number of bytes are copied.
       (unsigned-byte-p 31 n)
       (equal (xr :rgf *rdx* x86) n)
       ;; All the stack addresses are canonical.
       (canonical-address-p (+ -8 (xr :rgf *rsp* x86)))
       (canonical-address-p (+ 8 (xr :rgf *rsp* x86)))
       ;; Return address of the copyData sub-routine is canonical.
       (canonical-address-p
        (logext
         64
         (combine-bytes
          (mv-nth 1
                  (rb (create-canonical-address-list 8 (xr :rgf *rsp* x86))
                      :r x86)))))
       ;; All the destination addresses are canonical.
       (canonical-address-p (xr :rgf *rsi* x86))
       (canonical-address-p (+ (ash n 2) (xr :rgf *rsi* x86)))
       ;; All the source addresses are canonical.
       (canonical-address-p (xr :rgf *rdi* x86))
       (canonical-address-p (+ (ash n 2) (xr :rgf *rdi* x86)))
       ;; Alignment Checking
       (if (alignment-checking-enabled-p x86)
           ;; rsi and rdi point to doublewords (four bytes), so their
           ;; natural boundary will be addresses divisible by 4.
           (and (equal (loghead 2 (xr :rgf *rsi* x86)) 0)
                (equal (loghead 2 (xr :rgf *rdi* x86)) 0)
                ;; rsp will be aligned to a 16-byte boundary.
                (equal (loghead 3 (+ -8 (xr :rgf *rsp* x86))) 0))
         t)
       ;; Memory locations of interest are disjoint.
       (disjoint-p
        ;; Return Addresses
        (create-canonical-address-list 8 (xr :rgf *rsp* x86))
        ;; Destination Addresses
        (create-canonical-address-list (ash n 2) (xr :rgf *rsi* x86)))
       (disjoint-p
        ;; Program addresses
        (create-canonical-address-list (len *copyData*) addr)
        ;; Destination addresses
        (create-canonical-address-list (ash n 2) (xr :rgf *rsi* x86)))
       (disjoint-p
        ;; Program addresses
        (create-canonical-address-list (len *copyData*) addr)
        ;; Stack
        (create-canonical-address-list 16 (+ -8 (xr :rgf *rsp* x86))))
       (disjoint-p
        ;; Source Addresses
        (create-canonical-address-list (ash n 2) (xr :rgf *rdi* x86))
        ;; Stack
        (create-canonical-address-list 16 (+ -8 (xr :rgf *rsp* x86))))
       (disjoint-p
        ;; Destination Addresses
        (create-canonical-address-list (ash n 2) (xr :rgf *rsi* x86))
        ;; Stack
        (create-canonical-address-list 16 (+ -8 (xr :rgf *rsp* x86))))
       (disjoint-p
        ;; Source Addresses
        (create-canonical-address-list (ash n 2) (xr :rgf *rdi* x86))
        ;; Destination Addresses
        (create-canonical-address-list (ash n 2) (xr :rgf *rsi* x86)))
       ;; Program is located at addr.
       ;; All program addresses are canonical.
       (canonical-address-p addr)
       (canonical-address-p (+ (len *copyData*) addr))
       (program-at (create-canonical-address-list (len *copyData*) addr)
                   *copyData* x86)))

(defthm preconditions-fwd-chain-to-its-body
  (implies (preconditions n addr x86)
           (and (x86p x86)
                (xr :programmer-level-mode 0 x86)
                (equal (xr :ms 0 x86) nil)
                (equal (xr :fault 0 x86) nil)
                ;; We are poised to run the copyData sub-routine.
                (equal (xr :rip 0 x86) addr)
                (unsigned-byte-p 31 n)
                (equal (xr :rgf *rdx* x86) n)
                ;; All the stack addresses are canonical.
                (canonical-address-p (+ -8 (xr :rgf *rsp* x86)))
                (canonical-address-p (+ 8 (xr :rgf *rsp* x86)))
                ;; Return address of the copyData sub-routine is canonical.
                (canonical-address-p
                 (logext
                  64
                  (combine-bytes
                   (mv-nth 1
                           (rb (create-canonical-address-list 8 (xr :rgf *rsp* x86))
                               :r x86)))))
                ;; All the destination addresses are canonical.
                (canonical-address-p (xr :rgf *rsi* x86))
                (canonical-address-p (+ (ash n 2) (xr :rgf *rsi* x86)))
                ;; All the source addresses are canonical.
                (canonical-address-p (xr :rgf *rdi* x86))
                (canonical-address-p (+ (ash n 2) (xr :rgf *rdi* x86)))
                ;; Alignment Checking
                (if (alignment-checking-enabled-p x86)
                    ;; rsi and rdi point to doublewords (four bytes), so their
                    ;; natural boundary will be addresses divisible by 4.
                    (and (equal (loghead 2 (xr :rgf *rsi* x86)) 0)
                         (equal (loghead 2 (xr :rgf *rdi* x86)) 0)
                         (equal (loghead 3 (+ -8 (xr :rgf *rsp* x86))) 0))
                  t)
                ;; Memory locations of interest are disjoint.
                (disjoint-p
                 ;; Return Addresses
                 (create-canonical-address-list 8 (xr :rgf *rsp* x86))
                 ;; Destination Addresses
                 (create-canonical-address-list (ash n 2) (xr :rgf *rsi* x86)))
                (disjoint-p
                 ;; Program addresses
                 (create-canonical-address-list (len *copyData*) addr)
                 ;; Destination addresses
                 (create-canonical-address-list (ash n 2) (xr :rgf *rsi* x86)))
                (disjoint-p
                 ;; Program addresses
                 (create-canonical-address-list (len *copyData*) addr)
                 ;; Stack
                 (create-canonical-address-list 16 (+ -8 (xr :rgf *rsp* x86))))
                (disjoint-p
                 ;; Source Addresses
                 (create-canonical-address-list (ash n 2) (xr :rgf *rdi* x86))
                 ;; Stack
                 (create-canonical-address-list 16 (+ -8 (xr :rgf *rsp* x86))))
                (disjoint-p
                 ;; Destination Addresses
                 (create-canonical-address-list (ash n 2) (xr :rgf *rsi* x86))
                 ;; Stack
                 (create-canonical-address-list 16 (+ -8 (xr :rgf *rsp* x86))))
                (disjoint-p
                 ;; Source Addresses
                 (create-canonical-address-list (ash n 2) (xr :rgf *rdi* x86))
                 ;; Destination Addresses
                 (create-canonical-address-list (ash n 2) (xr :rgf *rsi* x86)))
                ;; Program is located at addr.
                ;; All program addresses are canonical.
                (canonical-address-p addr)
                (canonical-address-p (+ (len *copyData*) addr))
                (program-at (create-canonical-address-list (len *copyData*) addr)
                            *copyData* x86)))
  :rule-classes :forward-chaining)

(defthm effects-copyData-pre
  (implies (preconditions n addr x86)
           (equal (x86-run (pre-clk n) x86)
                  (if (< 0 n)
                      (XW
                       :RGF *RAX*
                       (ASH (XR :RGF *RDX* X86) 2)
                       (XW
                        :RGF *RSP* (+ -8 (XR :RGF *RSP* X86))
                        (XW
                         :RGF *RBP* (+ -8 (XR :RGF *RSP* X86))
                         (XW
                          :RIP 0 (+ 16 (XR :RIP 0 X86))
                          (MV-NTH
                           1
                           (WB
                            (CREATE-ADDR-BYTES-ALIST
                             (CREATE-CANONICAL-ADDRESS-LIST 8 (+ -8 (XR :RGF *RSP* X86)))
                             (BYTE-IFY 8 (LOGHEAD 64 (XR :RGF *RBP* X86))))
                            (WRITE-USER-RFLAGS
                             (LOGIOR
                              (LOGHEAD 1
                                       (BOOL->BIT (LOGBITP 31 (XR :RGF *RDX* X86))))
                              (LOGHEAD
                               32
                               (ASH
                                (PF-SPEC64
                                 (LOGHEAD 64
                                          (ASH (LOGHEAD 64 (LOGEXT 32 (XR :RGF *RDX* X86)))
                                               2)))
                                2))
                              (LOGAND
                               4294967290
                               (LOGIOR
                                (LOGHEAD
                                 32
                                 (ASH
                                  (ZF-SPEC
                                   (LOGHEAD 64
                                            (ASH (LOGHEAD 64 (LOGEXT 32 (XR :RGF *RDX* X86)))
                                                 2)))
                                  6))
                                (LOGAND
                                 4294967230
                                 (LOGIOR
                                  (LOGHEAD
                                   32
                                   (ASH
                                    (SF-SPEC64
                                     (LOGHEAD 64
                                              (ASH (LOGHEAD 64 (LOGEXT 32 (XR :RGF *RDX* X86)))
                                                   2)))
                                    7))
                                  (LOGAND
                                   4294967166
                                   (BITOPS::LOGSQUASH
                                    1
                                    (XR
                                     :RFLAGS 0
                                     (WRITE-USER-RFLAGS
                                      (LOGIOR
                                       (LOGHEAD 32
                                                (ASH (PF-SPEC32 (XR :RGF *RDX* X86)) 2))
                                       (LOGAND
                                        4294967226
                                        (LOGIOR (LOGAND 4294965118
                                                        (BITOPS::LOGSQUASH 1 (XR :RFLAGS 0 X86)))
                                                (LOGHEAD 32
                                                         (ASH (SF-SPEC32 (XR :RGF *RDX* X86))
                                                              7)))))
                                      16 X86)))))))))
                             2064
                             (WRITE-USER-RFLAGS
                              (LOGIOR
                               (LOGHEAD 32
                                        (ASH (PF-SPEC32 (XR :RGF *RDX* X86)) 2))
                               (LOGAND 4294967226
                                       (LOGIOR (LOGAND 4294965118
                                                       (BITOPS::LOGSQUASH 1 (XR :RFLAGS 0 X86)))
                                               (LOGHEAD 32
                                                        (ASH (SF-SPEC32 (XR :RGF *RDX* X86))
                                                             7)))))
                              16 X86))))))))
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
                          16 X86)))))))))
  :hints (("Goal" :in-theory (e/d* (instruction-decoding-and-spec-rules

                                    gpr-and-spec-4
                                    jcc/cmovcc/setcc-spec
                                    sal/shl-spec
                                    sal/shl-spec-64

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
                                    subset-p)

                                   (wb-remove-duplicate-writes
                                    create-canonical-address-list
                                    force (force))))))

(defthm effects-copyData-pre-programmer-level-mode-projection
  (implies (preconditions n addr x86)
           (equal (xr :programmer-level-mode 0 (x86-run (pre-clk n) x86))
                  (xr :programmer-level-mode 0 x86)))
  :hints (("Goal"
           :use ((:instance effects-copydata-pre))
           :in-theory (e/d* ()
                            ((pre-clk) pre-clk force (force))))))

(defthm effects-copyData-pre-rsi-projection
  (implies (preconditions n addr x86)
           (equal (xr :rgf *rsi* (x86-run (pre-clk n) x86))
                  (xr :rgf *rsi* x86)))
  :hints (("Goal" :use ((:instance effects-copydata-pre))
           :in-theory (e/d* () ((pre-clk) pre-clk force (force))))))

(defthm effects-copyData-pre-rdi-projection
  (implies (preconditions n addr x86)
           (equal (xr :rgf *rdi* (x86-run (pre-clk n) x86))
                  (xr :rgf *rdi* x86)))
  :hints (("Goal" :use ((:instance effects-copydata-pre))
           :in-theory (e/d* ()
                            ((pre-clk) pre-clk force (force))))))

(defthm effects-copyData-pre-rsp-projection
  (implies (preconditions n addr x86)
           (equal (xr :rgf *rsp* (x86-run (pre-clk n) x86))
                  (+ -8 (xr :rgf *rsp* x86))))
  :hints (("Goal" :use ((:instance effects-copydata-pre))
           :in-theory (e/d* ()
                            ((pre-clk) pre-clk force (force))))))

(defthm effects-copyData-pre-rax-projection
  (implies (and (preconditions n addr x86)
                (not (zp n)))
           (equal (xr :rgf *rax* (x86-run (pre-clk n) x86))
                  (ash n 2)))
  :hints (("Goal" :use ((:instance effects-copydata-pre))
           :in-theory (e/d* ()
                            ((pre-clk) pre-clk force (force))))))

(defthm effects-copyData-pre-program-at-projection
  (implies (and (preconditions n addr x86)
                (equal prog-len (len *copydata*)))
           (equal (program-at (create-canonical-address-list prog-len addr)
                              *copyData* (x86-run (pre-clk n) x86))
                  (program-at (create-canonical-address-list prog-len addr)
                              *copyData* x86)))
  :hints (("Goal" :use ((:instance effects-copydata-pre))
           :in-theory (e/d* ()
                            ((pre-clk) pre-clk force (force))))))

(defthm effects-copyData-pre-fault-projection
  (implies (preconditions n addr x86)
           (equal (xr :fault 0 (x86-run (pre-clk n) x86))
                  (xr :fault 0 x86)))
  :hints (("Goal" :use ((:instance effects-copydata-pre))
           :in-theory (e/d* ()
                            ((pre-clk) pre-clk force (force))))))

(defthm effects-copyData-pre-ms-projection
  (implies (preconditions n addr x86)
           (equal (xr :ms 0 (x86-run (pre-clk n) x86))
                  (xr :ms 0 x86)))
  :hints (("Goal" :use ((:instance effects-copydata-pre))
           :in-theory (e/d* ()
                            ((pre-clk) pre-clk force (force))))))

(defthm effects-copyData-pre-rip-projection
  (implies (and (preconditions n addr x86)
                (not (zp n)))
           (equal (xr :rip 0 (x86-run (pre-clk n) x86))
                  (+ 16 (xr :rip 0 x86))))
  :hints (("Goal" :use ((:instance effects-copydata-pre))
           :in-theory (e/d* ()
                            ((pre-clk) pre-clk force (force))))))

(defthm effects-copyData-pre-x86p-projection
  (implies (preconditions n addr x86)
           (x86p (x86-run (pre-clk n) x86)))
  :hints (("Goal" :in-theory (e/d* () ((pre-clk) pre-clk force (force))))))

(defthm effects-copyData-pre-return-address-projection
  (implies (preconditions n addr x86)
           (equal (mv-nth 1
                          (rb (create-canonical-address-list 8 (xr :rgf *rsp* x86))
                              :r (x86-run (pre-clk n) x86)))
                  (mv-nth 1
                          (rb (create-canonical-address-list 8 (xr :rgf *rsp* x86))
                              :r x86))))
  :hints (("Goal" :use ((:instance effects-copydata-pre))
           :in-theory (e/d* (canonical-address-p-limits-thm-3)
                            ((pre-clk) pre-clk force (force)
                             preconditions)))))

(defthm effects-copyData-pre-alignment-checking-enabled-p-projection
  (implies (preconditions n addr x86)
           (equal (alignment-checking-enabled-p (x86-run (pre-clk n) x86))
                  (alignment-checking-enabled-p x86)))
  :hints (("Goal"
           :use ((:instance effects-copydata-pre))
           :in-theory (e/d* (alignment-checking-enabled-p)
                            ((pre-clk) pre-clk force (force))))))

(defthm preconditions-implies-loop-preconditions-after-pre-clk
  (implies (and (preconditions n addr x86)
                (not (zp n))
                (equal m (ash n 2)))
           (loop-preconditions
            0 m addr
            (xr :rgf *rdi* x86) ;; src-addr
            (xr :rgf *rsi* x86) ;; dst-addr
            (x86-run (pre-clk n) x86)))
  :hints (("Goal" :hands-off (x86-run)
           :use ((:instance preconditions-fwd-chain-to-its-body))
           :in-theory (e/d* (unsigned-byte-p
                             canonical-address-p-limits-thm-3)
                            (pre-clk
                             (pre-clk) preconditions
                             preconditions-fwd-chain-to-its-body)))))

(defthmd x86-run-plus-for-clk
  (equal (x86-run (binary-clk+ (pre-clk n) (loop-clk (ash n 2))) x86)
         (x86-run (loop-clk (ash n 2)) (x86-run (pre-clk n) x86)))
  :hints (("Goal" :in-theory (e/d* (binary-clk+)
                                   (x86-run-plus
                                    (loop-clk)
                                    loop-clk
                                    pre-clk
                                    (pre-clk)))
           :use ((:instance x86-run-plus
                            (n2 (loop-clk (ash n 2)))
                            (n1 (pre-clk n)))))))

(defthmd pre+loop-copies-m-bytes-from-source-to-destination-helper-1
  (implies (and (preconditions n addr x86)
                (not (zp n))
                (equal m (ash n 2)))
           (equal (destination-bytes m (+ m (xr :rgf *rsi* x86)) (x86-run (clk n) x86))
                  (source-bytes m (+ m (xr :rgf *rdi* x86)) (x86-run (pre-clk n) x86))))
  :hints (("Goal"
           :use ((:instance preconditions-implies-loop-preconditions-after-pre-clk))
           :in-theory (e/d* (x86-run-plus-for-clk)
                            (wb-remove-duplicate-writes
                             effects-copydata-loop
                             preconditions-implies-loop-preconditions-after-pre-clk
                             loop-preconditions
                             effects-copydata-pre
                             preconditions
                             destination-bytes
                             source-bytes
                             (loop-clk)
                             loop-clk
                             pre-clk
                             (pre-clk)
                             create-canonical-address-list
                             force (force))))))

(defthmd pre+loop-copies-m-bytes-from-source-to-destination-helper-2
  (implies (and (preconditions n addr x86)
                (not (zp n))
                (equal m (ash n 2)))
           (equal (source-bytes m (+ m (xr :rgf *rdi* x86)) (x86-run (pre-clk n) x86))
                  (source-bytes m (+ m (xr :rgf *rdi* x86)) x86)))
  :hints (("Goal"
           :in-theory (e/d* ()
                            (wb-remove-duplicate-writes
                             preconditions-implies-loop-preconditions-after-pre-clk
                             preconditions
                             destination-bytes
                             (loop-clk)
                             loop-clk
                             pre-clk
                             (pre-clk)
                             create-canonical-address-list
                             force (force))))))

(defthm pre+loop-copies-m-bytes-from-source-to-destination
  (implies (and (preconditions n addr x86)
                (not (zp n))
                (equal m (ash n 2)))
           (equal (destination-bytes m (+ m (xr :rgf *rsi* x86)) (x86-run (clk n) x86))
                  (source-bytes m (+ m (xr :rgf *rdi* x86)) x86)))
  :hints (("Goal"
           :use ((:instance pre+loop-copies-m-bytes-from-source-to-destination-helper-1)
                 (:instance pre+loop-copies-m-bytes-from-source-to-destination-helper-2))
           :in-theory (e/d* ()
                            (wb-remove-duplicate-writes
                             preconditions-implies-loop-preconditions-after-pre-clk
                             loop-copies-m-bytes-from-source-to-destination
                             effects-copydata-pre
                             preconditions
                             destination-bytes
                             source-bytes
                             (loop-clk)
                             loop-clk
                             pre-clk
                             clk
                             (pre-clk)
                             create-canonical-address-list
                             force (force))))))

(defthm pre+loop-leaves-m-bytes-of-source-unmodified
  (implies (and (preconditions n addr x86)
                (not (zp n))
                (equal m (ash n 2)))
           (equal (source-bytes m (+ m (xr :rgf *rdi* x86)) (x86-run (clk n) x86))
                  (source-bytes m (+ m (xr :rgf *rdi* x86)) x86)))
  :hints (("Goal"
           :use ((:instance preconditions-implies-loop-preconditions-after-pre-clk)
                 (:instance pre+loop-copies-m-bytes-from-source-to-destination-helper-2))
           :in-theory (e/d* (x86-run-plus-for-clk)
                            (wb-remove-duplicate-writes
                             loop-preconditions
                             preconditions-implies-loop-preconditions-after-pre-clk
                             loop-copies-m-bytes-from-source-to-destination
                             effects-copydata-pre
                             effects-copydata-loop
                             preconditions
                             destination-bytes
                             source-bytes
                             (loop-clk)
                             loop-clk
                             pre-clk
                             (pre-clk)
                             create-canonical-address-list
                             force (force))))))

;; Now, to prove a theorem similar to
;; pre+loop-copies-m-bytes-from-source-to-destination, but in terms of
;; program-clk...

(defthm loop-state-programmer-level-mode-projection
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (natp k))
           (equal (xr :programmer-level-mode 0 (loop-state k m src-addr dst-addr x86))
                  (xr :programmer-level-mode 0 x86)))
  :hints (("Goal"
           :hands-off (x86-run)
           :in-theory (e/d* ()
                            (loop-preconditions
                             loop-invariant
                             destination-bytes
                             source-bytes
                             loop-clk-recur
                             (loop-clk-recur)
                             loop-clk-base
                             (loop-clk-base)
                             create-canonical-address-list
                             force (force))))))

(defthm loop-clk-programmer-level-mode-projection
  (implies (loop-preconditions 0 m addr src-addr dst-addr x86)
           (equal (xr :programmer-level-mode 0 (x86-run (loop-clk m) x86))
                  (xr :programmer-level-mode 0 x86)))
  :hints (("Goal"
           :use ((:instance effects-copydata-loop (k 0)))
           :hands-off (x86-run)
           :in-theory (e/d* ()
                            (loop-preconditions
                             (loop-clk) loop-clk
                             effects-copydata-loop
                             create-canonical-address-list)))))

(defthm loop-state-program-at-projection
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (natp k)
                (equal prog-len (len *copydata*)))
           (equal (program-at (create-canonical-address-list prog-len addr)
                              *copyData* (loop-state k m src-addr dst-addr x86))
                  (program-at (create-canonical-address-list prog-len addr)
                              *copyData* x86)))
  :hints (("Goal"
           :hands-off (x86-run)
           :in-theory (e/d* ()
                            (loop-preconditions
                             loop-invariant
                             destination-bytes
                             source-bytes
                             loop-clk-recur
                             (loop-clk-recur)
                             loop-clk-base
                             (loop-clk-base)
                             create-canonical-address-list)))))

(defthm loop-clk-program-at-projection
  (implies (and (loop-preconditions 0 m addr src-addr dst-addr x86)
                (equal prog-len (len *copydata*)))
           (equal (program-at (create-canonical-address-list prog-len addr)
                              *copyData* (x86-run (loop-clk m) x86))
                  (program-at (create-canonical-address-list prog-len addr)
                              *copyData* x86)))
  :hints (("Goal"
           :use ((:instance effects-copydata-loop (k 0)))
           :hands-off (x86-run)
           :in-theory (e/d* ()
                            (loop-preconditions
                             (loop-clk) loop-clk
                             effects-copydata-loop
                             create-canonical-address-list)))))

(defthm loop-state-ms-projection
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (natp k))
           (equal (xr :ms 0 (loop-state k m src-addr dst-addr x86))
                  (xr :ms 0 x86)))
  :hints (("Goal"
           :hands-off (x86-run)
           :in-theory (e/d* ()
                            (loop-preconditions
                             loop-invariant
                             destination-bytes
                             source-bytes
                             loop-clk-recur
                             (loop-clk-recur)
                             loop-clk-base
                             (loop-clk-base)
                             create-canonical-address-list)))))

(defthm loop-clk-ms-projection
  (implies (loop-preconditions 0 m addr src-addr dst-addr x86)
           (equal (xr :ms 0 (x86-run (loop-clk m) x86))
                  (xr :ms 0 x86)))
  :hints (("Goal"
           :use ((:instance effects-copydata-loop (k 0)))
           :hands-off (x86-run)
           :in-theory (e/d* ()
                            (loop-preconditions
                             (loop-clk) loop-clk
                             effects-copydata-loop
                             create-canonical-address-list)))))

(defthm loop-state-fault-projection
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (natp k))
           (equal (xr :fault 0 (loop-state k m src-addr dst-addr x86))
                  (xr :fault 0 x86)))
  :hints (("Goal"
           :hands-off (x86-run)
           :in-theory (e/d* ()
                            (loop-preconditions
                             loop-invariant
                             destination-bytes
                             source-bytes
                             loop-clk-recur
                             (loop-clk-recur)
                             loop-clk-base
                             (loop-clk-base)
                             create-canonical-address-list)))))

(defthm loop-clk-fault-projection
  (implies (loop-preconditions 0 m addr src-addr dst-addr x86)
           (equal (xr :fault 0 (x86-run (loop-clk m) x86))
                  (xr :fault 0 x86)))
  :hints (("Goal"
           :use ((:instance effects-copydata-loop (k 0)))
           :hands-off (x86-run)
           :in-theory (e/d* ()
                            (loop-preconditions
                             (loop-clk) loop-clk
                             effects-copydata-loop
                             create-canonical-address-list)))))

(defthm loop-state-rip-projection
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (natp k))
           (equal (xr :rip 0 (loop-state k m src-addr dst-addr x86))
                  (+ 18 (xr :rip 0 x86))))
  :hints (("Goal"
           :hands-off (x86-run)
           :in-theory (e/d* ()
                            (loop-preconditions
                             loop-invariant
                             destination-bytes
                             source-bytes
                             loop-clk-recur
                             (loop-clk-recur)
                             loop-clk-base
                             (loop-clk-base)
                             create-canonical-address-list)))))

(defthm loop-clk-rip-projection
  (implies (loop-preconditions 0 m addr src-addr dst-addr x86)
           (equal (xr :rip 0 (x86-run (loop-clk m) x86))
                  (+ 18 (xr :rip 0 x86))))
  :hints (("Goal"
           :use ((:instance effects-copydata-loop (k 0)))
           :hands-off (x86-run)
           :in-theory (e/d* ()
                            (loop-preconditions
                             (loop-clk) loop-clk
                             effects-copydata-loop
                             create-canonical-address-list)))))

(defthm loop-state-rsp-projection
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (natp k))
           (equal (xr :rgf *rsp* (loop-state k m src-addr dst-addr x86))
                  (xr :rgf *rsp* x86)))
  :hints (("Goal"
           :hands-off (x86-run)
           :in-theory (e/d* ()
                            (loop-preconditions
                             loop-invariant
                             destination-bytes
                             source-bytes
                             loop-clk-recur
                             (loop-clk-recur)
                             loop-clk-base
                             (loop-clk-base)
                             create-canonical-address-list)))))

(defthm loop-clk-rsp-projection
  (implies (loop-preconditions 0 m addr src-addr dst-addr x86)
           (equal (xr :rgf *rsp* (x86-run (loop-clk m) x86))
                  (xr :rgf *rsp* x86)))
  :hints (("Goal"
           :use ((:instance effects-copydata-loop (k 0)))
           :hands-off (x86-run)
           :in-theory (e/d* ()
                            (loop-preconditions
                             (loop-clk) loop-clk
                             effects-copydata-loop
                             create-canonical-address-list)))))

(defthm loop-state-rsi-projection
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (natp k))
           (equal (xr :rgf *rsi* (loop-state k m src-addr dst-addr x86))
                  (+ m dst-addr)))
  :hints (("Goal"
           :hands-off (x86-run)
           :in-theory (e/d* ()
                            (loop-preconditions
                             loop-invariant
                             destination-bytes
                             source-bytes
                             loop-clk-recur
                             (loop-clk-recur)
                             loop-clk-base
                             (loop-clk-base)
                             create-canonical-address-list)))
          ("Subgoal *1/3" :in-theory (e/d* (effects-copyData-loop-helper-11)
                                           (loop-preconditions)))))

(defthm loop-clk-rsi-projection
  (implies (loop-preconditions 0 m addr src-addr dst-addr x86)
           (equal (xr :rgf *rsi* (x86-run (loop-clk m) x86))
                  (+ m dst-addr)))
  :hints (("Goal"
           :use ((:instance effects-copydata-loop (k 0)))
           :hands-off (x86-run)
           :in-theory (e/d* ()
                            (loop-preconditions
                             (loop-clk) loop-clk
                             effects-copydata-loop
                             create-canonical-address-list)))))

(defthm clk-rsi-projection
  (implies (preconditions n addr x86)
           (equal (xr :rgf *rsi* (x86-run (clk n) x86))
                  (+ (ash n 2) (xr :rgf *rsi* x86))))
  :hints (("Goal"
           :use ((:instance preconditions-implies-loop-preconditions-after-pre-clk
                            (m (ash n 2))))
           :in-theory (e/d* (x86-run-plus-for-clk)
                            (loop-preconditions
                             preconditions-implies-loop-preconditions-after-pre-clk
                             preconditions
                             (loop-clk) loop-clk (pre-clk)
                             (clk)
                             pre-clk
                             effects-copydata-loop
                             effects-copydata-pre
                             create-canonical-address-list)))))

(defthm loop-state-rdi-projection
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (natp k))
           (equal (xr :rgf *rdi* (loop-state k m src-addr dst-addr x86))
                  (+ m src-addr)))
  :hints (("Goal"
           :hands-off (x86-run)
           :in-theory (e/d* ()
                            (loop-preconditions
                             loop-invariant
                             destination-bytes
                             source-bytes
                             loop-clk-recur
                             (loop-clk-recur)
                             loop-clk-base
                             (loop-clk-base)
                             create-canonical-address-list)))
          ("Subgoal *1/3" :in-theory (e/d* (effects-copyData-loop-helper-11)
                                           (loop-preconditions)))))

(defthm loop-clk-rdi-projection
  (implies (loop-preconditions 0 m addr src-addr dst-addr x86)
           (equal (xr :rgf *rdi* (x86-run (loop-clk m) x86))
                  (+ m src-addr)))
  :hints (("Goal"
           :use ((:instance effects-copydata-loop (k 0)))
           :hands-off (x86-run)
           :in-theory (e/d* ()
                            (loop-preconditions
                             (loop-clk) loop-clk
                             effects-copydata-loop
                             create-canonical-address-list)))))

(defthm clk-rdi-projection
  (implies (preconditions n addr x86)
           (equal (xr :rgf *rdi* (x86-run (clk n) x86))
                  (+ (ash n 2) (xr :rgf *rdi* x86))))
  :hints (("Goal"
           :use ((:instance preconditions-implies-loop-preconditions-after-pre-clk
                            (m (ash n 2))))
           :in-theory (e/d* (x86-run-plus-for-clk)
                            (loop-preconditions
                             preconditions-implies-loop-preconditions-after-pre-clk
                             preconditions
                             (loop-clk) loop-clk (pre-clk)
                             (clk)
                             pre-clk
                             effects-copydata-loop
                             effects-copydata-pre
                             create-canonical-address-list)))))

(defthm loop-state-return-address-projection
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (natp k))
           (equal (mv-nth 1
                          (rb (create-canonical-address-list
                               8 (+ 8 (xr :rgf *rsp* x86)))
                              :r (loop-state k m src-addr dst-addr x86)))
                  (mv-nth 1
                          (rb (create-canonical-address-list
                               8 (+ 8 (xr :rgf *rsp* x86)))
                              :r x86))))
  :hints (("Goal"
           :hands-off (x86-run)
           :in-theory (e/d* ()
                            (loop-preconditions
                             loop-invariant
                             destination-bytes
                             source-bytes
                             loop-clk-recur
                             (loop-clk-recur)
                             loop-clk-base
                             (loop-clk-base)
                             create-canonical-address-list)))))

(defthm loop-clk-return-address-projection
  (implies (loop-preconditions 0 m addr src-addr dst-addr x86)
           (equal (mv-nth 1
                          (rb (create-canonical-address-list
                               8 (+ 8 (xr :rgf *rsp* x86)))
                              :r (x86-run (loop-clk m) x86)))
                  (mv-nth 1
                          (rb (create-canonical-address-list
                               8 (+ 8 (xr :rgf *rsp* x86)))
                              :r x86))))
  :hints (("Goal"
           :use ((:instance effects-copydata-loop (k 0)))
           :hands-off (x86-run)
           :in-theory (e/d* ()
                            (loop-preconditions
                             (loop-clk) loop-clk
                             effects-copydata-loop
                             create-canonical-address-list)))))

(defthm loop-state-alignment-checking-enabled-p-projection
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (natp k))
           (equal (alignment-checking-enabled-p (loop-state k m src-addr dst-addr x86))
                  (alignment-checking-enabled-p x86)))
  :hints (("Goal"
           :hands-off (x86-run)
           :in-theory (e/d* ()
                            (loop-preconditions
                             loop-invariant
                             destination-bytes
                             source-bytes
                             loop-clk-recur
                             (loop-clk-recur)
                             loop-clk-base
                             (loop-clk-base)
                             create-canonical-address-list)))))

(defthm loop-clk-alignment-checking-enabled-p-projection
  (implies (loop-preconditions 0 m addr src-addr dst-addr x86)
           (equal (alignment-checking-enabled-p (x86-run (loop-clk m) x86))
                  (alignment-checking-enabled-p x86)))
  :hints (("Goal"
           :use ((:instance effects-copydata-loop (k 0)))
           :hands-off (x86-run)
           :in-theory (e/d* ()
                            (loop-preconditions
                             (loop-clk) loop-clk
                             effects-copydata-loop
                             create-canonical-address-list)))))

(defun-nx after-the-copy-conditions (n addr x86)
  (and (x86p x86)
       (xr :programmer-level-mode 0 x86)
       (equal (xr :ms 0 x86) nil)
       (equal (xr :fault 0 x86) nil)
       ;; We are poised to run the last two instructions.
       (equal addr (+ -34 (xr :rip 0 x86)))
       ;; All the stack addresses are canonical.
       (canonical-address-p (xr :rgf *rsp* x86))
       (canonical-address-p (+ 16 (xr :rgf *rsp* x86)))
       ;; The value of the return address is canonical.
       (canonical-address-p
        (logext 64
                (combine-bytes
                 (mv-nth 1 (rb
                            (create-canonical-address-list 8 (+ 8 (xr :rgf *rsp* x86)))
                            :r x86)))))
       ;; Alignment Checking
       (if (alignment-checking-enabled-p x86)
           (equal (loghead 3 (xr :rgf *rsp* x86)) 0)
         t)
       ;; All program addresses are canonical.
       (canonical-address-p addr)
       ;; [Shilpi]: Why not (canonical-address-p (+ -1 (len *copyData*) addr))?
       ;; In case of instructions like ret and jump, hyp 20 of
       ;; x86-fetch-decode-execute-opener doesn't apply. Modify?
       ;; (CANONICAL-ADDRESS-P$INLINE (BINARY-+ '2 (XR ':RIP '0 X86)))
       (canonical-address-p (+ (len *copyData*) addr))
       (program-at (create-canonical-address-list (len *copyData*) addr)
                   *copyData* x86)))

(defthmd preconditions-implies-after-the-copy-conditions-after-clk-helper
  (implies (and (loop-preconditions 0 (ash n 2)
                                    addr (xr :rgf *rdi* x86)
                                    (xr :rgf *rsi* x86)
                                    (x86-run (pre-clk n) x86))
                (preconditions n addr x86)
                (< 0 n))
           (canonical-address-p
            (logext
             64
             (combine-bytes
              (mv-nth
               1
               (rb (create-canonical-address-list 8 (+ 8 (xr :rgf *rsp* (x86-run (pre-clk n) x86))))
                   :r (x86-run (loop-clk (ash n 2)) (x86-run (pre-clk n) x86))))))))
  :hints (("Goal"
           :hands-off (x86-run)
           :in-theory (e/d* ()
                            ((loop-clk)
                             loop-clk
                             (pre-clk)
                             pre-clk
                             effects-copyData-loop
                             effects-copyData-pre-rsp-projection
                             preconditions
                             loop-preconditions
                             preconditions-implies-loop-preconditions-after-pre-clk
                             effects-copydata-pre)))))

(defthm preconditions-implies-after-the-copy-conditions-after-clk
  (implies (and (preconditions n addr x86)
                (not (zp n))
                (equal m (ash n 2)))
           (after-the-copy-conditions n addr (x86-run (clk n) x86)))
  :hints (("Goal"
           :use ((:instance preconditions-fwd-chain-to-its-body)
                 (:instance preconditions-implies-after-the-copy-conditions-after-clk-helper)
                 (:instance effects-copyData-pre-rsp-projection)
                 (:instance preconditions-implies-loop-preconditions-after-pre-clk)
                 (:instance effects-copyData-loop
                            (k 0) (src-addr (xr :rgf *rdi* x86))
                            (dst-addr (xr :rgf *rsi* x86))))
           :in-theory (e/d* (x86-run-plus-for-clk)
                            ((loop-clk)
                             loop-clk
                             (pre-clk)
                             pre-clk
                             effects-copyData-loop
                             effects-copyData-pre-rsp-projection
                             preconditions
                             loop-preconditions
                             preconditions-implies-loop-preconditions-after-pre-clk
                             effects-copydata-pre)))))

(defthmd effects-copyData-after-clk
  (implies (after-the-copy-conditions n addr x86)
           (equal (x86-run (post-clk) x86)
                  (XW
                   :RGF *RSP* (+ 16 (XR :RGF *RSP* X86))
                   (XW
                    :RGF *RBP*
                    (LOGEXT
                     64
                     (COMBINE-BYTES
                      (MV-NTH 1
                              (RB (CREATE-CANONICAL-ADDRESS-LIST 8 (XR :RGF *RSP* X86))
                                  :R X86))))
                    (XW
                     :RIP 0
                     (LOGEXT
                      64
                      (COMBINE-BYTES
                       (MV-NTH
                        1
                        (RB (CREATE-CANONICAL-ADDRESS-LIST 8 (+ 8 (XR :RGF *RSP* X86)))
                            :R X86))))
                     X86)))))
  :hints (("Goal"
           :in-theory (e/d* (instruction-decoding-and-spec-rules
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
                             rim64
                             n32-to-i32
                             n64-to-i64
                             rim08
                             two-byte-opcode-decode-and-execute
                             x86-effective-addr
                             subset-p
                             signed-byte-p)
                            (wb-remove-duplicate-writes
                             create-canonical-address-list)))))

(defthmd x86-run-plus-for-program-clk
  (equal (x86-run (binary-clk+ (clk n) (post-clk)) x86)
         (x86-run (post-clk) (x86-run (clk n) x86)))
  :hints (("Goal" :in-theory (e/d* (binary-clk+)
                                   (x86-run-plus
                                    (loop-clk)
                                    loop-clk
                                    pre-clk
                                    (pre-clk)))
           :use ((:instance x86-run-plus
                            (n1 (clk n))
                            (n2 (post-clk)))))))

(defthmd program-copies-m-bytes-from-source-to-destination-till-finish-helper-1
  ;; (xr :rgf *rsi* x86) here is really (+ m (xr :rgf *rsi* x86_0)), where
  ;; x86_0 is the state before the loop.
  (implies (and (after-the-copy-conditions n addr x86)
                (not (zp n))
                (equal m (ash n 2)))
           (equal (destination-bytes m (xr :rgf *rsi* x86) (x86-run (post-clk) x86))
                  (destination-bytes m (xr :rgf *rsi* x86) x86)))
  :hints (("Goal" :use ((:instance effects-copyData-after-clk))
           :in-theory (e/d* ()
                            (wb-remove-duplicate-writes
                             preconditions-implies-loop-preconditions-after-pre-clk
                             loop-copies-m-bytes-from-source-to-destination
                             effects-copydata-pre
                             preconditions
                             source-bytes
                             clk post-clk
                             (clk) (post-clk)
                             create-canonical-address-list
                             force (force))))))

(defthm program-copies-m-bytes-from-source-to-destination-till-finish-helper-2
  (implies (and (preconditions n addr x86)
                (not (zp n))
                (equal m (ash n 2)))
           (equal (destination-bytes m (+ m (xr :rgf *rsi* x86)) (x86-run (program-clk n) x86))
                  (source-bytes m (+ m (xr :rgf *rdi* x86)) x86)))
  :hints (("Goal"
           :use ((:instance preconditions-implies-after-the-copy-conditions-after-clk)
                 (:instance program-copies-m-bytes-from-source-to-destination-till-finish-helper-1
                            (x86 (x86-run (clk n) x86))))
           :in-theory (e/d* (x86-run-plus-for-program-clk)
                            (wb-remove-duplicate-writes
                             after-the-copy-conditions
                             preconditions-implies-loop-preconditions-after-pre-clk
                             preconditions-implies-after-the-copy-conditions-after-clk
                             loop-copies-m-bytes-from-source-to-destination
                             effects-copydata-pre
                             preconditions
                             destination-bytes
                             source-bytes
                             clk post-clk
                             (clk) (post-clk)
                             create-canonical-address-list
                             force (force))))))

(defthmd program-leaves-m-bytes-of-source-unmodified-helper-1
  ;; (xr :rgf *rsi* x86) here is really (+ m (xr :rgf *rsi* x86_0)), where
  ;; x86_0 is the state before the loop.
  (implies (and (after-the-copy-conditions n addr x86)
                (not (zp n))
                (equal m (ash n 2)))
           (equal (source-bytes m (xr :rgf *rdi* x86) (x86-run (post-clk) x86))
                  (source-bytes m (xr :rgf *rdi* x86) x86)))
  :hints (("Goal" :use ((:instance effects-copyData-after-clk))
           :in-theory (e/d* ()
                            (wb-remove-duplicate-writes
                             preconditions-implies-loop-preconditions-after-pre-clk
                             loop-copies-m-bytes-from-source-to-destination
                             effects-copydata-pre
                             preconditions
                             clk post-clk
                             (clk) (post-clk)
                             create-canonical-address-list
                             force (force))))))

(defthmd program-leaves-m-bytes-of-source-unmodified-helper-2
  (implies (and (preconditions n addr x86)
                (not (zp n))
                (equal m (ash n 2)))
           (equal (source-bytes m (+ m (xr :rgf *rdi* x86)) (x86-run (program-clk n) x86))
                  (source-bytes m (+ m (xr :rgf *rdi* x86)) x86)))
  :hints (("Goal"
           :use ((:instance preconditions-implies-after-the-copy-conditions-after-clk)
                 (:instance program-leaves-m-bytes-of-source-unmodified-helper-1
                            (x86 (x86-run (clk n) x86))))
           :in-theory (e/d* (x86-run-plus-for-program-clk)
                            (wb-remove-duplicate-writes
                             after-the-copy-conditions
                             preconditions-implies-loop-preconditions-after-pre-clk
                             preconditions-implies-after-the-copy-conditions-after-clk
                             loop-copies-m-bytes-from-source-to-destination
                             effects-copydata-pre
                             preconditions
                             destination-bytes
                             source-bytes
                             clk post-clk
                             (clk) (post-clk)
                             create-canonical-address-list
                             force (force))))))

;; ======================================================================

;; Now, the top-level theorems:

(defthm destination-array-is-a-copy-of-the-source-array
  (implies (and (preconditions n addr x86)
                (equal m (ash n 2)))
           (equal (destination-bytes m (+ m (xr :rgf *rsi* x86)) (x86-run (program-clk n) x86))
                  (source-bytes m (+ m (xr :rgf *rdi* x86)) x86)))
  :hints (("Goal"
           :use ((:instance program-copies-m-bytes-from-source-to-destination-till-finish-helper-2))
           :in-theory (e/d* ()
                            (wb-remove-duplicate-writes
                             program-copies-m-bytes-from-source-to-destination-till-finish-helper-2
                             after-the-copy-conditions
                             preconditions
                             clk post-clk pre-clk
                             (clk) (post-clk) (pre-clk)
                             create-canonical-address-list
                             force (force))))))

(defthm source-array-is-unmodified
  (implies (and (preconditions n addr x86)
                (equal m (ash n 2)))
           (equal (source-bytes m (+ m (xr :rgf *rdi* x86)) (x86-run (program-clk n) x86))
                  (source-bytes m (+ m (xr :rgf *rdi* x86)) x86)))
  :hints (("Goal" :use ((:instance program-leaves-m-bytes-of-source-unmodified-helper-2))
           :in-theory (e/d* ()
                            (wb-remove-duplicate-writes
                             after-the-copy-conditions
                             preconditions
                             clk post-clk pre-clk
                             (clk) (post-clk) (pre-clk)
                             create-canonical-address-list
                             force (force))))))

;; ======================================================================
