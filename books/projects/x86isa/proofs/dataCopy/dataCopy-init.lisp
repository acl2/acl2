;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")

(include-book "programmer-level-mode/programmer-level-memory-utils" :dir :proof-utils :ttags :all)
(include-book "centaur/bitops/ihs-extensions" :dir :system)

(local (include-book "centaur/bitops/signed-byte-p" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))

(local (in-theory (e/d* (rb-rb-subset)
                        (mv-nth-1-wb-and-!flgi-commute
                         ia32e-la-to-pa-values-and-!flgi
                         las-to-pas
                         las-to-pas-values-and-!flgi
                         mv-nth-2-las-to-pas-and-!flgi-not-ac-commute
                         xr-fault-wb-in-system-level-marking-mode
                         xr-fault-wb-in-system-level-mode))))

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
                :r x86)))

(defun-nx destination-bytes (k dst-addr x86)
  (mv-nth 1 (rb (create-canonical-address-list k (+ (- k) dst-addr))
                :r x86)))

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

;; Some lemmas for effects theorems:

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

;; ======================================================================
