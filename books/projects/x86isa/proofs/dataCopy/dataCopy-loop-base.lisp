;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")

(include-book "programmer-level-mode/programmer-level-memory-utils" :dir :proof-utils :ttags :all)
(include-book "dataCopy-init" :ttags :all)
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
                         :R X86)))
            (XW
             :RGF *RSI*
             (LOGEXT 64
                     (+ 4 (LOGHEAD 64 (XR :RGF *RSI* X86))))
             (XW
              :RGF *RDI*
              (LOGEXT 64
                      (+ 4 (LOGHEAD 64 (XR :RGF *RDI* X86))))
              (XW
               :RIP 0 (+ 18 (XR :RIP 0 X86))
               (MV-NTH
                1
                (WB
                 (CREATE-ADDR-BYTES-ALIST
                  (CREATE-CANONICAL-ADDRESS-LIST 4 (XR :RGF *RSI* X86))
                  (MV-NTH 1
                          (RB (CREATE-CANONICAL-ADDRESS-LIST 4 (XR :RGF *RDI* X86))
                              :R X86)))
                 (!FLGI
                  *CF* 1
                  (!FLGI *PF* 1
                         (!FLGI *AF* 1
                                (!FLGI *ZF* 1
                                       (!FLGI *SF* 0 (!FLGI *OF* 0 X86)))))))))))))))
  :hints (("Goal"
           :do-not '(preprocess)
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
                             mv-nth-1-wb-and-!flgi-commute
                             create-canonical-address-list
                             default-+-2
                             get-prefixes-opener-lemma-group-4-prefix
                             get-prefixes-opener-lemma-group-3-prefix
                             get-prefixes-opener-lemma-group-2-prefix
                             get-prefixes-opener-lemma-group-1-prefix)))))

(defthm effects-copyData-loop-base-destination-address-projection-original
  ;; dst[(+ -k dst-addr) to dst-addr] in (x86-run (loop-clk-base) x86) =
  ;; dst[(+ -k src-addr) to src-addr] in x86
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (<= m 4))
           (equal (destination-bytes k dst-addr (x86-run (loop-clk-base) x86))
                  (source-bytes k dst-addr x86)))
  :hints (("Goal" :use ((:instance effects-copydata-loop-base))
           :in-theory (e/d* ()
                            (mv-nth-1-wb-and-!flgi-commute
                             loop-clk-base
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
  (implies
   (and (loop-preconditions k m addr src-addr dst-addr x86)
        (<= m 4))
   (equal (destination-bytes (+ 4 k) (+ 4 dst-addr) (x86-run (loop-clk-base) x86))
          (source-bytes (+ 4 k) (+ 4 src-addr) x86)))
  :hints (("Goal" :use ((:instance effects-copydata-loop-base)
                        (:instance effects-copyData-loop-base-destination-address-projection-copied)
                        (:instance effects-copyData-loop-base-destination-address-projection-original)
                        (:instance rb-rb-split-reads
                                   (k k)
                                   (j 4)
                                   (r-w-x :r)
                                   (addr (+ (- k) (xr :rgf *rsi* x86)))
                                   (x86 (x86-run (loop-clk-base) x86)))
                        (:instance rb-rb-split-reads
                                   (k k)
                                   (j 4)
                                   (r-w-x :r)
                                   (addr (+ (- k) (xr :rgf *rdi* x86)))
                                   (x86 (x86-run (loop-clk-base) x86))))
           :in-theory (e/d* ()
                            (loop-clk-base
                             effects-copyData-loop-base-destination-address-projection-copied
                             effects-copyData-loop-base-destination-address-projection-original
                             rb-rb-split-reads
                             take-and-rb
                             (loop-clk-base)
                             (:t xw)
                             (:t consp-append)
                             create-canonical-address-list
                             canonical-address-p-limits-thm-0
                             disjoint-p-two-create-canonical-address-lists-thm-1
                             default-+-1
                             default-+-2
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
                                   (r-w-x :r)
                                   (addr (+ (- k) (xr :rgf *rdi* x86)))
                                   (x86 (x86-run (loop-clk-base) x86)))
                        (:instance rb-rb-split-reads
                                   (k k)
                                   (j 4)
                                   (r-w-x :r)
                                   (addr (+ (- k) (xr :rgf *rdi* x86)))
                                   (x86 (x86-run (loop-clk-base) x86))))
           :in-theory (e/d* ()
                            (loop-clk-base
                             effects-copyData-loop-base-source-address-projection-copied
                             effects-copyData-loop-base-source-address-projection-original
                             rb-rb-split-reads
                             take-and-rb
                             (loop-clk-base)
                             (:t xw)
                             (:t consp-append)
                             create-canonical-address-list
                             canonical-address-p-limits-thm-0
                             disjoint-p-two-create-canonical-address-lists-thm-1
                             default-+-1
                             default-+-2
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
                          (rb
                           (create-canonical-address-list 8 (+ 8 (xr :rgf *rsp* x86)))
                           :r (x86-run (loop-clk-base) x86)))
                  (mv-nth 1
                          (rb
                           (create-canonical-address-list 8 (+ 8 (xr :rgf *rsp* x86)))
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

;; ======================================================================
