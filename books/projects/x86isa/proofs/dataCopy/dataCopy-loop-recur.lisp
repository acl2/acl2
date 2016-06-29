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
                                 :r X86)))
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
                                        :r X86)))))
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
                                   (r-w-x :r)
                                   (addr (+ (- k) (xr :rgf *rsi* x86)))
                                   (x86 (x86-run (loop-clk-recur) x86))))
           :in-theory (e/d* ()
                            (loop-clk-recur
                             effects-copyData-loop-recur-destination-address-projection-copied
                             effects-copyData-loop-recur-destination-address-projection-original
                             rb-rb-split-reads
                             take-and-rb
                             (loop-clk-recur)
                             force (force))))
          ("Subgoal 7" :use ((:instance rb-rb-split-reads
                                        (k k)
                                        (j 4)
                                        (r-w-x :r)
                                        (addr (+ (- k) (xr :rgf *rdi* x86)))
                                        (x86 x86)))
           :in-theory (e/d* ()
                            (loop-clk-recur
                             effects-copyData-loop-recur-destination-address-projection-copied
                             effects-copyData-loop-recur-destination-address-projection-original
                             rb-rb-split-reads
                             take-and-rb
                             (loop-clk-recur)
                             force (force))))
          ("Subgoal 5" :use ((:instance rb-rb-split-reads
                                        (k k)
                                        (j 4)
                                        (r-w-x :r)
                                        (addr (+ (- k) (xr :rgf *rdi* x86)))
                                        (x86 x86)))
           :in-theory (e/d* ()
                            (loop-clk-recur
                             effects-copyData-loop-recur-destination-address-projection-copied
                             effects-copyData-loop-recur-destination-address-projection-original
                             rb-rb-split-reads
                             take-and-rb
                             (loop-clk-recur)
                             force (force))))
          ("Subgoal 2" :use ((:instance rb-rb-split-reads
                                        (k k)
                                        (j 4)
                                        (r-w-x :r)
                                        (addr (+ (- k) (xr :rgf *rdi* x86)))
                                        (x86 x86)))
           :in-theory (e/d* ()
                            (loop-clk-recur
                             effects-copyData-loop-recur-destination-address-projection-copied
                             effects-copyData-loop-recur-destination-address-projection-original
                             rb-rb-split-reads
                             take-and-rb
                             (loop-clk-recur)
                             force (force))))
          ("Subgoal 1" :use ((:instance rb-rb-split-reads
                                        (k k)
                                        (j 4)
                                        (r-w-x :r)
                                        (addr (+ (- k) (xr :rgf *rdi* x86)))
                                        (x86 x86)))
           :in-theory (e/d* ()
                            (loop-clk-recur
                             effects-copyData-loop-recur-destination-address-projection-copied
                             effects-copyData-loop-recur-destination-address-projection-original
                             rb-rb-split-reads
                             take-and-rb
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
                                   (r-w-x :r)
                                   (addr (+ (- k) (xr :rgf *rdi* x86)))
                                   (x86 (x86-run (loop-clk-recur) x86))))
           :in-theory (e/d* ()
                            (loop-clk-recur
                             effects-copyData-loop-recur-source-address-projection-copied
                             effects-copyData-loop-recur-source-address-projection-original
                             rb-rb-split-reads
                             take-and-rb
                             (loop-clk-recur)
                             force (force))))
          ("Subgoal 1" :use ((:instance rb-rb-split-reads
                                        (k k)
                                        (j 4)
                                        (r-w-x :r)
                                        (addr (+ (- k) (xr :rgf *rdi* x86)))
                                        (x86 x86)))
           :in-theory (e/d* ()
                            (loop-clk-recur
                             effects-copyData-loop-recur-source-address-projection-copied
                             effects-copyData-loop-recur-source-address-projection-original
                             rb-rb-split-reads
                             take-and-rb
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

;; ======================================================================
