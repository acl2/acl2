(in-package "X86ISA")

(include-book "../../../../machine/paging")
(include-book "la-to-pa-without-tlb-lemmas")
(include-book "common-paging-lemmas")
(include-book "paging-equiv")

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))

(define tlb-consistent ((lin-addr canonical-address-p)
                        (r-w-x    :type (member  :r :w :x))
                        x86)
  :non-executable t
  :guard (not (app-view x86))
  :returns (tlb-consistent? booleanp)
  (b* ((lin-addr (mbe :logic (logext 48 (loghead 48 lin-addr))
                      :exec lin-addr))
       ((mv flg phys-addr &) (ia32e-la-to-pa lin-addr r-w-x x86))
       ((mv flg2 phys-addr2 &) (ia32e-la-to-pa-without-tlb lin-addr r-w-x x86)))
      (and (equal flg flg2)
           (equal phys-addr
                  phys-addr2)))
  ///
  (local (in-theory (e/d (ia32e-la-to-pa) (unsigned-byte-p signed-byte-p))))

  (defthm empty-tlb-is-consistent
          (implies (atom (xr :tlb nil x86))
                   (tlb-consistent lin-addr r-w-x x86)))

  (defthm translating-addresses-maintains-consistency
          (equal (tlb-consistent lin-addr r-w-x
                                 (mv-nth 2 (ia32e-la-to-pa lin-addr2 r-w-x2 x86)))
                 (tlb-consistent lin-addr r-w-x x86))
          :hints (("Goal"  :in-theory (e/d ()
                                           (ia32e-la-to-pa-without-tlb-fixes-address))
                   :use ((:instance logext-n-same-page-if-loghead-logtail-equal
                                    (n 48) (k 36) (a lin-addr) (b lin-addr2))))))

  (defthm same-page-lin-addrs-have-same-tlb-consistent
          (implies (same-page lin-addr lin-addr2)
                   (equal (tlb-consistent lin-addr r-w-x x86)
                          (tlb-consistent lin-addr2 r-w-x x86)))
          :rule-classes :congruence
          :hints (("Goal" :in-theory (disable fty::logapp-of-logext))))

  (defthm tlb-consistent-implies-we-can-lookup-without-tlb
          (implies (tlb-consistent lin-addr r-w-x x86)
                   (b* (((mv flg phys-addr &) (ia32e-la-to-pa lin-addr r-w-x x86))
                        ((mv flg2 phys-addr2 &) (ia32e-la-to-pa-without-tlb lin-addr r-w-x x86)))
                       (and (equal flg flg2)
                            (equal phys-addr
                                   phys-addr2)))))

  (defthm tlb-consistent-lin-addr-int-equiv-cong
          (implies (int-equiv la1 la2)
                   (equal (tlb-consistent la1 r-w-x x86)
                          (tlb-consistent la2 r-w-x x86)))
          :rule-classes :congruence
          :hints (("Goal" :in-theory (disable int-equiv
                                              bitops::cancel-loghead-under-logext
                                              ia32e-la-to-pa))))

  (defthm writing-non-page-table-memory-maintains-tlb-consistency
          (implies (disjoint-p (list index)
                               (xlation-governing-entries-paddrs (logext 48 lin-addr) x86))
                   (equal (tlb-consistent lin-addr r-w-x (xw :mem index val x86))
                          (tlb-consistent lin-addr r-w-x x86)))
          :hints (("Goal" :in-theory (disable ia32e-la-to-pa-without-tlb-fixes-address))))

  (in-theory (disable ia32e-la-to-pa))

  (defthm xw-maintains-tlb-consistent
          (implies (and (not (equal fld :mem))
                        (not (equal fld :rflags))
                        (not (equal fld :fault))
                        (not (equal fld :ctr))
                        (not (equal fld :msr))
                        (not (equal fld :seg-visible))
                        (not (equal fld :app-view))
                        (not (equal fld :tlb))
                        (not (equal fld :implicit-supervisor-access)))
                   (equal (tlb-consistent lin-addr r-w-x
                                          (xw fld idx val x86))
                          (tlb-consistent lin-addr r-w-x x86))))

  (defthm xw-rflags-not-ac-maintains-tlb-consistent
          (implies (equal (rflagsBits->ac value)
                          (rflagsBits->ac (rflags (double-rewrite x86))))
                   (equal (tlb-consistent lin-addr r-w-x (xw :rflags nil value x86))
                          (tlb-consistent lin-addr r-w-x x86))))

  (defthm ia32e-la-to-pa-without-tlb-maintains-tlb-consistency
          (implies (tlb-consistent lin-addr r-w-x x86)
                   (tlb-consistent lin-addr r-w-x
                                   (mv-nth 2 (ia32e-la-to-pa-without-tlb in-addr2 r-w-x2 x86)))))

  (local (in-theory (disable tlb-consistent)))

  (defthm las-to-pas-maintains-tlb-consistency
          (implies (tlb-consistent lin-addr r-w-x x86)
                   (tlb-consistent lin-addr r-w-x
                                   (mv-nth 2 (las-to-pas n lin-addr2 r-w-x2 x86))))
          :hints (("Goal" :in-theory (enable las-to-pas))))

  (defthm write-to-physical-memory-maintains-tlb-consistency
          (implies (and (disjoint-p
                          p-addrs
                          (xlation-governing-entries-paddrs (logext 48 lin-addr) (double-rewrite x86)))
                        (tlb-consistent lin-addr r-w-x x86))
                   (tlb-consistent lin-addr r-w-x
                                   (write-to-physical-memory p-addrs value x86)))
          :hints (("Goal" :in-theory (enable disjoint-p write-to-physical-memory))))

  (defthm wb-maintains-tlb-consistency
          (implies (and (not (app-view x86))
                        (disjoint-p
                          (mv-nth 1 (las-to-pas n-w write-addr :w (double-rewrite x86)))
                          (xlation-governing-entries-paddrs (logext 48 lin-addr) (double-rewrite x86)))
                        (tlb-consistent lin-addr r-w-x x86))
                   (tlb-consistent lin-addr r-w-x
                                   (mv-nth 1 (wb n-w write-addr w value x86))))
          :hints (("Goal" :in-theory (enable wb)))))

(define tlb-consistent-n ((n natp)
                          (lin-addr integerp)
                          (r-w-x    :type (member  :r :w :x))
                          x86)
  :guard (not (app-view x86))
  (if (or (zp n)
          (not (canonical-address-p lin-addr)))
    t
    (and (tlb-consistent lin-addr r-w-x x86)
         (tlb-consistent-n (1- n) (1+ lin-addr) r-w-x x86)))
  ///

  (defthm empty-tlb-is-consistent-n
          (implies (atom (xr :tlb nil x86))
                   (tlb-consistent-n n lin-addr r-w-x x86)))

  (defthm translating-addresses-maintains-consistency-n
          (equal (tlb-consistent-n n lin-addr r-w-x
                                   (mv-nth 2 (ia32e-la-to-pa lin-addr2 r-w-x2 x86)))
                 (tlb-consistent-n n lin-addr r-w-x x86)))

  (defthm writing-non-page-table-memory-maintains-tlb-consistency-n
          (implies (not (member-p index
                                  (all-xlation-governing-entries-paddrs n lin-addr x86)))
                   (equal (tlb-consistent-n n lin-addr r-w-x (xw :mem index val x86))
                          (tlb-consistent-n n lin-addr r-w-x x86)))
          :hints (("Goal" :in-theory (e/d (disjoint-p) (ia32e-la-to-pa)))))

  ;; (skip-proofs (defthm tlb-consistent-n-non-canonical
  ;;                      (implies (not (tlb-consistent-n n lin-addr r-w-x x86))
  ;;                               (canonical-address-p lin-addr))))

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthm tlb-consistent-n-implies-tlb-consistent
          (implies (and (tlb-consistent-n n lin-addr-base r-w-x x86)
                        (natp n)
                        (case-split (canonical-address-p lin-addr))
                        (case-split (canonical-address-p lin-addr-base))
                        (>= lin-addr lin-addr-base)
                        (< lin-addr (+ lin-addr-base n)))
                   (tlb-consistent lin-addr r-w-x x86))
          :hints (("Goal" ;; :cases ()
                   )))

  (defthm tlb-consistent-n-implies-tlb-consistent-subset
          (implies (and (tlb-consistent-n n lin-addr-base r-w-x x86)
                        (case-split (canonical-address-p lin-addr-base))
                        (case-split (canonical-address-p lin-addr))
                        (natp n)
                        (>= lin-addr lin-addr-base)
                        (< lin-addr (+ lin-addr-base n))
                        (natp k)
                        (<= (+ lin-addr k) (+ lin-addr-base n)))
                   (tlb-consistent-n k lin-addr r-w-x x86)))

  (defthm tlb-consistent-n-1-is-tlb-consistent
          (implies (canonical-address-p lin-addr)
                   (equal (tlb-consistent-n 1 lin-addr r-w-x x86)
                          (tlb-consistent lin-addr r-w-x x86)))
          :hints (("Goal" :expand (tlb-consistent-n 1 lin-addr r-w-x x86))))

  (defthm writing-non-page-table-memory-maintains-tlb-consistent-n
          (implies (disjoint-p (list index)
                               (all-xlation-governing-entries-paddrs n (logext 48 lin-addr) x86))
                   (equal (tlb-consistent-n n lin-addr r-w-x (xw :mem index val x86))
                          (tlb-consistent-n n lin-addr r-w-x x86)))
          :hints (("Goal" :in-theory (disable ia32e-la-to-pa-without-tlb-fixes-address))))

  (local (in-theory (disable ia32e-la-to-pa)))

  (defthm las-to-pas-maintains-tlb-consistent-n
          (implies (tlb-consistent-n n lin-addr r-w-x x86)
                   (tlb-consistent-n n lin-addr r-w-x
                                   (mv-nth 2 (las-to-pas n2 lin-addr2 r-w-x2 x86))))
          :hints (("Goal" :in-theory (enable tlb-consistent-n)
                          :induct (tlb-consistent-n n lin-addr r-w-x x86))))

  (defthm write-to-physical-memory-maintains-tlb-consistent-n
          (implies (and (disjoint-p
                          p-addrs
                          (all-xlation-governing-entries-paddrs n (logext 48 lin-addr) (double-rewrite x86)))
                        (tlb-consistent-n n lin-addr r-w-x x86))
                   (tlb-consistent-n n lin-addr r-w-x
                                   (write-to-physical-memory p-addrs value x86)))
          :hints (("Goal" :in-theory (enable disjoint-p write-to-physical-memory))))

  (defthm wm-low-64-maintains-tlb-consistent-n
          (implies (and (disjoint-p
                          (addr-range 8 addr)
                          (all-xlation-governing-entries-paddrs n (logext 48 lin-addr) (double-rewrite x86)))
                        (not (app-view x86))
                        (tlb-consistent-n n lin-addr r-w-x x86))
                   (tlb-consistent-n n lin-addr r-w-x
                                   (wm-low-64 addr value x86)))
          :hints (("Goal" :in-theory (enable disjoint-p rewrite-wm-low-64-to-write-to-physical-memory))))

  (defthm wb-maintains-tlb-consistent-n
          (implies (and (not (app-view x86))
                        (disjoint-p
                          (mv-nth 1 (las-to-pas n-w write-addr :w (double-rewrite x86)))
                          (all-xlation-governing-entries-paddrs n (logext 48 lin-addr) (double-rewrite x86)))
                        (tlb-consistent-n n lin-addr r-w-x x86))
                   (tlb-consistent-n n lin-addr r-w-x
                                   (mv-nth 1 (wb n-w write-addr w value x86))))
          :hints (("Goal" :in-theory (enable wb))))

  (defthm ia32e-la-to-pa-without-tlb-maintains-tlb-consistent-n
          (implies (tlb-consistent-n n lin-addr r-w-x x86)
                   (tlb-consistent-n n lin-addr r-w-x
                                     (mv-nth 2 (ia32e-la-to-pa-without-tlb in-addr2 r-w-x2 x86)))))

  (defthm xw-maintains-tlb-consistent-n
          (implies (and (not (equal fld :mem))
                        (not (equal fld :rflags))
                        (not (equal fld :fault))
                        (not (equal fld :ctr))
                        (not (equal fld :msr))
                        (not (equal fld :seg-visible))
                        (not (equal fld :app-view))
                        (not (equal fld :tlb))
                        (not (equal fld :implicit-supervisor-access)))
                   (equal (tlb-consistent-n n lin-addr r-w-x
                                            (xw fld idx val x86))
                          (tlb-consistent-n n lin-addr r-w-x x86))))

  (defthm xw-rflags-not-ac-maintains-tlb-consistent-n
          (implies (equal (rflagsBits->ac value)
                          (rflagsBits->ac (rflags (double-rewrite x86))))
                   (equal (tlb-consistent-n n lin-addr r-w-x (xw :rflags nil value x86))
                          (tlb-consistent-n n lin-addr r-w-x x86)))))
