(in-package "X86ISA")

(include-book "../../../../machine/paging")
(include-book "la-to-pa-without-tlb-lemmas")

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "centaur/bitops/equal-by-logbitp" :dir :system))

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

  ;; Taken from ihsext-basics book
  ;; For some reason, it's local in that book rather than just disabled
  (local (defthmd ash-of-logior
                  (implies (natp size)
                           (equal (ash (logior a b) size)
                                  (logior (ash a size)
                                          (ash b size))))
                  :hints(("Goal" :in-theory (enable* ihsext-inductions
                                                     ihsext-redefs)))))

  ;; So many lemmas have to be proved to get the later theorems
  ;; to be accepted. There's got to be a better way.

  (local (defthmd logior-ash-ash-logior
                  (implies (and (natp n)
                                (natp m)
                                (<= n m)
                                (integerp x)
                                (integerp y))
                           (equal (logior (ash x n)
                                          (ash y m))
                                  (ash (logior x 
                                               (ash y (- m n)))
                                       n)))
                  :hints (("Goal" :in-theory (enable ash-of-logior)))))

  (local (defthmd logior-ash-to-logapp
                  (implies (and (natp x)
                                (integerp y)
                                (natp n)
                                (>= n (integer-length x)))
                           (equal (logior x (ash y n))
                                  (logapp n x y)))
                  :hints (("Goal" :in-theory (enable logtail** bitops::logtail-induct
                                                     logior** bitops::logior-induct
                                                     logapp** bitops::logapp-induct)))))

  (local (defthmd equal-logapps-equal-components
                  (implies (and (integerp x)
                                (integerp y)
                                (integerp z)
                                (integerp w)
                                (natp n))
                           (equal (equal (logapp n x y)
                                         (logapp n z w))
                                  (and (equal (loghead n x)
                                              (loghead n z))
                                       (equal y w))))
                  :hints (("Goal" :in-theory (enable loghead** bitops::loghead-induct
                                                     logapp** bitops::logapp-induct)))))

  (local (defthmd loghead-ident-nat-integer-length
                  (implies (and (natp n)
                                (natp x)
                                (>= n (integer-length x)))
                           (equal (loghead n x)
                                  x))
                  :hints (("Goal" :in-theory (enable loghead** bitops::loghead-induct)))))

  (local (defthmd equal-logior-disjoint
                  (implies (and (natp x)
                                (natp y)
                                (integerp z)
                                (integerp w)
                                (natp n)
                                (>= n (max (integer-length x)
                                           (integer-length y))))
                           (equal (equal (logior x (ash z n))
                                         (logior y (ash w n)))
                                  (and (equal x y)
                                       (equal z w))))
                  :hints (("Goal" :in-theory (enable logior-ash-to-logapp
                                                     loghead-ident-nat-integer-length
                                                     equal-logapps-equal-components)))))


  (local (defthmd loghead-logtail-swap
                  (implies (and (natp n)
                                (natp m))
                           (equal (loghead m (logtail n x))
                                  (logtail n (loghead (+ n m) x))))
                  :hints (("Goal" :in-theory (enable loghead** bitops::loghead-induct
                                                     logtail** bitops::logtail-induct)))))

  (local (defthm equal-logapp-equal-components
                 (implies (and (natp n)
                               (integerp x)
                               (integerp y)
                               (integerp z))
                          (equal (equal (logapp n x y)
                                        z)
                                 (and (equal (loghead n x)
                                             (loghead n z))
                                      (equal y (logtail n z)))))
                 :hints (("Goal" :in-theory (enable logapp** bitops::logapp-induct
                                                    loghead** bitops::loghead-induct
                                                    logtail** bitops::logtail-induct)))))

  (local (defthm logtail-of-logext
                 (implies (and (natp n)
                               (natp m)
                               (> m n))
                          (equal (logtail n (logext m x))
                                 (logext (- m n)
                                         (logtail n x))))
                 :hints (("Goal" :in-theory (enable logtail** bitops::logtail-induct
                                                    logext** bitops::logext-induct)))))

  (local (defthm equal-logheads-means-equal-logexts
                 (implies (and (integerp n)
                               (> n 0)
                               (integerp x)
                               (integerp y))
                          (equal (equal (loghead n x)
                                        (loghead n y))
                                 (equal (logext n x)
                                        (logext n y))))
                 :hints (("Goal" :in-theory (enable loghead** bitops::loghead-induct
                                                    logext** bitops::logext-induct)))))

  (local (defthm equal-logtail-loghead-implies-equal-logtail-logext
                 (implies (and (natp n)
                               (natp m)
                               (< n m))
                          (equal (equal (logtail n (loghead m x))
                                        (logtail n (loghead m y)))
                                 (equal (logtail n (logext m x))
                                        (logtail n (logext m y)))))))

  (defthm translating-addresses-maintains-consistency
          (equal (tlb-consistent lin-addr r-w-x
                                 (mv-nth 2 (ia32e-la-to-pa lin-addr2 r-w-x2 x86)))
                 (tlb-consistent lin-addr r-w-x x86))
          :hints (("Goal" :in-theory (e/d (equal-logior-disjoint
                                            loghead-logtail-swap
                                            segment-selectorbits->rpl
                                            logior-ash-ash-logior)
                                          (acl2::simplify-logior
                                            fty::logapp-of-logext
                                            bitops::logtail-of-loghead
                                            bitops::cancel-logext-under-loghead
                                            ia32e-la-to-pa-without-tlb-fixes-address))
                   :use (:instance logtails<=12-equal-implies-same-page
                                   (x (logext 48 lin-addr))
                                   (y (logext 48 lin-addr2))
                                   (n 12)))))

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
                                              ia32e-la-to-pa)))))

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

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthm tlb-consistent-n-implies-tlb-consistent
          (implies (and (natp n)
                        (canonical-address-p lin-addr)
                        (tlb-consistent-n n lin-addr-base r-w-x x86)
                        (canonical-address-p lin-addr-base)
                        (>= lin-addr lin-addr-base)
                        (< lin-addr (+ lin-addr-base n)))
                   (tlb-consistent lin-addr r-w-x x86))))
