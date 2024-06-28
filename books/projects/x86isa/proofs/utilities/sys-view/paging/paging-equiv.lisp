(in-package "X86ISA")

(include-book "common-paging-lemmas" :ttags :all)

;; First, we show that ia32e-la-to-pa is invariant under ia32e-la-to-pa
;; We use make-event tricks to prove theorems for all levels
;; of the paging hierarchy

(encapsulate
  ()

  (make-event
    `(progn
       ,@(loop$ for level in *paging-levels*
                collect
                (b* ((la-to-pa-fn (acl2::packn (list 'ia32e-la-to-pa- level))))
                    `(progn
                       (defthm
                         ,(acl2::packn (list la-to-pa-fn '-invariant-under- la-to-pa-fn))
                         (and
                           (equal
                             (mv-nth 0 (,la-to-pa-fn
                                         lin-addr base-addr
                                         ,@(if (equal level 'pml4-table) nil '(us rw xd))
                                         wp smep smap ac nxe r-w-x cpl
                                         (mv-nth 2 (,la-to-pa-fn
                                                     lin-addr2 base-addr2
                                                     ,@(if (equal level 'pml4-table) nil '(us2 rw2 xd2))
                                                     wp2 smep2 smap2 ac2 nxe2 r-w-x2 cpl2
                                                     x86))))
                             (mv-nth 0 (,la-to-pa-fn
                                         lin-addr base-addr
                                         ,@(if (equal level 'pml4-table) nil '(us rw xd))
                                         wp smep smap ac nxe r-w-x cpl x86)))
                           (equal
                             (mv-nth 1 (,la-to-pa-fn
                                         lin-addr base-addr
                                         ,@(if (equal level 'pml4-table) nil '(us rw xd))
                                         wp smep smap ac nxe r-w-x cpl
                                         (mv-nth 2 (,la-to-pa-fn
                                                     lin-addr2 base-addr2
                                                     ,@(if (equal level 'pml4-table) nil '(us2 rw2 xd2))
                                                     wp2 smep2 smap2 ac2 nxe2 r-w-x2 cpl2
                                                     x86))))
                             (mv-nth 1 (,la-to-pa-fn
                                         lin-addr base-addr
                                         ,@(if (equal level 'pml4-table) nil '(us rw xd))
                                         wp smep smap ac nxe r-w-x cpl x86))))
                         :hints (("Goal" :in-theory (e/d (,la-to-pa-fn
                                                           paging-entry-no-page-fault-p-invariant-under-paging-entry-no-page-fault-p
                                                           page-user-supervisor
                                                           page-execute-disable)
                                                         ())
                                  :use (:instance
                                         equal-loghead-n-k-integers-are-either-equal-or-disjoint-p-addr-range-m<=2^n
                                         (n 3) (m 8) (k 0)
                                         (x (,(acl2::packn (list level '-entry-addr))
                                              (logext 48 lin-addr2)
                                              (logand 18446744073709547520
                                                      (loghead 52 base-addr2))))
                                         (y (,(acl2::packn (list level '-entry-addr))
                                              (logext 48 lin-addr)
                                              (logand 18446744073709547520
                                                      (loghead 52 base-addr))))))))

                       ;; These macros are just to let me use the forms they expand to in the theorems
                       ;; proven in the loop below
                       (defmacro loghead-8-logtail-13 (x)
                         `(loghead 8 (logtail 13 ,x)))

                       (defmacro loghead-17-logtail-13 (x)
                         `(loghead 17 (logtail 13 ,x)))

                       ,@(loop$ for accessor in '(ia32e-page-tablesbits->xd ia32e-page-tablesbits->u/s page-read-write page-present page-size
                                                                            page-user-supervisor page-execute-disable
                                                                            loghead-8-logtail-13 loghead-17-logtail-13
                                                                            ia32e-pde-2mb-pagebits->page ia32e-pdpte-1gb-pagebits->page)
                                collect
                                `(defthm ,(acl2::packn (list accessor '-aligned-read-invariant-under- la-to-pa-fn))
                                         (implies (and (integerp addr)
                                                       (equal (loghead 3 addr) 0))
                                                  (equal (,accessor (rm-low-64 addr
                                                                               (mv-nth 2 (,la-to-pa-fn
                                                                                           lin-addr2 base-addr2
                                                                                           ,@(if (equal level 'pml4-table) nil '(us2 rw2 xd2))
                                                                                           wp2 smep2 smap2 ac2 nxe2 r-w-x2 cpl2
                                                                                           x86))))
                                                         (,accessor (rm-low-64 addr x86))))
                                         :hints (("Goal" :in-theory (enable ,la-to-pa-fn)
                                                  :use (:instance
                                                         equal-loghead-n-k-integers-are-either-equal-or-disjoint-p-addr-range-m<=2^n
                                                         (n 3) (m 8) (k 0)
                                                         (x addr)
                                                         (y (,(acl2::packn (list level '-entry-addr))
                                                              (logext 48 lin-addr2)
                                                              (logand 18446744073709547520
                                                                      (loghead 52 base-addr2)))))))))

                       (defthm ,(acl2::packn (list 'paging-entry-no-page-fault-p-invariant-under- la-to-pa-fn))
                               (and (equal (mv-nth 0 (paging-entry-no-page-fault-p
                                                       structure-type lin-addr entry
                                                       u/s-acc r/w-acc x/d-acc
                                                       wp smep smap ac nxe r-w-x cpl 
                                                       (mv-nth 2 (,la-to-pa-fn
                                                                   lin-addr2 base-addr2
                                                                   ,@(if (equal level 'pml4-table) nil '(us2 rw2 xd2))
                                                                   wp2 smep2 smap2 ac2 nxe2 r-w-x2 cpl2
                                                                   x86))))
                                           (mv-nth 0 (paging-entry-no-page-fault-p
                                                       structure-type lin-addr entry
                                                       u/s-acc r/w-acc x/d-acc
                                                       wp smep smap ac nxe r-w-x cpl x86)))
                                    (equal (mv-nth 1 (paging-entry-no-page-fault-p
                                                       structure-type lin-addr entry
                                                       u/s-acc r/w-acc x/d-acc
                                                       wp smep smap ac nxe r-w-x cpl 
                                                       (mv-nth 2 (,la-to-pa-fn
                                                                   lin-addr2 base-addr2
                                                                   ,@(if (equal level 'pml4-table) nil '(us2 rw2 xd2))
                                                                   wp2 smep2 smap2 ac2 nxe2 r-w-x2 cpl2
                                                                   x86))))
                                           (mv-nth 1 (paging-entry-no-page-fault-p
                                                       structure-type lin-addr entry
                                                       u/s-acc r/w-acc x/d-acc
                                                       wp smep smap ac nxe r-w-x cpl x86))))
                               :hints (("Goal" :in-theory (enable paging-entry-no-page-fault-p page-fault-exception))))

                       (defthm ,(acl2::packn (list 'paging-entry-no-page-fault-p-invariant-under-reading-entry-after- la-to-pa-fn))
                               (implies (and (integerp entry-addr)
                                             (equal (loghead 3 entry-addr) 0))
                                        (and (equal (mv-nth 0 (paging-entry-no-page-fault-p
                                                                structure-type lin-addr
                                                                (rm-low-64 entry-addr
                                                                           (mv-nth 2 (,la-to-pa-fn
                                                                                       lin-addr2 base-addr2
                                                                                       ,@(if (equal level 'pml4-table) nil '(us2 rw2 xd2))
                                                                                       wp2 smep2 smap2 ac2 nxe2 r-w-x2 cpl2
                                                                                       x86)))
                                                                u/s-acc r/w-acc x/d-acc
                                                                wp smep smap ac nxe r-w-x cpl x86))
                                                    (mv-nth 0 (paging-entry-no-page-fault-p
                                                                structure-type lin-addr (rm-low-64 entry-addr x86)
                                                                u/s-acc r/w-acc x/d-acc
                                                                wp smep smap ac nxe r-w-x cpl x86)))
                                             (equal (mv-nth 1 (paging-entry-no-page-fault-p
                                                                structure-type lin-addr
                                                                (rm-low-64 entry-addr
                                                                           (mv-nth 2 (,la-to-pa-fn
                                                                                       lin-addr2 base-addr2
                                                                                       ,@(if (equal level 'pml4-table) nil '(us2 rw2 xd2))
                                                                                       wp2 smep2 smap2 ac2 nxe2 r-w-x2 cpl2
                                                                                       x86)))
                                                                u/s-acc r/w-acc x/d-acc
                                                                wp smep smap ac nxe r-w-x cpl x86))
                                                    (mv-nth 1 (paging-entry-no-page-fault-p
                                                                structure-type lin-addr (rm-low-64 entry-addr x86)
                                                                u/s-acc r/w-acc x/d-acc
                                                                wp smep smap ac nxe r-w-x cpl x86)))))
                               :hints (("Goal" :in-theory (e/d (paging-entry-no-page-fault-p)
                                                               (,(acl2::packn (list level '-entry-addr)))))))

                       (defmacro set-dirty-and-accessed-bits (x)
                         `(set-dirty-bit (set-accessed-bit ,x)))

                       ,@(loop$ for setter in '(set-accessed-bit set-dirty-bit set-dirty-and-accessed-bits)
                                collect
                                `(defthm
                                   ,(acl2::packn (list la-to-pa-fn '-invariant-under-aligned-write- setter))
                                   (implies (and (integerp entry-addr)
                                                 (equal (loghead 3 entry-addr) 0))
                                            (and (equal (mv-nth 0 (,la-to-pa-fn
                                                                    lin-addr base-addr
                                                                    ,@(if (equal level 'pml4-table) nil '(us rw xd))
                                                                    wp smep smap ac nxe r-w-x cpl
                                                                    (wm-low-64 entry-addr
                                                                               (,setter (rm-low-64 entry-addr x86))
                                                                               x86)))
                                                        (mv-nth 0 (,la-to-pa-fn
                                                                    lin-addr base-addr
                                                                    ,@(if (equal level 'pml4-table) nil '(us rw xd))
                                                                    wp smep smap ac nxe r-w-x cpl
                                                                    x86)))
                                                 (equal (mv-nth 1 (,la-to-pa-fn
                                                                    lin-addr base-addr
                                                                    ,@(if (equal level 'pml4-table) nil '(us rw xd))
                                                                    wp smep smap ac nxe r-w-x cpl
                                                                    (wm-low-64 entry-addr
                                                                               (,setter (rm-low-64 entry-addr x86))
                                                                               x86)))
                                                        (mv-nth 1 (,la-to-pa-fn
                                                                    lin-addr base-addr
                                                                    ,@(if (equal level 'pml4-table) nil '(us rw xd))
                                                                    wp smep smap ac nxe r-w-x cpl
                                                                    x86)))))
                                   :hints (("Goal" :in-theory (e/d (,la-to-pa-fn) ())
                                            :use (:instance
                                                   equal-loghead-n-k-integers-are-either-equal-or-disjoint-p-addr-range-m<=2^n
                                                   (n 3) (m 8) (k 0)
                                                   (x entry-addr)
                                                   (y (,(acl2::packn (list level '-entry-addr))
                                                        (logext 48 lin-addr)
                                                        (logand 18446744073709547520
                                                                (loghead 52 base-addr)))))))))

                       (defthm ,(acl2::packn (list la-to-pa-fn '-invariant-under-paging-entry-no-page-fault-p))
                               (and (equal (mv-nth 0 (,la-to-pa-fn
                                                       lin-addr base-addr
                                                       ,@(if (equal level 'pml4-table) nil '(us rw xd))
                                                       wp smep smap ac nxe r-w-x cpl
                                                       (mv-nth 2 (paging-entry-no-page-fault-p
                                                                   structure-type2 lin-addr2 entry2
                                                                   u/s-acc2 r/w-acc2 x/d-acc2
                                                                   wp2 smep2 smap2 ac2 nxe2 r-w-x2 cpl2 x86))))
                                           (mv-nth 0 (,la-to-pa-fn
                                                       lin-addr base-addr
                                                       ,@(if (equal level 'pml4-table) nil '(us rw xd))
                                                       wp smep smap ac nxe r-w-x cpl
                                                       x86)))
                                    (equal (mv-nth 1 (,la-to-pa-fn
                                                       lin-addr base-addr
                                                       ,@(if (equal level 'pml4-table) nil '(us rw xd))
                                                       wp smep smap ac nxe r-w-x cpl
                                                       (mv-nth 2 (paging-entry-no-page-fault-p
                                                                   structure-type2 lin-addr2 entry2
                                                                   u/s-acc2 r/w-acc2 x/d-acc2
                                                                   wp2 smep2 smap2 ac2 nxe2 r-w-x2 cpl2 x86))))
                                           (mv-nth 1 (,la-to-pa-fn
                                                       lin-addr base-addr
                                                       ,@(if (equal level 'pml4-table) nil '(us rw xd))
                                                       wp smep smap ac nxe r-w-x cpl
                                                       x86))))
                               :hints (("Goal" :in-theory (e/d (,la-to-pa-fn paging-entry-no-page-fault-p page-fault-exception)
                                                               (paging-entry-no-page-fault-p-did-fault?))))))))))

  (defthm ia32e-la-to-pa-without-tlb-invariant-under-ia32e-la-to-pa-without-tlb
          (and (equal (mv-nth 0 (ia32e-la-to-pa-without-tlb lin-addr r-w-x
                                                            (mv-nth 2 (ia32e-la-to-pa-without-tlb lin-addr2 r-w-x-2 x86))))
                      (mv-nth 0 (ia32e-la-to-pa-without-tlb lin-addr r-w-x x86)))
               (equal (mv-nth 1 (ia32e-la-to-pa-without-tlb lin-addr r-w-x
                                                            (mv-nth 2 (ia32e-la-to-pa-without-tlb lin-addr2 r-w-x-2 x86))))
                      (mv-nth 1 (ia32e-la-to-pa-without-tlb lin-addr r-w-x x86))))
          :hints (("Goal" :in-theory (enable ia32e-la-to-pa-without-tlb))))

  (defthm ia32e-la-to-pa-invariant-under-ia32e-la-to-pa-without-tlb
          (and (equal (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x
                                                            (mv-nth 2 (ia32e-la-to-pa-without-tlb lin-addr2 r-w-x-2 x86))))
                      (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x x86)))
               (equal (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x
                                                            (mv-nth 2 (ia32e-la-to-pa-without-tlb lin-addr2 r-w-x-2 x86))))
                      (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x x86))))
          :hints (("Goal" :in-theory (enable ia32e-la-to-pa))))

  (local (defthm logtail-logext-logext-logtail
                 (implies (and (natp n)
                               (natp k)
                               (>= n 1)
                               (> k n))
                          (equal (logtail n (logext k x))
                                 (logext (- k n) (logtail n x))))
                 :hints (("Goal" :in-theory (enable logtail** bitops::logtail-induct
                                                    logext** bitops::logext-induct)))))

  (local (defthmd equal-logext-equal-loghead
                  (implies (and (natp n)
                                (>= n 1))
                           (equal (equal (loghead n x)
                                         (loghead n (double-rewrite y)))
                                  (equal (logext n x)
                                         (logext n y))))
                  ;; :hints (("Goal" :in-theory (enab)))
                  :hints (("Goal" :in-theory (enable loghead** bitops::loghead-induct
                                                     logext** bitops::logext-induct)))))

  (defthmd logext-n-same-page-if-loghead-logtail-equal
           (implies (and (natp n)
                         (>= n 12)
                         (equal (loghead k (logtail 12 a))
                                (loghead k (logtail 12 b)))
                         (equal k (- n 12))
                         (>= k 1))
                    (same-page (logext n a)
                               (logext n b)))
           :hints (("Goal" :in-theory (enable same-page)
                    :use (:instance equal-logext-equal-loghead
                                    (x (logtail 12 a)) (y (logtail 12 b)) (n (- n 12))))))

  (defthm equal-logapp-int-head-tail
          (implies (and (natp n)
                        (integerp z))
                   (equal (equal (logapp n x y)
                                 z)
                          (and (equal (loghead n x)
                                      (loghead n z))
                               (equal (logtail n z)
                                      (ifix y)))))
          :hints (("Goal" :in-theory (enable logapp** bitops::logapp-induct
                                             loghead** bitops::loghead-induct
                                             logtail** bitops::logtail-induct))))

  (defthm ia32e-la-to-pa-invariant-under-ia32e-la-to-pa
          (and (equal (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x
                                                (mv-nth 2 (ia32e-la-to-pa lin-addr2 r-w-x-2 x86))))
                      (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x x86)))
               (equal (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x
                                                (mv-nth 2 (ia32e-la-to-pa lin-addr2 r-w-x-2 x86))))
                      (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x x86))))
          :hints (("Goal" :in-theory (e/d (ia32e-la-to-pa)
                                          (ia32e-la-to-pa-without-tlb-fixes-address
                                            acl2::ifix-under-int-equiv))
                   :cases ((equal (tlb-key (logtail 12 lin-addr) r-w-x (cpl x86))
                                  (tlb-key (logtail 12 lin-addr2) r-w-x (cpl x86))))
                   :use ((:instance logext-n-same-page-if-loghead-logtail-equal
                                    (n 48) (k 36) (a lin-addr) (b lin-addr2)))))))

(define paging-equiv-int ((lin-addr :type (signed-byte   #.*max-linear-address-size*))
                          (r-w-x     :type (member  :r :w :x))
                          x86-1 x86-2)
  :non-executable t
  :verify-guards nil
  :enabled t
  (and (equal (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x x86-1))
              (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x x86-2)))
       (equal (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x x86-1))
              (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x x86-2)))))

(defthm paging-equiv-int-transitive
        (implies (and (paging-equiv-int lin-addr r-w-x x86-1 x86-2)
                      (paging-equiv-int lin-addr r-w-x x86-2 x86-3))
                 (paging-equiv-int lin-addr r-w-x x86-1 x86-3)))

(defthm paging-equiv-int-commute
        (equal (paging-equiv-int lin-addr r-w-x x86-1 x86-2)
               (paging-equiv-int lin-addr r-w-x x86-2 x86-1)))

(defthm paging-equiv-int-ident
        (paging-equiv-int lin-addr r-w-x x86-1 x86-1))

(defthm paging-equiv-int-boolean
        (booleanp (paging-equiv-int lin-addr r-w-x x86-1 x86-2)))

(define paging-equiv-n (n lin-addr r-w-x x86-1 x86-2)
  :non-executable t
  :verify-guards nil
  :enabled t
  (if (zp n)
    t
    (and (paging-equiv-int lin-addr r-w-x x86-1 x86-2)
         (paging-equiv-n (1- n) (1+ lin-addr) r-w-x x86-1 x86-2))))

(defthm paging-equiv-n-transitive
        (implies (and (paging-equiv-n n lin-addr r-w-x x86-1 x86-2)
                      (paging-equiv-n n lin-addr r-w-x x86-2 x86-3))
                 (paging-equiv-n n lin-addr r-w-x x86-1 x86-3)))

(defthm paging-equiv-n-commute
        (equal (paging-equiv-n n lin-addr r-w-x x86-1 x86-2)
               (paging-equiv-n n lin-addr r-w-x x86-2 x86-1)))

(defthm paging-equiv-n-ident
        (paging-equiv-n n lin-addr r-w-x x86-1 x86-1))

(defthm paging-equiv-n-boolean
        (booleanp (paging-equiv-n n lin-addr r-w-x x86-1 x86-2)))


(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthm paging-equiv-n-ia32e-la-to-pa
          (implies (and (paging-equiv-n n addr r-w-x-2 x86-1 x86-2)
                        (equal r-w-x-2 r-w-x)
                        (not (zp n))
                        (canonical-address-p addr)
                        (canonical-address-p addr2)
                        (<= addr addr2)
                        (< addr2 (+ addr n)))
                   (and (equal (mv-nth 0 (ia32e-la-to-pa addr2 r-w-x x86-1))
                               (mv-nth 0 (ia32e-la-to-pa addr2 r-w-x x86-2)))
                        (equal (mv-nth 1 (ia32e-la-to-pa addr2 r-w-x x86-1))
                               (mv-nth 1 (ia32e-la-to-pa addr2 r-w-x x86-2)))))
          :hints (("Goal" :in-theory (enable signed-byte-p))))

  (defthm ia32e-la-to-pa-paging-equiv-n
          (equal (paging-equiv-n n lin-addr r-w-x
                                 x86
                                 (mv-nth 2 (ia32e-la-to-pa lin-addr2 r-w-x2 x862)))
                 (paging-equiv-n n lin-addr r-w-x x86 x862)))

  (defthm ia32e-la-to-pa-without-tlb-paging-equiv-n
          (equal (paging-equiv-n n lin-addr r-w-x
                                 x86
                                 (mv-nth 2 (ia32e-la-to-pa-without-tlb lin-addr2 r-w-x2 x862)))
                 (paging-equiv-n n lin-addr r-w-x x86 x862))
          :hints (("Goal" :do-not '(generalize)))))

(defthm paging-equiv-n-app-view
        (implies (and (app-view x86-1)
                      (app-view x86-2))
                 (paging-equiv-n n lin-addr r-w-x x86-1 x86-2))
        :hints (("Goal" :in-theory (enable ia32e-la-to-pa))))

(define paging-equiv (x86-1 x86-2)
  :verify-guards nil
  :non-executable t
  :enabled t
  (and (paging-equiv-n (expt 2 48) (- (expt 2 47)) :r x86-1 x86-2)
       (paging-equiv-n (expt 2 48) (- (expt 2 47)) :w x86-1 x86-2)
       (paging-equiv-n (expt 2 48) (- (expt 2 47)) :x x86-1 x86-2)))

(defequiv paging-equiv)

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (local (defthmd ia32e-la-to-pa-paging-equiv-canonical-address-p
                  (implies (and (paging-equiv x86-1 x86-2)
                                (canonical-address-p lin-addr))
                           (and (equal (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x x86-1))
                                       (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x x86-2)))
                                (equal (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x x86-1))
                                       (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x x86-2)))))
                  :hints (("Goal" :cases ((member-p r-w-x '(:r :w :x)))
                           :in-theory (enable signed-byte-p)))))

  (local (in-theory (enable ia32e-la-to-pa-fixes-address)))

  (defthm mv-nth-0-ia32e-la-to-pa-paging-equiv-cong
          (implies (paging-equiv x86-1 x86-2)
                   (equal (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x x86-1))
                          (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x x86-2))))
          :rule-classes :congruence
          :hints (("Goal" :in-theory (disable paging-equiv)
                   :use ((:instance ia32e-la-to-pa-paging-equiv-canonical-address-p)
                         (:instance ia32e-la-to-pa-paging-equiv-canonical-address-p
                                    (lin-addr (logext 48 lin-addr)))))))

  (defthm mv-nth-1-ia32e-la-to-pa-paging-equiv-cong
          (implies (paging-equiv x86-1 x86-2)
                   (equal (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x x86-1))
                          (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x x86-2))))
          :rule-classes :congruence
          :hints (("Goal" :in-theory (disable paging-equiv)
                   :use ((:instance ia32e-la-to-pa-paging-equiv-canonical-address-p)
                         (:instance ia32e-la-to-pa-paging-equiv-canonical-address-p
                                    (lin-addr (logext 48 lin-addr)))))))

  (defthm ia32e-la-to-pa-paging-equiv
          (paging-equiv (mv-nth 2 (ia32e-la-to-pa lin-addr r-w-x x86))
                        (double-rewrite x86))
          :hints (("Goal" :in-theory (enable paging-equiv-n))))

  (defthm mv-nth-2-ia32e-la-to-pa-paging-equiv-cong
          (implies (paging-equiv x86-1 x86-2)
                   (paging-equiv (mv-nth 2 (ia32e-la-to-pa lin-addr r-w-x x86-1))
                                 (mv-nth 2 (ia32e-la-to-pa lin-addr r-w-x x86-2))))
          :rule-classes :congruence
          :hints (("Goal" :in-theory (disable paging-equiv)
                   :use ((:instance ia32e-la-to-pa-paging-equiv-canonical-address-p)
                         (:instance ia32e-la-to-pa-paging-equiv-canonical-address-p
                                    (lin-addr (logext 48 lin-addr)))))))

  (defthm paging-equiv-app-view
          (implies (and (app-view x86-1)
                        (app-view x86-2))
                   (paging-equiv x86-1 x86-2)))

  (defthm mv-nth-2-ia32e-la-to-pa-without-tlb-paging-equiv
        (paging-equiv (mv-nth 2 (ia32e-la-to-pa-without-tlb lin-addr r-w-x x86))
                      x86)
        :hints (("Goal" :in-theory (enable paging-equiv-n)))))

(in-theory (disable paging-equiv))

(defthm mv-nth-0-las-to-pas-paging-equiv-cong
        (implies (paging-equiv x86-1 x86-2)
                 (equal (mv-nth 0 (las-to-pas n lin-addr r-w-x x86-1))
                        (mv-nth 0 (las-to-pas n lin-addr r-w-x x86-2))))
        :rule-classes :congruence)

(defthm mv-nth-1-las-to-pas-paging-equiv-cong
        (implies (paging-equiv x86-1 x86-2)
                 (equal (mv-nth 1 (las-to-pas n lin-addr r-w-x x86-1))
                        (mv-nth 1 (las-to-pas n lin-addr r-w-x x86-2))))
        :rule-classes :congruence)

(defthm mv-nth-2-las-to-pas-paging-equiv-cong
        (implies (paging-equiv x86-1 x86-2)
                 (paging-equiv (mv-nth 2 (las-to-pas n lin-addr r-w-x x86-1))
                               (mv-nth 2 (las-to-pas n lin-addr r-w-x x86-2))))
        :rule-classes :congruence)

(defthm mv-nth-2-las-to-pas-paging-equiv
        (paging-equiv (mv-nth 2 (las-to-pas n lin-addr r-w-x x86))
                      x86))

;; This is an obvious corollary of the above. In some contexts,
;; this rewrite rule is necessary to get ACL2 to make this simplification.
;; I don't understand why.
(defthm las-to-pas-mv-nth-2-las-to-pas
        (and (equal (mv-nth 0 (las-to-pas n lin-addr r-w-x
                                          (mv-nth 2 (las-to-pas n2 lin-addr2 r-w-x2 x86))))
                    (mv-nth 0 (las-to-pas n lin-addr r-w-x x86)))
             (equal (mv-nth 1 (las-to-pas n lin-addr r-w-x
                                          (mv-nth 2 (las-to-pas n2 lin-addr2 r-w-x2 x86))))
                    (mv-nth 1 (las-to-pas n lin-addr r-w-x x86)))))

(include-book "gather-paging-structures" :ttags :all)

(define paging-equiv-memory (x86-1 x86-2)
  :non-executable t
  :verify-guards nil
  (if (and (equal (xr :app-view nil x86-1) nil)
           (equal (xr :app-view nil x86-2) nil)
           (64-bit-modep x86-1)
           (64-bit-modep x86-2))

      (and (paging-equiv x86-1 x86-2)
           (all-mem-except-paging-structures-equal x86-1 x86-2))

    (equal x86-1 x86-2))
  ///
  (defequiv paging-equiv-memory)

  (defthm paging-equiv-refines-all-mem-except-paging-structures-equal
    (implies (paging-equiv-memory x86-1 x86-2)
             (all-mem-except-paging-structures-equal x86-1 x86-2))
    :rule-classes :refinement)

  (defthm paging-equiv-refines-paging-equiv
    (implies (paging-equiv-memory x86-1 x86-2)
             (paging-equiv x86-1 x86-2))
    :rule-classes :refinement)

  (defcong paging-equiv-memory equal (64-bit-modep x86) 1)

  (defcong paging-equiv-memory equal (app-view x86) 1))

;; I'm going to be honest, I'm not 100% sure what this does. I copied it
;; from gather-paging-structures.lisp's analogous definitions for xlate-equiv-structures
;; and swapped xlate-equiv-structures for paging-equiv for use in the theorems where in the
;; hypothesis places where I've replaced xlate-equiv-* with paging-equiv*.
(defun find-paging-equiv-structures-from-occurrence
    (bound-x86-term mfc state)
  (declare (xargs :stobjs (state) :mode :program)
           (ignorable state))
  (b* ((call (acl2::find-call-lst 'paging-equiv-memory (acl2::mfc-clause mfc)))
       ((when (not call))
        ;; paging-equiv term not encountered.
        nil)
       (x86-1-var (second call))
       (x86-2-var (third call))

       (x86-var
        (if (equal bound-x86-term x86-1-var)
            x86-2-var
          x86-1-var)))
    x86-var))

(defun find-an-paging-equiv-x86-aux (thm-name x86-term mfc state)
  (declare (xargs :stobjs (state) :mode :program)
           (ignorable thm-name state))

  ;; Finds a "smaller" x86 that is paging-equiv to x86-term.
  (if (atom x86-term)

      (b* ((equiv-x86-term
            (find-paging-equiv-structures-from-occurrence
             x86-term ;; bound-x86-term
             mfc state))
           ((when (not equiv-x86-term))
            x86-term))
        equiv-x86-term)

    (b* ((outer-fn (car x86-term))
         ((when (and (not (equal outer-fn 'MV-NTH))
                     (not (equal outer-fn 'WM-LOW-64))
                     ;; (not (equal outer-fn '!FLGI))
                     (not (and (equal outer-fn 'XW)
                               (equal (second x86-term) '':MEM)))))
          ;; (cw "~%~p0: Unexpected x86-term encountered:~p1~%" thm-name x86-term)
          x86-term
          ))
      (cond ((equal outer-fn 'MV-NTH)
             ;; We expect x86-term to be a function related to page
             ;; traversals.
             (b* ((mv-nth-index (second x86-term))
                  (inner-fn-call (third x86-term))
                  (inner-fn (first inner-fn-call))
                  ((when (if (equal mv-nth-index ''2)
                             (not (member-p inner-fn
                                            '(IA32E-LA-TO-PA-PAGE-TABLE
                                              IA32E-LA-TO-PA-PAGE-DIRECTORY
                                              IA32E-LA-TO-PA-PAGE-DIR-PTR-TABLE
                                              IA32E-LA-TO-PA-PML4-TABLE
                                              IA32E-LA-TO-PA
                                              LAS-TO-PAS
                                              PAGING-ENTRY-NO-PAGE-FAULT-P$INLINE
                                              RM08
                                              RB
                                              GET-PREFIXES
                                              RB-ALT
                                              GET-PREFIXES-ALT)))
                           (if (equal mv-nth-index ''1)
                               (not (member-p inner-fn '(WM08 WB)))
                             t)))
                   ;; (cw "~%~p0: Unexpected mv-nth x86-term encountered:~p1~%" thm-name x86-term)
                   x86-term)
                  (sub-x86
                   (if (equal inner-fn 'PAGING-ENTRY-NO-PAGE-FAULT-P$INLINE)
                       ;; x86 is the next to last argument for these functions.
                       (first (last (butlast inner-fn-call 1)))
                     (first (last inner-fn-call)))))
               sub-x86))
            ((or (equal outer-fn 'WM-LOW-64)
                 (equal outer-fn 'XW)
                 ;; (equal outer-fn '!FLGI)
                 )
             ;; We expect x86-term to be of the form (wm-low-64 index
             ;; val sub-x86) or (xw :mem val index).
             (b* ((sub-x86 (first (last x86-term))))
               sub-x86))))))

(defun find-an-paging-equiv-x86 (thm-name bound-x86-term free-x86-var mfc state)
  (declare (xargs :stobjs (state) :mode :program)
           (ignorable thm-name state))
  ;; bind-free for an x86 in paging-equiv-structures: should check just
  ;; for the page traversal functions and wm-low-64.
  (declare (xargs :mode :program))
  (b* ((equiv-x86 (find-an-paging-equiv-x86-aux thm-name bound-x86-term mfc state)))
    `((,free-x86-var . ,equiv-x86))))
