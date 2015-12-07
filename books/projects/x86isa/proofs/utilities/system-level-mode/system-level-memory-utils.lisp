;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")
(include-book "paging-lib/paging-top")

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "centaur/gl/gl" :dir :system))

;; ======================================================================

(defsection system-level-memory-utils
  :parents (proof-utilities)

  :short "Helper lemmas for reasoning about memory in the system-level
  mode"
  )

(local (xdoc::set-default-parents system-level-memory-utils))

(local (in-theory (e/d* (entry-found-p-and-good-paging-structures-x86p
                         entry-found-p-and-lin-addr)
                        ())))

;; ======================================================================

(local
 (defthm good-paging-structures-x86p-implies-mult-8-qword-paddr-list-listp-paging-structure-addrs
   (implies (good-paging-structures-x86p X86)
            (mult-8-qword-paddr-list-listp
             (gather-all-paging-structure-qword-addresses x86)))
   :hints (("Goal" :in-theory (e/d* (good-paging-structures-x86p) ())))))

(defthm rm08-wm08-disjoint-in-system-level-mode
  (implies (and (not (programmer-level-mode x86))
                (paging-entries-found-p addr-1 x86)
                (paging-entries-found-p addr-2 x86)
                (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
                (not
                 ;; The physical addresses corresponding to addr-1 and
                 ;; addr-2 are different.
                 (equal (mv-nth 1 (ia32e-entries-found-la-to-pa addr-1 r-x cpl x86))
                        (mv-nth 1 (ia32e-entries-found-la-to-pa addr-2 :w cpl x86))))
                (pairwise-disjoint-p-aux
                 ;; The read isn't being done from the page tables.
                 (list (mv-nth 1 (ia32e-entries-found-la-to-pa addr-1 r-x cpl x86)))
                 (open-qword-paddr-list-list (gather-all-paging-structure-qword-addresses x86)))
                (pairwise-disjoint-p-aux
                 ;; The write isn't being done to the page tables ---
                 ;; this means that the translation-governing entries
                 ;; for addr-1 cannot be affected by the write.
                 (list (mv-nth 1 (ia32e-entries-found-la-to-pa addr-2 :w cpl x86)))
                 (open-qword-paddr-list-list
                  (gather-all-paging-structure-qword-addresses x86)))
                (unsigned-byte-p 8 val))
           (equal (mv-nth 1 (rm08 addr-1 r-x (mv-nth 1 (wm08 addr-2 val x86))))
                  (mv-nth 1 (rm08 addr-1 r-x x86))))
  :hints (("Goal"
           :use ((:instance gather-all-paging-structure-qword-addresses-xw-fld=mem-disjoint
                            (addrs (gather-all-paging-structure-qword-addresses x86))
                            (index (mv-nth 1 (ia32e-entries-found-la-to-pa addr-2 :w cpl x86)))
                            (val val)
                            (x86 x86)))
           :in-theory (e/d* (ia32e-la-to-pa-and-ia32e-entries-found-la-to-pa
                             rm08
                             wm08)
                            (signed-byte-p
                             unsigned-byte-p
                             gather-all-paging-structure-qword-addresses-xw-fld=mem-disjoint)))))

;; ======================================================================

;; Relating top-level memory accessors and updaters with rb and wb in
;; system-level mode:

(defthm rb-and-rm08-in-the-system-level-mode
  (implies (and (not (programmer-level-mode x86))
                (paging-entries-found-p lin-addr x86))
           (equal (rm08 lin-addr r-x x86)
                  (b* (((mv flg bytes x86)
                        (rb (create-canonical-address-list 1 lin-addr) r-x x86))
                       (result (combine-bytes bytes)))
                    (mv flg result x86))))
  :hints (("Goal"
           :in-theory (e/d* (ia32e-la-to-pa-and-ia32e-entries-found-la-to-pa
                             rm08
                             rb)
                            (signed-byte-p
                             unsigned-byte-p)))))

(defthm wb-and-wm08-in-the-system-level-mode
  (implies (and (not (programmer-level-mode x86))
                (paging-entries-found-p lin-addr x86)
                (unsigned-byte-p 8 byte))
           (equal (wm08 lin-addr byte x86)
                  (wb (create-addr-bytes-alist
                       (create-canonical-address-list 1 lin-addr)
                       (list byte))
                      x86)))
  :hints (("Goal"
           :in-theory (e/d* (ia32e-la-to-pa-and-ia32e-entries-found-la-to-pa
                             wm08
                             wb)
                            (signed-byte-p
                             unsigned-byte-p)))))

(defthm rb-and-rm16-in-system-level-mode
  (implies (and ;; (not (programmer-level-mode x86))
            (paging-entries-found-p lin-addr x86)
            (paging-entries-found-p (1+ lin-addr) x86)
            (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))

            ;; No page faults occur during the translation of (+ 1
            ;; lin-addr).
            ;; (not (mv-nth 0 (ia32e-la-to-pa      lin-addr  r-w-x cpl x86)))
            (not (mv-nth 0 (ia32e-la-to-pa (+ 1 lin-addr) r-w-x cpl x86)))

            ;; Physical address corresponding to lin-addr does not
            ;; contain any paging information.
            (pairwise-disjoint-p-aux
             (list (mv-nth 1 (ia32e-entries-found-la-to-pa lin-addr r-w-x cpl x86)))
             (open-qword-paddr-list-list
              (gather-all-paging-structure-qword-addresses x86)))
            ;; (pairwise-disjoint-p-aux
            ;;  (list (mv-nth 1 (ia32e-entries-found-la-to-pa (+ 1 lin-addr) r-w-x cpl x86)))
            ;;  (open-qword-paddr-list-list
            ;;   (gather-all-paging-structure-qword-addresses x86)))
            )
           (equal (rm16 lin-addr r-w-x x86)
                  (b* (((mv flg bytes x86)
                        (rb (create-canonical-address-list 2 lin-addr) r-w-x x86))
                       (result (combine-bytes bytes)))
                    (mv flg result x86))))
  :hints (("Goal"
           :in-theory (e/d* (ia32e-la-to-pa-and-ia32e-entries-found-la-to-pa
                             rm16
                             rm08)
                            (signed-byte-p
                             unsigned-byte-p
                             bitops::logior-equal-0
                             rb-and-rm08-in-the-system-level-mode
                             (:meta acl2::mv-nth-cons-meta))))))

(defthm wb-and-wm16-in-system-level-mode
  (implies (and ;; (not (programmer-level-mode x86))
            (paging-entries-found-p lin-addr x86)
            (paging-entries-found-p (1+ lin-addr) x86)
            (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))

            ;; No page faults occur during the translation of (+ 1 lin-addr).
            ;; (not (mv-nth 0 (ia32e-la-to-pa      lin-addr  :w cpl x86)))
            (not (mv-nth 0 (ia32e-la-to-pa (+ 1 lin-addr) :w cpl x86)))

            ;; Physical address corresponding to lin-addr does not
            ;; contain any paging infowmation.
            (pairwise-disjoint-p-aux
             (list (mv-nth 1 (ia32e-entries-found-la-to-pa lin-addr :w cpl x86)))
             (open-qword-paddr-list-list
              (gather-all-paging-structure-qword-addresses x86)))
            ;; (pairwise-disjoint-p-aux
            ;;  (list (mv-nth 1 (ia32e-entries-found-la-to-pa (+ 1 lin-addr) :w cpl x86)))
            ;;  (open-qword-paddr-list-list
            ;;   (gather-all-paging-structure-qword-addresses x86)))
            )
           (equal (wm16 lin-addr word x86)
                  (b* (((mv flg x86)
                        (wb (create-addr-bytes-alist
                             (create-canonical-address-list 2 lin-addr)
                             (byte-ify 2 word))
                            x86)))
                    (mv flg x86))))
  :hints (("Goal"
           :in-theory (e/d* (ia32e-la-to-pa-and-ia32e-entries-found-la-to-pa
                             wm16
                             wm08
                             byte-ify)
                            (signed-byte-p
                             unsigned-byte-p
                             bitops::logior-equal-0
                             wb-and-wm08-in-the-system-level-mode
                             (:meta acl2::mv-nth-cons-meta))))))


(local
 (def-gl-thm rm32-rb-system-level-mode-proof-helper
   :hyp (and (n08p a)
             (n08p b)
             (n08p c)
             (n08p d))
   :concl (equal (logior a (ash b 8) (ash (logior c (ash d 8)) 16))
                 (logior a (ash (logior b (ash (logior c (ash d 8)) 8)) 8)))
   :g-bindings
   (gl::auto-bindings
    (:mix (:nat a 8) (:nat b 8) (:nat c 8) (:nat d 8)))
   :rule-classes :linear))

(local (in-theory (e/d () (rm32-rb-system-level-mode-proof-helper))))

(defthm rb-and-rm32-in-system-level-mode
  (implies (and ;; (not (programmer-level-mode x86))
            (paging-entries-found-p      lin-addr  x86)
            (paging-entries-found-p (+ 1 lin-addr) x86)
            (paging-entries-found-p (+ 2 lin-addr) x86)
            (paging-entries-found-p (+ 3 lin-addr) x86)
            (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
            (not (mv-nth 0 (ia32e-la-to-pa (+ 1 lin-addr) r-w-x cpl x86)))
            (not (mv-nth 0 (ia32e-la-to-pa (+ 2 lin-addr) r-w-x cpl x86)))
            (not (mv-nth 0 (ia32e-la-to-pa (+ 3 lin-addr) r-w-x cpl x86)))
            ;; Physical address corresponding to lin-addr does not
            ;; contain any paging information.
            (pairwise-disjoint-p-aux
             (list (mv-nth 1 (ia32e-entries-found-la-to-pa lin-addr r-w-x cpl x86)))
             (open-qword-paddr-list-list
              (gather-all-paging-structure-qword-addresses x86)))
            (pairwise-disjoint-p-aux
             (list (mv-nth 1 (ia32e-entries-found-la-to-pa (+ 1 lin-addr) r-w-x cpl x86)))
             (open-qword-paddr-list-list
              (gather-all-paging-structure-qword-addresses x86)))
            (pairwise-disjoint-p-aux
             (list (mv-nth 1 (ia32e-entries-found-la-to-pa (+ 2 lin-addr) r-w-x cpl x86)))
             (open-qword-paddr-list-list
              (gather-all-paging-structure-qword-addresses x86))))
           (equal (rm32 lin-addr r-w-x x86)
                  (b* (((mv flg bytes x86)
                        (rb (create-canonical-address-list 4 lin-addr) r-w-x x86))
                       (result (combine-bytes bytes)))
                    (mv flg result x86))))
  :hints (("Goal"
           :in-theory (e/d* (ia32e-la-to-pa-and-ia32e-entries-found-la-to-pa
                             rm32
                             rm08
                             rm32-rb-system-level-mode-proof-helper)
                            (signed-byte-p
                             unsigned-byte-p
                             bitops::logior-equal-0
                             rb-and-rm08-in-the-system-level-mode
                             (:meta acl2::mv-nth-cons-meta))))))

(defthm wb-and-wm32-in-system-level-mode
  (implies (and (paging-entries-found-p lin-addr x86)
                (paging-entries-found-p (+ 1 lin-addr) x86)
                (paging-entries-found-p (+ 2 lin-addr) x86)
                (paging-entries-found-p (+ 3 lin-addr) x86)
                (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
                (not (mv-nth 0 (ia32e-la-to-pa (+ 1 lin-addr) :w cpl x86)))
                (not (mv-nth 0 (ia32e-la-to-pa (+ 2 lin-addr) :w cpl x86)))
                (not (mv-nth 0 (ia32e-la-to-pa (+ 3 lin-addr) :w cpl x86)))
                (pairwise-disjoint-p-aux
                 (list (mv-nth 1 (ia32e-entries-found-la-to-pa lin-addr :w cpl x86)))
                 (open-qword-paddr-list-list
                  (gather-all-paging-structure-qword-addresses x86)))
                (pairwise-disjoint-p-aux
                 (list (mv-nth 1 (ia32e-entries-found-la-to-pa (+ 1 lin-addr) :w cpl x86)))
                 (open-qword-paddr-list-list
                  (gather-all-paging-structure-qword-addresses x86)))
                (pairwise-disjoint-p-aux
                 (list (mv-nth 1 (ia32e-entries-found-la-to-pa (+ 2 lin-addr) :w cpl x86)))
                 (open-qword-paddr-list-list
                  (gather-all-paging-structure-qword-addresses x86))))
           (equal (wm32 lin-addr dword x86)
                  (b* (((mv flg x86)
                        (wb (create-addr-bytes-alist
                             (create-canonical-address-list 4 lin-addr)
                             (byte-ify 4 dword))
                            x86)))
                    (mv flg x86))))
  :hints (("Goal"
           :in-theory (e/d* (ia32e-la-to-pa-and-ia32e-entries-found-la-to-pa
                             wm32
                             wm08
                             byte-ify
                             rm32-rb-system-level-mode-proof-helper)
                            (signed-byte-p
                             unsigned-byte-p
                             bitops::logior-equal-0
                             wb-and-wm08-in-the-system-level-mode
                             (:meta acl2::mv-nth-cons-meta))))))

(local
 (def-gl-thm rb-and-rvm64-helper
   :hyp (and (n08p a) (n08p b) (n08p c) (n08p d)
             (n08p e) (n08p f) (n08p g) (n08p h))
   :concl (equal
           (logior a (ash b 8)
                   (ash (logior c (ash d 8)) 16)
                   (ash (logior e (ash f 8) (ash (logior g (ash h 8)) 16)) 32))
           (logior a
                   (ash (logior
                         b
                         (ash (logior
                               c
                               (ash (logior
                                     d
                                     (ash (logior
                                           e
                                           (ash (logior f (ash (logior g (ash h 8)) 8)) 8)) 8)) 8))
                              8))
                        8)))
   :g-bindings
   (gl::auto-bindings
    (:mix (:nat a 8) (:nat b 8) (:nat c 8) (:nat d 8)
          (:nat e 8) (:nat f 8) (:nat g 8) (:nat h 8)))
   :rule-classes :linear))

(local (in-theory (e/d () (rb-and-rvm64-helper))))

(defthm rb-and-rm64-in-system-level-mode
  (implies (and (not (programmer-level-mode x86))
                (paging-entries-found-p      lin-addr  x86)
                (paging-entries-found-p (+ 1 lin-addr) x86)
                (paging-entries-found-p (+ 2 lin-addr) x86)
                (paging-entries-found-p (+ 3 lin-addr) x86)
                (paging-entries-found-p (+ 4 lin-addr) x86)
                (paging-entries-found-p (+ 5 lin-addr) x86)
                (paging-entries-found-p (+ 6 lin-addr) x86)
                (paging-entries-found-p (+ 7 lin-addr) x86)
                (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))

                ;; No page faults occur during the translation of lin-addr
                ;; to (+ 7 lin-addr).
                (not (mv-nth 0 (ia32e-la-to-pa      lin-addr  r-w-x cpl x86)))
                (not (mv-nth 0 (ia32e-la-to-pa (+ 1 lin-addr) r-w-x cpl x86)))
                (not (mv-nth 0 (ia32e-la-to-pa (+ 2 lin-addr) r-w-x cpl x86)))
                (not (mv-nth 0 (ia32e-la-to-pa (+ 3 lin-addr) r-w-x cpl x86)))
                (not (mv-nth 0 (ia32e-la-to-pa (+ 4 lin-addr) r-w-x cpl x86)))
                (not (mv-nth 0 (ia32e-la-to-pa (+ 5 lin-addr) r-w-x cpl x86)))
                (not (mv-nth 0 (ia32e-la-to-pa (+ 6 lin-addr) r-w-x cpl x86)))
                (not (mv-nth 0 (ia32e-la-to-pa (+ 7 lin-addr) r-w-x cpl x86)))

                ;; Physical address corresponding to lin-addr does not
                ;; contain any paging information.
                (pairwise-disjoint-p-aux
                 (list (mv-nth 1 (ia32e-entries-found-la-to-pa lin-addr r-w-x cpl x86)))
                 (open-qword-paddr-list-list
                  (gather-all-paging-structure-qword-addresses x86)))
                (pairwise-disjoint-p-aux
                 (list (mv-nth 1 (ia32e-entries-found-la-to-pa (+ 1 lin-addr) r-w-x cpl x86)))
                 (open-qword-paddr-list-list
                  (gather-all-paging-structure-qword-addresses x86)))
                (pairwise-disjoint-p-aux
                 (list (mv-nth 1 (ia32e-entries-found-la-to-pa (+ 2 lin-addr) r-w-x cpl x86)))
                 (open-qword-paddr-list-list
                  (gather-all-paging-structure-qword-addresses x86)))
                (pairwise-disjoint-p-aux
                 (list (mv-nth 1 (ia32e-entries-found-la-to-pa (+ 3 lin-addr) r-w-x cpl x86)))
                 (open-qword-paddr-list-list
                  (gather-all-paging-structure-qword-addresses x86)))
                (pairwise-disjoint-p-aux
                 (list (mv-nth 1 (ia32e-entries-found-la-to-pa (+ 4 lin-addr) r-w-x cpl x86)))
                 (open-qword-paddr-list-list
                  (gather-all-paging-structure-qword-addresses x86)))
                (pairwise-disjoint-p-aux
                 (list (mv-nth 1 (ia32e-entries-found-la-to-pa (+ 5 lin-addr) r-w-x cpl x86)))
                 (open-qword-paddr-list-list
                  (gather-all-paging-structure-qword-addresses x86)))
                (pairwise-disjoint-p-aux
                 (list (mv-nth 1 (ia32e-entries-found-la-to-pa (+ 6 lin-addr) r-w-x cpl x86)))
                 (open-qword-paddr-list-list
                  (gather-all-paging-structure-qword-addresses x86)))
                (pairwise-disjoint-p-aux
                 (list (mv-nth 1 (ia32e-entries-found-la-to-pa (+ 7 lin-addr) r-w-x cpl x86)))
                 (open-qword-paddr-list-list
                  (gather-all-paging-structure-qword-addresses x86))))
           (equal (rm64 lin-addr r-w-x x86)
                  (b* (((mv flg bytes x86)
                        (rb (create-canonical-address-list 8 lin-addr) r-w-x x86))
                       (result (combine-bytes bytes)))
                    (mv flg result x86))))
  :hints (("Goal"
           :in-theory (e/d* (ia32e-la-to-pa-and-ia32e-entries-found-la-to-pa
                             rb-and-rvm64-helper
                             rm64 rm08)
                            (signed-byte-p
                             unsigned-byte-p
                             bitops::logior-equal-0
                             rb-and-rm08-in-the-system-level-mode
                             (:meta acl2::mv-nth-cons-meta))))))

;; (i-am-here)

;; (defthm wb-and-wm64-in-system-level-mode
;;   (implies (and
;;             (not (programmer-level-mode x86))
;;             (paging-entries-found-p      lin-addr  x86)
;;             (paging-entries-found-p (+ 1 lin-addr) x86)
;;             (paging-entries-found-p (+ 2 lin-addr) x86)
;;             (paging-entries-found-p (+ 3 lin-addr) x86)
;;             (paging-entries-found-p (+ 4 lin-addr) x86)
;;             (paging-entries-found-p (+ 5 lin-addr) x86)
;;             (paging-entries-found-p (+ 6 lin-addr) x86)
;;             (paging-entries-found-p (+ 7 lin-addr) x86)
;;             (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))

;;             ;; No page faults occur during the translation of lin-addr
;;             ;; to (+ 7 lin-addr).
;;             (not (mv-nth 0 (ia32e-la-to-pa      lin-addr  :w cpl x86)))
;;             (not (mv-nth 0 (ia32e-la-to-pa (+ 1 lin-addr) :w cpl x86)))
;;             (not (mv-nth 0 (ia32e-la-to-pa (+ 2 lin-addr) :w cpl x86)))
;;             (not (mv-nth 0 (ia32e-la-to-pa (+ 3 lin-addr) :w cpl x86)))
;;             (not (mv-nth 0 (ia32e-la-to-pa (+ 4 lin-addr) :w cpl x86)))
;;             (not (mv-nth 0 (ia32e-la-to-pa (+ 5 lin-addr) :w cpl x86)))
;;             (not (mv-nth 0 (ia32e-la-to-pa (+ 6 lin-addr) :w cpl x86)))
;;             (not (mv-nth 0 (ia32e-la-to-pa (+ 7 lin-addr) :w cpl x86)))

;;             ;; Physical address corresponding to lin-addr does not
;;             ;; contain any paging infowmation.
;;             ;; (pairwise-disjoint-p-aux
;;             ;;  (list (mv-nth 1 (ia32e-entries-found-la-to-pa lin-addr :w cpl x86)))
;;             ;;  (open-qword-paddr-list-list
;;             ;;   (gather-all-paging-structure-qword-addresses x86)))
;;             (pairwise-disjoint-p-aux
;;              (list (mv-nth 1 (ia32e-entries-found-la-to-pa (+ 1 lin-addr) :w cpl x86)))
;;              (open-qword-paddr-list-list
;;               (gather-all-paging-structure-qword-addresses x86)))
;;             (pairwise-disjoint-p-aux
;;              (list (mv-nth 1 (ia32e-entries-found-la-to-pa (+ 2 lin-addr) :w cpl x86)))
;;              (open-qword-paddr-list-list
;;               (gather-all-paging-structure-qword-addresses x86)))
;;             (pairwise-disjoint-p-aux
;;              (list (mv-nth 1 (ia32e-entries-found-la-to-pa (+ 3 lin-addr) :w cpl x86)))
;;              (open-qword-paddr-list-list
;;               (gather-all-paging-structure-qword-addresses x86)))
;;             (pairwise-disjoint-p-aux
;;              (list (mv-nth 1 (ia32e-entries-found-la-to-pa (+ 4 lin-addr) :w cpl x86)))
;;              (open-qword-paddr-list-list
;;               (gather-all-paging-structure-qword-addresses x86)))
;;             (pairwise-disjoint-p-aux
;;              (list (mv-nth 1 (ia32e-entries-found-la-to-pa (+ 5 lin-addr) :w cpl x86)))
;;              (open-qword-paddr-list-list
;;               (gather-all-paging-structure-qword-addresses x86)))
;;             (pairwise-disjoint-p-aux
;;              (list (mv-nth 1 (ia32e-entries-found-la-to-pa (+ 6 lin-addr) :w cpl x86)))
;;              (open-qword-paddr-list-list
;;               (gather-all-paging-structure-qword-addresses x86)))
;;             (pairwise-disjoint-p-aux
;;              (list (mv-nth 1 (ia32e-entries-found-la-to-pa (+ 7 lin-addr) :w cpl x86)))
;;              (open-qword-paddr-list-list
;;               (gather-all-paging-structure-qword-addresses x86))))
;;            (equal (wm64 lin-addr qword x86)
;;                   (b* (((mv flg bytes x86)
;;                         (wb (create-addr-bytes-alist
;;                              (create-canonical-address-list 8 lin-addr)
;;                              (byte-ify 8 qword))
;;                             x86))
;;                        (result (combine-bytes bytes)))
;;                     (mv flg result x86))))
;;   :hints (("Goal"
;;            :in-theory (e/d* (ia32e-la-to-pa-and-ia32e-entries-found-la-to-pa
;;                              rb-and-rvm64-helper
;;                              wm64
;;                              wm08
;;                              byte-ify)
;;                             (signed-byte-p
;;                              unsigned-byte-p
;;                              bitops::logior-equal-0
;;                              wb-and-wm08-in-the-system-level-mode
;;                              (:meta acl2::mv-nth-cons-meta))))))

;; ======================================================================
