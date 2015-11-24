;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")
(include-book "paging-page-table-lemmas" :ttags :all)

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "centaur/bitops/signed-byte-p" :dir :system))
(local (include-book "centaur/gl/gl" :dir :system))

;; ======================================================================

(local
 (def-gl-thm logand-loghead-and-page-directory-base-addr-helper
   :hyp (unsigned-byte-p 64 x)
   :concl (equal (logand 18446744073709547520 (ash (loghead 40 (logtail 12 x)) 12))
                 (ash (loghead 40 (logtail 12 x)) 12))
   :g-bindings `((x (:g-number ,(gl-int 0 1 65))))))

;; (local
;;  (defthm logand-loghead-and-page-directory-base-addr
;;    (implies (x86p x86)
;;             (equal (logand 18446744073709547520
;;                            (loghead 52 (mv-nth 1 (page-directory-base-addr lin-addr x86))))
;;                    (mv-nth 1 (page-directory-base-addr lin-addr x86))))
;;    :hints (("Goal" :in-theory (e/d* (page-directory-base-addr) ())))))

;; (defthmd page-directory-entry-addr-found-p-and-lin-addr
;;   (implies (page-directory-entry-addr-found-p lin-addr x86)
;;            (equal (logext 48 lin-addr) lin-addr))
;;   :hints (("Goal" :in-theory (e/d* (page-directory-entry-addr-found-p
;;                                     page-table-entry-addr-found-p
;;                                     page-dir-ptr-table-entry-addr-found-p
;;                                     pml4-table-entry-addr-found-p)
;;                                    ()))))

(i-am-here)

(local
 (defthmd ia32e-la-to-pa-PD-with-xlate-equiv-x86s-2M-pages
   ;; TO-DO: Speed this up.
   (implies (and (xlate-equiv-x86s x86-1 x86-2)
                 (logbitp
                  7
                  (rm-low-64
                   (page-directory-entry-addr
                    lin-addr
                    (mv-nth 1 (page-directory-base-addr lin-addr x86-1)))
                   x86-1)))
            (and
             (equal (mv-nth
                     0
                     (ia32e-la-to-pa-PD
                      lin-addr wp smep nxe r-w-x cpl x86-1))
                    (mv-nth
                     0
                     (ia32e-la-to-pa-PD
                      lin-addr wp smep nxe r-w-x cpl x86-2)))
             (equal (mv-nth
                     1
                     (ia32e-la-to-pa-PD
                      lin-addr wp smep nxe r-w-x cpl x86-1))
                    (mv-nth
                     1
                     (ia32e-la-to-pa-PD
                      lin-addr wp smep nxe r-w-x cpl x86-2)))))
   :hints (("Goal"
            :in-theory (e/d* (ia32e-la-to-pa-page-directory
                              page-directory-entry-addr-found-p-and-lin-addr
                              page-fault-exception)
                             (xlate-equiv-x86s
                              xlate-equiv-x86s-and-page-table-entry-addr-address
                              page-table-entry-addr-found-p-and-xlate-equiv-x86s
                              ia32e-la-to-pa-PT-with-xlate-equiv-x86s
                              xlate-equiv-x86s-and-page-directory-entry-addr-value
                              xlate-equiv-x86s-and-page-directory-base-addr-address
                              xlate-equiv-x86s-and-page-directory-entry-addr-address
                              xlate-equiv-x86s-and-page-table-base-addr-address
                              page-directory-entry-addr-found-p-and-xlate-equiv-x86s
                              bitops::logand-with-negated-bitmask
                              unsigned-byte-p
                              signed-byte-p
                              bitops::logior-equal-0))
            :use ((:instance xlate-equiv-x86s-and-page-directory-entry-addr-value)
                  (:instance xlate-equiv-x86s-and-page-directory-base-addr-address)
                  (:instance page-directory-entry-addr-found-p-and-xlate-equiv-x86s)
                  (:instance page-directory-entry-addr-found-p-and-xlate-equiv-x86s
                             (x86-1 x86-2)
                             (x86-2 x86-1))
                  (:instance page-table-entry-addr-found-p-and-xlate-equiv-x86s)
                  ;; xlate-equiv-entries-and-loghead
                  (:instance xlate-equiv-entries-and-loghead
                             (e1 (rm-low-64
                                  (page-directory-entry-addr
                                   lin-addr
                                   (mv-nth 1 (page-directory-base-addr lin-addr x86-2)))
                                  x86-1))
                             (e2 (rm-low-64
                                  (page-directory-entry-addr
                                   lin-addr
                                   (mv-nth 1 (page-directory-base-addr lin-addr x86-2)))
                                  x86-2))
                             (n 1))
                  ;; xlate-equiv-entries-and-logtail
                  (:instance xlate-equiv-entries-and-logtail
                             (e1 (rm-low-64
                                  (page-directory-entry-addr
                                   lin-addr
                                   (mv-nth 1 (page-directory-base-addr lin-addr x86-2)))
                                  x86-1))
                             (e2 (rm-low-64
                                  (page-directory-entry-addr
                                   lin-addr
                                   (mv-nth 1 (page-directory-base-addr lin-addr x86-2)))
                                  x86-2))
                             (n 13))
                  (:instance xlate-equiv-entries-and-logtail
                             (e1 (rm-low-64
                                  (page-directory-entry-addr
                                   lin-addr
                                   (mv-nth 1 (page-directory-base-addr lin-addr x86-2)))
                                  x86-1))
                             (e2 (rm-low-64
                                  (page-directory-entry-addr
                                   lin-addr
                                   (mv-nth 1 (page-directory-base-addr lin-addr x86-2)))
                                  x86-2))
                             (n 21))
                  (:instance xlate-equiv-entries-and-logtail
                             (e1 (rm-low-64
                                  (page-directory-entry-addr
                                   lin-addr
                                   (mv-nth 1 (page-directory-base-addr lin-addr x86-2)))
                                  x86-1))
                             (e2 (rm-low-64
                                  (page-directory-entry-addr
                                   lin-addr
                                   (mv-nth 1 (page-directory-base-addr lin-addr x86-2)))
                                  x86-2))
                             (n 52))
                  ;; loghead-smaller-and-logbitp
                  (:instance loghead-smaller-and-logbitp
                             (e1 (rm-low-64
                                  (page-directory-entry-addr
                                   lin-addr
                                   (mv-nth 1 (page-directory-base-addr lin-addr x86-2)))
                                  x86-1))
                             (e2 (rm-low-64
                                  (page-directory-entry-addr
                                   lin-addr
                                   (mv-nth 1 (page-directory-base-addr lin-addr x86-2)))
                                  x86-2))
                             (m 1)
                             (n 5))
                  (:instance loghead-smaller-and-logbitp
                             (e1 (rm-low-64
                                  (page-directory-entry-addr
                                   lin-addr
                                   (mv-nth 1 (page-directory-base-addr lin-addr x86-2)))
                                  x86-1))
                             (e2 (rm-low-64
                                  (page-directory-entry-addr
                                   lin-addr
                                   (mv-nth 1 (page-directory-base-addr lin-addr x86-2)))
                                  x86-2))
                             (m 2)
                             (n 5))
                  ;; logtail-bigger-and-logbitp
                  (:instance logtail-bigger-and-logbitp
                             (e1 (rm-low-64
                                  (page-directory-entry-addr
                                   lin-addr
                                   (mv-nth 1 (page-directory-base-addr lin-addr x86-2)))
                                  x86-1))
                             (e2 (rm-low-64
                                  (page-directory-entry-addr
                                   lin-addr
                                   (mv-nth 1 (page-directory-base-addr lin-addr x86-2)))
                                  x86-2))
                             (m 7)
                             (n 52))
                  (:instance logtail-bigger-and-logbitp
                             (e1 (rm-low-64
                                  (page-directory-entry-addr
                                   lin-addr
                                   (mv-nth 1 (page-directory-base-addr lin-addr x86-2)))
                                  x86-1))
                             (e2 (rm-low-64
                                  (page-directory-entry-addr
                                   lin-addr
                                   (mv-nth 1 (page-directory-base-addr lin-addr x86-2)))
                                  x86-2))
                             (m 7)
                             (n 63)))))))

(local
 (defthmd ia32e-la-to-pa-PD-with-xlate-equiv-x86s-4K-pages
   ;; TO-DO: Speed this up.
   (implies (and (xlate-equiv-x86s x86-1 x86-2)
                 (not
                  (logbitp
                   7
                   (rm-low-64
                    (page-directory-entry-addr
                     lin-addr
                     (mv-nth 1 (page-directory-base-addr lin-addr x86-1)))
                    x86-1))))
            (and
             (equal (mv-nth
                     0
                     (ia32e-la-to-pa-PD
                      lin-addr wp smep nxe r-w-x cpl x86-1))
                    (mv-nth
                     0
                     (ia32e-la-to-pa-PD
                      lin-addr wp smep nxe r-w-x cpl x86-2)))
             (equal (mv-nth
                     1
                     (ia32e-la-to-pa-PD
                      lin-addr wp smep nxe r-w-x cpl x86-1))
                    (mv-nth
                     1
                     (ia32e-la-to-pa-PD
                      lin-addr wp smep nxe r-w-x cpl x86-2)))))
   :hints (("Goal"
            :in-theory (e/d* (ia32e-la-to-pa-page-directory
                              page-directory-entry-addr-found-p-and-lin-addr
                              page-fault-exception)
                             (xlate-equiv-x86s
                              xlate-equiv-x86s-and-page-table-entry-addr-address
                              page-table-entry-addr-found-p-and-xlate-equiv-x86s
                              ia32e-la-to-pa-PT-with-xlate-equiv-x86s
                              xlate-equiv-x86s-and-page-directory-entry-addr-value
                              xlate-equiv-x86s-and-page-directory-base-addr-address
                              xlate-equiv-x86s-and-page-directory-entry-addr-address
                              xlate-equiv-x86s-and-page-table-base-addr-address
                              page-directory-entry-addr-found-p-and-xlate-equiv-x86s
                              unsigned-byte-p
                              signed-byte-p
                              bitops::logand-with-negated-bitmask
                              bitops::logior-equal-0))
            :use ((:instance xlate-equiv-x86s-and-page-directory-entry-addr-value)
                  (:instance xlate-equiv-x86s-and-page-directory-base-addr-address)
                  (:instance page-directory-entry-addr-found-p-and-xlate-equiv-x86s)
                  (:instance page-directory-entry-addr-found-p-and-xlate-equiv-x86s
                             (x86-1 x86-2)
                             (x86-2 x86-1))
                  (:instance page-table-entry-addr-found-p-and-xlate-equiv-x86s)
                  ;; xlate-equiv-entries-and-loghead
                  (:instance xlate-equiv-entries-and-loghead
                             (e1 (rm-low-64
                                  (page-directory-entry-addr
                                   lin-addr
                                   (mv-nth 1 (page-directory-base-addr lin-addr x86-2)))
                                  x86-1))
                             (e2 (rm-low-64
                                  (page-directory-entry-addr
                                   lin-addr
                                   (mv-nth 1 (page-directory-base-addr lin-addr x86-2)))
                                  x86-2))
                             (n 1))
                  ;; xlate-equiv-entries-and-logtail
                  (:instance xlate-equiv-entries-and-logtail
                             (e1 (rm-low-64
                                  (page-directory-entry-addr
                                   lin-addr
                                   (mv-nth 1 (page-directory-base-addr lin-addr x86-2)))
                                  x86-1))
                             (e2 (rm-low-64
                                  (page-directory-entry-addr
                                   lin-addr
                                   (mv-nth 1 (page-directory-base-addr lin-addr x86-2)))
                                  x86-2))
                             (n 12))
                  (:instance xlate-equiv-entries-and-logtail
                             (e1 (rm-low-64
                                  (page-directory-entry-addr
                                   lin-addr
                                   (mv-nth 1 (page-directory-base-addr lin-addr x86-2)))
                                  x86-1))
                             (e2 (rm-low-64
                                  (page-directory-entry-addr
                                   lin-addr
                                   (mv-nth 1 (page-directory-base-addr lin-addr x86-2)))
                                  x86-2))
                             (n 13))
                  (:instance xlate-equiv-entries-and-logtail
                             (e1 (rm-low-64
                                  (page-directory-entry-addr
                                   lin-addr
                                   (mv-nth 1 (page-directory-base-addr lin-addr x86-2)))
                                  x86-1))
                             (e2 (rm-low-64
                                  (page-directory-entry-addr
                                   lin-addr
                                   (mv-nth 1 (page-directory-base-addr lin-addr x86-2)))
                                  x86-2))
                             (n 21))
                  (:instance xlate-equiv-entries-and-logtail
                             (e1 (rm-low-64
                                  (page-directory-entry-addr
                                   lin-addr
                                   (mv-nth 1 (page-directory-base-addr lin-addr x86-2)))
                                  x86-1))
                             (e2 (rm-low-64
                                  (page-directory-entry-addr
                                   lin-addr
                                   (mv-nth 1 (page-directory-base-addr lin-addr x86-2)))
                                  x86-2))
                             (n 52))
                  ;; loghead-smaller-and-logbitp
                  (:instance loghead-smaller-and-logbitp
                             (e1 (rm-low-64
                                  (page-directory-entry-addr
                                   lin-addr
                                   (mv-nth 1 (page-directory-base-addr lin-addr x86-2)))
                                  x86-1))
                             (e2 (rm-low-64
                                  (page-directory-entry-addr
                                   lin-addr
                                   (mv-nth 1 (page-directory-base-addr lin-addr x86-2)))
                                  x86-2))
                             (m 1)
                             (n 5))
                  (:instance loghead-smaller-and-logbitp
                             (e1 (rm-low-64
                                  (page-directory-entry-addr
                                   lin-addr
                                   (mv-nth 1 (page-directory-base-addr lin-addr x86-2)))
                                  x86-1))
                             (e2 (rm-low-64
                                  (page-directory-entry-addr
                                   lin-addr
                                   (mv-nth 1 (page-directory-base-addr lin-addr x86-2)))
                                  x86-2))
                             (m 2)
                             (n 5))
                  ;; logtail-bigger-and-logbitp
                  (:instance logtail-bigger-and-logbitp
                             (e1 (rm-low-64
                                  (page-directory-entry-addr
                                   lin-addr
                                   (mv-nth 1 (page-directory-base-addr lin-addr x86-2)))
                                  x86-1))
                             (e2 (rm-low-64
                                  (page-directory-entry-addr
                                   lin-addr
                                   (mv-nth 1 (page-directory-base-addr lin-addr x86-2)))
                                  x86-2))
                             (m 7)
                             (n 7))
                  (:instance logtail-bigger-and-logbitp
                             (e1 (rm-low-64
                                  (page-directory-entry-addr
                                   lin-addr
                                   (mv-nth 1 (page-directory-base-addr lin-addr x86-2)))
                                  x86-1))
                             (e2 (rm-low-64
                                  (page-directory-entry-addr
                                   lin-addr
                                   (mv-nth 1 (page-directory-base-addr lin-addr x86-2)))
                                  x86-2))
                             (m 7)
                             (n 52))
                  (:instance logtail-bigger-and-logbitp
                             (e1 (rm-low-64
                                  (page-directory-entry-addr
                                   lin-addr
                                   (mv-nth 1 (page-directory-base-addr lin-addr x86-2)))
                                  x86-1))
                             (e2 (rm-low-64
                                  (page-directory-entry-addr
                                   lin-addr
                                   (mv-nth 1 (page-directory-base-addr lin-addr x86-2)))
                                  x86-2))
                             (m 7)
                             (n 63)))))))

(defthm ia32e-la-to-pa-PD-with-xlate-equiv-x86s
  ;; TO-DO: Speed this up.
  (implies (xlate-equiv-x86s x86-1 x86-2)
           (and
            (equal (mv-nth
                    0
                    (ia32e-la-to-pa-PD
                     lin-addr wp smep nxe r-w-x cpl x86-1))
                   (mv-nth
                    0
                    (ia32e-la-to-pa-PD
                     lin-addr wp smep nxe r-w-x cpl x86-2)))
            (equal (mv-nth
                    1
                    (ia32e-la-to-pa-PD
                     lin-addr wp smep nxe r-w-x cpl x86-1))
                   (mv-nth
                    1
                    (ia32e-la-to-pa-PD
                     lin-addr wp smep nxe r-w-x cpl x86-2)))))
  :hints (("Goal"
           :use ((:instance ia32e-la-to-pa-PD-with-xlate-equiv-x86s-2M-pages)
                 (:instance ia32e-la-to-pa-PD-with-xlate-equiv-x86s-4K-pages))))
  :rule-classes :congruence)

(defrule xlate-equiv-x86s-with-mv-nth-2-ia32e-la-to-pa-PD
  (implies (and (page-directory-entry-addr-found-p lin-addr x86)
                (good-paging-structures-x86p x86))
           (xlate-equiv-x86s
            (mv-nth 2 (ia32e-la-to-pa-PD lin-addr wp smep nxe r-w-x cpl x86))
            x86))
  :in-theory (e/d* (ia32e-la-to-pa-page-directory
                    page-fault-exception
                    page-directory-entry-addr-found-p-and-lin-addr
                    good-paging-structures-x86p)
                   (bitops::logand-with-negated-bitmask
                    xlate-equiv-x86s-and-page-directory-entry-addr-address
                    xlate-equiv-x86s-and-page-directory-base-addr-address)))

(defrule two-page-directory-walks-ia32e-la-to-pa-page-directory
  (implies (and (page-directory-entry-addr-found-p lin-addr-1 x86)
                (page-directory-entry-addr-found-p lin-addr-2 x86)
                (good-paging-structures-x86p x86))
           (equal
            (mv-nth
             1
             (ia32e-la-to-pa-PD
              lin-addr-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
              (mv-nth
               2
               (ia32e-la-to-pa-PD
                lin-addr-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
            (mv-nth
             1
             (ia32e-la-to-pa-PD
              lin-addr-1 u-s-acc-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86))))
  :use ((:instance page-directory-entry-addr-found-p-after-a-page-walk)
        (:instance xlate-equiv-x86s-with-mv-nth-2-ia32e-la-to-pa-PD
                   (lin-addr lin-addr-2)
                   (wp wp-2)
                   (smep smep-2)
                   (nxe nxe-2)
                   (r-w-x r-w-x-2)
                   (cpl cpl-2)
                   (x86 x86))
        (:instance ia32e-la-to-pa-PD-with-xlate-equiv-x86s
                   (x86-1 (mv-nth 2
                                  (ia32e-la-to-pa-page-directory
                                   lin-addr-2
                                   (mv-nth 1 (page-directory-base-addr lin-addr-2 x86))
                                   u-s-acc-2
                                   wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)))
                   (x86-2 x86)
                   (lin-addr lin-addr-1)
                   (wp wp-1)
                   (smep smep-1)
                   (nxe nxe-1)
                   (r-w-x r-w-x-1)
                   (cpl cpl-1)))
  :in-theory (e/d ()
                  (page-directory-entry-addr-found-p-after-a-page-walk
                   xlate-equiv-x86s-with-mv-nth-2-ia32e-la-to-pa-PD
                   ia32e-la-to-pa-PD-with-xlate-equiv-x86s
                   xlate-equiv-x86s-and-page-directory-base-addr-address
                   unsigned-byte-p
                   signed-byte-p
                   member-p-cons
                   disjoint-p-cons)))

;; ======================================================================

;; (defthm page-directory-entry-addr-found-p-after-a-page-walk
;;   (implies (and (page-directory-entry-addr-found-p lin-addr-1 x86)
;;                 (page-directory-entry-addr-found-p lin-addr-2 x86)
;;                 (good-paging-structures-x86p x86))
;;            (page-directory-entry-addr-found-p
;;             lin-addr-1
;;             (mv-nth 2
;;                     (ia32e-la-to-pa-page-directory
;;                      lin-addr-2
;;                      (mv-nth 1 (page-directory-base-addr lin-addr-2 x86))
;;                      u-s-acc-2
;;                      wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
;;   :hints (("Goal"
;;            :use ((:instance logand-loghead-and-page-directory-base-addr
;;                             (lin-addr lin-addr-2))
;;                  (:instance page-directory-entry-addr-found-p-and-xlate-equiv-x86s
;;                             (x86-1 x86)
;;                             (lin-addr lin-addr-1)
;;                             (x86-2
;;                              (mv-nth 2
;;                                      (ia32e-la-to-pa-page-directory
;;                                       lin-addr-2
;;                                       (mv-nth 1 (page-directory-base-addr lin-addr-2 x86))
;;                                       u-s-acc-2
;;                                       wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
;;                  (:instance xlate-equiv-x86s-with-mv-nth-2-ia32e-la-to-pa-PT
;;                             (x86 x86)
;;                             (lin-addr lin-addr-2)
;;                             (u-s-acc u-s-acc-2)
;;                             (wp wp-2)
;;                             (smep smep-2)
;;                             (nxe nxe-2)
;;                             (r-w-x r-w-x-2)
;;                             (cpl cpl-2)))
;;            :in-theory (e/d* ()
;;                             (physical-address-p
;;                              page-directory-entry-addr-found-p-and-xlate-equiv-x86s
;;                              xlate-equiv-x86s-with-mv-nth-2-ia32e-la-to-pa-PT
;;                              xlate-equiv-x86s-and-page-dir-ptr-table-base-addr-address
;;                              xlate-equiv-x86s-and-page-dir-ptr-table-entry-addr-address
;;                              xlate-equiv-x86s-and-page-table-base-addr-address
;;                              xlate-equiv-x86s-and-page-table-base-addr-error
;;                              xlate-equiv-x86s-and-page-table-entry-addr-address
;;                              xlate-equiv-x86s-and-page-directory-base-addr-address
;;                              xlate-equiv-x86s-and-page-directory-entry-addr-address
;;                              bitops::logand-with-negated-bitmask)))))
