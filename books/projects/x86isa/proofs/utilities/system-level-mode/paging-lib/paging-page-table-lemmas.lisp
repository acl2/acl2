;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")
(include-book "gather-paging-structures-thms" :ttags :all)

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "centaur/bitops/signed-byte-p" :dir :system))
(local (include-book "centaur/gl/gl" :dir :system))

;; ======================================================================

(local
 (def-gl-thm logand-loghead-and-page-table-base-addr-helper
   :hyp (unsigned-byte-p 64 x)
   :concl (equal (logand 18446744073709547520 (ash (loghead 40 (logtail 12 x)) 12))
                 (ash (loghead 40 (logtail 12 x)) 12))
   :g-bindings `((x (:g-number ,(gl-int 0 1 65))))))

(defthmd ia32e-la-to-pa-PT-with-xlate-equiv-x86s
  ;; TO-DO: Speed this up.
  (implies (xlate-equiv-x86s x86-1 x86-2)
           (and
            (equal (mv-nth
                    0
                    (ia32e-la-to-pa-PT
                     lin-addr u-s-acc wp smep nxe r-w-x cpl x86-1))
                   (mv-nth
                    0
                    (ia32e-la-to-pa-PT
                     lin-addr u-s-acc wp smep nxe r-w-x cpl x86-2)))
            (equal (mv-nth
                    1
                    (ia32e-la-to-pa-PT
                     lin-addr u-s-acc wp smep nxe r-w-x cpl x86-1))
                   (mv-nth
                    1
                    (ia32e-la-to-pa-PT
                     lin-addr u-s-acc wp smep nxe r-w-x cpl x86-2)))))
  :hints (("Goal"
           :in-theory (e/d* (ia32e-la-to-pa-PT
                             ia32e-la-to-pa-page-table
                             entry-found-p-and-lin-addr
                             PAGE-TABLE-ENTRY-NO-PAGE-FAULT-P
                             page-fault-exception)
                            (xlate-equiv-x86s
                             xlate-equiv-x86s-and-page-table-entry-addr-value
                             xlate-equiv-x86s-and-page-table-base-addr-address
                             xlate-equiv-x86s-and-page-table-entry-addr-address
                             page-table-entry-addr-found-p-and-xlate-equiv-x86s
                             bitops::logand-with-negated-bitmask
                             bitops::logior-equal-0))
           :use ((:instance xlate-equiv-x86s-and-page-table-entry-addr-value)
                 (:instance page-table-entry-addr-found-p-and-xlate-equiv-x86s
                            (x86-1 x86-1)
                            (x86-2 x86-2))
                 (:instance page-table-entry-addr-found-p-and-xlate-equiv-x86s
                            (x86-1 x86-2)
                            (x86-2 x86-1))
                 (:instance xlate-equiv-x86s-and-page-table-base-addr-address)
                 ;; xlate-equiv-entries-and-loghead
                 (:instance xlate-equiv-entries-and-loghead
                            (e1 (rm-low-64
                                 (page-table-entry-addr
                                  lin-addr
                                  (mv-nth 1 (page-table-base-addr lin-addr x86-2)))
                                 x86-1))
                            (e2 (rm-low-64
                                 (page-table-entry-addr
                                  lin-addr
                                  (mv-nth 1 (page-table-base-addr lin-addr x86-2)))
                                 x86-2))
                            (n 1))
                 ;; xlate-equiv-entries-and-logtail
                 (:instance xlate-equiv-entries-and-logtail
                            (e1 (rm-low-64
                                 (page-table-entry-addr
                                  lin-addr
                                  (mv-nth 1 (page-table-base-addr lin-addr x86-2)))
                                 x86-1))
                            (e2 (rm-low-64
                                 (page-table-entry-addr
                                  lin-addr
                                  (mv-nth 1 (page-table-base-addr lin-addr x86-2)))
                                 x86-2))
                            (n 12))
                 (:instance xlate-equiv-entries-and-logtail
                            (e1 (rm-low-64
                                 (page-table-entry-addr
                                  lin-addr
                                  (mv-nth 1 (page-table-base-addr lin-addr x86-2)))
                                 x86-1))
                            (e2 (rm-low-64
                                 (page-table-entry-addr
                                  lin-addr
                                  (mv-nth 1 (page-table-base-addr lin-addr x86-2)))
                                 x86-2))
                            (n 52))
                 ;; loghead-smaller-and-logbitp
                 (:instance loghead-smaller-and-logbitp
                            (e1 (rm-low-64
                                 (page-table-entry-addr
                                  lin-addr
                                  (mv-nth 1 (page-table-base-addr lin-addr x86-2)))
                                 x86-1))
                            (e2 (rm-low-64
                                 (page-table-entry-addr
                                  lin-addr
                                  (mv-nth 1 (page-table-base-addr lin-addr x86-2)))
                                 x86-2))
                            (m 1)
                            (n 5))
                 (:instance loghead-smaller-and-logbitp
                            (e1 (rm-low-64
                                 (page-table-entry-addr
                                  lin-addr
                                  (mv-nth 1 (page-table-base-addr lin-addr x86-2)))
                                 x86-1))
                            (e2 (rm-low-64
                                 (page-table-entry-addr
                                  lin-addr
                                  (mv-nth 1 (page-table-base-addr lin-addr x86-2)))
                                 x86-2))
                            (m 2)
                            (n 5))
                 ;; logtail-bigger-and-logbitp
                 (:instance logtail-bigger-and-logbitp
                            (e1 (rm-low-64
                                 (page-table-entry-addr
                                  lin-addr
                                  (mv-nth 1 (page-table-base-addr lin-addr x86-2)))
                                 x86-1))
                            (e2 (rm-low-64
                                 (page-table-entry-addr
                                  lin-addr
                                  (mv-nth 1 (page-table-base-addr lin-addr x86-2)))
                                 x86-2))
                            (m 7)
                            (n 52))
                 (:instance logtail-bigger-and-logbitp
                            (e1 (rm-low-64
                                 (page-table-entry-addr
                                  lin-addr
                                  (mv-nth 1 (page-table-base-addr lin-addr x86-2)))
                                 x86-1))
                            (e2 (rm-low-64
                                 (page-table-entry-addr
                                  lin-addr
                                  (mv-nth 1 (page-table-base-addr lin-addr x86-2)))
                                 x86-2))
                            (m 7)
                            (n 63))))))

(defthm mv-nth-0-ia32e-la-to-pa-PT-with-xlate-equiv-x86s
  (implies (xlate-equiv-x86s x86-1 x86-2)
           (equal (mv-nth
                   0
                   (ia32e-la-to-pa-PT
                    lin-addr u-s-acc wp smep nxe r-w-x cpl x86-1))
                  (mv-nth
                   0
                   (ia32e-la-to-pa-PT
                    lin-addr u-s-acc wp smep nxe r-w-x cpl x86-2))))
  :hints (("Goal" :use ((:instance ia32e-la-to-pa-PT-with-xlate-equiv-x86s))))
  :rule-classes :congruence)

(defthm mv-nth-1-ia32e-la-to-pa-PT-with-xlate-equiv-x86s
  (implies (xlate-equiv-x86s x86-1 x86-2)
           (equal (mv-nth
                   1
                   (ia32e-la-to-pa-PT
                    lin-addr u-s-acc wp smep nxe r-w-x cpl x86-1))
                  (mv-nth
                   1
                   (ia32e-la-to-pa-PT
                    lin-addr u-s-acc wp smep nxe r-w-x cpl x86-2))))
  :hints (("Goal" :use ((:instance ia32e-la-to-pa-PT-with-xlate-equiv-x86s))))
  :rule-classes :congruence)

(local
 (defthm page-table-entry-addr-found-p-and-mult-8-qword-paddr-list-listp
   (implies (page-table-entry-addr-found-p lin-addr x86)
            (mult-8-qword-paddr-list-listp (gather-all-paging-structure-qword-addresses x86)))
   :hints (("goal"
            :in-theory (e/d* (good-paging-structures-x86p)
                             (page-table-entry-addr-found-p-implies-good-paging-structures-x86p))
            :use ((:instance page-table-entry-addr-found-p-implies-good-paging-structures-x86p))))))

(local
 (defthm page-table-entry-addr-found-p-and-no-duplicates-list-listp
   (implies (page-table-entry-addr-found-p lin-addr x86)
            (no-duplicates-list-p (gather-all-paging-structure-qword-addresses x86)))
   :hints (("Goal"
            :in-theory (e/d* (good-paging-structures-x86p)
                             (page-table-entry-addr-found-p-implies-good-paging-structures-x86p))
            :use ((:instance page-table-entry-addr-found-p-implies-good-paging-structures-x86p))))))

(defthm xlate-equiv-x86s-with-mv-nth-2-ia32e-la-to-pa-PT
  (xlate-equiv-x86s
   (mv-nth 2 (ia32e-la-to-pa-PT lin-addr u-s-acc wp smep nxe r-w-x cpl x86))
   x86)
  :hints (("Goal"
           :in-theory (e/d* (ia32e-la-to-pa-page-table
                             PAGE-TABLE-ENTRY-NO-PAGE-FAULT-P
                             page-fault-exception
                             entry-found-p-and-lin-addr
                             good-paging-structures-x86p)
                            (bitops::logand-with-negated-bitmask
                             xlate-equiv-x86s-and-page-table-entry-addr-address
                             xlate-equiv-x86s-and-page-table-base-addr-address
                             no-duplicates-list-p)))))

(defthm two-page-table-walks-ia32e-la-to-pa-PT
  (and

   (equal
    (mv-nth
     0
     (ia32e-la-to-pa-PT
      lin-addr-1 u-s-acc-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
      (mv-nth
       2
       (ia32e-la-to-pa-PT
        lin-addr-2 u-s-acc-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
    (mv-nth
     0
     (ia32e-la-to-pa-PT
      lin-addr-1 u-s-acc-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)))

   (equal
    (mv-nth
     1
     (ia32e-la-to-pa-PT
      lin-addr-1 u-s-acc-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
      (mv-nth
       2
       (ia32e-la-to-pa-PT
        lin-addr-2 u-s-acc-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
    (mv-nth
     1
     (ia32e-la-to-pa-PT
      lin-addr-1 u-s-acc-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86))))

  :hints (("Goal" :in-theory (e/d* () (ia32e-la-to-pa-PT)))))

(in-theory (e/d* () (ia32e-la-to-pa-PT)))

;; ======================================================================

;; Now rewriting page-table to PT so that all we see while reasoning,
;; when page-table-entry-addr-found-p is true, is the PT function and
;; not the page-table function:

;; (defthm ia32e-la-to-pa-page-table-in-terms-of-ia32e-la-to-pa-PT
;;   (implies (and (page-table-entry-addr-found-p lin-addr x86)
;;                 (equal base-addr (mv-nth 1 (page-table-base-addr lin-addr x86))))
;;            (and
;;             (equal (mv-nth
;;                     0
;;                     (ia32e-la-to-pa-page-table lin-addr base-addr u-s-acc wp smep nxe r-w-x cpl x86))
;;                    (mv-nth
;;                     0
;;                     (ia32e-la-to-pa-PT lin-addr u-s-acc wp smep nxe r-w-x cpl x86)))
;;             (equal (mv-nth
;;                     1
;;                     (ia32e-la-to-pa-page-table lin-addr base-addr u-s-acc wp smep nxe r-w-x cpl x86))
;;                    (mv-nth
;;                     1
;;                     (ia32e-la-to-pa-PT lin-addr u-s-acc wp smep nxe r-w-x cpl x86))))))


;; (defthm page-table-entry-addr-found-p-after-a-page-walk
;;   (implies (and (page-table-entry-addr-found-p lin-addr-1 x86)
;;                 (page-table-entry-addr-found-p lin-addr-2 x86)
;;                 (good-paging-structures-x86p x86))
;;            (page-table-entry-addr-found-p
;;             lin-addr-1
;;             (mv-nth 2
;;                     (ia32e-la-to-pa-page-table
;;                      lin-addr-2
;;                      (mv-nth 1 (page-table-base-addr lin-addr-2 x86))
;;                      u-s-acc-2
;;                      wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
;;   :hints (("Goal"
;;            :use ((:instance logand-loghead-and-page-table-base-addr
;;                             (lin-addr lin-addr-2))
;;                  (:instance page-table-entry-addr-found-p-and-xlate-equiv-x86s
;;                             (x86-1 x86)
;;                             (lin-addr lin-addr-1)
;;                             (x86-2
;;                              (mv-nth 2
;;                                      (ia32e-la-to-pa-page-table
;;                                       lin-addr-2
;;                                       (mv-nth 1 (page-table-base-addr lin-addr-2 x86))
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
;;                              page-table-entry-addr-found-p-and-xlate-equiv-x86s
;;                              xlate-equiv-x86s-with-mv-nth-2-ia32e-la-to-pa-PT
;;                              xlate-equiv-x86s-and-page-dir-ptr-table-base-addr-address
;;                              xlate-equiv-x86s-and-page-dir-ptr-table-entry-addr-address
;;                              xlate-equiv-x86s-and-page-directory-base-addr-address
;;                              xlate-equiv-x86s-and-page-directory-base-addr-error
;;                              xlate-equiv-x86s-and-page-directory-entry-addr-address
;;                              xlate-equiv-x86s-and-page-table-base-addr-address
;;                              xlate-equiv-x86s-and-page-table-entry-addr-address
;;                              bitops::logand-with-negated-bitmask)))))
