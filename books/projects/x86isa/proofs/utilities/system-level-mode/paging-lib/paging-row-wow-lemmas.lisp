;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

;; WORK IN PROGRESS (Thursday, December 10 2015)

;; This book will be folded into books under paging-top. For now, this
;; is a "hanging" book --- not included by anything else.

(in-package "X86ISA")
(include-book "paging-top" :ttags :all)

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "centaur/bitops/signed-byte-p" :dir :system))

(local (in-theory (e/d (entry-found-p-and-lin-addr
                        entry-found-p-and-good-paging-structures-x86p)
                       (signed-byte-p
                        unsigned-byte-p))))

;; ======================================================================

(defthm page-table-entry-no-page-fault-p-and-wm-low-64-with-same-entries
  (equal
   (mv-nth
    0
    (page-table-entry-no-page-fault-p
     lin-addr
     entry
     u-s-acc
     wp smep nxe r-w-x cpl
     (wm-low-64 index val x86)))
   (mv-nth
    0
    (page-table-entry-no-page-fault-p
     lin-addr
     entry
     u-s-acc wp smep nxe r-w-x cpl x86)))
  :hints (("Goal" :in-theory (e/d* (page-table-entry-no-page-fault-p
                                    page-fault-exception)
                                   ()))))

(defun remove-set-accessed-and-dirty-bits (e-1)
  ;; Find an xlate-equiv entry (e-2) for e-1 by peeling away
  ;; occurrences of set-accessed-bit and set-dirty-bit from e-1.
  (if (or (equal (first e-1) 'set-accessed-bit)
          (equal (first e-1) 'set-dirty-bit))
      (remove-set-accessed-and-dirty-bits (second e-1))
    e-1))

(defun find-xlate-equiv-entry (e-1)
  `((e-2 . ,(remove-set-accessed-and-dirty-bits e-1))))

(defthm page-table-entry-no-page-fault-p-and-wm-low-64-with-xlate-equiv-entries
  (implies (and
            (syntaxp (and (consp e-1)
                          (or (eq (car e-1) 'set-accessed-bit)
                              (eq (car e-1) 'set-dirty-bit))))
            (bind-free (find-xlate-equiv-entry e-1) (e-2))
            (xlate-equiv-entries e-1 e-2)
            (unsigned-byte-p 64 e-1)
            (unsigned-byte-p 64 e-2))
           (equal
            (mv-nth
             0
             (page-table-entry-no-page-fault-p
              lin-addr e-1 u-s-acc wp smep nxe r-w-x cpl x86))
            (mv-nth
             0
             (page-table-entry-no-page-fault-p
              lin-addr e-2 u-s-acc wp smep nxe r-w-x cpl x86))))
  :hints (("Goal" :in-theory (e/d* (page-table-entry-no-page-fault-p
                                    page-fault-exception)
                                   ())
           :use ((:instance xlate-equiv-entries-and-page-present
                            (e1 e-1)
                            (e2 e-2))
                 (:instance xlate-equiv-entries-and-page-size
                            (e1 e-1)
                            (e2 e-2))
                 (:instance xlate-equiv-entries-and-page-execute-disable
                            (e1 e-1)
                            (e2 e-2))
                 (:instance xlate-equiv-entries-and-page-read-write
                            (e1 e-1)
                            (e2 e-2))
                 (:instance xlate-equiv-entries-and-page-user-supervisor
                            (e1 e-1)
                            (e2 e-2))
                 (:instance xlate-equiv-entries-and-logtail
                            (e1 e-1)
                            (e2 e-2)
                            (n 52))))))

(defthm mv-nth-2-page-table-entry-no-page-fault-p-with-wm-low-64
  (implies (not (mv-nth
                 0
                 (page-table-entry-no-page-fault-p
                  lin-addr entry u-s-acc wp smep nxe r-w-x cpl x86)))
           (equal (mv-nth
                   2
                   (page-table-entry-no-page-fault-p
                    lin-addr
                    entry
                    u-s-acc
                    wp smep nxe r-w-x cpl
                    (wm-low-64 index val x86)))
                  (wm-low-64 index val x86)))
  :hints (("Goal" :in-theory (e/d* (page-table-entry-no-page-fault-p)
                                   ()))))

(defthm ia32e-la-to-pa-PT-state-WoW-no-page-fault
  (implies (and (page-table-entry-addr-found-p lin-addr-1 x86)
                (page-table-entry-addr-found-p lin-addr-2 x86)
                (not
                 (mv-nth 0
                         (page-table-entry-no-page-fault-p
                          lin-addr-1
                          (rm-low-64
                           (page-table-entry-addr
                            lin-addr-1
                            (mv-nth 1 (page-table-base-addr lin-addr-1 x86)))
                           x86)
                          u-s-acc-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)))
                (not
                 (mv-nth
                  0
                  (page-table-entry-no-page-fault-p
                   lin-addr-2
                   (rm-low-64
                    (page-table-entry-addr
                     lin-addr-2
                     (mv-nth 1 (page-table-base-addr lin-addr-2 x86)))
                    x86)
                   u-s-acc-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
           (equal
            (mv-nth
             2
             (ia32e-la-to-pa-PT
              lin-addr-1 u-s-acc-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
              (mv-nth
               2
               (ia32e-la-to-pa-PT
                lin-addr-2 u-s-acc-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
            (mv-nth
             2
             (ia32e-la-to-pa-PT
              lin-addr-2 u-s-acc-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2
              (mv-nth
               2
               (ia32e-la-to-pa-PT
                lin-addr-1 u-s-acc-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86))))))
  :hints (("Goal"
           :cases ((equal
                    (page-table-entry-addr
                     lin-addr-1
                     (mv-nth 1 (page-table-base-addr lin-addr-1 x86)))
                    (page-table-entry-addr
                     lin-addr-2
                     (mv-nth 1 (page-table-base-addr lin-addr-2 x86)))))
           :in-theory (e/d* (ia32e-la-to-pa-PT
                             ia32e-la-to-pa-page-table)
                            (bitops::logand-with-negated-bitmask
                             accessed-bit
                             dirty-bit
                             bitops::logior-equal-0)))))

;; ----------------------------------------------------------------------

(defthm paging-entry-no-page-fault-p-and-wm-low-64-with-same-entries
  (equal
   (mv-nth
    0
    (paging-entry-no-page-fault-p
     lin-addr
     entry
     wp smep nxe r-w-x cpl
     (wm-low-64 index val x86)))
   (mv-nth
    0
    (paging-entry-no-page-fault-p
     lin-addr
     entry
     wp smep nxe r-w-x cpl x86)))
  :hints (("Goal" :in-theory (e/d* (paging-entry-no-page-fault-p
                                    page-fault-exception)
                                   ()))))

(defthm paging-entry-no-page-fault-p-and-wm-low-64-with-xlate-equiv-entries
  (implies (and
            (syntaxp (and (consp e-1)
                          (or (eq (car e-1) 'set-accessed-bit)
                              (eq (car e-1) 'set-dirty-bit))))
            (bind-free (find-xlate-equiv-entry e-1) (e-2))
            (xlate-equiv-entries e-1 e-2)
            (unsigned-byte-p 64 e-1)
            (unsigned-byte-p 64 e-2))
           (equal
            (mv-nth
             0
             (paging-entry-no-page-fault-p
              lin-addr e-1 wp smep nxe r-w-x cpl x86))
            (mv-nth
             0
             (paging-entry-no-page-fault-p
              lin-addr e-2 wp smep nxe r-w-x cpl x86))))
  :hints (("Goal" :in-theory (e/d* (paging-entry-no-page-fault-p
                                    page-fault-exception)
                                   ())
           :use ((:instance xlate-equiv-entries-and-page-present
                            (e1 e-1)
                            (e2 e-2))
                 (:instance xlate-equiv-entries-and-page-size
                            (e1 e-1)
                            (e2 e-2))
                 (:instance xlate-equiv-entries-and-page-execute-disable
                            (e1 e-1)
                            (e2 e-2))
                 (:instance xlate-equiv-entries-and-page-read-write
                            (e1 e-1)
                            (e2 e-2))
                 (:instance xlate-equiv-entries-and-page-user-supervisor
                            (e1 e-1)
                            (e2 e-2))
                 (:instance xlate-equiv-entries-and-logtail
                            (e1 e-1)
                            (e2 e-2)
                            (n 52))
                 (:instance xlate-equiv-entries-and-logtail
                            (e1 e-1)
                            (e2 e-2)
                            (n 13))))))

(defthm mv-nth-2-paging-entry-no-page-fault-p-with-wm-low-64
  (implies (not (mv-nth
                 0
                 (paging-entry-no-page-fault-p
                  lin-addr entry wp smep nxe r-w-x cpl x86)))
           (equal (mv-nth
                   2
                   (paging-entry-no-page-fault-p
                    lin-addr
                    entry
                    wp smep nxe r-w-x cpl
                    (wm-low-64 index val x86)))
                  (wm-low-64 index val x86)))
  :hints (("Goal" :in-theory (e/d* (paging-entry-no-page-fault-p)
                                   ()))))

(local
 (defthm ia32e-la-to-pa-PD-state-WoW-no-page-fault-both-2M-pages
   (implies (and
             (equal (page-size (rm-low-64
                                (page-directory-entry-addr
                                 lin-addr-1
                                 (mv-nth 1 (page-directory-base-addr lin-addr-1 x86)))
                                x86))
                    1)
             (equal (page-size (rm-low-64
                                (page-directory-entry-addr
                                 lin-addr-2
                                 (mv-nth 1 (page-directory-base-addr lin-addr-2 x86)))
                                x86))
                    1)
             (page-directory-entry-addr-found-p lin-addr-1 x86)
             (page-directory-entry-addr-found-p lin-addr-2 x86)
             (not
              (mv-nth 0
                      (paging-entry-no-page-fault-p
                       lin-addr-1
                       (rm-low-64
                        (page-directory-entry-addr
                         lin-addr-1
                         (mv-nth 1 (page-directory-base-addr lin-addr-1 x86)))
                        x86)
                       wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)))
             (not
              (mv-nth
               0
               (paging-entry-no-page-fault-p
                lin-addr-2
                (rm-low-64
                 (page-directory-entry-addr
                  lin-addr-2
                  (mv-nth 1 (page-directory-base-addr lin-addr-2 x86)))
                 x86)
                wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
            (equal
             (mv-nth
              2
              (ia32e-la-to-pa-PD
               lin-addr-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
               (mv-nth
                2
                (ia32e-la-to-pa-PD
                 lin-addr-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
             (mv-nth
              2
              (ia32e-la-to-pa-PD
               lin-addr-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2
               (mv-nth
                2
                (ia32e-la-to-pa-PD
                 lin-addr-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86))))))
   :hints (("Goal"
            :cases ((equal
                     (page-directory-entry-addr
                      lin-addr-1
                      (mv-nth 1 (page-directory-base-addr lin-addr-1 x86)))
                     (page-directory-entry-addr
                      lin-addr-2
                      (mv-nth 1 (page-directory-base-addr lin-addr-2 x86)))))
            :in-theory (e/d* (ia32e-la-to-pa-PD
                              ia32e-la-to-pa-page-directory)
                             (bitops::logand-with-negated-bitmask
                              accessed-bit
                              dirty-bit
                              bitops::logior-equal-0))))))

#||

(i-am-here)

;; Need RoW of PAGE-DIRECTORY-BASE-ADDR and IA32E-LA-TO-PA-PT.

(defthm ia32e-la-to-pa-PD-state-WoW-no-page-fault
  (implies (and
            (page-directory-entry-addr-found-p lin-addr-1 x86)
            (page-directory-entry-addr-found-p lin-addr-2 x86)
            (not
             (mv-nth 0
                     (paging-entry-no-page-fault-p
                      lin-addr-1
                      (rm-low-64
                       (page-directory-entry-addr
                        lin-addr-1
                        (mv-nth 1 (page-directory-base-addr lin-addr-1 x86)))
                       x86)
                      wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)))
            (not
             (mv-nth
              0
              (paging-entry-no-page-fault-p
               lin-addr-2
               (rm-low-64
                (page-directory-entry-addr
                 lin-addr-2
                 (mv-nth 1 (page-directory-base-addr lin-addr-2 x86)))
                x86)
               wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)))
            (equal u-s-acc-1
                   (page-user-supervisor
                    (rm-low-64
                     (page-directory-entry-addr
                      lin-addr-1
                      (mv-nth 1 (page-directory-base-addr lin-addr-1 x86)))
                     x86)))
            (equal u-s-acc-2
                   (page-user-supervisor
                    (rm-low-64
                     (page-directory-entry-addr
                      lin-addr-2
                      (mv-nth 1 (page-directory-base-addr lin-addr-2 x86)))
                     x86)))
            (page-table-entry-addr-found-p lin-addr-1 x86)
            (page-table-entry-addr-found-p lin-addr-2 x86)
            (not
             (mv-nth 0
                     (page-table-entry-no-page-fault-p
                      lin-addr-1
                      (rm-low-64
                       (page-table-entry-addr
                        lin-addr-1
                        (mv-nth 1 (page-table-base-addr lin-addr-1 x86)))
                       x86)
                      u-s-acc-1
                      wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)))
            (not
             (mv-nth
              0
              (page-table-entry-no-page-fault-p
               lin-addr-2
               (rm-low-64
                (page-table-entry-addr
                 lin-addr-2
                 (mv-nth 1 (page-table-base-addr lin-addr-2 x86)))
                x86)
               u-s-acc-2
               wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
           (equal
            (mv-nth
             2
             (ia32e-la-to-pa-PD
              lin-addr-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
              (mv-nth
               2
               (ia32e-la-to-pa-PD
                lin-addr-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
            (mv-nth
             2
             (ia32e-la-to-pa-PD
              lin-addr-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2
              (mv-nth
               2
               (ia32e-la-to-pa-PD
                lin-addr-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86))))))
  :hints (("Goal"
           :cases ((equal
                    (page-directory-entry-addr
                     lin-addr-1
                     (mv-nth 1 (page-directory-base-addr lin-addr-1 x86)))
                    (page-directory-entry-addr
                     lin-addr-2
                     (mv-nth 1 (page-directory-base-addr lin-addr-2 x86)))))
           :in-theory (e/d* (ia32e-la-to-pa-PD
                             ia32e-la-to-pa-page-directory)
                            (bitops::logand-with-negated-bitmask
                             accessed-bit
                             dirty-bit
                             bitops::logior-equal-0)))))

;; ----------------------------------------------------------------------

(defthm ia32e-la-to-pa-PDPT-state-WoW-no-page-fault
  (implies (and (page-dir-ptr-table-entry-addr-found-p lin-addr-1 x86)
                (page-dir-ptr-table-entry-addr-found-p lin-addr-2 x86)
                (not
                 (mv-nth 0
                         (paging-entry-no-page-fault-p
                          lin-addr-1
                          (rm-low-64
                           (page-dir-ptr-table-entry-addr
                            lin-addr-1
                            (mv-nth 1 (page-dir-ptr-table-base-addr lin-addr-1 x86)))
                           x86)
                          wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)))
                (not
                 (mv-nth
                  0
                  (paging-entry-no-page-fault-p
                   lin-addr-2
                   (rm-low-64
                    (page-dir-ptr-table-entry-addr
                     lin-addr-2
                     (mv-nth 1 (page-dir-ptr-table-base-addr lin-addr-2 x86)))
                    x86)
                   wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
           (equal
            (mv-nth
             2
             (ia32e-la-to-pa-PDPT
              lin-addr-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
              (mv-nth
               2
               (ia32e-la-to-pa-PDPT
                lin-addr-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
            (mv-nth
             2
             (ia32e-la-to-pa-PDPT
              lin-addr-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2
              (mv-nth
               2
               (ia32e-la-to-pa-PDPT
                lin-addr-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86))))))
  :hints (("Goal"
           :cases ((equal
                    (page-dir-ptr-table-entry-addr
                     lin-addr-1
                     (mv-nth 1 (page-dir-ptr-table-base-addr lin-addr-1 x86)))
                    (page-dir-ptr-table-entry-addr
                     lin-addr-2
                     (mv-nth 1 (page-dir-ptr-table-base-addr lin-addr-2 x86)))))
           :in-theory (e/d* (ia32e-la-to-pa-PDPT
                             ia32e-la-to-pa-page-dir-ptr-table)
                            (bitops::logand-with-negated-bitmask
                             accessed-bit
                             dirty-bit
                             bitops::logior-equal-0)))))

(defthm ia32e-la-to-pa-PML4T-state-WoW-no-page-fault
  (implies (and (pml4-table-entry-addr-found-p lin-addr-1 x86)
                (pml4-table-entry-addr-found-p lin-addr-2 x86)
                (not
                 (mv-nth 0
                         (paging-entry-no-page-fault-p
                          lin-addr-1
                          (rm-low-64
                           (pml4-table-entry-addr
                            lin-addr-1
                            (mv-nth 1 (pml4-table-base-addr lin-addr-1 x86)))
                           x86)
                          wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)))
                (not
                 (mv-nth
                  0
                  (paging-entry-no-page-fault-p
                   lin-addr-2
                   (rm-low-64
                    (pml4-table-entry-addr
                     lin-addr-2
                     (mv-nth 1 (pml4-table-base-addr lin-addr-2 x86)))
                    x86)
                   wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
           (equal
            (mv-nth
             2
             (ia32e-la-to-pa-PML4T
              lin-addr-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
              (mv-nth
               2
               (ia32e-la-to-pa-PML4T
                lin-addr-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
            (mv-nth
             2
             (ia32e-la-to-pa-PML4T
              lin-addr-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2
              (mv-nth
               2
               (ia32e-la-to-pa-PML4T
                lin-addr-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86))))))
  :hints (("Goal"
           :cases ((equal
                    (pml4-table-entry-addr
                     lin-addr-1
                     (mv-nth 1 (pml4-table-base-addr lin-addr-1 x86)))
                    (pml4-table-entry-addr
                     lin-addr-2
                     (mv-nth 1 (pml4-table-base-addr lin-addr-2 x86)))))
           :in-theory (e/d* (ia32e-la-to-pa-PML4T
                             ia32e-la-to-pa-pml4-table)
                            (bitops::logand-with-negated-bitmask
                             accessed-bit
                             dirty-bit
                             bitops::logior-equal-0)))))


(defthm ia32e-entries-found-la-to-pa-WoW-no-page-fault
  (implies
   (and
    (paging-entries-found-p lin-addr-1 x86)
    (paging-entries-found-p lin-addr-2 x86)
    (not (mv-nth 0 (ia32e-entries-found-la-to-pa lin-addr-1 r-w-x-1 cpl-1 x86)))
    (not (mv-nth 0 (ia32e-entries-found-la-to-pa lin-addr-2 r-w-x-2 cpl-2 x86))))
   (equal
    (mv-nth
     2
     (ia32e-entries-found-la-to-pa
      lin-addr-1 r-w-x-1 cpl-1
      (mv-nth 2 (ia32e-entries-found-la-to-pa lin-addr-2 r-w-x-2 cpl-2 x86))))
    (mv-nth
     2
     (ia32e-entries-found-la-to-pa
      lin-addr-2 r-w-x-2 cpl-2
      (mv-nth 2 (ia32e-entries-found-la-to-pa lin-addr-1 r-w-x-1 cpl-1 x86)))))))

||#

;; ======================================================================
