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

(defthm mv-nth-2-page-table-entry-no-page-fault-p-value
  (implies (not (mv-nth
                 0
                 (page-table-entry-no-page-fault-p
                  lin-addr entry u-s-acc wp smep nxe r-w-x cpl x86)))
           (equal (mv-nth
                   2
                   (page-table-entry-no-page-fault-p
                    lin-addr entry u-s-acc wp smep nxe r-w-x cpl x86))
                  x86))
  :hints (("Goal" :in-theory (e/d* (page-table-entry-no-page-fault-p)
                                   ()))))

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

(defthm page-table-entry-no-page-fault-p-with-xlate-equiv-entries
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

(defthm mv-nth-2-paging-entry-no-page-fault-p-value
  (implies (not (mv-nth
                 0
                 (paging-entry-no-page-fault-p
                  lin-addr entry wp smep nxe r-w-x cpl x86)))
           (equal (mv-nth
                   2
                   (paging-entry-no-page-fault-p
                    lin-addr entry wp smep nxe r-w-x cpl x86))
                  x86))
  :hints (("Goal" :in-theory (e/d* (paging-entry-no-page-fault-p)
                                   ()))))

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

(defthm paging-entry-no-page-fault-p-with-xlate-equiv-entries
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

(defthmd paging-entry-no-page-fault-p-with-xlate-equiv-entries-and-x86s
  ;; This theorem is intended to be used in a :use hint.
  (implies (and (xlate-equiv-x86s x86-1 x86-2)
                (xlate-equiv-entries e-1 e-2)
                (unsigned-byte-p 64 e-1)
                (unsigned-byte-p 64 e-2))
           (equal
            (mv-nth
             0
             (paging-entry-no-page-fault-p
              lin-addr e-1 wp smep nxe r-w-x cpl x86-1))
            (mv-nth
             0
             (paging-entry-no-page-fault-p
              lin-addr e-2 wp smep nxe r-w-x cpl x86-2))))
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

;; (i-am-here)

;; See help.lisp. I think I need *found-p and xlate-equiv-x86s rules.

(defthm no-error-from-ia32e-la-to-pa-PT-if-no-error-from-page-table-entry-no-page-fault-p
  (implies (and (not (mv-nth 0
                             (page-table-entry-no-page-fault-p
                              lin-addr
                              (rm-low-64
                               (page-table-entry-addr
                                lin-addr
                                (mv-nth 1 (page-table-base-addr lin-addr x86)))
                               x86)
                              u-s-acc wp smep nxe r-w-x cpl x86)))
                (page-table-entry-addr-found-p lin-addr x86))
           (equal (mv-nth 0 (ia32e-la-to-pa-PT lin-addr u-s-acc wp smep nxe r-w-x cpl x86))
                  nil))
  :hints (("Goal" :in-theory (e/d* (ia32e-la-to-pa-PT
                                    ia32e-la-to-pa-page-table)
                                   (bitops::logand-with-negated-bitmask)))))

;; (defthm ia32e-la-to-pa-PD-and-PT-state-WoW-no-page-fault
;;   (implies (and
;;             ;; Page directory
;;             (page-directory-entry-addr-found-p lin-addr-1 x86)
;;             (not
;;              (mv-nth 0
;;                      (paging-entry-no-page-fault-p
;;                       lin-addr-1
;;                       (rm-low-64
;;                        (page-directory-entry-addr
;;                         lin-addr-1
;;                         (mv-nth 1 (page-directory-base-addr lin-addr-1 x86)))
;;                        x86)
;;                       wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)))
;;             ;; Page table
;;             (page-table-entry-addr-found-p lin-addr-2 x86)
;;             (not
;;              (mv-nth
;;               0
;;               (page-table-entry-no-page-fault-p
;;                lin-addr-2
;;                (rm-low-64
;;                 (page-table-entry-addr
;;                  lin-addr-2
;;                  (mv-nth 1 (page-table-base-addr lin-addr-2 x86)))
;;                 x86)
;;                u-s-acc-2
;;                wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
;;            (equal
;;             (mv-nth
;;              2
;;              (ia32e-la-to-pa-PD
;;               lin-addr-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
;;               (mv-nth
;;                2
;;                (ia32e-la-to-pa-PT
;;                 lin-addr-2 u-s-acc-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
;;             (mv-nth
;;              2
;;              (ia32e-la-to-pa-PT
;;               lin-addr-2 u-s-acc-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2
;;               (mv-nth
;;                2
;;                (ia32e-la-to-pa-PD
;;                 lin-addr-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86))))))
;;   :hints (("Goal"
;;            :use ((:instance paging-entry-no-page-fault-p-with-xlate-equiv-entries-and-x86s
;;                             (lin-addr lin-addr-1)
;;                             (wp wp-1) (smep smep-1) (nxe nxe-1) (r-w-x r-w-x-1) (cpl cpl-1)
;;                             (e-1 (rm-low-64
;;                                   (page-directory-entry-addr
;;                                    lin-addr-1
;;                                    (mv-nth
;;                                     1
;;                                     (page-directory-base-addr
;;                                      lin-addr-1
;;                                      (mv-nth 2
;;                                              (ia32e-la-to-pa-pt lin-addr-2 u-s-acc-2
;;                                                                 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)))))
;;                                   (mv-nth 2
;;                                           (ia32e-la-to-pa-pt lin-addr-2 u-s-acc-2
;;                                                              wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
;;                             (e-2 (rm-low-64
;;                                   (page-directory-entry-addr
;;                                    lin-addr-1 (mv-nth 1 (page-directory-base-addr lin-addr-1 x86)))
;;                                   x86))
;;                             (x86-1 (mv-nth 2
;;                                            (ia32e-la-to-pa-PT
;;                                             lin-addr-2 u-s-acc-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)))
;;                             (x86-2 x86)))
;;            :in-theory (e/d* (ia32e-la-to-pa-PD
;;                              ia32e-la-to-pa-page-directory)
;;                             (bitops::logand-with-negated-bitmask
;;                              accessed-bit
;;                              dirty-bit
;;                              bitops::logior-equal-0)))))



;; (DEFTHM XLATE-EQUIV-X86S-AND-PAGE-DIRECTORY-ENTRY-ADDR-ADDRESS
;;   (IMPLIES (AND (XLATE-EQUIV-X86S X86-1 X86-2)
;;                 (PAGE-DIR-PTR-TABLE-ENTRY-ADDR-FOUND-P LIN-ADDR X86-1))
;;            (EQUAL (PAGE-DIRECTORY-ENTRY-ADDR
;;                    LIN-ADDR
;;                    (MV-NTH 1
;;                            (PAGE-DIRECTORY-BASE-ADDR LIN-ADDR X86-1)))
;;                   (PAGE-DIRECTORY-ENTRY-ADDR
;;                    LIN-ADDR
;;                    (MV-NTH 1
;;                            (PAGE-DIRECTORY-BASE-ADDR LIN-ADDR X86-2))))))

;; (DEFTHM XLATE-EQUIV-X86S-AND-PAGE-DIRECTORY-ENTRY-ADDR-VALUE
;;   (IMPLIES (AND (XLATE-EQUIV-X86S X86-1 X86-2)
;;                 (PAGE-DIRECTORY-ENTRY-ADDR-FOUND-P LIN-ADDR X86-1))
;;            (XLATE-EQUIV-ENTRIES
;;             (RM-LOW-64 (PAGE-DIRECTORY-ENTRY-ADDR
;;                         LIN-ADDR
;;                         (MV-NTH 1
;;                                 (PAGE-DIRECTORY-BASE-ADDR LIN-ADDR X86-1)))
;;                        X86-1)
;;             (RM-LOW-64 (PAGE-DIRECTORY-ENTRY-ADDR
;;                         LIN-ADDR
;;                         (MV-NTH 1 (PAGE-DIRECTORY-BASE-ADDR LIN-ADDR X86-2)))
;;                        X86-2))))

;; (defthm foo
;;   (implies (page-directory-entry-addr-found-p lin-addr-1 x86)
;;            (xlate-equiv-entries
;;             (rm-low-64
;;              (page-directory-entry-addr
;;               lin-addr-1
;;               (mv-nth
;;                1
;;                (page-directory-base-addr
;;                 lin-addr-1
;;                 (mv-nth 2
;;                         (ia32e-la-to-pa-PT
;;                          lin-addr-2 u-s-acc-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)))))
;;              (mv-nth 2
;;                      (ia32e-la-to-pa-PT
;;                       lin-addr-2 u-s-acc-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)))

;;             (rm-low-64
;;              (page-directory-entry-addr
;;               lin-addr-1 (mv-nth 1 (page-directory-base-addr lin-addr-1 x86)))
;;              x86)))
;;   :hints (("Goal"
;;            :use ((:instance xlate-equiv-x86s-and-page-directory-entry-addr-value
;;                             (lin-addr lin-addr-1)
;;                             (x86-2 (mv-nth 2
;;                                            (ia32e-la-to-pa-PT
;;                                             lin-addr-2 u-s-acc-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)))
;;                             (x86-1 x86)))
;;            :in-theory (e/d* ()
;;                             (xlate-equiv-x86s-and-page-directory-entry-addr-value)))))

;; (defthm good-paging-structures-x86p-and-page-table-entry-no-page-fault-p
;;   (implies (good-paging-structures-x86p x86)
;;            (equal (good-paging-structures-x86p
;;                    (mv-nth 2
;;                            (page-table-entry-no-page-fault-p
;;                             lin-addr entry u-s-acc wp smep nxe r-w-x cpl x86)))
;;                   (good-paging-structures-x86p x86)))
;;   :hints (("Goal" :in-theory (e/d* (page-table-entry-no-page-fault-p
;;                                     page-fault-exception)
;;                                    ()))))

;; (defthm rm-low-64-and-mv-nth-2-page-table-entry-no-page-fault-p-value-when-error
;;   (implies (mv-nth 0
;;                    (page-table-entry-no-page-fault-p
;;                     lin-addr entry
;;                     u-s-acc wp smep nxe r-w-x cpl x86))
;;            (equal (rm-low-64 addr
;;                              (mv-nth 2
;;                                      (page-table-entry-no-page-fault-p
;;                                       lin-addr entry
;;                                       u-s-acc wp smep nxe r-w-x cpl x86)))
;;                   (rm-low-64 addr x86)))
;;   :hints
;;   (("Goal" :in-theory (e/d* (page-table-entry-no-page-fault-p
;;                              page-fault-exception)
;;                             ()))))

;; ;; PML4 Table:

;; (defthm pml4-table-base-addr-and-page-table-entry-no-page-fault-p
;;   (implies (good-paging-structures-x86p x86)
;;            (equal (pml4-table-base-addr
;;                    (mv-nth 2
;;                            (page-table-entry-no-page-fault-p
;;                             lin-addr entry u-s-acc wp smep nxe r-w-x cpl x86)))
;;                   (pml4-table-base-addr x86)))
;;   :hints (("Goal" :in-theory (e/d* (pml4-table-base-addr
;;                                     page-table-entry-no-page-fault-p
;;                                     page-fault-exception)
;;                                    ()))))

;; (defthm pml4-table-base-addr-and-ia32e-la-to-pa-PT
;;   (equal (pml4-table-base-addr
;;           (mv-nth
;;            2
;;            (ia32e-la-to-pa-PT
;;             lin-addr u-s-acc wp smep nxe r-w-x cpl x86)))
;;          (pml4-table-base-addr x86))
;;   :hints (("Goal" :in-theory (e/d* (pml4-table-base-addr
;;                                     ia32e-la-to-pa-PT
;;                                     ia32e-la-to-pa-page-table)
;;                                    (bitops::logand-with-negated-bitmask)))))

;; ;; Page Directory Pointer Table:

;; (defthm page-dir-ptr-table-base-addr-and-page-table-entry-no-page-fault-p
;;   (implies (good-paging-structures-x86p x86)
;;            (equal (page-dir-ptr-table-base-addr
;;                    lin-addr
;;                    (mv-nth 2
;;                            (page-table-entry-no-page-fault-p
;;                             lin-addr entry u-s-acc wp smep nxe r-w-x cpl x86)))
;;                   (page-dir-ptr-table-base-addr lin-addr x86)))
;;   :hints (("Goal" :in-theory (e/d* (page-dir-ptr-table-base-addr
;;                                     page-table-entry-no-page-fault-p
;;                                     page-fault-exception)
;;                                    ()))))

;; (defthm page-dir-ptr-table-base-addr-and-ia32e-la-to-pa-PT
;;   (equal (page-dir-ptr-table-base-addr
;;           lin-addr
;;           (mv-nth
;;            2
;;            (ia32e-la-to-pa-PT
;;             lin-addr u-s-acc wp smep nxe r-w-x cpl x86)))
;;          (page-dir-ptr-table-base-addr lin-addr x86))
;;   :hints (("Goal"
;;            :cases
;;            ((equal
;;              (pml4-table-entry-addr
;;               lin-addr
;;               (mv-nth 1 (pml4-table-base-addr x86)))
;;              (page-table-entry-addr
;;               lin-addr
;;               (mv-nth 1 (page-table-base-addr lin-addr x86)))))
;;            :in-theory (e/d* (page-dir-ptr-table-base-addr
;;                              ia32e-la-to-pa-PT
;;                              ia32e-la-to-pa-page-table)
;;                             (bitops::logand-with-negated-bitmask)))))

;; ;; Page Directory:

;; (defthm page-directory-base-addr-and-page-table-entry-no-page-fault-p
;;   (implies (good-paging-structures-x86p x86)
;;            (equal (page-directory-base-addr
;;                    lin-addr
;;                    (mv-nth 2
;;                            (page-table-entry-no-page-fault-p
;;                             lin-addr entry u-s-acc wp smep nxe r-w-x cpl x86)))
;;                   (page-directory-base-addr lin-addr x86)))
;;   :hints (("Goal" :in-theory (e/d* (page-directory-base-addr
;;                                     page-table-entry-no-page-fault-p
;;                                     page-fault-exception)
;;                                    ()))))

;; (defthm page-directory-base-addr-and-ia32e-la-to-pa-PT
;;   (equal (page-directory-base-addr
;;           lin-addr
;;           (mv-nth
;;            2
;;            (ia32e-la-to-pa-PT
;;             lin-addr u-s-acc wp smep nxe r-w-x cpl x86)))
;;          (page-directory-base-addr lin-addr x86))
;;   :hints (("Goal"
;;            :cases
;;            ((equal
;;              (page-dir-ptr-table-entry-addr
;;               lin-addr
;;               (mv-nth 1 (page-dir-ptr-table-base-addr lin-addr x86)))
;;              (page-table-entry-addr
;;               lin-addr
;;               (mv-nth 1 (page-table-base-addr lin-addr x86)))))
;;            :in-theory (e/d* (page-directory-base-addr
;;                              ia32e-la-to-pa-PT
;;                              ia32e-la-to-pa-page-table)
;;                             (bitops::logand-with-negated-bitmask)))))


;; ;; (skip-proofs
;; ;;  (defthm page-directory-base-addr-and-ia32e-la-to-pa-PT
;; ;;    (implies (page-directory-entry-addr-found-p lin-addr-2 x86)
;; ;;             (equal (page-directory-base-addr
;; ;;                     lin-addr-1
;; ;;                     (mv-nth
;; ;;                      2
;; ;;                      (ia32e-la-to-pa-PT
;; ;;                       lin-addr-2 u-s-acc-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)))
;; ;;                    (page-directory-base-addr lin-addr-1 x86)))
;; ;;    :hints (("Goal" :in-theory (e/d* (page-directory-base-addr)
;; ;;                                     ())))))

;; (DEFTHM PAGE-DIRECTORY-ENTRY-ADDR-FOUND-P-AND-WM-LOW-64-ENTRY-ADDR
;;   (IMPLIES
;;    (AND (EQUAL ADDRS
;;                (GATHER-ALL-PAGING-STRUCTURE-QWORD-ADDRESSES X86))
;;         (MEMBER-LIST-P INDEX ADDRS)
;;         (XLATE-EQUIV-ENTRIES VAL (RM-LOW-64 INDEX X86))
;;         (UNSIGNED-BYTE-P 64 VAL)
;;         (PAGE-DIR-PTR-TABLE-ENTRY-ADDR-FOUND-P LIN-ADDR X86))
;;    (EQUAL
;;     (PAGE-DIRECTORY-ENTRY-ADDR-FOUND-P LIN-ADDR (WM-LOW-64 INDEX VAL X86))
;;     (PAGE-DIRECTORY-ENTRY-ADDR-FOUND-P LIN-ADDR X86))))

;; (skip-proofs
;;  (defthm page-directory-entry-addr-found-p-and-wm-low-64-entry-addr-xlate-equiv-x86s
;;    ;; For this thm, x86-1 == x86 and x86-2 is the state after a page
;;    ;; traversal function.
;;    (implies
;;     (and (xlate-equiv-entries val (rm-low-64 index x86-1))
;;          (xlate-equiv-x86s x86-1 x86-2)
;;          (equal addrs (gather-all-paging-structure-qword-addresses x86-1))
;;          (member-list-p index addrs)
;;          (unsigned-byte-p 64 val)
;;          (page-dir-ptr-table-entry-addr-found-p lin-addr x86-1))
;;     (equal
;;      (page-directory-entry-addr-found-p lin-addr (wm-low-64 index val x86-2))
;;      (page-directory-entry-addr-found-p lin-addr x86-1)))))

;; (DEFTHM XLATE-EQUIV-X86S-AND-PAGE-DIRECTORY-ENTRY-ADDR-ADDRESS
;;   ;; Ugh, free var.
;;   (IMPLIES
;;    (AND (XLATE-EQUIV-X86S X86-1 X86-2)
;;         (PAGE-DIR-PTR-TABLE-ENTRY-ADDR-FOUND-P LIN-ADDR X86-1))
;;    (EQUAL
;;     (PAGE-DIRECTORY-ENTRY-ADDR
;;      LIN-ADDR
;;      (MV-NTH 1
;;              (PAGE-DIRECTORY-BASE-ADDR LIN-ADDR X86-1)))
;;     (PAGE-DIRECTORY-ENTRY-ADDR
;;      LIN-ADDR
;;      (MV-NTH 1
;;              (PAGE-DIRECTORY-BASE-ADDR LIN-ADDR X86-2))))))

;; (defthm ia32e-la-to-pa-PD-state-WoW-no-page-fault-both-4K-pages
;;   (implies (and
;;             (equal (page-size (rm-low-64
;;                                (page-directory-entry-addr
;;                                 lin-addr-1
;;                                 (mv-nth 1 (page-directory-base-addr lin-addr-1 x86)))
;;                                x86))
;;                    0)
;;             (equal (page-size (rm-low-64
;;                                (page-directory-entry-addr
;;                                 lin-addr-2
;;                                 (mv-nth 1 (page-directory-base-addr lin-addr-2 x86)))
;;                                x86))
;;                    0)
;;             (page-directory-entry-addr-found-p lin-addr-1 x86)
;;             (page-directory-entry-addr-found-p lin-addr-2 x86)
;;             (not
;;              (mv-nth 0
;;                      (paging-entry-no-page-fault-p
;;                       lin-addr-1
;;                       (rm-low-64
;;                        (page-directory-entry-addr
;;                         lin-addr-1
;;                         (mv-nth 1 (page-directory-base-addr lin-addr-1 x86)))
;;                        x86)
;;                       wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)))
;;             (not
;;              (mv-nth
;;               0
;;               (paging-entry-no-page-fault-p
;;                lin-addr-2
;;                (rm-low-64
;;                 (page-directory-entry-addr
;;                  lin-addr-2
;;                  (mv-nth 1 (page-directory-base-addr lin-addr-2 x86)))
;;                 x86)
;;                wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)))
;;             (equal u-s-acc-1
;;                    (page-user-supervisor
;;                     (rm-low-64
;;                      (page-directory-entry-addr
;;                       lin-addr-1
;;                       (mv-nth 1 (page-directory-base-addr lin-addr-1 x86)))
;;                      x86)))
;;             (equal u-s-acc-2
;;                    (page-user-supervisor
;;                     (rm-low-64
;;                      (page-directory-entry-addr
;;                       lin-addr-2
;;                       (mv-nth 1 (page-directory-base-addr lin-addr-2 x86)))
;;                      x86)))
;;             (page-table-entry-addr-found-p lin-addr-1 x86)
;;             (page-table-entry-addr-found-p lin-addr-2 x86)
;;             (not
;;              (mv-nth 0
;;                      (page-table-entry-no-page-fault-p
;;                       lin-addr-1
;;                       (rm-low-64
;;                        (page-table-entry-addr
;;                         lin-addr-1
;;                         (mv-nth 1 (page-table-base-addr lin-addr-1 x86)))
;;                        x86)
;;                       u-s-acc-1
;;                       wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)))
;;             (not
;;              (mv-nth
;;               0
;;               (page-table-entry-no-page-fault-p
;;                lin-addr-2
;;                (rm-low-64
;;                 (page-table-entry-addr
;;                  lin-addr-2
;;                  (mv-nth 1 (page-table-base-addr lin-addr-2 x86)))
;;                 x86)
;;                u-s-acc-2
;;                wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
;;            (equal
;;             (mv-nth
;;              2
;;              (ia32e-la-to-pa-PD
;;               lin-addr-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
;;               (mv-nth
;;                2
;;                (ia32e-la-to-pa-PD
;;                 lin-addr-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
;;             (mv-nth
;;              2
;;              (ia32e-la-to-pa-PD
;;               lin-addr-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2
;;               (mv-nth
;;                2
;;                (ia32e-la-to-pa-PD
;;                 lin-addr-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86))))))
;;   :hints (("Goal"
;;            ;; :use ((:instance paging-entry-no-page-fault-p-with-xlate-equiv-entries-and-x86s
;;            ;;                  (x86-1 )
;;            ;;                  (e-1 )
;;            ;;                  (x86-2 )
;;            ;;                  (e-2 )
;;            ;;                  (lin-addr lin-addr-2)
;;            ;;                  (wp wp-2)
;;            ;;                  (smep smep-2)
;;            ;;                  (nxe nxe-2)
;;            ;;                  (r-w-x r-w-x-2)
;;            ;;                  (cpl cpl-2)))
;;            :cases ((not (equal
;;                          (page-directory-entry-addr
;;                           lin-addr-1
;;                           (mv-nth 1 (page-directory-base-addr lin-addr-1 x86)))
;;                          (page-directory-entry-addr
;;                           lin-addr-2
;;                           (mv-nth 1 (page-directory-base-addr lin-addr-2 x86))))))
;;            :in-theory (e/d* (ia32e-la-to-pa-PD
;;                              ia32e-la-to-pa-page-directory)
;;                             (bitops::logand-with-negated-bitmask
;;                              accessed-bit
;;                              dirty-bit
;;                              bitops::logior-equal-0)))))

;; ;; ----------------------------------------------------------------------

;; (defthm ia32e-la-to-pa-PDPT-state-WoW-no-page-fault
;;   (implies (and (page-dir-ptr-table-entry-addr-found-p lin-addr-1 x86)
;;                 (page-dir-ptr-table-entry-addr-found-p lin-addr-2 x86)
;;                 (not
;;                  (mv-nth 0
;;                          (paging-entry-no-page-fault-p
;;                           lin-addr-1
;;                           (rm-low-64
;;                            (page-dir-ptr-table-entry-addr
;;                             lin-addr-1
;;                             (mv-nth 1 (page-dir-ptr-table-base-addr lin-addr-1 x86)))
;;                            x86)
;;                           wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)))
;;                 (not
;;                  (mv-nth
;;                   0
;;                   (paging-entry-no-page-fault-p
;;                    lin-addr-2
;;                    (rm-low-64
;;                     (page-dir-ptr-table-entry-addr
;;                      lin-addr-2
;;                      (mv-nth 1 (page-dir-ptr-table-base-addr lin-addr-2 x86)))
;;                     x86)
;;                    wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
;;            (equal
;;             (mv-nth
;;              2
;;              (ia32e-la-to-pa-PDPT
;;               lin-addr-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
;;               (mv-nth
;;                2
;;                (ia32e-la-to-pa-PDPT
;;                 lin-addr-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
;;             (mv-nth
;;              2
;;              (ia32e-la-to-pa-PDPT
;;               lin-addr-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2
;;               (mv-nth
;;                2
;;                (ia32e-la-to-pa-PDPT
;;                 lin-addr-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86))))))
;;   :hints (("Goal"
;;            :cases ((equal
;;                     (page-dir-ptr-table-entry-addr
;;                      lin-addr-1
;;                      (mv-nth 1 (page-dir-ptr-table-base-addr lin-addr-1 x86)))
;;                     (page-dir-ptr-table-entry-addr
;;                      lin-addr-2
;;                      (mv-nth 1 (page-dir-ptr-table-base-addr lin-addr-2 x86)))))
;;            :in-theory (e/d* (ia32e-la-to-pa-PDPT
;;                              ia32e-la-to-pa-page-dir-ptr-table)
;;                             (bitops::logand-with-negated-bitmask
;;                              accessed-bit
;;                              dirty-bit
;;                              bitops::logior-equal-0)))))

;; (defthm ia32e-la-to-pa-PML4T-state-WoW-no-page-fault
;;   (implies (and (pml4-table-entry-addr-found-p lin-addr-1 x86)
;;                 (pml4-table-entry-addr-found-p lin-addr-2 x86)
;;                 (not
;;                  (mv-nth 0
;;                          (paging-entry-no-page-fault-p
;;                           lin-addr-1
;;                           (rm-low-64
;;                            (pml4-table-entry-addr
;;                             lin-addr-1
;;                             (mv-nth 1 (pml4-table-base-addr x86)))
;;                            x86)
;;                           wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)))
;;                 (not
;;                  (mv-nth
;;                   0
;;                   (paging-entry-no-page-fault-p
;;                    lin-addr-2
;;                    (rm-low-64
;;                     (pml4-table-entry-addr
;;                      lin-addr-2
;;                      (mv-nth 1 (pml4-table-base-addr x86)))
;;                     x86)
;;                    wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
;;            (equal
;;             (mv-nth
;;              2
;;              (ia32e-la-to-pa-PML4T
;;               lin-addr-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
;;               (mv-nth
;;                2
;;                (ia32e-la-to-pa-PML4T
;;                 lin-addr-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
;;             (mv-nth
;;              2
;;              (ia32e-la-to-pa-PML4T
;;               lin-addr-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2
;;               (mv-nth
;;                2
;;                (ia32e-la-to-pa-PML4T
;;                 lin-addr-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86))))))
;;   :hints (("Goal"
;;            :cases ((equal
;;                     (pml4-table-entry-addr
;;                      lin-addr-1
;;                      (mv-nth 1 (pml4-table-base-addr x86)))
;;                     (pml4-table-entry-addr
;;                      lin-addr-2
;;                      (mv-nth 1 (pml4-table-base-addr x86)))))
;;            :in-theory (e/d* (ia32e-la-to-pa-PML4T
;;                              ia32e-la-to-pa-pml4-table)
;;                             (bitops::logand-with-negated-bitmask
;;                              accessed-bit
;;                              dirty-bit
;;                              bitops::logior-equal-0)))))


;; (defthm ia32e-entries-found-la-to-pa-WoW-no-page-fault
;;   (implies
;;    (and
;;     (paging-entries-found-p lin-addr-1 x86)
;;     (paging-entries-found-p lin-addr-2 x86)
;;     (not (mv-nth 0 (ia32e-entries-found-la-to-pa lin-addr-1 r-w-x-1 cpl-1 x86)))
;;     (not (mv-nth 0 (ia32e-entries-found-la-to-pa lin-addr-2 r-w-x-2 cpl-2 x86))))
;;    (equal
;;     (mv-nth
;;      2
;;      (ia32e-entries-found-la-to-pa
;;       lin-addr-1 r-w-x-1 cpl-1
;;       (mv-nth 2 (ia32e-entries-found-la-to-pa lin-addr-2 r-w-x-2 cpl-2 x86))))
;;     (mv-nth
;;      2
;;      (ia32e-entries-found-la-to-pa
;;       lin-addr-2 r-w-x-2 cpl-2
;;       (mv-nth 2 (ia32e-entries-found-la-to-pa lin-addr-1 r-w-x-1 cpl-1 x86))))))
;;   :hints (("Goal" :in-theory (e/d* (ia32e-entries-found-la-to-pa)
;;                                    ()))))

;; ======================================================================
