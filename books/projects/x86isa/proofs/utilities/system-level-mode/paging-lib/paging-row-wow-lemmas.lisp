;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")
(include-book "paging-top" :ttags :all)

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "centaur/bitops/signed-byte-p" :dir :system))

(local (in-theory (e/d (entry-found-p-and-lin-addr
                        entry-found-p-and-good-paging-structures-x86p
                        ia32e-la-to-pa-and-ia32e-entries-found-la-to-pa)
                       (signed-byte-p
                        unsigned-byte-p))))

;; ======================================================================

(defthm ia32e-la-to-pa-PT-state-WoW-no-page-fault
  (implies (and (page-table-entry-addr-found-p lin-addr-1 (double-rewrite x86))
                (not
                 (mv-nth
                  0
                  (page-table-entry-no-page-fault-p
                   lin-addr-1
                   (mv-nth 2 (read-page-table-entry lin-addr-1 x86))
                   u-s-acc-1
                   wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)))
                (not
                 (mv-nth
                  0
                  (page-table-entry-no-page-fault-p
                   lin-addr-2
                   (mv-nth 2 (read-page-table-entry lin-addr-2 x86))
                   u-s-acc-2
                   wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
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
                             ia32e-la-to-pa-page-table-alt
                             read-page-table-entry)
                            (bitops::logand-with-negated-bitmask
                             accessed-bit
                             dirty-bit
                             bitops::logior-equal-0)))))

;; ======================================================================

(i-am-here)

(local
 (defthm ia32e-la-to-pa-PD-state-WoW-no-page-fault-both-2M-pages
   (implies (and
             (page-directory-entry-addr-found-p lin-addr-1 (double-rewrite x86))
             (equal (page-size (mv-nth 2 (read-page-directory-entry lin-addr-1 x86)))
                    1)
             (equal (page-size (mv-nth 2 (read-page-directory-entry lin-addr-2 x86)))
                    1)
             (not
              (mv-nth
               0
               (paging-entry-no-page-fault-p
                lin-addr-1
                (mv-nth 2 (read-page-directory-entry lin-addr-1 x86))
                wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)))
             (not
              (mv-nth
               0
               (paging-entry-no-page-fault-p
                lin-addr-2
                (mv-nth 2 (read-page-directory-entry lin-addr-2 x86))
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
                              ia32e-la-to-pa-page-directory-alt
                              read-page-directory-entry)
                             (bitops::logand-with-negated-bitmask
                              accessed-bit
                              dirty-bit
                              bitops::logior-equal-0))))))

(defthm ia32e-la-to-pa-PT-returns-no-error
  (implies (and (page-table-entry-addr-found-p lin-addr (double-rewrite x86))
                (not (mv-nth 0
                             (page-table-entry-no-page-fault-p
                              lin-addr
                              (mv-nth 2 (read-page-table-entry lin-addr x86))
                              u-s-acc
                              wp smep nxe r-w-x cpl x86))))
           (equal
            (mv-nth 0
                    (ia32e-la-to-pa-PT
                     lin-addr u-s-acc wp smep nxe r-w-x cpl x86))
            nil))
  :hints (("Goal" :in-theory (e/d* (ia32e-la-to-pa-PT
                                    ia32e-la-to-pa-page-table-alt)
                                   ()))))

(defthm foo
  ;; I don't want to enable READ-PAGE-DIRECTORY-ENTRY because
  ;; otherwise rules like
  ;; MV-NTH-2-PAGING-ENTRY-NO-PAGE-FAULT-P-VALUE-NO-ERROR won't
  ;; fire. But the rule XLATE-EQUIV-X86S-AND-WM-LOW-64-ENTRY-ADDR
  ;; needs to relieve it's xlate-equiv-entries hyp with
  ;; rm-low-64. This rule is a stop-gap to get around this right now.
  (implies (page-directory-entry-addr-found-p lin-addr (double-rewrite x86))
           (xlate-equiv-entries
            (mv-nth 2 (read-page-directory-entry lin-addr x86))
            (rm-low-64 (page-directory-entry-addr
                        lin-addr
                        (mv-nth 1 (page-directory-base-addr lin-addr x86)))
                       x86)))
  :hints (("Goal" :in-theory (e/d* (read-page-directory-entry)
                                   ()))))

(defthm mv-nth-2-paging-entry-no-page-fault-p-value-no-error-new
  (implies
   (and (not (mv-nth 0
                     (paging-entry-no-page-fault-p
                      lin-addr
                      entry wp smep nxe r-w-x cpl x86)))
        (unsigned-byte-p 64 entry))
   (equal (mv-nth 2
                  (paging-entry-no-page-fault-p
                   lin-addr
                   entry wp smep nxe r-w-x cpl x86))
          x86)))

(defthm bar
  (implies
   (and
    (not
     (mv-nth
      '0
      (paging-entry-no-page-fault-p$inline
       lin-addr-2
       (mv-nth '2
               (read-page-directory-entry lin-addr-2 x86))
       wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
   (not
    (mv-nth
     '0
     (paging-entry-no-page-fault-p$inline
      lin-addr-2
      (mv-nth
       '2
       (read-page-directory-entry
        lin-addr-2
        (mv-nth
         '2
         (ia32e-la-to-pa-pt
          lin-addr-1
          (page-user-supervisor
           (rm-low-64
            (page-directory-entry-addr$inline
             lin-addr-1
             (mv-nth '1
                     (page-directory-base-addr lin-addr-1 x86)))
            x86))
          wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86))))
      wp-2 smep-2 nxe-2 r-w-x-2 cpl-2
      (mv-nth
       '2
       (ia32e-la-to-pa-pt
        lin-addr-1
        (page-user-supervisor
         (rm-low-64
          (page-directory-entry-addr$inline
           lin-addr-1
           (mv-nth '1
                   (page-directory-base-addr lin-addr-1 x86)))
          x86))
        wp-1
        smep-1 nxe-1 r-w-x-1 cpl-1 x86)))))))

(defthm baz
  (implies
   (and
    (equal (page-directory-entry-addr
            lin-addr-1
            (mv-nth 1
                    (page-directory-base-addr lin-addr-1 x86)))
           (page-directory-entry-addr
            lin-addr-2
            (mv-nth 1
                    (page-directory-base-addr lin-addr-2 x86))))
    (not
     (mv-nth
      0
      (paging-entry-no-page-fault-p
       lin-addr-1
       (rm-low-64 (page-directory-entry-addr
                   lin-addr-1
                   (mv-nth 1
                           (page-directory-base-addr lin-addr-1 x86)))
                  x86)
       wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)))
    (page-table-entry-addr-found-p lin-addr-1 x86)
    (page-table-entry-addr-found-p lin-addr-2 x86))
   (NOT
    (MV-NTH
     '0
     (PAGING-ENTRY-NO-PAGE-FAULT-P$INLINE
      LIN-ADDR-1
      (MV-NTH
       '2
       (READ-PAGE-DIRECTORY-ENTRY
        LIN-ADDR-1
        (MV-NTH
         '2
         (IA32E-LA-TO-PA-PT
          LIN-ADDR-2
          (PAGE-USER-SUPERVISOR
           (RM-LOW-64 (PAGE-DIRECTORY-ENTRY-ADDR$INLINE
                       LIN-ADDR-1
                       (MV-NTH '1
                               (PAGE-DIRECTORY-BASE-ADDR LIN-ADDR-1 X86)))
                      X86))
          WP-2 SMEP-2 NXE-2 R-W-X-2 CPL-2
          (WM-LOW-64 (PAGE-DIRECTORY-ENTRY-ADDR$INLINE
                      LIN-ADDR-1
                      (MV-NTH '1
                              (PAGE-DIRECTORY-BASE-ADDR LIN-ADDR-1 X86)))
                     (SET-ACCESSED-BIT
                      (MV-NTH '2
                              (READ-PAGE-DIRECTORY-ENTRY LIN-ADDR-2 X86)))
                     X86)))))
      WP-1 SMEP-1 NXE-1 R-W-X-1 CPL-1
      (MV-NTH
       '2
       (IA32E-LA-TO-PA-PT
        LIN-ADDR-2
        (PAGE-USER-SUPERVISOR
         (RM-LOW-64 (PAGE-DIRECTORY-ENTRY-ADDR$INLINE
                     LIN-ADDR-1
                     (MV-NTH '1
                             (PAGE-DIRECTORY-BASE-ADDR LIN-ADDR-1 X86)))
                    X86))
        WP-2 SMEP-2 NXE-2 R-W-X-2 CPL-2
        (WM-LOW-64
         (PAGE-DIRECTORY-ENTRY-ADDR$INLINE
          LIN-ADDR-1
          (MV-NTH '1
                  (PAGE-DIRECTORY-BASE-ADDR LIN-ADDR-1 X86)))
         (SET-ACCESSED-BIT (MV-NTH '2
                                   (READ-PAGE-DIRECTORY-ENTRY LIN-ADDR-2 X86)))
         X86))))))))


(defthm ia32e-la-to-pa-PD-state-WoW-no-page-fault-both-4K-pages
  (implies (and
            (DISJOINT-P
             (ADDR-RANGE 8
                         (PAGE-DIRECTORY-ENTRY-ADDR
                          LIN-ADDR-1
                          (MV-NTH 1 (PAGE-DIRECTORY-BASE-ADDR LIN-ADDR-1 X86))))
             (ADDR-RANGE 8
                         (PAGE-TABLE-ENTRY-ADDR
                          LIN-ADDR-1
                          (MV-NTH 1 (PAGE-TABLE-BASE-ADDR LIN-ADDR-1 X86)))))
            (DISJOINT-P
             (ADDR-RANGE 8
                         (PAGE-DIRECTORY-ENTRY-ADDR
                          LIN-ADDR-1
                          (MV-NTH 1 (PAGE-DIRECTORY-BASE-ADDR LIN-ADDR-1 X86))))
             (ADDR-RANGE 8
                         (PAGE-TABLE-ENTRY-ADDR
                          LIN-ADDR-2
                          (MV-NTH 1 (PAGE-TABLE-BASE-ADDR LIN-ADDR-2 X86)))))

            (equal (page-size
                    (mv-nth 2 (read-page-directory-entry lin-addr-1 x86)))
                   0)
            (equal (page-size
                    (mv-nth 2 (read-page-directory-entry lin-addr-2 x86)))
                   0)
            (page-directory-entry-addr-found-p lin-addr-1 x86)
            (page-directory-entry-addr-found-p lin-addr-2 x86)
            (not
             (mv-nth 0
                     (paging-entry-no-page-fault-p
                      lin-addr-1
                      (mv-nth 2 (read-page-directory-entry lin-addr-1 x86))
                      wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)))
            (not
             (mv-nth
              0
              (paging-entry-no-page-fault-p
               lin-addr-2
               (mv-nth 2 (read-page-directory-entry lin-addr-2 x86))
               wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)))
            (equal u-s-acc-1
                   (page-user-supervisor
                    (mv-nth 2 (read-page-directory-entry lin-addr-1 x86))))
            (equal u-s-acc-2
                   (page-user-supervisor
                    (mv-nth 2 (read-page-directory-entry lin-addr-2 x86))))
            (page-table-entry-addr-found-p lin-addr-1 x86)
            (page-table-entry-addr-found-p lin-addr-2 x86)
            (not
             (mv-nth 0
                     (page-table-entry-no-page-fault-p
                      lin-addr-1
                      (mv-nth 2 (read-page-table-entry lin-addr-1 x86))
                      u-s-acc-1
                      wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)))
            (not
             (mv-nth
              0
              (page-table-entry-no-page-fault-p
               lin-addr-2
               (mv-nth 2 (read-page-table-entry lin-addr-2 x86))
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
           :cases ((not (equal
                         (page-directory-entry-addr
                          lin-addr-1
                          (mv-nth 1 (page-directory-base-addr lin-addr-1 x86)))
                         (page-directory-entry-addr
                          lin-addr-2
                          (mv-nth 1 (page-directory-base-addr lin-addr-2 x86))))))
           :in-theory (e/d* (ia32e-la-to-pa-PD
                             ia32e-la-to-pa-page-directory-alt)
                            (bitops::logand-with-negated-bitmask
                             accessed-bit
                             dirty-bit
                             bitops::logior-equal-0)))))


;; ======================================================================

#||

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
                        entry-found-p-and-good-paging-structures-x86p
                        ia32e-la-to-pa-and-ia32e-entries-found-la-to-pa)
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
            (xlate-equiv-entries (double-rewrite e-1) e-2)
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
  (implies (and (page-table-entry-addr-found-p lin-addr-1 (double-rewrite x86))
                (page-table-entry-addr-found-p lin-addr-2 (double-rewrite x86))
                (double-rewrite
                 (not
                  (mv-nth 0
                          (page-table-entry-no-page-fault-p
                           lin-addr-1
                           (rm-low-64
                            (page-table-entry-addr
                             lin-addr-1
                             (mv-nth 1 (page-table-base-addr lin-addr-1 x86)))
                            x86)
                           u-s-acc-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86))))
                (double-rewrite
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
                    u-s-acc-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)))))
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
                             ia32e-la-to-pa-page-table-alt
                             read-page-table-entry)
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
            (xlate-equiv-entries (double-rewrite e-1) e-2)
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

(local
 (defthm ia32e-la-to-pa-PD-state-WoW-no-page-fault-both-2M-pages
   (implies (and
             (double-rewrite
              (equal (page-size (rm-low-64
                                 (page-directory-entry-addr
                                  lin-addr-1
                                  (mv-nth 1 (page-directory-base-addr lin-addr-1 x86)))
                                 x86))
                     1))
             (double-rewrite
              (equal (page-size (rm-low-64
                                 (page-directory-entry-addr
                                  lin-addr-2
                                  (mv-nth 1 (page-directory-base-addr lin-addr-2 x86)))
                                 x86))
                     1))
             (page-directory-entry-addr-found-p lin-addr-1 (double-rewrite x86))
             (page-directory-entry-addr-found-p lin-addr-2 (double-rewrite x86))
             (double-rewrite
              (not
               (mv-nth 0
                       (paging-entry-no-page-fault-p
                        lin-addr-1
                        (rm-low-64
                         (page-directory-entry-addr
                          lin-addr-1
                          (mv-nth 1 (page-directory-base-addr lin-addr-1 x86)))
                         x86)
                        wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86))))
             (double-rewrite
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
                 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)))))
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

(defthm page-table-entry-no-page-fault-p-and-wm-low-64-commute
  (equal
   (mv-nth
    2
    (page-table-entry-no-page-fault-p
     lin-addr
     entry
     u-s-acc
     wp smep nxe r-w-x cpl
     (wm-low-64 index val x86)))
   (wm-low-64
    index val
    (mv-nth
     2
     (page-table-entry-no-page-fault-p
      lin-addr
      entry
      u-s-acc wp smep nxe r-w-x cpl x86))))
  :hints (("Goal" :in-theory (e/d* (page-table-entry-no-page-fault-p
                                    page-fault-exception)
                                   ()))))

(defthm no-error-from-ia32e-la-to-pa-PT-if-no-error-from-page-table-entry-no-page-fault-p
  (implies (and
            (not (mv-nth 0
                         (page-table-entry-no-page-fault-p
                          lin-addr
                          (rm-low-64
                           (page-table-entry-addr
                            lin-addr
                            (mv-nth 1 (page-table-base-addr lin-addr (double-rewrite x86))))
                           x86)
                          u-s-acc wp smep nxe r-w-x cpl x86)))
            (page-table-entry-addr-found-p lin-addr (double-rewrite x86)))
           (equal (mv-nth 0 (ia32e-la-to-pa-PT lin-addr u-s-acc wp smep nxe r-w-x cpl x86))
                  nil))
  :hints (("Goal" :in-theory (e/d* (ia32e-la-to-pa-PT
                                    ia32e-la-to-pa-page-table)
                                   (bitops::logand-with-negated-bitmask)))))

(defthm ia32e-la-to-pa-PT-and-wm-low-64-entry-addr-commute
  (implies (and
            (equal addrs (gather-all-paging-structure-qword-addresses x86))
            (member-list-p index addrs)
            (xlate-equiv-entries (double-rewrite val) (rm-low-64 index x86))
            (unsigned-byte-p 64 val)
            (page-directory-entry-addr-found-p lin-addr (double-rewrite x86))
            (disjoint-p (addr-range 8 index)
                        (addr-range 8
                                    (page-table-entry-addr
                                     lin-addr
                                     (mv-nth 1
                                             (page-table-base-addr
                                              lin-addr
                                              (double-rewrite x86)))))))
           (equal
            (mv-nth 2
                    (ia32e-la-to-pa-PT
                     lin-addr u-s-acc wp smep nxe r-w-x cpl
                     (wm-low-64 index val x86)))
            (wm-low-64 index val
                       (mv-nth 2
                               (ia32e-la-to-pa-PT
                                lin-addr u-s-acc wp smep nxe r-w-x cpl
                                x86)))))
  :hints (("Goal"
           :use ((:instance member-list-p-and-mult-8-qword-paddr-list-listp
                            (addrs (gather-all-paging-structure-qword-addresses x86))
                            (index index)))
           :in-theory (e/d* (ia32e-la-to-pa-PT
                             ia32e-la-to-pa-page-table)
                            (bitops::logand-with-negated-bitmask
                             member-list-p-and-mult-8-qword-paddr-list-listp)))))

;; (defthm xlate-equiv-x86s-with-mv-nth-2-paging-entry-no-page-fault-p
;; ;; Copied over.
;;   (implies (x86p x86)
;;            (xlate-equiv-x86s
;;             (mv-nth 2 (paging-entry-no-page-fault-p lin-addr entry wp smep nxe r-w-x cpl x86))
;;             (double-rewrite x86)))
;;   :hints (("Goal" :in-theory (e/d* (paging-entry-no-page-fault-p
;;                                     page-fault-exception
;;                                     xlate-equiv-x86s)
;;                                    ()))))

;; (defun find-an-xlate-equiv-x86-aux (thm-name x86-term)
;;   ;; Copied over.

;;   ;; Finds a "smaller" x86 that is xlate-equiv to x86-term.
;;   (if (atom x86-term)
;;       x86-term
;;     (b* ((outer-fn (car x86-term))
;;          ((when (and (not (equal outer-fn 'MV-NTH))
;;                      (not (equal outer-fn 'WM-LOW-64))))
;;           (cw "~%~p0: Unexpected x86-term encountered:~p1~%" thm-name x86-term)
;;           x86-term))
;;       (cond ((equal outer-fn 'MV-NTH)
;;              ;; We expect x86-term to be a function related to page
;;              ;; traversals.
;;              (b* ((mv-nth-index (second x86-term))
;;                   (inner-fn-call (third x86-term))
;;                   (inner-fn (first inner-fn-call))
;;                   ((when (or (not (equal mv-nth-index ''2))
;;                              (not (member-p inner-fn
;;                                             '(IA32E-LA-TO-PA-PT
;;                                               IA32E-LA-TO-PA-PD
;;                                               IA32E-LA-TO-PA-PDPT
;;                                               IA32E-LA-TO-PA-PML4T
;;                                               PAGE-TABLE-ENTRY-NO-PAGE-FAULT-P$INLINE
;;                                               PAGING-ENTRY-NO-PAGE-FAULT-P$INLINE)))))
;;                    (cw "~%~p0: Unexpected mv-nth x86-term encountered:~p1~%" thm-name x86-term)
;;                    x86-term)
;;                   (sub-x86 (first (last inner-fn-call))))
;;                sub-x86))
;;             ((equal outer-fn 'WM-LOW-64)
;;              ;; We expect x86-term to be of the form (wm-low-64 index val sub-x86).
;;              (b* ((sub-x86 (first (last x86-term))))
;;                sub-x86))))))

;; (defun find-an-xlate-equiv-x86 (thm-name x86-var x86-term)
;;   ;; Copied over.

;;   ;; bind-free for an x86 in xlate-equiv-x86s: should check just for the
;;   ;; page traversal functions and wm-low-64.

;;   ;; rewrite rules for xlate-equiv-x86s:
;;   ;; XLATE-EQUIV-X86S-WITH-MV-NTH-2-PAGING-ENTRY-NO-PAGE-FAULT-P
;;   ;; XLATE-EQUIV-X86S-WITH-MV-NTH-2-IA32E-LA-TO-PA-PT
;;   ;; XLATE-EQUIV-X86S-WITH-MV-NTH-2-IA32E-LA-TO-PA-PD
;;   ;; XLATE-EQUIV-X86S-WITH-MV-NTH-2-IA32E-LA-TO-PA-PDPT
;;   ;; XLATE-EQUIV-X86S-WITH-MV-NTH-2-IA32E-LA-TO-PA-PML4T
;;   ;; XLATE-EQUIV-X86S-WITH-MV-NTH-2-IA32E-ENTRIES-FOUND-LA-TO-PA
;;   ;; XLATE-EQUIV-X86S-AND-WM-LOW-64

;;   ;; TO-DO: Logic mode...
;;   (declare (xargs :mode :program))
;;   (b* ((equiv-x86-1 (find-an-xlate-equiv-x86-aux thm-name x86-term))
;;        (equiv-x86-2 (find-an-xlate-equiv-x86-aux thm-name equiv-x86-1)))
;;     (if (equal equiv-x86-1 equiv-x86-2)
;;         `((,x86-var . ,equiv-x86-1))
;;       (find-an-xlate-equiv-x86 thm-name x86-var equiv-x86-2))))

(defthm paging-entry-no-page-fault-p-error-with-xlate-equiv-x86s
  (implies (xlate-equiv-x86s x86-1 x86-2)
           (equal
            (mv-nth
             0
             (paging-entry-no-page-fault-p
              lin-addr entry wp smep nxe r-w-x cpl x86-1))
            (mv-nth
             0
             (paging-entry-no-page-fault-p
              lin-addr entry wp smep nxe r-w-x cpl x86-2))))
  :hints (("Goal" :in-theory (e/d* (paging-entry-no-page-fault-p
                                    page-fault-exception)
                                   ())))
  :rule-classes :congruence)

(defthm xlate-equiv-x86s-and-xlate-equiv-entries
  (implies (and
            ;; So that this rule doesn't attempt to rewrite
            ;; "smaller" x86s.
            (syntaxp (consp x86-1))
            (bind-free (find-an-xlate-equiv-x86
                        'xlate-equiv-x86s-and-xlate-equiv-entries
                        'x86-2 x86-1)
                       (x86-2))
            ;; The following double-rewrite is critical. The rule
            ;; won't apply without that.
            (xlate-equiv-x86s (double-rewrite x86-1) x86-2)
            (member-list-p index (gather-all-paging-structure-qword-addresses x86-1))
            (good-paging-structures-x86p x86-1))
           (xlate-equiv-entries (rm-low-64 index x86-1) (rm-low-64 index x86-2)))
  :hints (("Goal" :in-theory (e/d* (xlate-equiv-x86s)
                                   ()))))

;; (defthm xlate-equiv-x86s-and-wm-low-64
;;   ;; Copied over to paging-page-table-lemmas.lisp.
;;   (implies (and
;;             ;; We need the bind-free below if this is an
;;             ;; xlate-equiv-x86s rewrite rule.
;;             (bind-free (find-an-xlate-equiv-x86
;;                         'xlate-equiv-x86s-and-wm-low-64
;;                         'x86 x86-equiv)
;;                        (x86))
;;             (xlate-equiv-x86s x86 (double-rewrite x86-equiv))
;;             (xlate-equiv-entries (double-rewrite val) (rm-low-64 index x86))
;;             (member-list-p index (gather-all-paging-structure-qword-addresses x86))
;;             (good-paging-structures-x86p x86)
;;             (x86p (wm-low-64 index val x86-equiv))
;;             (unsigned-byte-p 64 val))
;;            (xlate-equiv-x86s (wm-low-64 index val x86-equiv) x86))
;;   :hints (("Goal"
;;            :use ((:instance
;;                   xlate-equiv-entries-at-qword-addresses?-with-wm-low-64-with-different-x86
;;                   (addrs (gather-all-paging-structure-qword-addresses x86))
;;                   (x86-1 x86)
;;                   (x86-2 x86-equiv)))
;;            :in-theory
;;            (e/d*
;;             (xlate-equiv-x86s
;;              good-paging-structures-x86p)
;;             (xlate-equiv-entries-at-qword-addresses?-with-wm-low-64-with-different-x86)))))

(defthm mv-nth-2-paging-entry-no-page-fault-p-after-wm-low-64-value
  (implies
   (not
    (mv-nth 0 (paging-entry-no-page-fault-p
               lin-addr entry wp smep nxe r-w-x cpl x86)))
   (equal
    (mv-nth 2
            (paging-entry-no-page-fault-p
             lin-addr entry wp smep nxe r-w-x cpl
             (wm-low-64 index val x86)))
    (wm-low-64 index val x86)))
  :hints (("Goal" :in-theory (e/d* (paging-entry-no-page-fault-p)
                                   ()))))

(defthm mv-nth-2-paging-entry-no-page-fault-p-after-page-table-traversal
  (implies
   (not
    (mv-nth 0
            (paging-entry-no-page-fault-p
             lin-addr-1 entry wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)))
   (equal
    (mv-nth 2
            (paging-entry-no-page-fault-p
             lin-addr-1 entry wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
             (mv-nth 2 (ia32e-la-to-pa-PT lin-addr-2 u-s-acc-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
    (mv-nth 2 (ia32e-la-to-pa-PT lin-addr-2 u-s-acc-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
  :hints (("Goal" :in-theory (e/d* (paging-entry-no-page-fault-p)
                                   ()))))

(defthm mv-nth-0-paging-entry-no-page-fault-p-after-page-table-traversal
  (equal
   (mv-nth 0
           (paging-entry-no-page-fault-p
            lin-addr-1 entry wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
            (mv-nth 2 (ia32e-la-to-pa-PT lin-addr-2 u-s-acc-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
   (mv-nth 0
           (paging-entry-no-page-fault-p
            lin-addr-1 entry wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)))
  :hints (("Goal" :in-theory (e/d* (paging-entry-no-page-fault-p)
                                   ()))))

(i-am-here)

;; (acl2::why ia32e-la-to-pa-PT-and-wm-low-64-entry-addr-commute)
;; (acl2::why xlate-equiv-x86s-and-xlate-equiv-entries)

(defthm ia32e-la-to-pa-PD-state-WoW-no-page-fault-both-4K-pages
  (implies (and
            (DISJOINT-P
             (ADDR-RANGE 8
                         (PAGE-DIRECTORY-ENTRY-ADDR
                          LIN-ADDR-1
                          (MV-NTH 1 (PAGE-DIRECTORY-BASE-ADDR LIN-ADDR-1 X86))))
             (ADDR-RANGE 8
                         (PAGE-TABLE-ENTRY-ADDR
                          LIN-ADDR-1
                          (MV-NTH 1 (PAGE-TABLE-BASE-ADDR LIN-ADDR-1 X86)))))
            (DISJOINT-P
             (ADDR-RANGE 8
                         (PAGE-DIRECTORY-ENTRY-ADDR
                          LIN-ADDR-1
                          (MV-NTH 1 (PAGE-DIRECTORY-BASE-ADDR LIN-ADDR-1 X86))))
             (ADDR-RANGE 8
                         (PAGE-TABLE-ENTRY-ADDR
                          LIN-ADDR-2
                          (MV-NTH 1 (PAGE-TABLE-BASE-ADDR LIN-ADDR-2 X86)))))

            (equal (page-size (rm-low-64
                               (page-directory-entry-addr
                                lin-addr-1
                                (mv-nth 1 (page-directory-base-addr lin-addr-1 x86)))
                               x86))
                   0)
            (equal (page-size (rm-low-64
                               (page-directory-entry-addr
                                lin-addr-2
                                (mv-nth 1 (page-directory-base-addr lin-addr-2 x86)))
                               x86))
                   0)
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
           :cases ((not (equal
                         (page-directory-entry-addr
                          lin-addr-1
                          (mv-nth 1 (page-directory-base-addr lin-addr-1 x86)))
                         (page-directory-entry-addr
                          lin-addr-2
                          (mv-nth 1 (page-directory-base-addr lin-addr-2 x86))))))
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
                            (mv-nth 1 (pml4-table-base-addr x86)))
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
                     (mv-nth 1 (pml4-table-base-addr x86)))
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
                     (mv-nth 1 (pml4-table-base-addr x86)))
                    (pml4-table-entry-addr
                     lin-addr-2
                     (mv-nth 1 (pml4-table-base-addr x86)))))
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
      (mv-nth 2 (ia32e-entries-found-la-to-pa lin-addr-1 r-w-x-1 cpl-1 x86))))))
  :hints (("Goal" :in-theory (e/d* (ia32e-entries-found-la-to-pa)
                                   ()))))

||#
