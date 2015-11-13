;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")
(include-book "gather-paging-structures")
(include-book "x86-ia32e-paging-alt")
(include-book "gather-paging-structures-thms")

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "centaur/bitops/signed-byte-p" :dir :system))

;; ======================================================================

;; ia32e-la-to-pa-page-table:

(skip-proofs
 (defrule page-table-base-addr-with-xlate-equiv-x86s-0
   (implies (xlate-equiv-x86s x86-1 x86-2)
            (equal (mv-nth
                    0
                    (page-table-base-addr
                     lin-addr x86-1))
                   (mv-nth
                    0
                    (page-table-base-addr
                     lin-addr x86-2))))
   :in-theory (e/d* (page-table-base-addr)
                    (not))
   :rule-classes :congruence))

(skip-proofs
 (defrule page-table-base-addr-with-xlate-equiv-x86s-1
   (implies (xlate-equiv-x86s x86-1 x86-2)
            (equal (mv-nth
                    1
                    (page-table-base-addr
                     lin-addr x86-1))
                   (mv-nth
                    1
                    (page-table-base-addr
                     lin-addr x86-2))))
   :in-theory (e/d* (page-table-base-addr)
                    (not))
   :rule-classes :congruence))

(defrule mv-nth-1-ia32e-la-to-pa-PT-with-xlate-equiv-x86s
  (implies (xlate-equiv-x86s x86-1 x86-2)
           (equal (mv-nth
                   1
                   (ia32e-la-to-pa-PT
                    lin-addr u-s-acc wp smep nxe r-w-x cpl x86-1))
                  (mv-nth
                   1
                   (ia32e-la-to-pa-PT
                    lin-addr u-s-acc wp smep nxe r-w-x cpl x86-2))))
  :in-theory (e/d* (ia32e-la-to-pa-page-table
                    xlate-equiv-entries-at-qword-addresses?)
                   (not
                    xlate-equiv-x86s))
  :rule-classes :congruence)

(defrule xlate-equiv-x86s-with-mv-nth-2-ia32e-la-to-pa-PT
  (implies (and (pairwise-disjoint-p (gather-all-paging-structure-qword-addresses x86))
                (x86p x86))
           (xlate-equiv-x86s
            (mv-nth
             2
             (ia32e-la-to-pa-PT
              lin-addr u-s-acc wp smep nxe r-w-x cpl x86))
            x86))
  :in-theory (e/d* (ia32e-la-to-pa-page-table
                    ;; gather-all-paging-structure-qword-addresses
                    ;; gather-pml4-table-qword-addresses
                    page-fault-exception
                    )
                   ()))

(i-am-here)

;; ======================================================================

(defmacro ia32e-la-to-pa-page-table-entry-components-equal-p-body
  (page-table-entry-1 page-table-entry-2)
  `(and (equal (ia32e-pte-4k-page-slice :pte-p   ,page-table-entry-1)
               (ia32e-pte-4k-page-slice :pte-p   ,page-table-entry-2))
        (equal (ia32e-pte-4k-page-slice :pte-r/w ,page-table-entry-1)
               (ia32e-pte-4k-page-slice :pte-r/w ,page-table-entry-2))
        (equal (ia32e-pte-4k-page-slice :pte-u/s ,page-table-entry-1)
               (ia32e-pte-4k-page-slice :pte-u/s ,page-table-entry-2))
        (equal (ia32e-pte-4k-page-slice :pte-xd  ,page-table-entry-1)
               (ia32e-pte-4k-page-slice :pte-xd  ,page-table-entry-2))
        ;; Reserved bits are zero.
        ;; (equal (loghead 11 (logtail 52 ,page-table-entry-2)) 0)
        (equal (loghead 11 (logtail 52 ,page-table-entry-1))
               (loghead 11 (logtail 52 ,page-table-entry-2)))))

(define ia32e-la-to-pa-page-table-entry-components-equal-p
  (page-table-entry-1 page-table-entry-2)
  :verify-guards nil
  :non-executable t
  (ia32e-la-to-pa-page-table-entry-components-equal-p-body page-table-entry-1 page-table-entry-2))

(defmacro ia32e-la-to-pa-page-table-entry-components-equal-p-macro (x y)
  `(ia32e-la-to-pa-page-table-entry-components-equal-p-body ,x ,y))

(defthm ia32e-la-to-pa-page-table-entry-components-equal-p-reflexive
  (ia32e-la-to-pa-page-table-entry-components-equal-p b b)
  :hints (("Goal" :in-theory (e/d
                              (ia32e-la-to-pa-page-table-entry-components-equal-p)
                              ()))))

(defthm ia32e-la-to-pa-page-table-entry-components-equal-p-accessed-bit-set
  (ia32e-la-to-pa-page-table-entry-components-equal-p
   b ;; (logior 32 (logand 18446744073709551583 b))
   (set-accessed-bit b))
  :hints (("Goal" :in-theory (e/d
                              (ia32e-la-to-pa-page-table-entry-components-equal-p
                               set-accessed-bit)
                              ()))))

(defthm ia32e-la-to-pa-page-table-entry-components-equal-p-dirty-bit-set
  (ia32e-la-to-pa-page-table-entry-components-equal-p
   b ;; (logior 64 (logand 18446744073709551551 b))
   (set-dirty-bit b))
  :hints (("Goal" :in-theory (e/d
                              (ia32e-la-to-pa-page-table-entry-components-equal-p
                               set-dirty-bit)
                              ()))))

(defthm ia32e-la-to-pa-page-table-entry-components-equal-p-accessed-and-dirty-bits-set
  (ia32e-la-to-pa-page-table-entry-components-equal-p
   b
   ;; (logior
   ;;  64
   ;;  (logand
   ;;   18446744073709551551
   ;;   (logior 32 (logand 18446744073709551583 b))))
   (set-dirty-bit (set-accessed-bit b)))
  :hints (("Goal" :in-theory (e/d
                              (ia32e-la-to-pa-page-table-entry-components-equal-p
                               set-dirty-bit
                               set-accessed-bit)
                              ()))))
;; ......................................................................
;; Rules about the three return values of ia32e-la-to-pa-page-table-entry:
;; ......................................................................

(defrule mv-nth-0-no-error-ia32e-la-to-pa-page-table
  (implies (ia32e-la-to-pa-page-table-entry-validp
            lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl x86)
           (equal (mv-nth
                   0
                   (ia32e-la-to-pa-page-table
                    lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl x86))
                  nil))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-table)
                  (not)))

(defrule mv-nth-0-no-error-ia32e-la-to-pa-page-table-with-disjoint-!memi
  (implies (and (ia32e-la-to-pa-page-table-entry-validp
                 lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl x86)
                (equal page-table-entry-addr
                       (page-table-entry-addr lin-addr page-table-base-addr))
                (disjoint-p (addr-range 1 addr)
                            (addr-range 8 page-table-entry-addr)))
           (equal (mv-nth
                   0
                   (ia32e-la-to-pa-page-table
                    lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl
                    (xw :mem addr val x86)))
                  nil))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-table)
                  (addr-range-1 not)))

(defrule mv-nth-0-no-error-ia32e-la-to-pa-page-table-with-disjoint-wm-low-64
  (implies (and (ia32e-la-to-pa-page-table-entry-validp
                 lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl x86)
                (equal page-table-entry-addr
                       (page-table-entry-addr lin-addr page-table-base-addr))
                (disjoint-p (addr-range 8 addr)
                            (addr-range 8 page-table-entry-addr))
                (integerp addr))
           (equal (mv-nth
                   0
                   (ia32e-la-to-pa-page-table
                    lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl
                    (wm-low-64 addr val x86)))
                  nil))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-table)
                  (not)))

(defrule mv-nth-1-no-error-ia32e-la-to-pa-page-table
  (implies (ia32e-la-to-pa-page-table-entry-validp
            lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl x86)
           (equal (mv-nth
                   1
                   (ia32e-la-to-pa-page-table
                    lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl x86))
                  ;; Physical address
                  (part-install
                   (part-select lin-addr :low 0 :high 11)
                   (ash (ia32e-pte-4K-page-slice
                         :pte-page
                         (rm-low-64 (page-table-entry-addr lin-addr page-table-base-addr)
                                    x86))
                        12)
                   :low 0 :high 11)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-table)
                  (not)))

(defruled mv-nth-1-no-error-ia32e-la-to-pa-page-table-different-components
  (implies (and (ia32e-la-to-pa-page-table-entry-validp
                 lin-addr page-table-base-addr u-s-acc-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)
                (ia32e-la-to-pa-page-table-entry-validp
                 lin-addr page-table-base-addr u-s-acc-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))
           (equal (mv-nth
                   1
                   (ia32e-la-to-pa-page-table
                    lin-addr page-table-base-addr u-s-acc-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86))
                  (mv-nth
                   1
                   (ia32e-la-to-pa-page-table
                    lin-addr page-table-base-addr u-s-acc-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
  :do-not '(preprocess)
  :in-theory (e/d () (ia32e-la-to-pa-page-table-entry-validp not)))

(defrule mv-nth-1-no-error-ia32e-la-to-pa-page-table-with-disjoint-!memi
  (implies (and (ia32e-la-to-pa-page-table-entry-validp
                 lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl x86)
                (equal page-table-entry-addr
                       (page-table-entry-addr lin-addr page-table-base-addr))
                (disjoint-p (addr-range 1 addr)
                            (addr-range 8 page-table-entry-addr)))
           (equal (mv-nth
                   1
                   (ia32e-la-to-pa-page-table
                    lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl
                    (xw :mem addr val x86)))
                  (mv-nth
                   1
                   (ia32e-la-to-pa-page-table
                    lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl
                    x86))))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-table)
                  (addr-range-1 not)))

(defrule mv-nth-1-no-error-ia32e-la-to-pa-page-table-with-disjoint-wm-low-64
  (implies (and (ia32e-la-to-pa-page-table-entry-validp
                 lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl x86)
                (equal page-table-entry-addr
                       (page-table-entry-addr lin-addr page-table-base-addr))
                (disjoint-p (addr-range 8 addr)
                            (addr-range 8 page-table-entry-addr))
                (integerp addr))
           (equal (mv-nth
                   1
                   (ia32e-la-to-pa-page-table
                    lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl
                    (wm-low-64 addr val x86)))
                  (mv-nth
                   1
                   (ia32e-la-to-pa-page-table
                    lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl
                    x86))))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-table)
                  ()))

(defrule mv-nth-2-no-error-ia32e-la-to-pa-page-table
  (implies (and (ia32e-la-to-pa-page-table-entry-validp
                 lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl x86)

                (equal page-table-entry-addr
                       (page-table-entry-addr lin-addr page-table-base-addr))
                (equal page-table-entry (rm-low-64 page-table-entry-addr x86))

                (equal accessed (ia32e-page-tables-slice :a page-table-entry))
                (equal dirty (ia32e-page-tables-slice :d page-table-entry))

                (equal accessed-entry
                       (if (equal accessed 0)
                           (set-accessed-bit page-table-entry)
                         page-table-entry))
                (equal dirty-entry
                       (if (and (equal dirty 0)
                                (equal r-w-x :w))
                           (set-dirty-bit accessed-entry)
                         accessed-entry))
                (equal dirty-x86
                       (if (or (equal accessed 0)
                               (and (equal dirty 0)
                                    (equal r-w-x :w)))
                           (wm-low-64 page-table-entry-addr dirty-entry x86)
                         x86)))
           (equal (mv-nth
                   2
                   (ia32e-la-to-pa-page-table
                    lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl x86))
                  dirty-x86))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-table)
                  ()))

;; ......................................................................
;; Reading page-table-entry-addr again using rm-low-64:
;; ......................................................................

(defruled rm-low-64-and-page-table
  ;; Note that the conclusion of this theorem is very similar to
  ;; theorems about other page-table-entry accessor functions.  After all, all
  ;; paging data structures are modified in the same way.
  (implies (and (ia32e-la-to-pa-page-table-entry-validp
                 lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl x86)
                (equal page-table-entry-addr
                       (page-table-entry-addr lin-addr page-table-base-addr))
                (equal page-table-entry (rm-low-64 page-table-entry-addr x86))
                (physical-address-p page-table-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 page-table-base-addr) 0)
                (x86p x86))
           (equal (rm-low-64 page-table-entry-addr
                             (mv-nth
                              2
                              (ia32e-la-to-pa-page-table
                               lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl x86)))
                  (cond
                   ( ;; Accessed and dirty bits are set.
                    (and (equal (ia32e-page-tables-slice :a page-table-entry) 1)
                         (equal (ia32e-page-tables-slice :d page-table-entry) 1))
                    (rm-low-64 page-table-entry-addr x86))

                   ( ;; Accessed bit is set and dirty bit is clear and
                    ;; memory write is being done.
                    (and (equal (ia32e-page-tables-slice :a page-table-entry) 1)
                         (equal (ia32e-page-tables-slice :d page-table-entry) 0)
                         (equal r-w-x :w))
                    (set-dirty-bit (rm-low-64 page-table-entry-addr x86)))

                   ( ;; Accessed bit is set and dirty bit is clear and
                    ;; memory write is not being done.
                    (and (equal (ia32e-page-tables-slice :a page-table-entry) 1)
                         (equal (ia32e-page-tables-slice :d page-table-entry) 0)
                         (not (equal r-w-x :w)))
                    (rm-low-64 page-table-entry-addr x86))

                   ( ;; Accessed and dirty bits are clear and memory
                    ;; write is being done.
                    (and (equal (ia32e-page-tables-slice :a page-table-entry) 0)
                         (equal (ia32e-page-tables-slice :d page-table-entry) 0)
                         (equal r-w-x :w))
                    (set-dirty-bit (set-accessed-bit (rm-low-64 page-table-entry-addr x86))))

                   ( ;; Accessed bit and dirty bits are clear and memory
                    ;; write is not being done.
                    (and (equal (ia32e-page-tables-slice :a page-table-entry) 0)
                         (equal (ia32e-page-tables-slice :d page-table-entry) 0)
                         (not (equal r-w-x :w)))
                    (set-accessed-bit (rm-low-64 page-table-entry-addr x86)))

                   (t
                    ;; This shouldn't be reached.
                    (rm-low-64 page-table-entry-addr
                               (mv-nth
                                2
                                (ia32e-la-to-pa-page-table
                                 lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl x86)))))))

  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-table)
                  (not
                   unsigned-byte-p
                   signed-byte-p)))

;; ......................................................................
;; !memi and state after data structure walk WoW theorem:
;; ......................................................................

(defrule disjoint-!memi-mv-nth-2-no-error-ia32e-la-to-pa-page-table
  (implies (and (ia32e-la-to-pa-page-table-entry-validp
                 lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl x86)
                (equal page-table-entry-addr
                       (page-table-entry-addr lin-addr page-table-base-addr))
                (disjoint-p (addr-range 1 addr)
                            (addr-range 8 page-table-entry-addr))
                (integerp addr))
           (equal
            (mv-nth 2 (ia32e-la-to-pa-page-table
                       lin-addr page-table-base-addr u-s-acc wp smep
                       nxe r-w-x cpl
                       (xw :mem addr val x86)))
            (xw :mem addr val
                (mv-nth 2 (ia32e-la-to-pa-page-table
                           lin-addr page-table-base-addr u-s-acc wp smep
                           nxe r-w-x cpl x86)))))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-table)
                  (not
                   addr-range-1)))

;; ......................................................................
;; Reading addresses disjoint from page-table-entry-addr after walking
;; the page table:
;; ......................................................................

(defrule disjoint-memi-mv-nth-2-no-error-ia32e-la-to-pa-page-table
  (implies (and (ia32e-la-to-pa-page-table-entry-validp
                 lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl x86)
                (equal page-table-entry-addr
                       (page-table-entry-addr lin-addr page-table-base-addr))
                (disjoint-p (addr-range 1 addr)
                            (addr-range 8 page-table-entry-addr)))
           (equal
            (xr :mem
                addr
                (mv-nth 2 (ia32e-la-to-pa-page-table
                           lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl x86)))
            (xr :mem addr x86)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-table)
                  (not
                   addr-range-1)))

(defrule disjoint-rm-low-64-mv-nth-2-no-error-ia32e-la-to-pa-page-table
  (implies (and (ia32e-la-to-pa-page-table-entry-validp
                 lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl x86)
                (equal page-table-entry-addr
                       (page-table-entry-addr lin-addr page-table-base-addr))
                (disjoint-p (addr-range 8 addr)
                            (addr-range 8 page-table-entry-addr))
                (integerp addr))
           (equal
            (rm-low-64
             addr
             (mv-nth 2 (ia32e-la-to-pa-page-table
                        lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl x86)))
            (rm-low-64 addr x86)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-table)
                  (not)))

(defrule disjoint-rm-low-32-mv-nth-2-no-error-ia32e-la-to-pa-page-table
  (implies (and (ia32e-la-to-pa-page-table-entry-validp
                 lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl x86)
                (equal page-table-entry-addr
                       (page-table-entry-addr lin-addr page-table-base-addr))
                (disjoint-p (addr-range 4 addr)
                            (addr-range 8 page-table-entry-addr))
                (integerp addr))
           (equal
            (rm-low-32
             addr
             (mv-nth 2 (ia32e-la-to-pa-page-table
                        lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl x86)))
            (rm-low-32 addr x86)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-table
                   wm-low-64)
                  (not)))

;; ......................................................................
;; Theorems that state that the validity of the page table entry is
;; preserved when writes are done to disjoint addresses or :a/:d are
;; set:
;; ......................................................................

(defrule page-table-entry-with-disjoint-!memi-still-valid-ia32e-la-to-pa-page-table
  (implies (and (ia32e-la-to-pa-page-table-entry-validp
                 lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl x86)
                (equal page-table-entry-addr
                       (page-table-entry-addr lin-addr page-table-base-addr))
                (disjoint-p
                 (addr-range 1 addr)
                 (addr-range 8 page-table-entry-addr)))
           (ia32e-la-to-pa-page-table-entry-validp
            lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl
            (xw :mem addr val x86)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-table)
                  (not addr-range-1
                       unsigned-byte-p
                       signed-byte-p)))

(defrule page-table-entry-with-disjoint-wm-low-64-still-valid-ia32e-la-to-pa-page-table
  (implies (and (ia32e-la-to-pa-page-table-entry-validp
                 lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl x86)
                (equal page-table-entry-addr
                       (page-table-entry-addr lin-addr page-table-base-addr))
                (disjoint-p
                 (addr-range 8 addr)
                 (addr-range 8 page-table-entry-addr))
                (integerp addr))
           (ia32e-la-to-pa-page-table-entry-validp
            lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl
            (wm-low-64 addr val x86)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-table)
                  (not
                   unsigned-byte-p
                   signed-byte-p)))

(defrule page-table-entry-with-accessed-bit-set-still-valid-ia32e-la-to-pa-page-table
  (implies (and (ia32e-la-to-pa-page-table-entry-validp
                 lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl x86)
                (equal page-table-entry-addr
                       (page-table-entry-addr lin-addr page-table-base-addr))
                (equal page-table-entry (rm-low-64 page-table-entry-addr x86))

                (physical-address-p page-table-base-addr)
                (canonical-address-p lin-addr)
                (x86p x86))

           (ia32e-la-to-pa-page-table-entry-validp
            lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl
            (wm-low-64
             page-table-entry-addr
             ;; (!ia32e-page-tables-slice :a 1 page-table-entry)
             ;; (logior 32 (logand 18446744073709551583 page-table-entry))
             (set-accessed-bit page-table-entry)
             x86)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-table
                   set-accessed-bit)
                  (not
                   unsigned-byte-p
                   signed-byte-p)))

(defrule page-table-entry-with-dirty-bit-set-still-valid-ia32e-la-to-pa-page-table
  (implies (and (ia32e-la-to-pa-page-table-entry-validp
                 lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl x86)
                (equal page-table-entry-addr
                       (page-table-entry-addr lin-addr page-table-base-addr))
                (equal page-table-entry (rm-low-64 page-table-entry-addr x86))

                (physical-address-p page-table-base-addr)
                (canonical-address-p lin-addr)
                (x86p x86))

           (ia32e-la-to-pa-page-table-entry-validp
            lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl
            (wm-low-64
             page-table-entry-addr
             ;; (!ia32e-page-tables-slice :d 1 page-table-entry)
             ;; (logior 64 (logand 18446744073709551551 page-table-entry))
             (set-dirty-bit page-table-entry)
             x86)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-table
                   set-dirty-bit)
                  (not
                   unsigned-byte-p
                   signed-byte-p)))

(defrule page-table-entry-with-accessed-and-dirty-bits-set-still-valid-ia32e-la-to-pa-page-table
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-table-entry-validp
                 lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl x86)
                (equal page-table-entry-addr
                       (page-table-entry-addr lin-addr page-table-base-addr))
                (equal page-table-entry (rm-low-64 page-table-entry-addr x86))

                (physical-address-p page-table-base-addr)
                (canonical-address-p lin-addr)
                (x86p x86))

           (ia32e-la-to-pa-page-table-entry-validp
            lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl
            (wm-low-64
             page-table-entry-addr
             ;; (!ia32e-page-tables-slice :d 1 (!ia32e-page-tables-slice :a 1 page-table-entry))
             ;; (logior
             ;;  64
             ;;  (logand
             ;;   18446744073709551551
             ;;   (logior 32 (logand 18446744073709551583 page-table-entry))))
             (set-dirty-bit (set-accessed-bit page-table-entry))
             x86)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-table
                   set-accessed-bit
                   set-dirty-bit)
                  (not
                   unsigned-byte-p
                   signed-byte-p)))

;; ......................................................................
;; Reading page table entry from x86 states where :a/:d are set:
;; ......................................................................

(defrule reading-entry-with-accessed-bit-set-ia32e-la-to-pa-page-table
  (implies
   (and (ia32e-la-to-pa-page-table-entry-validp
         lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl x86)
        (equal page-table-entry-addr
               (page-table-entry-addr lin-addr page-table-base-addr))
        (equal page-table-entry
               (rm-low-64 page-table-entry-addr x86))
        (physical-address-p page-table-base-addr)
        (canonical-address-p lin-addr)
        (x86p x86))
   (equal
    (mv-nth
     1
     (ia32e-la-to-pa-page-table
      lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl
      (wm-low-64
       page-table-entry-addr
       ;; (!ia32e-page-tables-slice :a 1 page-table-entry)
       ;; (logior 32 (logand 18446744073709551583 page-table-entry))
       (set-accessed-bit page-table-entry)
       x86)))
    (mv-nth
     1
     (ia32e-la-to-pa-page-table
      lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl x86))))
  :do-not '(preprocess)
  :in-theory (e/d (set-accessed-bit)
                  (not
                   mv-nth-2-no-error-ia32e-la-to-pa-page-table
                   unsigned-byte-p
                   signed-byte-p)))

(defrule reading-entry-with-dirty-bit-set-ia32e-la-to-pa-page-table
  (implies (and (ia32e-la-to-pa-page-table-entry-validp
                 lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl x86)
                (equal page-table-entry-addr
                       (page-table-entry-addr lin-addr page-table-base-addr))
                (equal page-table-entry (rm-low-64 page-table-entry-addr x86))
                (physical-address-p page-table-base-addr)
                (canonical-address-p lin-addr)
                (x86p x86))

           (equal
            (mv-nth
             1
             (ia32e-la-to-pa-page-table
              lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl
              (wm-low-64
               page-table-entry-addr
               ;; (!ia32e-page-tables-slice :d 1 page-table-entry)
               ;; (logior 64 (logand 18446744073709551551 page-table-entry))
               (set-dirty-bit page-table-entry)
               x86)))
            (mv-nth
             1
             (ia32e-la-to-pa-page-table
              lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl x86))))
  :do-not '(preprocess)
  :in-theory (e/d (set-dirty-bit)
                  (not
                   mv-nth-2-no-error-ia32e-la-to-pa-page-table
                   unsigned-byte-p
                   signed-byte-p)))

(defrule reading-entry-with-accessed-and-dirty-bits-set-ia32e-la-to-pa-page-table
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-table-entry-validp
                 lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl x86)
                (equal page-table-entry-addr
                       (page-table-entry-addr lin-addr page-table-base-addr))
                (equal page-table-entry (rm-low-64 page-table-entry-addr x86))
                (physical-address-p page-table-base-addr)
                (canonical-address-p lin-addr)
                (x86p x86))

           (equal
            (mv-nth
             1
             (ia32e-la-to-pa-page-table
              lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl
              (wm-low-64
               page-table-entry-addr
               ;; (!ia32e-page-tables-slice :d 1 (!ia32e-page-tables-slice :a 1 page-table-entry))
               ;; (logior
               ;;  64
               ;;  (logand
               ;;   18446744073709551551
               ;;   (logior 32 (logand 18446744073709551583 page-table-entry))))
               (set-dirty-bit (set-accessed-bit page-table-entry))
               x86)))
            (mv-nth
             1
             (ia32e-la-to-pa-page-table
              lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl x86))))
  :do-not '(preprocess)
  :in-theory (e/d (set-accessed-bit
                   set-dirty-bit)
                  (not
                   mv-nth-2-no-error-ia32e-la-to-pa-page-table
                   unsigned-byte-p
                   signed-byte-p)))

;; ......................................................................
;; More theorems about preservation of validity of page table entries:
;; ......................................................................

(defrule relating-validity-of-two-entries-in-two-x86-states-wrt-page-table-4K-pages
  (implies (and (ia32e-la-to-pa-page-table-entry-validp
                 lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl x86)
                (equal page-table-entry-addr
                       (page-table-entry-addr lin-addr page-table-base-addr))
                (equal page-table-entry-1 (rm-low-64 page-table-entry-addr x86))
                (equal page-table-entry-2 (rm-low-64 page-table-entry-addr x86-another))
                (ia32e-la-to-pa-page-table-entry-components-equal-p
                 page-table-entry-1 page-table-entry-2))

           (ia32e-la-to-pa-page-table-entry-validp
            lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl
            x86-another))
  :in-theory (e/d (ia32e-la-to-pa-page-table-entry-components-equal-p)
                  ()))

(defruled page-table-components-equal-rm-low-64-of-table-page-table-entry-addr-via-page-table-4K-pages
  (implies (and (ia32e-la-to-pa-page-table-entry-validp
                 lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl x86)
                (equal page-table-entry-addr
                       (page-table-entry-addr lin-addr page-table-base-addr))
                (equal page-table-entry (rm-low-64 page-table-entry-addr x86))
                (physical-address-p page-table-base-addr)
                (canonical-address-p lin-addr)
                (x86p x86))

           (ia32e-la-to-pa-page-table-entry-components-equal-p
            (rm-low-64 page-table-entry-addr x86)
            (rm-low-64
             page-table-entry-addr
             (mv-nth
              2
              (ia32e-la-to-pa-page-table
               lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl x86)))))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (e/d (rm-low-64-and-page-table
                            ia32e-la-to-pa-page-table-entry-components-equal-p)
                           (not
                            member-p-cons
                            disjoint-p-cons
                            ia32e-la-to-pa-page-table-entry-validp
                            unsigned-byte-p
                            signed-byte-p)))))

(defrule re-read-entry-still-valid-ia32e-la-to-pa-page-table
  (implies (and (ia32e-la-to-pa-page-table-entry-validp
                 lin-addr page-table-base-addr u-s-acc-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)
                (ia32e-la-to-pa-page-table-entry-validp
                 lin-addr page-table-base-addr u-s-acc-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)
                (physical-address-p page-table-base-addr)
                (canonical-address-p lin-addr)
                (x86p x86))
           (ia32e-la-to-pa-page-table-entry-validp
            lin-addr page-table-base-addr u-s-acc-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
            (mv-nth
             2
             (ia32e-la-to-pa-page-table
              lin-addr page-table-base-addr u-s-acc-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
  :do-not '(preprocess)
  :in-theory (e/d (page-table-components-equal-rm-low-64-of-table-page-table-entry-addr-via-page-table-4K-pages)
                  (ia32e-la-to-pa-page-table-entry-validp
                   mv-nth-2-no-error-ia32e-la-to-pa-page-table
                   not
                   unsigned-byte-p
                   signed-byte-p)))

;; ......................................................................
;; Two page table walks
;; ......................................................................

(encapsulate
 ()

 (local
  (defthm open-addr-range
    (implies (natp x)
             (equal (addr-range 8 x)
                    (list x (+ 1 x) (+ 2 x) (+ 3 x)
                          (+ 4 x) (+ 5 x) (+ 6 x) (+ 7 x))))))

 (local
  (encapsulate
   ()

   (local (include-book "arithmetic-5/top" :dir :system))

   (defthm multiples-of-8-and-disjointness-of-physical-addresses-helper-1
     (implies (and (equal (loghead 3 x) 0)
                   (equal (loghead 3 y) 0)
                   (posp n)
                   (<= n 7)
                   (natp x)
                   (natp y))
              (not (equal (+ n x) y)))
     :hints (("Goal" :in-theory (e/d* (loghead)
                                      ()))))

   (defthm multiples-of-8-and-disjointness-of-physical-addresses-helper-2
     (implies (and (equal (loghead 3 x) 0)
                   (equal (loghead 3 y) 0)
                   (not (equal x y))
                   (posp n)
                   (<= n 7)
                   (posp m)
                   (<= m 7)
                   (natp x)
                   (natp y))
              (not (equal (+ n x) (+ m y))))
     :hints (("Goal" :in-theory (e/d* (loghead)
                                      ()))))))

 (defthm multiples-of-8-and-disjointness-of-physical-addresses
   (implies (and (equal (loghead 3 addr-1) 0)
                 (equal (loghead 3 addr-2) 0)
                 (not (equal addr-2 addr-1))
                 (natp addr-1)
                 (natp addr-2))
            (disjoint-p (addr-range 8 addr-2)
                        (addr-range 8 addr-1)))))

(defrule two-page-table-walks-ia32e-la-to-pa-page-table
  (implies (and (ia32e-la-to-pa-page-table-entry-validp
                 lin-addr-1 page-table-base-addr-1 u-s-acc-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)
                (ia32e-la-to-pa-page-table-entry-validp
                 lin-addr-2 page-table-base-addr-2 u-s-acc-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)

                (equal page-table-entry-addr-1
                       (page-table-entry-addr lin-addr-1 page-table-base-addr-1))
                (equal page-table-entry-addr-2
                       (page-table-entry-addr lin-addr-2 page-table-base-addr-2))

                ;; Both page-table-entry-addr are multiples of 8. (see
                ;; PAGE-TABLE-ENTRY-ADDR-IS-A-MULTIPLE-OF-8) So, one
                ;; of the following can be true:
                ;; 1. (equal (addr-range 8 page-table-entry-addr-1)
                ;;           (addr-range 8 page-table-entry-addr-2))
                ;; 2. (disjoint-p (addr-range 8 page-table-entry-addr-1)
                ;;                (addr-range 8 page-table-entry-addr-2))
                (equal (loghead 12 page-table-base-addr-1) 0)
                (equal (loghead 12 page-table-base-addr-2) 0)

                (canonical-address-p lin-addr-1)
                (canonical-address-p lin-addr-2)
                (physical-address-p page-table-base-addr-1)
                (physical-address-p page-table-base-addr-2)
                (x86p x86))
           (equal
            (mv-nth
             1
             (ia32e-la-to-pa-page-table
              lin-addr-1 page-table-base-addr-1 u-s-acc-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
              (mv-nth
               2
               (ia32e-la-to-pa-page-table
                lin-addr-2 page-table-base-addr-2 u-s-acc-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
            (mv-nth
             1
             (ia32e-la-to-pa-page-table
              lin-addr-1 page-table-base-addr-1 u-s-acc-1 wp-1 smep-1 nxe-1 r-w-x-1
              cpl-1 x86))))
  :cases ((equal (page-table-entry-addr lin-addr-1 page-table-base-addr-1)
                 (page-table-entry-addr lin-addr-2 page-table-base-addr-2)))
  :in-theory (e/d ()
                  (ia32e-la-to-pa-page-table-entry-validp
                   mv-nth-1-no-error-ia32e-la-to-pa-page-table
                   unsigned-byte-p
                   signed-byte-p
                   member-p-cons
                   disjoint-p-cons))
  :do-not '(preprocess))

;; ......................................................................
;; Validity of a page table entry is preserved after a walk
;; ......................................................................

(defrule validity-preserved-same-x86-state-wrt-page-table
  (implies (and (ia32e-la-to-pa-page-table-entry-validp
                 lin-addr-1 page-table-base-addr-1 u-s-acc-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)
                (ia32e-la-to-pa-page-table-entry-validp
                 lin-addr-2 page-table-base-addr-2 u-s-acc-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)

                (equal page-table-entry-addr-1
                       (page-table-entry-addr lin-addr-1 page-table-base-addr-1))
                (equal page-table-entry-addr-2
                       (page-table-entry-addr lin-addr-2 page-table-base-addr-2))

                ;; Both page-table-entry-addr are multiples of 8 (the
                ;; function page-table-entry-addr always returns
                ;; addresses that are a multiple of 8 if the base-addr
                ;; is 4K-aligned --- I could have the 4K-aligned
                ;; nature of page-table-base-addr in the hyps as an
                ;; alternative to the following two hyps.)

                ;; So, one of the following can be true:
                ;; 1. (equal (addr-range 8 page-table-entry-addr-1)
                ;;           (addr-range 8 page-table-entry-addr-2))
                ;; 2. (disjoint-p (addr-range 8 page-table-entry-addr-1)
                ;;                (addr-range 8 page-table-entry-addr-2))
                (equal (loghead 12 page-table-base-addr-1) 0)
                (equal (loghead 12 page-table-base-addr-2) 0)

                (canonical-address-p lin-addr-1)
                (canonical-address-p lin-addr-2)
                (physical-address-p page-table-base-addr-1)
                (physical-address-p page-table-base-addr-2)
                (x86p x86))
           (ia32e-la-to-pa-page-table-entry-validp
            lin-addr-1 page-table-base-addr-1 u-s-acc-1 wp-1 smep-1
            nxe-1 r-w-x-1 cpl-1
            (mv-nth 2
                    (ia32e-la-to-pa-page-table
                     lin-addr-2 page-table-base-addr-2 u-s-acc-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
  :cases ((equal (page-table-entry-addr lin-addr-1 page-table-base-addr-1)
                 (page-table-entry-addr lin-addr-2 page-table-base-addr-2)))
  :in-theory (e/d (mv-nth-2-no-error-ia32e-la-to-pa-page-table)
                  (addr-range-1
                   ia32e-la-to-pa-page-table-entry-validp
                   member-p-cons
                   disjoint-p-cons
                   not
                   unsigned-byte-p
                   signed-byte-p)))

;; ......................................................................
;; Translation-Governing-Addresses-For-Page-Table and
;; ia32e-la-to-pa-page-table-entry:
;; ......................................................................

(defrule translation-governing-addresses-for-page-table-and-ia32e-la-to-pa-page-table
  (equal
   (translation-governing-addresses-for-page-table
    lin-addr-1 page-table-base-addr-1
    (mv-nth 2
            (ia32e-la-to-pa-page-table
             lin-addr-2 page-table-base-addr-2 u-s-acc-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)))
   (translation-governing-addresses-for-page-table
    lin-addr-1 page-table-base-addr-1 x86))
  :in-theory (e/d ()
                  (ia32e-la-to-pa-page-table-entry-validp
                   addr-range-1
                   mv-nth-2-no-error-ia32e-la-to-pa-page-table
                   member-p-cons
                   disjoint-p-cons
                   not
                   unsigned-byte-p
                   signed-byte-p)))

(in-theory (e/d () (ia32e-la-to-pa-page-table-entry-validp)))

;; ======================================================================
