;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")
(include-book "paging-page-table-lemmas")

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))

;; ======================================================================

;; ia32e-la-to-pa-page-directory:

(defmacro ia32e-la-to-pa-page-directory-entry-components-equal-p-2M-body
  (page-directory-entry-1 page-directory-entry-2)
  `(and (equal (ia32e-pde-2MB-page-slice :pde-p    ,page-directory-entry-1)
               (ia32e-pde-2MB-page-slice :pde-p    ,page-directory-entry-2))
        (equal (ia32e-pde-2MB-page-slice :pde-r/w  ,page-directory-entry-1)
               (ia32e-pde-2MB-page-slice :pde-r/w  ,page-directory-entry-2))
        (equal (ia32e-pde-2MB-page-slice :pde-u/s  ,page-directory-entry-1)
               (ia32e-pde-2MB-page-slice :pde-u/s  ,page-directory-entry-2))
        (equal (ia32e-pde-2MB-page-slice :pde-ps   ,page-directory-entry-1)
               (ia32e-pde-2MB-page-slice :pde-ps   ,page-directory-entry-2))
        (equal (ia32e-pde-2MB-page-slice :pde-xd   ,page-directory-entry-1)
               (ia32e-pde-2MB-page-slice :pde-xd   ,page-directory-entry-2))
        ;; Reserved bits are zero.
        ;; (equal (loghead 11 (logtail 52 ,page-directory-entry-2)) 0)
        ;; (equal (loghead  8 (logtail 13 ,page-directory-entry-2)) 0)
        (equal (loghead 11 (logtail 52 ,page-directory-entry-1))
               (loghead 11 (logtail 52 ,page-directory-entry-2)))
        (equal (loghead  8 (logtail 13 ,page-directory-entry-1))
               (loghead  8 (logtail 13 ,page-directory-entry-2)))))

(defmacro ia32e-la-to-pa-page-directory-entry-components-equal-p-4K-body
  (page-directory-entry-1 page-directory-entry-2)
  `(and (equal (ia32e-pde-pg-table-slice :pde-p     ,page-directory-entry-1)
               (ia32e-pde-pg-table-slice :pde-p     ,page-directory-entry-2))
        (equal (ia32e-pde-pg-table-slice :pde-r/w   ,page-directory-entry-1)
               (ia32e-pde-pg-table-slice :pde-r/w   ,page-directory-entry-2))
        (equal (ia32e-pde-pg-table-slice :pde-u/s   ,page-directory-entry-1)
               (ia32e-pde-pg-table-slice :pde-u/s   ,page-directory-entry-2))
        (equal (ia32e-pde-pg-table-slice :pde-ps    ,page-directory-entry-1)
               (ia32e-pde-pg-table-slice :pde-ps    ,page-directory-entry-2))
        (equal (ia32e-pde-pg-table-slice :pde-pt    ,page-directory-entry-1)
               (ia32e-pde-pg-table-slice :pde-pt    ,page-directory-entry-2))
        (equal (ia32e-pde-pg-table-slice :pde-xd    ,page-directory-entry-1)
               (ia32e-pde-pg-table-slice :pde-xd    ,page-directory-entry-2))
        ;; Reserved bits are zero.
        ;; (equal (loghead 11 (logtail 52 ,page-directory-entry-2)) 0)
        (equal (loghead 11 (logtail 52 ,page-directory-entry-1))
               (loghead 11 (logtail 52 ,page-directory-entry-2)))))

(define ia32e-la-to-pa-page-directory-entry-components-equal-p
  (page-size? page-directory-entry-1 page-directory-entry-2)
  :verify-guards nil
  :non-executable t
  (if (equal page-size? '2M)
      (ia32e-la-to-pa-page-directory-entry-components-equal-p-2M-body
       page-directory-entry-1 page-directory-entry-2)
    (if (equal page-size? '4K)
        (ia32e-la-to-pa-page-directory-entry-components-equal-p-4K-body
         page-directory-entry-1 page-directory-entry-2)
      't)))

(defmacro ia32e-la-to-pa-page-directory-entry-components-equal-p-4K-macro (x y)
  `(ia32e-la-to-pa-page-directory-entry-components-equal-p-4K-body ,x ,y))

(defmacro ia32e-la-to-pa-page-directory-entry-components-equal-p-2M-macro (x y)
  `(ia32e-la-to-pa-page-directory-entry-components-equal-p-2M-body ,x
  ,y))

(defthm ia32e-la-to-pa-page-directory-entry-components-equal-p-reflexive
  (ia32e-la-to-pa-page-directory-entry-components-equal-p a b b)
  :hints (("Goal" :in-theory (e/d
                              (ia32e-la-to-pa-page-directory-entry-components-equal-p)
                              ()))))

(defthm ia32e-la-to-pa-page-directory-entry-components-equal-p-accessed-bit-set
  (ia32e-la-to-pa-page-directory-entry-components-equal-p
   a b ;; (logior 32 (logand 18446744073709551583 b))
   (set-accessed-bit b))
  :hints (("Goal" :in-theory (e/d
                              (ia32e-la-to-pa-page-directory-entry-components-equal-p
                               set-accessed-bit)
                              ()))))

(defthm ia32e-la-to-pa-page-directory-entry-components-equal-p-dirty-bit-set
  (ia32e-la-to-pa-page-directory-entry-components-equal-p
   a b ;; (logior 64 (logand 18446744073709551551 b))
   (set-dirty-bit b))
  :hints (("Goal" :in-theory (e/d
                              (ia32e-la-to-pa-page-directory-entry-components-equal-p
                               set-dirty-bit)
                              ()))))

(defthm ia32e-la-to-pa-page-directory-entry-components-equal-p-accessed-and-dirty-bits-set
  (ia32e-la-to-pa-page-directory-entry-components-equal-p
   a b
   ;; (logior
   ;;  64
   ;;  (logand
   ;;   18446744073709551551
   ;;   (logior 32 (logand 18446744073709551583 b))))
   (set-dirty-bit (set-accessed-bit b)))
  :hints (("Goal" :in-theory (e/d
                              (ia32e-la-to-pa-page-directory-entry-components-equal-p
                               set-dirty-bit
                               set-accessed-bit)
                              ()))))

;; ......................................................................
;; Establishing inferior data structure entry validity from page
;; directory entry's validity:
;; ......................................................................

(defrule page-directory-entry-validp-to-page-table-entry-validp
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
                 lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)
                (equal page-directory-entry-addr
                       (page-directory-entry-addr lin-addr page-directory-base-addr))
                (equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps page-directory-entry) 0)
                (equal page-table-base-addr
                       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry)
                            12))
                (equal u-s-acc
                       (ia32e-page-tables-slice :u/s page-directory-entry)))
           (ia32e-la-to-pa-page-table-entry-validp
            lin-addr page-table-base-addr u-s-acc
            wp smep nxe r-w-x cpl x86))
  :rule-classes (:rewrite :forward-chaining))

;; ......................................................................
;; Rules about the three return values of ia32e-la-to-pa-page-directory-entry:
;; ......................................................................

(defrule mv-nth-0-no-error-ia32e-la-to-pa-page-directory
  (implies (ia32e-la-to-pa-page-directory-entry-validp
            lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)
           (equal (mv-nth
                   0
                   (ia32e-la-to-pa-page-directory
                    lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86))
                  nil))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-directory)
                  (not)))

;; 2M pages:

(defrule mv-nth-0-no-error-ia32e-la-to-pa-page-directory-2M-pages-with-disjoint-!memi
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
                 lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)
                (equal page-directory-entry-addr
                       (page-directory-entry-addr lin-addr page-directory-base-addr))
                (equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  page-directory-entry) 1)
                (disjoint-p
                 (addr-range 1 addr)
                 (addr-range 8 page-directory-entry-addr)))
           (equal (mv-nth
                   0
                   (ia32e-la-to-pa-page-directory
                    lin-addr page-directory-base-addr wp smep nxe r-w-x cpl
                    (xw :mem addr val x86)))
                  nil))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-directory)
                  (not addr-range-1)))

(defrule mv-nth-0-no-error-ia32e-la-to-pa-page-directory-2M-pages-with-disjoint-wm-low-64
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
                 lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)
                (equal page-directory-entry-addr
                       (page-directory-entry-addr lin-addr page-directory-base-addr))
                (equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  page-directory-entry) 1)
                (disjoint-p
                 (addr-range 8 addr)
                 (addr-range 8 page-directory-entry-addr))
                (integerp addr))
           (equal (mv-nth
                   0
                   (ia32e-la-to-pa-page-directory
                    lin-addr page-directory-base-addr wp smep nxe r-w-x cpl
                    (wm-low-64 addr val x86)))
                  nil))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-directory)
                  (not)))

(defrule mv-nth-1-no-error-ia32e-la-to-pa-page-directory-2M-pages
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
                 lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)
                (equal page-directory-entry-addr
                       (page-directory-entry-addr lin-addr page-directory-base-addr))
                (equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  page-directory-entry) 1))

           (equal (mv-nth
                   1
                   (ia32e-la-to-pa-page-directory
                    lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86))
                  (part-install
                   (part-select lin-addr :low 0 :high 20)
                   (ash (ia32e-pde-2MB-page-slice :pde-page page-directory-entry) 21)
                   :low 0 :high 20)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-directory)
                  (not)))

(defrule mv-nth-1-no-error-ia32e-la-to-pa-page-directory-2M-pages-with-disjoint-!memi
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
                 lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)
                (equal page-directory-entry-addr
                       (page-directory-entry-addr lin-addr page-directory-base-addr))
                (equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  page-directory-entry) 1)
                (disjoint-p
                 (addr-range 1 addr)
                 (addr-range 8 page-directory-entry-addr))
                (integerp addr))

           (equal (mv-nth
                   1
                   (ia32e-la-to-pa-page-directory
                    lin-addr page-directory-base-addr wp smep nxe r-w-x cpl
                    (xw :mem addr val x86)))
                  (mv-nth
                   1
                   (ia32e-la-to-pa-page-directory
                    lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86))))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-directory)
                  (not
                   addr-range-1
                   ia32e-la-to-pa-page-directory-entry-validp)))

(defrule mv-nth-1-no-error-ia32e-la-to-pa-page-directory-2M-pages-with-disjoint-wm-low-64
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
                 lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)
                (equal page-directory-entry-addr
                       (page-directory-entry-addr lin-addr page-directory-base-addr))
                (equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  page-directory-entry) 1)
                (disjoint-p
                 (addr-range 8 addr)
                 (addr-range 8 page-directory-entry-addr))
                (integerp addr))

           (equal (mv-nth
                   1
                   (ia32e-la-to-pa-page-directory
                    lin-addr page-directory-base-addr wp smep nxe r-w-x cpl
                    (wm-low-64 addr val x86)))
                  (mv-nth
                   1
                   (ia32e-la-to-pa-page-directory
                    lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86))))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-directory)
                  (not
                   ia32e-la-to-pa-page-directory-entry-validp)))

(defrule mv-nth-2-no-error-ia32e-la-to-pa-page-directory-2M-pages
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
                 lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)

                (equal page-directory-entry-addr
                       (page-directory-entry-addr lin-addr page-directory-base-addr))
                (equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  page-directory-entry) 1)

                (equal accessed (ia32e-pde-2MB-page-slice :pde-a page-directory-entry))
                (equal dirty (ia32e-pde-2MB-page-slice :pde-d page-directory-entry))
                (equal accessed-entry
                       (if (equal accessed 0)
                           ;; (!ia32e-pde-2MB-page-slice :pde-a 1 page-directory-entry)
                           (set-accessed-bit page-directory-entry)
                         page-directory-entry))
                (equal dirty-entry
                       (if (and (equal dirty 0)
                                (equal r-w-x :w))
                           ;; (!ia32e-pde-2MB-page-slice :pde-d 1 accessed-entry)
                           (set-dirty-bit accessed-entry)
                         accessed-entry))
                (equal dirty-x86
                       (if (or (equal accessed 0)
                               (and (equal dirty 0)
                                    (equal r-w-x :w)))
                           (wm-low-64 page-directory-entry-addr dirty-entry x86)
                         x86)))

           (equal (mv-nth
                   2
                   (ia32e-la-to-pa-page-directory
                    lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86))
                  dirty-x86))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-directory)
                  (not)))

;; 4K pages:

(defrule mv-nth-0-no-error-ia32e-la-to-pa-page-directory-4K-pages-with-disjoint-!memi
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
                 lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)
                (equal page-directory-entry-addr
                       (page-directory-entry-addr lin-addr page-directory-base-addr))
                (equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  page-directory-entry) 0)
                ;; For ia32e-la-to-pa-page-table:
                (equal page-table-base-addr
                       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry)
                            12))
                (equal page-table-entry-addr
                       (page-table-entry-addr lin-addr page-table-base-addr))
                (pairwise-disjoint-p-aux
                 (addr-range 1 addr)
                 (translation-governing-addresses-for-page-directory
                  lin-addr page-directory-base-addr x86))
                (integerp addr))
           (equal (mv-nth
                   0
                   (ia32e-la-to-pa-page-directory
                    lin-addr page-directory-base-addr wp smep nxe r-w-x cpl
                    (xw :mem addr val x86)))
                  nil))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-directory)
                  (not
                   addr-range-1
                   ia32e-la-to-pa-page-table-entry-validp)))

(defrule mv-nth-0-no-error-ia32e-la-to-pa-page-directory-4K-pages-with-disjoint-wm-low-64
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
                 lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)
                (equal page-directory-entry-addr
                       (page-directory-entry-addr lin-addr page-directory-base-addr))
                (equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  page-directory-entry) 0)
                ;; For ia32e-la-to-pa-page-table:
                (equal page-table-base-addr
                       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry)
                            12))
                (equal page-table-entry-addr
                       (page-table-entry-addr lin-addr page-table-base-addr))

                (pairwise-disjoint-p-aux
                 (addr-range 8 addr)
                 (translation-governing-addresses-for-page-directory
                  lin-addr page-directory-base-addr x86))
                (integerp addr))
           (equal (mv-nth
                   0
                   (ia32e-la-to-pa-page-directory
                    lin-addr page-directory-base-addr wp smep nxe r-w-x cpl
                    (wm-low-64 addr val x86)))
                  nil))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-directory)
                  (not
                   ia32e-la-to-pa-page-table-entry-validp)))

(defrule mv-nth-1-no-error-ia32e-la-to-pa-page-directory-4K-pages
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
                 lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)
                (equal page-directory-entry-addr
                       (page-directory-entry-addr lin-addr page-directory-base-addr))
                (equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  page-directory-entry) 0))

           (equal (mv-nth
                   1
                   (ia32e-la-to-pa-page-directory
                    lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86))
                  (mv-nth
                   1
                   (ia32e-la-to-pa-page-table
                    lin-addr
                    (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12)
                    (ia32e-page-tables-slice :u/s page-directory-entry)
                    wp smep nxe r-w-x cpl x86))))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-directory)
                  (not)))

(defrule mv-nth-1-no-error-ia32e-la-to-pa-page-directory-4K-pages-with-disjoint-!memi
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
                 lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)
                (equal page-directory-entry-addr
                       (page-directory-entry-addr lin-addr page-directory-base-addr))
                (equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  page-directory-entry) 0)
                ;; For ia32e-la-to-pa-page-table:
                (equal page-table-base-addr
                       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry)
                            12))
                (equal page-table-entry-addr
                       (page-table-entry-addr lin-addr page-table-base-addr))
                (pairwise-disjoint-p-aux
                 (addr-range 1 addr)
                 (translation-governing-addresses-for-page-directory
                  lin-addr page-directory-base-addr x86))
                (integerp addr))

           (equal (mv-nth
                   1
                   (ia32e-la-to-pa-page-directory
                    lin-addr page-directory-base-addr wp smep nxe r-w-x cpl
                    (xw :mem addr val x86)))
                  (mv-nth
                   1
                   (ia32e-la-to-pa-page-directory
                    lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86))))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-directory)
                  (not
                   mv-nth-1-no-error-ia32e-la-to-pa-page-table
                   addr-range-1
                   ia32e-la-to-pa-page-table-entry-validp)))

(defrule mv-nth-1-no-error-ia32e-la-to-pa-page-directory-4K-pages-with-disjoint-wm-low-64
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
                 lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)
                (equal page-directory-entry-addr
                       (page-directory-entry-addr lin-addr page-directory-base-addr))
                (equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  page-directory-entry) 0)
                ;; For ia32e-la-to-pa-page-table:
                (equal page-table-base-addr
                       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry)
                            12))
                (equal page-table-entry-addr
                       (page-table-entry-addr lin-addr page-table-base-addr))
                (pairwise-disjoint-p-aux
                 (addr-range 8 addr)
                 (translation-governing-addresses-for-page-directory
                  lin-addr page-directory-base-addr x86))
                (integerp addr))

           (equal (mv-nth
                   1
                   (ia32e-la-to-pa-page-directory
                    lin-addr page-directory-base-addr wp smep nxe r-w-x cpl
                    (wm-low-64 addr val x86)))
                  (mv-nth
                   1
                   (ia32e-la-to-pa-page-directory
                    lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86))))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-directory)
                  (not
                   ia32e-la-to-pa-page-table-entry-validp)))

(defrule mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
                 lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)
                (equal page-directory-entry-addr
                       (page-directory-entry-addr lin-addr page-directory-base-addr))
                (equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  page-directory-entry) 0)

                (equal accessed (ia32e-page-tables-slice :a page-directory-entry))
                (equal accessed-entry
                       (if (equal accessed 0)
                           ;; (!ia32e-page-tables-slice :a 1 page-directory-entry)
                           (set-accessed-bit page-directory-entry)
                         page-directory-entry)))

           (equal (mv-nth
                   2
                   (ia32e-la-to-pa-page-directory
                    lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86))
                  (let* ((page-table-x86
                          (mv-nth
                           2
                           (ia32e-la-to-pa-page-table
                            lin-addr
                            (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12)
                            (ia32e-page-tables-slice :u/s page-directory-entry)
                            wp smep nxe r-w-x cpl x86))))
                    (if (equal accessed 0)
                        (wm-low-64 page-directory-entry-addr accessed-entry page-table-x86)
                      page-table-x86))))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-directory)
                  (not
                   ia32e-la-to-pa-page-table-entry-validp)))

;; ......................................................................
;; Reading page-directory-entry-addr again using rm-low-64:
;; ......................................................................

;; 2M pages:

(defruled rm-low-64-and-page-directory-2M-pages
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
                 lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)
                (equal page-directory-entry-addr
                       (page-directory-entry-addr lin-addr page-directory-base-addr))
                (equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  page-directory-entry) 1)
                (physical-address-p page-directory-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 page-directory-base-addr) 0)
                (x86p x86))
           (equal (rm-low-64 page-directory-entry-addr
                             (mv-nth
                              2
                              (ia32e-la-to-pa-page-directory
                               lin-addr page-directory-base-addr wp smep nxe r-w-x
                               cpl x86)))
                  (cond
                   ( ;; Accessed and dirty bits are set.
                    (and (equal (ia32e-page-tables-slice :a page-directory-entry) 1)
                         (equal (ia32e-page-tables-slice :d page-directory-entry) 1))
                    (rm-low-64 page-directory-entry-addr x86))

                   ( ;; Accessed bit is set and dirty bit is clear and
                    ;; memory write is being done.
                    (and (equal (ia32e-page-tables-slice :a page-directory-entry) 1)
                         (equal (ia32e-page-tables-slice :d page-directory-entry) 0)
                         (equal r-w-x :w))
                    ;; (!ia32e-page-tables-slice :d 1 (rm-low-64 page-directory-entry-addr x86))
                    (set-dirty-bit (rm-low-64 page-directory-entry-addr x86)))

                   ( ;; Accessed bit is set and dirty bit is clear and
                    ;; memory write is not being done.
                    (and (equal (ia32e-page-tables-slice :a page-directory-entry) 1)
                         (equal (ia32e-page-tables-slice :d page-directory-entry) 0)
                         (not (equal r-w-x :w)))
                    (rm-low-64 page-directory-entry-addr x86))

                   ( ;; Accessed and dirty bits are clear and memory
                    ;; write is being done.
                    (and (equal (ia32e-page-tables-slice :a page-directory-entry) 0)
                         (equal (ia32e-page-tables-slice :d page-directory-entry) 0)
                         (equal r-w-x :w))
                    ;; (!ia32e-page-tables-slice
                    ;;  :d 1
                    ;;  (!ia32e-page-tables-slice
                    ;;   :a 1
                    ;;   (rm-low-64 page-directory-entry-addr x86)))
                    (set-dirty-bit (set-accessed-bit (rm-low-64 page-directory-entry-addr x86))))

                   ( ;; Accessed bit and dirty bits are clear and memory
                    ;; write is not being done.
                    (and (equal (ia32e-page-tables-slice :a page-directory-entry) 0)
                         (equal (ia32e-page-tables-slice :d page-directory-entry) 0)
                         (not (equal r-w-x :w)))
                    ;; (!ia32e-page-tables-slice :a 1 (rm-low-64 page-directory-entry-addr x86))
                    (set-accessed-bit (rm-low-64 page-directory-entry-addr x86)))

                   (t
                    ;; This shouldn't be reached.
                    (rm-low-64 page-directory-entry-addr
                               (mv-nth
                                2
                                (ia32e-la-to-pa-page-directory
                                 lin-addr page-directory-base-addr wp smep nxe r-w-x
                                 cpl x86)))))))

  :do-not '(preprocess)
  :in-theory (e/d ()
                  (not
                   ia32e-la-to-pa-page-directory-entry-validp
                   ia32e-la-to-pa-page-table-entry-validp
                   unsigned-byte-p
                   signed-byte-p)))

;; 4K pages:

(defruled rm-low-64-and-page-directory-4K-pages
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
                 lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)
                (equal page-directory-entry-addr
                       (page-directory-entry-addr lin-addr page-directory-base-addr))
                (equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  page-directory-entry) 0)

                (equal page-table-base-addr
                       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
                (equal page-table-entry-addr
                       (page-table-entry-addr lin-addr page-table-base-addr))

                (pairwise-disjoint-p
                 (translation-governing-addresses-for-page-directory
                  lin-addr page-directory-base-addr x86))
                (physical-address-p page-directory-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 page-directory-base-addr) 0)
                (x86p x86))

           (equal (rm-low-64 page-directory-entry-addr
                             (mv-nth
                              2
                              (ia32e-la-to-pa-page-directory
                               lin-addr page-directory-base-addr wp smep nxe r-w-x
                               cpl x86)))
                  (cond
                   ((equal (ia32e-page-tables-slice :a page-directory-entry) 0)
                    ;; (!ia32e-page-tables-slice
                    ;;  :a 1 (rm-low-64 page-directory-entry-addr x86))
                    (set-accessed-bit (rm-low-64 page-directory-entry-addr x86)))
                   ((equal (ia32e-page-tables-slice :a page-directory-entry) 1)
                    (rm-low-64 page-directory-entry-addr x86)))))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (e/d ()
                           (ia32e-la-to-pa-page-directory-entry-validp
                            not
                            member-p-cons
                            disjoint-p-cons
                            mv-nth-1-no-error-ia32e-la-to-pa-page-table
                            ;; mv-nth-2-no-error-ia32e-la-to-pa-page-table
                            ia32e-la-to-pa-page-table-entry-validp
                            unsigned-byte-p
                            signed-byte-p)))))

;; ......................................................................
;; !memi and state after data structure walk WoW theorem:
;; ......................................................................

;; 2M pages:

(defrule disjoint-!memi-mv-nth-2-no-error-ia32e-la-to-pa-page-directory-2M-pages
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
                 lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)
                (equal page-directory-entry-addr
                       (page-directory-entry-addr lin-addr page-directory-base-addr))
                (equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  page-directory-entry) 1)

                (disjoint-p
                 (addr-range 1 addr)
                 (addr-range 8 page-directory-entry-addr))
                (integerp addr))
           (equal
            (mv-nth
             2
             (ia32e-la-to-pa-page-directory
              lin-addr page-directory-base-addr wp smep nxe r-w-x cpl
              (xw :mem addr val x86)))
            (xw :mem
                addr val
                (mv-nth
                 2
                 (ia32e-la-to-pa-page-directory
                  lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)))))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-directory)
                  (not
                   ia32e-la-to-pa-page-directory-entry-validp
                   addr-range-1)))

;; 4K pages:

(defrule disjoint-!memi-mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
                 lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)
                (equal page-directory-entry-addr
                       (page-directory-entry-addr lin-addr page-directory-base-addr))
                (equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  page-directory-entry) 0)

                ;; For ia32e-la-to-pa-page-table:
                (equal page-table-base-addr
                       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
                (equal page-table-entry-addr
                       (page-table-entry-addr lin-addr page-table-base-addr))

                (pairwise-disjoint-p-aux
                 (addr-range 1 addr)
                 (translation-governing-addresses-for-page-directory
                  lin-addr page-directory-base-addr x86))
                (integerp addr))
           (equal
            (mv-nth
             2
             (ia32e-la-to-pa-page-directory
              lin-addr page-directory-base-addr wp smep nxe r-w-x cpl
              (xw :mem addr val x86)))
            (xw :mem
                addr val
                (mv-nth
                 2
                 (ia32e-la-to-pa-page-directory
                  lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)))))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-directory
                   wm-low-64 wm-low-32)
                  (not
                   mv-nth-1-no-error-ia32e-la-to-pa-page-directory-2M-pages
                   mv-nth-2-no-error-ia32e-la-to-pa-page-table
                   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-2M-pages
                   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages
                   ia32e-la-to-pa-page-table-entry-validp)))

;; ......................................................................
;; Reading addresses disjoint from page-directory-entry-addr after walking
;; the page directory:
;; ......................................................................

;; 2M pages:

(defrule disjoint-memi-read-mv-nth-2-no-error-ia32e-la-to-pa-page-directory-2M-pages
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
                 lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)
                (equal page-directory-entry-addr
                       (page-directory-entry-addr lin-addr page-directory-base-addr))
                (equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  page-directory-entry) 1)

                (disjoint-p
                 (addr-range 1 addr)
                 (addr-range 8 page-directory-entry-addr)))
           (equal
            (xr :mem
                addr
                (mv-nth
                 2
                 (ia32e-la-to-pa-page-directory
                  lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)))
            (xr :mem addr x86)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-directory)
                  (not
                   addr-range-1)))

(defrule disjoint-rm-low-64-read-mv-nth-2-no-error-ia32e-la-to-pa-page-directory-2M-pages
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
                 lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)
                (equal page-directory-entry-addr
                       (page-directory-entry-addr lin-addr page-directory-base-addr))
                (equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  page-directory-entry) 1)

                (disjoint-p
                 (addr-range 8 addr)
                 (addr-range 8 page-directory-entry-addr))
                (integerp addr))
           (equal
            (rm-low-64
             addr
             (mv-nth
              2
              (ia32e-la-to-pa-page-directory
               lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)))
            (rm-low-64 addr x86)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-directory)
                  (not)))

(defrule disjoint-rm-low-32-read-mv-nth-2-no-error-ia32e-la-to-pa-page-directory-2M-pages
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
                 lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)
                (equal page-directory-entry-addr
                       (page-directory-entry-addr lin-addr page-directory-base-addr))
                (equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  page-directory-entry) 1)

                (disjoint-p
                 (addr-range 4 addr)
                 (addr-range 8 page-directory-entry-addr))
                (integerp addr))
           (equal
            (rm-low-32
             addr
             (mv-nth
              2
              (ia32e-la-to-pa-page-directory
               lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)))
            (rm-low-32 addr x86)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-directory
                   wm-low-64)
                  (not)))

;; 4K pages:

(defrule disjoint-memi-read-mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
                 lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)
                (equal page-directory-entry-addr
                       (page-directory-entry-addr lin-addr page-directory-base-addr))
                (equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  page-directory-entry) 0)

                ;; For ia32e-la-to-pa-page-table:
                (equal page-table-base-addr
                       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
                (equal page-table-entry-addr
                       (page-table-entry-addr lin-addr page-table-base-addr))

                (pairwise-disjoint-p-aux
                 (addr-range 1 addr)
                 (translation-governing-addresses-for-page-directory
                  lin-addr page-directory-base-addr x86)))
           (equal
            (xr :mem
                addr
                (mv-nth
                 2
                 (ia32e-la-to-pa-page-directory
                  lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)))
            (xr :mem addr x86)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-directory
                   wm-low-64 wm-low-32)
                  (not
                   disjoint-memi-read-mv-nth-2-no-error-ia32e-la-to-pa-page-directory-2M-pages
                   disjoint-memi-read-mv-nth-2-no-error-ia32e-la-to-pa-page-directory-2M-pages
                   disjoint-rm-low-64-read-mv-nth-2-no-error-ia32e-la-to-pa-page-directory-2M-pages
                   disjoint-rm-low-32-read-mv-nth-2-no-error-ia32e-la-to-pa-page-directory-2M-pages
                   mv-nth-2-no-error-ia32e-la-to-pa-page-table
                   ia32e-la-to-pa-page-table-entry-validp
                   mv-nth-1-no-error-ia32e-la-to-pa-page-table)))

(defrule disjoint-rm-low-64-read-mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
                 lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)
                (equal page-directory-entry-addr
                       (page-directory-entry-addr lin-addr page-directory-base-addr))
                (equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  page-directory-entry) 0)

                ;; For ia32e-la-to-pa-page-table:
                (equal page-table-base-addr
                       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
                (equal page-table-entry-addr
                       (page-table-entry-addr lin-addr page-table-base-addr))

                (pairwise-disjoint-p-aux
                 (addr-range 8 addr)
                 (translation-governing-addresses-for-page-directory
                  lin-addr page-directory-base-addr x86))

                (integerp addr))
           (equal
            (rm-low-64
             addr
             (mv-nth
              2
              (ia32e-la-to-pa-page-directory
               lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)))
            (rm-low-64 addr x86)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-directory)
                  (not
                   disjoint-rm-low-64-read-mv-nth-2-no-error-ia32e-la-to-pa-page-directory-2M-pages
                   disjoint-rm-low-32-read-mv-nth-2-no-error-ia32e-la-to-pa-page-directory-2M-pages
                   mv-nth-2-no-error-ia32e-la-to-pa-page-table
                   ia32e-la-to-pa-page-table-entry-validp
                   mv-nth-1-no-error-ia32e-la-to-pa-page-table)))

(defrule disjoint-rm-low-32-read-mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
                 lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)
                (equal page-directory-entry-addr
                       (page-directory-entry-addr lin-addr page-directory-base-addr))
                (equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  page-directory-entry) 0)

                ;; For ia32e-la-to-pa-page-table:
                (equal page-table-base-addr
                       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
                (equal page-table-entry-addr
                       (page-table-entry-addr lin-addr page-table-base-addr))

                (pairwise-disjoint-p-aux
                 (addr-range 4 addr)
                 (translation-governing-addresses-for-page-directory
                  lin-addr page-directory-base-addr x86))

                (integerp addr))
           (equal
            (rm-low-32
             addr
             (mv-nth
              2
              (ia32e-la-to-pa-page-directory
               lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)))
            (rm-low-32 addr x86)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-directory
                   wm-low-64)
                  (not
                   disjoint-rm-low-64-read-mv-nth-2-no-error-ia32e-la-to-pa-page-directory-2M-pages
                   disjoint-rm-low-32-read-mv-nth-2-no-error-ia32e-la-to-pa-page-directory-2M-pages
                   mv-nth-2-no-error-ia32e-la-to-pa-page-table
                   ia32e-la-to-pa-page-table-entry-validp
                   mv-nth-1-no-error-ia32e-la-to-pa-page-table)))

;; ......................................................................
;; Theorems that state that the validity of the page directory entry
;; is preserved when writes are done to disjoint addresses or :a/:d
;; are set:
;; ......................................................................

;; 2M pages:

(defrule page-directory-entry-with-disjoint-!memi-still-valid-ia32e-la-to-pa-page-directory-2M-pages
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
                 lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)
                (equal page-directory-entry-addr
                       (page-directory-entry-addr lin-addr page-directory-base-addr))
                (equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  page-directory-entry) 1)

                (disjoint-p (addr-range 1 addr)
                            (addr-range 8 page-directory-entry-addr)))

           (ia32e-la-to-pa-page-directory-entry-validp
            lin-addr page-directory-base-addr wp smep nxe r-w-x cpl
            (xw :mem addr val x86)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-directory)
                  (not
                   addr-range-1
                   ia32e-la-to-pa-page-table-entry-validp
                   unsigned-byte-p
                   signed-byte-p)))

(defrule page-directory-entry-with-disjoint-wm-low-64-still-valid-ia32e-la-to-pa-page-directory-2M-pages
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
                 lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)
                (equal page-directory-entry-addr
                       (page-directory-entry-addr lin-addr page-directory-base-addr))
                (equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  page-directory-entry) 1)

                (disjoint-p (addr-range 8 addr)
                            (addr-range 8 page-directory-entry-addr))

                (integerp addr)
                (physical-address-p page-directory-base-addr)
                (x86p x86))

           (ia32e-la-to-pa-page-directory-entry-validp
            lin-addr page-directory-base-addr wp smep nxe r-w-x cpl
            (wm-low-64 addr val x86)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-directory)
                  (not
                   ia32e-la-to-pa-page-table-entry-validp
                   unsigned-byte-p
                   signed-byte-p)))

(defrule page-directory-entry-with-accessed-bit-set-still-valid-ia32e-la-to-pa-page-directory-2M-pages
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
                 lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)
                (equal page-directory-entry-addr
                       (page-directory-entry-addr lin-addr page-directory-base-addr))
                (equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  page-directory-entry) 1)
                (physical-address-p page-directory-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 page-directory-base-addr) 0)
                (x86p x86))

           (ia32e-la-to-pa-page-directory-entry-validp
            lin-addr page-directory-base-addr wp smep nxe r-w-x cpl
            (wm-low-64
             page-directory-entry-addr
             ;; (!ia32e-page-tables-slice :a 1 page-directory-entry)
             ;; (logior 32 (logand 18446744073709551583 page-directory-entry))
             (set-accessed-bit page-directory-entry)
             x86)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-directory)
                  (not
                   ia32e-la-to-pa-page-table-entry-validp
                   unsigned-byte-p
                   signed-byte-p)))

(defrule page-directory-entry-with-dirty-bit-set-still-valid-ia32e-la-to-pa-page-directory-2M-pages
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
                 lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)
                (equal page-directory-entry-addr
                       (page-directory-entry-addr lin-addr page-directory-base-addr))
                (equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  page-directory-entry) 1)
                (physical-address-p page-directory-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 page-directory-base-addr) 0)
                (x86p x86))

           (ia32e-la-to-pa-page-directory-entry-validp
            lin-addr page-directory-base-addr wp smep nxe r-w-x cpl
            (wm-low-64
             page-directory-entry-addr
             ;; (!ia32e-page-tables-slice :d 1 page-directory-entry)
             ;; (logior 64 (logand 18446744073709551551 page-directory-entry))
             (set-dirty-bit page-directory-entry)
             x86)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-directory)
                  (not
                   ia32e-la-to-pa-page-table-entry-validp
                   unsigned-byte-p
                   signed-byte-p)))

(defrule page-directory-entry-with-accessed-and-dirty-bits-set-still-valid-ia32e-la-to-pa-page-directory-2M-pages
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
                 lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)
                (equal page-directory-entry-addr
                       (page-directory-entry-addr lin-addr page-directory-base-addr))
                (equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  page-directory-entry) 1)
                (physical-address-p page-directory-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 page-directory-base-addr) 0)
                (x86p x86))

           (ia32e-la-to-pa-page-directory-entry-validp
            lin-addr page-directory-base-addr wp smep nxe r-w-x cpl
            (wm-low-64
             page-directory-entry-addr
             ;; (!ia32e-page-tables-slice :d 1 (!ia32e-page-tables-slice :a 1 page-directory-entry))
             ;; (logior
             ;;  64
             ;;  (logand
             ;;   18446744073709551551
             ;;   (logior 32 (logand 18446744073709551583 page-directory-entry))))
             (set-dirty-bit (set-accessed-bit page-directory-entry))
             x86)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-directory)
                  (not
                   ia32e-la-to-pa-page-table-entry-validp
                   unsigned-byte-p
                   signed-byte-p)))

;; 4K pages:

(defrule page-directory-entry-with-accessed-bit-set-still-valid-ia32e-la-to-pa-page-directory-4K-pages
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
                 lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)
                (equal page-directory-entry-addr
                       (page-directory-entry-addr lin-addr page-directory-base-addr))
                (equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps page-directory-entry) 0)
                (equal page-table-base-addr
                       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
                (equal page-table-entry-addr
                       (page-table-entry-addr lin-addr page-table-base-addr))
                (pairwise-disjoint-p
                 (translation-governing-addresses-for-page-directory
                  lin-addr page-directory-base-addr x86))
                (physical-address-p page-directory-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 page-directory-base-addr) 0)
                (x86p x86))

           (ia32e-la-to-pa-page-directory-entry-validp
            lin-addr page-directory-base-addr wp smep nxe r-w-x cpl
            (wm-low-64
             page-directory-entry-addr
             ;; (!ia32e-page-tables-slice :a 1 page-directory-entry)
             ;; (logior 32 (logand 18446744073709551583 page-directory-entry))
             (set-accessed-bit page-directory-entry)
             x86)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-directory)
                  (not
                   mv-nth-2-no-error-ia32e-la-to-pa-page-table
                   mv-nth-1-no-error-ia32e-la-to-pa-page-table
                   ia32e-la-to-pa-page-table-entry-validp
                   unsigned-byte-p
                   signed-byte-p)))

(defrule page-directory-entry-with-dirty-bit-set-still-valid-ia32e-la-to-pa-page-directory-4K-pages
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
                 lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)
                (equal page-directory-entry-addr
                       (page-directory-entry-addr lin-addr page-directory-base-addr))
                (equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps page-directory-entry) 0)
                (equal page-table-base-addr
                       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
                (equal page-table-entry-addr
                       (page-table-entry-addr lin-addr page-table-base-addr))
                (pairwise-disjoint-p
                 (translation-governing-addresses-for-page-directory
                  lin-addr page-directory-base-addr x86))
                (physical-address-p page-directory-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 page-directory-base-addr) 0)
                (x86p x86))

           (ia32e-la-to-pa-page-directory-entry-validp
            lin-addr page-directory-base-addr wp smep nxe r-w-x cpl
            (wm-low-64
             page-directory-entry-addr
             ;; (!ia32e-page-tables-slice :d 1 page-directory-entry)
             ;; (logior 64 (logand 18446744073709551551 page-directory-entry))
             (set-dirty-bit page-directory-entry)
             x86)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-directory)
                  (not
                   mv-nth-2-no-error-ia32e-la-to-pa-page-table
                   mv-nth-1-no-error-ia32e-la-to-pa-page-table
                   ia32e-la-to-pa-page-table-entry-validp
                   unsigned-byte-p
                   signed-byte-p)))

(defrule page-directory-entry-with-accessed-and-dirty-bits-set-still-valid-ia32e-la-to-pa-page-directory-4K-pages
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
                 lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)
                (equal page-directory-entry-addr
                       (page-directory-entry-addr lin-addr page-directory-base-addr))
                (equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  page-directory-entry) 0)
                (equal page-table-base-addr
                       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
                (equal page-table-entry-addr
                       (page-table-entry-addr lin-addr page-table-base-addr))
                (pairwise-disjoint-p
                 (translation-governing-addresses-for-page-directory
                  lin-addr page-directory-base-addr x86))
                (physical-address-p page-directory-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 page-directory-base-addr) 0)
                (x86p x86))

           (ia32e-la-to-pa-page-directory-entry-validp
            lin-addr page-directory-base-addr wp smep nxe r-w-x cpl
            (wm-low-64
             page-directory-entry-addr
             ;; (!ia32e-page-tables-slice :d 1 (!ia32e-page-tables-slice :a 1 page-directory-entry))
             ;; (logior
             ;;  64
             ;;  (logand
             ;;   18446744073709551551
             ;;   (logior 32 (logand 18446744073709551583 page-directory-entry))))
             (set-dirty-bit (set-accessed-bit page-directory-entry))
             x86)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-directory)
                  (not
                   ia32e-la-to-pa-page-table-entry-validp
                   mv-nth-2-no-error-ia32e-la-to-pa-page-table
                   mv-nth-1-no-error-ia32e-la-to-pa-page-table
                   unsigned-byte-p
                   signed-byte-p)))

(defrule page-directory-entry-with-disjoint-!memi-still-valid-ia32e-la-to-pa-page-directory-4K-pages
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
                 lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)
                (equal page-directory-entry-addr
                       (page-directory-entry-addr lin-addr page-directory-base-addr))
                (equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  page-directory-entry) 0)
                (equal page-table-base-addr
                       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
                (equal page-table-entry-addr
                       (page-table-entry-addr lin-addr page-table-base-addr))

                (pairwise-disjoint-p-aux
                 (addr-range 1 addr)
                 (translation-governing-addresses-for-page-directory
                  lin-addr page-directory-base-addr x86))

                (integerp addr)
                (physical-address-p page-directory-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 page-directory-base-addr) 0)
                (x86p x86))

           (ia32e-la-to-pa-page-directory-entry-validp
            lin-addr page-directory-base-addr wp smep nxe r-w-x cpl
            (xw :mem addr val x86)))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (e/d ()
                           (ia32e-la-to-pa-page-table-entry-validp
                            mv-nth-2-no-error-ia32e-la-to-pa-page-table
                            mv-nth-1-no-error-ia32e-la-to-pa-page-table
                            not
                            addr-range-1
                            unsigned-byte-p
                            signed-byte-p)))))

(defrule page-directory-entry-with-disjoint-wm-low-64-still-valid-ia32e-la-to-pa-page-directory-4K-pages
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
                 lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)
                (equal page-directory-entry-addr
                       (page-directory-entry-addr lin-addr page-directory-base-addr))
                (equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  page-directory-entry) 0)

                (equal page-table-base-addr
                       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
                (equal page-table-entry-addr
                       (page-table-entry-addr lin-addr page-table-base-addr))

                (pairwise-disjoint-p-aux
                 (addr-range 8 addr)
                 (translation-governing-addresses-for-page-directory
                  lin-addr page-directory-base-addr x86))

                (integerp addr)
                (physical-address-p page-directory-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 page-directory-base-addr) 0)
                (x86p x86))

           (ia32e-la-to-pa-page-directory-entry-validp
            lin-addr page-directory-base-addr wp smep nxe r-w-x cpl
            (wm-low-64 addr val x86)))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (e/d ()
                           (ia32e-la-to-pa-page-table-entry-validp
                            mv-nth-2-no-error-ia32e-la-to-pa-page-table
                            mv-nth-1-no-error-ia32e-la-to-pa-page-table
                            not
                            unsigned-byte-p
                            signed-byte-p)))))

;; ......................................................................
;; Reading page directory entry from x86 states where :a/:d are set:
;; ......................................................................

;; 2M pages:

(defrule reading-entry-with-accessed-bit-set-ia32e-la-to-pa-page-directory-2M-pages
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
                 lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)
                (equal page-directory-entry-addr
                       (page-directory-entry-addr lin-addr page-directory-base-addr))
                (equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  page-directory-entry) 1)
                (physical-address-p page-directory-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 page-directory-base-addr) 0)
                (x86p x86))

           (equal
            (mv-nth
             1
             (ia32e-la-to-pa-page-directory
              lin-addr page-directory-base-addr wp smep nxe r-w-x cpl
              (wm-low-64
               page-directory-entry-addr
               ;; (!ia32e-page-tables-slice :a 1 page-directory-entry)
               ;; (logior 32 (logand 18446744073709551583 page-directory-entry))
               (set-accessed-bit page-directory-entry)
               x86)))
            (mv-nth
             1
             (ia32e-la-to-pa-page-directory
              lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86))))
  :do-not '(preprocess)
  :in-theory (e/d ()
                  (ia32e-la-to-pa-page-directory-entry-validp
                   mv-nth-2-no-error-ia32e-la-to-pa-page-table
                   mv-nth-1-no-error-ia32e-la-to-pa-page-table
                   not
                   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-2M-pages
                   unsigned-byte-p
                   signed-byte-p)))

(defrule reading-entry-with-dirty-bit-set-ia32e-la-to-pa-page-directory-2M-pages
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
                 lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)
                (equal page-directory-entry-addr
                       (page-directory-entry-addr lin-addr page-directory-base-addr))
                (equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  page-directory-entry) 1)
                (physical-address-p page-directory-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 page-directory-base-addr) 0)
                (x86p x86))

           (equal
            (mv-nth
             1
             (ia32e-la-to-pa-page-directory
              lin-addr page-directory-base-addr wp smep nxe r-w-x cpl
              (wm-low-64
               page-directory-entry-addr
               ;; (!ia32e-page-tables-slice :d 1 page-directory-entry)
               ;; (logior 64 (logand 18446744073709551551 page-directory-entry))
               (set-dirty-bit page-directory-entry)
               x86)))
            (mv-nth
             1
             (ia32e-la-to-pa-page-directory
              lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86))))
  :do-not '(preprocess)
  :in-theory (e/d ()
                  (ia32e-la-to-pa-page-directory-entry-validp
                   mv-nth-2-no-error-ia32e-la-to-pa-page-table
                   mv-nth-1-no-error-ia32e-la-to-pa-page-table
                   not
                   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-2M-pages
                   unsigned-byte-p
                   signed-byte-p)))

(defrule reading-entry-with-accessed-and-dirty-bits-ia32e-la-to-pa-page-directory-2M-pages
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
                 lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)
                (equal page-directory-entry-addr
                       (page-directory-entry-addr lin-addr page-directory-base-addr))
                (equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  page-directory-entry) 1)
                (physical-address-p page-directory-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 page-directory-base-addr) 0)
                (x86p x86))

           (equal
            (mv-nth
             1
             (ia32e-la-to-pa-page-directory
              lin-addr page-directory-base-addr wp smep nxe r-w-x cpl
              (wm-low-64
               page-directory-entry-addr
               ;; (!ia32e-page-tables-slice :d 1 (!ia32e-page-tables-slice :a 1 page-directory-entry))
               ;; (logior
               ;;  64
               ;;  (logand
               ;;   18446744073709551551
               ;;   (logior 32 (logand 18446744073709551583 page-directory-entry))))
               (set-dirty-bit (set-accessed-bit page-directory-entry))
               x86)))
            (mv-nth
             1
             (ia32e-la-to-pa-page-directory
              lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86))))
  :do-not '(preprocess)
  :in-theory (e/d ()
                  (ia32e-la-to-pa-page-directory-entry-validp
                   mv-nth-2-no-error-ia32e-la-to-pa-page-table
                   mv-nth-1-no-error-ia32e-la-to-pa-page-table
                   not
                   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-2M-pages
                   unsigned-byte-p
                   signed-byte-p)))

;; 4K pages:

(defrule reading-entry-with-accessed-bit-set-ia32e-la-to-pa-page-directory-4K-pages
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
                 lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)
                (equal page-directory-entry-addr
                       (page-directory-entry-addr lin-addr page-directory-base-addr))
                (equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  page-directory-entry) 0)
                (equal page-table-base-addr
                       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
                (equal page-table-entry-addr
                       (page-table-entry-addr lin-addr page-table-base-addr))
                (pairwise-disjoint-p
                 (translation-governing-addresses-for-page-directory
                  lin-addr page-directory-base-addr x86))
                (physical-address-p page-directory-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 page-directory-base-addr) 0)
                (x86p x86))

           (equal
            (mv-nth
             1
             (ia32e-la-to-pa-page-directory
              lin-addr page-directory-base-addr wp smep nxe r-w-x cpl
              (wm-low-64
               page-directory-entry-addr
               ;; (!ia32e-page-tables-slice :a 1 page-directory-entry)
               ;; (logior 32 (logand 18446744073709551583 page-directory-entry))
               (set-accessed-bit page-directory-entry)
               x86)))
            (mv-nth
             1
             (ia32e-la-to-pa-page-directory
              lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86))))
  :do-not '(preprocess)
  :in-theory (e/d ()
                  (ia32e-la-to-pa-page-directory-entry-validp
                   mv-nth-1-no-error-ia32e-la-to-pa-page-table
                   mv-nth-2-no-error-ia32e-la-to-pa-page-table
                   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages
                   not
                   unsigned-byte-p
                   signed-byte-p)))

(defrule reading-entry-with-dirty-bit-set-ia32e-la-to-pa-page-directory-4K-pages
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
                 lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)
                (equal page-directory-entry-addr
                       (page-directory-entry-addr lin-addr page-directory-base-addr))
                (equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  page-directory-entry) 0)
                (equal page-table-base-addr
                       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
                (equal page-table-entry-addr
                       (page-table-entry-addr lin-addr page-table-base-addr))
                (pairwise-disjoint-p
                 (translation-governing-addresses-for-page-directory
                  lin-addr page-directory-base-addr x86))
                (physical-address-p page-directory-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 page-directory-base-addr) 0)
                (x86p x86))

           (equal
            (mv-nth
             1
             (ia32e-la-to-pa-page-directory
              lin-addr page-directory-base-addr wp smep nxe r-w-x cpl
              (wm-low-64
               page-directory-entry-addr
               ;; (!ia32e-page-tables-slice :d 1 page-directory-entry)
               ;; (logior 64 (logand 18446744073709551551 page-directory-entry))
               (set-dirty-bit page-directory-entry)
               x86)))
            (mv-nth
             1
             (ia32e-la-to-pa-page-directory
              lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86))))
  :do-not '(preprocess)
  :in-theory (e/d ()
                  (ia32e-la-to-pa-page-directory-entry-validp
                   mv-nth-1-no-error-ia32e-la-to-pa-page-table
                   mv-nth-2-no-error-ia32e-la-to-pa-page-table
                   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages
                   not
                   ia32e-la-to-pa-page-table-entry-validp
                   unsigned-byte-p
                   signed-byte-p)))

(defrule reading-entry-with-accessed-and-dirty-bits-set-ia32e-la-to-pa-page-directory-4K-pages
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
                 lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)
                (equal page-directory-entry-addr
                       (page-directory-entry-addr lin-addr page-directory-base-addr))
                (equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  page-directory-entry) 0)
                (equal page-table-base-addr
                       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
                (equal page-table-entry-addr
                       (page-table-entry-addr lin-addr page-table-base-addr))
                (pairwise-disjoint-p
                 (translation-governing-addresses-for-page-directory
                  lin-addr page-directory-base-addr x86))
                (physical-address-p page-directory-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 page-directory-base-addr) 0)
                (x86p x86))

           (equal
            (mv-nth
             1
             (ia32e-la-to-pa-page-directory
              lin-addr page-directory-base-addr wp smep nxe r-w-x cpl
              (wm-low-64
               page-directory-entry-addr
               ;; (!ia32e-page-tables-slice :d 1 (!ia32e-page-tables-slice :a 1 page-directory-entry))
               ;; (logior
               ;;  64
               ;;  (logand
               ;;   18446744073709551551
               ;;   (logior 32 (logand 18446744073709551583 page-directory-entry))))
               (set-dirty-bit (set-accessed-bit page-directory-entry))
               x86)))
            (mv-nth
             1
             (ia32e-la-to-pa-page-directory
              lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86))))
  :do-not '(preprocess)
  :in-theory (e/d ()
                  (ia32e-la-to-pa-page-directory-entry-validp
                   mv-nth-1-no-error-ia32e-la-to-pa-page-table
                   mv-nth-2-no-error-ia32e-la-to-pa-page-table
                   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages
                   not
                   unsigned-byte-p
                   signed-byte-p)))

;; ......................................................................
;; More theorems about preservation of validity of page directory entries:
;; ......................................................................

;; 2M pages:

(defrule relating-validity-of-two-entries-in-two-x86-states-wrt-page-directory-2M-pages
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
                 lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)
                (equal page-directory-entry-addr
                       (page-directory-entry-addr lin-addr page-directory-base-addr))
                (equal page-directory-entry-1 (rm-low-64 page-directory-entry-addr x86))
                (equal page-directory-entry-2 (rm-low-64 page-directory-entry-addr x86-another))
                (equal (ia32e-pde-2MB-page-slice :pde-ps page-directory-entry-1) 1)
                (ia32e-la-to-pa-page-directory-entry-components-equal-p
                 '2M page-directory-entry-1 page-directory-entry-2))
           (ia32e-la-to-pa-page-directory-entry-validp
            lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86-another))
  :in-theory (e/d
              (ia32e-la-to-pa-page-directory-entry-components-equal-p)
              ()))

(defruled page-directory-components-equal-rm-low-64-of-page-directory-entry-addr-via-page-directory-2M-pages
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
                 lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)
                (equal page-directory-entry-addr
                       (page-directory-entry-addr lin-addr page-directory-base-addr))
                (equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  page-directory-entry) 1)
                (physical-address-p page-directory-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 page-directory-base-addr) 0)
                (x86p x86))
           (ia32e-la-to-pa-page-directory-entry-components-equal-p
            '2M
            (rm-low-64 page-directory-entry-addr x86)
            (rm-low-64
             page-directory-entry-addr
             (mv-nth
              2
              (ia32e-la-to-pa-page-directory
               lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)))))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (e/d (rm-low-64-and-page-directory-2M-pages
                            ia32e-la-to-pa-page-directory-entry-components-equal-p)
                           (ia32e-la-to-pa-page-directory
                            mv-nth-2-no-error-ia32e-la-to-pa-page-table
                            mv-nth-1-no-error-ia32e-la-to-pa-page-table
                            not
                            member-p-cons
                            disjoint-p-cons
                            unsigned-byte-p
                            signed-byte-p)))))

(defrule re-read-entry-still-valid-ia32e-la-to-pa-page-directory-2M-pages

  ;; To prove this kind of theorem, we need the following kinds of key
  ;; lemmas:

  ;; 1. relating-validity-of-two-entries-in-two-x86-states-wrt-page-directory-2M-pages
  ;; 2. page-directory-components-equal-rm-low-64-of-page-directory-entry-addr-via-page-directory-2M-pages
  ;;    (to relieve the components hyp in lemma 1).

  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
                 lin-addr page-directory-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)
                (ia32e-la-to-pa-page-directory-entry-validp
                 lin-addr page-directory-base-addr wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)
                (equal page-directory-entry-addr
                       (page-directory-entry-addr lin-addr page-directory-base-addr))
                (equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  page-directory-entry) 1)
                (physical-address-p page-directory-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 page-directory-base-addr) 0)
                (x86p x86))
           (ia32e-la-to-pa-page-directory-entry-validp
            lin-addr page-directory-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
            (mv-nth
             2
             (ia32e-la-to-pa-page-directory
              lin-addr page-directory-base-addr wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
  :do-not '(preprocess)
  :in-theory (e/d (page-directory-components-equal-rm-low-64-of-page-directory-entry-addr-via-page-directory-2M-pages)
                  (ia32e-la-to-pa-page-directory-entry-validp
                   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-2M-pages
                   mv-nth-2-no-error-ia32e-la-to-pa-page-table
                   mv-nth-1-no-error-ia32e-la-to-pa-page-table
                   not
                   ia32e-la-to-pa-page-table
                   ia32e-la-to-pa-page-table-entry-validp
                   unsigned-byte-p
                   signed-byte-p)))

;; 4K pages:

(defrule relating-validity-of-two-entries-in-two-x86-states-wrt-page-directory-4K-pages
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
                 lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)
                (equal page-directory-entry-addr
                       (page-directory-entry-addr lin-addr page-directory-base-addr))
                (equal page-directory-entry-1 (rm-low-64 page-directory-entry-addr x86))
                (equal page-directory-entry-2 (rm-low-64 page-directory-entry-addr x86-another))
                (equal (ia32e-pde-pg-table-slice :pde-ps page-directory-entry-1) 0)
                (ia32e-la-to-pa-page-directory-entry-components-equal-p
                 '4K page-directory-entry-1 page-directory-entry-2)

                (equal page-table-base-addr-1
                       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry-1) 12))
                (equal page-table-entry-addr
                       (page-table-entry-addr lin-addr page-table-base-addr-1))

                (equal page-table-entry-1 (rm-low-64 page-table-entry-addr x86))
                (equal page-table-entry-2 (rm-low-64 page-table-entry-addr x86-another))

                (ia32e-la-to-pa-page-table-entry-components-equal-p
                 page-table-entry-1 page-table-entry-2))

           (ia32e-la-to-pa-page-directory-entry-validp
            lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86-another))
  :in-theory (e/d
              (ia32e-la-to-pa-page-directory-entry-components-equal-p)
              ()))

(defruled page-directory-components-equal-rm-low-64-of-page-directory-entry-addr-via-page-directory-4K-pages
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
                 lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)
                (equal page-directory-entry-addr
                       (page-directory-entry-addr lin-addr page-directory-base-addr))
                (equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  page-directory-entry) 0)

                (equal page-table-base-addr
                       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
                (equal page-table-entry-addr
                       (page-table-entry-addr lin-addr page-table-base-addr))

                (pairwise-disjoint-p
                 (translation-governing-addresses-for-page-directory
                  lin-addr page-directory-base-addr x86))

                (physical-address-p page-directory-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 page-directory-base-addr) 0)
                (x86p x86))

           (ia32e-la-to-pa-page-directory-entry-components-equal-p
            '4K
            (rm-low-64 page-directory-entry-addr x86)
            (rm-low-64
             page-directory-entry-addr
             (mv-nth
              2
              (ia32e-la-to-pa-page-directory
               lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)))))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (e/d (rm-low-64-and-page-directory-4K-pages)
                           (ia32e-la-to-pa-page-directory-entry-validp
                            mv-nth-2-no-error-ia32e-la-to-pa-page-table
                            mv-nth-1-no-error-ia32e-la-to-pa-page-table
                            mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages
                            not
                            member-p-cons
                            disjoint-p-cons
                            unsigned-byte-p
                            signed-byte-p)))))

(defruled page-table-components-equal-rm-low-64-of-page-table-entry-addr-via-page-directory-4K-pages
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
                 lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)
                (equal page-directory-entry-addr
                       (page-directory-entry-addr lin-addr page-directory-base-addr))
                (equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  page-directory-entry) 0)

                (equal page-table-base-addr
                       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
                (equal page-table-entry-addr
                       (page-table-entry-addr lin-addr page-table-base-addr))

                (pairwise-disjoint-p (translation-governing-addresses-for-page-directory
                                      lin-addr page-directory-base-addr x86))

                (physical-address-p page-directory-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 page-directory-base-addr) 0)
                (x86p x86))

           (ia32e-la-to-pa-page-table-entry-components-equal-p
            (rm-low-64 page-table-entry-addr x86)
            (rm-low-64
             page-table-entry-addr
             (mv-nth
              2
              (ia32e-la-to-pa-page-directory
               lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)))))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (e/d (ia32e-la-to-pa-page-table-entry-components-equal-p
                            mv-nth-2-no-error-ia32e-la-to-pa-page-table
                            mv-nth-1-no-error-ia32e-la-to-pa-page-table
                            page-table-components-equal-rm-low-64-of-table-page-table-entry-addr-via-page-table-4K-pages)
                           (ia32e-la-to-pa-page-directory-entry-validp
                            not
                            member-p-cons
                            disjoint-p-cons
                            unsigned-byte-p
                            signed-byte-p)))))

(defrule re-read-entry-still-valid-ia32e-la-to-pa-page-directory-4K-pages
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
                 lin-addr page-directory-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)
                (ia32e-la-to-pa-page-directory-entry-validp
                 lin-addr page-directory-base-addr wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)
                (equal page-directory-entry-addr
                       (page-directory-entry-addr lin-addr page-directory-base-addr))
                (equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  page-directory-entry) 0)

                (equal page-table-base-addr
                       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
                (equal page-table-entry-addr
                       (page-table-entry-addr lin-addr page-table-base-addr))
                (pairwise-disjoint-p
                 (translation-governing-addresses-for-page-directory
                  lin-addr page-directory-base-addr x86))
                (physical-address-p page-directory-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 page-directory-base-addr) 0)
                (x86p x86))

           (ia32e-la-to-pa-page-directory-entry-validp
            lin-addr page-directory-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
            (mv-nth
             2
             (ia32e-la-to-pa-page-directory
              lin-addr page-directory-base-addr wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (e/d
                       (page-directory-components-equal-rm-low-64-of-page-directory-entry-addr-via-page-directory-4K-pages
                        page-table-components-equal-rm-low-64-of-page-table-entry-addr-via-page-directory-4K-pages)
                       (ia32e-la-to-pa-page-directory-entry-validp
                        member-p-cons
                        disjoint-p-cons
                        not
                        mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages
                        unsigned-byte-p
                        signed-byte-p)))))


;; ......................................................................
;; Two page directory walks --- same directory and table entries:
;; ......................................................................

#||

Various configurations possible with PD and PT are as follows. We
require (very reasonably) that there be no cycles in the paging
data structures --- e.g., a page directory entry should point to a
page table entry that is distinct from itself.

**********
2M Pages:
**********

Scenario (1)

             _____
        ----| PD0 |----
            |_____|
             _____
        ----| PD1 |----
            |_____|

Scenario (2)

             _____
        ----| PD0 |-----
            |_____|  -
             _____  -
        ----| PD1 |-
            |_____|

Scenario (3)

             _____
        ----| PD0 |----
        ----|_____|----

Scenario (4)

             _____
        ----| PD0 |----
        ----|_____|_-

**********
4K Pages:
**********

Scenario (1)

             _____           _____
        ----| PD0 |---- ----| PT0 |----
            |_____|         |_____|
             _____           _____
        ----| PD1 |---- ----| PT1 |----
            |_____|         |_____|

Scenario (2)

             _____           _____
        ----| PD0 |---- ----| PT0 |----
            |_____|     ----|_____|
             _____    --
        ----| PD1 |_--
            |_____|

Scenario (3)

             _____           _____
        ----| PD0 |---- ----| PT0 |----
            |_____|---      |_____|
                     --      _____
                      --    | PT1 |----
                        ----|_____|


Scenario (4)

             _____           _____
        ----| PD0 |---- ----| PT0 |----
        ----|_____|---- ----|_____|----

||#


;; 2M pages:

;; 2M - Scenario (3), (4)
(local
 (defrule two-page-table-walks-ia32e-la-to-pa-page-directory-2M-pages-same-entry
   ;; Two walks of a page directory entry, with same or different
   ;; "input" linear addresses.

   ;; Shilpi: A very rough (and possibly imprecise) proof sketch, which
   ;; I'm leaving as a note to myself:

   ;; For primary pages of a data structure (i.e., pages that can be
   ;; accessed directly from the data structure), the two page walks
   ;; theorem needs the following kinds of key lemmas:

   ;; 1. mv-nth-2-no-error-ia32e-la-to-pa-page-directory-2m-pages
   ;; 2. reading-entry-with-accessed-bit-set-ia32e-la-to-pa-page-directory-2m-pages
   ;; 3. reading-entry-with-dirty-bit-set-ia32e-la-to-pa-page-directory-2m-pages
   ;; 4. reading-entry-with-accessed-and-dirty-bits-ia32e-la-to-pa-page-directory-2m-pages

   ;; The x86 state returned by walking the page directory the first
   ;; time (i.e., (mv-nth 2 (ia32e-la-to-pa-page-directory ...))) can
   ;; be described in terms of the initial x86 state, with or without
   ;; the accessed/dirty bits being set. Lemma 1 is used to rewrite
   ;; this state in the LHS of the theorem.  Four cases result from the
   ;; application of lemma 1: one, no modification of page-directory-entry
   ;; (so LHS = RHS); two, :a set in page-directory-entry; three, :d set in
   ;; page-directory-entry; and four, both :a and :d set in page-directory-entry.
   ;; Lemmas 2, 3, and 4 deal with cases two, three, and four, and
   ;; rewrite the LHS to RHS.

   (implies (and (ia32e-la-to-pa-page-directory-entry-validp
                  lin-addr-1 page-directory-base-addr-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)
                 (ia32e-la-to-pa-page-directory-entry-validp
                  lin-addr-2 page-directory-base-addr-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)
                 (equal page-directory-entry-addr-1
                        (page-directory-entry-addr lin-addr-1 page-directory-base-addr-1))
                 (equal page-directory-entry-addr-2
                        (page-directory-entry-addr lin-addr-2 page-directory-base-addr-2))
                 (equal page-directory-entry-1 (rm-low-64 page-directory-entry-addr-1 x86))
                 (equal (ia32e-page-tables-slice :ps page-directory-entry-1) 1)

                 ;; Same page directory entry.
                 (equal page-directory-entry-addr-2 page-directory-entry-addr-1)

                 (equal (loghead 12 page-directory-base-addr-1) 0)
                 (physical-address-p page-directory-base-addr-1)
                 (canonical-address-p lin-addr-1)
                 (canonical-address-p lin-addr-2)
                 (x86p x86))
            (equal
             (mv-nth
              1
              (ia32e-la-to-pa-page-directory
               lin-addr-1 page-directory-base-addr-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
               (mv-nth
                2
                (ia32e-la-to-pa-page-directory
                 lin-addr-2 page-directory-base-addr-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
             (mv-nth
              1
              (ia32e-la-to-pa-page-directory
               lin-addr-1 page-directory-base-addr-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
               x86))))
   :do-not '(preprocess)
   :in-theory (e/d* ()
                    (ia32e-la-to-pa-page-directory-entry-validp
                     mv-nth-1-no-error-ia32e-la-to-pa-page-directory-2m-pages
                     mv-nth-1-no-error-ia32e-la-to-pa-page-table
                     mv-nth-2-no-error-ia32e-la-to-pa-page-table
                     member-p-cons
                     disjoint-p-cons
                     not
                     unsigned-byte-p
                     signed-byte-p))))

;; 4K pages:

(defruled page-directory-components-equal-rm-low-64-of-page-directory-entry-addr-via-page-table-4K-pages
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
                 lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)
                (equal page-directory-entry-addr
                       (page-directory-entry-addr lin-addr page-directory-base-addr))
                (equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  page-directory-entry) 0)

                (equal page-table-base-addr
                       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
                (equal page-table-entry-addr
                       (page-table-entry-addr lin-addr page-table-base-addr))


                (pairwise-disjoint-p
                 (translation-governing-addresses-for-page-directory
                  lin-addr page-directory-base-addr x86))

                (equal page-table-base-addr
                       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
                (equal u-s-acc (ia32e-page-tables-slice :u/s
                                                        page-directory-entry))

                (physical-address-p page-directory-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 page-directory-base-addr) 0)
                (x86p x86))

           (ia32e-la-to-pa-page-directory-entry-components-equal-p
            '4K
            (rm-low-64 page-directory-entry-addr x86)
            (rm-low-64
             page-directory-entry-addr
             (mv-nth
              2
              (ia32e-la-to-pa-page-table
               lin-addr page-table-base-addr u-s-acc
               wp smep nxe r-w-x cpl x86)))))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (e/d
                       (ia32e-la-to-pa-page-directory-entry-components-equal-p)
                       (ia32e-la-to-pa-page-directory-entry-validp
                        not
                        member-p-cons
                        disjoint-p-cons
                        ia32e-la-to-pa-page-table-entry-validp
                        unsigned-byte-p
                        signed-byte-p)))))

(local
 (defrule re-read-entry-still-page-directory-valid-page-table-4K-pages
   (implies (and (ia32e-la-to-pa-page-directory-entry-validp
                  lin-addr-1 page-directory-base-addr-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)
                 (ia32e-la-to-pa-page-directory-entry-validp
                  lin-addr-2 page-directory-base-addr-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)
                 (equal page-directory-entry-addr-1
                        (page-directory-entry-addr lin-addr-1 page-directory-base-addr-1))
                 (equal page-directory-entry-addr-2
                        (page-directory-entry-addr lin-addr-2 page-directory-base-addr-2))

                 (equal page-directory-entry-addr-2 page-directory-entry-addr-1)

                 (equal page-directory-entry-1 (rm-low-64 page-directory-entry-addr-1 x86))
                 (equal (ia32e-page-tables-slice :ps  page-directory-entry-1) 0)

                 ;; For ia32e-la-to-pa-page-table:
                 (equal page-table-base-addr
                        ;; Same if page directory entry is the same.
                        (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry-1) 12))
                 (equal u-s-acc
                        ;; Same if page directory entry is the same.
                        (ia32e-page-tables-slice :u/s page-directory-entry-1))
                 (equal page-table-entry-addr-1
                        (page-table-entry-addr lin-addr-1 page-table-base-addr))
                 (equal page-table-entry-addr-2
                        (page-table-entry-addr lin-addr-2 page-table-base-addr))

                 ;; Same page table entries.
                 (equal page-table-entry-addr-1 page-table-entry-addr-2)

                 (pairwise-disjoint-p
                  (translation-governing-addresses-for-page-directory
                   lin-addr-1 page-directory-base-addr-1 x86))
                 (pairwise-disjoint-p
                  (translation-governing-addresses-for-page-directory
                   lin-addr-2 page-directory-base-addr-2 x86))

                 (physical-address-p page-directory-base-addr-1)
                 (physical-address-p page-directory-base-addr-2)
                 (canonical-address-p lin-addr-1)
                 (canonical-address-p lin-addr-2)
                 (equal (loghead 12 page-directory-base-addr-1) 0)
                 (equal (loghead 12 page-directory-base-addr-2) 0)
                 (x86p x86))

            (ia32e-la-to-pa-page-directory-entry-validp
             lin-addr-1 page-directory-base-addr-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
             (mv-nth
              2
              (ia32e-la-to-pa-page-table
               lin-addr-2 page-table-base-addr u-s-acc wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))

   :hints (("Goal" :do-not '(preprocess)
            :in-theory (e/d
                        (page-directory-components-equal-rm-low-64-of-page-directory-entry-addr-via-page-table-4K-pages
                         page-table-components-equal-rm-low-64-of-table-page-table-entry-addr-via-page-table-4K-pages
                         re-read-entry-still-valid-ia32e-la-to-pa-page-directory-4K-pages)
                        (ia32e-la-to-pa-page-directory-entry-validp
                         member-p-cons
                         disjoint-p-cons
                         not
                         mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages
                         mv-nth-2-no-error-ia32e-la-to-pa-page-table
                         mv-nth-1-no-error-ia32e-la-to-pa-page-table
                         unsigned-byte-p
                         signed-byte-p))))))

;; 4K - Scenario (3), (4)
(local
 (defrule two-page-table-walks-ia32e-la-to-pa-page-directory-4K-pages-same-entry
   ;; Two walks of a page directory entry, with same or different page table entries

   ;; Shilpi: A very rough (and possibly imprecise) proof sketch, which
   ;; I'm leaving as a note to myself:

   ;; For secondary pages of a data structure (i.e., the pages that
   ;; have to be accessed after one level of indirection), the two page
   ;; walks theorem needs the following kinds of key lemmas:

   ;; 1. mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages
   ;; 2. re-read-entry-still-page-directory-valid-page-table-4K-pages
   ;; 3. reading-entry-with-accessed-bit-set-ia32e-la-to-pa-page-directory-4K-pages
   ;; 4. reading-entry-with-dirty-bit-set-ia32e-la-to-pa-page-directory-4K-pages
   ;; 5. reading-entry-with-accessed-and-dirty-bits-set-ia32e-la-to-pa-page-directory-4K-pages
   ;; 6. mv-nth-1-no-error-ia32e-la-to-pa-page-directory-4K-pages
   ;; 7. page-directory-entry-validp-to-page-table-entry-validp
   ;; 8. two-page-table-walks-ia32e-la-to-pa-page-table

   ;; The x86 state returned by walking the page directory the first
   ;; time (i.e., (mv-nth 2 (ia32e-la-to-pa-page-directory ...))) can
   ;; be described in terms of the x86 state returned after walking the
   ;; page table (i.e., (mv-nth 2 (ia32e-la-to-pa-page-table ...))),
   ;; with or without the accessed/dirty bits being set.  Lemma 1
   ;; rewrites this state in the LHS of the theorem.  Lemma 2
   ;; establishes that the state returned after walking the page table
   ;; satisfies ia32e-la-to-pa-page-directory-entry-validp, and lemmas
   ;; 3, 4, and 5 will rewrite the LHS to the following form:

   ;; (mv-nth 1 (ia32e-la-to-pa-page-directory ....
   ;;           (mv-nth 2 (ia32e-la-to-pa-page-table ...)))

   ;; Using lemmas 2 and 6, the above form will be re-written to:

   ;; (mv-nth 1 (ia32e-la-to-pa-page-table ....
   ;;           (mv-nth 2 (ia32e-la-to-pa-page-table ...)))

   ;; and lemmas 7 and 8 will re-write this to (mv-nth 1
   ;; (ia32e-la-to-pa-page-table ....).

   ;; Lemma 6 will rewrite the RHS to match this LHS.

   (implies
    (and (ia32e-la-to-pa-page-directory-entry-validp
          lin-addr-1 page-directory-base-addr-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)
         (ia32e-la-to-pa-page-directory-entry-validp
          lin-addr-2 page-directory-base-addr-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)
         (equal page-directory-entry-addr-1
                (page-directory-entry-addr lin-addr-1 page-directory-base-addr-1))
         (equal page-directory-entry-addr-2
                (page-directory-entry-addr lin-addr-2 page-directory-base-addr-2))

         ;; Same page directory entry.
         (equal page-directory-entry-addr-2 page-directory-entry-addr-1)

         (equal page-directory-entry-1 (rm-low-64 page-directory-entry-addr-1 x86))
         (equal (ia32e-page-tables-slice :ps  page-directory-entry-1) 0)
         ;; For ia32e-la-to-pa-page-table:
         (equal page-table-base-addr
                ;; Same for the page table entries if page directory entry is the same.
                (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry-1) 12))
         (equal u-s-acc
                ;; Same for the page table entries if page directory entry is the same.
                (ia32e-page-tables-slice :u/s page-directory-entry-1))
         (equal page-table-entry-addr-1
                (page-table-entry-addr lin-addr-1 page-table-base-addr))
         (equal page-table-entry-addr-2
                (page-table-entry-addr lin-addr-2 page-table-base-addr))

         ;; Page table entries may or may not be the same.

         (pairwise-disjoint-p
          (translation-governing-addresses-for-page-directory
           lin-addr-1 page-directory-base-addr-1 x86))
         (pairwise-disjoint-p
          (translation-governing-addresses-for-page-directory
           lin-addr-2 page-directory-base-addr-2 x86))

         (physical-address-p page-directory-base-addr-1)
         (physical-address-p page-directory-base-addr-2)
         (canonical-address-p lin-addr-1)
         (canonical-address-p lin-addr-2)
         (equal (loghead 12 page-directory-base-addr-1) 0)
         (equal (loghead 12 page-directory-base-addr-2) 0)
         (x86p x86))

    (equal
     (mv-nth
      1
      (ia32e-la-to-pa-page-directory
       lin-addr-1 page-directory-base-addr-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
       (mv-nth
        2
        (ia32e-la-to-pa-page-directory
         lin-addr-2 page-directory-base-addr-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
     (mv-nth
      1
      (ia32e-la-to-pa-page-directory
       lin-addr-1 page-directory-base-addr-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
       x86))))
   :cases ((equal page-table-entry-addr-1 page-table-entry-addr-2))
   :do-not '(preprocess)
   :in-theory (e/d
               ()
               (ia32e-la-to-pa-page-directory-entry-validp
                mv-nth-1-no-error-ia32e-la-to-pa-page-table
                mv-nth-2-no-error-ia32e-la-to-pa-page-table
                member-p-cons
                disjoint-p-cons
                not
                unsigned-byte-p
                signed-byte-p))))

;; ......................................................................
;; Two page table walks --- different entries:
;; ......................................................................

;; 2M - Scenario (1), (2)
;; 4K - Scenario (1)
(local
 (defrule two-page-table-walks-ia32e-la-to-pa-page-directory-different-entries
   ;; Two walks of a page directory, all the directory and table
   ;; entries are mutually disjoint.
   (implies (and (ia32e-la-to-pa-page-directory-entry-validp
                  lin-addr-1 page-directory-base-addr-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)
                 (ia32e-la-to-pa-page-directory-entry-validp
                  lin-addr-2 page-directory-base-addr-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)

                 (pairwise-disjoint-p
                  (append
                   (translation-governing-addresses-for-page-directory
                    lin-addr-2 page-directory-base-addr-2 x86)
                   (translation-governing-addresses-for-page-directory
                    lin-addr-1 page-directory-base-addr-1 x86)))

                 (physical-address-p page-directory-base-addr-1)
                 (canonical-address-p lin-addr-1)
                 (equal (loghead 12 page-directory-base-addr-1) 0)

                 (physical-address-p page-directory-base-addr-2)
                 (canonical-address-p lin-addr-2)
                 (equal (loghead 12 page-directory-base-addr-2) 0)

                 (x86p x86))
            (equal
             (mv-nth
              1
              (ia32e-la-to-pa-page-directory
               lin-addr-1 page-directory-base-addr-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
               (mv-nth
                2
                (ia32e-la-to-pa-page-directory
                 lin-addr-2 page-directory-base-addr-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
             (mv-nth
              1
              (ia32e-la-to-pa-page-directory
               lin-addr-1 page-directory-base-addr-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
               x86))))
   :do-not '(preprocess)
   :cases ((and (equal (ia32e-page-tables-slice :ps
                                                (rm-low-64 (part-install (part-select lin-addr-1 :low 21 :high 29)
                                                                         page-directory-base-addr-1
                                                                         :low 3 :high 11)
                                                           x86))
                       1)
                (equal (ia32e-page-tables-slice :ps
                                                (rm-low-64 (part-install (part-select lin-addr-2 :low 21 :high 29)
                                                                         page-directory-base-addr-2
                                                                         :low 3 :high 11) x86))
                       1))

           (and (equal (ia32e-page-tables-slice :ps
                                                (rm-low-64 (part-install (part-select lin-addr-1 :low 21 :high 29)
                                                                         page-directory-base-addr-1
                                                                         :low 3 :high 11)
                                                           x86))
                       1)
                (equal (ia32e-page-tables-slice :ps
                                                (rm-low-64 (part-install (part-select lin-addr-2 :low 21 :high 29)
                                                                         page-directory-base-addr-2
                                                                         :low 3 :high 11) x86))
                       0))

           (and (equal (ia32e-page-tables-slice :ps
                                                (rm-low-64 (part-install (part-select lin-addr-1 :low 21 :high 29)
                                                                         page-directory-base-addr-1
                                                                         :low 3 :high 11)
                                                           x86))
                       0)
                (equal (ia32e-page-tables-slice :ps
                                                (rm-low-64 (part-install (part-select lin-addr-2 :low 21 :high 29)
                                                                         page-directory-base-addr-2
                                                                         :low 3 :high 11) x86))
                       1))

           (and (equal (ia32e-page-tables-slice :ps
                                                (rm-low-64 (part-install (part-select lin-addr-1 :low 21 :high 29)
                                                                         page-directory-base-addr-1
                                                                         :low 3 :high 11)
                                                           x86))
                       0)
                (equal (ia32e-page-tables-slice :ps
                                                (rm-low-64 (part-install (part-select lin-addr-2 :low 21 :high 29)
                                                                         page-directory-base-addr-2
                                                                         :low 3 :high 11) x86))
                       0)))
   :in-theory (e/d ()
                   (ia32e-la-to-pa-page-directory-entry-validp
                    mv-nth-1-no-error-ia32e-la-to-pa-page-table
                    mv-nth-2-no-error-ia32e-la-to-pa-page-table
                    member-p-cons
                    disjoint-p-cons
                    not
                    unsigned-byte-p
                    signed-byte-p))))

(local
 (defrule re-read-entry-still-page-directory-valid-page-table-4K-pages-different-dir-entries
   (implies (and (ia32e-la-to-pa-page-directory-entry-validp
                  lin-addr-1 page-directory-base-addr-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)
                 (ia32e-la-to-pa-page-directory-entry-validp
                  lin-addr-2 page-directory-base-addr-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)
                 (equal page-directory-entry-addr-1
                        (page-directory-entry-addr lin-addr-1 page-directory-base-addr-1))
                 (equal page-directory-entry-addr-2
                        (page-directory-entry-addr lin-addr-2 page-directory-base-addr-2))

                 (equal page-directory-entry-1 (rm-low-64 page-directory-entry-addr-1 x86))
                 (equal (ia32e-page-tables-slice :ps  page-directory-entry-1) 0)
                 (equal page-directory-entry-2 (rm-low-64 page-directory-entry-addr-2 x86))
                 (equal (ia32e-page-tables-slice :ps  page-directory-entry-2) 0)

                 ;; For ia32e-la-to-pa-page-table:
                 (equal page-table-base-addr-1
                        (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry-1) 12))
                 (equal page-table-base-addr-2
                        (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry-2) 12))
                 (equal u-s-acc-2
                        (ia32e-page-tables-slice :u/s page-directory-entry-2))

                 (equal page-table-entry-addr-1
                        (page-table-entry-addr lin-addr-1 page-table-base-addr-1))
                 (equal page-table-entry-addr-2
                        (page-table-entry-addr lin-addr-2 page-table-base-addr-2))

                 ;; Same page table entries.
                 (equal page-table-entry-addr-2 page-table-entry-addr-1)

                 (pairwise-disjoint-p
                  (translation-governing-addresses-for-page-directory
                   lin-addr-1 page-directory-base-addr-1 x86))
                 (pairwise-disjoint-p
                  (translation-governing-addresses-for-page-directory
                   lin-addr-2 page-directory-base-addr-2 x86))

                 (physical-address-p page-directory-base-addr-1)
                 (physical-address-p page-directory-base-addr-2)
                 (canonical-address-p lin-addr-1)
                 (canonical-address-p lin-addr-2)
                 (equal (loghead 12 page-directory-base-addr-1) 0)
                 (equal (loghead 12 page-directory-base-addr-2) 0)
                 (x86p x86))

            (ia32e-la-to-pa-page-directory-entry-validp
             lin-addr-1 page-directory-base-addr-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
             (mv-nth
              2
              (ia32e-la-to-pa-page-table
               lin-addr-2 page-table-base-addr-2 u-s-acc-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))

   :hints (("Goal" :do-not '(preprocess)
            :in-theory (e/d
                        (page-directory-components-equal-rm-low-64-of-page-directory-entry-addr-via-page-table-4K-pages
                         page-table-components-equal-rm-low-64-of-table-page-table-entry-addr-via-page-table-4K-pages
                         re-read-entry-still-valid-ia32e-la-to-pa-page-directory-4K-pages)
                        (ia32e-la-to-pa-page-directory-entry-validp
                         member-p-cons
                         disjoint-p-cons
                         not
                         mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages
                         mv-nth-2-no-error-ia32e-la-to-pa-page-table
                         mv-nth-1-no-error-ia32e-la-to-pa-page-table
                         unsigned-byte-p
                         signed-byte-p))))))

;; 4K - Scenario (2)
(local
 (defrule two-page-table-walks-ia32e-la-to-pa-page-directory-4K-pages-different-dir-entries-same-table-entry
   (implies (and (ia32e-la-to-pa-page-directory-entry-validp
                  lin-addr-1 page-directory-base-addr-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)
                 (ia32e-la-to-pa-page-directory-entry-validp
                  lin-addr-2 page-directory-base-addr-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)
                 (equal page-directory-entry-addr-1
                        (page-directory-entry-addr lin-addr-1 page-directory-base-addr-1))
                 (equal page-directory-entry-addr-2
                        (page-directory-entry-addr lin-addr-2 page-directory-base-addr-2))

                 (equal page-directory-entry-1 (rm-low-64 page-directory-entry-addr-1 x86))
                 (equal (ia32e-page-tables-slice :ps  page-directory-entry-1) 0)
                 (equal page-directory-entry-2 (rm-low-64 page-directory-entry-addr-2 x86))
                 (equal (ia32e-page-tables-slice :ps  page-directory-entry-2) 0)

                 ;; For ia32e-la-to-pa-page-table:
                 (equal page-table-base-addr-1
                        (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry-1) 12))
                 (equal page-table-base-addr-2
                        (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry-2) 12))
                 (equal u-s-acc-2
                        (ia32e-page-tables-slice :u/s page-directory-entry-2))

                 (equal page-table-entry-addr-1
                        (page-table-entry-addr lin-addr-1 page-table-base-addr-1))
                 (equal page-table-entry-addr-2
                        (page-table-entry-addr lin-addr-2 page-table-base-addr-2))

                 ;; Same page table entries.
                 (equal page-table-entry-addr-2 page-table-entry-addr-1)

                 (pairwise-disjoint-p
                  (translation-governing-addresses-for-page-directory
                   lin-addr-1 page-directory-base-addr-1 x86))
                 (pairwise-disjoint-p
                  (translation-governing-addresses-for-page-directory
                   lin-addr-2 page-directory-base-addr-2 x86))

                 (physical-address-p page-directory-base-addr-1)
                 (physical-address-p page-directory-base-addr-2)
                 (canonical-address-p lin-addr-1)
                 (canonical-address-p lin-addr-2)
                 (equal (loghead 12 page-directory-base-addr-1) 0)
                 (equal (loghead 12 page-directory-base-addr-2) 0)
                 (x86p x86))
            (equal
             (mv-nth
              1
              (ia32e-la-to-pa-page-directory
               lin-addr-1 page-directory-base-addr-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
               (mv-nth
                2
                (ia32e-la-to-pa-page-directory
                 lin-addr-2 page-directory-base-addr-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
             (mv-nth
              1
              (ia32e-la-to-pa-page-directory
               lin-addr-1 page-directory-base-addr-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
               x86))))
   :do-not '(preprocess)
   :cases ((equal page-directory-entry-addr-2 page-directory-entry-addr-1))
   :in-theory (e/d
               ()
               (ia32e-la-to-pa-page-directory-entry-validp
                mv-nth-1-no-error-ia32e-la-to-pa-page-table
                mv-nth-2-no-error-ia32e-la-to-pa-page-table
                member-p-cons
                disjoint-p-cons
                not
                unsigned-byte-p
                signed-byte-p))))

(local
 (defthmd pairwise-disjoint-p-lemma-for-page-directory
   (implies (and (not (equal (page-directory-entry-addr lin-addr-1 page-directory-base-addr-1)
                             (page-directory-entry-addr lin-addr-2 page-directory-base-addr-2)))
                 (pairwise-disjoint-p
                  (translation-governing-addresses-for-page-directory
                   lin-addr-1 page-directory-base-addr-1 x86))
                 (pairwise-disjoint-p
                  (translation-governing-addresses-for-page-directory
                   lin-addr-2 page-directory-base-addr-2 x86))

                 (if (equal (ia32e-page-tables-slice
                             :ps
                             (rm-low-64
                              (page-directory-entry-addr lin-addr-2 page-directory-base-addr-2)
                              x86))
                            0)
                     (disjoint-p
                      (addr-range 8 (page-table-entry-addr
                                     lin-addr-2
                                     (ash (ia32e-pde-pg-table-slice
                                           :pde-pt
                                           (rm-low-64
                                            (page-directory-entry-addr
                                             lin-addr-2
                                             page-directory-base-addr-2)
                                            x86))
                                          12)))
                      (addr-range 8 (page-directory-entry-addr lin-addr-1 page-directory-base-addr-1)))
                   t)

                 (if (equal (ia32e-page-tables-slice
                             :ps
                             (rm-low-64
                              (page-directory-entry-addr lin-addr-1 page-directory-base-addr-1)
                              x86))
                            0)
                     (disjoint-p
                      (addr-range 8 (page-directory-entry-addr lin-addr-2 page-directory-base-addr-2))
                      (addr-range 8 (page-table-entry-addr
                                     lin-addr-1
                                     (ash (ia32e-pde-pg-table-slice
                                           :pde-pt
                                           (rm-low-64
                                            (page-directory-entry-addr
                                             lin-addr-1
                                             page-directory-base-addr-1)
                                            x86))
                                          12))))
                   t)

                 (if (and
                      (equal (ia32e-page-tables-slice
                              :ps
                              (rm-low-64
                               (page-directory-entry-addr lin-addr-1 page-directory-base-addr-1)
                               x86))
                             0)
                      (equal (ia32e-page-tables-slice
                              :ps
                              (rm-low-64
                               (page-directory-entry-addr lin-addr-2 page-directory-base-addr-2)
                               x86))
                             0))
                     (disjoint-p
                      (addr-range
                       8
                       (page-table-entry-addr
                        lin-addr-2
                        (ash
                         (loghead
                          40
                          (logtail
                           12
                           (rm-low-64
                            (page-directory-entry-addr lin-addr-2 page-directory-base-addr-2)
                            x86)))
                         12)))
                      (addr-range
                       8
                       (page-table-entry-addr
                        lin-addr-1
                        (ash
                         (loghead
                          40
                          (logtail
                           12
                           (rm-low-64
                            (page-directory-entry-addr lin-addr-1 page-directory-base-addr-1)
                            x86)))
                         12))))
                   t)

                 (equal (loghead 12 page-directory-base-addr-1) 0)
                 (equal (loghead 12 page-directory-base-addr-2) 0)
                 (physical-address-p page-directory-base-addr-1)
                 (physical-address-p page-directory-base-addr-2)
                 (canonical-address-p lin-addr-1)
                 (canonical-address-p lin-addr-2)
                 (x86p x86))
            (pairwise-disjoint-p
             (append (translation-governing-addresses-for-page-directory
                      lin-addr-2 page-directory-base-addr-2 x86)
                     (translation-governing-addresses-for-page-directory
                      lin-addr-1 page-directory-base-addr-1 x86))))))

(defrule two-page-table-walks-ia32e-la-to-pa-page-directory
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
                 lin-addr-1 page-directory-base-addr-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)
                (ia32e-la-to-pa-page-directory-entry-validp
                 lin-addr-2 page-directory-base-addr-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)


                (pairwise-disjoint-p
                 (translation-governing-addresses-for-page-directory
                  lin-addr-1 page-directory-base-addr-1 x86))

                (pairwise-disjoint-p
                 (translation-governing-addresses-for-page-directory
                  lin-addr-2 page-directory-base-addr-2 x86))

                (if (equal (ia32e-page-tables-slice
                            :ps
                            (rm-low-64
                             (page-directory-entry-addr lin-addr-2 page-directory-base-addr-2)
                             x86))
                           0)
                    (disjoint-p
                     (addr-range 8 (page-table-entry-addr
                                    lin-addr-2
                                    (ash (ia32e-pde-pg-table-slice
                                          :pde-pt
                                          (rm-low-64
                                           (page-directory-entry-addr
                                            lin-addr-2
                                            page-directory-base-addr-2)
                                           x86))
                                         12)))
                     (addr-range 8 (page-directory-entry-addr lin-addr-1 page-directory-base-addr-1)))
                  t)

                (if (equal (ia32e-page-tables-slice
                            :ps
                            (rm-low-64
                             (page-directory-entry-addr lin-addr-1 page-directory-base-addr-1)
                             x86))
                           0)
                    (disjoint-p
                     (addr-range 8 (page-directory-entry-addr lin-addr-2 page-directory-base-addr-2))
                     (addr-range 8 (page-table-entry-addr
                                    lin-addr-1
                                    (ash (ia32e-pde-pg-table-slice
                                          :pde-pt
                                          (rm-low-64
                                           (page-directory-entry-addr
                                            lin-addr-1
                                            page-directory-base-addr-1)
                                           x86))
                                         12))))
                  t)

                (equal (loghead 12 page-directory-base-addr-1) 0)
                (equal (loghead 12 page-directory-base-addr-2) 0)
                (physical-address-p page-directory-base-addr-1)
                (physical-address-p page-directory-base-addr-2)
                (canonical-address-p lin-addr-1)
                (canonical-address-p lin-addr-2)
                (x86p x86))
           (equal
            (mv-nth
             1
             (ia32e-la-to-pa-page-directory
              lin-addr-1 page-directory-base-addr-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
              (mv-nth
               2
               (ia32e-la-to-pa-page-directory
                lin-addr-2 page-directory-base-addr-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
            (mv-nth
             1
             (ia32e-la-to-pa-page-directory
              lin-addr-1 page-directory-base-addr-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
              x86))))
  :hints (("Goal"
           :do-not '(preprocess)
           :cases (
                   ;; validity-preserved-same-x86-state-2M-pages-wrt-page-directory-same-entry
                   (and (logbitp
                         7
                         (rm-low-64
                          (page-directory-entry-addr lin-addr-1 page-directory-base-addr-1)
                          x86))
                        (equal (page-directory-entry-addr lin-addr-1 page-directory-base-addr-1)
                               (page-directory-entry-addr lin-addr-2 page-directory-base-addr-2)))

                   ;; validity-preserved-same-x86-state-4K-pages-wrt-page-directory-same-entry
                   (and (not (logbitp
                              7
                              (rm-low-64
                               (page-directory-entry-addr lin-addr-1 page-directory-base-addr-1)
                               x86)))
                        (equal (page-directory-entry-addr lin-addr-1 page-directory-base-addr-1)
                               (page-directory-entry-addr lin-addr-2 page-directory-base-addr-2)))

                   ;; validity-preserved-same-x86-state-wrt-page-directory-different-entries
                   (pairwise-disjoint-p
                    (append
                     (translation-governing-addresses-for-page-directory
                      lin-addr-2 page-directory-base-addr-2 x86)
                     (translation-governing-addresses-for-page-directory
                      lin-addr-1 page-directory-base-addr-1 x86)))

                   ;; validity-preserved-same-x86-state-wrt-page-directory-4K-pages-different-dir-entries-same-table-entry
                   (and (not (logbitp
                              7
                              (rm-low-64
                               (page-directory-entry-addr lin-addr-1 page-directory-base-addr-1)
                               x86)))
                        (not (logbitp
                              7
                              (rm-low-64
                               (page-directory-entry-addr lin-addr-2 page-directory-base-addr-2)
                               x86)))
                        (equal (page-table-entry-addr lin-addr-2 (ash (ia32e-pde-pg-table-slice
                                                                       :pde-pt
                                                                       (rm-low-64
                                                                        (page-directory-entry-addr
                                                                         lin-addr-2
                                                                         page-directory-base-addr-2)
                                                                        x86))
                                                                      12))
                               (page-table-entry-addr lin-addr-1 (ash (ia32e-pde-pg-table-slice
                                                                       :pde-pt
                                                                       (rm-low-64
                                                                        (page-directory-entry-addr
                                                                         lin-addr-1
                                                                         page-directory-base-addr-1)
                                                                        x86))
                                                                      12)))))
           :in-theory (e/d* ()
                            (ia32e-la-to-pa-page-directory-entry-validp
                             mv-nth-1-no-error-ia32e-la-to-pa-page-directory-2m-pages
                             mv-nth-2-no-error-ia32e-la-to-pa-page-directory-2M-pages
                             mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4k-pages
                             mv-nth-1-no-error-ia32e-la-to-pa-page-table
                             mv-nth-2-no-error-ia32e-la-to-pa-page-table
                             member-p-cons
                             pairwise-disjoint-p
                             translation-governing-addresses-for-page-directory
                             disjoint-p-cons
                             pairwise-disjoint-p-aux
                             unsigned-byte-p
                             signed-byte-p)))
          ("Subgoal 5"
           :use ((:instance pairwise-disjoint-p-lemma-for-page-directory))
           :in-theory (e/d* ()
                            (ia32e-la-to-pa-page-directory-entry-validp
                             pairwise-disjoint-p-lemma-for-page-directory
                             mv-nth-1-no-error-ia32e-la-to-pa-page-directory-2m-pages
                             mv-nth-2-no-error-ia32e-la-to-pa-page-directory-2M-pages
                             mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4k-pages
                             mv-nth-1-no-error-ia32e-la-to-pa-page-table
                             mv-nth-2-no-error-ia32e-la-to-pa-page-table
                             member-p-cons
                             translation-governing-addresses-for-page-directory
                             disjoint-p-cons
                             pairwise-disjoint-p-aux
                             unsigned-byte-p
                             signed-byte-p)))))

;; ......................................................................
;; More theorems about validity of page directory entries being
;; preserved when the translation-governing addresses are disjoint:
;; ......................................................................

;; 2M - Scenario (3), (4)
(local
 (defrule validity-preserved-same-x86-state-2M-pages-wrt-page-directory-same-entry
   ;; Two walks of a page directory entry, with same or different
   ;; "input" linear addresses.

   (implies (and (ia32e-la-to-pa-page-directory-entry-validp
                  lin-addr-1 page-directory-base-addr-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)
                 (ia32e-la-to-pa-page-directory-entry-validp
                  lin-addr-2 page-directory-base-addr-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)
                 (equal page-directory-entry-addr-1
                        (page-directory-entry-addr lin-addr-1 page-directory-base-addr-1))
                 (equal page-directory-entry-addr-2
                        (page-directory-entry-addr lin-addr-2 page-directory-base-addr-2))
                 (equal page-directory-entry-1 (rm-low-64 page-directory-entry-addr-1 x86))
                 (equal (ia32e-page-tables-slice :ps page-directory-entry-1) 1)

                 ;; Same page directory entry.
                 (equal page-directory-entry-addr-2 page-directory-entry-addr-1)

                 (equal (loghead 12 page-directory-base-addr-1) 0)
                 (physical-address-p page-directory-base-addr-1)
                 (canonical-address-p lin-addr-1)
                 (canonical-address-p lin-addr-2)
                 (x86p x86))
            (ia32e-la-to-pa-page-directory-entry-validp
             lin-addr-1 page-directory-base-addr-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
             (mv-nth 2 (ia32e-la-to-pa-page-directory
                        lin-addr-2 page-directory-base-addr-2
                        wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
   :do-not '(preprocess)
   :in-theory (e/d* ()
                    (ia32e-la-to-pa-page-directory-entry-validp
                     mv-nth-1-no-error-ia32e-la-to-pa-page-directory-2m-pages
                     mv-nth-1-no-error-ia32e-la-to-pa-page-table
                     mv-nth-2-no-error-ia32e-la-to-pa-page-table
                     member-p-cons
                     disjoint-p-cons
                     not
                     unsigned-byte-p
                     signed-byte-p))))

;; 4K - Scenario (3), (4)
(local
 (defrule validity-preserved-same-x86-state-4K-pages-wrt-page-directory-same-entry
   ;; Two walks of a page directory entry, with same or different page table entries
   (implies
    (and (ia32e-la-to-pa-page-directory-entry-validp
          lin-addr-1 page-directory-base-addr-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)
         (ia32e-la-to-pa-page-directory-entry-validp
          lin-addr-2 page-directory-base-addr-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)
         (equal page-directory-entry-addr-1
                (page-directory-entry-addr lin-addr-1 page-directory-base-addr-1))
         (equal page-directory-entry-addr-2
                (page-directory-entry-addr lin-addr-2 page-directory-base-addr-2))

         ;; Same page directory entry.
         (equal page-directory-entry-addr-2 page-directory-entry-addr-1)

         (equal page-directory-entry-1 (rm-low-64 page-directory-entry-addr-1 x86))
         (equal (ia32e-page-tables-slice :ps  page-directory-entry-1) 0)
         ;; For ia32e-la-to-pa-page-table:
         (equal page-table-base-addr
                ;; Same for the page table entries if page directory entry is the same.
                (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry-1) 12))
         (equal u-s-acc
                ;; Same for the page table entries if page directory entry is the same.
                (ia32e-page-tables-slice :u/s page-directory-entry-1))
         (equal page-table-entry-addr-1
                (page-table-entry-addr lin-addr-1 page-table-base-addr))
         (equal page-table-entry-addr-2
                (page-table-entry-addr lin-addr-2 page-table-base-addr))

         ;; Page table entries may or may not be the same.

         (pairwise-disjoint-p
          (translation-governing-addresses-for-page-directory
           lin-addr-1 page-directory-base-addr-1 x86))
         (pairwise-disjoint-p
          (translation-governing-addresses-for-page-directory
           lin-addr-2 page-directory-base-addr-2 x86))

         (physical-address-p page-directory-base-addr-1)
         (physical-address-p page-directory-base-addr-2)
         (canonical-address-p lin-addr-1)
         (canonical-address-p lin-addr-2)
         (equal (loghead 12 page-directory-base-addr-1) 0)
         (equal (loghead 12 page-directory-base-addr-2) 0)
         (x86p x86))
    (ia32e-la-to-pa-page-directory-entry-validp
     lin-addr-1 page-directory-base-addr-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
     (mv-nth 2 (ia32e-la-to-pa-page-directory
                lin-addr-2 page-directory-base-addr-2
                wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
   :cases ((equal page-table-entry-addr-1 page-table-entry-addr-2))
   :do-not '(preprocess)
   :in-theory (e/d
               ()
               (ia32e-la-to-pa-page-directory-entry-validp
                mv-nth-1-no-error-ia32e-la-to-pa-page-table
                mv-nth-2-no-error-ia32e-la-to-pa-page-table
                member-p-cons
                disjoint-p-cons
                not
                unsigned-byte-p
                signed-byte-p))))

;; 2M - Scenario (1), (2)
;; 4K - Scenario (1)
(local
 (defrule validity-preserved-same-x86-state-wrt-page-directory-different-entries
   (implies (and (ia32e-la-to-pa-page-directory-entry-validp
                  lin-addr-1 page-directory-base-addr-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)
                 (ia32e-la-to-pa-page-directory-entry-validp
                  lin-addr-2 page-directory-base-addr-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)

                 (pairwise-disjoint-p
                  (append
                   (translation-governing-addresses-for-page-directory
                    lin-addr-2 page-directory-base-addr-2 x86)
                   (translation-governing-addresses-for-page-directory
                    lin-addr-1 page-directory-base-addr-1 x86)))

                 (physical-address-p page-directory-base-addr-1)
                 (canonical-address-p lin-addr-1)
                 (equal (loghead 12 page-directory-base-addr-1) 0)

                 (physical-address-p page-directory-base-addr-2)
                 (canonical-address-p lin-addr-2)
                 (equal (loghead 12 page-directory-base-addr-2) 0)

                 (x86p x86))

            (ia32e-la-to-pa-page-directory-entry-validp
             lin-addr-1 page-directory-base-addr-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
             (mv-nth 2 (ia32e-la-to-pa-page-directory
                        lin-addr-2 page-directory-base-addr-2
                        wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
   :in-theory (e/d ()
                   (ia32e-la-to-pa-page-directory-entry-validp
                    mv-nth-2-no-error-ia32e-la-to-pa-page-directory-2M-pages
                    mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages
                    member-p-cons
                    disjoint-p-cons
                    not
                    unsigned-byte-p
                    signed-byte-p))))

;; 4K - Scenario (2)
(local
 (defrule validity-preserved-same-x86-state-wrt-page-directory-4K-pages-different-dir-entries-same-table-entry
   (implies (and (ia32e-la-to-pa-page-directory-entry-validp
                  lin-addr-1 page-directory-base-addr-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)
                 (ia32e-la-to-pa-page-directory-entry-validp
                  lin-addr-2 page-directory-base-addr-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)
                 (equal page-directory-entry-addr-1
                        (page-directory-entry-addr lin-addr-1 page-directory-base-addr-1))
                 (equal page-directory-entry-addr-2
                        (page-directory-entry-addr lin-addr-2 page-directory-base-addr-2))

                 (equal page-directory-entry-1 (rm-low-64 page-directory-entry-addr-1 x86))
                 (equal (ia32e-page-tables-slice :ps  page-directory-entry-1) 0)
                 (equal page-directory-entry-2 (rm-low-64 page-directory-entry-addr-2 x86))
                 (equal (ia32e-page-tables-slice :ps  page-directory-entry-2) 0)

                 ;; For ia32e-la-to-pa-page-table:
                 (equal page-table-base-addr-1
                        (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry-1) 12))
                 (equal page-table-base-addr-2
                        (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry-2) 12))
                 (equal u-s-acc-2
                        (ia32e-page-tables-slice :u/s page-directory-entry-2))

                 (equal page-table-entry-addr-1
                        (page-table-entry-addr lin-addr-1 page-table-base-addr-1))
                 (equal page-table-entry-addr-2
                        (page-table-entry-addr lin-addr-2 page-table-base-addr-2))

                 ;; Same page table entries.
                 (equal page-table-entry-addr-2 page-table-entry-addr-1)

                 (pairwise-disjoint-p
                  (translation-governing-addresses-for-page-directory
                   lin-addr-1 page-directory-base-addr-1 x86))
                 (pairwise-disjoint-p
                  (translation-governing-addresses-for-page-directory
                   lin-addr-2 page-directory-base-addr-2 x86))

                 (physical-address-p page-directory-base-addr-1)
                 (physical-address-p page-directory-base-addr-2)
                 (canonical-address-p lin-addr-1)
                 (canonical-address-p lin-addr-2)
                 (equal (loghead 12 page-directory-base-addr-1) 0)
                 (equal (loghead 12 page-directory-base-addr-2) 0)
                 (x86p x86))
            (ia32e-la-to-pa-page-directory-entry-validp
             lin-addr-1 page-directory-base-addr-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
             (mv-nth 2 (ia32e-la-to-pa-page-directory
                        lin-addr-2 page-directory-base-addr-2
                        wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
   :do-not '(preprocess)
   :cases ((equal page-directory-entry-addr-2 page-directory-entry-addr-1))
   :in-theory (e/d
               ()
               (ia32e-la-to-pa-page-directory-entry-validp
                mv-nth-1-no-error-ia32e-la-to-pa-page-table
                mv-nth-2-no-error-ia32e-la-to-pa-page-table
                member-p-cons
                disjoint-p-cons
                not
                unsigned-byte-p
                signed-byte-p))))

(defrule validity-preserved-same-x86-state-page-directory
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
                 lin-addr-1 page-directory-base-addr-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)
                (ia32e-la-to-pa-page-directory-entry-validp
                 lin-addr-2 page-directory-base-addr-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)


                (pairwise-disjoint-p
                 (translation-governing-addresses-for-page-directory
                  lin-addr-1 page-directory-base-addr-1 x86))

                (pairwise-disjoint-p
                 (translation-governing-addresses-for-page-directory
                  lin-addr-2 page-directory-base-addr-2 x86))

                (if (equal (ia32e-page-tables-slice
                            :ps
                            (rm-low-64
                             (page-directory-entry-addr lin-addr-2 page-directory-base-addr-2)
                             x86))
                           0)
                    (disjoint-p
                     (addr-range 8 (page-table-entry-addr
                                    lin-addr-2
                                    (ash (ia32e-pde-pg-table-slice
                                          :pde-pt
                                          (rm-low-64
                                           (page-directory-entry-addr
                                            lin-addr-2
                                            page-directory-base-addr-2)
                                           x86))
                                         12)))
                     (addr-range 8 (page-directory-entry-addr lin-addr-1 page-directory-base-addr-1)))
                  t)

                (if (equal (ia32e-page-tables-slice
                            :ps
                            (rm-low-64
                             (page-directory-entry-addr lin-addr-1 page-directory-base-addr-1)
                             x86))
                           0)
                    (disjoint-p
                     (addr-range 8 (page-directory-entry-addr lin-addr-2 page-directory-base-addr-2))
                     (addr-range 8 (page-table-entry-addr
                                    lin-addr-1
                                    (ash (ia32e-pde-pg-table-slice
                                          :pde-pt
                                          (rm-low-64
                                           (page-directory-entry-addr
                                            lin-addr-1
                                            page-directory-base-addr-1)
                                           x86))
                                         12))))
                  t)

                (equal (loghead 12 page-directory-base-addr-1) 0)
                (equal (loghead 12 page-directory-base-addr-2) 0)
                (physical-address-p page-directory-base-addr-1)
                (physical-address-p page-directory-base-addr-2)
                (canonical-address-p lin-addr-1)
                (canonical-address-p lin-addr-2)
                (x86p x86))
           (ia32e-la-to-pa-page-directory-entry-validp
            lin-addr-1 page-directory-base-addr-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
            (mv-nth 2 (ia32e-la-to-pa-page-directory
                       lin-addr-2 page-directory-base-addr-2
                       wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
  :hints (("Goal"
           :do-not '(preprocess)
           :cases (
                   ;; validity-preserved-same-x86-state-2M-pages-wrt-page-directory-same-entry
                   (and (logbitp
                         7
                         (rm-low-64
                          (page-directory-entry-addr lin-addr-1 page-directory-base-addr-1)
                          x86))
                        (equal (page-directory-entry-addr lin-addr-1 page-directory-base-addr-1)
                               (page-directory-entry-addr lin-addr-2 page-directory-base-addr-2)))

                   ;; validity-preserved-same-x86-state-4K-pages-wrt-page-directory-same-entry
                   (and (not (logbitp
                              7
                              (rm-low-64
                               (page-directory-entry-addr lin-addr-1 page-directory-base-addr-1)
                               x86)))
                        (equal (page-directory-entry-addr lin-addr-1 page-directory-base-addr-1)
                               (page-directory-entry-addr lin-addr-2 page-directory-base-addr-2)))

                   ;; validity-preserved-same-x86-state-wrt-page-directory-different-entries
                   (pairwise-disjoint-p
                    (append
                     (translation-governing-addresses-for-page-directory
                      lin-addr-2 page-directory-base-addr-2 x86)
                     (translation-governing-addresses-for-page-directory
                      lin-addr-1 page-directory-base-addr-1 x86)))

                   ;; validity-preserved-same-x86-state-wrt-page-directory-4K-pages-different-dir-entries-same-table-entry
                   (and (not (logbitp
                              7
                              (rm-low-64
                               (page-directory-entry-addr lin-addr-1 page-directory-base-addr-1)
                               x86)))
                        (not (logbitp
                              7
                              (rm-low-64
                               (page-directory-entry-addr lin-addr-2 page-directory-base-addr-2)
                               x86)))
                        (equal (page-table-entry-addr lin-addr-2 (ash (ia32e-pde-pg-table-slice
                                                                       :pde-pt
                                                                       (rm-low-64
                                                                        (page-directory-entry-addr
                                                                         lin-addr-2
                                                                         page-directory-base-addr-2)
                                                                        x86))
                                                                      12))
                               (page-table-entry-addr lin-addr-1 (ash (ia32e-pde-pg-table-slice
                                                                       :pde-pt
                                                                       (rm-low-64
                                                                        (page-directory-entry-addr
                                                                         lin-addr-1
                                                                         page-directory-base-addr-1)
                                                                        x86))
                                                                      12)))))
           :in-theory (e/d* ()
                            (ia32e-la-to-pa-page-directory-entry-validp
                             mv-nth-1-no-error-ia32e-la-to-pa-page-directory-2m-pages
                             mv-nth-2-no-error-ia32e-la-to-pa-page-directory-2M-pages
                             mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4k-pages
                             mv-nth-1-no-error-ia32e-la-to-pa-page-table
                             mv-nth-2-no-error-ia32e-la-to-pa-page-table
                             member-p-cons
                             pairwise-disjoint-p
                             translation-governing-addresses-for-page-directory
                             disjoint-p-cons
                             pairwise-disjoint-p-aux
                             unsigned-byte-p
                             signed-byte-p)))
          ("Subgoal 5"
           :use ((:instance pairwise-disjoint-p-lemma-for-page-directory))
           :in-theory (e/d* ()
                            (ia32e-la-to-pa-page-directory-entry-validp
                             pairwise-disjoint-p-lemma-for-page-directory
                             mv-nth-1-no-error-ia32e-la-to-pa-page-directory-2m-pages
                             mv-nth-2-no-error-ia32e-la-to-pa-page-directory-2M-pages
                             mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4k-pages
                             mv-nth-1-no-error-ia32e-la-to-pa-page-table
                             mv-nth-2-no-error-ia32e-la-to-pa-page-table
                             member-p-cons
                             translation-governing-addresses-for-page-directory
                             disjoint-p-cons
                             pairwise-disjoint-p-aux
                             unsigned-byte-p
                             signed-byte-p)))))

;; ......................................................................
;; Translation-Governing-Addresses-For-Page-Directory and
;; ia32e-la-to-pa-page-directory-entry:
;; ......................................................................

(defrule translation-governing-addresses-for-page-directory-and-ia32e-la-to-pa-page-directory-pairwise-disjoint
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
                 lin-addr-2 page-directory-base-addr-2 wp-2
                 smep-2 nxe-2 r-w-x-2 cpl-2 x86)
                (pairwise-disjoint-p
                 (append
                  (translation-governing-addresses-for-page-directory
                   lin-addr-2 page-directory-base-addr-2 x86)
                  (translation-governing-addresses-for-page-directory
                   lin-addr-1 page-directory-base-addr-1 x86))))
           (equal
            (translation-governing-addresses-for-page-directory
             lin-addr-1 page-directory-base-addr-1
             (mv-nth 2
                     (ia32e-la-to-pa-page-directory
                      lin-addr-2 page-directory-base-addr-2
                      wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)))
            (translation-governing-addresses-for-page-directory
             lin-addr-1 page-directory-base-addr-1 x86)))
  :in-theory (e/d ()
                  (ia32e-la-to-pa-page-directory-entry-validp
                   addr-range-1
                   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages
                   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-2M-pages
                   member-p-cons
                   disjoint-p-cons
                   not
                   unsigned-byte-p
                   signed-byte-p)))

(defrule translation-governing-addresses-for-page-directory-and-ia32e-la-to-pa-page-directory-same-addr-2M-pages
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
                 lin-addr page-directory-base-addr wp
                 smep nxe r-w-x cpl x86)
                (equal page-directory-entry-addr
                       (page-directory-entry-addr lin-addr page-directory-base-addr))
                (equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps page-directory-entry) 1)
                (physical-address-p page-directory-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 page-directory-base-addr) 0)
                (x86p x86))
           (equal
            (translation-governing-addresses-for-page-directory
             lin-addr page-directory-base-addr
             (mv-nth 2
                     (ia32e-la-to-pa-page-directory
                      lin-addr page-directory-base-addr
                      wp smep nxe r-w-x cpl x86)))
            (translation-governing-addresses-for-page-directory
             lin-addr page-directory-base-addr x86)))
  :in-theory (e/d ()
                  (ia32e-la-to-pa-page-directory-entry-validp
                   addr-range-1
                   member-p-cons
                   disjoint-p-cons
                   not
                   unsigned-byte-p
                   signed-byte-p)))

(defrule translation-governing-addresses-for-page-directory-and-wm-low-64-disjoint-2M-pages
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
                 lin-addr page-directory-base-addr wp
                 smep nxe r-w-x cpl x86)
                (equal page-directory-entry-addr
                       (page-directory-entry-addr lin-addr page-directory-base-addr))
                (equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps page-directory-entry) 1)
                (pairwise-disjoint-p-aux
                 (addr-range 8 addr)
                 (translation-governing-addresses-for-page-directory
                  lin-addr page-directory-base-addr x86))
                (integerp addr)
                (physical-address-p page-directory-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 page-directory-base-addr) 0)
                (x86p x86))
           (equal
            (translation-governing-addresses-for-page-directory
             lin-addr page-directory-base-addr
             (wm-low-64 addr val x86))
            (translation-governing-addresses-for-page-directory
             lin-addr page-directory-base-addr x86)))
  :in-theory (e/d ()
                  (ia32e-la-to-pa-page-directory-entry-validp
                   addr-range-1
                   member-p-cons
                   disjoint-p-cons
                   not
                   unsigned-byte-p
                   signed-byte-p)))

(defrule translation-governing-addresses-for-page-directory-and-ia32e-la-to-pa-page-directory-same-addr-4K-pages
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
                 lin-addr page-directory-base-addr wp
                 smep nxe r-w-x cpl x86)
                (equal page-directory-entry-addr
                       (page-directory-entry-addr lin-addr page-directory-base-addr))
                (equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps page-directory-entry) 0)
                ;; For ia32e-la-to-pa-page-table:
                (equal page-table-base-addr
                       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
                (equal page-table-entry-addr
                       (page-table-entry-addr lin-addr page-table-base-addr))

                (pairwise-disjoint-p (translation-governing-addresses-for-page-directory
                                      lin-addr page-directory-base-addr x86))

                (physical-address-p page-directory-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 page-directory-base-addr) 0)
                (x86p x86))
           (equal
            (translation-governing-addresses-for-page-directory
             lin-addr page-directory-base-addr
             (mv-nth 2
                     (ia32e-la-to-pa-page-directory
                      lin-addr page-directory-base-addr
                      wp smep nxe r-w-x cpl x86)))
            (translation-governing-addresses-for-page-directory
             lin-addr page-directory-base-addr x86)))
  :in-theory (e/d ()
                  (ia32e-la-to-pa-page-directory-entry-validp
                   addr-range-1
                   member-p-cons
                   disjoint-p-cons
                   not
                   unsigned-byte-p
                   signed-byte-p)))

(defrule translation-governing-addresses-for-page-directory-and-wm-low-64-disjoint-4K-page
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
                 lin-addr page-directory-base-addr wp
                 smep nxe r-w-x cpl x86)
                (equal page-directory-entry-addr
                       (page-directory-entry-addr lin-addr page-directory-base-addr))
                (equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps page-directory-entry) 0)
                ;; For ia32e-la-to-pa-page-table:
                (equal page-table-base-addr
                       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
                (equal page-table-entry-addr
                       (page-table-entry-addr lin-addr page-table-base-addr))

                (pairwise-disjoint-p
                 (translation-governing-addresses-for-page-directory
                  lin-addr page-directory-base-addr x86))
                (pairwise-disjoint-p-aux
                 (addr-range 8 addr)
                 (translation-governing-addresses-for-page-directory
                  lin-addr page-directory-base-addr x86))

                (integerp addr)
                (physical-address-p page-directory-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 page-directory-base-addr) 0)
                (x86p x86))
           (equal
            (translation-governing-addresses-for-page-directory
             lin-addr page-directory-base-addr
             (wm-low-64 addr val x86))
            (translation-governing-addresses-for-page-directory
             lin-addr page-directory-base-addr x86)))
  :in-theory (e/d ()
                  (ia32e-la-to-pa-page-directory-entry-validp
                   addr-range-1
                   member-p-cons
                   disjoint-p-cons
                   not
                   unsigned-byte-p
                   signed-byte-p)))

(in-theory (e/d () (ia32e-la-to-pa-page-directory-entry-validp)))

;; ======================================================================
