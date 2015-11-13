;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")
(include-book "paging-page-directory-lemmas")

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))

;; ======================================================================

;; ia32e-la-to-pa-page-dir-ptr-table:

(defmacro ia32e-la-to-pa-page-dir-ptr-table-entry-components-equal-p-1G-body
  (entry-1 entry-2)
  `(and (equal (ia32e-pdpte-1GB-page-slice :pdpte-p ,entry-1)
               (ia32e-pdpte-1GB-page-slice :pdpte-p ,entry-2))
        (equal (ia32e-pdpte-1GB-page-slice :pdpte-r/w ,entry-1)
               (ia32e-pdpte-1GB-page-slice :pdpte-r/w ,entry-2))
        (equal (ia32e-pdpte-1GB-page-slice :pdpte-u/s ,entry-1)
               (ia32e-pdpte-1GB-page-slice :pdpte-u/s ,entry-2))
        (equal (ia32e-pdpte-1GB-page-slice :pdpte-ps ,entry-1)
               (ia32e-pdpte-1GB-page-slice :pdpte-ps ,entry-2))
        (equal (ia32e-pdpte-1GB-page-slice :pdpte-xd ,entry-1)
               (ia32e-pdpte-1GB-page-slice :pdpte-xd ,entry-2))
        ;; Reserved bits are zero.
        ;; (equal (loghead 11 (logtail 52 ,entry-2)) 0)
        ;; (equal (loghead 17 (logtail 13 ,entry-2)) 0)
        (equal (loghead 11 (logtail 52 ,entry-1))
               (loghead 11 (logtail 52 ,entry-2)))
        (equal (loghead 17 (logtail 13 ,entry-1))
               (loghead 17 (logtail 13 ,entry-2)))))

(defmacro ia32e-la-to-pa-page-dir-ptr-table-entry-components-equal-p-4K-or-2M-body
  (entry-1 entry-2)
  `(and (equal (ia32e-pdpte-pg-dir-slice :pdpte-p ,entry-1)
               (ia32e-pdpte-pg-dir-slice :pdpte-p ,entry-2))
        (equal (ia32e-pdpte-pg-dir-slice :pdpte-r/w ,entry-1)
               (ia32e-pdpte-pg-dir-slice :pdpte-r/w ,entry-2))
        (equal (ia32e-pdpte-pg-dir-slice :pdpte-u/s ,entry-1)
               (ia32e-pdpte-pg-dir-slice :pdpte-u/s ,entry-2))
        (equal (ia32e-pdpte-pg-dir-slice :pdpte-ps ,entry-1)
               (ia32e-pdpte-pg-dir-slice :pdpte-ps ,entry-2))
        (equal (ia32e-pdpte-pg-dir-slice :pdpte-pd ,entry-1)
               (ia32e-pdpte-pg-dir-slice :pdpte-pd ,entry-2))
        (equal (ia32e-pdpte-pg-dir-slice :pdpte-xd ,entry-1)
               (ia32e-pdpte-pg-dir-slice :pdpte-xd ,entry-2))
        ;; Reserved bits are zero.
        ;; (equal (loghead 11 (logtail 52 ,entry-2)) 0)
        (equal (loghead 11 (logtail 52 ,entry-1))
               (loghead 11 (logtail 52 ,entry-2)))))

(define ia32e-la-to-pa-page-dir-ptr-table-entry-components-equal-p
  (page-size? entry-1 entry-2)
  :verify-guards nil
  :non-executable t
  (if (equal page-size? '1G)
      (ia32e-la-to-pa-page-dir-ptr-table-entry-components-equal-p-1G-body
       entry-1 entry-2)
    (if (equal page-size? '4K-or-2M)
        (ia32e-la-to-pa-page-dir-ptr-table-entry-components-equal-p-4K-or-2M-body
         entry-1 entry-2)
      't)))

(defmacro ia32e-la-to-pa-page-dir-ptr-table-entry-components-equal-p-1G-macro (x y)
  `(ia32e-la-to-pa-page-dir-ptr-table-entry-components-equal-p-1G-body ,x ,y))

(defmacro ia32e-la-to-pa-page-dir-ptr-table-entry-components-equal-p-4K-or-2M-macro (x y)
  `(ia32e-la-to-pa-page-dir-ptr-table-entry-components-equal-p-4K-or-2M-body
  ,x ,y))

(defthm ia32e-la-to-pa-page-dir-ptr-table-entry-components-equal-p-reflexive
  (ia32e-la-to-pa-page-dir-ptr-table-entry-components-equal-p a b b)
  :hints (("Goal" :in-theory (e/d
                              (ia32e-la-to-pa-page-dir-ptr-table-entry-components-equal-p)
                              ()))))

(defthm ia32e-la-to-pa-page-dir-ptr-table-entry-components-equal-p-accessed-bit-set
  (ia32e-la-to-pa-page-dir-ptr-table-entry-components-equal-p
   a b (set-accessed-bit b))
  :hints (("Goal" :in-theory (e/d
                              (ia32e-la-to-pa-page-dir-ptr-table-entry-components-equal-p
                               set-accessed-bit)
                              ()))))

(defthm ia32e-la-to-pa-page-dir-ptr-table-entry-components-equal-p-dirty-bit-set
  (ia32e-la-to-pa-page-dir-ptr-table-entry-components-equal-p
   a b (set-dirty-bit b))
  :hints (("Goal" :in-theory (e/d
                              (ia32e-la-to-pa-page-dir-ptr-table-entry-components-equal-p
                               set-dirty-bit)
                              ()))))

(defthm ia32e-la-to-pa-page-dir-ptr-table-entry-components-equal-p-accessed-and-dirty-bits-set
  (ia32e-la-to-pa-page-dir-ptr-table-entry-components-equal-p
   a b (set-dirty-bit (set-accessed-bit b)))
  :hints (("Goal" :in-theory (e/d
                              (ia32e-la-to-pa-page-dir-ptr-table-entry-components-equal-p
                               set-accessed-bit
                               set-dirty-bit)
                              ()))))

;; ......................................................................
;; Establishing inferior data structure entry validity from page
;; directory pointer table entry's validity:
;; ......................................................................

(defrule page-dir-ptr-entry-validp-to-page-directory-entry-validp
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
                (equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps ptr-table-entry) 0)
                (equal page-directory-base-addr
                       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry)
                            12)))
           (ia32e-la-to-pa-page-directory-entry-validp
            lin-addr page-directory-base-addr
            wp smep nxe r-w-x cpl x86)))

(defrule page-dir-ptr-entry-validp-to-page-table-entry-validp
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
                (equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)a
                ;; For ia32e-la-to-pa-page-directory:
                (equal page-directory-base-addr
                       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
                (equal page-directory-entry-addr
                       (page-directory-entry-addr lin-addr page-directory-base-addr))
                (equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps page-directory-entry) 0)
                ;; For ia32e-la-to-pa-page-table:
                (equal page-table-base-addr
                       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
                (equal u-s-acc (ia32e-page-tables-slice :u/s page-directory-entry)))
           (ia32e-la-to-pa-page-table-entry-validp
            lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl x86)))

;; ......................................................................
;; Rules about the three return values of
;; ia32e-la-to-pa-page-dir-ptr-table:
;; ......................................................................

(defrule mv-nth-0-no-error-ia32e-la-to-pa-page-dir-ptr-table
  (implies (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
            lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
           (equal (mv-nth
                   0
                   (ia32e-la-to-pa-page-dir-ptr-table
                    lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86))
                  nil))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-dir-ptr-table)
                  (not)))

;; 1G pages:

(defrule mv-nth-0-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages-with-disjoint-!memi
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
                (equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  ptr-table-entry) 1)
                (disjoint-p (addr-range 1 addr)
                            (addr-range 8 ptr-table-entry-addr))
                (integerp addr))
           (equal (mv-nth
                   0
                   (ia32e-la-to-pa-page-dir-ptr-table
                    lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl
                    (xw :mem addr val x86)))
                  nil))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-dir-ptr-table)
                  (not
                   addr-range-1)))

(defrule mv-nth-0-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages-with-disjoint-wm-low-64
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
                (equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  ptr-table-entry) 1)
                (disjoint-p (addr-range 8 addr)
                            (addr-range 8 ptr-table-entry-addr))
                (integerp addr))
           (equal (mv-nth
                   0
                   (ia32e-la-to-pa-page-dir-ptr-table
                    lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl
                    (wm-low-64 addr val x86)))
                  nil))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-dir-ptr-table)
                  (not)))

(defrule mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
                (equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  ptr-table-entry) 1))
           (equal (mv-nth
                   1
                   (ia32e-la-to-pa-page-dir-ptr-table
                    lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86))
                  (part-install
                   (part-select lin-addr :low 0 :high 29)
                   (ash (ia32e-pdpte-1GB-page-slice :pdpte-page ptr-table-entry) 30)
                   :low 0 :high 29)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-dir-ptr-table)
                  (not)))

(defrule mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages-with-disjoint-!memi
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
                (equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  ptr-table-entry) 1)
                (disjoint-p (addr-range 1 addr)
                            (addr-range 8 ptr-table-entry-addr))
                (integerp addr))
           (equal (mv-nth
                   1
                   (ia32e-la-to-pa-page-dir-ptr-table
                    lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl
                    (xw :mem addr val x86)))
                  (mv-nth
                   1
                   (ia32e-la-to-pa-page-dir-ptr-table
                    lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86))))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-dir-ptr-table)
                  (not
                   addr-range-1)))

(defrule mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages-with-disjoint-wm-low-64
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
                (equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps ptr-table-entry) 1)
                (disjoint-p (addr-range 8 addr)
                            (addr-range 8 ptr-table-entry-addr))
                (integerp addr))
           (equal (mv-nth
                   1
                   (ia32e-la-to-pa-page-dir-ptr-table
                    lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl
                    (wm-low-64 addr val x86)))
                  (mv-nth
                   1
                   (ia32e-la-to-pa-page-dir-ptr-table
                    lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86))))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-dir-ptr-table)
                  (not)))

(defrule mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
                (equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps ptr-table-entry) 1)
                (equal accessed (ia32e-pdpte-1GB-page-slice :pdpte-a ptr-table-entry))
                (equal dirty (ia32e-pdpte-1GB-page-slice :pdpte-d ptr-table-entry))
                (equal accessed-entry
                       (if (equal accessed 0)
                           (set-accessed-bit ptr-table-entry)
                         ptr-table-entry))
                (equal dirty-entry
                       (if (and (equal dirty 0)
                                (equal r-w-x :w))
                           (set-dirty-bit accessed-entry)
                         accessed-entry)))
           (equal (mv-nth
                   2
                   (ia32e-la-to-pa-page-dir-ptr-table
                    lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86))
                  (if (or (equal accessed 0)
                          (and (equal dirty 0)
                               (equal r-w-x :w)))
                      (wm-low-64 ptr-table-entry-addr dirty-entry x86)
                    x86)))

  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-dir-ptr-table)
                  (not
                   mv-nth-1-no-error-ia32e-la-to-pa-page-directory-4K-pages
                   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages)))

;; 2M pages:

(defrule mv-nth-0-no-error-ia32e-la-to-pa-page-dir-ptr-table-2M-pages-with-disjoint-!memi
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
                (equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps ptr-table-entry) 0)
                ;; For ia32e-la-to-pa-page-directory:
                (equal page-directory-base-addr
                       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
                (equal page-directory-entry-addr
                       (page-directory-entry-addr lin-addr page-directory-base-addr))
                (equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps page-directory-entry) 1)
                (pairwise-disjoint-p-aux
                 (addr-range 1 addr)
                 (translation-governing-addresses-for-page-dir-ptr-table
                  lin-addr ptr-table-base-addr x86))
                (integerp addr))
           (equal (mv-nth
                   0
                   (ia32e-la-to-pa-page-dir-ptr-table
                    lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl
                    (xw :mem addr val x86)))
                  nil))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-dir-ptr-table)
                  (not
                   addr-range-1)))

(defrule mv-nth-0-no-error-ia32e-la-to-pa-page-dir-ptr-table-2M-pages-with-disjoint-wm-low-64
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
                (equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps ptr-table-entry) 0)
                ;; For ia32e-la-to-pa-page-directory:
                (equal page-directory-base-addr
                       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
                (equal page-directory-entry-addr
                       (page-directory-entry-addr lin-addr page-directory-base-addr))
                (equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps page-directory-entry) 1)
                (pairwise-disjoint-p-aux
                 (addr-range 8 addr)
                 (translation-governing-addresses-for-page-dir-ptr-table
                  lin-addr ptr-table-base-addr x86))
                (integerp addr))
           (equal (mv-nth
                   0
                   (ia32e-la-to-pa-page-dir-ptr-table
                    lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl
                    (wm-low-64 addr val x86)))
                  nil))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-dir-ptr-table)
                  (not)))

(defrule mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-4K-or-2M-pages
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
                (equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps ptr-table-entry) 0))
           (equal (mv-nth
                   1
                   (ia32e-la-to-pa-page-dir-ptr-table
                    lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86))
                  (mv-nth
                   1
                   (ia32e-la-to-pa-page-directory
                    lin-addr
                    (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12)
                    wp smep nxe r-w-x cpl x86))))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-dir-ptr-table)
                  (not)))

(defrule mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-2M-pages-with-disjoint-!memi
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
                (equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps ptr-table-entry) 0)
                ;; For ia32e-la-to-pa-page-directory:
                (equal page-directory-base-addr
                       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
                (equal page-directory-entry-addr
                       (page-directory-entry-addr lin-addr page-directory-base-addr))
                (equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps page-directory-entry) 1)
                (pairwise-disjoint-p-aux
                 (addr-range 1 addr)
                 (translation-governing-addresses-for-page-dir-ptr-table
                  lin-addr ptr-table-base-addr x86))
                (integerp addr))
           (equal (mv-nth
                   1
                   (ia32e-la-to-pa-page-dir-ptr-table
                    lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl
                    (xw :mem addr val x86)))
                  (mv-nth
                   1
                   (ia32e-la-to-pa-page-dir-ptr-table
                    lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86))))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-dir-ptr-table)
                  (not
                   addr-range-1)))

(defrule mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-2M-pages-with-disjoint-wm-low-64
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
                (equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps ptr-table-entry) 0)
                ;; For ia32e-la-to-pa-page-directory:
                (equal page-directory-base-addr
                       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
                (equal page-directory-entry-addr
                       (page-directory-entry-addr lin-addr page-directory-base-addr))
                (equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps page-directory-entry) 1)
                (pairwise-disjoint-p-aux
                 (addr-range 8 addr)
                 (translation-governing-addresses-for-page-dir-ptr-table
                  lin-addr ptr-table-base-addr x86))
                (integerp addr))
           (equal (mv-nth
                   1
                   (ia32e-la-to-pa-page-dir-ptr-table
                    lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl
                    (wm-low-64 addr val x86)))
                  (mv-nth
                   1
                   (ia32e-la-to-pa-page-dir-ptr-table
                    lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86))))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-dir-ptr-table)
                  (not)))


(defrule mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4K-or-2M-pages
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
                (equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps ptr-table-entry) 0)
                (equal accessed (ia32e-page-tables-slice :a ptr-table-entry))
                (equal accessed-entry (if (equal accessed 0)
                                          (set-accessed-bit ptr-table-entry)
                                        ptr-table-entry)))
           (equal (mv-nth
                   2
                   (ia32e-la-to-pa-page-dir-ptr-table
                    lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86))
                  (let* ((page-dir-x86
                          (mv-nth
                           2
                           (ia32e-la-to-pa-page-directory
                            lin-addr
                            (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12)
                            wp smep nxe r-w-x cpl x86)))
                         (accessed-x86
                          (if (equal accessed 0)
                              (wm-low-64 ptr-table-entry-addr accessed-entry page-dir-x86)
                            page-dir-x86)))
                    accessed-x86)))

  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-dir-ptr-table)
                  (not
                   mv-nth-1-no-error-ia32e-la-to-pa-page-directory-4K-pages
                   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages)))

;; 4K pages:

(defrule mv-nth-0-no-error-ia32e-la-to-pa-page-dir-ptr-table-4K-pages-with-disjoint-!memi
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
                (equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)
                ;; For ia32e-la-to-pa-page-directory:
                (equal page-directory-base-addr
                       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
                (equal page-directory-entry-addr
                       (page-directory-entry-addr lin-addr page-directory-base-addr))
                (equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps page-directory-entry) 0)
                ;; For ia32e-la-to-pa-page-table:
                (equal page-table-base-addr
                       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
                (equal page-table-entry-addr
                       (page-table-entry-addr lin-addr page-table-base-addr))
                (pairwise-disjoint-p-aux
                 (addr-range 1 addr)
                 (translation-governing-addresses-for-page-dir-ptr-table
                  lin-addr ptr-table-base-addr x86))
                (integerp addr))
           (equal (mv-nth
                   0
                   (ia32e-la-to-pa-page-dir-ptr-table
                    lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl
                    (xw :mem addr val x86)))
                  nil))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-dir-ptr-table)
                  (not
                   addr-range-1)))

(defrule mv-nth-0-no-error-ia32e-la-to-pa-page-dir-ptr-table-4K-pages-with-disjoint-wm-low-64
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
                (equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)a
                ;; For ia32e-la-to-pa-page-directory:
                (equal page-directory-base-addr
                       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
                (equal page-directory-entry-addr
                       (page-directory-entry-addr lin-addr page-directory-base-addr))
                (equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps page-directory-entry) 0)
                ;; For ia32e-la-to-pa-page-table:
                (equal page-table-base-addr
                       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
                (equal page-table-entry-addr
                       (page-table-entry-addr lin-addr page-table-base-addr))
                (pairwise-disjoint-p-aux
                 (addr-range 8 addr)
                 (translation-governing-addresses-for-page-dir-ptr-table
                  lin-addr ptr-table-base-addr x86))
                (integerp addr))
           (equal (mv-nth
                   0
                   (ia32e-la-to-pa-page-dir-ptr-table
                    lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl
                    (wm-low-64 addr val x86)))
                  nil))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-dir-ptr-table)
                  (not)))


(defrule mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-4K-pages-with-disjoint-!memi
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
                (equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)
                ;; For ia32e-la-to-pa-page-directory:
                (equal page-directory-base-addr
                       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
                (equal page-directory-entry-addr
                       (page-directory-entry-addr lin-addr page-directory-base-addr))
                (equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps page-directory-entry) 0)
                ;; For ia32e-la-to-pa-page-table:
                (equal page-table-base-addr
                       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
                (equal page-table-entry-addr
                       (page-table-entry-addr lin-addr page-table-base-addr))
                (pairwise-disjoint-p-aux
                 (addr-range 1 addr)
                 (translation-governing-addresses-for-page-dir-ptr-table
                  lin-addr ptr-table-base-addr x86))
                (integerp addr))
           (equal (mv-nth
                   1
                   (ia32e-la-to-pa-page-dir-ptr-table
                    lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl
                    (xw :mem addr val x86)))
                  (mv-nth
                   1
                   (ia32e-la-to-pa-page-dir-ptr-table
                    lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86))))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-dir-ptr-table)
                  (not
                   mv-nth-1-no-error-ia32e-la-to-pa-page-directory-4K-pages
                   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages
                   addr-range-1)))

(defrule mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-4K-pages-with-disjoint-wm-low-64
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
                (equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps ptr-table-entry) 0)
                ;; For ia32e-la-to-pa-page-directory:
                (equal page-directory-base-addr
                       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
                (equal page-directory-entry-addr
                       (page-directory-entry-addr lin-addr page-directory-base-addr))
                (equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps page-directory-entry) 0)
                ;; For ia32e-la-to-pa-page-table:
                (equal page-table-base-addr
                       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
                (equal page-table-entry-addr
                       (page-table-entry-addr lin-addr page-table-base-addr))
                (pairwise-disjoint-p-aux
                 (addr-range 8 addr)
                 (translation-governing-addresses-for-page-dir-ptr-table
                  lin-addr ptr-table-base-addr x86))
                (integerp addr))
           (equal (mv-nth
                   1
                   (ia32e-la-to-pa-page-dir-ptr-table
                    lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl
                    (wm-low-64 addr val x86)))
                  (mv-nth
                   1
                   (ia32e-la-to-pa-page-dir-ptr-table
                    lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86))))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-dir-ptr-table)
                  (not
                   mv-nth-1-no-error-ia32e-la-to-pa-page-directory-4K-pages
                   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages)))

;; ......................................................................
;; Reading page-dir-ptr-table-entry-addr again using rm-low-64:
;; ......................................................................

;; 1G pages:

(defruled rm-low-64-and-page-dir-ptr-table-1G-pages
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
                (equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps ptr-table-entry) 1)
                (physical-address-p ptr-table-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 ptr-table-base-addr) 0)
                (x86p x86))
           (equal (rm-low-64 ptr-table-entry-addr
                             (mv-nth
                              2
                              (ia32e-la-to-pa-page-dir-ptr-table
                               lin-addr ptr-table-base-addr wp smep nxe r-w-x
                               cpl x86)))
                  (cond
                   ( ;; Accessed and dirty bits are set.
                    (and (equal (ia32e-page-tables-slice :a ptr-table-entry) 1)
                         (equal (ia32e-page-tables-slice :d ptr-table-entry) 1))
                    (rm-low-64 ptr-table-entry-addr x86))

                   ( ;; Accessed bit is set and dirty bit is clear and
                    ;; memory write is being done.
                    (and (equal (ia32e-page-tables-slice :a ptr-table-entry) 1)
                         (equal (ia32e-page-tables-slice :d ptr-table-entry) 0)
                         (equal r-w-x :w))
                    (set-dirty-bit (rm-low-64 ptr-table-entry-addr x86)))

                   ( ;; Accessed bit is set and dirty bit is clear and
                    ;; memory write is not being done.
                    (and (equal (ia32e-page-tables-slice :a ptr-table-entry) 1)
                         (equal (ia32e-page-tables-slice :d ptr-table-entry) 0)
                         (not (equal r-w-x :w)))
                    (rm-low-64 ptr-table-entry-addr x86))

                   ( ;; Accessed and dirty bits are clear and memory
                    ;; write is being done.
                    (and (equal (ia32e-page-tables-slice :a ptr-table-entry) 0)
                         (equal (ia32e-page-tables-slice :d ptr-table-entry) 0)
                         (equal r-w-x :w))
                    (set-dirty-bit
                     (set-accessed-bit
                      (rm-low-64 ptr-table-entry-addr x86))))

                   ( ;; Accessed bit and dirty bits are clear and memory
                    ;; write is not being done.
                    (and (equal (ia32e-page-tables-slice :a ptr-table-entry) 0)
                         (equal (ia32e-page-tables-slice :d ptr-table-entry) 0)
                         (not (equal r-w-x :w)))
                    (set-accessed-bit (rm-low-64 ptr-table-entry-addr x86)))

                   (t
                    ;; This shouldn't be reached.
                    (rm-low-64 ptr-table-entry-addr
                               (mv-nth
                                2
                                (ia32e-la-to-pa-page-dir-ptr-table
                                 lin-addr ptr-table-base-addr wp smep nxe r-w-x
                                 cpl x86)))))))

  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-dir-ptr-table)
                  (not
                   unsigned-byte-p
                   signed-byte-p
                   mv-nth-1-no-error-ia32e-la-to-pa-page-directory-4K-pages
                   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages)))

;; 2M pages:

(defruled rm-low-64-and-page-dir-ptr-table-2M-pages
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
                (equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)

                ;; For ia32e-la-to-pa-page-directory:
                (equal page-directory-base-addr
                       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
                (equal page-directory-entry-addr
                       (page-directory-entry-addr lin-addr page-directory-base-addr))

                (equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps page-directory-entry) 1)

                ;; (disjoint-p
                ;;  (addr-range 8 ptr-table-entry-addr)
                ;;  (addr-range 8 page-directory-entry-addr))
                (pairwise-disjoint-p
                 (translation-governing-addresses-for-page-dir-ptr-table
                  lin-addr ptr-table-base-addr x86))
                (physical-address-p ptr-table-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 ptr-table-base-addr) 0)
                (x86p x86))

           (equal (rm-low-64 ptr-table-entry-addr
                             (mv-nth
                              2
                              (ia32e-la-to-pa-page-dir-ptr-table
                               lin-addr ptr-table-base-addr wp smep nxe r-w-x
                               cpl x86)))
                  (cond
                   ((equal (ia32e-page-tables-slice :a ptr-table-entry) 0)
                    (set-accessed-bit ptr-table-entry))
                   ((equal (ia32e-page-tables-slice :a ptr-table-entry) 1)
                    ptr-table-entry))))

  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-dir-ptr-table)
                  (not
                   unsigned-byte-p
                   signed-byte-p
                   mv-nth-1-no-error-ia32e-la-to-pa-page-directory-4K-pages
                   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages)))

;; 4K pages:

(defruled rm-low-64-and-page-dir-ptr-table-4K-pages
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
                (equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)

                ;; For ia32e-la-to-pa-page-directory:
                (equal page-directory-base-addr
                       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
                (equal page-directory-entry-addr
                       (page-directory-entry-addr lin-addr page-directory-base-addr))

                (equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps page-directory-entry) 0)

                (equal page-table-base-addr
                       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
                (equal page-table-entry-addr
                       (page-table-entry-addr lin-addr page-table-base-addr))
                (pairwise-disjoint-p
                 (translation-governing-addresses-for-page-dir-ptr-table
                  lin-addr ptr-table-base-addr x86))
                (physical-address-p ptr-table-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 ptr-table-base-addr) 0)
                (x86p x86))

           (equal (rm-low-64 ptr-table-entry-addr
                             (mv-nth
                              2
                              (ia32e-la-to-pa-page-dir-ptr-table
                               lin-addr ptr-table-base-addr wp smep nxe r-w-x
                               cpl x86)))
                  (cond
                   ((equal (ia32e-page-tables-slice :a ptr-table-entry) 0)
                    (set-accessed-bit ptr-table-entry))
                   ((equal (ia32e-page-tables-slice :a ptr-table-entry) 1)
                    ptr-table-entry))))

  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-dir-ptr-table)
                  (disjoint-p-cons
                   member-p-cons
                   not
                   mv-nth-1-no-error-ia32e-la-to-pa-page-directory-4K-pages
                   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages
                   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-2M-pages
                   unsigned-byte-p
                   signed-byte-p
                   acl2::mv-nth-cons-meta)))

;; ......................................................................
;; !memi and state after data structure walk WoW theorem:
;; ......................................................................

;; 1G pages:

(defrule disjoint-!memi-mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
                (equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  ptr-table-entry) 1)

                (disjoint-p
                 (addr-range 1 addr)
                 (addr-range 8 ptr-table-entry-addr))
                (integerp addr))
           (equal
            (mv-nth
             2
             (ia32e-la-to-pa-page-dir-ptr-table
              lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl
              (xw :mem addr val x86)))
            (xw :mem addr val
                   (mv-nth
                    2
                    (ia32e-la-to-pa-page-dir-ptr-table
                     lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)))))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-dir-ptr-table)
                  (not
                   addr-range-1
                   mv-nth-1-no-error-ia32e-la-to-pa-page-directory-4K-pages
                   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages)))

;; 2M pages:

(defrule disjoint-!memi-mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-2M-pages
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
                (equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)

                ;; For ia32e-la-to-pa-page-directory:
                (equal page-directory-base-addr
                       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
                (equal page-directory-entry-addr
                       (page-directory-entry-addr lin-addr page-directory-base-addr))

                (pairwise-disjoint-p-aux
                 (addr-range 1 addr)
                 (list (addr-range 8 ptr-table-entry-addr)
                       (addr-range 8 page-directory-entry-addr)))

                (equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps page-directory-entry) 1)
                (integerp addr))
           (equal
            (mv-nth
             2
             (ia32e-la-to-pa-page-dir-ptr-table
              lin-addr ptr-table-base-addr wp smep nxe
              r-w-x cpl (xw :mem addr val x86)))
            (xw :mem addr val
                   (mv-nth
                    2
                    (ia32e-la-to-pa-page-dir-ptr-table
                     lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)))))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-dir-ptr-table)
                  (not
                   addr-range-1
                   ia32e-la-to-pa-page-directory-entry-validp
                   ia32e-la-to-pa-page-table-entry-validp
                   mv-nth-1-no-error-ia32e-la-to-pa-page-directory-4K-pages
                   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages)))

;; 4K pages:

(defrule disjoint-!memi-mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4K-pages
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
                (equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)

                ;; For ia32e-la-to-pa-page-directory:
                (equal page-directory-base-addr
                       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
                (equal page-directory-entry-addr
                       (page-directory-entry-addr lin-addr page-directory-base-addr))

                (equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps page-directory-entry) 0)

                ;; For ia32e-la-to-pa-page-table:
                (equal page-table-base-addr
                       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
                (equal page-table-entry-addr
                       (page-table-entry-addr lin-addr page-table-base-addr))

                (pairwise-disjoint-p-aux
                 (addr-range 1 addr)
                 (translation-governing-addresses-for-page-dir-ptr-table
                  lin-addr ptr-table-base-addr x86))
                (integerp addr))
           (equal
            (mv-nth
             2
             (ia32e-la-to-pa-page-dir-ptr-table
              lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl
              (xw :mem addr val x86)))
            (xw :mem
             addr val
             (mv-nth
              2
              (ia32e-la-to-pa-page-dir-ptr-table
               lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)))))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-dir-ptr-table
                   wm-low-64 wm-low-32)
                  (not
                   mv-nth-1-no-error-ia32e-la-to-pa-page-directory-4K-pages
                   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages)))

;; ......................................................................
;; Reading addresses disjoint from page-dir-ptr-table-entry-addr after
;; walking the page directory pointer table:
;; ......................................................................

;; 1G pages:

(defrule disjoint-memi-read-mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
                (equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  ptr-table-entry) 1)

                (disjoint-p
                 (addr-range 1 addr)
                 (addr-range 8 ptr-table-entry-addr)))
           (equal
            (xr :mem addr
                  (mv-nth
                   2
                   (ia32e-la-to-pa-page-dir-ptr-table
                    lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)))
            (xr :mem addr x86)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-dir-ptr-table)
                  (not
                   addr-range-1
                   mv-nth-1-no-error-ia32e-la-to-pa-page-directory-4K-pages
                   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages)))

(defrule disjoint-rm-low-64-read-mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
                (equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  ptr-table-entry) 1)

                (disjoint-p
                 (addr-range 8 addr)
                 (addr-range 8 ptr-table-entry-addr))
                (integerp addr))
           (equal
            (rm-low-64 addr
                       (mv-nth
                        2
                        (ia32e-la-to-pa-page-dir-ptr-table
                         lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)))
            (rm-low-64 addr x86)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-dir-ptr-table)
                  (not
                   mv-nth-1-no-error-ia32e-la-to-pa-page-directory-4K-pages
                   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages)))

(defrule disjoint-rm-low-32-read-mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
                (equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  ptr-table-entry) 1)

                (disjoint-p
                 (addr-range 4 addr)
                 (addr-range 8 ptr-table-entry-addr))
                (integerp addr))
           (equal
            (rm-low-32 addr
                       (mv-nth
                        2
                        (ia32e-la-to-pa-page-dir-ptr-table
                         lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)))
            (rm-low-32 addr x86)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-dir-ptr-table
                   wm-low-64)
                  (not
                   mv-nth-1-no-error-ia32e-la-to-pa-page-directory-4K-pages
                   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages)))

;; 2M pages:

(defrule disjoint-memi-read-mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-2M-pages
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
                (equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)

                ;; For ia32e-la-to-pa-page-directory:
                (equal page-directory-base-addr
                       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
                (equal page-directory-entry-addr
                       (page-directory-entry-addr lin-addr page-directory-base-addr))

                (pairwise-disjoint-p-aux
                 (addr-range 1 addr)
                 (translation-governing-addresses-for-page-dir-ptr-table
                  lin-addr ptr-table-base-addr x86))

                (equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps page-directory-entry) 1))
           (equal
            (xr :mem addr
                  (mv-nth
                   2
                   (ia32e-la-to-pa-page-dir-ptr-table
                    lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)))
            (xr :mem addr x86)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-dir-ptr-table)
                  (not
                   addr-range-1
                   ia32e-la-to-pa-page-directory-entry-validp
                   ia32e-la-to-pa-page-table-entry-validp
                   mv-nth-1-no-error-ia32e-la-to-pa-page-directory-4K-pages
                   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages)))

(defrule disjoint-rm-low-64-read-mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-2M-pages
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
                (equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)

                ;; For ia32e-la-to-pa-page-directory:
                (equal page-directory-base-addr
                       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
                (equal page-directory-entry-addr
                       (page-directory-entry-addr lin-addr page-directory-base-addr))

                (pairwise-disjoint-p-aux
                 (addr-range 8 addr)
                 (translation-governing-addresses-for-page-dir-ptr-table
                  lin-addr ptr-table-base-addr x86))

                (equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps page-directory-entry) 1)
                (integerp addr))
           (equal
            (rm-low-64 addr
                       (mv-nth
                        2
                        (ia32e-la-to-pa-page-dir-ptr-table
                         lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)))
            (rm-low-64 addr x86)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-dir-ptr-table)
                  (not
                   ia32e-la-to-pa-page-directory-entry-validp
                   ia32e-la-to-pa-page-table-entry-validp
                   mv-nth-1-no-error-ia32e-la-to-pa-page-directory-4K-pages
                   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages)))

(defrule disjoint-rm-low-32-read-mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-2M-pages
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
                (equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)

                ;; For ia32e-la-to-pa-page-directory:
                (equal page-directory-base-addr
                       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
                (equal page-directory-entry-addr
                       (page-directory-entry-addr lin-addr page-directory-base-addr))

                (pairwise-disjoint-p-aux
                 (addr-range 4 addr)
                 (translation-governing-addresses-for-page-dir-ptr-table
                  lin-addr ptr-table-base-addr x86))
                (equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps page-directory-entry) 1)
                (integerp addr))
           (equal
            (rm-low-32 addr
                       (mv-nth
                        2
                        (ia32e-la-to-pa-page-dir-ptr-table
                         lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)))
            (rm-low-32 addr x86)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-dir-ptr-table
                   wm-low-64)
                  (not
                   ia32e-la-to-pa-page-directory-entry-validp
                   ia32e-la-to-pa-page-table-entry-validp
                   mv-nth-1-no-error-ia32e-la-to-pa-page-directory-4K-pages
                   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages)))

;; 4K pages:

(defrule disjoint-memi-read-mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4K-pages
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
                (equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)

                ;; For ia32e-la-to-pa-page-directory:
                (equal page-directory-base-addr
                       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
                (equal page-directory-entry-addr
                       (page-directory-entry-addr lin-addr page-directory-base-addr))

                (equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps page-directory-entry) 0)

                ;; For ia32e-la-to-pa-page-table:
                (equal page-table-base-addr
                       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
                (equal page-table-entry-addr
                       (page-table-entry-addr lin-addr page-table-base-addr))

                (pairwise-disjoint-p-aux
                 (addr-range 1 addr)
                 (translation-governing-addresses-for-page-dir-ptr-table
                  lin-addr ptr-table-base-addr x86)))
           (equal
            (xr :mem
             addr
             (mv-nth
              2
              (ia32e-la-to-pa-page-dir-ptr-table
               lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)))
            (xr :mem addr x86)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-dir-ptr-table
                   wm-low-64 wm-low-32 ifix)
                  (not
                   mv-nth-1-no-error-ia32e-la-to-pa-page-directory-4K-pages
                   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages)))

(defrule disjoint-rm-low-64-read-mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4K-pages
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
                (equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)

                ;; For ia32e-la-to-pa-page-directory:
                (equal page-directory-base-addr
                       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
                (equal page-directory-entry-addr
                       (page-directory-entry-addr lin-addr page-directory-base-addr))

                (equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps page-directory-entry) 0)

                ;; For ia32e-la-to-pa-page-table:
                (equal page-table-base-addr
                       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
                (equal page-table-entry-addr
                       (page-table-entry-addr lin-addr page-table-base-addr))

                (pairwise-disjoint-p-aux
                 (addr-range 8 addr)
                 (translation-governing-addresses-for-page-dir-ptr-table
                  lin-addr ptr-table-base-addr x86))
                (integerp addr))
           (equal
            (rm-low-64
             addr
             (mv-nth
              2
              (ia32e-la-to-pa-page-dir-ptr-table
               lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)))
            (rm-low-64 addr x86)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-dir-ptr-table)
                  (not
                   mv-nth-1-no-error-ia32e-la-to-pa-page-directory-4K-pages
                   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages)))

(defrule disjoint-rm-low-32-read-mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4K-pages
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
                (equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)

                ;; For ia32e-la-to-pa-page-directory:
                (equal page-directory-base-addr
                       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
                (equal page-directory-entry-addr
                       (page-directory-entry-addr lin-addr page-directory-base-addr))

                (equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps page-directory-entry) 0)

                ;; For ia32e-la-to-pa-page-table:
                (equal page-table-base-addr
                       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
                (equal page-table-entry-addr
                       (page-table-entry-addr lin-addr page-table-base-addr))

                (pairwise-disjoint-p-aux
                 (addr-range 4 addr)
                 (translation-governing-addresses-for-page-dir-ptr-table
                  lin-addr ptr-table-base-addr x86))
                (integerp addr))
           (equal
            (rm-low-32 addr
                       (mv-nth
                        2
                        (ia32e-la-to-pa-page-dir-ptr-table
                         lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)))
            (rm-low-32 addr x86)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-dir-ptr-table
                   wm-low-64)
                  (not
                   mv-nth-1-no-error-ia32e-la-to-pa-page-directory-4K-pages
                   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages)))

;; ......................................................................
;; Theorems that state that the validity of the page directory pointer
;; table entry is preserved when writes are done to disjoint addresses
;; or :a/:d are set:
;; ......................................................................

;; 1G pages:

(defrule entry-with-disjoint-!memi-still-valid-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
                (equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  ptr-table-entry) 1)
                (disjoint-p (addr-range 1 addr)
                            (addr-range 8 ptr-table-entry-addr))
                (integerp addr)
                (physical-address-p ptr-table-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 ptr-table-base-addr) 0)
                (x86p x86))
           (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
            lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl
            (xw :mem addr val x86)))
  :in-theory (e/d (ia32e-la-to-pa-page-dir-ptr-table)
                  (not
                   mv-nth-1-no-error-ia32e-la-to-pa-page-directory-4K-pages
                   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages
                   addr-range-1
                   unsigned-byte-p
                   signed-byte-p)))

(defrule entry-with-disjoint-wm-low-64-still-valid-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
                (equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  ptr-table-entry) 1)
                (disjoint-p (addr-range 8 addr)
                            (addr-range 8 ptr-table-entry-addr))
                (integerp addr)
                (physical-address-p ptr-table-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 ptr-table-base-addr) 0)
                (x86p x86))
           (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
            lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl
            (wm-low-64 addr val x86)))
  :in-theory (e/d (ia32e-la-to-pa-page-dir-ptr-table)
                  (not
                   mv-nth-1-no-error-ia32e-la-to-pa-page-directory-4K-pages
                   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages
                   unsigned-byte-p
                   signed-byte-p)))

(defrule entry-with-accessed-bit-set-still-valid-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
                (equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  ptr-table-entry) 1)
                (physical-address-p ptr-table-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 ptr-table-base-addr) 0)
                (x86p x86))
           (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
            lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl
            (wm-low-64
             ptr-table-entry-addr
             ;; (!ia32e-page-tables-slice :a 1 ptr-table-entry)
             ;; (logior 32 (logand 18446744073709551583 ptr-table-entry))
             (set-accessed-bit ptr-table-entry)
             x86)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-dir-ptr-table)
                  (mv-nth-1-no-error-ia32e-la-to-pa-page-directory-4K-pages
                   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages
                   not
                   unsigned-byte-p
                   signed-byte-p)))

(defrule entry-with-dirty-bit-set-still-valid-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
                (equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  ptr-table-entry) 1)
                (physical-address-p ptr-table-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 ptr-table-base-addr) 0)
                (x86p x86))
           (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
            lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl
            (wm-low-64
             ptr-table-entry-addr
             ;; (!ia32e-page-tables-slice :d 1 ptr-table-entry)
             ;; (logior 64 (logand 18446744073709551551 ptr-table-entry))
             (set-dirty-bit ptr-table-entry)
             x86)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-dir-ptr-table)
                  (mv-nth-1-no-error-ia32e-la-to-pa-page-directory-4K-pages
                   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages
                   not
                   unsigned-byte-p
                   signed-byte-p)))

(defrule entry-with-accessed-and-dirty-bits-set-still-valid-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
                (equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  ptr-table-entry) 1)
                (physical-address-p ptr-table-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 ptr-table-base-addr) 0)
                (x86p x86))
           (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
            lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl
            (wm-low-64
             ptr-table-entry-addr
             ;; (!ia32e-page-tables-slice :d 1 (!ia32e-page-tables-slice :a 1 ptr-table-entry))
             ;; (logior
             ;;  64
             ;;  (logand
             ;;   18446744073709551551
             ;;   (logior 32 (logand 18446744073709551583 ptr-table-entry))))
             (set-dirty-bit (set-accessed-bit ptr-table-entry))
             x86)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-dir-ptr-table)
                  (mv-nth-1-no-error-ia32e-la-to-pa-page-directory-4K-pages
                   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages
                   not
                   unsigned-byte-p
                   signed-byte-p)))

;; 2M pages:

(defrule entry-with-disjoint-!memi-still-valid-ia32e-la-to-pa-page-dir-ptr-table-2M-pages
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
                (equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)
                ;; For ia32e-la-to-pa-page-directory:
                (equal page-directory-base-addr
                       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
                (equal page-directory-entry-addr
                       (page-directory-entry-addr lin-addr page-directory-base-addr))
                (equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps page-directory-entry) 1)
                (pairwise-disjoint-p-aux
                 (addr-range 1 addr)
                 (translation-governing-addresses-for-page-dir-ptr-table
                  lin-addr ptr-table-base-addr x86))
                (integerp addr)
                (physical-address-p ptr-table-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 ptr-table-base-addr) 0)
                (x86p x86))
           (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
            lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl
            (xw :mem addr val x86)))
  :in-theory (e/d (ia32e-la-to-pa-page-dir-ptr-table)
                  (mv-nth-1-no-error-ia32e-la-to-pa-page-directory-4K-pages
                   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages
                   not
                   addr-range-1
                   unsigned-byte-p
                   signed-byte-p)))

(defrule entry-with-disjoint-wm-low-64-still-valid-ia32e-la-to-pa-page-dir-ptr-table-2M-pages
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
                (equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)
                ;; For ia32e-la-to-pa-page-directory:
                (equal page-directory-base-addr
                       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
                (equal page-directory-entry-addr
                       (page-directory-entry-addr lin-addr page-directory-base-addr))
                (equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps page-directory-entry) 1)
                (pairwise-disjoint-p-aux
                 (addr-range 8 addr)
                 (translation-governing-addresses-for-page-dir-ptr-table
                  lin-addr ptr-table-base-addr x86))
                (integerp addr)
                (physical-address-p ptr-table-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 ptr-table-base-addr) 0)
                (x86p x86))
           (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
            lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl
            (wm-low-64 addr val x86)))
  :in-theory (e/d (ia32e-la-to-pa-page-dir-ptr-table)
                  (mv-nth-1-no-error-ia32e-la-to-pa-page-directory-4K-pages
                   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages
                   not
                   unsigned-byte-p
                   signed-byte-p)))

(defrule entry-with-accessed-bit-set-still-valid-ia32e-la-to-pa-page-dir-ptr-table-2M-pages
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
                (equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)
                ;; For ia32e-la-to-pa-page-directory:
                (equal page-directory-base-addr
                       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
                (equal page-directory-entry-addr
                       (page-directory-entry-addr lin-addr page-directory-base-addr))
                (equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps page-directory-entry) 1)
                ;; (disjoint-p
                ;;  (addr-range 8 ptr-table-entry-addr)
                ;;  (addr-range 8 page-directory-entry-addr))
                (pairwise-disjoint-p
                 (translation-governing-addresses-for-page-dir-ptr-table
                  lin-addr ptr-table-base-addr x86))
                (physical-address-p ptr-table-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 ptr-table-base-addr) 0)
                (x86p x86))
           (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
            lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl
            (wm-low-64
             ptr-table-entry-addr
             ;; (!ia32e-page-tables-slice :a 1 ptr-table-entry)
             ;; (logior 32 (logand 18446744073709551583 ptr-table-entry))
             (set-accessed-bit ptr-table-entry)
             x86)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-dir-ptr-table)
                  (mv-nth-1-no-error-ia32e-la-to-pa-page-directory-2M-pages
                   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-2M-pages
                   not
                   unsigned-byte-p
                   signed-byte-p)))

(defrule entry-with-dirty-bit-set-still-valid-ia32e-la-to-pa-page-dir-ptr-table-2M-pages
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
                (equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)
                ;; For ia32e-la-to-pa-page-directory:
                (equal page-directory-base-addr
                       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
                (equal page-directory-entry-addr
                       (page-directory-entry-addr lin-addr page-directory-base-addr))
                (equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps page-directory-entry) 1)
                ;; (disjoint-p
                ;;  (addr-range 8 ptr-table-entry-addr)
                ;;  (addr-range 8 page-directory-entry-addr))
                (pairwise-disjoint-p
                 (translation-governing-addresses-for-page-dir-ptr-table
                  lin-addr ptr-table-base-addr x86))
                (physical-address-p ptr-table-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 ptr-table-base-addr) 0)
                (x86p x86))
           (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
            lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl
            (wm-low-64
             ptr-table-entry-addr
             ;; (!ia32e-page-tables-slice :d 1 ptr-table-entry)
             ;; (logior 64 (logand 18446744073709551551 ptr-table-entry))
             (set-dirty-bit ptr-table-entry)
             x86)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-dir-ptr-table)
                  (mv-nth-1-no-error-ia32e-la-to-pa-page-directory-2M-pages
                   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-2M-pages
                   not
                   unsigned-byte-p
                   signed-byte-p)))

(defrule entry-with-accessed-and-dirty-bits-set-still-valid-ia32e-la-to-pa-page-dir-ptr-table-2M-pages
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
                (equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)
                ;; For ia32e-la-to-pa-page-directory:
                (equal page-directory-base-addr
                       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
                (equal page-directory-entry-addr
                       (page-directory-entry-addr lin-addr page-directory-base-addr))
                (equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps page-directory-entry) 1)
                ;; (disjoint-p
                ;;  (addr-range 8 ptr-table-entry-addr)
                ;;  (addr-range 8 page-directory-entry-addr))
                (pairwise-disjoint-p
                 (translation-governing-addresses-for-page-dir-ptr-table
                  lin-addr ptr-table-base-addr x86))
                (physical-address-p ptr-table-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 ptr-table-base-addr) 0)
                (x86p x86))
           (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
            lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl
            (wm-low-64
             ptr-table-entry-addr
             ;; (!ia32e-page-tables-slice :d 1 (!ia32e-page-tables-slice :a 1 ptr-table-entry))
             ;; (logior
             ;;  64
             ;;  (logand
             ;;   18446744073709551551
             ;;   (logior 32 (logand 18446744073709551583 ptr-table-entry))))
             (set-dirty-bit (set-accessed-bit ptr-table-entry))
             x86)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-dir-ptr-table)
                  (mv-nth-1-no-error-ia32e-la-to-pa-page-directory-2M-pages
                   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-2M-pages
                   not
                   unsigned-byte-p
                   signed-byte-p)))

;; 4K pages:

(defrule entry-with-disjoint-!memi-still-valid-ia32e-la-to-pa-page-dir-ptr-table-4K-pages
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
                (equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)

                ;; For ia32e-la-to-pa-page-directory:
                (equal page-directory-base-addr
                       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
                (equal page-directory-entry-addr
                       (page-directory-entry-addr lin-addr page-directory-base-addr))

                (equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps page-directory-entry) 0)

                ;; For ia32e-la-to-pa-page-table:
                (equal page-table-base-addr
                       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
                (equal page-table-entry-addr
                       (page-table-entry-addr lin-addr page-table-base-addr))

                (pairwise-disjoint-p-aux
                 (addr-range 1 addr)
                 (translation-governing-addresses-for-page-dir-ptr-table
                  lin-addr ptr-table-base-addr x86))
                (integerp addr)

                (physical-address-p ptr-table-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 ptr-table-base-addr) 0)
                (x86p x86))
           (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
            lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl
            (xw :mem addr val x86)))
  :in-theory (e/d (ia32e-la-to-pa-page-dir-ptr-table)
                  (mv-nth-1-no-error-ia32e-la-to-pa-page-directory-4K-pages
                   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages
                   not
                   addr-range-1
                   unsigned-byte-p
                   signed-byte-p)))

(defrule entry-with-disjoint-wm-low-64-still-valid-ia32e-la-to-pa-page-dir-ptr-table-4K-pages
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
                (equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)

                ;; For ia32e-la-to-pa-page-directory:
                (equal page-directory-base-addr
                       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
                (equal page-directory-entry-addr
                       (page-directory-entry-addr lin-addr page-directory-base-addr))

                (equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps page-directory-entry) 0)

                ;; For ia32e-la-to-pa-page-table:
                (equal page-table-base-addr
                       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
                (equal page-table-entry-addr
                       (page-table-entry-addr lin-addr page-table-base-addr))

                (pairwise-disjoint-p-aux
                 (addr-range 8 addr)
                 (translation-governing-addresses-for-page-dir-ptr-table
                  lin-addr ptr-table-base-addr x86))
                (integerp addr)

                (physical-address-p ptr-table-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 ptr-table-base-addr) 0)
                (x86p x86))
           (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
            lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl
            (wm-low-64 addr val x86)))
  :in-theory (e/d (ia32e-la-to-pa-page-dir-ptr-table)
                  (mv-nth-1-no-error-ia32e-la-to-pa-page-directory-4K-pages
                   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages
                   not
                   unsigned-byte-p
                   signed-byte-p)))

(defrule entry-with-accessed-bit-set-still-valid-ia32e-la-to-pa-page-dir-ptr-table-4K-pages
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
                (equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)

                ;; For ia32e-la-to-pa-page-directory:
                (equal page-directory-base-addr
                       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
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
                 (translation-governing-addresses-for-page-dir-ptr-table
                  lin-addr ptr-table-base-addr x86))
                (physical-address-p ptr-table-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 ptr-table-base-addr) 0)
                (x86p x86))
           (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
            lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl
            (wm-low-64
             ptr-table-entry-addr
             ;; (!ia32e-page-tables-slice :a 1 ptr-table-entry)
             ;; (logior 32 (logand 18446744073709551583 ptr-table-entry))
             (set-accessed-bit ptr-table-entry)
             x86)))
  :do-not '(preprocess)
  :in-theory (e/d ()
                  (not
                   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages
                   mv-nth-1-no-error-ia32e-la-to-pa-page-directory-4K-pages
                   unsigned-byte-p
                   signed-byte-p)))

(defrule entry-with-dirty-bit-set-still-valid-ia32e-la-to-pa-page-dir-ptr-table-4K-pages
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
                (equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)

                ;; For ia32e-la-to-pa-page-directory:
                (equal page-directory-base-addr
                       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
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
                 (translation-governing-addresses-for-page-dir-ptr-table
                  lin-addr ptr-table-base-addr x86))
                (physical-address-p ptr-table-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 ptr-table-base-addr) 0)
                (x86p x86))
           (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
            lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl
            (wm-low-64
             ptr-table-entry-addr
             ;; (!ia32e-page-tables-slice :d 1 ptr-table-entry)
             ;; (logior 64 (logand 18446744073709551551 ptr-table-entry))
             (set-dirty-bit ptr-table-entry)
             x86)))
  :do-not '(preprocess)
  :in-theory (e/d ()
                  (mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages
                   mv-nth-1-no-error-ia32e-la-to-pa-page-directory-4K-pages
                   not
                   unsigned-byte-p
                   signed-byte-p)))

(defrule entry-with-accessed-and-dirty-bits-set-still-valid-ia32e-la-to-pa-page-dir-ptr-table-4K-pages
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
                (equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)

                ;; For ia32e-la-to-pa-page-directory:
                (equal page-directory-base-addr
                       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
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
                 (translation-governing-addresses-for-page-dir-ptr-table
                  lin-addr ptr-table-base-addr x86))
                (physical-address-p ptr-table-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 ptr-table-base-addr) 0)
                (x86p x86))
           (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
            lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl
            (wm-low-64
             ptr-table-entry-addr
             ;; (!ia32e-page-tables-slice :d 1 (!ia32e-page-tables-slice :a 1 ptr-table-entry))
             ;; (logior
             ;;  64
             ;;  (logand
             ;;   18446744073709551551
             ;;   (logior 32 (logand 18446744073709551583 ptr-table-entry))))
             (set-dirty-bit (set-accessed-bit ptr-table-entry))
             x86)))
  :do-not '(preprocess)
  :in-theory (e/d ()
                  (mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages
                   mv-nth-1-no-error-ia32e-la-to-pa-page-directory-4K-pages
                   not
                   unsigned-byte-p
                   signed-byte-p)))

;; ......................................................................
;; Reading page directory pointer table entry from x86 states where
;; :a/:d are set:
;; ......................................................................

;; 1G pages:

(defrule reading-entry-with-accessed-bit-set-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
                (equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  ptr-table-entry) 1)
                (physical-address-p ptr-table-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 ptr-table-base-addr) 0)
                (x86p x86))
           (equal
            (mv-nth
             1
             (ia32e-la-to-pa-page-dir-ptr-table
              lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl
              (wm-low-64
               ptr-table-entry-addr
               ;; (!ia32e-page-tables-slice :a 1 ptr-table-entry)
               ;; (logior 32 (logand 18446744073709551583 ptr-table-entry))
               (set-accessed-bit ptr-table-entry)
               x86)))
            (mv-nth
             1
             (ia32e-la-to-pa-page-dir-ptr-table
              lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86))))
  :do-not '(preprocess)
  :in-theory (e/d ()
                  (mv-nth-1-no-error-ia32e-la-to-pa-page-directory-4K-pages
                   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages
                   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
                   not
                   unsigned-byte-p
                   signed-byte-p)))

(defrule reading-entry-with-dirty-bit-set-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
                (equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  ptr-table-entry) 1)
                (physical-address-p ptr-table-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 ptr-table-base-addr) 0)
                (x86p x86))
           (equal
            (mv-nth
             1
             (ia32e-la-to-pa-page-dir-ptr-table
              lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl
              (wm-low-64
               ptr-table-entry-addr
               ;; (!ia32e-page-tables-slice :d 1 ptr-table-entry)
               ;; (logior 64 (logand 18446744073709551551 ptr-table-entry))
               (set-dirty-bit ptr-table-entry)
               x86)))
            (mv-nth
             1
             (ia32e-la-to-pa-page-dir-ptr-table
              lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86))))
  :do-not '(preprocess)
  :in-theory (e/d ()
                  (mv-nth-1-no-error-ia32e-la-to-pa-page-directory-4K-pages
                   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages
                   not
                   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
                   unsigned-byte-p
                   signed-byte-p)))

(defrule reading-entry-with-accessed-and-dirty-bits-set-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
                (equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  ptr-table-entry) 1)
                (physical-address-p ptr-table-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 ptr-table-base-addr) 0)
                (x86p x86))
           (equal
            (mv-nth
             1
             (ia32e-la-to-pa-page-dir-ptr-table
              lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl
              (wm-low-64
               ptr-table-entry-addr
               ;; (!ia32e-page-tables-slice :d 1 (!ia32e-page-tables-slice :a 1 ptr-table-entry))
               ;; (logior
               ;;  64
               ;;  (logand
               ;;   18446744073709551551
               ;;   (logior 32 (logand 18446744073709551583 ptr-table-entry))))
               (set-dirty-bit (set-accessed-bit ptr-table-entry))
               x86)))
            (mv-nth
             1
             (ia32e-la-to-pa-page-dir-ptr-table
              lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86))))
  :do-not '(preprocess)
  :in-theory (e/d ()
                  (mv-nth-1-no-error-ia32e-la-to-pa-page-directory-4K-pages
                   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages
                   not
                   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
                   unsigned-byte-p
                   signed-byte-p)))

;; 2M pages:

(defrule reading-entry-with-accessed-bit-set-ia32e-la-to-pa-page-dir-ptr-table-2M-pages
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
                (equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)
                ;; For ia32e-la-to-pa-page-directory:
                (equal page-directory-base-addr
                       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
                (equal page-directory-entry-addr
                       (page-directory-entry-addr lin-addr page-directory-base-addr))
                (equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps page-directory-entry) 1)
                ;; (disjoint-p
                ;;  (addr-range 8 ptr-table-entry-addr)
                ;;  (addr-range 8 page-directory-entry-addr))
                (pairwise-disjoint-p
                 (translation-governing-addresses-for-page-dir-ptr-table
                  lin-addr ptr-table-base-addr x86))
                (physical-address-p ptr-table-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 ptr-table-base-addr) 0)
                (x86p x86))
           (equal
            (mv-nth
             1
             (ia32e-la-to-pa-page-dir-ptr-table
              lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl
              (wm-low-64
               ptr-table-entry-addr
               ;; (!ia32e-page-tables-slice :a 1 ptr-table-entry)
               ;; (logior 32 (logand 18446744073709551583 ptr-table-entry))
               (set-accessed-bit ptr-table-entry)
               x86)))
            (mv-nth
             1
             (ia32e-la-to-pa-page-dir-ptr-table
              lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86))))
  :do-not '(preprocess)
  :in-theory (e/d ()
                  (mv-nth-1-no-error-ia32e-la-to-pa-page-directory-2M-pages
                   not
                   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-2M-pages
                   unsigned-byte-p
                   signed-byte-p)))

(defrule reading-entry-with-dirty-bit-set-ia32e-la-to-pa-page-dir-ptr-table-2M-pages
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
                (equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)
                ;; For ia32e-la-to-pa-page-directory:
                (equal page-directory-base-addr
                       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
                (equal page-directory-entry-addr
                       (page-directory-entry-addr lin-addr page-directory-base-addr))
                (equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps page-directory-entry) 1)
                ;; (disjoint-p
                ;;  (addr-range 8 ptr-table-entry-addr)
                ;;  (addr-range 8 page-directory-entry-addr))
                (pairwise-disjoint-p
                 (translation-governing-addresses-for-page-dir-ptr-table
                  lin-addr ptr-table-base-addr x86))
                (physical-address-p ptr-table-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 ptr-table-base-addr) 0)
                (x86p x86))
           (equal
            (mv-nth
             1
             (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
              lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl
              (wm-low-64
               ptr-table-entry-addr
               ;; (!ia32e-page-tables-slice :d 1 ptr-table-entry)
               ;; (logior 64 (logand 18446744073709551551 ptr-table-entry))
               (set-dirty-bit ptr-table-entry)
               x86)))
            (mv-nth
             1
             (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
              lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86))))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-dir-ptr-table)
                  (not
                   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-2M-pages
                   mv-nth-1-no-error-ia32e-la-to-pa-page-directory-2M-pages
                   unsigned-byte-p
                   signed-byte-p)))

(defrule reading-entry-with-accessed-and-dirty-bits-set-ia32e-la-to-pa-page-dir-ptr-table-2M-pages
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
                (equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)
                ;; For ia32e-la-to-pa-page-directory:
                (equal page-directory-base-addr
                       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
                (equal page-directory-entry-addr
                       (page-directory-entry-addr lin-addr page-directory-base-addr))
                (equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps page-directory-entry) 1)
                ;; (disjoint-p
                ;;  (addr-range 8 ptr-table-entry-addr)
                ;;  (addr-range 8 page-directory-entry-addr))
                (pairwise-disjoint-p
                 (translation-governing-addresses-for-page-dir-ptr-table
                  lin-addr ptr-table-base-addr x86))
                (physical-address-p ptr-table-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 ptr-table-base-addr) 0)
                (x86p x86))
           (equal
            (mv-nth
             1
             (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
              lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl
              (wm-low-64
               ptr-table-entry-addr
               ;; (!ia32e-page-tables-slice :d 1 (!ia32e-page-tables-slice :a 1 ptr-table-entry))
               ;; (logior
               ;;  64
               ;;  (logand
               ;;   18446744073709551551
               ;;   (logior 32 (logand 18446744073709551583 ptr-table-entry))))
               (set-dirty-bit (set-accessed-bit ptr-table-entry))
               x86)))
            (mv-nth
             1
             (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
              lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86))))
  :do-not '(preprocess)
  :in-theory (e/d ()
                  (not
                   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-2M-pages
                   mv-nth-1-no-error-ia32e-la-to-pa-page-directory-2M-pages
                   unsigned-byte-p
                   signed-byte-p)))

;; 4K pages:

(defrule reading-entry-with-accessed-bit-set-ia32e-la-to-pa-page-dir-ptr-table-4K-pages
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
                (equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)

                ;; For ia32e-la-to-pa-page-directory:
                (equal page-directory-base-addr
                       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
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
                 (translation-governing-addresses-for-page-dir-ptr-table
                  lin-addr ptr-table-base-addr x86))
                (physical-address-p ptr-table-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 ptr-table-base-addr) 0)
                (x86p x86))
           (equal
            (mv-nth
             1
             (ia32e-la-to-pa-page-dir-ptr-table
              lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl
              (wm-low-64
               ptr-table-entry-addr
               ;; (!ia32e-page-tables-slice :a 1 ptr-table-entry)
               ;; (logior 32 (logand 18446744073709551583 ptr-table-entry))
               (set-accessed-bit ptr-table-entry)
               x86)))
            (mv-nth
             1
             (ia32e-la-to-pa-page-dir-ptr-table
              lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl
              x86))))
  :do-not '(preprocess)
  :in-theory (e/d ()
                  (not
                   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-2M-pages
                   mv-nth-1-no-error-ia32e-la-to-pa-page-directory-2M-pages
                   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages
                   mv-nth-1-no-error-ia32e-la-to-pa-page-directory-4K-pages
                   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
                   unsigned-byte-p
                   signed-byte-p)))

(defrule reading-entry-with-dirty-bit-set-ia32e-la-to-pa-page-dir-ptr-table-4K-pages
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
                (equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)

                ;; For ia32e-la-to-pa-page-directory:
                (equal page-directory-base-addr
                       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
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
                 (translation-governing-addresses-for-page-dir-ptr-table
                  lin-addr ptr-table-base-addr x86))
                (physical-address-p ptr-table-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 ptr-table-base-addr) 0)
                (x86p x86))
           (equal
            (mv-nth
             1
             (ia32e-la-to-pa-page-dir-ptr-table
              lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl
              (wm-low-64
               ptr-table-entry-addr
               ;; (!ia32e-page-tables-slice :d 1 ptr-table-entry)
               ;; (logior 64 (logand 18446744073709551551 ptr-table-entry))
               (set-dirty-bit ptr-table-entry)
               x86)))
            (mv-nth
             1
             (ia32e-la-to-pa-page-dir-ptr-table
              lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86))))
  :do-not '(preprocess)
  :in-theory (e/d ()
                  (not
                   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-2M-pages
                   mv-nth-1-no-error-ia32e-la-to-pa-page-directory-2M-pages
                   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages
                   mv-nth-1-no-error-ia32e-la-to-pa-page-directory-4K-pages
                   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
                   unsigned-byte-p
                   signed-byte-p)))

(defrule reading-entry-with-accessed-and-dirty-bits-set-ia32e-la-to-pa-page-dir-ptr-table-4K-pages
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
                (equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)
                ;; For ia32e-la-to-pa-page-directory:
                (equal page-directory-base-addr
                       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
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
                 (translation-governing-addresses-for-page-dir-ptr-table
                  lin-addr ptr-table-base-addr x86))
                (physical-address-p ptr-table-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 ptr-table-base-addr) 0)
                (x86p x86))
           (equal
            (mv-nth
             1
             (ia32e-la-to-pa-page-dir-ptr-table
              lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl
              (wm-low-64
               ptr-table-entry-addr
               ;; (!ia32e-page-tables-slice :d 1 (!ia32e-page-tables-slice :a 1 ptr-table-entry))
               ;; (logior
               ;;  64
               ;;  (logand
               ;;   18446744073709551551
               ;;   (logior 32 (logand 18446744073709551583 ptr-table-entry))))
               (set-dirty-bit (set-accessed-bit ptr-table-entry))
               x86)))
            (mv-nth
             1
             (ia32e-la-to-pa-page-dir-ptr-table
              lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86))))
  :do-not '(preprocess)
  :in-theory (e/d ()
                  (not
                   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-2M-pages
                   mv-nth-1-no-error-ia32e-la-to-pa-page-directory-2M-pages
                   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages
                   mv-nth-1-no-error-ia32e-la-to-pa-page-directory-4K-pages
                   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
                   unsigned-byte-p
                   signed-byte-p)))

;; ......................................................................
;; More theorems about preservation of validity of page directory
;; pointer table entries:
;; ......................................................................

;; 1G pages:

(defrule relating-validity-of-two-entries-in-two-x86-states-wrt-page-dir-ptr-table-1G-pages
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
                (equal entry-1 (rm-low-64 ptr-table-entry-addr x86))
                (equal entry-2 (rm-low-64 ptr-table-entry-addr x86-another))
                (equal (ia32e-page-tables-slice :ps entry-1) 1)
                (ia32e-la-to-pa-page-dir-ptr-table-entry-components-equal-p
                 '1G entry-1 entry-2))

           (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
            lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86-another))
  :in-theory (e/d
              (ia32e-la-to-pa-page-dir-ptr-table-entry-components-equal-p)
              ()))

(defruled page-dir-ptr-table-components-equal-rm-low-64-of-page-dir-ptr-table-entry-addr-via-page-dir-ptr-table-1G-pages
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
                (equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  ptr-table-entry) 1)
                (physical-address-p ptr-table-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 ptr-table-base-addr) 0)
                (x86p x86))
           (ia32e-la-to-pa-page-dir-ptr-table-entry-components-equal-p
            '1G
            (rm-low-64 ptr-table-entry-addr x86)
            (rm-low-64 ptr-table-entry-addr
                       (mv-nth
                        2
                        (ia32e-la-to-pa-page-dir-ptr-table
                         lin-addr ptr-table-base-addr wp smep nxe
                         r-w-x cpl x86)))))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (e/d (rm-low-64-and-page-dir-ptr-table-1G-pages
                            ia32e-la-to-pa-page-dir-ptr-table-entry-components-equal-p)
                           (not
                            member-p-cons
                            disjoint-p-cons
                            unsigned-byte-p
                            signed-byte-p)))))

(defrule re-read-entry-still-valid-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                 lin-addr ptr-table-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)
                (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                 lin-addr ptr-table-base-addr wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
                (equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  ptr-table-entry) 1)
                (physical-address-p ptr-table-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 ptr-table-base-addr) 0)
                (x86p x86))
           (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
            lin-addr ptr-table-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
            (mv-nth
             2
             (ia32e-la-to-pa-page-dir-ptr-table
              lin-addr ptr-table-base-addr wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
  :do-not '(preprocess)
  :in-theory (e/d (page-dir-ptr-table-components-equal-rm-low-64-of-page-dir-ptr-table-entry-addr-via-page-dir-ptr-table-1G-pages)
                  (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-1g-pages
                   not
                   unsigned-byte-p
                   signed-byte-p)))

;; 2M pages:

(defrule relating-validity-of-two-entries-in-two-x86-states-wrt-page-dir-ptr-table-2M-pages
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                 lin-addr
                 ptr-table-base-addr wp smep nxe r-w-x cpl x86)
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
                (equal entry-1 (rm-low-64 ptr-table-entry-addr x86))
                (equal entry-2 (rm-low-64 ptr-table-entry-addr x86-another))

                (equal (ia32e-page-tables-slice :ps entry-1) 0)

                (ia32e-la-to-pa-page-dir-ptr-table-entry-components-equal-p
                 '4K-or-2M entry-1 entry-2)

                (equal page-directory-base-addr
                       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd entry-1)
                            12))
                (equal page-directory-entry-addr
                       (page-directory-entry-addr lin-addr page-directory-base-addr))
                (equal page-directory-entry-1 (rm-low-64 page-directory-entry-addr x86))
                (equal page-directory-entry-2 (rm-low-64 page-directory-entry-addr x86-another))

                (equal (ia32e-page-tables-slice :ps page-directory-entry-1) 1)

                (ia32e-la-to-pa-page-directory-entry-components-equal-p
                 '2M page-directory-entry-1 page-directory-entry-2))

           (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
            lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86-another))
  :in-theory (e/d
              (ia32e-la-to-pa-page-dir-ptr-table-entry-components-equal-p)
              ()))

(defruled page-dir-ptr-table-components-equal-rm-low-64-of-page-dir-ptr-table-entry-addr-via-page-dir-ptr-table-2M-pages
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
                (equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)
                ;; For ia32e-la-to-pa-page-directory:
                (equal page-directory-base-addr
                       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry)
                            12))
                (equal page-directory-entry-addr
                       (page-directory-entry-addr lin-addr page-directory-base-addr))
                (equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps page-directory-entry) 1)

                ;; (disjoint-p (addr-range 8 ptr-table-entry-addr)
                ;;          (addr-range 8 page-directory-entry-addr))

                (pairwise-disjoint-p
                 (translation-governing-addresses-for-page-dir-ptr-table
                  lin-addr ptr-table-base-addr x86))
                (physical-address-p ptr-table-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 ptr-table-base-addr) 0)
                (x86p x86))
           (ia32e-la-to-pa-page-dir-ptr-table-entry-components-equal-p
            '4K-or-2M
            (rm-low-64 ptr-table-entry-addr x86)
            (rm-low-64 ptr-table-entry-addr
                       (mv-nth
                        2
                        (ia32e-la-to-pa-page-dir-ptr-table
                         lin-addr ptr-table-base-addr wp smep nxe
                         r-w-x cpl x86)))))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (e/d
                       (rm-low-64-and-page-dir-ptr-table-2M-pages
                        ia32e-la-to-pa-page-dir-ptr-table-entry-components-equal-p)
                       (mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
                        mv-nth-2-no-error-ia32e-la-to-pa-page-directory-2m-pages
                        mv-nth-1-no-error-ia32e-la-to-pa-page-directory-2m-pages
                        ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                        not
                        member-p-cons
                        disjoint-p-cons
                        unsigned-byte-p
                        signed-byte-p)))))

(defruled page-directory-components-equal-rm-low-64-of-page-directory-entry-addr-via-page-dir-ptr-table-2M-pages
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
                (equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)
                ;; For ia32e-la-to-pa-page-directory:
                (equal page-directory-base-addr
                       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry)
                            12))
                (equal page-directory-entry-addr
                       (page-directory-entry-addr lin-addr page-directory-base-addr))
                (equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps page-directory-entry) 1)

                ;; (disjoint-p (addr-range 8 ptr-table-entry-addr)
                ;;          (addr-range 8 page-directory-entry-addr))
                (pairwise-disjoint-p
                 (translation-governing-addresses-for-page-dir-ptr-table
                  lin-addr ptr-table-base-addr x86))

                (physical-address-p ptr-table-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 ptr-table-base-addr) 0)
                (x86p x86))

           (ia32e-la-to-pa-page-directory-entry-components-equal-p
            '2M
            (rm-low-64 page-directory-entry-addr x86)
            (rm-low-64
             page-directory-entry-addr
             (mv-nth
              2
              (ia32e-la-to-pa-page-dir-ptr-table
               lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)))))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (e/d
                       (page-directory-components-equal-rm-low-64-of-page-directory-entry-addr-via-page-directory-2M-pages)
                       (not
                        mv-nth-2-no-error-ia32e-la-to-pa-page-directory-2m-pages
                        mv-nth-1-no-error-ia32e-la-to-pa-page-directory-2m-pages
                        member-p-cons
                        ia32e-la-to-pa-page-directory-entry-validp
                        disjoint-p-cons
                        unsigned-byte-p
                        signed-byte-p)))))

(defrule re-read-entry-still-valid-ia32e-la-to-pa-page-dir-ptr-table-2M-pages
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                 lin-addr ptr-table-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)
                (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                 lin-addr ptr-table-base-addr wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
                (equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)
                ;; For ia32e-la-to-pa-page-directory:
                (equal page-directory-base-addr
                       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
                (equal page-directory-entry-addr
                       (page-directory-entry-addr lin-addr page-directory-base-addr))
                (equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps page-directory-entry) 1)
                ;; (disjoint-p
                ;;  (addr-range 8 ptr-table-entry-addr)
                ;;  (addr-range 8 page-directory-entry-addr))
                (pairwise-disjoint-p
                 (translation-governing-addresses-for-page-dir-ptr-table
                  lin-addr ptr-table-base-addr x86))
                (physical-address-p ptr-table-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 ptr-table-base-addr) 0)
                (x86p x86))

           (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
            lin-addr ptr-table-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
            (mv-nth
             2
             (ia32e-la-to-pa-page-dir-ptr-table
              lin-addr ptr-table-base-addr wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
  :do-not '(preprocess)
  :in-theory (e/d
              (page-directory-components-equal-rm-low-64-of-page-directory-entry-addr-via-page-dir-ptr-table-2M-pages
               page-dir-ptr-table-components-equal-rm-low-64-of-page-dir-ptr-table-entry-addr-via-page-dir-ptr-table-2M-pages)
              (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
               mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
               mv-nth-2-no-error-ia32e-la-to-pa-page-directory-2m-pages
               not
               unsigned-byte-p
               signed-byte-p)))

;; 4K pages:

(defrule relating-validity-of-two-entries-in-two-x86-states-wrt-page-dir-ptr-table-4K-pages
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
                (equal entry-1 (rm-low-64 ptr-table-entry-addr x86))
                (equal entry-2 (rm-low-64 ptr-table-entry-addr x86-another))
                (equal (ia32e-page-tables-slice :ps entry-1) 0)
                (ia32e-la-to-pa-page-dir-ptr-table-entry-components-equal-p
                 '4K-or-2M entry-1 entry-2)

                (equal page-directory-base-addr
                       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd entry-1)
                            12))
                (equal page-directory-entry-addr
                       (page-directory-entry-addr lin-addr page-directory-base-addr))
                (equal page-directory-entry-1 (rm-low-64 page-directory-entry-addr x86))
                (equal page-directory-entry-2 (rm-low-64 page-directory-entry-addr x86-another))

                (equal (ia32e-page-tables-slice :ps page-directory-entry-1) 0)

                (ia32e-la-to-pa-page-directory-entry-components-equal-p
                 '4K page-directory-entry-1 page-directory-entry-2)

                (equal page-table-base-addr-1
                       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry-1) 12))
                (equal page-table-entry-addr
                       (page-table-entry-addr lin-addr page-table-base-addr-1))

                (equal table-entry-1 (rm-low-64 page-table-entry-addr x86))
                (equal table-entry-2 (rm-low-64 page-table-entry-addr x86-another))

                (ia32e-la-to-pa-page-table-entry-components-equal-p
                 table-entry-1 table-entry-2))

           (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
            lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86-another))
  :in-theory (e/d
              (ia32e-la-to-pa-page-dir-ptr-table-entry-components-equal-p)
              ()))

(defruled page-dir-ptr-table-components-equal-rm-low-64-of-page-dir-ptr-table-entry-addr-via-page-dir-ptr-table-4K-pages
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
                (equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
                (equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)

                ;; For ia32e-la-to-pa-page-directory:
                (equal page-directory-base-addr
                       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
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
                 (translation-governing-addresses-for-page-dir-ptr-table
                  lin-addr ptr-table-base-addr x86))

                (physical-address-p ptr-table-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 ptr-table-base-addr) 0)
                (x86p x86))
           (ia32e-la-to-pa-page-dir-ptr-table-entry-components-equal-p
            '4K-or-2M
            (rm-low-64 ptr-table-entry-addr x86)
            (rm-low-64 ptr-table-entry-addr
                       (mv-nth
                        2
                        (ia32e-la-to-pa-page-dir-ptr-table
                         lin-addr ptr-table-base-addr wp smep nxe
                         r-w-x cpl x86)))))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (e/d
                       (rm-low-64-and-page-dir-ptr-table-4K-pages
                        ia32e-la-to-pa-page-dir-ptr-table-entry-components-equal-p)
                       (mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
                        mv-nth-1-no-error-ia32e-la-to-pa-page-directory-4K-pages
                        mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages
                        ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                        not
                        member-p-cons
                        disjoint-p-cons
                        unsigned-byte-p
                        signed-byte-p)))))

(defruled page-directory-components-equal-rm-low-64-of-page-directory-entry-addr-via-page-dir-ptr-table-4K-pages
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
                (equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
                (equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)

                ;; For ia32e-la-to-pa-page-directory:
                (equal page-directory-base-addr
                       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
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
                 (translation-governing-addresses-for-page-dir-ptr-table
                  lin-addr ptr-table-base-addr x86))

                (physical-address-p ptr-table-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 ptr-table-base-addr) 0)
                (x86p x86))
           (ia32e-la-to-pa-page-directory-entry-components-equal-p
            '4K
            (rm-low-64 page-directory-entry-addr x86)
            (rm-low-64 page-directory-entry-addr
                       (mv-nth
                        2
                        (ia32e-la-to-pa-page-dir-ptr-table
                         lin-addr ptr-table-base-addr wp smep nxe
                         r-w-x cpl x86)))))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (e/d
                       (page-directory-components-equal-rm-low-64-of-page-directory-entry-addr-via-page-directory-4K-pages)
                       (not
                        mv-nth-1-no-error-ia32e-la-to-pa-page-directory-4K-pages
                        mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages
                        member-p-cons
                        ia32e-la-to-pa-page-directory-entry-validp
                        disjoint-p-cons
                        unsigned-byte-p
                        signed-byte-p)))))

(defruled page-table-components-equal-rm-low-64-of-page-table-entry-addr-via-page-dir-ptr-table-4K-pages
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
                (equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)

                ;; For ia32e-la-to-pa-page-directory:
                (equal page-directory-base-addr
                       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
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
                 (translation-governing-addresses-for-page-dir-ptr-table
                  lin-addr ptr-table-base-addr x86))
                (physical-address-p ptr-table-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 ptr-table-base-addr) 0)
                (x86p x86))

           (ia32e-la-to-pa-page-table-entry-components-equal-p
            (rm-low-64 page-table-entry-addr x86)
            (rm-low-64
             page-table-entry-addr
             (mv-nth
              2
              (ia32e-la-to-pa-page-dir-ptr-table
               lin-addr ptr-table-base-addr wp smep nxe
               r-w-x cpl x86)))))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (e/d
                       (page-table-components-equal-rm-low-64-of-page-table-entry-addr-via-page-directory-4K-pages)
                       (mv-nth-1-no-error-ia32e-la-to-pa-page-directory-4K-pages
                        mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4k-pages
                        not
                        member-p-cons
                        disjoint-p-cons
                        unsigned-byte-p
                        signed-byte-p)))))

(defrule re-read-entry-still-valid-ia32e-la-to-pa-page-dir-ptr-table-4K-pages
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                 lin-addr ptr-table-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)
                (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                 lin-addr ptr-table-base-addr wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
                (equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)

                ;; For ia32e-la-to-pa-page-directory:
                (equal page-directory-base-addr
                       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
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
                 (translation-governing-addresses-for-page-dir-ptr-table
                  lin-addr ptr-table-base-addr x86))

                (physical-address-p ptr-table-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 ptr-table-base-addr) 0)
                (x86p x86))

           (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
            lin-addr ptr-table-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
            (mv-nth
             2
             (ia32e-la-to-pa-page-dir-ptr-table
              lin-addr ptr-table-base-addr wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
  :do-not '(preprocess)
  :in-theory (e/d
              (page-dir-ptr-table-components-equal-rm-low-64-of-page-dir-ptr-table-entry-addr-via-page-dir-ptr-table-4K-pages
               page-directory-components-equal-rm-low-64-of-page-directory-entry-addr-via-page-dir-ptr-table-4K-pages
               page-table-components-equal-rm-low-64-of-page-table-entry-addr-via-page-dir-ptr-table-4K-pages)
              (mv-nth-1-no-error-ia32e-la-to-pa-page-directory-4K-pages
               mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages
               ia32e-la-to-pa-page-dir-ptr-table-entry-validp
               mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
               not
               unsigned-byte-p
               signed-byte-p)))

;; ......................................................................
;; Two page directory pointer table walks theorem --- same addresses:
;; ......................................................................

;; 1G pages:

(local
 (defrule two-page-table-walks-ia32e-la-to-pa-dir-ptr-table-1G-pages-same-entry
   ;; Two walks of a page dir ptr table entry, with same or different
   ;; "input" linear addresses.

   (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                  lin-addr-1 ptr-table-base-addr-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)
                 (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                  lin-addr-2 ptr-table-base-addr-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)
                 (equal ptr-table-entry-addr-1
                        (page-dir-ptr-table-entry-addr lin-addr-1 ptr-table-base-addr-1))
                 (equal ptr-table-entry-addr-2
                        (page-dir-ptr-table-entry-addr lin-addr-2 ptr-table-base-addr-2))
                 (equal ptr-table-entry-1 (rm-low-64 ptr-table-entry-addr-1 x86))
                 (equal (ia32e-page-tables-slice :ps  ptr-table-entry-1) 1)

                 ;; Same page directory pointer table entry
                 (equal ptr-table-entry-addr-2 ptr-table-entry-addr-1)

                 (physical-address-p ptr-table-base-addr-1)
                 (physical-address-p ptr-table-base-addr-2)
                 (canonical-address-p lin-addr-1)
                 (canonical-address-p lin-addr-2)
                 (equal (loghead 12 ptr-table-base-addr-1) 0)
                 (equal (loghead 12 ptr-table-base-addr-2) 0)
                 (x86p x86))
            (equal
             (mv-nth
              1
              (ia32e-la-to-pa-page-dir-ptr-table
               lin-addr-1 ptr-table-base-addr-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
               (mv-nth
                2
                (ia32e-la-to-pa-page-dir-ptr-table
                 lin-addr-2 ptr-table-base-addr-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
             (mv-nth
              1
              (ia32e-la-to-pa-page-dir-ptr-table
               lin-addr-1 ptr-table-base-addr-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86))))
   :do-not '(preprocess)
   :in-theory (e/d
               ()
               (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
                mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-4K-or-2M-pages
                mv-nth-2-no-error-ia32e-la-to-pa-page-directory-2M-pages
                mv-nth-1-no-error-ia32e-la-to-pa-page-directory-2M-pages
                mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages
                mv-nth-1-no-error-ia32e-la-to-pa-page-directory-4K-pages
                member-p-cons
                disjoint-p-cons
                not
                unsigned-byte-p
                signed-byte-p))))

(i-am-here)

;; 2M pages:

(defruled page-dir-ptr-table-components-equal-rm-low-64-of-page-dir-ptr-table-entry-addr-via-page-directory-2M-pages
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
                (equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)
                ;; For ia32e-la-to-pa-page-directory:
                (equal page-directory-base-addr
                       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry)
                            12))
                (equal page-directory-entry-addr
                       (page-directory-entry-addr lin-addr page-directory-base-addr))
                (equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps page-directory-entry) 1)

                ;; (disjoint-p (addr-range 8 ptr-table-entry-addr)
                ;;          (addr-range 8 page-directory-entry-addr))
                (pairwise-disjoint-p
                 (translation-governing-addresses-for-page-dir-ptr-table
                  lin-addr ptr-table-base-addr x86))

                (physical-address-p ptr-table-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 ptr-table-base-addr) 0)
                (x86p x86))
           (ia32e-la-to-pa-page-dir-ptr-table-entry-components-equal-p
            '4K-or-2M
            (rm-low-64 ptr-table-entry-addr x86)
            (rm-low-64 ptr-table-entry-addr
                       (mv-nth
                        2
                        (ia32e-la-to-pa-page-directory
                         lin-addr page-directory-base-addr
                         wp smep nxe r-w-x cpl x86)))))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (e/d
                       (ia32e-la-to-pa-page-dir-ptr-table-entry-components-equal-p)
                       (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                        mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
                        mv-nth-2-no-error-ia32e-la-to-pa-page-directory-2m-pages
                        mv-nth-1-no-error-ia32e-la-to-pa-page-directory-2m-pages
                        ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                        not
                        member-p-cons
                        disjoint-p-cons
                        unsigned-byte-p
                        signed-byte-p)))))

(defrule re-read-entry-still-page-dir-ptr-table-valid-page-directory-2M-pages
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                 lin-addr ptr-table-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)
                (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                 lin-addr ptr-table-base-addr wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
                (equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)
                ;; For ia32e-la-to-pa-page-directory:
                (equal page-directory-base-addr
                       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
                (equal page-directory-entry-addr
                       (page-directory-entry-addr lin-addr page-directory-base-addr))
                (equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps page-directory-entry) 1)
                ;; (disjoint-p
                ;;  (addr-range 8 ptr-table-entry-addr)
                ;;  (addr-range 8 page-directory-entry-addr))
                (pairwise-disjoint-p
                 (translation-governing-addresses-for-page-dir-ptr-table
                  lin-addr ptr-table-base-addr x86))
                (physical-address-p ptr-table-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 ptr-table-base-addr) 0)
                (x86p x86))

           (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
            lin-addr ptr-table-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
            (mv-nth
             2
             (ia32e-la-to-pa-page-directory
              lin-addr page-directory-base-addr
              wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
  :do-not '(preprocess)
  :in-theory (e/d
              (page-dir-ptr-table-components-equal-rm-low-64-of-page-dir-ptr-table-entry-addr-via-page-directory-2M-pages
               page-directory-components-equal-rm-low-64-of-page-directory-entry-addr-via-page-directory-2M-pages)
              (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
               mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
               mv-nth-2-no-error-ia32e-la-to-pa-page-directory-2m-pages
               not
               unsigned-byte-p
               signed-byte-p)))

(defruled page-dir-ptr-table-entry-equal-rm-low-64-of-page-dir-ptr-table-entry-addr-via-page-directory-2M-pages
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                 lin-addr-1 ptr-table-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)
                (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                 lin-addr-2 ptr-table-base-addr wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)
                (equal ptr-table-entry-addr-1
                       (page-dir-ptr-table-entry-addr lin-addr-1 ptr-table-base-addr))
                (equal ptr-table-entry-1 (rm-low-64 ptr-table-entry-addr-1 x86))
                (equal (ia32e-page-tables-slice :ps  ptr-table-entry-1) 0)

                ;; For ia32e-la-to-pa-page-directory:
                (equal page-directory-base-addr
                       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry-1) 12))
                (equal page-directory-entry-addr
                       (page-directory-entry-addr lin-addr-1 page-directory-base-addr))

                (equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps page-directory-entry) 1)

                (pairwise-disjoint-p
                 (translation-governing-addresses-for-page-dir-ptr-table
                  lin-addr-1 ptr-table-base-addr x86))

                ;; So that the ptr table entries are the same...
                (equal (part-select lin-addr-1 :low 30 :high 38)
                       (part-select lin-addr-2 :low 30 :high 38))
                ;; So that the page directory entries are the same...
                (equal (part-select lin-addr-1 :low 21 :high 29)
                       (part-select lin-addr-2 :low 21 :high 29))
                ;; So that the physical address is different...
                (not (equal (part-select lin-addr-1 :low 0 :high 20)
                            (part-select lin-addr-2 :low 0 :high 20)))

                (physical-address-p ptr-table-base-addr)
                (canonical-address-p lin-addr-1)
                (canonical-address-p lin-addr-2)
                (equal (loghead 12 ptr-table-base-addr) 0)
                (x86p x86))
           (equal
            (rm-low-64
             ptr-table-entry-addr-1
             (mv-nth
              2
              (ia32e-la-to-pa-page-directory
               lin-addr-2 page-directory-base-addr wp-2 smep-2 nxe-2 r-w-x-2
               cpl-2 x86)))
            (rm-low-64 ptr-table-entry-addr-1 x86)))
  :hints (("Goal" :do-not '(preprocess)
           :use ((:instance equality-of-page-dir-ptr-table-entry-addr)
                 (:instance equality-of-page-directory-entry-addr))
           :in-theory (e/d
                       (ia32e-la-to-pa-page-dir-ptr-table-entry-components-equal-p)
                       (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                        not
                        member-p-cons
                        disjoint-p-cons
                        unsigned-byte-p
                        signed-byte-p)))))

(defrule re-read-entry-still-page-dir-ptr-table-valid-page-directory-2M-pages-same-entry-different-addrs
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                 lin-addr-1 ptr-table-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)
                (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                 lin-addr-2 ptr-table-base-addr wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)
                (equal ptr-table-entry-addr-1
                       (page-dir-ptr-table-entry-addr lin-addr-1 ptr-table-base-addr))
                (equal ptr-table-entry-1 (rm-low-64 ptr-table-entry-addr-1 x86))
                (equal (ia32e-page-tables-slice :ps  ptr-table-entry-1) 0)

                ;; For ia32e-la-to-pa-page-directory:
                (equal page-directory-base-addr
                       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry-1) 12))
                (equal page-directory-entry-addr
                       (page-directory-entry-addr lin-addr-1 page-directory-base-addr))

                (equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps page-directory-entry) 1)

                (pairwise-disjoint-p
                 (translation-governing-addresses-for-page-dir-ptr-table
                  lin-addr-1 ptr-table-base-addr x86))

                ;; So that the ptr table entries are the same...
                (equal (part-select lin-addr-1 :low 30 :high 38)
                       (part-select lin-addr-2 :low 30 :high 38))
                ;; So that the page directory entries are the same...
                (equal (part-select lin-addr-1 :low 21 :high 29)
                       (part-select lin-addr-2 :low 21 :high 29))
                ;; So that the physical address is different...
                (not (equal (part-select lin-addr-1 :low 0 :high 20)
                            (part-select lin-addr-2 :low 0 :high 20)))

                (physical-address-p ptr-table-base-addr)
                (canonical-address-p lin-addr-1)
                (canonical-address-p lin-addr-2)
                (equal (loghead 12 ptr-table-base-addr) 0)
                (x86p x86))
           (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
            lin-addr-1 ptr-table-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
            (mv-nth
             2
             (ia32e-la-to-pa-page-directory
              lin-addr-2 page-directory-base-addr wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
  :hints (("Goal" :do-not '(preprocess)
           :use ((:instance equality-of-page-dir-ptr-table-entry-addr)
                 (:instance equality-of-page-directory-entry-addr))
           :in-theory (e/d
                       (ia32e-la-to-pa-page-directory-entry-components-equal-p
                        page-dir-ptr-table-entry-equal-rm-low-64-of-page-dir-ptr-table-entry-addr-via-page-directory-2M-pages
                        page-dir-ptr-table-components-equal-rm-low-64-of-page-dir-ptr-table-entry-addr-via-page-directory-2M-pages)
                       (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                        not
                        member-p-cons
                        disjoint-p-cons
                        ia32e-la-to-pa-page-table-entry-validp
                        unsigned-byte-p
                        signed-byte-p)))))

(defruled page-size-from-re-reading-page-directory-entry-given-page-directory-entry-validp-2M-pages
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
            (ia32e-page-tables-slice
             :ps
             (rm-low-64 page-directory-entry-addr
                        (mv-nth
                         2
                         (ia32e-la-to-pa-page-directory
                          lin-addr page-directory-base-addr wp smep nxe r-w-x
                          cpl x86))))
            (ia32e-page-tables-slice :ps page-directory-entry)))
  :do-not '(preprocess)
  :in-theory (e/d* (rm-low-64-and-page-directory-2M-pages)
                   (ia32e-la-to-pa-page-directory-entry-validp
                    not
                    unsigned-byte-p
                    signed-byte-p)))

(defruled page-dir-ptr-table-components-equal-rm-low-64-of-page-dir-ptr-table-entry-addr-via-page-directory-4K-pages
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
                (equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)

                ;; For ia32e-la-to-pa-page-directory:
                (equal page-directory-base-addr
                       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
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
                 (translation-governing-addresses-for-page-dir-ptr-table
                  lin-addr ptr-table-base-addr x86))
                (physical-address-p ptr-table-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 ptr-table-base-addr) 0)
                (x86p x86))
           (ia32e-la-to-pa-page-dir-ptr-table-entry-components-equal-p
            '4K-or-2M
            (rm-low-64 ptr-table-entry-addr x86)
            (rm-low-64 ptr-table-entry-addr
                       (mv-nth
                        2
                        (ia32e-la-to-pa-page-directory
                         lin-addr page-directory-base-addr
                         wp smep nxe r-w-x cpl x86)))))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (e/d
                       (ia32e-la-to-pa-page-dir-ptr-table-entry-components-equal-p)
                       (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                        mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
                        mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages
                        mv-nth-1-no-error-ia32e-la-to-pa-page-directory-4K-pages
                        ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                        not
                        member-p-cons
                        disjoint-p-cons
                        unsigned-byte-p
                        signed-byte-p)))))

(defrule re-read-entry-still-page-dir-ptr-table-valid-page-directory-4K-pages
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                 lin-addr ptr-table-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)
                (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                 lin-addr ptr-table-base-addr wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
                (equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)

                ;; For ia32e-la-to-pa-page-directory:
                (equal page-directory-base-addr
                       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
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
                 (translation-governing-addresses-for-page-dir-ptr-table
                  lin-addr ptr-table-base-addr x86))
                (physical-address-p ptr-table-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 ptr-table-base-addr) 0)
                (x86p x86))
           (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
            lin-addr ptr-table-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
            (mv-nth
             2
             (ia32e-la-to-pa-page-directory
              lin-addr page-directory-base-addr
              wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
  :do-not '(preprocess)
  :in-theory (e/d
              (page-dir-ptr-table-components-equal-rm-low-64-of-page-dir-ptr-table-entry-addr-via-page-directory-4K-pages
               page-directory-components-equal-rm-low-64-of-page-directory-entry-addr-via-page-directory-4K-pages
               page-table-components-equal-rm-low-64-of-page-table-entry-addr-via-page-directory-4K-pages)
              (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
               mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
               mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages
               not
               unsigned-byte-p
               signed-byte-p)))

(defruled page-size-from-reading-page-dir-ptr-table-entry-from-state-after-page-directory-given-page-dir-ptr-table-entry-validp-4K-pages
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
                (equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)

                ;; For ia32e-la-to-pa-page-directory:
                (equal page-directory-base-addr
                       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
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
                 (translation-governing-addresses-for-page-dir-ptr-table
                  lin-addr ptr-table-base-addr x86))
                (physical-address-p ptr-table-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 ptr-table-base-addr) 0)
                (x86p x86))
           (equal (ia32e-page-tables-slice
                   :ps
                   (rm-low-64
                    ptr-table-entry-addr
                    (mv-nth
                     2
                     (ia32e-la-to-pa-page-directory
                      lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86))))
                  ;; (ia32e-page-tables-slice
                  ;;  :ps
                  ;;  (rm-low-64 ptr-table-entry-addr x86))
                  0
                  ))

  :do-not '(preprocess)
  :in-theory (e/d (rm-low-64-and-page-directory-4K-pages
                   rm-low-64-and-page-dir-ptr-table-4K-pages)
                  (ia32e-la-to-pa-page-directory-entry-validp
                   mv-nth-1-no-error-ia32e-la-to-pa-page-directory-4K-pages
                   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages
                   not
                   unsigned-byte-p
                   signed-byte-p)))

(defruled page-size-from-re-reading-page-directory-entry-given-page-dir-ptr-table-entry-validp-4K-pages
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
                (equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)

                ;; For ia32e-la-to-pa-page-directory:
                (equal page-directory-base-addr
                       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
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
                 (translation-governing-addresses-for-page-dir-ptr-table
                  lin-addr ptr-table-base-addr x86))
                (physical-address-p ptr-table-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 ptr-table-base-addr) 0)
                (x86p x86))
           (equal (ia32e-page-tables-slice
                   :ps
                   (rm-low-64
                    page-directory-entry-addr
                    (mv-nth
                     2
                     (ia32e-la-to-pa-page-directory
                      lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86))))
                  ;; (ia32e-page-tables-slice
                  ;;  :ps
                  ;;  (rm-low-64 page-directory-entry-addr x86))
                  0
                  ))

  :do-not '(preprocess)
  :in-theory (e/d (rm-low-64-and-page-directory-4K-pages
                   rm-low-64-and-page-dir-ptr-table-4K-pages)
                  (ia32e-la-to-pa-page-directory-entry-validp
                   mv-nth-1-no-error-ia32e-la-to-pa-page-directory-4K-pages
                   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages
                   not
                   unsigned-byte-p
                   signed-byte-p)))

(local
 (defrule two-page-table-walks-ia32e-la-to-pa-dir-ptr-table-2M-or-4K-pages-same-entry
   ;; Two talks of a page directory pointer table entry, with same or
   ;; different page directory and (if applicable) page table entries.

   (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                  lin-addr-1 ptr-table-base-addr-2 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)
                 (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                  lin-addr-2 ptr-table-base-addr-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)
                 (equal ptr-table-entry-addr-1
                        (page-dir-ptr-table-entry-addr lin-addr-1 ptr-table-base-addr-1))
                 (equal ptr-table-entry-addr-2
                        (page-dir-ptr-table-entry-addr lin-addr-2 ptr-table-base-addr-2))
                 (equal ptr-table-entry-1 (rm-low-64 ptr-table-entry-addr-1 x86))
                 (equal (ia32e-page-tables-slice :ps  ptr-table-entry-1) 0)

                 ;; Same page directory pointer table entry.
                 (equal ptr-table-entry-addr-2 ptr-table-entry-addr-1)

                 (pairwise-disjoint-p
                  (translation-governing-addresses-for-page-dir-ptr-table
                   lin-addr-1 ptr-table-base-addr-1 x86))
                 (pairwise-disjoint-p
                  (translation-governing-addresses-for-page-dir-ptr-table
                   lin-addr-2 ptr-table-base-addr-2 x86))

                 ;; Page directory and table (if applicable) entries
                 ;; may or may not be the same.

                 (equal page-directory-base-addr-1
                        (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry-1) 12))
                 (equal page-directory-base-addr-2
                        (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry-2) 12))

                 (pairwise-disjoint-p-aux
                  (addr-range 8 ptr-table-entry-addr-1)
                  (translation-governing-addresses-for-page-directory
                   lin-addr-2 page-directory-base-addr-2 x86))

                 (if
                     ;; 4K pages for entry-2
                     (equal (ia32e-page-tables-slice
                             :ps
                             (rm-low-64
                              (page-directory-entry-addr lin-addr-2 page-directory-base-addr-2)
                              x86))
                            0)

                     (pairwise-disjoint-p-aux
                      (addr-range 8 (page-directory-entry-addr lin-addr-1 page-directory-base-addr-1))
                      (translation-governing-addresses-for-page-table
                       lin-addr-2
                       ;; page-table-base-addr-2
                       (ash (ia32e-pde-pg-table-slice
                             :pde-pt
                             (rm-low-64
                              (page-directory-entry-addr
                               lin-addr-2
                               page-directory-base-addr-2)
                              x86))
                            12)
                       x86))

                   t)

                 (physical-address-p ptr-table-base-addr-1)
                 (physical-address-p ptr-table-base-addr-2)
                 (canonical-address-p lin-addr-1)
                 (canonical-address-p lin-addr-2)
                 (equal (loghead 12 ptr-table-base-addr-1) 0)
                 (equal (loghead 12 ptr-table-base-addr-2) 0)
                 (x86p x86))
            (equal
             (mv-nth
              1
              (ia32e-la-to-pa-page-dir-ptr-table
               lin-addr-1 ptr-table-base-addr-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
               (mv-nth
                2
                (ia32e-la-to-pa-page-dir-ptr-table
                 lin-addr-2 ptr-table-base-addr-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
             (mv-nth
              1
              (ia32e-la-to-pa-page-dir-ptr-table
               lin-addr-1 ptr-table-base-addr-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86))))
   :do-not '(preprocess)
   :in-theory (e/d
               (page-size-from-re-reading-page-directory-entry-given-page-directory-entry-validp-2M-pages)
               (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
                mv-nth-2-no-error-ia32e-la-to-pa-page-directory-2M-pages
                mv-nth-1-no-error-ia32e-la-to-pa-page-directory-2M-pages
                mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages
                mv-nth-1-no-error-ia32e-la-to-pa-page-directory-4K-pages
                member-p-cons
                disjoint-p-cons
                not
                unsigned-byte-p
                signed-byte-p))))


;; 4K pages:

(defruled page-dir-ptr-table-entry-equal-rm-low-64-of-page-dir-ptr-table-entry-addr-via-page-directory-4K-pages
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                 lin-addr-1 ptr-table-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)
                (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                 lin-addr-2 ptr-table-base-addr wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)
                (equal ptr-table-entry-addr-1
                       (page-dir-ptr-table-entry-addr lin-addr-1 ptr-table-base-addr))
                (equal ptr-table-entry-1 (rm-low-64 ptr-table-entry-addr-1 x86))
                (equal (ia32e-page-tables-slice :ps  ptr-table-entry-1) 0)

                ;; For ia32e-la-to-pa-page-directory:
                (equal page-directory-base-addr
                       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry-1) 12))
                (equal page-directory-entry-addr
                       (page-directory-entry-addr lin-addr-1 page-directory-base-addr))

                (equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps page-directory-entry) 0)

                ;; For ia32e-la-to-pa-page-table:
                (equal page-table-base-addr
                       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
                (equal page-table-entry-addr
                       (page-table-entry-addr lin-addr-1 page-table-base-addr))

                (pairwise-disjoint-p
                 (translation-governing-addresses-for-page-dir-ptr-table
                  lin-addr-1 ptr-table-base-addr x86))

                ;; So that the ptr table entries are the same...
                (equal (part-select lin-addr-1 :low 30 :high 38)
                       (part-select lin-addr-2 :low 30 :high 38))
                ;; So that the page directory entries are the same...
                (equal (part-select lin-addr-1 :low 21 :high 29)
                       (part-select lin-addr-2 :low 21 :high 29))
                ;; So that the page table entries are the same...
                (equal (part-select lin-addr-1 :low 12 :high 20)
                       (part-select lin-addr-2 :low 12 :high 20))
                ;; So that the physical address is different...
                (not (equal (part-select lin-addr-1 :low 0 :width 12)
                            (part-select lin-addr-2 :low 0 :width 12)))

                (physical-address-p ptr-table-base-addr)
                (canonical-address-p lin-addr-1)
                (canonical-address-p lin-addr-2)
                (equal (loghead 12 ptr-table-base-addr) 0)
                (x86p x86))
           (equal
            (rm-low-64
             ptr-table-entry-addr-1
             (mv-nth
              2
              (ia32e-la-to-pa-page-directory
               lin-addr-2 page-directory-base-addr wp-2 smep-2 nxe-2 r-w-x-2
               cpl-2 x86)))
            (rm-low-64 ptr-table-entry-addr-1 x86)))
  :hints (("Goal" :do-not '(preprocess)
           :use ((:instance equality-of-page-dir-ptr-table-entry-addr)
                 (:instance equality-of-page-directory-entry-addr)
                 (:instance equality-of-page-table-entry-addr))
           :in-theory (e/d
                       (ia32e-la-to-pa-page-dir-ptr-table-entry-components-equal-p)
                       (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                        not
                        member-p-cons
                        disjoint-p-cons
                        unsigned-byte-p
                        signed-byte-p)))))

(defrule re-read-entry-still-page-dir-ptr-table-valid-page-directory-4K-pages-same-entry-different-addrs
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                 lin-addr-1 ptr-table-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)
                (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                 lin-addr-2 ptr-table-base-addr wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)
                (equal ptr-table-entry-addr-1
                       (page-dir-ptr-table-entry-addr lin-addr-1 ptr-table-base-addr))
                (equal ptr-table-entry-1 (rm-low-64 ptr-table-entry-addr-1 x86))
                (equal (ia32e-page-tables-slice :ps  ptr-table-entry-1) 0)

                ;; For ia32e-la-to-pa-page-directory:
                (equal page-directory-base-addr
                       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry-1) 12))
                (equal page-directory-entry-addr
                       (page-directory-entry-addr lin-addr-1 page-directory-base-addr))

                (equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps page-directory-entry) 0)

                ;; For ia32e-la-to-pa-page-table:
                (equal page-table-base-addr
                       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
                (equal page-table-entry-addr
                       (page-table-entry-addr lin-addr-1 page-table-base-addr))

                (pairwise-disjoint-p
                 (translation-governing-addresses-for-page-dir-ptr-table
                  lin-addr-1 ptr-table-base-addr x86))

                ;; So that the ptr table entries are the same...
                (equal (part-select lin-addr-1 :low 30 :high 38)
                       (part-select lin-addr-2 :low 30 :high 38))
                ;; So that the page directory entries are the same...
                (equal (part-select lin-addr-1 :low 21 :high 29)
                       (part-select lin-addr-2 :low 21 :high 29))
                ;; So that the page table entries are the same...
                (equal (part-select lin-addr-1 :low 12 :high 20)
                       (part-select lin-addr-2 :low 12 :high 20))
                ;; So that the physical address is different...
                (not (equal (part-select lin-addr-1 :low 0 :width 12)
                            (part-select lin-addr-2 :low 0 :width 12)))

                (physical-address-p ptr-table-base-addr)
                (canonical-address-p lin-addr-1)
                (canonical-address-p lin-addr-2)
                (equal (loghead 12 ptr-table-base-addr) 0)
                (x86p x86))
           (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
            lin-addr-1 ptr-table-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
            (mv-nth
             2
             (ia32e-la-to-pa-page-directory
              lin-addr-2 page-directory-base-addr wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
  :hints (("Goal" :do-not '(preprocess)
           :use ((:instance equality-of-page-dir-ptr-table-entry-addr)
                 (:instance equality-of-page-directory-entry-addr)
                 (:instance equality-of-page-table-entry-addr))
           :in-theory (e/d
                       (ia32e-la-to-pa-page-directory-entry-components-equal-p
                        page-dir-ptr-table-entry-equal-rm-low-64-of-page-dir-ptr-table-entry-addr-via-page-directory-2M-pages
                        page-dir-ptr-table-components-equal-rm-low-64-of-page-dir-ptr-table-entry-addr-via-page-directory-2M-pages)
                       (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                        not
                        member-p-cons
                        disjoint-p-cons
                        ia32e-la-to-pa-page-table-entry-validp
                        unsigned-byte-p
                        signed-byte-p)))))

;; ......................................................................
;; Two page directory pointer table walks theorem --- different
;; entries:
;; ......................................................................

(local
 (defrule two-page-table-walks-ia32e-la-to-pa-page-dir-ptr-table-different-entries
   ;; Two walks of a page dir ptr table, all the dir ptr, directory,
   ;; and table entries are mutually disjoint.

   (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                  lin-addr-1 ptr-table-base-addr-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)
                 (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                  lin-addr-2 ptr-table-base-addr-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)

                 (pairwise-disjoint-p
                  (append
                   (translation-governing-addresses-for-page-dir-ptr-table
                    lin-addr-2 ptr-table-base-addr-2 x86)
                   (translation-governing-addresses-for-page-dir-ptr-table
                    lin-addr-1 ptr-table-base-addr-1 x86)))

                 (physical-address-p ptr-table-base-addr-1)
                 (canonical-address-p lin-addr-1)
                 (equal (loghead 12 ptr-table-base-addr-1) 0)

                 (physical-address-p ptr-table-base-addr-2)
                 (canonical-address-p lin-addr-2)
                 (equal (loghead 12 ptr-table-base-addr-2) 0)

                 (x86p x86))
            (equal
             (mv-nth
              1
              (ia32e-la-to-pa-page-dir-ptr-table
               lin-addr-1 ptr-table-base-addr-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
               (mv-nth
                2
                (ia32e-la-to-pa-page-dir-ptr-table
                 lin-addr-2 ptr-table-base-addr-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
             (mv-nth
              1
              (ia32e-la-to-pa-page-dir-ptr-table
               lin-addr-1 ptr-table-base-addr-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
               x86))))
   :do-not '(preprocess)
   :in-theory (e/d (ia32e-la-to-pa-page-directory-entry-components-equal-p)
                   (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                    ;; mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
                    ;; mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
                    mv-nth-1-no-error-ia32e-la-to-pa-page-directory-2M-pages
                    mv-nth-1-no-error-ia32e-la-to-pa-page-directory-4K-pages
                    mv-nth-2-no-error-ia32e-la-to-pa-page-directory-2M-pages
                    mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages
                    member-p-cons
                    disjoint-p-cons
                    not
                    unsigned-byte-p
                    signed-byte-p))))

;; ......................................................................
;; More theorems about validity of page directory pointer table
;; entries being preserved when the translation-governing addresses
;; are disjoint:
;; ......................................................................

(defrule validity-preserved-same-x86-state-disjoint-addresses-wrt-page-dir-ptr-table
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                 lin-addr-1 ptr-table-base-addr-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)
                (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                 lin-addr-2 ptr-table-base-addr-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)

                (pairwise-disjoint-p
                 (append
                  (translation-governing-addresses-for-page-dir-ptr-table
                   lin-addr-2 ptr-table-base-addr-2 x86)
                  (translation-governing-addresses-for-page-dir-ptr-table
                   lin-addr-1 ptr-table-base-addr-1 x86)))

                (physical-address-p ptr-table-base-addr-1)
                (canonical-address-p lin-addr-1)
                (equal (loghead 12 ptr-table-base-addr-1) 0)

                (physical-address-p ptr-table-base-addr-2)
                (canonical-address-p lin-addr-2)
                (equal (loghead 12 ptr-table-base-addr-2) 0)

                (x86p x86))

           (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
            lin-addr-1 ptr-table-base-addr-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
            (mv-nth 2 (ia32e-la-to-pa-page-dir-ptr-table
                       lin-addr-2 ptr-table-base-addr-2
                       wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))

  :in-theory (e/d ()
                  (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-2M-pages
                   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages
                   member-p-cons
                   disjoint-p-cons
                   not
                   unsigned-byte-p
                   signed-byte-p)))

;; ......................................................................
;; Translation-Governing-Addresses-For-Page-Dir-Ptr-Table and
;; ia32e-la-to-pa-page-dir-ptr-table-entry:
;; ......................................................................

(defrule translation-governing-addresses-for-page-dir-ptr-table-and-ia32e-la-to-pa-page-dir-ptr-table-pairwise-disjoint
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                 lin-addr-2 ptr-table-base-addr-2 wp-2
                 smep-2 nxe-2 r-w-x-2 cpl-2 x86)
                (pairwise-disjoint-p
                 (append
                  (translation-governing-addresses-for-page-dir-ptr-table
                   lin-addr-2 ptr-table-base-addr-2 x86)
                  (translation-governing-addresses-for-page-dir-ptr-table
                   lin-addr-1 ptr-table-base-addr-1 x86)))
                (physical-address-p ptr-table-base-addr-2))
           (equal
            (translation-governing-addresses-for-page-dir-ptr-table
             lin-addr-1 ptr-table-base-addr-1
             (mv-nth 2
                     (ia32e-la-to-pa-page-dir-ptr-table
                      lin-addr-2 ptr-table-base-addr-2
                      wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)))
            (translation-governing-addresses-for-page-dir-ptr-table
             lin-addr-1 ptr-table-base-addr-1 x86)))
  :in-theory (e/d ()
                  (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                   addr-range-1
                   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
                   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
                   member-p-cons
                   disjoint-p-cons
                   not
                   unsigned-byte-p
                   signed-byte-p)))

;; 1G pages:

(defrule translation-governing-addresses-for-page-dir-ptr-table-and-ia32e-la-to-pa-page-dir-ptr-table-same-addr-1G-pages
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                 lin-addr ptr-table-base-addr wp
                 smep nxe r-w-x cpl x86)
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
                (equal page-dir-ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps page-dir-ptr-table-entry) 1)

                (physical-address-p ptr-table-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 ptr-table-base-addr) 0)
                (x86p x86))
           (equal
            (translation-governing-addresses-for-page-dir-ptr-table
             lin-addr ptr-table-base-addr
             (mv-nth 2
                     (ia32e-la-to-pa-page-dir-ptr-table
                      lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)))
            (translation-governing-addresses-for-page-dir-ptr-table
             lin-addr ptr-table-base-addr x86)))
  :in-theory (e/d ()
                  (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                   translation-governing-addresses-for-page-directory
                   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
                   addr-range-1
                   member-p-cons
                   disjoint-p-cons
                   not
                   unsigned-byte-p
                   signed-byte-p)))

(defrule translation-governing-addresses-for-page-dir-ptr-table-and-disjoint-wm-low-64-1G-pages
  (implies (and (bind-free '((wp . wp)
                             (smep . smep)
                             (nxe . nxe)
                             (r-w-x . r-w-x)
                             (cpl . cpl))
                           (wp smep nxe r-w-x cpl))
                (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
                (equal page-dir-ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps page-dir-ptr-table-entry) 1)

                (pairwise-disjoint-p-aux
                 (addr-range 8 addr)
                 (translation-governing-addresses-for-page-dir-ptr-table
                  lin-addr ptr-table-base-addr x86))
                (integerp addr))
           (equal
            (translation-governing-addresses-for-page-dir-ptr-table
             lin-addr ptr-table-base-addr (wm-low-64 addr val x86))
            (translation-governing-addresses-for-page-dir-ptr-table
             lin-addr ptr-table-base-addr x86)))
  :in-theory (e/d ()
                  (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                   translation-governing-addresses-for-page-directory
                   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
                   addr-range-1
                   member-p-cons
                   disjoint-p-cons
                   not
                   unsigned-byte-p
                   signed-byte-p)))

;; 2M pages:

(defrule translation-governing-addresses-for-page-dir-ptr-table-and-ia32e-la-to-pa-page-dir-ptr-table-same-addr-2M-pages
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
                (equal page-dir-ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps page-dir-ptr-table-entry) 0)
                ;; For page directory:
                (equal page-directory-base-addr
                       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd page-dir-ptr-table-entry) 12))
                (equal page-directory-entry-addr
                       (page-directory-entry-addr lin-addr page-directory-base-addr))

                (equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps page-directory-entry) 1)

                ;; (disjoint-p
                ;;  (addr-range 8 ptr-table-base-addr)
                ;;  (addr-range 8 page-directory-entry-addr))
                (pairwise-disjoint-p
                 (translation-governing-addresses-for-page-dir-ptr-table
                  lin-addr ptr-table-base-addr x86))


                (physical-address-p ptr-table-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 ptr-table-base-addr) 0)
                (x86p x86))
           (equal
            (translation-governing-addresses-for-page-dir-ptr-table
             lin-addr ptr-table-base-addr
             (mv-nth 2
                     (ia32e-la-to-pa-page-dir-ptr-table
                      lin-addr ptr-table-base-addr
                      wp smep nxe r-w-x cpl x86)))
            (translation-governing-addresses-for-page-dir-ptr-table
             lin-addr ptr-table-base-addr x86)))
  :in-theory (e/d* ()
                   (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                    mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
                    addr-range-1
                    member-p-cons
                    disjoint-p-cons
                    not
                    unsigned-byte-p
                    signed-byte-p)))

(defrule translation-governing-addresses-for-page-dir-ptr-table-and-disjoint-wm-low-64-2M-pages
  (implies (and (bind-free '((wp . wp)
                             (smep . smep)
                             (nxe . nxe)
                             (r-w-x . r-w-x)
                             (cpl . cpl))
                           (wp smep nxe r-w-x cpl))
                (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
                (equal page-dir-ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps page-dir-ptr-table-entry) 0)
                ;; For page directory:
                (equal page-directory-base-addr
                       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd page-dir-ptr-table-entry) 12))
                (equal page-directory-entry-addr
                       (page-directory-entry-addr lin-addr page-directory-base-addr))

                (equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps page-directory-entry) 1)
                (pairwise-disjoint-p
                 (translation-governing-addresses-for-page-dir-ptr-table
                  lin-addr ptr-table-base-addr x86))
                (pairwise-disjoint-p-aux
                 (addr-range 8 addr)
                 (translation-governing-addresses-for-page-dir-ptr-table
                  lin-addr ptr-table-base-addr x86))
                (integerp addr)
                (physical-address-p ptr-table-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 ptr-table-base-addr) 0)
                (x86p x86))
           (equal
            (translation-governing-addresses-for-page-dir-ptr-table
             lin-addr ptr-table-base-addr
             (wm-low-64 addr val x86))
            (translation-governing-addresses-for-page-dir-ptr-table
             lin-addr ptr-table-base-addr x86)))
  :in-theory (e/d ()
                  (translation-governing-addresses-for-page-directory
                   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
                   addr-range-1
                   member-p-cons
                   disjoint-p-cons
                   not
                   unsigned-byte-p
                   signed-byte-p)))

;; 4K pages:

(defrule translation-governing-addresses-for-page-dir-ptr-table-and-ia32e-la-to-pa-page-dir-ptr-table-same-addr-4K-pages
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
                (equal page-dir-ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps page-dir-ptr-table-entry) 0)
                ;; For ia32e-la-to-pa-page-directory:
                (equal page-directory-base-addr
                       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd page-dir-ptr-table-entry) 12))
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
                 (translation-governing-addresses-for-page-dir-ptr-table
                  lin-addr ptr-table-base-addr x86))

                (physical-address-p ptr-table-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 ptr-table-base-addr) 0)
                (x86p x86))
           (equal
            (translation-governing-addresses-for-page-dir-ptr-table
             lin-addr ptr-table-base-addr
             (mv-nth 2
                     (ia32e-la-to-pa-page-dir-ptr-table
                      lin-addr ptr-table-base-addr
                      wp smep nxe r-w-x cpl x86)))
            (translation-governing-addresses-for-page-dir-ptr-table
             lin-addr ptr-table-base-addr x86)))
  :in-theory (e/d* (
                    )
                   (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                    mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
                    addr-range-1
                    member-p-cons
                    disjoint-p-cons
                    not
                    unsigned-byte-p
                    signed-byte-p)))

(defrule translation-governing-addresses-for-page-dir-ptr-table-and-disjoint-wm-low-64-4K-pages
  (implies (and (bind-free '((wp . wp)
                             (smep . smep)
                             (nxe . nxe)
                             (r-w-x . r-w-x)
                             (cpl . cpl))
                           (wp smep nxe r-w-x cpl))
                (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
                (equal page-dir-ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps page-dir-ptr-table-entry) 0)
                ;; For ia32e-la-to-pa-page-directory:
                (equal page-directory-base-addr
                       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd page-dir-ptr-table-entry) 12))
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
                 (translation-governing-addresses-for-page-dir-ptr-table
                  lin-addr ptr-table-base-addr x86))
                (pairwise-disjoint-p-aux
                 (addr-range 8 addr)
                 (translation-governing-addresses-for-page-dir-ptr-table
                  lin-addr ptr-table-base-addr x86))

                (integerp addr)
                (physical-address-p ptr-table-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 ptr-table-base-addr) 0)
                (x86p x86))
           (equal
            (translation-governing-addresses-for-page-dir-ptr-table
             lin-addr ptr-table-base-addr
             (wm-low-64 addr val x86))
            (translation-governing-addresses-for-page-dir-ptr-table
             lin-addr ptr-table-base-addr x86)))
  :in-theory (e/d ()
                  (translation-governing-addresses-for-page-directory
                   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
                   addr-range-1
                   member-p-cons
                   disjoint-p-cons
                   not
                   unsigned-byte-p
                   signed-byte-p)))

(in-theory (e/d () (ia32e-la-to-pa-page-dir-ptr-table-entry-validp)))

;; ======================================================================
