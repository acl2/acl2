;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")
(include-book "paging-page-directory-lemmas" :ttags :all)

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))

;; ======================================================================

(defsection reasoning-about-page-tables
  :parents (proof-utilities)

  :short "Reasoning about paging data structures"

  :long "<p>For each function that walks a paging data structure, we
define recognizers for valid entries and functions to determine which
addresses govern the translation. E.g.:</p>

<ul>

<li> <b>Page table:</b> @(see ia32e-la-to-pa-page-table-entry-validp)
and @(see translation-governing-addresses-for-page-table) </li>

<li> <b>Page directory:</b> @(see
ia32e-la-to-pa-page-directory-entry-validp) and @(see
translation-governing-addresses-for-page-directory) </li>

<li> <b>Page directory pointer table:</b> @(see
ia32e-la-to-pa-page-dir-ptr-table-entry-validp) and @(see
translation-governing-addresses-for-page-dir-ptr-table) </li>

<li> <b>PML4 table:</b> @(see ia32e-la-to-pa-pml4-table-entry-validp)
and @(see translation-governing-addresses-for-pml4-table) </li>

</ul>

<p>Corresponding to the top-level walker @(see ia32e-la-to-pa), we
define a top-level valid entry recognizer and translation-governing
address function that employs all the above recognizers and functions.
See @(see ia32e-la-to-pa-validp) and @(see
translation-governing-addresses).</p>

<p>Various kinds of lemmas about @(see ia32e-la-to-pa) are briefly
described below. Note that this book @('paging-top.lisp') contains
similar lemmas for the walkers of each paging data structure.</p>

<ul>

<li> Characterization of return values, e.g.:
<ol>
<li> @(see mv-nth-0-no-error-ia32e-la-to-pa) </li>
<li> @(see mv-nth-1-no-error-ia32e-la-to-pa) </li>
<li> @(see mv-nth-2-no-error-ia32e-la-to-pa) </li>
<li> @(see mv-nth-0-no-error-ia32e-la-to-pa-with-disjoint-!memi) </li>
<li> @(see mv-nth-0-no-error-ia32e-la-to-pa-with-disjoint-wm-low-64) </li>
<li> @(see mv-nth-1-no-error-ia32e-la-to-pa-with-disjoint-!memi) </li>
<li> @(see mv-nth-1-no-error-ia32e-la-to-pa-with-disjoint-wm-low-64) </li>
</ol>
</li>

<li> Commutativity of @('!memi') and the walker function, given that
@('!memi') writes to an address disjoint from the
translation-governing address, e.g.:
<ol>
<li> @(see disjoint-!memi-mv-nth-2-no-error-ia32e-la-to-pa) </li>
</ol>
</li>

<li> Characterization of reads from physical addresses disjoint from
the translation-governing addresses, e.g.:
<ol>
<li> @(see disjoint-memi-read-mv-nth-2-no-error-ia32e-la-to-pa) </li>
<li> @(see disjoint-rm-low-32-read-mv-nth-2-no-error-ia32e-la-to-pa) </li>
<li> @(see disjoint-rm-low-64-read-mv-nth-2-no-error-ia32e-la-to-pa) </li>
</ol>
</li>

<li> Preservation of the validity of a paging entry when writes are
done to addresses disjoint from the translation-governing addresses,
e.g.:
<ol>
<li> @(see entry-with-disjoint-!memi-still-valid-ia32e-la-to-pa) </li>
<li> @(see entry-with-disjoint-wm-low-64-still-valid-ia32e-la-to-pa) </li>
</ol>
</li>

</ul>

<p> All the lemmas below are about the independence of two (same or
different) walks of the paging data structures. These lemmas aid in
the RoW/WoW proofs about linear memory in the system-level mode of the
x86 model, i.e., when paging is enabled. Note that in the description
below, by 'permissions', we mean the combination of the current
privilege level @('cpl') and the type of operation, i.e., read, write,
or execute @('r-w-x'). In many cases, we could have proved more
general theorems; for now, we just proved what we needed to make
progress with code verification.</p>
<ul>

<li> A walk of a paging data structure preserves the validity of the
paging entry for future walks, irrespective of the permissions with
which the walks are done. The first three theorems below concern the
walks for the same linear address with possibly different permissions,
while the fourth theorem concerns the walks for different linear
addresses with possibly different permissions.

<ol>
<li> @(see re-read-entry-still-valid-ia32e-la-to-pa-1G-pages) </li>
<li> @(see re-read-entry-still-valid-ia32e-la-to-pa-2M-pages) </li>
<li> @(see re-read-entry-still-valid-ia32e-la-to-pa-4K-pages) </li>
<li> @(see validity-preserved-same-x86-state-disjoint-addresses-top-level-thm) </li>
</ol>
</li>

<li> The translation of a linear address @('lin-addr') to a physical
address @('phy-addr') with permissions @('p2') does not affect a
future translation of @('lin-addr') with the same or different
permissions @('p1'), i.e., this future translation also returns
@('phy-addr').
<ol>
<li> @(see two-page-table-walks-ia32e-la-to-pa-1G-pages-same-addresses) </li>
<li> @(see two-page-table-walks-ia32e-la-to-pa-2M-pages-same-addresses) </li>
<li> @(see two-page-table-walks-ia32e-la-to-pa-4K-pages-same-addresses) </li>
</ol>
</li>

<li> The translation of a linear address @('lin-addr-2') with
permissions @('p2') does not affect a future translation of a
different linear address @('lin-addr-1') with the same or different
permissions @('p1'). There is a restriction on @('lin-addr-1') though:
@('lin-addr-1') and @('lin-addr-2') are translated to physical
addresses that fall within the same page.

<ol>
<li> @(see two-page-table-walks-ia32e-la-to-pa-1G-pages-same-entry-different-addrs) </li>
<li> @(see two-page-table-walks-ia32e-la-to-pa-2M-pages-same-entry-different-addrs) </li>
<li> @(see two-page-table-walks-ia32e-la-to-pa-4K-pages-same-entry-different-addrs) </li>
</ol>
</li>


<li> The translation of a linear address @('lin-addr-2') with
permissions @('p2') does not affect a future translation of a
different linear address @('lin-addr-1') with the same or different
permissions @('p1'). In this case, the translation-governing addresses
of both @('lin-addr-1') and @('lin-addr-2') should be
pairwise-disjoint (see @(see pairwise-disjoint-p)).
<ol>
<li> @(see two-page-table-walks-ia32e-la-to-pa-different-entries) </li>
</ol>
</li>

<li> The translation-governing addresses of a linear address
@('lin-addr-1') are unaffected by a paging structure walk done for a
completely different linear address @('lin-addr-2'). There is a
restriction on @('lin-addr-1') and @('lin-addr-2'): their respective
translation-governing addresses are pairwise-disjoint.
<ol>
<li> @(see translation-governing-addresses-and-ia32e-la-to-pa-pairwise-disjoint) </li>
</ol>
</li>

</ul>

<p>Some important theorems about the other walker functions include
those that state that the accessed and dirty bits do not affect either
the validity of a paging data structure entry or the return value from
the walker function (e.g., see @(see
page-table-entry-with-accessed-and-dirty-bits-set-still-valid-ia32e-la-to-pa-page-table)
and @(see
reading-entry-with-accessed-and-dirty-bits-set-ia32e-la-to-pa-page-table)).
</p>
"
  )

(local (xdoc::set-default-parents reasoning-about-page-tables))

;; I've got theorems (like two page walk theorem) about the following
;; three cases:

;; 1. same linear addresses, same translation-governing addresses (of
;;    course): this would correspond to the same physical addresses,
;;    of course.

;; 2. linear addresses differing only in their offsets, same
;;    translation-governing addresses (of course): this would
;;    correspond to the physical addresses being in the same page

;; 3. radically different linear addresses such that the
;;    translation-governing addresses are pairwise disjoint: physical
;;    addresses can be anything really.

;; ======================================================================

;; ia32e-la-to-pa-pml4-table:

(defmacro ia32e-la-to-pa-pml4-table-entry-components-equal-p-body
  (entry-1 entry-2)
  `(and (equal (ia32e-pml4e-slice :pml4e-p ,entry-1)
               (ia32e-pml4e-slice :pml4e-p ,entry-2))
        (equal (ia32e-pml4e-slice :pml4e-r/w ,entry-1)
               (ia32e-pml4e-slice :pml4e-r/w ,entry-2))
        (equal (ia32e-pml4e-slice :pml4e-u/s ,entry-1)
               (ia32e-pml4e-slice :pml4e-u/s ,entry-2))
        (equal (ia32e-pml4e-slice :pml4e-ps ,entry-1)
               (ia32e-pml4e-slice :pml4e-ps ,entry-2))
        (equal (ia32e-pml4e-slice :pml4e-pdpt ,entry-1)
               (ia32e-pml4e-slice :pml4e-pdpt ,entry-2))
        (equal (ia32e-pml4e-slice :pml4e-xd ,entry-1)
               (ia32e-pml4e-slice :pml4e-xd ,entry-2))
        ;; Reserved bits are zero.
        ;; (equal (loghead 11 (logtail 52 ,entry-2)) 0)
        ;; (equal (loghead 17 (logtail 13 ,entry-2)) 0)
        (equal (loghead 11 (logtail 52 ,entry-1))
               (loghead 11 (logtail 52 ,entry-2)))
        (equal (loghead  4 (logtail  8 ,entry-1))
               (loghead  4 (logtail  8 ,entry-2)))))

(define ia32e-la-to-pa-pml4-table-entry-components-equal-p
  (entry-1 entry-2)
  :verify-guards nil
  :non-executable t
  (ia32e-la-to-pa-pml4-table-entry-components-equal-p-body
   entry-1 entry-2))

(defmacro ia32e-la-to-pa-pml4-table-entry-components-equal-p-macro (x y)
  `(ia32e-la-to-pa-pml4-table-entry-components-equal-p-body
    ,x ,y))

(defthm ia32e-la-to-pa-pml4-table-entry-components-equal-p-reflexive
  (ia32e-la-to-pa-pml4-table-entry-components-equal-p b b)
  :hints (("Goal" :in-theory (e/d
                              (ia32e-la-to-pa-pml4-table-entry-components-equal-p)
                              ()))))

(defthm ia32e-la-to-pa-pml4-table-entry-components-equal-p-accessed-bit-set
  (ia32e-la-to-pa-pml4-table-entry-components-equal-p
   b (logior 32 (logand 18446744073709551583 b)))
  :hints (("Goal" :in-theory (e/d
                              (ia32e-la-to-pa-pml4-table-entry-components-equal-p)
                              ()))))

;; ......................................................................
;; Establishing inferior data structure entry validity from pml4 table
;; entry's validity:
;; ......................................................................

(defrule pml4-table-entry-validp-to-page-dir-ptr-entry-validp
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
                 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
                (equal pml4-entry-addr
                       (pml4-table-entry-addr lin-addr pml4-base-addr))
                (equal pml4-entry (rm-low-64 pml4-entry-addr x86))
                ;; For ia32e-la-to-pa-page-dir-ptr-table:
                (equal ptr-table-base-addr
                       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12)))
           (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
            lin-addr ptr-table-base-addr
            wp smep nxe r-w-x cpl x86)))

(defrule pml4-table-entry-validp-to-page-directory-entry-validp
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
                 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
                (equal pml4-entry-addr
                       (pml4-table-entry-addr lin-addr pml4-base-addr))
                (equal pml4-entry (rm-low-64 pml4-entry-addr x86))
                ;; For ia32e-la-to-pa-page-dir-ptr-table:
                (equal ptr-table-base-addr
                       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
                (equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)
                ;; For ia32e-la-to-pa-page-directory:
                (equal page-directory-base-addr
                       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12)))
           (ia32e-la-to-pa-page-directory-entry-validp
            lin-addr page-directory-base-addr
            wp smep nxe r-w-x cpl x86)))

(defrule pml4-table-entry-validp-to-page-table-entry-validp
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
                 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
                (equal pml4-entry-addr
                       (pml4-table-entry-addr lin-addr pml4-base-addr))
                (equal pml4-entry (rm-low-64 pml4-entry-addr x86))
                ;; For ia32e-la-to-pa-page-dir-ptr-table:
                (equal ptr-table-base-addr
                       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
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
                (equal page-table-pml4-base-addr
                       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
                (equal u-s-acc (ia32e-page-tables-slice :u/s
                                                        page-directory-entry)))
           (ia32e-la-to-pa-page-table-entry-validp
            lin-addr page-table-pml4-base-addr u-s-acc wp smep nxe r-w-x cpl x86)))

;; ......................................................................
;; Rules about the three return values of
;; ia32e-la-to-pa-pml4-table:
;; ......................................................................

(defrule mv-nth-0-no-error-ia32e-la-to-pa-pml4-table
  (implies (ia32e-la-to-pa-pml4-table-entry-validp
            lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
           (equal (mv-nth
                   0
                   (ia32e-la-to-pa-pml4-table
                    lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86))
                  nil))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-pml4-table)
                  (not)))

(defrule mv-nth-1-no-error-ia32e-la-to-pa-pml4-table
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
                 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
                (equal pml4-entry-addr
                       (pml4-table-entry-addr lin-addr pml4-base-addr))
                (equal entry (rm-low-64 pml4-entry-addr x86)))
           (equal (mv-nth
                   1
                   (ia32e-la-to-pa-pml4-table
                    lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86))
                  (mv-nth
                   1
                   (ia32e-la-to-pa-page-dir-ptr-table
                    lin-addr
                    (ash (ia32e-pml4e-slice :pml4e-pdpt entry) 12)
                    wp smep nxe r-w-x cpl x86))))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-pml4-table)
                  (not
                   mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
                   mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-4K-or-2M-pages
                   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-1g-pages
                   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages)))

(defrule mv-nth-2-no-error-ia32e-la-to-pa-pml4-table
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
                 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
                (equal pml4-entry-addr
                       (pml4-table-entry-addr lin-addr pml4-base-addr))
                (equal entry (rm-low-64 pml4-entry-addr x86))
                (equal accessed (ia32e-page-tables-slice :a entry))
                (equal accessed-entry
                       (if (equal accessed 0)
                           (!ia32e-page-tables-slice :a 1 entry)
                         entry)))
           (equal (mv-nth
                   2
                   (ia32e-la-to-pa-pml4-table
                    lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86))
                  (let* ((ptpr-x86
                          (mv-nth
                           2
                           (ia32e-la-to-pa-page-dir-ptr-table
                            lin-addr
                            (ash (ia32e-pml4e-slice :pml4e-pdpt entry) 12)
                            wp smep nxe r-w-x cpl x86)))
                         (accessed-x86
                          (if (equal accessed 0)
                              (wm-low-64 pml4-entry-addr accessed-entry ptpr-x86)
                            ptpr-x86)))
                    accessed-x86)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-pml4-table)
                  (not
                   mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
                   mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-4K-or-2M-pages
                   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
                   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4K-or-2M-pages)))


;; 1G pages:

(defrule mv-nth-0-no-error-ia32e-la-to-pa-pml4-table-1G-pages-with-disjoint-!memi
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
                 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
                (equal pml4-entry-addr
                       (pml4-table-entry-addr lin-addr pml4-base-addr))
                (equal pml4-entry (rm-low-64 pml4-entry-addr x86))
                ;; For ia32e-la-to-pa-page-dir-ptr-table:
                (equal ptr-table-base-addr
                       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
                (equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  ptr-table-entry) 1)

                (pairwise-disjoint-p-aux
                 (addr-range 1 addr)
                 (translation-governing-addresses-for-pml4-table
                  lin-addr pml4-base-addr x86))
                (integerp addr))
           (equal (mv-nth
                   0
                   (ia32e-la-to-pa-pml4-table
                    lin-addr pml4-base-addr wp smep nxe r-w-x cpl
                    (xw :mem addr val x86)))
                  nil))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-pml4-table)
                  (not
                   addr-range-1
                   unsigned-byte-p
                   signed-byte-p)))

(defrule mv-nth-0-no-error-ia32e-la-to-pa-pml4-table-1G-pages-with-disjoint-wm-low-64
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
                 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
                (equal pml4-entry-addr
                       (pml4-table-entry-addr lin-addr pml4-base-addr))
                (equal pml4-entry (rm-low-64 pml4-entry-addr x86))
                ;; For ia32e-la-to-pa-page-dir-ptr-table:
                (equal ptr-table-base-addr
                       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
                (equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  ptr-table-entry) 1)

                (pairwise-disjoint-p-aux
                 (addr-range 8 addr)
                 (translation-governing-addresses-for-pml4-table
                  lin-addr pml4-base-addr x86))
                (integerp addr))
           (equal (mv-nth
                   0
                   (ia32e-la-to-pa-pml4-table
                    lin-addr pml4-base-addr wp smep nxe r-w-x cpl
                    (wm-low-64 addr val x86)))
                  nil))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-pml4-table)
                  (not
                   unsigned-byte-p
                   signed-byte-p)))

(defrule mv-nth-1-no-error-ia32e-la-to-pa-pml4-table-1G-pages-with-disjoint-!memi
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
                 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
                (equal pml4-entry-addr
                       (pml4-table-entry-addr lin-addr pml4-base-addr))
                (equal pml4-entry (rm-low-64 pml4-entry-addr x86))
                ;; For ia32e-la-to-pa-page-dir-ptr-table:
                (equal ptr-table-base-addr
                       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
                (equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  ptr-table-entry) 1)

                (pairwise-disjoint-p-aux
                 (addr-range 1 addr)
                 (translation-governing-addresses-for-pml4-table
                  lin-addr pml4-base-addr x86)))
           (equal (mv-nth
                   1
                   (ia32e-la-to-pa-pml4-table
                    lin-addr pml4-base-addr wp smep nxe r-w-x cpl
                    (xw :mem addr val x86)))
                  (mv-nth
                   1
                   (ia32e-la-to-pa-pml4-table
                    lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86))))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-pml4-table)
                  (not
                   addr-range-1
                   unsigned-byte-p
                   signed-byte-p)))

(defrule mv-nth-1-no-error-ia32e-la-to-pa-pml4-table-1G-pages-with-disjoint-wm-low-64
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
                 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
                (equal pml4-entry-addr
                       (pml4-table-entry-addr lin-addr pml4-base-addr))
                (equal pml4-entry (rm-low-64 pml4-entry-addr x86))
                ;; For ia32e-la-to-pa-page-dir-ptr-table:
                (equal ptr-table-base-addr
                       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
                (equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  ptr-table-entry) 1)

                (pairwise-disjoint-p-aux
                 (addr-range 8 addr)
                 (translation-governing-addresses-for-pml4-table
                  lin-addr pml4-base-addr x86))
                (integerp addr))
           (equal (mv-nth
                   1
                   (ia32e-la-to-pa-pml4-table
                    lin-addr pml4-base-addr wp smep nxe r-w-x cpl
                    (wm-low-64 addr val x86)))
                  (mv-nth
                   1
                   (ia32e-la-to-pa-pml4-table
                    lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86))))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-pml4-table)
                  (not
                   unsigned-byte-p
                   signed-byte-p)))

;; 2M pages:

(defrule mv-nth-0-no-error-ia32e-la-to-pa-pml4-table-2M-pages-with-disjoint-!memi
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
                 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
                (equal pml4-entry-addr
                       (pml4-table-entry-addr lin-addr pml4-base-addr))
                (equal pml4-entry (rm-low-64 pml4-entry-addr x86))
                ;; For ia32e-la-to-pa-page-dir-ptr-table:
                (equal ptr-table-base-addr
                       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
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
                 (translation-governing-addresses-for-pml4-table
                  lin-addr pml4-base-addr x86))
                (integerp addr))
           (equal (mv-nth
                   0
                   (ia32e-la-to-pa-pml4-table
                    lin-addr pml4-base-addr wp smep nxe r-w-x cpl
                    (xw :mem addr val x86)))
                  nil))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-pml4-table)
                  (not
                   addr-range-1
                   unsigned-byte-p
                   signed-byte-p)))

(defrule mv-nth-0-no-error-ia32e-la-to-pa-pml4-table-2M-pages-with-disjoint-wm-low-64
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
                 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
                (equal pml4-entry-addr
                       (pml4-table-entry-addr lin-addr pml4-base-addr))
                (equal pml4-entry (rm-low-64 pml4-entry-addr x86))
                ;; For ia32e-la-to-pa-page-dir-ptr-table:
                (equal ptr-table-base-addr
                       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
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
                 (translation-governing-addresses-for-pml4-table
                  lin-addr pml4-base-addr x86))
                (integerp addr))
           (equal (mv-nth
                   0
                   (ia32e-la-to-pa-pml4-table
                    lin-addr pml4-base-addr wp smep nxe r-w-x cpl
                    (wm-low-64 addr val x86)))
                  nil))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-pml4-table)
                  (not
                   unsigned-byte-p
                   signed-byte-p)))

(defrule mv-nth-1-no-error-ia32e-la-to-pa-pml4-table-2M-pages-with-disjoint-!memi
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
                 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
                (equal pml4-entry-addr
                       (pml4-table-entry-addr lin-addr pml4-base-addr))
                (equal pml4-entry (rm-low-64 pml4-entry-addr x86))
                ;; For ia32e-la-to-pa-page-dir-ptr-table:
                (equal ptr-table-base-addr
                       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
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
                 (translation-governing-addresses-for-pml4-table
                  lin-addr pml4-base-addr x86))
                (integerp addr))
           (equal (mv-nth
                   1
                   (ia32e-la-to-pa-pml4-table
                    lin-addr pml4-base-addr wp smep nxe r-w-x cpl
                    (xw :mem addr val x86)))
                  (mv-nth
                   1
                   (ia32e-la-to-pa-pml4-table
                    lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86))))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-pml4-table)
                  (mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
                   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
                   not
                   addr-range-1
                   unsigned-byte-p
                   signed-byte-p)))

(defrule mv-nth-1-no-error-ia32e-la-to-pa-pml4-table-2M-pages-with-disjoint-wm-low-64
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
                 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
                (equal pml4-entry-addr
                       (pml4-table-entry-addr lin-addr pml4-base-addr))
                (equal pml4-entry (rm-low-64 pml4-entry-addr x86))
                ;; For ia32e-la-to-pa-page-dir-ptr-table:
                (equal ptr-table-base-addr
                       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
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
                 (translation-governing-addresses-for-pml4-table
                  lin-addr pml4-base-addr x86))
                (integerp addr))
           (equal (mv-nth
                   1
                   (ia32e-la-to-pa-pml4-table
                    lin-addr pml4-base-addr wp smep nxe r-w-x cpl
                    (wm-low-64 addr val x86)))
                  (mv-nth
                   1
                   (ia32e-la-to-pa-pml4-table
                    lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86))))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-pml4-table)
                  (not
                   mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
                   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
                   unsigned-byte-p
                   signed-byte-p)))

;; 4K pages:

(defrule mv-nth-0-no-error-ia32e-la-to-pa-pml4-table-4K-pages-with-disjoint-!memi
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
                 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
                (equal pml4-entry-addr
                       (pml4-table-entry-addr lin-addr pml4-base-addr))
                (equal pml4-entry (rm-low-64 pml4-entry-addr x86))
                ;; For ia32e-la-to-pa-page-dir-ptr-table:
                (equal ptr-table-base-addr
                       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
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
                 (translation-governing-addresses-for-pml4-table
                  lin-addr pml4-base-addr x86))
                (integerp addr))
           (equal (mv-nth
                   0
                   (ia32e-la-to-pa-pml4-table
                    lin-addr pml4-base-addr wp smep nxe r-w-x cpl
                    (xw :mem addr val x86)))
                  nil))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-pml4-table)
                  (not
                   addr-range-1
                   unsigned-byte-p
                   signed-byte-p)))

(defrule mv-nth-0-no-error-ia32e-la-to-pa-pml4-table-4K-pages-with-disjoint-wm-low-64
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
                 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
                (equal pml4-entry-addr
                       (pml4-table-entry-addr lin-addr pml4-base-addr))
                (equal pml4-entry (rm-low-64 pml4-entry-addr x86))
                ;; For ia32e-la-to-pa-page-dir-ptr-table:
                (equal ptr-table-base-addr
                       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
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
                 (translation-governing-addresses-for-pml4-table
                  lin-addr pml4-base-addr x86))
                (integerp addr))
           (equal (mv-nth
                   0
                   (ia32e-la-to-pa-pml4-table
                    lin-addr pml4-base-addr wp smep nxe r-w-x cpl
                    (wm-low-64 addr val x86)))
                  nil))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-pml4-table)
                  (not
                   unsigned-byte-p
                   signed-byte-p)))

(defrule mv-nth-1-no-error-ia32e-la-to-pa-pml4-table-4K-pages-with-disjoint-!memi
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
                 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
                (equal pml4-entry-addr
                       (pml4-table-entry-addr lin-addr pml4-base-addr))
                (equal pml4-entry (rm-low-64 pml4-entry-addr x86))
                ;; For ia32e-la-to-pa-page-dir-ptr-table:
                (equal ptr-table-base-addr
                       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
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
                 (translation-governing-addresses-for-pml4-table
                  lin-addr pml4-base-addr x86))
                (integerp addr))
           (equal (mv-nth
                   1
                   (ia32e-la-to-pa-pml4-table
                    lin-addr pml4-base-addr wp smep nxe r-w-x cpl
                    (xw :mem addr val x86)))
                  (mv-nth
                   1
                   (ia32e-la-to-pa-pml4-table
                    lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86))))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-pml4-table)
                  (not
                   mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
                   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
                   addr-range-1
                   unsigned-byte-p
                   signed-byte-p)))

(defrule mv-nth-1-no-error-ia32e-la-to-pa-pml4-table-4K-pages-with-disjoint-wm-low-64
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
                 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
                (equal pml4-entry-addr
                       (pml4-table-entry-addr lin-addr pml4-base-addr))
                (equal pml4-entry (rm-low-64 pml4-entry-addr x86))
                ;; For ia32e-la-to-pa-page-dir-ptr-table:
                (equal ptr-table-base-addr
                       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
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
                 (translation-governing-addresses-for-pml4-table
                  lin-addr pml4-base-addr x86))
                (integerp addr))
           (equal (mv-nth
                   1
                   (ia32e-la-to-pa-pml4-table
                    lin-addr pml4-base-addr wp smep nxe r-w-x cpl
                    (wm-low-64 addr val x86)))
                  (mv-nth
                   1
                   (ia32e-la-to-pa-pml4-table
                    lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86))))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-pml4-table)
                  (not
                   mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
                   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
                   unsigned-byte-p
                   signed-byte-p)))

;; ......................................................................
;; Reading pml4-table-entry-addr again using rm-low-64:
;; ......................................................................

;; 1G pages:

(defruled rm-low-64-and-ia32e-la-to-pa-pml4-table-1G-pages
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
                 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
                (equal pml4-entry-addr
                       (pml4-table-entry-addr lin-addr pml4-base-addr))
                (equal pml4-entry (rm-low-64 pml4-entry-addr x86))
                ;; For ia32e-la-to-pa-page-dir-ptr-table:
                (equal ptr-table-base-addr
                       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
                (equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  ptr-table-entry) 1)

                (pairwise-disjoint-p
                 (translation-governing-addresses-for-pml4-table
                  lin-addr pml4-base-addr x86))

                (physical-address-p pml4-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 pml4-base-addr) 0)
                (x86p x86))
           (equal
            (rm-low-64 pml4-entry-addr
                       (mv-nth
                        2
                        (ia32e-la-to-pa-pml4-table
                         lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)))
            (cond
             ((equal (ia32e-page-tables-slice :a pml4-entry) 1)
              ;; Accessed bit is set.
              (rm-low-64 pml4-entry-addr x86))

             (t ;; Accessed is clear.
              (!ia32e-page-tables-slice
               :a 1
               (rm-low-64 pml4-entry-addr x86))))))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-pml4-table)
                  (not
                   mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
                   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
                   mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
                   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
                   unsigned-byte-p
                   signed-byte-p)))

;; 2M pages:

(defruled rm-low-64-and-ia32e-la-to-pa-pml4-table-2M-pages
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
                 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
                (equal pml4-entry-addr
                       (pml4-table-entry-addr lin-addr pml4-base-addr))
                (equal pml4-entry (rm-low-64 pml4-entry-addr x86))
                ;; For ia32e-la-to-pa-page-dir-ptr-table:
                (equal ptr-table-base-addr
                       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
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

                (pairwise-disjoint-p
                 (translation-governing-addresses-for-pml4-table
                  lin-addr pml4-base-addr x86))

                (physical-address-p pml4-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 pml4-base-addr) 0)
                (x86p x86))
           (equal
            (rm-low-64 pml4-entry-addr
                       (mv-nth
                        2
                        (ia32e-la-to-pa-pml4-table
                         lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)))
            (cond
             ((equal (ia32e-page-tables-slice :a pml4-entry) 1)
              ;; Accessed bit is set.
              (rm-low-64 pml4-entry-addr x86))

             (t ;; Accessed is clear.
              (!ia32e-page-tables-slice
               :a 1
               (rm-low-64 pml4-entry-addr x86))))))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-pml4-table)
                  (not
                   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4K-or-2M-pages
                   unsigned-byte-p
                   signed-byte-p)))

;; 4K pages:

(defruled rm-low-64-and-ia32e-la-to-pa-pml4-table-4K-pages
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
                 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
                (equal pml4-entry-addr
                       (pml4-table-entry-addr lin-addr pml4-base-addr))
                (equal pml4-entry (rm-low-64 pml4-entry-addr x86))
                ;; For ia32e-la-to-pa-page-dir-ptr-table:
                (equal ptr-table-base-addr
                       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
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
                 (translation-governing-addresses-for-pml4-table
                  lin-addr pml4-base-addr x86))


                (physical-address-p pml4-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 pml4-base-addr) 0)
                (x86p x86))
           (equal
            (rm-low-64 pml4-entry-addr
                       (mv-nth
                        2
                        (ia32e-la-to-pa-pml4-table
                         lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)))
            (cond
             ((equal (ia32e-page-tables-slice :a pml4-entry) 1)
              ;; Accessed bit is set.
              (rm-low-64 pml4-entry-addr x86))

             (t ;; Accessed is clear.
              (!ia32e-page-tables-slice
               :a 1
               (rm-low-64 pml4-entry-addr x86))))))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-pml4-table)
                  (not
                   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4K-or-2M-pages
                   unsigned-byte-p
                   signed-byte-p)))

;; ......................................................................
;; !memi and state after data structure walk WoW theorem:
;; ......................................................................

;; 1G pages:

(defrule disjoint-!memi-mv-nth-2-no-error-ia32e-la-to-pa-pml4-table-1G-pages
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
                 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
                (equal pml4-entry-addr
                       (pml4-table-entry-addr lin-addr pml4-base-addr))
                (equal pml4-entry (rm-low-64 pml4-entry-addr x86))
                ;; For ia32e-la-to-pa-page-dir-ptr-table:
                (equal ptr-table-base-addr
                       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
                (equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  ptr-table-entry) 1)

                (pairwise-disjoint-p-aux
                 (addr-range 1 addr)
                 (translation-governing-addresses-for-pml4-table
                  lin-addr pml4-base-addr x86))
                (integerp addr))
           (equal
            (mv-nth
             2
             (ia32e-la-to-pa-pml4-table
              lin-addr pml4-base-addr wp smep nxe r-w-x cpl
              (xw :mem addr val x86)))
            (xw :mem addr val
                   (mv-nth
                    2
                    (ia32e-la-to-pa-pml4-table
                     lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)))))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-pml4-table
                   wm-low-64 wm-low-32)
                  (not
                   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
                   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4K-or-2M-pages)))

;; 2M pages:

(defrule disjoint-!memi-mv-nth-2-no-error-ia32e-la-to-pa-pml4-table-2M-pages
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
                 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
                (equal pml4-entry-addr
                       (pml4-table-entry-addr lin-addr pml4-base-addr))
                (equal pml4-entry (rm-low-64 pml4-entry-addr x86))
                ;; For ia32e-la-to-pa-page-dir-ptr-table:
                (equal ptr-table-base-addr
                       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
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
                 (translation-governing-addresses-for-pml4-table
                  lin-addr pml4-base-addr x86))
                (integerp addr))
           (equal
            (mv-nth
             2
             (ia32e-la-to-pa-pml4-table
              lin-addr pml4-base-addr wp smep nxe r-w-x cpl
              (xw :mem addr val x86)))
            (xw :mem addr val
                   (mv-nth
                    2
                    (ia32e-la-to-pa-pml4-table
                     lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)))))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-pml4-table
                   wm-low-64 wm-low-32)
                  (not
                   addr-range-1
                   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
                   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages)))

;; 4K pages:

(defrule disjoint-!memi-mv-nth-2-no-error-ia32e-la-to-pa-pml4-table-4K-pages
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
                 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
                (equal pml4-entry-addr
                       (pml4-table-entry-addr lin-addr pml4-base-addr))
                (equal pml4-entry (rm-low-64 pml4-entry-addr x86))
                ;; For ia32e-la-to-pa-page-dir-ptr-table:
                (equal ptr-table-base-addr
                       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
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
                 (translation-governing-addresses-for-pml4-table
                  lin-addr pml4-base-addr x86))

                (integerp addr))
           (equal
            (mv-nth
             2
             (ia32e-la-to-pa-pml4-table
              lin-addr pml4-base-addr wp smep nxe r-w-x cpl
              (xw :mem addr val x86)))
            (xw :mem
             addr val
             (mv-nth
              2
              (ia32e-la-to-pa-pml4-table
               lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)))))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-pml4-table
                   wm-low-64 wm-low-32
                   )
                  (not
                   addr-range-1
                   acl2::mv-nth-cons-meta
                   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
                   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4k-pages
                   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages)))

;; ......................................................................
;; Reading addresses disjoint from pml4-table-entry-addr after
;; walking the pml4 table:
;; ......................................................................

;; 1G pages:

(defrule disjoint-memi-read-mv-nth-2-no-error-ia32e-la-to-pa-pml4-table-1G-pages
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
                 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
                (equal pml4-entry-addr
                       (pml4-table-entry-addr lin-addr pml4-base-addr))
                (equal pml4-entry (rm-low-64 pml4-entry-addr x86))
                ;; For ia32e-la-to-pa-page-dir-ptr-table:
                (equal ptr-table-base-addr
                       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
                (equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  ptr-table-entry) 1)

                (pairwise-disjoint-p-aux
                 (addr-range 1 addr)
                 (translation-governing-addresses-for-pml4-table
                  lin-addr pml4-base-addr x86)))
           (equal
            (xr :mem addr
                  (mv-nth
                   2
                   (ia32e-la-to-pa-pml4-table
                    lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)))
            (xr :mem addr x86)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-pml4-table
                   wm-low-64 wm-low-32)
                  (not
                   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
                   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4K-or-2M-pages)))

(defrule disjoint-rm-low-64-read-mv-nth-2-no-error-ia32e-la-to-pa-pml4-table-1G-pages
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
                 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
                (equal pml4-entry-addr
                       (pml4-table-entry-addr lin-addr pml4-base-addr))
                (equal pml4-entry (rm-low-64 pml4-entry-addr x86))
                ;; For ia32e-la-to-pa-page-dir-ptr-table:
                (equal ptr-table-base-addr
                       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
                (equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  ptr-table-entry) 1)

                (pairwise-disjoint-p-aux
                 (addr-range 8 addr)
                 (translation-governing-addresses-for-pml4-table
                  lin-addr pml4-base-addr x86))
                (integerp addr))
           (equal
            (rm-low-64 addr
                       (mv-nth
                        2
                        (ia32e-la-to-pa-pml4-table
                         lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)))
            (rm-low-64 addr x86)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-pml4-table)
                  (not
                   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
                   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4K-or-2M-pages)))

(defrule disjoint-rm-low-32-read-mv-nth-2-no-error-ia32e-la-to-pa-pml4-table-1G-pages
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
                 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
                (equal pml4-entry-addr
                       (pml4-table-entry-addr lin-addr pml4-base-addr))
                (equal pml4-entry (rm-low-64 pml4-entry-addr x86))
                ;; For ia32e-la-to-pa-page-dir-ptr-table:
                (equal ptr-table-base-addr
                       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
                (equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  ptr-table-entry) 1)

                (pairwise-disjoint-p-aux
                 (addr-range 4 addr)
                 (translation-governing-addresses-for-pml4-table
                  lin-addr pml4-base-addr x86))

                (integerp addr))
           (equal
            (rm-low-32 addr
                       (mv-nth
                        2
                        (ia32e-la-to-pa-pml4-table
                         lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)))
            (rm-low-32 addr x86)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-pml4-table
                   wm-low-64)
                  (not
                   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
                   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4K-or-2M-pages)))

;; 2M pages:

(defrule disjoint-memi-read-mv-nth-2-no-error-ia32e-la-to-pa-pml4-table-2M-pages
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
                 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
                (equal pml4-entry-addr
                       (pml4-table-entry-addr lin-addr pml4-base-addr))
                (equal pml4-entry (rm-low-64 pml4-entry-addr x86))
                ;; For ia32e-la-to-pa-page-dir-ptr-table:
                (equal ptr-table-base-addr
                       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
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
                 (translation-governing-addresses-for-pml4-table
                  lin-addr pml4-base-addr x86)))
           (equal
            (xr :mem addr
                  (mv-nth
                   2
                   (ia32e-la-to-pa-pml4-table
                    lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)))
            (xr :mem addr x86)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-pml4-table)
                  (not
                   addr-range-1
                   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
                   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages)))

(defrule disjoint-rm-low-64-read-mv-nth-2-no-error-ia32e-la-to-pa-pml4-table-2M-pages
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
                 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
                (equal pml4-entry-addr
                       (pml4-table-entry-addr lin-addr pml4-base-addr))
                (equal pml4-entry (rm-low-64 pml4-entry-addr x86))
                ;; For ia32e-la-to-pa-page-dir-ptr-table:
                (equal ptr-table-base-addr
                       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
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
                 (translation-governing-addresses-for-pml4-table
                  lin-addr pml4-base-addr x86))
                (integerp addr))
           (equal
            (rm-low-64 addr
                       (mv-nth
                        2
                        (ia32e-la-to-pa-pml4-table
                         lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)))
            (rm-low-64 addr x86)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-pml4-table)
                  (not
                   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
                   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages)))

(defrule disjoint-rm-low-32-read-mv-nth-2-no-error-ia32e-la-to-pa-pml4-table-2M-pages
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
                 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
                (equal pml4-entry-addr
                       (pml4-table-entry-addr lin-addr pml4-base-addr))
                (equal pml4-entry (rm-low-64 pml4-entry-addr x86))
                ;; For ia32e-la-to-pa-page-dir-ptr-table:
                (equal ptr-table-base-addr
                       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
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
                 (addr-range 4 addr)
                 (translation-governing-addresses-for-pml4-table
                  lin-addr pml4-base-addr x86))
                (integerp addr))
           (equal
            (rm-low-32 addr
                       (mv-nth
                        2
                        (ia32e-la-to-pa-pml4-table
                         lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)))
            (rm-low-32 addr x86)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-pml4-table
                   wm-low-64)
                  (not
                   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
                   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages)))

;; 4K pages:

(defrule disjoint-memi-read-mv-nth-2-no-error-ia32e-la-to-pa-pml4-table-4K-pages
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
                 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
                (equal pml4-entry-addr
                       (pml4-table-entry-addr lin-addr pml4-base-addr))
                (equal pml4-entry (rm-low-64 pml4-entry-addr x86))
                ;; For ia32e-la-to-pa-page-dir-ptr-table:
                (equal ptr-table-base-addr
                       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
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
                 (translation-governing-addresses-for-pml4-table
                  lin-addr pml4-base-addr x86)))
           (equal
            (xr :mem
             addr
             (mv-nth
              2
              (ia32e-la-to-pa-pml4-table
               lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)))
            (xr :mem addr x86)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-pml4-table
                   wm-low-64 wm-low-32)
                  (not
                   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
                   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages)))

(defrule disjoint-rm-low-64-read-mv-nth-2-no-error-ia32e-la-to-pa-pml4-table-4K-pages
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
                 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
                (equal pml4-entry-addr
                       (pml4-table-entry-addr lin-addr pml4-base-addr))
                (equal pml4-entry (rm-low-64 pml4-entry-addr x86))
                ;; For ia32e-la-to-pa-page-dir-ptr-table:
                (equal ptr-table-base-addr
                       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
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
                 (translation-governing-addresses-for-pml4-table
                  lin-addr pml4-base-addr x86))
                (integerp addr))
           (equal
            (rm-low-64
             addr
             (mv-nth
              2
              (ia32e-la-to-pa-pml4-table
               lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)))
            (rm-low-64 addr x86)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-pml4-table)
                  (not
                   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
                   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages)))

(defrule disjoint-rm-low-32-read-mv-nth-2-no-error-ia32e-la-to-pa-pml4-table-4K-pages
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
                 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
                (equal pml4-entry-addr
                       (pml4-table-entry-addr lin-addr pml4-base-addr))
                (equal pml4-entry (rm-low-64 pml4-entry-addr x86))
                ;; For ia32e-la-to-pa-page-dir-ptr-table:
                (equal ptr-table-base-addr
                       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
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
                 (translation-governing-addresses-for-pml4-table
                  lin-addr pml4-base-addr x86))
                (integerp addr))
           (equal
            (rm-low-32 addr
                       (mv-nth
                        2
                        (ia32e-la-to-pa-pml4-table
                         lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)))
            (rm-low-32 addr x86)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-pml4-table
                   wm-low-64)
                  (not
                   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
                   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages)))

;; ......................................................................
;; Theorems that state that the validity of the pml4 table entry is
;; preserved when writes are done to disjoint addresses or :a/:d are
;; set:
;; ......................................................................

;; 1G pages:

(defrule entry-with-disjoint-!memi-still-valid-ia32e-la-to-pa-pml4-table-1G-pages
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
                 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
                (equal pml4-entry-addr
                       (pml4-table-entry-addr lin-addr pml4-base-addr))
                (equal pml4-entry (rm-low-64 pml4-entry-addr x86))
                ;; For ia32e-la-to-pa-page-dir-ptr-table:
                (equal ptr-table-base-addr
                       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
                (equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  ptr-table-entry) 1)

                (pairwise-disjoint-p-aux
                 (addr-range 1 addr)
                 (translation-governing-addresses-for-pml4-table
                  lin-addr pml4-base-addr x86))
                (integerp addr)

                (physical-address-p pml4-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 pml4-base-addr) 0)
                (x86p x86))
           (ia32e-la-to-pa-pml4-table-entry-validp
            lin-addr pml4-base-addr wp smep nxe r-w-x cpl
            (xw :mem addr val x86)))
  :in-theory (e/d (ia32e-la-to-pa-pml4-table)
                  (mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
                   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
                   not
                   addr-range-1
                   unsigned-byte-p
                   signed-byte-p)))

(defrule entry-with-disjoint-wm-low-64-still-valid-ia32e-la-to-pa-pml4-table-1G-pages
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
                 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
                (equal pml4-entry-addr
                       (pml4-table-entry-addr lin-addr pml4-base-addr))
                (equal pml4-entry (rm-low-64 pml4-entry-addr x86))
                ;; For ia32e-la-to-pa-page-dir-ptr-table:
                (equal ptr-table-base-addr
                       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
                (equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  ptr-table-entry) 1)

                (pairwise-disjoint-p-aux
                 (addr-range 8 addr)
                 (translation-governing-addresses-for-pml4-table
                  lin-addr pml4-base-addr x86))
                (integerp addr)

                (physical-address-p pml4-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 pml4-base-addr) 0)
                (x86p x86))
           (ia32e-la-to-pa-pml4-table-entry-validp
            lin-addr pml4-base-addr wp smep nxe r-w-x cpl
            (wm-low-64 addr val x86)))
  :in-theory (e/d (ia32e-la-to-pa-pml4-table)
                  (not
                   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
                   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
                   unsigned-byte-p
                   signed-byte-p)))

(defrule entry-with-accessed-bit-set-still-valid-ia32e-la-to-pa-pml4-table-1G-pages
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
                 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
                (equal pml4-entry-addr
                       (pml4-table-entry-addr lin-addr pml4-base-addr))
                (equal pml4-entry (rm-low-64 pml4-entry-addr x86))
                ;; For ia32e-la-to-pa-page-dir-ptr-table:
                (equal ptr-table-base-addr
                       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
                (equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  ptr-table-entry) 1)

                ;; (disjoint-p (addr-range 8 pml4-entry-addr)
                ;;          (addr-range 8 ptr-table-entry-addr))
                (pairwise-disjoint-p
                 (translation-governing-addresses-for-pml4-table
                  lin-addr pml4-base-addr x86))
                (physical-address-p pml4-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 pml4-base-addr) 0)
                (x86p x86))
           (ia32e-la-to-pa-pml4-table-entry-validp
            lin-addr pml4-base-addr wp smep nxe r-w-x cpl
            (wm-low-64
             pml4-entry-addr
             ;; (!ia32e-page-tables-slice :a 1 entry)
             (logior 32 (logand 18446744073709551583 pml4-entry))
             x86)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-pml4-table)
                  (not
                   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
                   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
                   unsigned-byte-p
                   signed-byte-p)))

;; 2M pages:

(defrule entry-with-disjoint-!memi-still-valid-ia32e-la-to-pa-pml4-table-2M-pages
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
                 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
                (equal pml4-entry-addr
                       (pml4-table-entry-addr lin-addr pml4-base-addr))
                (equal pml4-entry (rm-low-64 pml4-entry-addr x86))
                ;; For ia32e-la-to-pa-page-dir-ptr-table:
                (equal ptr-table-base-addr
                       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
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
                 (translation-governing-addresses-for-pml4-table
                  lin-addr pml4-base-addr x86))
                (integerp addr)
                (physical-address-p pml4-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 pml4-base-addr) 0)
                (x86p x86))
           (ia32e-la-to-pa-pml4-table-entry-validp
            lin-addr pml4-base-addr wp smep nxe r-w-x cpl
            (xw :mem addr val x86)))
  :in-theory (e/d ()
                  (mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
                   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4K-or-2M-pages
                   not
                   addr-range-1
                   unsigned-byte-p
                   signed-byte-p)))

(defrule entry-with-disjoint-wm-low-64-still-valid-ia32e-la-to-pa-pml4-table-2M-pages
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
                 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
                (equal pml4-entry-addr
                       (pml4-table-entry-addr lin-addr pml4-base-addr))
                (equal pml4-entry (rm-low-64 pml4-entry-addr x86))
                ;; For ia32e-la-to-pa-page-dir-ptr-table:
                (equal ptr-table-base-addr
                       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
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
                 (translation-governing-addresses-for-pml4-table
                  lin-addr pml4-base-addr x86))
                (integerp addr)
                (physical-address-p pml4-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 pml4-base-addr) 0)
                (x86p x86))
           (ia32e-la-to-pa-pml4-table-entry-validp
            lin-addr pml4-base-addr wp smep nxe r-w-x cpl
            (wm-low-64 addr val x86)))
  :in-theory (e/d (ia32e-la-to-pa-pml4-table
                   rm-low-64-and-ia32e-la-to-pa-pml4-table-2M-pages)
                  (mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
                   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4K-or-2M-pages
                   not
                   unsigned-byte-p
                   signed-byte-p)))

(defrule entry-with-accessed-bit-set-still-valid-ia32e-la-to-pa-pml4-table-2M-pages
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
                 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
                (equal pml4-entry-addr
                       (pml4-table-entry-addr lin-addr pml4-base-addr))
                (equal pml4-entry (rm-low-64 pml4-entry-addr x86))
                ;; For ia32e-la-to-pa-page-dir-ptr-table:
                (equal ptr-table-base-addr
                       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
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

                (pairwise-disjoint-p
                 (translation-governing-addresses-for-pml4-table
                  lin-addr pml4-base-addr x86))

                (physical-address-p pml4-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 pml4-base-addr) 0)
                (x86p x86))
           (ia32e-la-to-pa-pml4-table-entry-validp
            lin-addr pml4-base-addr wp smep nxe r-w-x cpl
            (wm-low-64
             pml4-entry-addr
             ;; (!ia32e-page-tables-slice :a 1 entry)
             (logior 32 (logand 18446744073709551583 pml4-entry))
             x86)))
  :do-not '(preprocess)
  :in-theory (e/d ()
                  (mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
                   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4K-or-2M-pages
                   not
                   unsigned-byte-p
                   signed-byte-p)))

;; 4K pages:

(defrule entry-with-disjoint-!memi-still-valid-ia32e-la-to-pa-pml4-table-4K-pages
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
                 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
                (equal pml4-entry-addr
                       (pml4-table-entry-addr lin-addr pml4-base-addr))
                (equal pml4-entry (rm-low-64 pml4-entry-addr x86))
                ;; For ia32e-la-to-pa-page-dir-ptr-table:
                (equal ptr-table-base-addr
                       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
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
                 (translation-governing-addresses-for-pml4-table
                  lin-addr pml4-base-addr x86))
                (integerp addr)
                (physical-address-p pml4-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 pml4-base-addr) 0)
                (x86p x86))
           (ia32e-la-to-pa-pml4-table-entry-validp
            lin-addr pml4-base-addr wp smep nxe r-w-x cpl
            (xw :mem addr val x86)))
  :in-theory (e/d ()
                  (mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
                   mv-nth-2-no-error-ia32e-la-to-pa-pml4-table
                   not
                   addr-range-1
                   unsigned-byte-p
                   signed-byte-p)))

(defrule entry-with-disjoint-wm-low-64-still-valid-ia32e-la-to-pa-pml4-table-4K-pages
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
                 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
                (equal pml4-entry-addr
                       (pml4-table-entry-addr lin-addr pml4-base-addr))
                (equal pml4-entry (rm-low-64 pml4-entry-addr x86))
                ;; For ia32e-la-to-pa-page-dir-ptr-table:
                (equal ptr-table-base-addr
                       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
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
                 (translation-governing-addresses-for-pml4-table
                  lin-addr pml4-base-addr x86))
                (integerp addr)
                (physical-address-p pml4-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 pml4-base-addr) 0)
                (x86p x86))
           (ia32e-la-to-pa-pml4-table-entry-validp
            lin-addr pml4-base-addr wp smep nxe r-w-x cpl
            (wm-low-64 addr val x86)))
  :in-theory (e/d ()
                  (mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
                   rm-low-64-and-ia32e-la-to-pa-pml4-table-4K-pages
                   not
                   unsigned-byte-p
                   signed-byte-p)))

(defrule entry-with-accessed-bit-set-still-valid-ia32e-la-to-pa-pml4-table-4K-pages
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
                 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
                (equal pml4-entry-addr
                       (pml4-table-entry-addr lin-addr pml4-base-addr))
                (equal pml4-entry (rm-low-64 pml4-entry-addr x86))
                ;; For ia32e-la-to-pa-page-dir-ptr-table:
                (equal ptr-table-base-addr
                       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
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
                 (translation-governing-addresses-for-pml4-table
                  lin-addr pml4-base-addr x86))

                (physical-address-p pml4-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 pml4-base-addr) 0)
                (x86p x86))
           (ia32e-la-to-pa-pml4-table-entry-validp
            lin-addr pml4-base-addr wp smep nxe r-w-x cpl
            (wm-low-64
             pml4-entry-addr
             ;; (!ia32e-page-tables-slice :a 1 entry)
             (logior 32 (logand 18446744073709551583 pml4-entry))
             x86)))
  :do-not '(preprocess)
  :in-theory (e/d ()
                  (rm-low-64-and-ia32e-la-to-pa-pml4-table-4K-pages
                   not
                   unsigned-byte-p
                   signed-byte-p)))

;; ......................................................................
;; Reading pml4 table entry from x86 states where :a/:d are set:
;; ......................................................................

;; 1G pages:

(defrule reading-entry-with-accessed-bit-set-ia32e-la-to-pa-pml4-table-1G-pages
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
                 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
                (equal pml4-entry-addr
                       (pml4-table-entry-addr lin-addr pml4-base-addr))
                (equal pml4-entry (rm-low-64 pml4-entry-addr x86))
                ;; For ia32e-la-to-pa-page-dir-ptr-table:
                (equal ptr-table-base-addr
                       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
                (equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  ptr-table-entry) 1)

                ;; (disjoint-p (addr-range 8 pml4-entry-addr)
                ;;          (addr-range 8 ptr-table-entry-addr))
                (pairwise-disjoint-p
                 (translation-governing-addresses-for-pml4-table
                  lin-addr pml4-base-addr x86))
                (physical-address-p pml4-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 pml4-base-addr) 0)
                (x86p x86))
           (equal
            (mv-nth
             1
             (ia32e-la-to-pa-pml4-table
              lin-addr pml4-base-addr wp smep nxe r-w-x cpl
              (wm-low-64
               pml4-entry-addr
               ;; (!ia32e-page-tables-slice :a 1 entry)
               (logior 32 (logand 18446744073709551583 pml4-entry))
               x86)))
            (mv-nth
             1
             (ia32e-la-to-pa-pml4-table
              lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86))))
  :do-not '(preprocess)
  :in-theory (e/d ()
                  (mv-nth-2-no-error-ia32e-la-to-pa-pml4-table
                   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
                   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
                   not
                   unsigned-byte-p
                   signed-byte-p)))

;; 2M pages:

(defrule reading-entry-with-accessed-bit-set-ia32e-la-to-pa-pml4-table-2M-pages
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
                 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
                (equal pml4-entry-addr
                       (pml4-table-entry-addr lin-addr pml4-base-addr))
                (equal pml4-entry (rm-low-64 pml4-entry-addr x86))
                ;; For ia32e-la-to-pa-page-dir-ptr-table:
                (equal ptr-table-base-addr
                       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
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

                (pairwise-disjoint-p
                 (translation-governing-addresses-for-pml4-table
                  lin-addr pml4-base-addr x86))

                (physical-address-p pml4-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 pml4-base-addr) 0)
                (x86p x86))
           (equal
            (mv-nth
             1
             (ia32e-la-to-pa-pml4-table
              lin-addr pml4-base-addr wp smep nxe r-w-x cpl
              (wm-low-64
               pml4-entry-addr
               ;; (!ia32e-page-tables-slice :a 1 entry)
               (logior 32 (logand 18446744073709551583 pml4-entry))
               x86)))
            (mv-nth
             1
             (ia32e-la-to-pa-pml4-table
              lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86))))
  :do-not '(preprocess)
  :in-theory (e/d ()
                  (not
                   ia32e-la-to-pa-pml4-table-entry-validp
                   mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
                   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4K-or-2M-pages
                   mv-nth-2-no-error-ia32e-la-to-pa-pml4-table
                   unsigned-byte-p
                   signed-byte-p)))

;; 4K pages:

(defrule reading-entry-with-accessed-bit-set-ia32e-la-to-pa-pml4-table-4K-pages
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
                 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
                (equal pml4-entry-addr
                       (pml4-table-entry-addr lin-addr pml4-base-addr))
                (equal pml4-entry (rm-low-64 pml4-entry-addr x86))
                ;; For ia32e-la-to-pa-page-dir-ptr-table:
                (equal ptr-table-base-addr
                       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
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
                 (translation-governing-addresses-for-pml4-table
                  lin-addr pml4-base-addr x86))

                (physical-address-p pml4-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 pml4-base-addr) 0)
                (x86p x86))
           (equal
            (mv-nth
             1
             (ia32e-la-to-pa-pml4-table
              lin-addr pml4-base-addr wp smep nxe r-w-x cpl
              (wm-low-64
               pml4-entry-addr
               ;; (!ia32e-page-tables-slice :a 1 entry)
               (logior 32 (logand 18446744073709551583 pml4-entry))
               x86)))
            (mv-nth
             1
             (ia32e-la-to-pa-pml4-table
              lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86))))
  :do-not '(preprocess)
  :in-theory (e/d ()
                  (not
                   ia32e-la-to-pa-pml4-table-entry-validp
                   mv-nth-2-no-error-ia32e-la-to-pa-pml4-table
                   mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-4K-or-2M-pages
                   unsigned-byte-p
                   signed-byte-p)))

;; ......................................................................
;; More theorems about preservation of validity of pml4 table entries:
;; ......................................................................

;; 1G pages:

(defrule relating-validity-of-two-entries-in-two-x86-states-wrt-pml4-table-1G-pages
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
                 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
                (equal pml4-entry-addr
                       (pml4-table-entry-addr lin-addr pml4-base-addr))
                (equal entry-1 (rm-low-64 pml4-entry-addr x86))
                (equal entry-2 (rm-low-64 pml4-entry-addr x86-another))
                (ia32e-la-to-pa-pml4-table-entry-components-equal-p
                 entry-1 entry-2)
                ;; For ia32e-la-to-pa-page-dir-ptr-table:
                (equal ptr-table-base-addr
                       (ash (ia32e-pml4e-slice :pml4e-pdpt entry-1) 12))
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
                (equal ptr-table-entry-1 (rm-low-64 ptr-table-entry-addr x86))
                (equal ptr-table-entry-2 (rm-low-64 ptr-table-entry-addr x86-another))

                (equal (ia32e-page-tables-slice :ps ptr-table-entry-1) 1)
                (ia32e-la-to-pa-page-dir-ptr-table-entry-components-equal-p
                 '1G ptr-table-entry-1 ptr-table-entry-2))

           (ia32e-la-to-pa-pml4-table-entry-validp
            lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86-another))
  :in-theory (e/d
              (ia32e-la-to-pa-pml4-table-entry-components-equal-p
               ia32e-la-to-pa-page-dir-ptr-table-entry-components-equal-p
               ia32e-la-to-pa-pml4-table-entry-validp)
              ()))

(defruled pml4-table-components-equal-rm-low-64-of-pml4-entry-addr-via-pml4-table-1G-pages

  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
                 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
                (equal pml4-entry-addr
                       (pml4-table-entry-addr lin-addr pml4-base-addr))
                (equal pml4-entry (rm-low-64 pml4-entry-addr x86))
                ;; For ia32e-la-to-pa-page-dir-ptr-table:
                (equal ptr-table-base-addr
                       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
                (equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  ptr-table-entry) 1)

                ;; (disjoint-p (addr-range 8 pml4-entry-addr)
                ;;          (addr-range 8 ptr-table-entry-addr))
                (pairwise-disjoint-p
                 (translation-governing-addresses-for-pml4-table
                  lin-addr pml4-base-addr x86))
                (physical-address-p pml4-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 pml4-base-addr) 0)
                (x86p x86))
           (ia32e-la-to-pa-pml4-table-entry-components-equal-p
            (rm-low-64 pml4-entry-addr x86)
            (rm-low-64
             pml4-entry-addr
             (mv-nth
              2
              (ia32e-la-to-pa-pml4-table
               lin-addr pml4-base-addr
               wp smep nxe r-w-x cpl x86)))))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (e/d (ia32e-la-to-pa-pml4-table-entry-components-equal-p
                            ia32e-la-to-pa-page-dir-ptr-table-entry-components-equal-p)
                           (mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
                            mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4K-or-2M-pages
                            not
                            member-p-cons
                            ia32e-la-to-pa-page-directory-entry-validp
                            disjoint-p-cons
                            unsigned-byte-p
                            signed-byte-p)))))

(defruled page-dir-ptr-table-components-equal-rm-low-64-of-ptr-table-base-addr-via-pml4-table-1G-pages
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
                 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
                (equal pml4-entry-addr
                       (pml4-table-entry-addr lin-addr pml4-base-addr))
                (equal pml4-entry (rm-low-64 pml4-entry-addr x86))
                ;; For ia32e-la-to-pa-page-dir-ptr-table:
                (equal ptr-table-base-addr
                       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
                (equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  ptr-table-entry) 1)

                ;; (disjoint-p (addr-range 8 pml4-entry-addr)
                ;;          (addr-range 8 ptr-table-entry-addr))
                (pairwise-disjoint-p
                 (translation-governing-addresses-for-pml4-table
                  lin-addr pml4-base-addr x86))
                (physical-address-p pml4-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 pml4-base-addr) 0)
                (x86p x86))
           (ia32e-la-to-pa-page-dir-ptr-table-entry-components-equal-p
            '1G
            (rm-low-64 ptr-table-entry-addr x86)
            (rm-low-64
             ptr-table-entry-addr
             (mv-nth
              2
              (ia32e-la-to-pa-pml4-table
               lin-addr pml4-base-addr
               wp smep nxe r-w-x cpl x86)))))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (e/d (page-dir-ptr-table-components-equal-rm-low-64-of-page-dir-ptr-table-entry-addr-via-page-dir-ptr-table-1G-pages)
                           (mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
                            mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4K-or-2M-pages
                            not
                            member-p-cons
                            ia32e-la-to-pa-page-directory-entry-validp
                            disjoint-p-cons
                            unsigned-byte-p
                            signed-byte-p)))))

(defrule re-read-entry-still-valid-ia32e-la-to-pa-pml4-table-1G-pages

  ;; 1. (mv-nth 2 (ia32e-la-to-pa-pml4-table ..)) --> (mv-nth 2
  ;;    (ia32e-la-to-pa-page-dir-ptr-table ...))
  ;;
  ;;    Let's ignore the accessed bit for now.

  ;; 2. relating-validity-of-two-entries-in-two-x86-states-wrt-pml4-table-1G-pages needs
  ;;    the following:
  ;;    ia32e-la-to-pa-pml4-table-entry-components-equal-p
  ;;    ia32e-la-to-pa-page-dir-ptr-table-entry-components-equal-p

  ;;    x86-another is what we get in (1), i.e., (mv-nth 2
  ;;    (ia32e-la-to-pa-page-dir-ptr-table ...)) (with the :a bit, which
  ;;    we're ignoring for now).

  ;; 3. entry-with-accessed-bit-set-still-valid-ia32e-la-to-pa-pml4-table-1g-pages
  ;;    takes care of the accessed bit case.


  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
                 lin-addr pml4-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)
                (ia32e-la-to-pa-pml4-table-entry-validp
                 lin-addr pml4-base-addr wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)
                (equal pml4-entry-addr
                       (pml4-table-entry-addr lin-addr pml4-base-addr))
                (equal pml4-entry (rm-low-64 pml4-entry-addr x86))
                ;; For ia32e-la-to-pa-page-dir-ptr-table:
                (equal ptr-table-base-addr
                       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
                (equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  ptr-table-entry) 1)

                ;; (disjoint-p (addr-range 8 pml4-entry-addr)
                ;;          (addr-range 8 ptr-table-entry-addr))
                (pairwise-disjoint-p
                 (translation-governing-addresses-for-pml4-table
                  lin-addr pml4-base-addr x86))
                (physical-address-p pml4-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 pml4-base-addr) 0)
                (x86p x86))
           (ia32e-la-to-pa-pml4-table-entry-validp
            lin-addr pml4-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
            (mv-nth
             2
             (ia32e-la-to-pa-pml4-table
              lin-addr pml4-base-addr wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
  :do-not '(preprocess)
  :in-theory (e/d
              (page-dir-ptr-table-components-equal-rm-low-64-of-page-dir-ptr-table-entry-addr-via-page-dir-ptr-table-1G-pages
               pml4-table-components-equal-rm-low-64-of-pml4-entry-addr-via-pml4-table-1G-pages)
              (ia32e-la-to-pa-pml4-table-entry-validp
               not
               mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-1g-pages
               mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-1g-pages
               acl2::mv-nth-cons-meta
               unsigned-byte-p
               signed-byte-p)))

;; 2M pages:

(defrule relating-validity-of-two-entries-in-two-x86-states-wrt-pml4-table-2M-pages
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
                 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
                (equal pml4-entry-addr
                       (pml4-table-entry-addr lin-addr pml4-base-addr))
                (equal entry-1 (rm-low-64 pml4-entry-addr x86))
                (equal entry-2 (rm-low-64 pml4-entry-addr x86-another))
                (ia32e-la-to-pa-pml4-table-entry-components-equal-p
                 entry-1 entry-2)

                ;; For ia32e-la-to-pa-page-dir-ptr-table:
                (equal ptr-table-base-addr
                       (ash (ia32e-pml4e-slice :pml4e-pdpt entry-1) 12))
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
                (equal ptr-table-entry-1 (rm-low-64 ptr-table-entry-addr x86))
                (equal ptr-table-entry-2 (rm-low-64 ptr-table-entry-addr x86-another))
                (equal (ia32e-page-tables-slice :ps ptr-table-entry-1) 0)

                (ia32e-la-to-pa-page-dir-ptr-table-entry-components-equal-p
                 '4K-or-2M ptr-table-entry-1 ptr-table-entry-2)

                ;; For ia32e-la-to-pa-page-directory:
                (equal page-directory-base-addr
                       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry-1) 12))
                (equal page-directory-entry-addr
                       (page-directory-entry-addr lin-addr page-directory-base-addr))
                (equal page-directory-entry-1 (rm-low-64 page-directory-entry-addr x86))
                (equal page-directory-entry-2 (rm-low-64 page-directory-entry-addr x86-another))

                (equal (ia32e-page-tables-slice :ps page-directory-entry-1) 1)

                (ia32e-la-to-pa-page-directory-entry-components-equal-p
                 '2M page-directory-entry-1 page-directory-entry-2))

           (ia32e-la-to-pa-pml4-table-entry-validp
            lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86-another))
  :in-theory (e/d
              (ia32e-la-to-pa-pml4-table-entry-components-equal-p
               ia32e-la-to-pa-page-dir-ptr-table-entry-components-equal-p
               ia32e-la-to-pa-page-directory-entry-components-equal-p)
              ()))

(defruled pml4-table-components-equal-rm-low-64-of-pml4-entry-addr-via-pml4-table-2M-pages
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
                 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
                (equal pml4-entry-addr
                       (pml4-table-entry-addr lin-addr pml4-base-addr))
                (equal pml4-entry (rm-low-64 pml4-entry-addr x86))
                ;; For ia32e-la-to-pa-page-dir-ptr-table:
                (equal ptr-table-base-addr
                       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
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

                (pairwise-disjoint-p
                 (translation-governing-addresses-for-pml4-table
                  lin-addr pml4-base-addr x86))

                (physical-address-p pml4-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 pml4-base-addr) 0)
                (x86p x86))
           (ia32e-la-to-pa-pml4-table-entry-components-equal-p
            (rm-low-64 pml4-entry-addr x86)
            (rm-low-64
             pml4-entry-addr
             (mv-nth
              2
              (ia32e-la-to-pa-pml4-table
               lin-addr pml4-base-addr
               wp smep nxe r-w-x cpl x86)))))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (e/d
                       (ia32e-la-to-pa-pml4-table-entry-components-equal-p
                        ia32e-la-to-pa-page-dir-ptr-table-entry-components-equal-p
                        ia32e-la-to-pa-page-directory-entry-components-equal-p)
                       (ia32e-la-to-pa-pml4-table-entry-validp
                        disjoint-rm-low-64-read-mv-nth-2-no-error-ia32e-la-to-pa-pml4-table-4k-pages
                        subset-p-two-addr-ranges
                        disjoint-p-two-addr-ranges-thm-3
                        disjoint-p-two-addr-ranges-thm-2
                        disjoint-p-two-addr-ranges-thm-1
                        <-preserved-by-adding-<-*pseudo-page-size-in-bytes*-commuted
                        <-preserved-by-adding-<-*pseudo-page-size-in-bytes*
                        not
                        mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
                        mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
                        mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
                        member-p-cons
                        disjoint-p-cons
                        unsigned-byte-p
                        signed-byte-p)))))

(defruled page-dir-ptr-table-components-equal-rm-low-64-of-ptr-table-entry-addr-via-pml4-table-2M-pages
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
                 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
                (equal pml4-entry-addr
                       (pml4-table-entry-addr lin-addr pml4-base-addr))
                (equal pml4-entry (rm-low-64 pml4-entry-addr x86))
                ;; For ia32e-la-to-pa-page-dir-ptr-table:
                (equal ptr-table-base-addr
                       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
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

                (pairwise-disjoint-p
                 (translation-governing-addresses-for-pml4-table
                  lin-addr pml4-base-addr x86))

                (physical-address-p pml4-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 pml4-base-addr) 0)
                (x86p x86))
           (ia32e-la-to-pa-page-dir-ptr-table-entry-components-equal-p
            '4K-or-2M
            (rm-low-64 ptr-table-entry-addr x86)
            (rm-low-64
             ptr-table-entry-addr
             (mv-nth
              2
              (ia32e-la-to-pa-pml4-table
               lin-addr pml4-base-addr
               wp smep nxe r-w-x cpl x86)))))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (e/d
                       (page-dir-ptr-table-components-equal-rm-low-64-of-page-dir-ptr-table-entry-addr-via-page-dir-ptr-table-2M-pages)
                       (mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
                        mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4K-or-2M-pages
                        disjoint-rm-low-64-read-mv-nth-2-no-error-ia32e-la-to-pa-pml4-table-4k-pages
                        not
                        member-p-cons
                        disjoint-p-cons
                        unsigned-byte-p
                        signed-byte-p)))))

(defruled page-directory-components-equal-rm-low-64-of-page-directory-entry-addr-via-pml4-table-2M-pages
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
                 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
                (equal pml4-entry-addr
                       (pml4-table-entry-addr lin-addr pml4-base-addr))
                (equal pml4-entry (rm-low-64 pml4-entry-addr x86))
                ;; For ia32e-la-to-pa-page-dir-ptr-table:
                (equal ptr-table-base-addr
                       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
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

                (pairwise-disjoint-p
                 (translation-governing-addresses-for-pml4-table
                  lin-addr pml4-base-addr x86))

                (physical-address-p pml4-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 pml4-base-addr) 0)
                (x86p x86))
           (ia32e-la-to-pa-page-directory-entry-components-equal-p
            '2M
            (rm-low-64 page-directory-entry-addr x86)
            (rm-low-64
             page-directory-entry-addr
             (mv-nth
              2
              (ia32e-la-to-pa-pml4-table
               lin-addr pml4-base-addr
               wp smep nxe r-w-x cpl x86)))))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (e/d
                       (page-directory-components-equal-rm-low-64-of-page-directory-entry-addr-via-page-dir-ptr-table-2M-pages)
                       (not
                        mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
                        disjoint-rm-low-64-read-mv-nth-2-no-error-ia32e-la-to-pa-pml4-table-4k-pages
                        mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4K-or-2M-pages
                        member-p-cons
                        disjoint-p-cons
                        unsigned-byte-p
                        signed-byte-p)))))

(defrule re-read-entry-still-valid-ia32e-la-to-pa-pml4-table-2M-pages

  ;;    relating-validity-of-two-entries-in-two-x86-states-wrt-pml4-table-2M-pages needs
  ;;    the following:
  ;;    ia32e-la-to-pa-pml4-table-entry-components-equal-p
  ;;    ia32e-la-to-pa-page-dir-ptr-table-entry-components-equal-p
  ;;    ia32e-la-to-pa-page-directory-entry-components-equal-p

  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
                 lin-addr pml4-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)
                (ia32e-la-to-pa-pml4-table-entry-validp
                 lin-addr pml4-base-addr wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)
                (equal pml4-entry-addr
                       (pml4-table-entry-addr lin-addr pml4-base-addr))
                (equal pml4-entry (rm-low-64 pml4-entry-addr x86))
                ;; For ia32e-la-to-pa-page-dir-ptr-table:
                (equal ptr-table-base-addr
                       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
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

                (pairwise-disjoint-p
                 (translation-governing-addresses-for-pml4-table
                  lin-addr pml4-base-addr x86))

                (physical-address-p pml4-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 pml4-base-addr) 0)
                (x86p x86))

           (ia32e-la-to-pa-pml4-table-entry-validp
            lin-addr pml4-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
            (mv-nth
             2
             (ia32e-la-to-pa-pml4-table
              lin-addr pml4-base-addr wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
  :do-not '(preprocess)
  :in-theory (e/d
              (page-directory-components-equal-rm-low-64-of-page-directory-entry-addr-via-pml4-table-2M-pages
               page-dir-ptr-table-components-equal-rm-low-64-of-ptr-table-entry-addr-via-pml4-table-2M-pages
               pml4-table-components-equal-rm-low-64-of-pml4-entry-addr-via-pml4-table-2M-pages)
              (ia32e-la-to-pa-pml4-table-entry-validp
               mv-nth-2-no-error-ia32e-la-to-pa-pml4-table
               not
               mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-4K-or-2M-pages
               mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
               acl2::mv-nth-cons-meta
               unsigned-byte-p
               signed-byte-p)))

;; 4K pages:

(defrule relating-validity-of-two-entries-in-two-x86-states-wrt-pml4-table-4K-pages
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
                 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
                (equal pml4-entry-addr
                       (pml4-table-entry-addr lin-addr pml4-base-addr))
                (equal entry-1 (rm-low-64 pml4-entry-addr x86))
                (equal entry-2 (rm-low-64 pml4-entry-addr x86-another))
                (ia32e-la-to-pa-pml4-table-entry-components-equal-p
                 entry-1 entry-2)

                ;; For ia32e-la-to-pa-page-dir-ptr-table:
                (equal ptr-table-base-addr
                       (ash (ia32e-pml4e-slice :pml4e-pdpt entry-1) 12))
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
                (equal ptr-table-entry-1 (rm-low-64 ptr-table-entry-addr x86))
                (equal ptr-table-entry-2 (rm-low-64 ptr-table-entry-addr x86-another))
                (equal (ia32e-page-tables-slice :ps ptr-table-entry-1) 0)

                (ia32e-la-to-pa-page-dir-ptr-table-entry-components-equal-p
                 '4K-or-2M ptr-table-entry-1 ptr-table-entry-2)

                ;; For ia32e-la-to-pa-page-directory:
                (equal page-directory-base-addr
                       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry-1) 12))
                (equal page-directory-entry-addr
                       (page-directory-entry-addr lin-addr page-directory-base-addr))
                (equal page-directory-entry-1 (rm-low-64 page-directory-entry-addr x86))
                (equal page-directory-entry-2 (rm-low-64 page-directory-entry-addr x86-another))

                (equal (ia32e-page-tables-slice :ps page-directory-entry-1) 0)

                (ia32e-la-to-pa-page-directory-entry-components-equal-p
                 '4K page-directory-entry-1 page-directory-entry-2)

                ;; For ia32e-la-to-pa-page-table:
                (equal page-table-base-addr
                       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry-1) 12))
                (equal page-table-entry-addr
                       (page-table-entry-addr lin-addr page-table-base-addr))
                (equal table-entry-1 (rm-low-64 page-table-entry-addr x86))
                (equal table-entry-2 (rm-low-64 page-table-entry-addr x86-another))

                (ia32e-la-to-pa-page-table-entry-components-equal-p
                 table-entry-1 table-entry-2))

           (ia32e-la-to-pa-pml4-table-entry-validp
            lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86-another))
  :in-theory (e/d
              (ia32e-la-to-pa-pml4-table-entry-components-equal-p
               ia32e-la-to-pa-page-dir-ptr-table-entry-components-equal-p
               ia32e-la-to-pa-page-directory-entry-components-equal-p
               ia32e-la-to-pa-page-table-entry-components-equal-p)
              ()))

(defruled pml4-table-components-equal-rm-low-64-of-pml4-entry-addr-via-pml4-table-4K-pages
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
                 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
                (equal pml4-entry-addr
                       (pml4-table-entry-addr lin-addr pml4-base-addr))
                (equal pml4-entry (rm-low-64 pml4-entry-addr x86))
                ;; For ia32e-la-to-pa-page-dir-ptr-table:
                (equal ptr-table-base-addr
                       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
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
                 (translation-governing-addresses-for-pml4-table
                  lin-addr pml4-base-addr x86))

                (physical-address-p pml4-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 pml4-base-addr) 0)
                (x86p x86))
           (ia32e-la-to-pa-pml4-table-entry-components-equal-p
            (rm-low-64 pml4-entry-addr x86)
            (rm-low-64
             pml4-entry-addr
             (mv-nth
              2
              (ia32e-la-to-pa-pml4-table lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)))))
  :hints (("Goal" :do-not '(preprocess)
           :use ((:instance rm-low-64-and-ia32e-la-to-pa-pml4-table-4K-pages))
           :in-theory (e/d
                       (ia32e-la-to-pa-pml4-table-entry-components-equal-p
                        ia32e-la-to-pa-page-dir-ptr-table-entry-components-equal-p
                        ia32e-la-to-pa-page-directory-entry-components-equal-p)
                       (ia32e-la-to-pa-pml4-table-entry-validp
                        mv-nth-2-no-error-ia32e-la-to-pa-pml4-table
                        disjoint-rm-low-64-read-mv-nth-2-no-error-ia32e-la-to-pa-pml4-table-4k-pages
                        subset-p-two-addr-ranges
                        disjoint-p-two-addr-ranges-thm-3
                        disjoint-p-two-addr-ranges-thm-2
                        disjoint-p-two-addr-ranges-thm-1
                        <-preserved-by-adding-<-*pseudo-page-size-in-bytes*-commuted
                        <-preserved-by-adding-<-*pseudo-page-size-in-bytes*
                        not
                        mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
                        mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
                        mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
                        member-p-cons
                        disjoint-p-cons
                        unsigned-byte-p
                        signed-byte-p)))))

(defruled page-dir-ptr-table-components-equal-rm-low-64-of-ptr-table-entry-addr-via-pml4-table-4K-pages
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
                 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
                (equal pml4-entry-addr
                       (pml4-table-entry-addr lin-addr pml4-base-addr))
                (equal pml4-entry (rm-low-64 pml4-entry-addr x86))
                ;; For ia32e-la-to-pa-page-dir-ptr-table:
                (equal ptr-table-base-addr
                       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
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
                 (translation-governing-addresses-for-pml4-table
                  lin-addr pml4-base-addr x86))

                (physical-address-p pml4-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 pml4-base-addr) 0)
                (x86p x86))
           (ia32e-la-to-pa-page-dir-ptr-table-entry-components-equal-p
            '4K-or-2M
            (rm-low-64 ptr-table-entry-addr x86)
            (rm-low-64
             ptr-table-entry-addr
             (mv-nth
              2
              (ia32e-la-to-pa-pml4-table
               lin-addr pml4-base-addr
               wp smep nxe r-w-x cpl x86)))))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (e/d
                       (page-dir-ptr-table-components-equal-rm-low-64-of-page-dir-ptr-table-entry-addr-via-page-dir-ptr-table-4K-pages)
                       (mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
                        mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4K-or-2M-pages
                        disjoint-rm-low-64-read-mv-nth-2-no-error-ia32e-la-to-pa-pml4-table-2M-pages
                        subset-p-two-addr-ranges
                        disjoint-p-two-addr-ranges-thm-3
                        disjoint-p-two-addr-ranges-thm-2
                        disjoint-p-two-addr-ranges-thm-1
                        <-preserved-by-adding-<-*pseudo-page-size-in-bytes*-commuted
                        <-preserved-by-adding-<-*pseudo-page-size-in-bytes*
                        not
                        member-p-cons
                        disjoint-p-cons
                        unsigned-byte-p
                        signed-byte-p)))))

(defruled page-directory-components-equal-rm-low-64-of-page-directory-entry-addr-via-pml4-table-4K-pages
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
                 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
                (equal pml4-entry-addr
                       (pml4-table-entry-addr lin-addr pml4-base-addr))
                (equal pml4-entry (rm-low-64 pml4-entry-addr x86))
                ;; For ia32e-la-to-pa-page-dir-ptr-table:
                (equal ptr-table-base-addr
                       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
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
                 (translation-governing-addresses-for-pml4-table
                  lin-addr pml4-base-addr x86))

                (physical-address-p pml4-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 pml4-base-addr) 0)
                (x86p x86))
           (ia32e-la-to-pa-page-directory-entry-components-equal-p
            '4K
            (rm-low-64 page-directory-entry-addr x86)
            (rm-low-64
             page-directory-entry-addr
             (mv-nth
              2
              (ia32e-la-to-pa-pml4-table
               lin-addr pml4-base-addr
               wp smep nxe r-w-x cpl x86)))))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (e/d
                       (page-directory-components-equal-rm-low-64-of-page-directory-entry-addr-via-page-dir-ptr-table-4K-pages)
                       (not
                        disjoint-rm-low-64-read-mv-nth-2-no-error-ia32e-la-to-pa-pml4-table-2M-pages
                        subset-p-two-addr-ranges
                        disjoint-p-two-addr-ranges-thm-3
                        disjoint-p-two-addr-ranges-thm-2
                        disjoint-p-two-addr-ranges-thm-1
                        <-preserved-by-adding-<-*pseudo-page-size-in-bytes*-commuted
                        <-preserved-by-adding-<-*pseudo-page-size-in-bytes*
                        mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
                        mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4K-or-2M-pages
                        member-p-cons
                        disjoint-p-cons
                        unsigned-byte-p
                        signed-byte-p)))))

(defruled page-table-components-equal-rm-low-64-of-page-table-entry-addr-via-pml4-table-4K-pages
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
                 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
                (equal pml4-entry-addr
                       (pml4-table-entry-addr lin-addr pml4-base-addr))
                (equal pml4-entry (rm-low-64 pml4-entry-addr x86))
                ;; For ia32e-la-to-pa-page-dir-ptr-table:
                (equal ptr-table-base-addr
                       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
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
                 (translation-governing-addresses-for-pml4-table
                  lin-addr pml4-base-addr x86))

                (physical-address-p pml4-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 pml4-base-addr) 0)
                (x86p x86))
           (ia32e-la-to-pa-page-table-entry-components-equal-p
            (rm-low-64 page-table-entry-addr x86)
            (rm-low-64
             page-table-entry-addr
             (mv-nth
              2
              (ia32e-la-to-pa-pml4-table
               lin-addr pml4-base-addr
               wp smep nxe r-w-x cpl x86)))))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (e/d
                       (page-table-components-equal-rm-low-64-of-page-table-entry-addr-via-page-dir-ptr-table-4K-pages)
                       (mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
                        mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4K-or-2M-pages
                        disjoint-rm-low-64-read-mv-nth-2-no-error-ia32e-la-to-pa-pml4-table-2M-pages
                        subset-p-two-addr-ranges
                        disjoint-p-two-addr-ranges-thm-3
                        disjoint-p-two-addr-ranges-thm-2
                        disjoint-p-two-addr-ranges-thm-1
                        <-preserved-by-adding-<-*pseudo-page-size-in-bytes*-commuted
                        <-preserved-by-adding-<-*pseudo-page-size-in-bytes*
                        not
                        member-p-cons
                        disjoint-p-cons
                        unsigned-byte-p
                        signed-byte-p)))))

(defrule re-read-entry-still-valid-ia32e-la-to-pa-pml4-table-4K-pages

  ;;    relating-validity-of-two-entries-in-two-x86-states-wrt-pml4-table-4K-pages needs
  ;;    the following:
  ;;    ia32e-la-to-pa-pml4-table-entry-components-equal-p
  ;;    ia32e-la-to-pa-page-dir-ptr-table-entry-components-equal-p
  ;;    ia32e-la-to-pa-page-directory-entry-components-equal-p
  ;;    ia32e-la-to-pa-page-table-entry-components-equal-p

  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
                 lin-addr pml4-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)
                (ia32e-la-to-pa-pml4-table-entry-validp
                 lin-addr pml4-base-addr wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)
                (equal pml4-entry-addr
                       (pml4-table-entry-addr lin-addr pml4-base-addr))
                (equal pml4-entry (rm-low-64 pml4-entry-addr x86))
                ;; For ia32e-la-to-pa-page-dir-ptr-table:
                (equal ptr-table-base-addr
                       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
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
                 (translation-governing-addresses-for-pml4-table
                  lin-addr pml4-base-addr x86))

                (physical-address-p pml4-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 pml4-base-addr) 0)
                (x86p x86))

           (ia32e-la-to-pa-pml4-table-entry-validp
            lin-addr pml4-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
            (mv-nth
             2
             (ia32e-la-to-pa-pml4-table
              lin-addr pml4-base-addr wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
  :do-not '(preprocess)
  :in-theory (e/d
              (pml4-table-components-equal-rm-low-64-of-pml4-entry-addr-via-pml4-table-4K-pages
               page-dir-ptr-table-components-equal-rm-low-64-of-ptr-table-entry-addr-via-pml4-table-4K-pages
               page-directory-components-equal-rm-low-64-of-page-directory-entry-addr-via-pml4-table-4K-pages
               page-table-components-equal-rm-low-64-of-page-table-entry-addr-via-pml4-table-4K-pages)
              (ia32e-la-to-pa-pml4-table-entry-validp
               not
               mv-nth-2-no-error-ia32e-la-to-pa-pml4-table
               mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-4K-or-2M-pages
               mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
               acl2::mv-nth-cons-meta
               unsigned-byte-p
               signed-byte-p)))

;; ......................................................................
;; Two pml4 table walks theorem --- same addresses:
;; ......................................................................

;; 1G pages:

(defruled page-size-from-re-reading-page-dir-ptr-table-entry-given-pml4-entry-validp-1G-pages
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
                 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
                (equal pml4-entry-addr
                       (pml4-table-entry-addr lin-addr pml4-base-addr))
                (equal pml4-entry (rm-low-64 pml4-entry-addr x86))
                ;; For ia32e-la-to-pa-page-dir-ptr-table:
                (equal ptr-table-base-addr
                       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
                (equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  ptr-table-entry) 1)

                ;; (disjoint-p (addr-range 8 pml4-entry-addr)
                ;;          (addr-range 8 ptr-table-entry-addr))
                (pairwise-disjoint-p
                 (translation-governing-addresses-for-pml4-table
                  lin-addr pml4-base-addr x86))
                (physical-address-p pml4-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 pml4-base-addr) 0)
                (x86p x86))
           (equal (ia32e-page-tables-slice
                   :ps
                   (rm-low-64
                    ptr-table-entry-addr
                    (mv-nth 2
                            (ia32e-la-to-pa-page-dir-ptr-table
                             lin-addr ptr-table-base-addr wp smep
                             nxe r-w-x cpl x86))))
                  1))
  :do-not '(preprocess)
  :in-theory (e/d* (
                    rm-low-64-and-page-dir-ptr-table-1G-pages)
                   (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                    not
                    unsigned-byte-p
                    signed-byte-p)))

(defruled logtail-12-of-reading-page-dir-ptr-table-entry-from-state-after-page-dir-ptr-table-given-pml4-table-validp-1G-pages
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
                 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
                (equal pml4-entry-addr
                       (pml4-table-entry-addr lin-addr pml4-base-addr))
                (equal pml4-entry (rm-low-64 pml4-entry-addr x86))
                ;; For ia32e-la-to-pa-page-dir-ptr-table:
                (equal ptr-table-base-addr
                       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
                (equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  ptr-table-entry) 1)

                ;; (disjoint-p (addr-range 8 pml4-entry-addr)
                ;;          (addr-range 8 ptr-table-entry-addr))
                (pairwise-disjoint-p
                 (translation-governing-addresses-for-pml4-table
                  lin-addr pml4-base-addr x86))
                (physical-address-p pml4-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 pml4-base-addr) 0)
                (x86p x86))
           (equal (logtail 12
                           (rm-low-64
                            ptr-table-entry-addr
                            (mv-nth 2
                                    (ia32e-la-to-pa-page-dir-ptr-table
                                     lin-addr ptr-table-base-addr wp smep
                                     nxe r-w-x cpl x86))))
                  (logtail 12 (rm-low-64 ptr-table-entry-addr x86))))
  :do-not '(preprocess)
  :in-theory (e/d* (
                    rm-low-64-and-page-dir-ptr-table-1G-pages)
                   (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                    not
                    unsigned-byte-p
                    signed-byte-p)))

(defruled re-read-entry-still-pml4-table-valid-page-dir-ptr-table-1G-pages
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
                 lin-addr pml4-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)
                (ia32e-la-to-pa-pml4-table-entry-validp
                 lin-addr pml4-base-addr wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)
                (equal pml4-entry-addr
                       (pml4-table-entry-addr lin-addr pml4-base-addr))
                (equal pml4-entry (rm-low-64 pml4-entry-addr x86))
                ;; For ia32e-la-to-pa-page-dir-ptr-table:
                (equal ptr-table-base-addr
                       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
                (equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  ptr-table-entry) 1)

                ;; (disjoint-p (addr-range 8 pml4-entry-addr)
                ;;          (addr-range 8 ptr-table-entry-addr))
                (pairwise-disjoint-p
                 (translation-governing-addresses-for-pml4-table
                  lin-addr pml4-base-addr x86))
                (physical-address-p pml4-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 pml4-base-addr) 0)
                (x86p x86))
           (ia32e-la-to-pa-pml4-table-entry-validp
            lin-addr pml4-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
            (mv-nth
             2
             (ia32e-la-to-pa-page-dir-ptr-table
              lin-addr ptr-table-base-addr wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
  :do-not '(preprocess)
  :in-theory (e/d
              (page-dir-ptr-table-components-equal-rm-low-64-of-page-dir-ptr-table-entry-addr-via-page-dir-ptr-table-1G-pages)
              (ia32e-la-to-pa-pml4-table-entry-validp
               not
               mv-nth-2-no-error-ia32e-la-to-pa-pml4-table
               mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-1g-pages
               mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-1g-pages
               acl2::mv-nth-cons-meta
               unsigned-byte-p
               signed-byte-p)))

(defrule two-page-table-walks-ia32e-la-to-pa-pml4-table-1G-pages-same-addresses

  ;; Key lemmas needed:
  ;; mv-nth-2-no-error-ia32e-la-to-pa-pml4-table
  ;; re-read-entry-still-pml4-table-valid-page-dir-ptr-table-1G-pages
  ;; reading-entry-with-accessed-bit-set-ia32e-la-to-pa-pml4-table-1G-pages
  ;; mv-nth-1-no-error-ia32e-la-to-pa-pml4-table
  ;; pml4-table-entry-validp-to-page-dir-ptr-entry-validp
  ;; two-page-table-walks-ia32e-la-to-pa-dir-ptr-table-1G-pages-same-addresses

  ;; Note that for this theorem, we also need:
  ;; page-size-from-re-reading-page-dir-ptr-table-entry-given-pml4-entry-validp-1G-pages
  ;; logtail-12-of-reading-page-dir-ptr-table-entry-from-state-after-page-dir-ptr-table-given-pml4-table-validp-1G-pages

  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
                 lin-addr pml4-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)
                (ia32e-la-to-pa-pml4-table-entry-validp
                 lin-addr pml4-base-addr wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)
                (equal pml4-entry-addr
                       (pml4-table-entry-addr lin-addr pml4-base-addr))
                (equal pml4-entry (rm-low-64 pml4-entry-addr x86))
                ;; For ia32e-la-to-pa-page-dir-ptr-table:
                (equal ptr-table-base-addr
                       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
                (equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  ptr-table-entry) 1)

                ;; (disjoint-p (addr-range 8 pml4-entry-addr)
                ;;          (addr-range 8 ptr-table-entry-addr))
                (pairwise-disjoint-p
                 (translation-governing-addresses-for-pml4-table
                  lin-addr pml4-base-addr x86))
                (physical-address-p pml4-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 pml4-base-addr) 0)
                (x86p x86))
           (equal
            (mv-nth
             1
             (ia32e-la-to-pa-pml4-table
              lin-addr pml4-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
              (mv-nth
               2
               (ia32e-la-to-pa-pml4-table
                lin-addr pml4-base-addr wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
            (mv-nth
             1
             (ia32e-la-to-pa-pml4-table
              lin-addr pml4-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86))))
  :do-not '(preprocess)
  :in-theory (e/d (page-size-from-re-reading-page-dir-ptr-table-entry-given-pml4-entry-validp-1G-pages
                   logtail-12-of-reading-page-dir-ptr-table-entry-from-state-after-page-dir-ptr-table-given-pml4-table-validp-1G-pages
                   re-read-entry-still-pml4-table-valid-page-dir-ptr-table-1G-pages)
                  (ia32e-la-to-pa-pml4-table-entry-validp
                   mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-1g-pages
                   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-1g-pages
                   member-p-cons
                   disjoint-p-cons
                   not
                   unsigned-byte-p
                   signed-byte-p)))

(defrule re-read-entry-still-pml4-table-valid-page-dir-ptr-table-1G-pages-same-entry-different-addrs
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
                 lin-addr-1 pml4-table-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)
                (ia32e-la-to-pa-pml4-table-entry-validp
                 lin-addr-2 pml4-table-base-addr wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)
                (equal pml4-entry-addr
                       (pml4-table-entry-addr lin-addr-1 pml4-table-base-addr))
                (equal pml4-entry (rm-low-64 pml4-entry-addr x86))
                ;; For ia32e-la-to-pa-page-dir-ptr-table:
                (equal ptr-table-base-addr
                       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr-1 ptr-table-base-addr))
                (equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  ptr-table-entry) 1)

                ;; So that pml4 table entries are the same...
                (equal (part-select lin-addr-1 :low 39 :high 47)
                       (part-select lin-addr-2 :low 39 :high 47))
                ;; So that the ptr table entries are the same...
                (equal (part-select lin-addr-1 :low 30 :high 38)
                       (part-select lin-addr-2 :low 30 :high 38))
                ;; So that the physical addresses are different...
                (not (equal (part-select lin-addr-1 :low 0 :high 29)
                            (part-select lin-addr-2 :low 0 :high 29)))

                (pairwise-disjoint-p
                 (translation-governing-addresses-for-pml4-table
                  lin-addr-1 pml4-table-base-addr x86))
                (physical-address-p pml4-table-base-addr)
                (canonical-address-p lin-addr-1)
                (canonical-address-p lin-addr-2)
                (equal (loghead 12 pml4-table-base-addr) 0)
                (x86p x86))
           (ia32e-la-to-pa-pml4-table-entry-validp
            lin-addr-1 pml4-table-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
            (mv-nth 2
                    (ia32e-la-to-pa-page-dir-ptr-table
                     lin-addr-2 ptr-table-base-addr wp-2 smep-2
                     nxe-2 r-w-x-2 cpl-2 x86))))
  :do-not '(preprocess)
  :use ((:instance equality-of-pml4-table-entry-addr)
        (:instance equality-of-page-dir-ptr-table-entry-addr))
  :in-theory (e/d
              (page-dir-ptr-table-components-equal-rm-low-64-of-page-dir-ptr-table-entry-addr-via-page-dir-ptr-table-1G-pages
               pml4-table-components-equal-rm-low-64-of-pml4-entry-addr-via-pml4-table-1G-pages)
              (ia32e-la-to-pa-pml4-table-entry-validp
               not
               mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-1g-pages
               mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-1g-pages
               acl2::mv-nth-cons-meta
               unsigned-byte-p
               signed-byte-p)))

(defrule two-page-table-walks-ia32e-la-to-pa-pml4-table-1G-pages-same-entry-different-addrs
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
                 lin-addr-1 pml4-table-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)
                (ia32e-la-to-pa-pml4-table-entry-validp
                 lin-addr-2 pml4-table-base-addr wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)
                (equal pml4-entry-addr
                       (pml4-table-entry-addr lin-addr-1 pml4-table-base-addr))
                (equal pml4-entry (rm-low-64 pml4-entry-addr x86))
                ;; For ia32e-la-to-pa-page-dir-ptr-table:
                (equal ptr-table-base-addr
                       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr-1 ptr-table-base-addr))
                (equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  ptr-table-entry) 1)

                ;; So that pml4 table entries are the same...
                (equal (part-select lin-addr-1 :low 39 :high 47)
                       (part-select lin-addr-2 :low 39 :high 47))
                ;; So that the ptr table entries are the same...
                (equal (part-select lin-addr-1 :low 30 :high 38)
                       (part-select lin-addr-2 :low 30 :high 38))
                ;; So that the physical addresses are different...
                (not (equal (part-select lin-addr-1 :low 0 :high 29)
                            (part-select lin-addr-2 :low 0 :high 29)))

                (pairwise-disjoint-p
                 (translation-governing-addresses-for-pml4-table
                  lin-addr-1 pml4-table-base-addr x86))
                (physical-address-p pml4-table-base-addr)
                (canonical-address-p lin-addr-1)
                (canonical-address-p lin-addr-2)
                (equal (loghead 12 pml4-table-base-addr) 0)
                (x86p x86))
           (equal
            (mv-nth
             1
             (ia32e-la-to-pa-pml4-table
              lin-addr-1 pml4-table-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
              (mv-nth
               2
               (ia32e-la-to-pa-pml4-table
                lin-addr-2 pml4-table-base-addr wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
            (mv-nth
             1
             (ia32e-la-to-pa-pml4-table
              lin-addr-1 pml4-table-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86))))
  :do-not '(preprocess)
  :use ((:instance equality-of-pml4-table-entry-addr)
        (:instance equality-of-page-dir-ptr-table-entry-addr))
  :in-theory (e/d (page-size-from-re-reading-page-dir-ptr-table-entry-given-pml4-entry-validp-1G-pages
                   logtail-12-of-reading-page-dir-ptr-table-entry-from-state-after-page-dir-ptr-table-given-pml4-table-validp-1G-pages
                   re-read-entry-still-pml4-table-valid-page-dir-ptr-table-1G-pages)
                  (ia32e-la-to-pa-pml4-table-entry-validp
                   mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-1g-pages
                   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-1g-pages
                   mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-4K-or-2M-pages
                   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
                   member-p-cons
                   disjoint-p-cons
                   not
                   unsigned-byte-p
                   signed-byte-p)))

;; 2M pages:

(defruled page-size-from-re-reading-page-dir-ptr-table-entry-given-pml4-entry-validp-2M-pages
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
                 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
                (equal pml4-entry-addr
                       (pml4-table-entry-addr lin-addr pml4-base-addr))
                (equal pml4-entry (rm-low-64 pml4-entry-addr x86))
                ;; For ia32e-la-to-pa-page-dir-ptr-table:
                (equal ptr-table-base-addr
                       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
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

                ;; (pairwise-disjoint-p
                ;;  (list (addr-range 8 pml4-entry-addr)
                ;;        (addr-range 8 ptr-table-entry-addr)
                ;;        (addr-range 8 page-directory-entry-addr)))
                (pairwise-disjoint-p
                 (translation-governing-addresses-for-pml4-table
                  lin-addr pml4-base-addr x86))
                (physical-address-p pml4-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 pml4-base-addr) 0)
                (x86p x86))
           (equal (ia32e-page-tables-slice
                   :ps
                   (rm-low-64
                    ptr-table-entry-addr
                    (mv-nth 2
                            (ia32e-la-to-pa-page-dir-ptr-table
                             lin-addr ptr-table-base-addr wp smep
                             nxe r-w-x cpl x86))))
                  0))
  :do-not '(preprocess)
  :in-theory (e/d* (
                    rm-low-64-and-page-dir-ptr-table-2M-pages)
                   (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                    mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
                    mv-nth-2-no-error-ia32e-la-to-pa-page-directory-2m-pages
                    subset-p-two-addr-ranges
                    disjoint-p-two-addr-ranges-thm-3
                    disjoint-p-two-addr-ranges-thm-2
                    disjoint-p-two-addr-ranges-thm-1
                    <-preserved-by-adding-<-*pseudo-page-size-in-bytes*-commuted
                    <-preserved-by-adding-<-*pseudo-page-size-in-bytes*
                    not
                    unsigned-byte-p
                    signed-byte-p)))

(defruled page-size-from-reading-page-directory-entry-from-state-after-page-dir-ptr-table-given-pml4-entry-validp-2M-pages
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
                 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
                (equal pml4-entry-addr
                       (pml4-table-entry-addr lin-addr pml4-base-addr))
                (equal pml4-entry (rm-low-64 pml4-entry-addr x86))
                ;; For ia32e-la-to-pa-page-dir-ptr-table:
                (equal ptr-table-base-addr
                       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
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

                ;; (pairwise-disjoint-p
                ;;  (list (addr-range 8 pml4-entry-addr)
                ;;        (addr-range 8 ptr-table-entry-addr)
                ;;        (addr-range 8 page-directory-entry-addr)))
                (pairwise-disjoint-p
                 (translation-governing-addresses-for-pml4-table
                  lin-addr pml4-base-addr x86))
                (physical-address-p pml4-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 pml4-base-addr) 0)
                (x86p x86))
           (equal (ia32e-page-tables-slice
                   :ps
                   (rm-low-64
                    page-directory-entry-addr
                    (mv-nth 2
                            (ia32e-la-to-pa-page-dir-ptr-table
                             lin-addr ptr-table-base-addr wp smep
                             nxe r-w-x cpl x86))))
                  1))
  :do-not '(preprocess)
  :in-theory (e/d* (rm-low-64-and-page-dir-ptr-table-2M-pages
                    rm-low-64-and-page-directory-2M-pages)
                   (subset-p-two-addr-ranges
                    disjoint-p-two-addr-ranges-thm-3
                    disjoint-p-two-addr-ranges-thm-2
                    disjoint-p-two-addr-ranges-thm-1
                    <-preserved-by-adding-<-*pseudo-page-size-in-bytes*-commuted
                    <-preserved-by-adding-<-*pseudo-page-size-in-bytes*
                    not
                    unsigned-byte-p
                    signed-byte-p)))

(defruled logtail-12-of-reading-page-dir-ptr-table-entry-from-state-after-page-dir-ptr-table-given-pml4-table-validp-2M-pages
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
                 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
                (equal pml4-entry-addr
                       (pml4-table-entry-addr lin-addr pml4-base-addr))
                (equal pml4-entry (rm-low-64 pml4-entry-addr x86))
                ;; For ia32e-la-to-pa-page-dir-ptr-table:
                (equal ptr-table-base-addr
                       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
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

                ;; (pairwise-disjoint-p
                ;;  (list (addr-range 8 pml4-entry-addr)
                ;;        (addr-range 8 ptr-table-entry-addr)
                ;;        (addr-range 8 page-directory-entry-addr)))
                (pairwise-disjoint-p
                 (translation-governing-addresses-for-pml4-table
                  lin-addr pml4-base-addr x86))
                (physical-address-p pml4-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 pml4-base-addr) 0)
                (x86p x86))
           (equal (logtail 12
                           (rm-low-64
                            ptr-table-entry-addr
                            (mv-nth 2
                                    (ia32e-la-to-pa-page-dir-ptr-table
                                     lin-addr ptr-table-base-addr wp smep
                                     nxe r-w-x cpl x86))))
                  (logtail 12 (rm-low-64 ptr-table-entry-addr x86))))
  :do-not '(preprocess)
  :in-theory (e/d* (
                    rm-low-64-and-page-dir-ptr-table-2M-pages
                    page-size-from-re-reading-page-dir-ptr-table-entry-given-pml4-entry-validp-2M-pages
                    page-size-from-reading-page-directory-entry-from-state-after-page-dir-ptr-table-given-pml4-entry-validp-2M-pages)
                   (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                    mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
                    mv-nth-2-no-error-ia32e-la-to-pa-page-directory-2m-pages
                    subset-p-two-addr-ranges
                    disjoint-p-two-addr-ranges-thm-3
                    disjoint-p-two-addr-ranges-thm-2
                    disjoint-p-two-addr-ranges-thm-1
                    <-preserved-by-adding-<-*pseudo-page-size-in-bytes*-commuted
                    <-preserved-by-adding-<-*pseudo-page-size-in-bytes*
                    not
                    unsigned-byte-p
                    signed-byte-p)))

(defruled re-read-entry-still-pml4-table-valid-page-dir-ptr-table-2M-pages
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
                 lin-addr pml4-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)
                (ia32e-la-to-pa-pml4-table-entry-validp
                 lin-addr pml4-base-addr wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)
                (equal pml4-entry-addr
                       (pml4-table-entry-addr lin-addr pml4-base-addr))
                (equal pml4-entry (rm-low-64 pml4-entry-addr x86))
                ;; For ia32e-la-to-pa-page-dir-ptr-table:
                (equal ptr-table-base-addr
                       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
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

                ;; (pairwise-disjoint-p
                ;;  (list (addr-range 8 pml4-entry-addr)
                ;;        (addr-range 8 ptr-table-entry-addr)
                ;;        (addr-range 8 page-directory-entry-addr)))

                (pairwise-disjoint-p
                 (translation-governing-addresses-for-pml4-table
                  lin-addr pml4-base-addr x86))

                (physical-address-p pml4-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 pml4-base-addr) 0)
                (x86p x86))

           (ia32e-la-to-pa-pml4-table-entry-validp
            lin-addr pml4-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
            (mv-nth
             2
             (ia32e-la-to-pa-page-dir-ptr-table
              lin-addr ptr-table-base-addr wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))

  :do-not '(preprocess)
  :in-theory (e/d
              (page-dir-ptr-table-components-equal-rm-low-64-of-page-dir-ptr-table-entry-addr-via-page-dir-ptr-table-2M-pages
               page-directory-components-equal-rm-low-64-of-page-directory-entry-addr-via-page-dir-ptr-table-2M-pages
               logtail-12-of-reading-page-dir-ptr-table-entry-from-state-after-page-dir-ptr-table-given-pml4-table-validp-2M-pages
               page-size-from-re-reading-page-dir-ptr-table-entry-given-pml4-entry-validp-2M-pages
               page-size-from-reading-page-directory-entry-from-state-after-page-dir-ptr-table-given-pml4-entry-validp-2M-pages)
              (ia32e-la-to-pa-pml4-table-entry-validp
               not
               mv-nth-2-no-error-ia32e-la-to-pa-pml4-table
               mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-4K-or-2M-pages
               mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
               acl2::mv-nth-cons-meta
               subset-p-two-addr-ranges
               disjoint-p-two-addr-ranges-thm-3
               disjoint-p-two-addr-ranges-thm-2
               disjoint-p-two-addr-ranges-thm-1
               <-preserved-by-adding-<-*pseudo-page-size-in-bytes*-commuted
               <-preserved-by-adding-<-*pseudo-page-size-in-bytes*
               unsigned-byte-p
               signed-byte-p)))

(defrule two-page-table-walks-ia32e-la-to-pa-pml4-table-2M-pages-same-addresses

  ;; Key lemmas needed:

  ;; mv-nth-2-no-error-ia32e-la-to-pa-pml4-table
  ;; re-read-entry-still-pml4-table-valid-page-dir-ptr-table-2M-pages
  ;; reading-entry-with-accessed-bit-set-ia32e-la-to-pa-pml4-table-2M-pages
  ;; mv-nth-1-no-error-ia32e-la-to-pa-pml4-table
  ;; pml4-table-entry-validp-to-page-dir-ptr-entry-validp
  ;; two-page-table-walks-ia32e-la-to-pa-dir-ptr-table-2M-pages-same-addresses

  ;; Note that for this theorem, we also need:
  ;; page-size-from-re-reading-page-dir-ptr-table-entry-given-pml4-entry-validp-2M-pages
  ;; page-size-from-reading-page-directory-entry-from-state-after-page-dir-ptr-table-given-pml4-entry-validp-2M-pages
  ;; logtail-12-of-reading-page-dir-ptr-table-entry-from-state-after-page-dir-ptr-table-given-pml4-table-validp-2M-pages

  ;; I discovered that I needed the additional lemmas by:
  ;; (acl2::why reading-entry-with-accessed-bit-set-ia32e-la-to-pa-pml4-table-2M-pages)
  ;; (acl2::why relating-validity-of-two-entries-in-two-x86-states-wrt-pml4-table-2M-pages)

  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
                 lin-addr pml4-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)
                (ia32e-la-to-pa-pml4-table-entry-validp
                 lin-addr pml4-base-addr wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)
                (equal pml4-entry-addr
                       (pml4-table-entry-addr lin-addr pml4-base-addr))
                (equal pml4-entry (rm-low-64 pml4-entry-addr x86))
                ;; For ia32e-la-to-pa-page-dir-ptr-table:
                (equal ptr-table-base-addr
                       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
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

                ;; (pairwise-disjoint-p
                ;;  (list (addr-range 8 pml4-entry-addr)
                ;;        (addr-range 8 ptr-table-entry-addr)
                ;;        (addr-range 8 page-directory-entry-addr)))

                (pairwise-disjoint-p
                 (translation-governing-addresses-for-pml4-table
                  lin-addr pml4-base-addr x86))

                (physical-address-p pml4-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 pml4-base-addr) 0)
                (x86p x86))
           (equal
            (mv-nth
             1
             (ia32e-la-to-pa-pml4-table
              lin-addr pml4-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
              (mv-nth
               2
               (ia32e-la-to-pa-pml4-table
                lin-addr pml4-base-addr wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
            (mv-nth
             1
             (ia32e-la-to-pa-pml4-table
              lin-addr pml4-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86))))
  :do-not '(preprocess)
  :in-theory (e/d (page-dir-ptr-table-components-equal-rm-low-64-of-page-dir-ptr-table-entry-addr-via-page-dir-ptr-table-2M-pages
                   page-directory-components-equal-rm-low-64-of-page-directory-entry-addr-via-page-dir-ptr-table-2M-pages
                   re-read-entry-still-pml4-table-valid-page-dir-ptr-table-2M-pages
                   page-size-from-re-reading-page-dir-ptr-table-entry-given-pml4-entry-validp-2M-pages
                   page-size-from-reading-page-directory-entry-from-state-after-page-dir-ptr-table-given-pml4-entry-validp-2M-pages
                   logtail-12-of-reading-page-dir-ptr-table-entry-from-state-after-page-dir-ptr-table-given-pml4-table-validp-2M-pages)
                  (ia32e-la-to-pa-pml4-table-entry-validp
                   member-p-cons
                   disjoint-p-cons
                   mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-4K-or-2M-pages
                   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
                   subset-p-two-addr-ranges
                   disjoint-p-two-addr-ranges-thm-3
                   disjoint-p-two-addr-ranges-thm-2
                   disjoint-p-two-addr-ranges-thm-1
                   <-preserved-by-adding-<-*pseudo-page-size-in-bytes*-commuted
                   <-preserved-by-adding-<-*pseudo-page-size-in-bytes*
                   not
                   unsigned-byte-p
                   signed-byte-p)))

(defrule two-page-table-walks-ia32e-la-to-pa-pml4-table-2M-pages-same-entry-different-addrs
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
                 lin-addr-1 pml4-table-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)
                (ia32e-la-to-pa-pml4-table-entry-validp
                 lin-addr-2 pml4-table-base-addr wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)
                (equal pml4-entry-addr
                       (pml4-table-entry-addr lin-addr-1 pml4-table-base-addr))
                (equal pml4-entry (rm-low-64 pml4-entry-addr x86))
                ;; For ia32e-la-to-pa-page-dir-ptr-table:
                (equal ptr-table-base-addr
                       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr-1 ptr-table-base-addr))
                (equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)
                ;; For ia32e-la-to-pa-page-directory:
                (equal page-directory-base-addr
                       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
                (equal page-directory-entry-addr
                       (page-directory-entry-addr lin-addr-1 page-directory-base-addr))
                (equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps page-directory-entry) 1)
                (pairwise-disjoint-p
                 (translation-governing-addresses-for-pml4-table
                  lin-addr-1 pml4-table-base-addr x86))

                ;; So that pml4 table entries are the same...
                (equal (part-select lin-addr-1 :low 39 :high 47)
                       (part-select lin-addr-2 :low 39 :high 47))
                ;; So that the ptr table entries are the same...
                (equal (part-select lin-addr-1 :low 30 :high 38)
                       (part-select lin-addr-2 :low 30 :high 38))
                ;; So that the page directory entries are the same...
                (equal (part-select lin-addr-1 :low 21 :high 29)
                       (part-select lin-addr-2 :low 21 :high 29))
                ;; So that the physical address is different...
                (not (equal (part-select lin-addr-1 :low 0 :high 20)
                            (part-select lin-addr-2 :low 0 :high 20)))

                (physical-address-p pml4-table-base-addr)
                (canonical-address-p lin-addr-1)
                (canonical-address-p lin-addr-2)
                (equal (loghead 12 pml4-table-base-addr) 0)
                (x86p x86))
           (equal
            (mv-nth
             1
             (ia32e-la-to-pa-pml4-table
              lin-addr-1 pml4-table-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
              (mv-nth
               2
               (ia32e-la-to-pa-pml4-table
                lin-addr-2 pml4-table-base-addr wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
            (mv-nth
             1
             (ia32e-la-to-pa-pml4-table
              lin-addr-1 pml4-table-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86))))
  :do-not '(preprocess)
  :use ((:instance equality-of-pml4-table-entry-addr)
        (:instance equality-of-page-dir-ptr-table-entry-addr)
        (:instance equality-of-page-directory-entry-addr))
  :in-theory (e/d (page-dir-ptr-table-components-equal-rm-low-64-of-page-dir-ptr-table-entry-addr-via-page-dir-ptr-table-2M-pages
                   page-directory-components-equal-rm-low-64-of-page-directory-entry-addr-via-page-dir-ptr-table-2M-pages
                   re-read-entry-still-pml4-table-valid-page-dir-ptr-table-2M-pages
                   page-size-from-re-reading-page-dir-ptr-table-entry-given-pml4-entry-validp-2M-pages
                   page-size-from-reading-page-directory-entry-from-state-after-page-dir-ptr-table-given-pml4-entry-validp-2M-pages
                   logtail-12-of-reading-page-dir-ptr-table-entry-from-state-after-page-dir-ptr-table-given-pml4-table-validp-2M-pages)
                  (ia32e-la-to-pa-pml4-table-entry-validp
                   mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-1g-pages
                   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-1g-pages
                   mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-4K-or-2M-pages
                   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
                   member-p-cons
                   disjoint-p-cons
                   not
                   unsigned-byte-p
                   signed-byte-p)))

;; 4K pages:

(defruled page-size-from-re-reading-page-dir-ptr-table-entry-given-pml4-entry-validp-4K-pages
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
                 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
                (equal pml4-entry-addr
                       (pml4-table-entry-addr lin-addr pml4-base-addr))
                (equal pml4-entry (rm-low-64 pml4-entry-addr x86))
                ;; For ia32e-la-to-pa-page-dir-ptr-table:
                (equal ptr-table-base-addr
                       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
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


                ;; (pairwise-disjoint-p
                ;;  (list (addr-range 8 pml4-entry-addr)
                ;;        (addr-range 8 ptr-table-entry-addr)
                ;;        (addr-range 8 page-directory-entry-addr)
                ;;        (addr-range 8 page-table-entry-addr)))

                (pairwise-disjoint-p
                 (translation-governing-addresses-for-pml4-table
                  lin-addr pml4-base-addr x86))

                (physical-address-p pml4-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 pml4-base-addr) 0)
                (x86p x86))
           (equal (ia32e-page-tables-slice
                   :ps
                   (rm-low-64
                    ptr-table-entry-addr
                    (mv-nth 2
                            (ia32e-la-to-pa-page-dir-ptr-table
                             lin-addr ptr-table-base-addr wp smep
                             nxe r-w-x cpl x86))))
                  0))
  :do-not '(preprocess)
  :in-theory (e/d* (
                    rm-low-64-and-page-dir-ptr-table-4K-pages)
                   (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                    mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
                    mv-nth-2-no-error-ia32e-la-to-pa-page-directory-2m-pages
                    subset-p-two-addr-ranges
                    disjoint-p-two-addr-ranges-thm-3
                    disjoint-p-two-addr-ranges-thm-2
                    disjoint-p-two-addr-ranges-thm-1
                    disjoint-p-two-addr-ranges-thm-0
                    <-preserved-by-adding-<-*pseudo-page-size-in-bytes*-commuted
                    <-preserved-by-adding-<-*pseudo-page-size-in-bytes*
                    not
                    unsigned-byte-p
                    signed-byte-p)))

(defruled page-size-from-reading-page-directory-entry-from-state-after-page-dir-ptr-table-given-pml4-entry-validp-4K-pages
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
                 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
                (equal pml4-entry-addr
                       (pml4-table-entry-addr lin-addr pml4-base-addr))
                (equal pml4-entry (rm-low-64 pml4-entry-addr x86))
                ;; For ia32e-la-to-pa-page-dir-ptr-table:
                (equal ptr-table-base-addr
                       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
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


                ;; (pairwise-disjoint-p
                ;;  (list (addr-range 8 pml4-entry-addr)
                ;;        (addr-range 8 ptr-table-entry-addr)
                ;;        (addr-range 8 page-directory-entry-addr)
                ;;        (addr-range 8 page-table-entry-addr)))
                (pairwise-disjoint-p
                 (translation-governing-addresses-for-pml4-table
                  lin-addr pml4-base-addr x86))


                (physical-address-p pml4-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 pml4-base-addr) 0)
                (x86p x86))
           (equal (ia32e-page-tables-slice
                   :ps
                   (rm-low-64
                    page-directory-entry-addr
                    (mv-nth 2
                            (ia32e-la-to-pa-page-dir-ptr-table
                             lin-addr ptr-table-base-addr wp smep
                             nxe r-w-x cpl x86))))
                  0))
  :do-not '(preprocess)
  :in-theory (e/d* (rm-low-64-and-page-dir-ptr-table-4K-pages
                    rm-low-64-and-page-directory-4K-pages
                    rm-low-64-and-page-table
                    ia32e-la-to-pa-page-dir-ptr-table-entry-validp)
                   (mv-nth-2-no-error-ia32e-la-to-pa-page-table
                    subset-p-two-addr-ranges
                    disjoint-p-two-addr-ranges-thm-3
                    disjoint-p-two-addr-ranges-thm-2
                    disjoint-p-two-addr-ranges-thm-1
                    disjoint-p-two-addr-ranges-thm-0
                    <-preserved-by-adding-<-*pseudo-page-size-in-bytes*-commuted
                    <-preserved-by-adding-<-*pseudo-page-size-in-bytes*
                    not
                    unsigned-byte-p
                    signed-byte-p)))

(defruled logtail-12-of-reading-page-dir-ptr-table-entry-from-state-after-page-dir-ptr-table-given-pml4-table-validp-4K-pages
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
                 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
                (equal pml4-entry-addr
                       (pml4-table-entry-addr lin-addr pml4-base-addr))
                (equal pml4-entry (rm-low-64 pml4-entry-addr x86))
                ;; For ia32e-la-to-pa-page-dir-ptr-table:
                (equal ptr-table-base-addr
                       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
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


                ;; (pairwise-disjoint-p
                ;;  (list (addr-range 8 pml4-entry-addr)
                ;;        (addr-range 8 ptr-table-entry-addr)
                ;;        (addr-range 8 page-directory-entry-addr)
                ;;        (addr-range 8 page-table-entry-addr)))
                (pairwise-disjoint-p
                 (translation-governing-addresses-for-pml4-table
                  lin-addr pml4-base-addr x86))

                (physical-address-p pml4-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 pml4-base-addr) 0)
                (x86p x86))
           (equal (logtail 12
                           (rm-low-64
                            ptr-table-entry-addr
                            (mv-nth 2
                                    (ia32e-la-to-pa-page-dir-ptr-table
                                     lin-addr ptr-table-base-addr wp smep
                                     nxe r-w-x cpl x86))))
                  (logtail 12 (rm-low-64 ptr-table-entry-addr x86))))
  :do-not '(preprocess)
  :in-theory (e/d* (rm-low-64-and-page-dir-ptr-table-4K-pages
                    page-size-from-re-reading-page-dir-ptr-table-entry-given-pml4-entry-validp-4K-pages
                    page-size-from-reading-page-directory-entry-from-state-after-page-dir-ptr-table-given-pml4-entry-validp-4K-pages)
                   (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
                    mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
                    mv-nth-2-no-error-ia32e-la-to-pa-page-directory-2m-pages
                    subset-p-two-addr-ranges
                    disjoint-p-two-addr-ranges-thm-3
                    disjoint-p-two-addr-ranges-thm-2
                    disjoint-p-two-addr-ranges-thm-1
                    disjoint-p-two-addr-ranges-thm-0
                    <-preserved-by-adding-<-*pseudo-page-size-in-bytes*-commuted
                    <-preserved-by-adding-<-*pseudo-page-size-in-bytes*
                    not
                    unsigned-byte-p
                    signed-byte-p)))

(defruled re-read-entry-still-pml4-table-valid-page-dir-ptr-table-4K-pages
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
                 lin-addr pml4-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)
                (ia32e-la-to-pa-pml4-table-entry-validp
                 lin-addr pml4-base-addr wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)
                (equal pml4-entry-addr
                       (pml4-table-entry-addr lin-addr pml4-base-addr))
                (equal pml4-entry (rm-low-64 pml4-entry-addr x86))
                ;; For ia32e-la-to-pa-page-dir-ptr-table:
                (equal ptr-table-base-addr
                       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
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

                ;; (pairwise-disjoint-p
                ;;  (list (addr-range 8 pml4-entry-addr)
                ;;        (addr-range 8 ptr-table-entry-addr)
                ;;        (addr-range 8 page-directory-entry-addr)
                ;;        (addr-range 8 page-table-entry-addr)))
                (pairwise-disjoint-p
                 (translation-governing-addresses-for-pml4-table
                  lin-addr pml4-base-addr x86))

                (physical-address-p pml4-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 pml4-base-addr) 0)
                (x86p x86))

           (ia32e-la-to-pa-pml4-table-entry-validp
            lin-addr pml4-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
            (mv-nth
             2
             (ia32e-la-to-pa-page-dir-ptr-table
              lin-addr ptr-table-base-addr wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))

  :do-not '(preprocess)
  :in-theory (e/d
              (page-dir-ptr-table-components-equal-rm-low-64-of-page-dir-ptr-table-entry-addr-via-page-dir-ptr-table-4K-pages
               page-directory-components-equal-rm-low-64-of-page-directory-entry-addr-via-page-dir-ptr-table-4K-pages
               page-table-components-equal-rm-low-64-of-page-table-entry-addr-via-page-dir-ptr-table-4K-pages
               logtail-12-of-reading-page-dir-ptr-table-entry-from-state-after-page-dir-ptr-table-given-pml4-table-validp-4K-pages
               page-size-from-re-reading-page-dir-ptr-table-entry-given-pml4-entry-validp-4K-pages
               page-size-from-reading-page-directory-entry-from-state-after-page-dir-ptr-table-given-pml4-entry-validp-4K-pages)
              (ia32e-la-to-pa-pml4-table-entry-validp
               not
               mv-nth-2-no-error-ia32e-la-to-pa-pml4-table
               mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-4K-or-2M-pages
               mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
               acl2::mv-nth-cons-meta
               subset-p-two-addr-ranges
               disjoint-p-two-addr-ranges-thm-3
               disjoint-p-two-addr-ranges-thm-2
               disjoint-p-two-addr-ranges-thm-1
               disjoint-p-two-addr-ranges-thm-0
               <-preserved-by-adding-<-*pseudo-page-size-in-bytes*-commuted
               <-preserved-by-adding-<-*pseudo-page-size-in-bytes*
               unsigned-byte-p
               signed-byte-p)))

(defruled logtail-12-of-reading-page-directory-entry-from-state-after-page-dir-ptr-table-given-pml4-table-validp-4K-pages
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
                 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
                (equal pml4-entry-addr
                       (pml4-table-entry-addr lin-addr pml4-base-addr))
                (equal pml4-entry (rm-low-64 pml4-entry-addr x86))
                ;; For ia32e-la-to-pa-page-dir-ptr-table:
                (equal ptr-table-base-addr
                       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
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


                ;; (pairwise-disjoint-p
                ;;  (list (addr-range 8 pml4-entry-addr)
                ;;        (addr-range 8 ptr-table-entry-addr)
                ;;        (addr-range 8 page-directory-entry-addr)
                ;;        (addr-range 8 page-table-entry-addr)))
                (pairwise-disjoint-p
                 (translation-governing-addresses-for-pml4-table
                  lin-addr pml4-base-addr x86))


                (physical-address-p pml4-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 pml4-base-addr) 0)
                (x86p x86))
           (equal (logtail 12
                           (rm-low-64
                            page-directory-entry-addr
                            (mv-nth 2
                                    (ia32e-la-to-pa-page-dir-ptr-table
                                     lin-addr ptr-table-base-addr wp smep
                                     nxe r-w-x cpl x86))))
                  (logtail 12 (rm-low-64 page-directory-entry-addr x86))))
  :do-not '(preprocess)
  :in-theory (e/d* (logtail-12-of-reading-page-directory-entry-from-state-after-page-directory-given-page-dir-ptr-table-validp
                    rm-low-64-and-page-dir-ptr-table-4K-pages
                    rm-low-64-and-page-directory-4K-pages
                    page-size-from-re-reading-page-dir-ptr-table-entry-given-pml4-entry-validp-4K-pages
                    page-size-from-reading-page-directory-entry-from-state-after-page-dir-ptr-table-given-pml4-entry-validp-4K-pages
                    ia32e-la-to-pa-page-dir-ptr-table-entry-validp)
                   (mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages
                    subset-p-two-addr-ranges
                    disjoint-p-two-addr-ranges-thm-3
                    disjoint-p-two-addr-ranges-thm-2
                    disjoint-p-two-addr-ranges-thm-1
                    disjoint-p-two-addr-ranges-thm-0
                    <-preserved-by-adding-<-*pseudo-page-size-in-bytes*-commuted
                    <-preserved-by-adding-<-*pseudo-page-size-in-bytes*
                    not
                    unsigned-byte-p
                    signed-byte-p)))

(defrule two-page-table-walks-ia32e-la-to-pa-pml4-table-4K-pages-same-addresses

  ;; Key lemmas:

  ;; mv-nth-2-no-error-ia32e-la-to-pa-pml4-table
  ;; re-read-entry-still-pml4-table-valid-page-dir-ptr-table-4K-pages
  ;; reading-entry-with-accessed-bit-set-ia32e-la-to-pa-pml4-table-4K-pages
  ;; mv-nth-1-no-error-ia32e-la-to-pa-pml4-table
  ;; pml4-table-entry-validp-to-page-dir-ptr-entry-validp
  ;; two-page-table-walks-ia32e-la-to-pa-dir-ptr-table-4K-pages-same-addresses

  ;; Note that for this theorem, we also need:
  ;; page-size-from-re-reading-page-dir-ptr-table-entry-given-pml4-entry-validp-4K-pages
  ;; page-size-from-reading-page-directory-entry-from-state-after-page-dir-ptr-table-given-pml4-entry-validp-4K-pages
  ;; logtail-12-of-reading-page-dir-ptr-table-entry-from-state-after-page-dir-ptr-table-given-pml4-table-validp-4K-pages
  ;; logtail-12-of-reading-page-directory-entry-from-state-after-page-dir-ptr-table-given-pml4-table-validp-4K-pages

  ;; I discovered that I needed the additional lemmas by:
  ;; (acl2::why reading-entry-with-accessed-bit-set-ia32e-la-to-pa-pml4-table-4K-pages)

  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
                 lin-addr pml4-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)
                (ia32e-la-to-pa-pml4-table-entry-validp
                 lin-addr pml4-base-addr wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)
                (equal pml4-entry-addr
                       (pml4-table-entry-addr lin-addr pml4-base-addr))
                (equal pml4-entry (rm-low-64 pml4-entry-addr x86))
                ;; For ia32e-la-to-pa-page-dir-ptr-table:
                (equal ptr-table-base-addr
                       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
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

                ;; (pairwise-disjoint-p
                ;;  (list (addr-range 8 pml4-entry-addr)
                ;;        (addr-range 8 ptr-table-entry-addr)
                ;;        (addr-range 8 page-directory-entry-addr)
                ;;        (addr-range 8 page-table-entry-addr)))
                (pairwise-disjoint-p
                 (translation-governing-addresses-for-pml4-table
                  lin-addr pml4-base-addr x86))

                (physical-address-p pml4-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 pml4-base-addr) 0)
                (x86p x86))
           (equal
            (mv-nth
             1
             (ia32e-la-to-pa-pml4-table
              lin-addr pml4-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
              (mv-nth
               2
               (ia32e-la-to-pa-pml4-table
                lin-addr pml4-base-addr wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
            (mv-nth
             1
             (ia32e-la-to-pa-pml4-table
              lin-addr pml4-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86))))
  :do-not '(preprocess)
  :in-theory (e/d
              (pml4-table-components-equal-rm-low-64-of-pml4-entry-addr-via-pml4-table-4K-pages
               page-dir-ptr-table-components-equal-rm-low-64-of-page-dir-ptr-table-entry-addr-via-page-dir-ptr-table-4K-pages
               page-directory-components-equal-rm-low-64-of-page-directory-entry-addr-via-page-dir-ptr-table-4K-pages
               page-table-components-equal-rm-low-64-of-page-table-entry-addr-via-page-dir-ptr-table-4K-pages
               re-read-entry-still-pml4-table-valid-page-dir-ptr-table-4K-pages
               page-size-from-re-reading-page-dir-ptr-table-entry-given-pml4-entry-validp-4K-pages
               page-size-from-reading-page-directory-entry-from-state-after-page-dir-ptr-table-given-pml4-entry-validp-4K-pages
               logtail-12-of-reading-page-dir-ptr-table-entry-from-state-after-page-dir-ptr-table-given-pml4-table-validp-4K-pages
               logtail-12-of-reading-page-directory-entry-from-state-after-page-dir-ptr-table-given-pml4-table-validp-4K-pages)
              (ia32e-la-to-pa-pml4-table-entry-validp
               member-p-cons
               disjoint-p-cons
               mv-nth-1-no-error-ia32e-la-to-pa-page-directory-4K-pages
               mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages
               mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-4K-or-2M-pages
               mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
               subset-p-two-addr-ranges
               disjoint-p-two-addr-ranges-thm-3
               disjoint-p-two-addr-ranges-thm-2
               disjoint-p-two-addr-ranges-thm-1
               disjoint-p-two-addr-ranges-thm-0
               <-preserved-by-adding-<-*pseudo-page-size-in-bytes*-commuted
               <-preserved-by-adding-<-*pseudo-page-size-in-bytes*
               not
               unsigned-byte-p
               signed-byte-p)))

(defrule two-page-table-walks-ia32e-la-to-pa-pml4-table-4K-pages-same-entry-different-addrs
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
                 lin-addr-1 pml4-table-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)
                (ia32e-la-to-pa-pml4-table-entry-validp
                 lin-addr-2 pml4-table-base-addr wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)
                (equal pml4-entry-addr
                       (pml4-table-entry-addr lin-addr-1 pml4-table-base-addr))
                (equal pml4-entry (rm-low-64 pml4-entry-addr x86))
                ;; For ia32e-la-to-pa-page-dir-ptr-table:
                (equal ptr-table-base-addr
                       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr-1 ptr-table-base-addr))
                (equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)
                ;; For ia32e-la-to-pa-page-directory:
                (equal page-directory-base-addr
                       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
                (equal page-directory-entry-addr
                       (page-directory-entry-addr lin-addr-1 page-directory-base-addr))
                (equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps page-directory-entry) 0)
                ;; For ia32e-la-to-pa-page-table:
                (equal page-table-base-addr
                       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
                (equal page-table-entry-addr
                       (page-table-entry-addr lin-addr-1 page-table-base-addr))

                ;; So that pml4 table entries are the same...
                (equal (part-select lin-addr-1 :low 39 :high 47)
                       (part-select lin-addr-2 :low 39 :high 47))
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

                (pairwise-disjoint-p
                 (translation-governing-addresses-for-pml4-table
                  lin-addr-1 pml4-table-base-addr x86))

                (physical-address-p pml4-table-base-addr)
                (canonical-address-p lin-addr-1)
                (canonical-address-p lin-addr-2)
                (equal (loghead 12 pml4-table-base-addr) 0)
                (x86p x86))
           (equal
            (mv-nth
             1
             (ia32e-la-to-pa-pml4-table
              lin-addr-1 pml4-table-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
              (mv-nth
               2
               (ia32e-la-to-pa-pml4-table
                lin-addr-2 pml4-table-base-addr wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
            (mv-nth
             1
             (ia32e-la-to-pa-pml4-table
              lin-addr-1 pml4-table-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86))))
  :do-not '(preprocess)
  :use ((:instance equality-of-pml4-table-entry-addr)
        (:instance equality-of-page-dir-ptr-table-entry-addr)
        (:instance equality-of-page-directory-entry-addr)
        (:instance equality-of-page-table-entry-addr))
  :in-theory (e/d
              (pml4-table-components-equal-rm-low-64-of-pml4-entry-addr-via-pml4-table-4K-pages
               page-dir-ptr-table-components-equal-rm-low-64-of-page-dir-ptr-table-entry-addr-via-page-dir-ptr-table-4K-pages
               page-directory-components-equal-rm-low-64-of-page-directory-entry-addr-via-page-dir-ptr-table-4K-pages
               page-table-components-equal-rm-low-64-of-page-table-entry-addr-via-page-dir-ptr-table-4K-pages
               re-read-entry-still-pml4-table-valid-page-dir-ptr-table-4K-pages
               page-size-from-re-reading-page-dir-ptr-table-entry-given-pml4-entry-validp-4K-pages
               page-size-from-reading-page-directory-entry-from-state-after-page-dir-ptr-table-given-pml4-entry-validp-4K-pages
               logtail-12-of-reading-page-dir-ptr-table-entry-from-state-after-page-dir-ptr-table-given-pml4-table-validp-4K-pages
               logtail-12-of-reading-page-directory-entry-from-state-after-page-dir-ptr-table-given-pml4-table-validp-4K-pages)
              (ia32e-la-to-pa-pml4-table-entry-validp
               member-p-cons
               disjoint-p-cons
               mv-nth-1-no-error-ia32e-la-to-pa-page-directory-4K-pages
               mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages
               mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-4K-or-2M-pages
               mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
               subset-p-two-addr-ranges
               disjoint-p-two-addr-ranges-thm-3
               disjoint-p-two-addr-ranges-thm-2
               disjoint-p-two-addr-ranges-thm-1
               disjoint-p-two-addr-ranges-thm-0
               <-preserved-by-adding-<-*pseudo-page-size-in-bytes*-commuted
               <-preserved-by-adding-<-*pseudo-page-size-in-bytes*
               not
               unsigned-byte-p
               signed-byte-p)))


;; ......................................................................
;; Two pml4 table walks theorem --- different entries:
;; ......................................................................

(defrule two-page-table-walks-ia32e-la-to-pa-pml4-table-different-entries

  ;; Key lemmas:

  ;; mv-nth-2-no-error-ia32e-la-to-pa-pml4-table
  ;; mv-nth-1-no-error-ia32e-la-to-pa-pml4-table-1G-pages-with-disjoint-wm-low-64
  ;; mv-nth-1-no-error-ia32e-la-to-pa-pml4-table-2M-pages-with-disjoint-wm-low-64
  ;; mv-nth-1-no-error-ia32e-la-to-pa-pml4-table-4K-pages-with-disjoint-wm-low-64

  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
                 lin-addr-1 pml4-base-addr-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)
                (ia32e-la-to-pa-pml4-table-entry-validp
                 lin-addr-2 pml4-base-addr-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)

                (pairwise-disjoint-p
                 (append
                  (translation-governing-addresses-for-pml4-table
                   lin-addr-2 pml4-base-addr-2 x86)
                  (translation-governing-addresses-for-pml4-table
                   lin-addr-1 pml4-base-addr-1 x86)))

                (physical-address-p pml4-base-addr-1)
                (canonical-address-p lin-addr-1)
                (equal (loghead 12 pml4-base-addr-1) 0)

                (physical-address-p pml4-base-addr-2)
                (canonical-address-p lin-addr-2)
                (equal (loghead 12 pml4-base-addr-2) 0)

                (x86p x86))
           (equal
            (mv-nth
             1
             (ia32e-la-to-pa-pml4-table
              lin-addr-1 pml4-base-addr-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
              (mv-nth
               2
               (ia32e-la-to-pa-pml4-table
                lin-addr-2 pml4-base-addr-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
            (mv-nth
             1
             (ia32e-la-to-pa-pml4-table
              lin-addr-1 pml4-base-addr-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
              x86))))
  :do-not '(preprocess)
  :in-theory (e/d (ifix
                   ia32e-la-to-pa-page-directory-entry-components-equal-p
                   ia32e-la-to-pa-page-dir-ptr-table-entry-components-equal-p)
                  (ia32e-la-to-pa-pml4-table-entry-validp
                   page-dir-ptr-entry-validp-to-page-directory-entry-validp
                   mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
                   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
                   mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
                   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
                   reading-entry-with-accessed-bit-set-ia32e-la-to-pa-pml4-table-4k-pages
                   addr-range
                   member-p-cons
                   disjoint-p-cons
                   not
                   unsigned-byte-p
                   signed-byte-p)))

;; ......................................................................
;; More theorems about validity of pml4 table entries being preserved
;; when the translation-governing addresses are disjoint:
;; ......................................................................

(defrule validity-preserved-same-x86-state-disjoint-addresses-wrt-pml4-table
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
                 lin-addr-1 pml4-base-addr-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)
                (ia32e-la-to-pa-pml4-table-entry-validp
                 lin-addr-2 pml4-base-addr-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)

                (pairwise-disjoint-p
                 (append
                  (translation-governing-addresses-for-pml4-table
                   lin-addr-2 pml4-base-addr-2 x86)
                  (translation-governing-addresses-for-pml4-table
                   lin-addr-1 pml4-base-addr-1 x86)))

                (physical-address-p pml4-base-addr-1)
                (canonical-address-p lin-addr-1)
                (equal (loghead 12 pml4-base-addr-1) 0)

                (physical-address-p pml4-base-addr-2)
                (canonical-address-p lin-addr-2)
                (equal (loghead 12 pml4-base-addr-2) 0)

                (x86p x86))

           (ia32e-la-to-pa-pml4-table-entry-validp
            lin-addr-1 pml4-base-addr-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
            (mv-nth
             2
             (ia32e-la-to-pa-pml4-table
              lin-addr-2 pml4-base-addr-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
  :in-theory (e/d (ifix
                   ia32e-la-to-pa-page-directory-entry-components-equal-p
                   ia32e-la-to-pa-page-dir-ptr-table-entry-components-equal-p)
                  (ia32e-la-to-pa-pml4-table-entry-validp
                   page-dir-ptr-entry-validp-to-page-directory-entry-validp
                   mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
                   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
                   mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
                   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
                   member-p-cons
                   disjoint-p-cons
                   not
                   unsigned-byte-p
                   signed-byte-p)))

;; ......................................................................
;; Translation-Governing-Addresses-For-PML4-Table and
;; ia32e-la-to-pa-pml4-table-entry:
;; ......................................................................

;; 1G pages

(defruled logtail-12-of-reading-pml4-entry-from-state-after-page-dir-ptr-table-given-pml4-table-validp-1G-pages
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
                 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
                (equal pml4-entry-addr
                       (pml4-table-entry-addr lin-addr pml4-base-addr))
                (equal pml4-entry (rm-low-64 pml4-entry-addr x86))
                ;; For ia32e-la-to-pa-page-dir-ptr-table:
                (equal ptr-table-base-addr
                       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
                (equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  ptr-table-entry) 1)
                (pairwise-disjoint-p
                 (translation-governing-addresses-for-pml4-table
                  lin-addr pml4-base-addr x86))
                (physical-address-p pml4-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 pml4-base-addr) 0)
                (x86p x86))
           (equal
            (logtail 12
                     (rm-low-64 pml4-entry-addr
                                (mv-nth 2
                                        (ia32e-la-to-pa-page-dir-ptr-table
                                         lin-addr ptr-table-base-addr wp smep
                                         nxe r-w-x cpl x86))))
            (logtail 12
                     (rm-low-64 pml4-entry-addr x86))))
  :do-not '(preprocess)
  :in-theory (e/d (rm-low-64-and-ia32e-la-to-pa-pml4-table-1G-pages)
                  (not
                   mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
                   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
                   mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
                   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
                   unsigned-byte-p
                   signed-byte-p)))

;; 2M pages:

(defruled logtail-12-of-reading-pml4-entry-from-state-after-page-dir-ptr-table-given-pml4-table-validp-2M-pages
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
                 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
                (equal pml4-entry-addr
                       (pml4-table-entry-addr lin-addr pml4-base-addr))
                (equal pml4-entry (rm-low-64 pml4-entry-addr x86))
                ;; For ia32e-la-to-pa-page-dir-ptr-table:
                (equal ptr-table-base-addr
                       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
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

                (pairwise-disjoint-p
                 (translation-governing-addresses-for-pml4-table
                  lin-addr pml4-base-addr x86))

                (physical-address-p pml4-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 pml4-base-addr) 0)
                (x86p x86))
           (equal
            (logtail 12
                     (rm-low-64 pml4-entry-addr
                                (mv-nth 2
                                        (ia32e-la-to-pa-page-dir-ptr-table
                                         lin-addr ptr-table-base-addr wp smep
                                         nxe r-w-x cpl x86))))
            (logtail 12
                     (rm-low-64 pml4-entry-addr x86))))
  :do-not '(preprocess)
  :in-theory (e/d (rm-low-64-and-ia32e-la-to-pa-pml4-table-2M-pages)
                  (not
                   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4K-or-2M-pages
                   unsigned-byte-p
                   signed-byte-p)))

;; 4K pages:

(defruled logtail-12-of-reading-pml4-entry-from-state-after-page-dir-ptr-table-given-pml4-table-validp-4K-pages
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
                 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
                (equal pml4-entry-addr
                       (pml4-table-entry-addr lin-addr pml4-base-addr))
                (equal pml4-entry (rm-low-64 pml4-entry-addr x86))
                ;; For ia32e-la-to-pa-page-dir-ptr-table:
                (equal ptr-table-base-addr
                       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
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
                 (translation-governing-addresses-for-pml4-table
                  lin-addr pml4-base-addr x86))

                (physical-address-p pml4-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 pml4-base-addr) 0)
                (x86p x86))
           (equal
            (logtail 12
                     (rm-low-64 pml4-entry-addr
                                (mv-nth 2
                                        (ia32e-la-to-pa-page-dir-ptr-table
                                         lin-addr ptr-table-base-addr wp smep
                                         nxe r-w-x cpl x86))))
            (logtail 12
                     (rm-low-64 pml4-entry-addr x86))))

  :do-not '(preprocess)
  :in-theory (e/d (rm-low-64-and-ia32e-la-to-pa-pml4-table-4K-pages)
                  (not
                   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4K-or-2M-pages
                   unsigned-byte-p
                   signed-byte-p)))

(defrule translation-governing-addresses-for-pml4-table-and-ia32e-la-to-pa-pml4-table-pairwise-disjoint
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
                 lin-addr-2 pml4-base-addr-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)
                (pairwise-disjoint-p
                 (append
                  (translation-governing-addresses-for-pml4-table
                   lin-addr-2 pml4-base-addr-2 x86)
                  (translation-governing-addresses-for-pml4-table
                   lin-addr-1 pml4-base-addr-1 x86))))

           (equal
            (translation-governing-addresses-for-pml4-table
             lin-addr-1 pml4-base-addr-1
             (mv-nth 2
                     (ia32e-la-to-pa-pml4-table
                      lin-addr-2 pml4-base-addr-2
                      wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)))
            (translation-governing-addresses-for-pml4-table
             lin-addr-1 pml4-base-addr-1 x86)))

  :in-theory (e/d
              ()
              (ia32e-la-to-pa-pml4-table-entry-validp
               addr-range-1
               mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
               mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
               member-p-cons
               disjoint-p-cons
               not
               unsigned-byte-p
               signed-byte-p)))

;; 1G pages:

(defrule translation-governing-addresses-for-pml4-table-and-ia32e-la-to-pa-pml4-table-same-addr-1G-pages
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
                 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
                (equal pml4-entry-addr
                       (pml4-table-entry-addr lin-addr pml4-base-addr))
                (equal pml4-entry (rm-low-64 pml4-entry-addr x86))
                (equal ptr-table-base-addr
                       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
                (equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  ptr-table-entry) 1)
                (pairwise-disjoint-p
                 (translation-governing-addresses-for-pml4-table
                  lin-addr pml4-base-addr x86))

                (physical-address-p pml4-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 pml4-base-addr) 0)
                (x86p x86))
           (equal
            (translation-governing-addresses-for-pml4-table
             lin-addr pml4-base-addr
             (mv-nth 2
                     (ia32e-la-to-pa-pml4-table
                      lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)))
            (translation-governing-addresses-for-pml4-table
             lin-addr pml4-base-addr x86)))
  :use ((:instance pml4-table-entry-validp-to-page-dir-ptr-entry-validp)
        (:instance page-size-from-re-reading-page-dir-ptr-table-entry-given-pml4-entry-validp-1G-pages))
  :in-theory (e/d
              (logtail-12-of-reading-pml4-entry-from-state-after-page-dir-ptr-table-given-pml4-table-validp-1G-pages)
              (pml4-table-entry-validp-to-page-dir-ptr-entry-validp
               ia32e-la-to-pa-pml4-table-entry-validp
               translation-governing-addresses-for-page-dir-ptr-table
               mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-1g-pages
               mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
               addr-range-1
               member-p-cons
               disjoint-p-cons
               not
               unsigned-byte-p
               signed-byte-p)))

(defrule translation-governing-addresses-for-pml4-table-and-ia32e-la-to-pa-pml4-table-same-addr-2M-pages
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
                 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
                (equal pml4-entry-addr
                       (pml4-table-entry-addr lin-addr pml4-base-addr))
                (equal pml4-entry (rm-low-64 pml4-entry-addr x86))
                ;; For ia32e-la-to-pa-page-dir-ptr-table:
                (equal ptr-table-base-addr
                       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
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

                (pairwise-disjoint-p
                 (translation-governing-addresses-for-pml4-table
                  lin-addr pml4-base-addr x86))

                (physical-address-p pml4-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 pml4-base-addr) 0)
                (x86p x86))
           (equal
            (translation-governing-addresses-for-pml4-table
             lin-addr pml4-base-addr
             (mv-nth 2
                     (ia32e-la-to-pa-pml4-table
                      lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)))
            (translation-governing-addresses-for-pml4-table
             lin-addr pml4-base-addr x86)))
  :use ((:instance pml4-table-entry-validp-to-page-dir-ptr-entry-validp)
        (:instance page-size-from-re-reading-page-dir-ptr-table-entry-given-pml4-entry-validp-2M-pages)
        (:instance page-size-from-reading-page-directory-entry-from-state-after-page-dir-ptr-table-given-pml4-entry-validp-2M-pages))
  :in-theory (e/d
              (logtail-12-of-reading-page-dir-ptr-table-entry-from-state-after-page-dir-ptr-table-given-pml4-table-validp-2M-pages)
              (pml4-table-entry-validp-to-page-dir-ptr-entry-validp
               ia32e-la-to-pa-pml4-table-entry-validp
               translation-governing-addresses-for-page-dir-ptr-table
               mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-1g-pages
               mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
               addr-range-1
               member-p-cons
               disjoint-p-cons
               not
               unsigned-byte-p
               signed-byte-p)))

(defrule translation-governing-addresses-for-pml4-table-and-ia32e-la-to-pa-pml4-table-same-addr-4K-pages
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
                 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
                (equal pml4-entry-addr
                       (pml4-table-entry-addr lin-addr pml4-base-addr))
                (equal pml4-entry (rm-low-64 pml4-entry-addr x86))
                ;; For ia32e-la-to-pa-page-dir-ptr-table:
                (equal ptr-table-base-addr
                       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
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
                 (translation-governing-addresses-for-pml4-table
                  lin-addr pml4-base-addr x86))

                (physical-address-p pml4-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 pml4-base-addr) 0)
                (x86p x86))
           (equal
            (translation-governing-addresses-for-pml4-table
             lin-addr pml4-base-addr
             (mv-nth 2
                     (ia32e-la-to-pa-pml4-table
                      lin-addr pml4-base-addr
                      wp smep nxe r-w-x cpl x86)))
            (translation-governing-addresses-for-pml4-table
             lin-addr pml4-base-addr x86)))
  :use ((:instance pml4-table-entry-validp-to-page-dir-ptr-entry-validp)
        (:instance page-size-from-re-reading-page-dir-ptr-table-entry-given-pml4-entry-validp-4K-pages)
        (:instance page-size-from-reading-page-directory-entry-from-state-after-page-dir-ptr-table-given-pml4-entry-validp-4K-pages))
  :in-theory (e/d
              (logtail-12-of-reading-page-dir-ptr-table-entry-from-state-after-page-dir-ptr-table-given-pml4-table-validp-4K-pages)
              (pml4-table-entry-validp-to-page-dir-ptr-entry-validp
               ia32e-la-to-pa-pml4-table-entry-validp
               translation-governing-addresses-for-page-dir-ptr-table
               mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-1g-pages
               mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
               addr-range-1
               member-p-cons
               disjoint-p-cons
               not
               unsigned-byte-p
               signed-byte-p)))

(in-theory (e/d () (ia32e-la-to-pa-pml4-table-entry-validp)))

;; ======================================================================

;; ia32e-la-to-pa:

;; ......................................................................
;; Rules about the three return values of ia32e-la-to-pa:
;; ......................................................................

(defrule mv-nth-0-no-error-ia32e-la-to-pa
  :parents (reasoning-about-page-tables)
  (implies (ia32e-la-to-pa-validp lin-addr r-w-x cpl x86)
           (equal (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x cpl x86))
                  nil))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa) (not force (force))))

(defrule mv-nth-1-no-error-ia32e-la-to-pa
  :parents (reasoning-about-page-tables)
  (implies (and (equal cr0 (n32 (ctri *cr0* x86)))
                (equal cr4 (n21 (ctri *cr4* x86)))
                (equal ia32-efer
                       (n12 (msri *ia32_efer-idx* x86)))
                (equal wp (cr0-slice :cr0-wp cr0))
                (equal smep (cr4-slice :cr4-smep cr4))
                (equal nxe
                       (ia32_efer-slice :ia32_efer-nxe ia32-efer))
                (equal cr3 (ctri *cr3* x86))
                (equal pml4-base-addr
                       (ash (cr3-slice :cr3-pdb cr3) 12)))
           (equal (mv-nth 1
                          (ia32e-la-to-pa lin-addr r-w-x cpl x86))
                  (mv-nth 1
                          (ia32e-la-to-pa-pml4-table
                           lin-addr pml4-base-addr wp smep nxe
                           r-w-x cpl x86))))

  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa) (not force (force))))

(defrule mv-nth-2-no-error-ia32e-la-to-pa
  :parents (reasoning-about-page-tables)
  (implies (and (equal cr0 (n32 (ctri *cr0* x86)))
                (equal cr4 (n21 (ctri *cr4* x86)))
                (equal ia32-efer
                       (n12 (msri *ia32_efer-idx* x86)))
                (equal wp (cr0-slice :cr0-wp cr0))
                (equal smep (cr4-slice :cr4-smep cr4))
                (equal nxe
                       (ia32_efer-slice :ia32_efer-nxe ia32-efer))
                (equal cr3 (ctri *cr3* x86))
                (equal pml4-base-addr
                       (ash (cr3-slice :cr3-pdb cr3) 12)))
           (equal (mv-nth
                   2
                   (ia32e-la-to-pa lin-addr r-w-x cpl x86))
                  (mv-nth
                   2
                   (ia32e-la-to-pa-pml4-table
                    lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86))))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa)
                  (not)))

(defrule mv-nth-0-no-error-ia32e-la-to-pa-with-disjoint-!memi
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-validp lin-addr r-w-x cpl x86)
                (pairwise-disjoint-p-aux
                 (addr-range 1 addr)
                 (translation-governing-addresses lin-addr x86)))
           (equal (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x cpl (xw :mem addr val x86)))
                  nil))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa)
                  (not
                   addr-range-1
                   unsigned-byte-p
                   signed-byte-p)))

(defrule mv-nth-0-no-error-ia32e-la-to-pa-with-disjoint-wm-low-64
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-validp lin-addr r-w-x cpl x86)
                (pairwise-disjoint-p-aux
                 (addr-range 8 addr)
                 (translation-governing-addresses lin-addr x86))
                (integerp addr))
           (equal (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x cpl (wm-low-64 addr val x86)))
                  nil))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa)
                  (not
                   addr-range-1
                   unsigned-byte-p
                   signed-byte-p)))

(defrule mv-nth-1-no-error-ia32e-la-to-pa-with-disjoint-!memi
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-validp lin-addr r-w-x cpl x86)
                (pairwise-disjoint-p-aux
                 (addr-range 1 addr)
                 (translation-governing-addresses lin-addr x86))
                (integerp addr))
           (equal (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x cpl (xw :mem addr val x86)))
                  (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x cpl x86))))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa)
                  (mv-nth-1-no-error-ia32e-la-to-pa-pml4-table
                   not
                   addr-range-1
                   unsigned-byte-p
                   signed-byte-p)))

(defrule mv-nth-1-no-error-ia32e-la-to-pa-with-disjoint-wm-low-64
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-validp lin-addr r-w-x cpl x86)
                (pairwise-disjoint-p-aux
                 (addr-range 8 addr)
                 (translation-governing-addresses lin-addr x86))
                (integerp addr))
           (equal (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x cpl (wm-low-64 addr val x86)))
                  (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x cpl x86))))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa)
                  (mv-nth-1-no-error-ia32e-la-to-pa-pml4-table
                   pairwise-disjoint-p-aux
                   not
                   addr-range-1
                   unsigned-byte-p
                   signed-byte-p)))

;; ......................................................................
;; !memi and state after data structure walk WoW theorem:
;; ......................................................................

(defrule disjoint-!memi-mv-nth-2-no-error-ia32e-la-to-pa
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-validp lin-addr r-w-x cpl x86)
                (pairwise-disjoint-p-aux
                 (addr-range 1 addr)
                 (translation-governing-addresses lin-addr x86))
                (integerp addr))
           (equal
            (mv-nth 2 (ia32e-la-to-pa lin-addr r-w-x cpl (xw :mem addr val x86)))
            (xw :mem addr val (mv-nth 2 (ia32e-la-to-pa lin-addr r-w-x cpl x86)))))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa)
                  (not
                   addr-range-1
                   mv-nth-2-no-error-ia32e-la-to-pa-pml4-table)))

;; ......................................................................
;; Reading addresses disjoint from pml4-table-entry-addr after
;; walking all the page tables:
;; ......................................................................

(defrule disjoint-memi-read-mv-nth-2-no-error-ia32e-la-to-pa
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-validp lin-addr r-w-x cpl x86)
                (pairwise-disjoint-p-aux
                 (addr-range 1 addr)
                 (translation-governing-addresses lin-addr x86)))
           (equal
            (xr :mem addr (mv-nth 2 (ia32e-la-to-pa lin-addr r-w-x cpl x86)))
            (xr :mem addr x86)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa)
                  (not
                   addr-range-1
                   mv-nth-2-no-error-ia32e-la-to-pa-pml4-table)))

(defrule disjoint-rm-low-64-read-mv-nth-2-no-error-ia32e-la-to-pa
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-validp lin-addr r-w-x cpl x86)
                (pairwise-disjoint-p-aux
                 (addr-range 8 addr)
                 (translation-governing-addresses lin-addr x86))
                (integerp addr))
           (equal
            (rm-low-64 addr (mv-nth 2 (ia32e-la-to-pa lin-addr r-w-x cpl x86)))
            (rm-low-64 addr x86)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa)
                  (not
                   mv-nth-2-no-error-ia32e-la-to-pa-pml4-table)))

(defrule disjoint-rm-low-32-read-mv-nth-2-no-error-ia32e-la-to-pa
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-validp lin-addr r-w-x cpl x86)
                (pairwise-disjoint-p-aux
                 (addr-range 4 addr)
                 (translation-governing-addresses lin-addr x86))
                (integerp addr))
           (equal
            (rm-low-32 addr (mv-nth 2 (ia32e-la-to-pa lin-addr r-w-x cpl x86)))
            (rm-low-32 addr x86)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa)
                  (not
                   mv-nth-2-no-error-ia32e-la-to-pa-pml4-table)))

;; ......................................................................
;; Theorems that state that the validity of the paging data structure
;; entries is preserved when writes are done to disjoint addresses:
;; ......................................................................

(defrule entry-with-disjoint-!memi-still-valid-ia32e-la-to-pa
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-validp lin-addr r-w-x cpl x86)
                (pairwise-disjoint-p-aux
                 (addr-range 1 addr)
                 (translation-governing-addresses lin-addr x86)))
           (ia32e-la-to-pa-validp
            lin-addr r-w-x cpl (xw :mem addr val x86)))
  :in-theory (e/d (ia32e-la-to-pa)
                  (not
                   addr-range-1
                   unsigned-byte-p
                   signed-byte-p)))

(defrule entry-with-disjoint-wm-low-64-still-valid-ia32e-la-to-pa
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-validp lin-addr r-w-x cpl x86)
                (pairwise-disjoint-p-aux
                 (addr-range 8 addr)
                 (translation-governing-addresses lin-addr x86))
                (integerp addr))
           (ia32e-la-to-pa-validp
            lin-addr r-w-x cpl (wm-low-64 addr val x86)))
  :in-theory (e/d (ia32e-la-to-pa)
                  (not
                   addr-range-1
                   unsigned-byte-p
                   signed-byte-p)))

;; ......................................................................
;; Theorems about preservation of validity of paging data structure
;; entries:
;; ......................................................................

;; 1G pages:

(defrule re-read-entry-still-valid-ia32e-la-to-pa-1G-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-validp lin-addr r-w-x-1 cpl-1 x86)
                (ia32e-la-to-pa-validp lin-addr r-w-x-2 cpl-2 x86)
                ;; For ia32e-la-to-pa-pml4-table
                (equal base-addr (ash (cr3-slice :cr3-pdb (ctri *cr3* x86)) 12))
                (equal p-entry-addr
                       (pml4-table-entry-addr lin-addr base-addr))
                (equal entry (rm-low-64 p-entry-addr x86))
                ;; For ia32e-la-to-pa-page-dir-ptr-table:
                (equal ptr-table-base-addr
                       (ash (ia32e-pml4e-slice :pml4e-pdpt entry) 12))
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
                (equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  ptr-table-entry) 1)

                (disjoint-p (addr-range 8 p-entry-addr)
                            (addr-range 8 ptr-table-entry-addr))
                (physical-address-p base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 base-addr) 0)
                (x86p x86))
           (ia32e-la-to-pa-validp lin-addr r-w-x-1 cpl-1
                                  (mv-nth 2 (ia32e-la-to-pa lin-addr r-w-x-2 cpl-2 x86))))
  :do-not '(preprocess)
  :in-theory (e/d
              (rm-low-64-and-ia32e-la-to-pa-pml4-table-1G-pages

               ;; The following theorem causes overflows.
               ;; rm-low-64-and-page-dir-ptr-table-1G-pages
               )
              (mv-nth-2-no-error-ia32e-la-to-pa-pml4-table
               not
               mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-1g-pages
               mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-1g-pages
               acl2::mv-nth-cons-meta
               unsigned-byte-p
               signed-byte-p)))

;; 2M pages:

(defrule re-read-entry-still-valid-ia32e-la-to-pa-2M-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-validp lin-addr r-w-x-1 cpl-1 x86)
                (ia32e-la-to-pa-validp lin-addr r-w-x-2 cpl-2 x86)
                ;; For ia32e-la-to-pa-pml4-table
                (equal base-addr (ash (cr3-slice :cr3-pdb (ctri *cr3* x86)) 12))
                (equal p-entry-addr
                       (pml4-table-entry-addr lin-addr base-addr))
                (equal entry (rm-low-64 p-entry-addr x86))
                ;; For ia32e-la-to-pa-page-dir-ptr-table:
                (equal ptr-table-base-addr
                       (ash (ia32e-pml4e-slice :pml4e-pdpt entry) 12))
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

                (pairwise-disjoint-p
                 (list (addr-range 8 p-entry-addr)
                       (addr-range 8 ptr-table-entry-addr)
                       (addr-range 8 page-directory-entry-addr)))
                (physical-address-p base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 base-addr) 0)
                (x86p x86))

           (ia32e-la-to-pa-validp
            lin-addr r-w-x-1 cpl-1
            (mv-nth 2 (ia32e-la-to-pa lin-addr r-w-x-2 cpl-2 x86))))
  :do-not '(preprocess)
  :in-theory (e/d ()
                  (mv-nth-2-no-error-ia32e-la-to-pa-pml4-table
                   not
                   mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
                   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
                   not
                   acl2::mv-nth-cons-meta
                   unsigned-byte-p
                   signed-byte-p)))

;; 4K pages:

(defrule re-read-entry-still-valid-ia32e-la-to-pa-4K-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-validp lin-addr r-w-x-1 cpl-1 x86)
                (ia32e-la-to-pa-validp lin-addr r-w-x-2 cpl-2 x86)
                ;; For ia32e-la-to-pa-pml4-table
                (equal base-addr (ash (cr3-slice :cr3-pdb (ctri *cr3* x86)) 12))
                (equal p-entry-addr
                       (pml4-table-entry-addr lin-addr base-addr))
                (equal entry (rm-low-64 p-entry-addr x86))
                ;; For ia32e-la-to-pa-page-dir-ptr-table:
                (equal ptr-table-base-addr
                       (ash (ia32e-pml4e-slice :pml4e-pdpt entry) 12))
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
                 (list (addr-range 8 p-entry-addr)
                       (addr-range 8 ptr-table-entry-addr)
                       (addr-range 8 page-directory-entry-addr)
                       (addr-range 8 page-table-entry-addr)))

                (physical-address-p base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 base-addr) 0)
                (x86p x86))

           (ia32e-la-to-pa-validp
            lin-addr r-w-x-1 cpl-1
            (mv-nth
             2
             (ia32e-la-to-pa lin-addr r-w-x-2 cpl-2 x86))))
  :do-not '(preprocess)
  :in-theory (e/d ()
                  (mv-nth-2-no-error-ia32e-la-to-pa-pml4-table
                   not
                   mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
                   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
                   not
                   acl2::mv-nth-cons-meta
                   unsigned-byte-p
                   signed-byte-p)))

;; ......................................................................
;; Two walks theorem --- same addresses:
;; ......................................................................

;; 1G pages:

(defrule two-page-table-walks-ia32e-la-to-pa-1G-pages-same-addresses
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-validp lin-addr r-w-x-1 cpl-1 x86)
                (ia32e-la-to-pa-validp lin-addr r-w-x-2 cpl-2 x86)
                ;; For ia32e-la-to-pa-pml4-table
                (equal base-addr (ash (cr3-slice :cr3-pdb (ctri *cr3* x86)) 12))
                (equal p-entry-addr
                       (pml4-table-entry-addr lin-addr base-addr))
                (equal entry (rm-low-64 p-entry-addr x86))
                ;; For ia32e-la-to-pa-page-dir-ptr-table:
                (equal ptr-table-base-addr
                       (ash (ia32e-pml4e-slice :pml4e-pdpt entry) 12))
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
                (equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  ptr-table-entry) 1)

                (pairwise-disjoint-p
                 (translation-governing-addresses lin-addr x86))
                (physical-address-p base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 base-addr) 0)
                (x86p x86))
           (equal
            (mv-nth 1
                    (ia32e-la-to-pa
                     lin-addr r-w-x-1 cpl-1
                     (mv-nth 2 (ia32e-la-to-pa lin-addr r-w-x-2 cpl-2 x86))))
            (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x-1 cpl-1 x86))))
  :do-not '(preprocess)
  :in-theory (e/d
              ()
              (mv-nth-2-no-error-ia32e-la-to-pa-pml4-table
               member-p-cons
               disjoint-p-cons
               not
               unsigned-byte-p
               signed-byte-p)))

(defrule two-page-table-walks-ia32e-la-to-pa-1G-pages-same-entry-different-addrs
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-validp lin-addr-1 r-w-x-1 cpl-1 x86)
                (ia32e-la-to-pa-validp lin-addr-2 r-w-x-2 cpl-2 x86)
                ;; For ia32e-la-to-pa-pml4-table
                (equal base-addr (ash (cr3-slice :cr3-pdb (ctri *cr3* x86)) 12))
                (equal p-entry-addr
                       (pml4-table-entry-addr lin-addr-1 base-addr))
                (equal entry (rm-low-64 p-entry-addr x86))
                ;; For ia32e-la-to-pa-page-dir-ptr-table:
                (equal ptr-table-base-addr
                       (ash (ia32e-pml4e-slice :pml4e-pdpt entry) 12))
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr-1 ptr-table-base-addr))
                (equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  ptr-table-entry) 1)

                (pairwise-disjoint-p
                 (translation-governing-addresses lin-addr-1 x86))
                ;; So that pml4 table entries are the same...
                (equal (part-select lin-addr-1 :low 39 :high 47)
                       (part-select lin-addr-2 :low 39 :high 47))
                ;; So that the ptr table entries are the same...
                (equal (part-select lin-addr-1 :low 30 :high 38)
                       (part-select lin-addr-2 :low 30 :high 38))
                ;; So that the physical addresses are different...
                (not (equal (part-select lin-addr-1 :low 0 :high 29)
                            (part-select lin-addr-2 :low 0 :high 29)))
                (physical-address-p base-addr)
                (canonical-address-p lin-addr-1)
                (canonical-address-p lin-addr-2)
                (equal (loghead 12 base-addr) 0)
                (x86p x86))
           (equal
            (mv-nth 1
                    (ia32e-la-to-pa
                     lin-addr-1 r-w-x-1 cpl-1
                     (mv-nth 2 (ia32e-la-to-pa lin-addr-2 r-w-x-2 cpl-2 x86))))
            (mv-nth 1 (ia32e-la-to-pa lin-addr-1 r-w-x-1 cpl-1 x86))))
  :do-not '(preprocess)
  :in-theory (e/d
              ()
              (mv-nth-2-no-error-ia32e-la-to-pa-pml4-table
               mv-nth-1-no-error-ia32e-la-to-pa-pml4-table
               member-p-cons
               disjoint-p-cons
               not
               unsigned-byte-p
               signed-byte-p)))

;; 2M pages:

(defrule two-page-table-walks-ia32e-la-to-pa-2M-pages-same-addresses
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-validp lin-addr r-w-x-1 cpl-1 x86)
                (ia32e-la-to-pa-validp lin-addr r-w-x-2 cpl-2 x86)
                ;; For ia32e-la-to-pa-pml4-table
                (equal base-addr (ash (cr3-slice :cr3-pdb (ctri *cr3* x86)) 12))
                (equal p-entry-addr
                       (pml4-table-entry-addr lin-addr base-addr))
                (equal entry (rm-low-64 p-entry-addr x86))
                ;; For ia32e-la-to-pa-page-dir-ptr-table:
                (equal ptr-table-base-addr
                       (ash (ia32e-pml4e-slice :pml4e-pdpt entry) 12))
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

                (pairwise-disjoint-p
                 (translation-governing-addresses lin-addr x86))

                (physical-address-p base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 base-addr) 0)
                (x86p x86))
           (equal
            (mv-nth
             1
             (ia32e-la-to-pa
              lin-addr r-w-x-1 cpl-1
              (mv-nth 2 (ia32e-la-to-pa lin-addr r-w-x-2 cpl-2 x86))))
            (mv-nth
             1
             (ia32e-la-to-pa lin-addr r-w-x-1 cpl-1 x86))))
  :do-not '(preprocess)
  :in-theory (e/d
              ()
              (mv-nth-2-no-error-ia32e-la-to-pa-pml4-table
               member-p-cons
               disjoint-p-cons
               not
               unsigned-byte-p
               signed-byte-p)))

(defrule two-page-table-walks-ia32e-la-to-pa-2M-pages-same-entry-different-addrs
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-validp lin-addr-1 r-w-x-1 cpl-1 x86)
                (ia32e-la-to-pa-validp lin-addr-2 r-w-x-2 cpl-2 x86)
                ;; For ia32e-la-to-pa-pml4-table
                (equal base-addr (ash (cr3-slice :cr3-pdb (ctri *cr3* x86)) 12))
                (equal p-entry-addr
                       (pml4-table-entry-addr lin-addr-1 base-addr))
                (equal entry (rm-low-64 p-entry-addr x86))
                ;; For ia32e-la-to-pa-page-dir-ptr-table:
                (equal ptr-table-base-addr
                       (ash (ia32e-pml4e-slice :pml4e-pdpt entry) 12))
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr-1 ptr-table-base-addr))
                (equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)
                ;; For ia32e-la-to-pa-page-directory:
                (equal page-directory-base-addr
                       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
                (equal page-directory-entry-addr
                       (page-directory-entry-addr lin-addr-1 page-directory-base-addr))
                (equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps page-directory-entry) 1)

                (pairwise-disjoint-p
                 (list (addr-range 8 p-entry-addr)
                       (addr-range 8 ptr-table-entry-addr)
                       (addr-range 8 page-directory-entry-addr)))
                ;; So that pml4 table entries are the same...
                (equal (part-select lin-addr-1 :low 39 :high 47)
                       (part-select lin-addr-2 :low 39 :high 47))
                ;; So that the ptr table entries are the same...
                (equal (part-select lin-addr-1 :low 30 :high 38)
                       (part-select lin-addr-2 :low 30 :high 38))
                ;; So that the page directory entries are the same...
                (equal (part-select lin-addr-1 :low 21 :high 29)
                       (part-select lin-addr-2 :low 21 :high 29))
                ;; So that the physical address is different...
                (not (equal (part-select lin-addr-1 :low 0 :high 20)
                            (part-select lin-addr-2 :low 0 :high 20)))
                (physical-address-p base-addr)
                (canonical-address-p lin-addr-1)
                (canonical-address-p lin-addr-2)
                (equal (loghead 12 base-addr) 0)
                (x86p x86))
           (equal
            (mv-nth
             1
             (ia32e-la-to-pa
              lin-addr-1 r-w-x-1 cpl-1
              (mv-nth 2 (ia32e-la-to-pa lin-addr-2 r-w-x-2 cpl-2 x86))))
            (mv-nth
             1
             (ia32e-la-to-pa lin-addr-1 r-w-x-1 cpl-1 x86))))
  :do-not '(preprocess)
  :in-theory (e/d
              ()
              (mv-nth-1-no-error-ia32e-la-to-pa-pml4-table
               mv-nth-2-no-error-ia32e-la-to-pa-pml4-table
               member-p-cons
               disjoint-p-cons
               not
               unsigned-byte-p
               signed-byte-p)))

;; 4K pages:

(defrule two-page-table-walks-ia32e-la-to-pa-4K-pages-same-addresses
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-validp lin-addr r-w-x-1 cpl-1 x86)
                (ia32e-la-to-pa-validp lin-addr r-w-x-2 cpl-2 x86)
                ;; For ia32e-la-to-pa-pml4-table
                (equal base-addr (ash (cr3-slice :cr3-pdb (ctri *cr3* x86)) 12))
                (equal p-entry-addr
                       (pml4-table-entry-addr lin-addr base-addr))
                (equal entry (rm-low-64 p-entry-addr x86))
                ;; For ia32e-la-to-pa-page-dir-ptr-table:
                (equal ptr-table-base-addr
                       (ash (ia32e-pml4e-slice :pml4e-pdpt entry) 12))
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
                (pairwise-disjoint-p
                 (translation-governing-addresses lin-addr x86))
                (physical-address-p base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 base-addr) 0)
                (x86p x86))
           (equal
            (mv-nth
             1
             (ia32e-la-to-pa lin-addr r-w-x-1 cpl-1
                             (mv-nth 2 (ia32e-la-to-pa lin-addr r-w-x-2 cpl-2 x86))))
            (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x-1 cpl-1 x86))))
  :in-theory (e/d
              ()
              (mv-nth-2-no-error-ia32e-la-to-pa-pml4-table
               member-p-cons
               disjoint-p-cons
               not
               unsigned-byte-p
               signed-byte-p)))

(defrule two-page-table-walks-ia32e-la-to-pa-4K-pages-same-entry-different-addrs
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-validp lin-addr-1 r-w-x-1 cpl-1 x86)
                (ia32e-la-to-pa-validp lin-addr-2 r-w-x-2 cpl-2 x86)
                ;; For ia32e-la-to-pa-pml4-table
                (equal base-addr (ash (cr3-slice :cr3-pdb (ctri *cr3* x86)) 12))
                (equal p-entry-addr
                       (pml4-table-entry-addr lin-addr-1 base-addr))
                (equal entry (rm-low-64 p-entry-addr x86))
                ;; For ia32e-la-to-pa-page-dir-ptr-table:
                (equal ptr-table-base-addr
                       (ash (ia32e-pml4e-slice :pml4e-pdpt entry) 12))
                (equal ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr-1 ptr-table-base-addr))
                (equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)
                ;; For ia32e-la-to-pa-page-directory:
                (equal page-directory-base-addr
                       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
                (equal page-directory-entry-addr
                       (page-directory-entry-addr lin-addr-1 page-directory-base-addr))
                (equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
                (equal (ia32e-page-tables-slice :ps page-directory-entry) 0)
                (pairwise-disjoint-p
                 (translation-governing-addresses lin-addr-1 x86))

                ;; So that pml4 table entries are the same...
                (equal (part-select lin-addr-1 :low 39 :high 47)
                       (part-select lin-addr-2 :low 39 :high 47))
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

                (physical-address-p base-addr)
                (canonical-address-p lin-addr-1)
                (canonical-address-p lin-addr-2)
                (equal (loghead 12 base-addr) 0)
                (x86p x86))
           (equal
            (mv-nth
             1
             (ia32e-la-to-pa lin-addr-1 r-w-x-1 cpl-1
                             (mv-nth 2 (ia32e-la-to-pa lin-addr-2 r-w-x-2 cpl-2 x86))))
            (mv-nth 1 (ia32e-la-to-pa lin-addr-1 r-w-x-1 cpl-1 x86))))
  :in-theory (e/d
              ()
              (mv-nth-2-no-error-ia32e-la-to-pa-pml4-table
               mv-nth-1-no-error-ia32e-la-to-pa-pml4-table
               member-p-cons
               disjoint-p-cons
               not
               unsigned-byte-p
               signed-byte-p)))

;; ......................................................................
;; Two walks theorem --- different entries
;; ......................................................................

(defrule two-page-table-walks-ia32e-la-to-pa-different-entries
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-validp lin-addr-1 r-w-x-1 cpl-1 x86)
                (ia32e-la-to-pa-validp lin-addr-2 r-w-x-2 cpl-2 x86)

                (pairwise-disjoint-p
                 (append
                  (translation-governing-addresses lin-addr-2 x86)
                  (translation-governing-addresses lin-addr-1 x86)))

                (canonical-address-p lin-addr-1)
                (canonical-address-p lin-addr-2)
                (x86p x86))
           (equal (mv-nth 1
                          (ia32e-la-to-pa lin-addr-1 r-w-x-1 cpl-1
                                          (mv-nth 2 (ia32e-la-to-pa
                                                     lin-addr-2 r-w-x-2 cpl-2 x86))))
                  (mv-nth 1
                          (ia32e-la-to-pa lin-addr-1 r-w-x-1 cpl-1 x86))))
  :do-not '(preprocess)
  :in-theory (e/d ()
                  (ia32e-la-to-pa-pml4-table-entry-validp
                   translation-governing-addresses-for-pml4-table
                   page-dir-ptr-entry-validp-to-page-directory-entry-validp
                   mv-nth-1-no-error-ia32e-la-to-pa-pml4-table
                   mv-nth-2-no-error-ia32e-la-to-pa-pml4-table
                   reading-entry-with-accessed-bit-set-ia32e-la-to-pa-pml4-table-4k-pages
                   addr-range
                   member-p-cons
                   disjoint-p-cons
                   not
                   unsigned-byte-p
                   signed-byte-p)))

;; ......................................................................
;; Validity of paging structure entries are preserved when the
;; translation-governing addresses are disjoint:
;; ......................................................................

(defrule validity-preserved-same-x86-state-disjoint-addresses-top-level-thm
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-validp lin-addr-1 r-w-x-1 cpl-1 x86)
                (ia32e-la-to-pa-validp lin-addr-2 r-w-x-2 cpl-2 x86)

                (pairwise-disjoint-p
                 (append
                  (translation-governing-addresses lin-addr-2 x86)
                  (translation-governing-addresses lin-addr-1 x86)))

                (canonical-address-p lin-addr-1)
                (canonical-address-p lin-addr-2)
                (x86p x86))

           (ia32e-la-to-pa-validp lin-addr-1 r-w-x-1 cpl-1
                                  (mv-nth 2 (ia32e-la-to-pa lin-addr-2 r-w-x-2 cpl-2 x86))))
  :in-theory (e/d
              ()
              (mv-nth-2-no-error-ia32e-la-to-pa-pml4-table
               mv-nth-1-no-error-ia32e-la-to-pa-pml4-table
               translation-governing-addresses-for-pml4-table
               member-p-cons
               disjoint-p-cons
               not
               unsigned-byte-p
               signed-byte-p)))

;; ......................................................................
;; Translation-Governing-Addresses and ia32e-la-to-pa:
;; ......................................................................

(defrule translation-governing-addresses-and-ia32e-la-to-pa-pairwise-disjoint
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-validp lin-addr-2 r-w-x-2 cpl-2 x86)
                (pairwise-disjoint-p
                 (append
                  (translation-governing-addresses lin-addr-2 x86)
                  (translation-governing-addresses lin-addr-1 x86))))

           (equal
            (translation-governing-addresses
             lin-addr-1
             (mv-nth 2
                     (ia32e-la-to-pa
                      lin-addr-2 r-w-x-2 cpl-2 x86)))
            (translation-governing-addresses lin-addr-1 x86)))

  :in-theory (e/d
              ()
              (ia32e-la-to-pa-pml4-table-entry-validp
               addr-range-1
               mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
               mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
               member-p-cons
               disjoint-p-cons
               not
               unsigned-byte-p
               signed-byte-p)))

;; ======================================================================
