;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")
(include-book "../physical-memory-utils")
(include-book "gl-lemmas")

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))

;; ======================================================================

(defsection paging-basics
  :parents (reasoning-about-page-tables)

  :short "Definitions of translation-governing addresses for paging
  structure entries"

  :long "<p>WORK IN PROGRESS...</p>

<p>This doc topic will be updated in later commits...</p>"
  )

(local (xdoc::set-default-parents paging-basics))

;; ======================================================================

;; Some helper rules:

(local (in-theory (e/d* () (greater-logbitp-of-unsigned-byte-p not))))

(encapsulate
 ()

 (defrule loghead-1-bool->bit-rule
   (equal (loghead 1 (bool->bit x))
          (bool->bit x)))

 (encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defrule low-3-bits-0-add-7-preserve-bound
    (implies (and (equal (loghead 3 x) 0)
                  (< x *mem-size-in-bytes*)
                  (integerp x))
             (< (+ 7 x) *mem-size-in-bytes*))
    :in-theory (e/d* (loghead) ())))

 (defthm-usb rm-low-64-logand-logior-helper-1
   :hyp (and (n64p x)
             (syntaxp (quotep n))
             (natp n)
             (<= n 64)
             (equal m (- (1+ n))))
   :bound 64
   :concl (logior n (logand m x))
   :hints-l (("Goal" :in-theory (e/d () (force (force)))))
   :gen-type t
   :gen-linear t))

(in-theory (e/d* (low-3-bits-0-add-7-preserve-bound) ()))

;; Disabling some expensive rules:

(local
 (in-theory (e/d ()
                 (ash-monotone-2
                  <-preserved-by-adding-<-*pseudo-page-size-in-bytes*-commuted
                  <-preserved-by-adding-<-*pseudo-page-size-in-bytes*))))

;; ======================================================================

;; For each paging data structure, we define recognizers for valid
;; entries and functions to determine which addresses govern the
;; translation.

;; Page Table:

(define page-table-entry-validp
  ((lin-addr             :type (signed-byte   #.*max-linear-address-size*))
   (page-table-base-addr :type (unsigned-byte #.*physical-address-size*))
   (u-s-acc              :type (unsigned-byte  1))
   (wp                   :type (unsigned-byte  1))
   (smep                 :type (unsigned-byte  1))
   (nxe                  :type (unsigned-byte  1))
   (r-w-x                :type (member  :r :w :x))
   (cpl                  :type (unsigned-byte  2))
   (x86))

  :enabled t
  :non-executable t
  :guard (and (not (programmer-level-mode x86))
              (canonical-address-p lin-addr)
              (equal (loghead 12 page-table-base-addr) 0))
  :guard-hints (("Goal"
                 :in-theory (e/d (adding-7-to-shifted-bits)
                                 (unsigned-byte-p
                                  signed-byte-p
                                  member-equal
                                  not))))
  (and
   (not (programmer-level-mode x86))
   (canonical-address-p lin-addr)
   (physical-address-p page-table-base-addr)
   ;; 4K-aligned --- the base address is
   ;; the 40 bits wide address obtained
   ;; from the referencing PDE, shifted
   ;; left by 12.
   (equal (loghead 12 page-table-base-addr) 0)
   (b* ((page-table-entry-addr
         (page-table-entry-addr lin-addr page-table-base-addr))
        (entry (rm-low-64 page-table-entry-addr x86))
        ((mv fault-flg & &)
         (page-table-entry-no-page-fault-p
          lin-addr entry u-s-acc wp smep nxe r-w-x cpl x86)))
     (not fault-flg))))

(defrule mv-nth-0-no-error-ia32e-la-to-pa-page-table
  (implies (page-table-entry-validp
            lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl x86)
           (equal (mv-nth
                   0
                   (ia32e-la-to-pa-page-table
                    lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl x86))
                  nil))
  :in-theory (e/d (ia32e-la-to-pa-page-table)
                  (bitops::logand-with-negated-bitmask
                   unsigned-byte-p
                   signed-byte-p)))

(define translation-governing-addresses-for-page-table
  ((lin-addr             :type (signed-byte   #.*max-linear-address-size*))
   (page-table-base-addr :type (unsigned-byte #.*physical-address-size*))
   (x86))
  :guard (and (not (programmer-level-mode x86))
              (canonical-address-p lin-addr)
              (equal (loghead 12 page-table-base-addr) 0))
  :enabled t
  :ignore-ok t

  (b* ((page-table-entry-addr
        (page-table-entry-addr lin-addr page-table-base-addr)))
    ;; 4K pages
    (list
     (addr-range 8 page-table-entry-addr))))

;; Page Directory:

(define page-directory-entry-validp
  ((lin-addr             :type (signed-byte   #.*max-linear-address-size*))
   (page-dir-base-addr   :type (unsigned-byte #.*physical-address-size*))
   (wp                   :type (unsigned-byte  1))
   (smep                 :type (unsigned-byte  1))
   (nxe                  :type (unsigned-byte  1))
   (r-w-x                :type (member  :r :w :x))
   (cpl                  :type (unsigned-byte  2))
   (x86))

  :enabled t
  :non-executable t
  :guard (and (not (programmer-level-mode x86))
              (canonical-address-p lin-addr)
              (equal (loghead 12 page-dir-base-addr) 0))
  :guard-hints (("Goal"
                 :in-theory (e/d (adding-7-to-shifted-bits)
                                 (unsigned-byte-p
                                  signed-byte-p
                                  member-equal
                                  not))))
  (and
   (not (programmer-level-mode x86))
   (canonical-address-p lin-addr)
   (physical-address-p page-dir-base-addr)
   ;; 4K-aligned --- the base address is
   ;; the 40 bits wide address obtained
   ;; from the referencing PDE, shifted
   ;; left by 12.
   (equal (loghead 12 page-dir-base-addr) 0)
   (b* ((entry-addr
         (page-directory-entry-addr lin-addr page-dir-base-addr))
        (entry (rm-low-64 entry-addr x86))
        ((mv fault-flg & &)
         (paging-entry-no-page-fault-p
          lin-addr entry wp smep nxe r-w-x cpl x86))
        ((when fault-flg)
         nil))
     (if (equal (page-size entry) 0)
         ;; 4K pages
         (b* ((page-table-base-addr
               (ash (ia32e-page-tables-slice :reference-addr entry) 12))
              (u-s-acc (page-user-supervisor entry)))
           (page-table-entry-validp
            lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl x86))
       t))))

(defthm x86-unchanged-if-no-error-in-paging-entry-no-page-fault-p
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

(defrule mv-nth-0-no-error-ia32e-la-to-pa-page-directory
  (implies (page-directory-entry-validp
            lin-addr base-addr wp smep nxe r-w-x cpl x86)
           (equal (mv-nth
                   0
                   (ia32e-la-to-pa-page-directory
                    lin-addr base-addr wp smep nxe r-w-x cpl x86))
                  nil))
  :in-theory (e/d (ia32e-la-to-pa-page-directory
                   page-size
                   page-user-supervisor)
                  (bitops::logand-with-negated-bitmask
                   page-table-entry-validp
                   unsigned-byte-p
                   signed-byte-p)))

(define translation-governing-addresses-for-page-directory
  ((lin-addr                 :type (signed-byte   #.*max-linear-address-size*))
   (page-directory-base-addr :type (unsigned-byte #.*physical-address-size*))
   (x86))
  :guard (and (not (programmer-level-mode x86))
              (canonical-address-p lin-addr)
              (equal (loghead 12 page-directory-base-addr) 0))
  :guard-hints (("Goal" :in-theory (e/d* (canonical-address-p)
                                         (translation-governing-addresses-for-page-table
                                          unsigned-byte-p
                                          signed-byte-p
                                          acl2::commutativity-of-logior))))
  :enabled t

  (b* (
       ;; 2M pages:
       (page-directory-entry-addr
        (page-directory-entry-addr lin-addr page-directory-base-addr))
       (page-directory-entry (rm-low-64 page-directory-entry-addr x86))

       (pde-ps? (equal (page-size page-directory-entry) 1))
       ((when pde-ps?)
        (list (addr-range 8 page-directory-entry-addr)))

       ;; 4K pages:
       (page-table-base-addr
        (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
       (page-table-addresses
        (translation-governing-addresses-for-page-table
         lin-addr page-table-base-addr x86)))

    (append
     (list (addr-range 8 page-directory-entry-addr))
     page-table-addresses)))

;; Page Directory Pointer Table:

(define page-dir-ptr-table-entry-validp
  ((lin-addr            :type (signed-byte   #.*max-linear-address-size*))
   (ptr-table-base-addr :type (unsigned-byte #.*physical-address-size*))
   (wp                  :type (unsigned-byte  1))
   (smep                :type (unsigned-byte  1))
   (nxe                 :type (unsigned-byte  1))
   (r-w-x               :type (member  :r :w :x))
   (cpl                 :type (unsigned-byte  2))
   (x86))

  :non-executable t
  :enabled t
  :guard (and (not (programmer-level-mode x86))
              (canonical-address-p lin-addr)
              (equal (loghead 12 ptr-table-base-addr) 0))
  :guard-hints (("Goal"
                 :in-theory (e/d (adding-7-to-shifted-bits)
                                 (unsigned-byte-p
                                  signed-byte-p
                                  member-equal
                                  not))))

  (and (not (programmer-level-mode x86))
       (canonical-address-p lin-addr)
       (physical-address-p ptr-table-base-addr)
       (equal (loghead 12 ptr-table-base-addr) 0)
       (b*
           ((ptr-table-entry-addr
             (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
            (entry (rm-low-64 ptr-table-entry-addr x86))
            ((mv fault-flg & &)
             (paging-entry-no-page-fault-p
              lin-addr entry wp smep nxe r-w-x cpl x86))
            ((when fault-flg)
             nil))
         (if (equal (page-size  entry) 0)
             ;; 4K or 2M pages
             (page-directory-entry-validp
              lin-addr
              (ash (ia32e-page-tables-slice :reference-addr entry) 12)
              wp smep nxe r-w-x cpl x86)
           t))))

(defrule mv-nth-0-no-error-ia32e-la-to-pa-page-dir-ptr-table
  (implies (page-dir-ptr-table-entry-validp
            lin-addr base-addr wp smep nxe r-w-x cpl x86)
           (equal (mv-nth
                   0
                   (ia32e-la-to-pa-page-dir-ptr-table
                    lin-addr base-addr wp smep nxe r-w-x cpl x86))
                  nil))
  :in-theory (e/d (ia32e-la-to-pa-page-dir-ptr-table
                   page-size)
                  (bitops::logand-with-negated-bitmask
                   page-table-entry-validp
                   unsigned-byte-p
                   signed-byte-p)))

(define translation-governing-addresses-for-page-dir-ptr-table
  ((lin-addr                 :type (signed-byte   #.*max-linear-address-size*))
   (ptr-table-base-addr :type (unsigned-byte #.*physical-address-size*))
   (x86))
  :guard (and (not (programmer-level-mode x86))
              (canonical-address-p lin-addr)
              (equal (loghead 12 ptr-table-base-addr) 0))
  :guard-hints (("Goal" :in-theory (e/d* (canonical-address-p)
                                         (translation-governing-addresses-for-page-directory
                                          unsigned-byte-p
                                          signed-byte-p
                                          acl2::commutativity-of-logior))))
  :enabled t

  (b* ((page-dir-ptr-table-entry-addr
        (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
       (page-dir-ptr-table-entry (rm-low-64 page-dir-ptr-table-entry-addr x86))

       (pdpte-ps? (equal (page-size page-dir-ptr-table-entry) 1))

       ;; 1G pages:
       ((when pdpte-ps?)
        (list
         (addr-range 8 page-dir-ptr-table-entry-addr)))

       ;; 2M or 4K pages:

       (page-directory-base-addr (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd page-dir-ptr-table-entry) 12))
       (page-directory-addresses
        (translation-governing-addresses-for-page-directory
         lin-addr page-directory-base-addr x86)))

    (append (list (addr-range 8 page-dir-ptr-table-entry-addr))
            page-directory-addresses)))


;; PML4 Table:

(define pml4-table-entry-validp
  ((lin-addr       :type (signed-byte   #.*max-linear-address-size*))
   (pml4-base-addr :type (unsigned-byte #.*physical-address-size*))
   (wp             :type (unsigned-byte  1))
   (smep           :type (unsigned-byte  1))
   (nxe            :type (unsigned-byte  1))
   (r-w-x          :type (member  :r :w :x))
   (cpl            :type (unsigned-byte  2))
   (x86))

  :non-executable t
  :enabled t
  :guard (and (not (programmer-level-mode x86))
              (canonical-address-p lin-addr)
              (equal (loghead 12 pml4-base-addr) 0))
  :guard-hints (("Goal"
                 :in-theory (e/d (adding-7-to-shifted-bits)
                                 (unsigned-byte-p
                                  signed-byte-p
                                  member-equal
                                  not))))

  (and (not (programmer-level-mode x86))
       (canonical-address-p lin-addr)
       (physical-address-p pml4-base-addr)
       (equal (loghead 12 pml4-base-addr) 0)
       (b*
           ((pml4-entry-addr
             (pml4-table-entry-addr lin-addr pml4-base-addr))
            (entry (rm-low-64 pml4-entry-addr x86))
            ((mv fault-flg & &)
             (paging-entry-no-page-fault-p
              lin-addr entry wp smep nxe r-w-x cpl x86))
            ((when fault-flg)
             nil))
         (page-dir-ptr-table-entry-validp
          lin-addr
          (ash (ia32e-page-tables-slice :reference-addr entry) 12)
          wp smep nxe r-w-x cpl x86))))

(defrule mv-nth-0-no-error-ia32e-la-to-pa-pml4-table
  (implies (pml4-table-entry-validp
            lin-addr base-addr wp smep nxe r-w-x cpl x86)
           (equal (mv-nth
                   0
                   (ia32e-la-to-pa-pml4-table
                    lin-addr base-addr wp smep nxe r-w-x cpl x86))
                  nil))
  :in-theory (e/d (ia32e-la-to-pa-pml4-table)
                  (bitops::logand-with-negated-bitmask
                   page-dir-ptr-table-entry-validp
                   page-table-entry-validp
                   unsigned-byte-p
                   signed-byte-p)))

(define translation-governing-addresses-for-pml4-table
  ((lin-addr       :type (signed-byte   #.*max-linear-address-size*))
   (pml4-base-addr :type (unsigned-byte #.*physical-address-size*))
   (x86))

  :guard (and (not (programmer-level-mode x86))
              (canonical-address-p lin-addr)
              (equal (loghead 12 pml4-base-addr) 0))
  :guard-hints (("Goal" :in-theory (e/d* (canonical-address-p)
                                         (translation-governing-addresses-for-page-dir-ptr-table
                                          unsigned-byte-p
                                          signed-byte-p
                                          acl2::commutativity-of-logior))))
  :enabled t

  (b* ((pml4-entry-addr
        (pml4-table-entry-addr lin-addr pml4-base-addr))
       (pml4-entry (rm-low-64 pml4-entry-addr x86))

       ;; Page Directory Pointer Table:
       (ptr-table-base-addr
        (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))

       (ptr-table-addresses
        (translation-governing-addresses-for-page-dir-ptr-table
         lin-addr ptr-table-base-addr x86)))

    (append
     (list (addr-range 8 pml4-entry-addr))
     ptr-table-addresses)))

;; Top-level recognizer:

(define ia32e-la-to-pa-validp
  ((lin-addr  :type (signed-byte   #.*max-linear-address-size*))
   (r-w-x     :type (member  :r :w :x))
   (cpl       :type (unsigned-byte  2))
   (x86))
  :enabled t
  :guard (and (not (xr :programmer-level-mode 0 x86))
              (canonical-address-p lin-addr))
  :guard-hints (("Goal"
                 :in-theory (e/d ()
                                 (unsigned-byte-p
                                  signed-byte-p
                                  member-equal
                                  not))))
  (b* ((cr0 (n32 (ctri *cr0* x86)))
       (cr4 (n21 (ctri *cr4* x86)))
       (ia32-efer (n12 (msri *ia32_efer-idx* x86)))
       (wp (cr0-slice :cr0-wp cr0))
       (smep (cr4-slice :cr4-smep cr4))
       (nxe (ia32_efer-slice :ia32_efer-nxe ia32-efer))
       (cr3 (ctri *cr3* x86))
       (pml4-base-addr (ash (cr3-slice :cr3-pdb cr3) 12)))
    (pml4-table-entry-validp
     lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)))

(define translation-governing-addresses
  ((lin-addr :type (signed-byte   #.*max-linear-address-size*)
             "Canonical linear address to be mapped to a physical address")
   (x86 "x86 state"))


  :long "<p>@('translation-governing-addresses') returns a
  @('true-listp') of physical addresses that govern the translation of
  a linear address @('lin-addr') to its corresponding physical address
  @('p-addr').  Addresses that can be a part of the
  output (depending on the page configurations, i.e., 4K, 2M, or 1G
  pages) include:</p>

<ol>
<li>The addresses of the relevant PML4 entry</li>

<li>The addresses of the relevant PDPT entry</li>

<li>The addresses of the relevant PD entry</li>

<li>The addresses of the relevant PT entry</li>

</ol>

<p>I intend to use this function for reasoning only, which is why I
don't have @('MBE')s to facilitate efficient execution.</p>"

  :guard (not (xr :programmer-level-mode 0 x86))
  :guard-hints (("Goal" :in-theory (e/d* (canonical-address-p)
                                         (translation-governing-addresses-for-pml4-table
                                          unsigned-byte-p
                                          signed-byte-p
                                          acl2::commutativity-of-logior))))

  :enabled t

  (b* ((cr3       (ctri *cr3* x86))
       ;; PML4 Table:
       (pml4-base-addr (ash (cr3-slice :cr3-pdb cr3) 12)))

    (translation-governing-addresses-for-pml4-table
     lin-addr pml4-base-addr x86)))

(defthm consp-translation-governing-addresses
  (consp (translation-governing-addresses lin-addr x86))
  :rule-classes (:type-prescription :rewrite))

(defthm true-list-listp-translation-governing-addresses
  (true-list-listp (translation-governing-addresses lin-addr x86))
  :rule-classes (:type-prescription :rewrite))

;; ======================================================================

;; Lemmas about set-accessed-bit, etc.:

(defthmd loghead-smaller-equality
  (implies (and (equal (loghead n x) (loghead n y))
                (natp n)
                (<= m n))
           (equal (loghead m x) (loghead m y)))
  :hints
  (("Goal"
    :in-theory (e/d* (acl2::ihsext-recursive-redefs acl2::ihsext-inductions)
                     nil))))

(defthm logbitp-n-of-set-accessed-bit
  (implies (and (syntaxp (quotep n))
                (natp n)
                (not (equal n 5)))
           (equal (logbitp n (set-accessed-bit entry))
                  (logbitp n entry)))
  :hints (("Goal" :in-theory (e/d* (set-accessed-bit not)
                                   ()))))

(defthm logbitp-n-of-set-dirty-bit
  (implies (and (syntaxp (quotep n))
                (natp n)
                (not (equal n 6)))
           (equal (logbitp n (set-dirty-bit entry))
                  (logbitp n entry)))
  :hints (("Goal" :in-theory (e/d* (set-dirty-bit not)
                                   ()))))

(defthm logbitp-n-of-set-dirty-and-accessed-bits
  (implies (and (syntaxp (quotep n))
                (natp n)
                (not (equal n 5))
                (not (equal n 6)))
           (equal (logbitp n (set-dirty-bit (set-accessed-bit entry)))
                  (logbitp n entry)))
  :hints (("Goal" :in-theory (e/d* (set-dirty-bit
                                    set-accessed-bit
                                    not)
                                   ()))))

(defthm logtail-n-of-set-accessed-bit
  (implies (and (syntaxp (quotep n))
                (natp n)
                (< 5 n))
           (equal (logtail n (set-accessed-bit entry))
                  (logtail n entry)))
  :hints ((logbitp-reasoning)
          ("Goal" :in-theory (e/d* (set-accessed-bit) ()))))

(defthm logtail-n-of-set-dirty-bit
  (implies (and (syntaxp (quotep n))
                (natp n)
                (< 6 n))
           (equal (logtail n (set-dirty-bit entry))
                  (logtail n entry)))
  :hints ((logbitp-reasoning)
          ("Goal" :in-theory (e/d* (set-dirty-bit) ()))))

(defthm logtail-n-of-set-dirty-and-accessed-bits
  (implies (and (syntaxp (quotep n))
                (natp n)
                (< 6 n))
           (equal (logtail n (set-dirty-bit (set-accessed-bit entry)))
                  (logtail n entry)))
  :hints (("Goal" :in-theory (e/d* ()
                                   (logtail-n-of-set-dirty-bit
                                    logtail-n-of-set-accessed-bit))
           :use ((:instance logtail-n-of-set-dirty-bit
                            (n n)
                            (entry (set-accessed-bit entry)))
                 (:instance logtail-n-of-set-accessed-bit
                            (n n)
                            (entry entry))))))

(defthm loghead-n-of-set-accessed-bit
  (implies (and (syntaxp (quotep n))
                (natp n)
                (<= n 5))
           (equal (loghead n (set-accessed-bit entry))
                  (loghead n entry)))
  :hints ((logbitp-reasoning)
          ("Goal" :in-theory (e/d* (set-accessed-bit) ()))))

(defthm loghead-n-of-set-dirty-bit
  (implies (and (syntaxp (quotep n))
                (natp n)
                (<= n 6))
           (equal (loghead n (set-dirty-bit entry))
                  (loghead n entry)))
  :hints ((logbitp-reasoning)
          ("Goal" :in-theory (e/d* (set-dirty-bit) ()))))

(defthm loghead-n-of-set-dirty-and-accessed-bits
  (implies (and (syntaxp (quotep n))
                (natp n)
                (<= n 5))
           (equal (loghead n (set-dirty-bit (set-accessed-bit entry)))
                  (loghead n entry)))
  :hints (("Goal" :in-theory (e/d* ()
                                   (loghead-n-of-set-dirty-bit
                                    loghead-n-of-set-accessed-bit))
           :use ((:instance loghead-n-of-set-dirty-bit
                            (n n)
                            (entry (set-accessed-bit entry)))
                 (:instance loghead-n-of-set-accessed-bit
                            (n n)
                            (entry entry))))))

(defthm accessed-bit-set-accessed-bit
  (equal (accessed-bit (set-accessed-bit e)) 1)
  :hints (("Goal" :in-theory (e/d* (accessed-bit set-accessed-bit) ()))))

(defthm accessed-bit-set-dirty-bit
  (equal (accessed-bit (set-dirty-bit e))
         (accessed-bit e))
  :hints (("Goal" :in-theory (e/d* (accessed-bit set-dirty-bit) ()))))

(defthm dirty-bit-set-dirty-bit
  (equal (dirty-bit (set-dirty-bit e)) 1)
  :hints (("Goal" :in-theory (e/d* (dirty-bit set-dirty-bit) ()))))

(defthm dirty-bit-set-accessed-bit
  (equal (dirty-bit (set-accessed-bit e))
         (dirty-bit e))
  :hints (("Goal" :in-theory (e/d* (dirty-bit set-accessed-bit) ()))))

(defthm page-size-set-accessed-bit
  (equal (page-size (set-accessed-bit e))
         (page-size e))
  :hints (("Goal" :in-theory (e/d* (page-size set-accessed-bit) ()))))

(defthm page-size-set-dirty-bit
  (equal (page-size (set-dirty-bit e))
         (page-size e))
  :hints (("Goal" :in-theory (e/d* (page-size set-dirty-bit) ()))))

(defthm page-present-set-accessed-bit
  (equal (page-present (set-accessed-bit e))
         (page-present e))
  :hints (("Goal" :in-theory (e/d* (page-present set-accessed-bit) ()))))

(defthm page-present-set-dirty-bit
  (equal (page-present (set-dirty-bit e))
         (page-present e))
  :hints (("Goal" :in-theory (e/d* (page-present set-dirty-bit) ()))))

(defthm page-read-write-set-accessed-bit
  (equal (page-read-write (set-accessed-bit e))
         (page-read-write e))
  :hints (("Goal" :in-theory (e/d* (page-read-write set-accessed-bit) ()))))

(defthm page-read-write-set-dirty-bit
  (equal (page-read-write (set-dirty-bit e))
         (page-read-write e))
  :hints (("Goal" :in-theory (e/d* (page-read-write set-dirty-bit) ()))))

(defthm page-user-supervisor-set-accessed-bit
  (equal (page-user-supervisor (set-accessed-bit e))
         (page-user-supervisor e))
  :hints (("Goal" :in-theory (e/d* (page-user-supervisor set-accessed-bit) ()))))

(defthm page-user-supervisor-set-dirty-bit
  (equal (page-user-supervisor (set-dirty-bit e))
         (page-user-supervisor e))
  :hints (("Goal" :in-theory (e/d* (page-user-supervisor set-dirty-bit) ()))))

(defthm page-execute-disable-set-accessed-bit
  (equal (page-execute-disable (set-accessed-bit e))
         (page-execute-disable e))
  :hints (("Goal" :in-theory (e/d* (page-execute-disable set-accessed-bit) ()))))

(defthm page-execute-disable-set-dirty-bit
  (equal (page-execute-disable (set-dirty-bit e))
         (page-execute-disable e))
  :hints (("Goal" :in-theory (e/d* (page-execute-disable set-dirty-bit) ()))))

;; ======================================================================
