;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")
(include-book "physical-memory-utils")

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))

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

(define ia32e-la-to-pa-page-table-entry-validp
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
  :guard (and (canonical-address-p lin-addr)
              (equal (loghead 12 page-table-base-addr) 0))
  :guard-hints (("Goal"
                 :in-theory (e/d (adding-7-to-shifted-bits)
                                 (unsigned-byte-p
                                  signed-byte-p
                                  member-equal
                                  not))))

  (let*
      ((page-table-entry-addr
        (page-table-entry-addr lin-addr page-table-base-addr))
       (entry (rm-low-64 page-table-entry-addr x86))
       (read-write (ia32e-page-tables-slice :r/w entry))
       (user-supervisor (ia32e-page-tables-slice :u/s entry))
       (execute-disable (ia32e-page-tables-slice :xd entry)))

    (and
     ;; 4K-aligned --- the base address is
     ;; the 40 bits wide address obtained
     ;; from the referencing PDE, shifted
     ;; left by 12.
     (equal (loghead 12 page-table-base-addr) 0)
     (equal (ia32e-page-tables-slice :p entry) 1)
     ;; The following three hyps state that the reserved
     ;; bits are unmodified.
     (equal
      (part-select entry :low
                   *physical-address-size* :high 62)
      0)
     (or
      (equal nxe 1)
      (equal (ia32e-pte-4K-page-slice :pte-xd entry) 0))
     ;; The following hyps state that access rights aren't
     ;; violated.

     (not
      (or
       ;; Read fault:
       (and (equal r-w-x :r)
            (if (< cpl 3)
                nil
              (equal user-supervisor 0)))
       ;; Write fault
       (and (equal r-w-x :w)
            (if (< cpl 3)
                (and (equal wp 1)
                     (equal read-write 0))
              (or (equal user-supervisor 0)
                  (equal read-write 0))))
       ;; Instruction fetch fault:
       (and (equal r-w-x :x)
            (if (< cpl 3)
                (if (equal nxe 0)
                    (and (equal smep 1)
                         (equal u-s-acc 1)
                         (equal user-supervisor 1))
                  (if (equal smep 0)
                      (equal execute-disable 1)
                    (or (equal execute-disable 1)
                        (and (equal u-s-acc 1)
                             (equal user-supervisor 1)))))
              (or (equal user-supervisor 0)
                  (and (equal nxe 1)
                       (equal execute-disable 1))))))))))

(define translation-governing-addresses-for-page-table
  ((lin-addr             :type (signed-byte   #.*max-linear-address-size*))
   (page-table-base-addr :type (unsigned-byte #.*physical-address-size*))
   (x86))
  :guard (and (canonical-address-p lin-addr)
              (equal (loghead 12 page-table-base-addr) 0))
  :enabled t
  :ignore-ok t

  (b* ((page-table-entry-addr
        (page-table-entry-addr lin-addr page-table-base-addr)))
      ;; 4K pages
      (list
       (addr-range 8 page-table-entry-addr))))

;; Page Directory:

(define ia32e-la-to-pa-page-directory-entry-validp
  ((lin-addr                 :type (signed-byte   #.*max-linear-address-size*))
   (page-directory-base-addr :type (unsigned-byte #.*physical-address-size*))
   (wp                       :type (unsigned-byte  1))
   (smep                     :type (unsigned-byte  1))
   (nxe                      :type (unsigned-byte  1))
   (r-w-x                    :type (member  :r :w :x))
   (cpl                      :type (unsigned-byte  2))
   (x86))
  :enabled t
  :guard (and (canonical-address-p lin-addr)
              (equal (loghead 12 page-directory-base-addr) 0))
  :guard-hints (("Goal"
                 :in-theory (e/d (adding-7-to-shifted-bits)
                                 (unsigned-byte-p
                                  signed-byte-p
                                  member-equal
                                  not))))

  (let*
      ((page-directory-entry-addr
        (page-directory-entry-addr lin-addr page-directory-base-addr))
       (entry (rm-low-64 page-directory-entry-addr x86))
       (read-write (ia32e-page-tables-slice :r/w entry))
       (user-supervisor (ia32e-page-tables-slice :u/s entry))
       (execute-disable (ia32e-page-tables-slice :xd entry))
       (page-size (ia32e-page-tables-slice :ps  entry)))

    (and
     (equal (ia32e-page-tables-slice :p entry) 1)
     (not
      (or (and (equal page-size 1)
               (not (equal (part-select entry :low 13 :high 20) 0)))
          (not (equal (part-select entry
                                   :low *physical-address-size*
                                   :high 62)
                      0))
          (and (equal nxe 0)
               (not (equal (ia32e-page-tables-slice :xd entry) 0)))))
     (not
      (or
       ;; Read fault:
       (and (equal r-w-x :r)
            (if (< cpl 3)
                nil
              (equal user-supervisor 0)))
       ;; Write fault:
       (and (equal r-w-x :w)
            (if (< cpl 3)
                (and (equal wp 1)
                     (equal read-write 0))
              (or (equal user-supervisor 0)
                  (equal read-write 0))))
       ;; Instruction fetch fault:
       (and (equal r-w-x :x)
            (if (< cpl 3)
                (and (equal nxe 1)
                     (equal execute-disable 1))
              (or (equal user-supervisor 0)
                  (and (equal nxe 1)
                       (equal execute-disable 1)))))))

     (if (equal (ia32e-page-tables-slice :ps  entry) 0)
         ;; 4K pages
         (ia32e-la-to-pa-page-table-entry-validp
          lin-addr
          (ash (ia32e-pde-pg-table-slice :pde-pt entry) 12)
          (ia32e-page-tables-slice :u/s entry)
          wp smep nxe r-w-x cpl x86)
       t))))

(define translation-governing-addresses-for-page-directory
  ((lin-addr                 :type (signed-byte   #.*max-linear-address-size*))
   (page-directory-base-addr :type (unsigned-byte #.*physical-address-size*))
   (x86))
  :guard (and (canonical-address-p lin-addr)
              (equal (loghead 12 page-directory-base-addr) 0))
  :guard-hints (("Goal" :in-theory (e/d* (canonical-address-p)
                                         (translation-governing-addresses-for-page-table
                                          ia32e-la-to-pa-page-table-entry-validp
                                          unsigned-byte-p
                                          signed-byte-p
                                          acl2::commutativity-of-logior))))
  :enabled t

  (b* (
       ;; 2M pages:
       (page-directory-entry-addr
        (page-directory-entry-addr lin-addr page-directory-base-addr))
       (page-directory-entry (rm-low-64 page-directory-entry-addr x86))

       (pde-ps? (equal (ia32e-page-tables-slice :ps page-directory-entry) 1))
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

(define ia32e-la-to-pa-page-dir-ptr-table-entry-validp
  ((lin-addr            :type (signed-byte   #.*max-linear-address-size*))
   (ptr-table-base-addr :type (unsigned-byte #.*physical-address-size*))
   (wp                  :type (unsigned-byte  1))
   (smep                :type (unsigned-byte  1))
   (nxe                 :type (unsigned-byte  1))
   (r-w-x               :type (member  :r :w :x))
   (cpl                 :type (unsigned-byte  2))
   (x86))


  :enabled t
  :guard (and (canonical-address-p lin-addr)
              (equal (loghead 12 ptr-table-base-addr) 0))
  :guard-hints (("Goal"
                 :in-theory (e/d (adding-7-to-shifted-bits)
                                 (unsigned-byte-p
                                  signed-byte-p
                                  member-equal
                                  not))))

  (let*
      ((ptr-table-entry-addr
        (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
       (entry (rm-low-64 ptr-table-entry-addr x86))
       (read-write (ia32e-page-tables-slice :r/w entry))
       (user-supervisor (ia32e-page-tables-slice :u/s entry))
       (execute-disable (ia32e-page-tables-slice :xd entry))
       (page-size (ia32e-page-tables-slice :ps  entry)))

    (and
     (equal (ia32e-page-tables-slice :p entry) 1)
     (not (and (equal page-size 1)
               (not (equal (part-select entry :low 13 :high 29) 0))))
     (not
      (or
       ;; Read fault:
       (and (equal r-w-x :r)
            (if (< cpl 3)
                nil
              (equal user-supervisor 0)))
       ;; Write fault:
       (and (equal r-w-x :w)
            (if (< cpl 3)
                (and (equal wp 1)
                     (equal read-write 0))
              (or (equal user-supervisor 0)
                  (equal read-write 0))))
       ;; Instructions fetch fault
       (and (equal r-w-x :x)
            (if (< cpl 3)
                (and (equal nxe 1)
                     (equal execute-disable 1))
              (or (equal user-supervisor 0)
                  (and (equal nxe 1)
                       (equal execute-disable 1)))))))

     (if (equal (ia32e-page-tables-slice :ps  entry) 0)
         ;; 4K or 2M pages
         (ia32e-la-to-pa-page-directory-entry-validp
          lin-addr
          (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd entry) 12)
          wp smep nxe r-w-x cpl x86)
       t))))

(define translation-governing-addresses-for-page-dir-ptr-table
  ((lin-addr                 :type (signed-byte   #.*max-linear-address-size*))
   (ptr-table-base-addr :type (unsigned-byte #.*physical-address-size*))
   (x86))
  :guard (and (canonical-address-p lin-addr)
              (equal (loghead 12 ptr-table-base-addr) 0))
  :guard-hints (("Goal" :in-theory (e/d* (canonical-address-p)
                                         (translation-governing-addresses-for-page-directory
                                          ia32e-la-to-pa-page-directory-entry-validp
                                          unsigned-byte-p
                                          signed-byte-p
                                          acl2::commutativity-of-logior))))
  :enabled t

  (b* ((page-dir-ptr-table-entry-addr
        (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
       (page-dir-ptr-table-entry (rm-low-64 page-dir-ptr-table-entry-addr x86))

       (pdpte-ps? (equal (ia32e-page-tables-slice :ps page-dir-ptr-table-entry) 1))

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

(define ia32e-la-to-pa-pml4-table-entry-validp
  ((lin-addr       :type (signed-byte   #.*max-linear-address-size*))
   (pml4-base-addr :type (unsigned-byte #.*physical-address-size*))
   (wp             :type (unsigned-byte  1))
   (smep           :type (unsigned-byte  1))
   (nxe            :type (unsigned-byte  1))
   (r-w-x          :type (member  :r :w :x))
   (cpl            :type (unsigned-byte  2))
   (x86))


  :enabled t
  :guard (and (canonical-address-p lin-addr)
              (equal (loghead 12 pml4-base-addr) 0))
  :guard-hints (("Goal"
                 :in-theory (e/d (adding-7-to-shifted-bits)
                                 (unsigned-byte-p
                                  signed-byte-p
                                  member-equal
                                  not))))

  (let*
      ((pml4-entry-addr
        (pml4-table-entry-addr lin-addr pml4-base-addr))
       (entry (rm-low-64 pml4-entry-addr x86))
       (read-write (ia32e-page-tables-slice :r/w entry))
       (user-supervisor (ia32e-page-tables-slice :u/s entry))
       (execute-disable (ia32e-page-tables-slice :xd entry))
       (page-size (ia32e-page-tables-slice :ps  entry)))

    (and
     (equal (ia32e-page-tables-slice :p entry) 1)
     (not (or (not (equal page-size 0))
              (and (equal nxe 0)
                   (not (equal execute-disable 0)))))
     (not
      (or
       ;; Read fault:
       (and (equal r-w-x :r)
            (if (< cpl 3)
                nil
              (equal user-supervisor 0)))
       ;; Write fault:
       (and (equal r-w-x :w)
            (if (< cpl 3)
                (and (equal wp 1)
                     (equal read-write 0))
              (or (equal user-supervisor 0)
                  (equal read-write 0))))
       ;; Instructions fetch fault:
       (and (equal r-w-x :x)
            (if (< cpl 3)
                (and (equal nxe 1)
                     (equal execute-disable 1))
              (or (equal user-supervisor 0)
                  (and (equal nxe 1)
                       (equal execute-disable 1)))))))

     (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
      lin-addr
      (ash (ia32e-pml4e-slice :pml4e-pdpt entry) 12)
      wp smep nxe r-w-x cpl x86))))

(define translation-governing-addresses-for-pml4-table
  ((lin-addr       :type (signed-byte   #.*max-linear-address-size*))
   (pml4-base-addr :type (unsigned-byte #.*physical-address-size*))
   (x86))

  :guard (and (canonical-address-p lin-addr)
              (equal (loghead 12 pml4-base-addr) 0))
  :guard-hints (("Goal" :in-theory (e/d* (canonical-address-p)
                                         (translation-governing-addresses-for-page-dir-ptr-table
                                          ia32e-la-to-pa-page-dir-ptr-table-entry-validp
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
  :guard (canonical-address-p lin-addr)
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
      (ia32e-la-to-pa-pml4-table-entry-validp
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

  :guard-hints (("Goal" :in-theory (e/d* (canonical-address-p)
                                         (translation-governing-addresses-for-pml4-table
                                          ia32e-la-to-pa-pml4-table-entry-validp
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

;; Rules that state when two paging entries are equal; this depends on
;; the appropriate parts of the linear address being equal.

(defthmd loghead-smaller-equality
  (implies (and (equal (loghead n x) (loghead n y))
                (natp n)
                (<= m n))
           (equal (loghead m x) (loghead m y)))
  :hints
  (("Goal"
    :in-theory (e/d* (acl2::ihsext-recursive-redefs acl2::ihsext-inductions)
                     nil))))

(defruled equality-of-page-table-entry-addr
  (implies (equal (part-select lin-addr-1 :low 12 :high 20)
                  (part-select lin-addr-2 :low 12 :high 20))
           (equal (page-table-entry-addr lin-addr-1 page-table-base-addr)
                  (page-table-entry-addr lin-addr-2 page-table-base-addr)))
  :use ((:instance loghead-smaller-equality
                   (x (logtail 12 lin-addr-1))
                   (y (logtail 12 lin-addr-2))
                   (n 40)
                   (m 9)))
  :in-theory (e/d (page-table-entry-addr)
                  (unsigned-byte-p
                   signed-byte-p)))

(defruled equality-of-page-directory-entry-addr
  (implies (equal (part-select lin-addr-1 :low 21 :high 29)
                  (part-select lin-addr-2 :low 21 :high 29))
           (equal (page-directory-entry-addr lin-addr-1 page-directory-base-addr)
                  (page-directory-entry-addr lin-addr-2 page-directory-base-addr)))
  :use ((:instance loghead-smaller-equality
                   (x (logtail 12 lin-addr-1))
                   (y (logtail 12 lin-addr-2))
                   (n 40)
                   (m 9)))
  :in-theory (e/d (page-directory-entry-addr)
                  (unsigned-byte-p
                   signed-byte-p)))

(defruled equality-of-page-dir-ptr-table-entry-addr
  (implies (equal (part-select lin-addr-1 :low 30 :high 38)
                  (part-select lin-addr-2 :low 30 :high 38))
           (equal (page-dir-ptr-table-entry-addr lin-addr-1 ptr-table-base-addr)
                  (page-dir-ptr-table-entry-addr lin-addr-2 ptr-table-base-addr)))
  :use ((:instance loghead-smaller-equality
                   (x (logtail 12 lin-addr-1))
                   (y (logtail 12 lin-addr-2))
                   (n 40)
                   (m 9)))
  :in-theory (e/d (page-dir-ptr-table-entry-addr)
                  (unsigned-byte-p
                   signed-byte-p)))

(defruled equality-of-pml4-table-entry-addr
  (implies (equal (part-select lin-addr-1 :low 39 :high 47)
                  (part-select lin-addr-2 :low 39 :high 47))
           (equal (pml4-table-entry-addr lin-addr-1 pml4-table-base-addr)
                  (pml4-table-entry-addr lin-addr-2 pml4-table-base-addr)))
  :use ((:instance loghead-smaller-equality
                   (x (logtail 12 lin-addr-1))
                   (y (logtail 12 lin-addr-2))
                   (n 40)
                   (m 9)))
  :in-theory (e/d (pml4-table-entry-addr)
                  (unsigned-byte-p
                   signed-byte-p)))

;; ======================================================================

;; Some arithmetic lemmas that should really be generalized:


;; (defthmd loghead-smaller-1
;;   ;; See basics.lisp.
;;   (implies (and (equal (loghead n x) (loghead n y))
;;                 (natp n)
;;                 (<= m n))
;;            (equal (loghead m x) (loghead m y)))
;;   :hints (("Goal" :in-theory (e/d*
;;                               (acl2::ihsext-recursive-redefs
;;                                acl2::ihsext-inductions)
;;                               ()))))

;; (defthmd logtail-bigger
;;   ;; See basics.lisp.
;;   (implies (and (equal (logtail n x) (logtail n y))
;;                 (<= n m)
;;                 (natp m)
;;                 (integerp x))
;;            (equal (logtail m x) (logtail m y)))
;;   :hints (("Goal" :in-theory (e/d*
;;                               (acl2::ihsext-recursive-redefs
;;                                acl2::ihsext-inductions)
;;                               ()))))

;; (encapsulate
;;  ()
;;  ;; I should prove thms in this encapsulate without GL... I don't want
;;  ;; the (unsigned-byte-p 64 entry) hyp around.
;;  (local (include-book "centaur/gl/gl" :dir :system))

;;  (def-gl-export logtail-n-of-set-accessed-bit
;;    :hyp (and (syntaxp (quotep n))
;;              (natp n)
;;              (<= 6 n)
;;              (<= n 64)
;;              (unsigned-byte-p 64 entry))
;;    :concl (equal (logtail n (set-accessed-bit entry))
;;                  (logtail n entry))
;;    :g-bindings `((n       (:g-number ,(gl-int 0 2 65)))
;;                  (entry   (:g-number ,(gl-int 1 2 65)))))

;;  (def-gl-export loghead-n-of-set-accessed-bit
;;    :hyp  (and (syntaxp (quotep n))
;;               (natp n)
;;               (<= n 5)
;;               (<= n 64)
;;               (unsigned-byte-p 64 entry))
;;    :concl (equal (loghead n (set-accessed-bit entry))
;;                  (loghead n entry))
;;    :g-bindings `((n       (:g-number ,(gl-int 0 2 65)))
;;                  (entry   (:g-number ,(gl-int 1 2 65)))))

;;  (def-gl-export logtail-n-of-set-dirty-bit
;;    :hyp (and (syntaxp (quotep n))
;;              (natp n)
;;              (<= 7 n)
;;              (<= n 64)
;;              (unsigned-byte-p 64 entry))
;;    :concl (equal (logtail n (set-dirty-bit entry))
;;                  (logtail n entry))
;;    :g-bindings `((n       (:g-number ,(gl-int 0 2 65)))
;;                  (entry   (:g-number ,(gl-int 1 2 65)))))

;;  (def-gl-export loghead-n-of-set-dirty-bit
;;    :hyp  (and (syntaxp (quotep n))
;;               (natp n)
;;               (<= n 5)
;;               (<= n 64)
;;               (unsigned-byte-p 64 entry))
;;    :concl (equal (loghead n (set-dirty-bit entry))
;;                  (loghead n entry))
;;    :g-bindings `((n       (:g-number ,(gl-int 0 2 65)))
;;                  (entry   (:g-number ,(gl-int 1 2 65)))))

;;  (def-gl-export logtail-n-of-set-dirty-and-accessed-bits
;;    :hyp (and (syntaxp (quotep n))
;;              (natp n)
;;              (<= 7 n)
;;              (<= n 64)
;;              (unsigned-byte-p 64 entry))
;;    :concl (equal (logtail n (set-dirty-bit (set-accessed-bit entry)))
;;                  (logtail n entry))
;;    :g-bindings `((n       (:g-number ,(gl-int 0 2 65)))
;;                  (entry   (:g-number ,(gl-int 1 2 65)))))

;;  (def-gl-export loghead-n-of-set-dirty-and-accessed-bits
;;    :hyp  (and (syntaxp (quotep n))
;;               (natp n)
;;               (<= n 5)
;;               (<= n 64)
;;               (unsigned-byte-p 64 entry))
;;    :concl (equal (loghead n (set-dirty-bit (set-accessed-bit entry)))
;;                  (loghead n entry))
;;    :g-bindings `((n       (:g-number ,(gl-int 0 2 65)))
;;                  (entry   (:g-number ,(gl-int 1 2 65))))))


;; General and for page table:

(defthm logbitp-1-of-set-accessed-bit
  (equal (logbitp 1 (set-accessed-bit entry))
         (logbitp 1 entry))
  :hints (("Goal" :in-theory (e/d* (set-accessed-bit)
                                   (ACL2::BIT->BOOL-OF-BOOL->BIT)))))

(defthm logbitp-1-of-set-dirty-bit
  (equal (logbitp 1 (set-dirty-bit entry))
         (logbitp 1 entry))
  :hints (("Goal" :in-theory (e/d* (set-dirty-bit)
                                   (ACL2::BIT->BOOL-OF-BOOL->BIT)))))

(defthm logbitp-1-of-set-dirty-and-accessed-bits
  (equal (logbitp 1 (set-dirty-bit (set-accessed-bit entry)))
         (logbitp 1 entry))
  :hints (("Goal" :in-theory (e/d* (set-accessed-bit
                                    set-dirty-bit)
                                   (ACL2::BIT->BOOL-OF-BOOL->BIT)))))

(defthm logbitp-2-of-set-accessed-bit
  (equal (logbitp 2 (set-accessed-bit entry))
         (logbitp 2 entry))
  :hints (("Goal" :in-theory (e/d* (set-accessed-bit)
                                   (ACL2::BIT->BOOL-OF-BOOL->BIT)))))

(defthm logbitp-2-of-set-dirty-bit
  (equal (logbitp 2 (set-dirty-bit entry))
         (logbitp 2 entry))
  :hints (("Goal" :in-theory (e/d* (set-dirty-bit)
                                   (ACL2::BIT->BOOL-OF-BOOL->BIT)))))

(defthm logbitp-2-of-set-dirty-and-accessed-bits
  (equal (logbitp 2 (set-dirty-bit (set-accessed-bit entry)))
         (logbitp 2 entry))
  :hints (("Goal" :in-theory (e/d* (set-accessed-bit
                                    set-dirty-bit)
                                   (ACL2::BIT->BOOL-OF-BOOL->BIT)))))

(defthm logbitp-6-of-set-accessed-bit
  (equal (logbitp 6 (set-accessed-bit entry))
         (logbitp 6 entry))
  :hints (("Goal" :in-theory (e/d* (set-accessed-bit)
                                   (ACL2::BIT->BOOL-OF-BOOL->BIT)))))

(defthm logbitp-63-of-set-accessed-bit
  (equal (logbitp 63 (set-accessed-bit entry))
         (logbitp 63 entry))
  :hints (("Goal" :in-theory (e/d* (set-accessed-bit)
                                   (ACL2::BIT->BOOL-OF-BOOL->BIT)))))

(defthm logbitp-63-of-set-dirty-bit
  (equal (logbitp 63 (set-dirty-bit entry))
         (logbitp 63 entry))
  :hints (("Goal" :in-theory (e/d* (set-dirty-bit)
                                   (ACL2::BIT->BOOL-OF-BOOL->BIT)))))

(defthm logbitp-63-of-set-dirty-and-accessed-bits
  (equal (logbitp 63 (set-dirty-bit (set-accessed-bit entry)))
         (logbitp 63 entry))
  :hints (("Goal" :in-theory (e/d* (set-accessed-bit
                                    set-dirty-bit)
                                   (ACL2::BIT->BOOL-OF-BOOL->BIT)))))

(defthm logtail-12-of-set-accessed-bit
  (equal (logtail 12 (set-accessed-bit entry))
         (logtail 12 entry))
  :hints (("Goal" :in-theory (e/d* (set-accessed-bit) ()))))

(defthm logtail-12-of-set-dirty-bit
  (equal (logtail 12 (set-dirty-bit entry))
         (logtail 12 entry))
  :hints (("Goal" :in-theory (e/d* (set-dirty-bit) ()))))

(defthm logtail-12-of-set-dirty-and-accessed-bits
  (equal (logtail 12 (set-dirty-bit (set-accessed-bit entry)))
         (logtail 12 entry))
  :hints (("Goal" :in-theory (e/d* (set-accessed-bit
                                    set-dirty-bit)
                                   ()))))

(defthm logtail-52-of-set-accessed-bit
  (equal (logtail 52 (set-accessed-bit entry))
         (logtail 52 entry))
  :hints (("Goal" :in-theory (e/d* (set-accessed-bit) ()))))

(defthm logtail-52-of-set-dirty-bit
  (equal (logtail 52 (set-dirty-bit entry))
         (logtail 52 entry))
  :hints (("Goal" :in-theory (e/d* (set-dirty-bit) ()))))

(defthm logtail-52-of-set-dirty-and-accessed-bits
  (equal (logtail 52 (set-dirty-bit (set-accessed-bit entry)))
         (logtail 52 entry))
  :hints (("Goal" :in-theory (e/d* (set-accessed-bit
                                    set-dirty-bit)
                                   ()))))

(defthm loghead-1-of-set-accessed-bit
  (equal (loghead 1 (set-accessed-bit entry))
         (loghead 1 entry))
  :hints (("Goal" :in-theory (e/d* (set-accessed-bit) ()))))

(defthm loghead-1-of-set-dirty-bit
  (equal (loghead 1 (set-dirty-bit entry))
         (loghead 1 entry))
  :hints (("Goal" :in-theory (e/d* (set-dirty-bit) ()))))

(defthm loghead-1-of-set-dirty-and-accessed-bits
  (equal (loghead 1 (set-dirty-bit (set-accessed-bit entry)))
         (loghead 1 entry))
  :hints (("Goal" :in-theory (e/d* (set-accessed-bit
                                    set-dirty-bit)
                                   ()))))

;; For page directory:

(defthm logtail-13-of-set-accessed-bit
  (equal (logtail 13 (set-accessed-bit entry))
         (logtail 13 entry))
  :hints (("Goal" :in-theory (e/d* (set-accessed-bit) ()))))

(defthm logtail-13-of-set-dirty-bit
  (equal (logtail 13 (set-dirty-bit entry))
         (logtail 13 entry))
  :hints (("Goal" :in-theory (e/d* (set-dirty-bit) ()))))

(defthm logtail-13-of-set-dirty-and-accessed-bits
  (equal (logtail 13 (set-dirty-bit (set-accessed-bit entry)))
         (logtail 13 entry))
  :hints (("Goal" :in-theory (e/d* (set-accessed-bit
                                    set-dirty-bit)
                                   ()))))

(defthm logtail-21-of-set-accessed-bit
  (equal (logtail 21 (set-accessed-bit entry))
         (logtail 21 entry))
  :hints (("Goal" :in-theory (e/d* (set-accessed-bit) ()))))

(defthm logtail-21-of-set-dirty-bit
  (equal (logtail 21 (set-dirty-bit entry))
         (logtail 21 entry))
  :hints (("Goal" :in-theory (e/d* (set-dirty-bit) ()))))

(defthm logtail-21-of-set-dirty-and-accessed-bits
  (equal (logtail 21 (set-dirty-bit (set-accessed-bit entry)))
         (logtail 21 entry))
  :hints (("Goal" :in-theory (e/d* (set-accessed-bit
                                    set-dirty-bit)
                                   ()))))

(defthm logbitp-7-of-set-accessed-bit
  (equal (logbitp 7 (set-accessed-bit entry))
         (logbitp 7 entry))
  :hints (("Goal" :in-theory (e/d* (set-accessed-bit)
                                   (ACL2::BIT->BOOL-OF-BOOL->BIT)))))

(defthm logbitp-7-of-set-dirty-bit
  (equal (logbitp 7 (set-dirty-bit entry))
         (logbitp 7 entry))
  :hints (("Goal" :in-theory (e/d* (set-dirty-bit)
                                   (ACL2::BIT->BOOL-OF-BOOL->BIT)))))

(defthm logbitp-7-of-set-dirty-and-accessed-bits
  (equal (logbitp 7 (set-dirty-bit (set-accessed-bit entry)))
         (logbitp 7 entry))
  :hints (("Goal" :in-theory (e/d* (set-accessed-bit
                                    set-dirty-bit)
                                   (ACL2::BIT->BOOL-OF-BOOL->BIT)))))

;; For page directory pointer table:

(defthm logtail-30-of-set-accessed-bit
  (equal (logtail 30 (set-accessed-bit entry))
         (logtail 30 entry))
  :hints (("Goal" :in-theory (e/d* (set-accessed-bit) ()))))

(defthm logtail-30-of-set-dirty-bit
  (equal (logtail 30 (set-dirty-bit entry))
         (logtail 30 entry))
  :hints (("Goal" :in-theory (e/d* (set-dirty-bit) ()))))

(defthm logtail-30-of-set-dirty-and-accessed-bits
  (equal (logtail 30 (set-dirty-bit (set-accessed-bit entry)))
         (logtail 30 entry))
  :hints (("Goal" :in-theory (e/d* (set-accessed-bit
                                    set-dirty-bit)
                                   ()))))

;; ======================================================================
