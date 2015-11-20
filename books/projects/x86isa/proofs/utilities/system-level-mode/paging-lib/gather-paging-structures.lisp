;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")
(include-book "paging-basics")

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "centaur/bitops/signed-byte-p" :dir :system))

;; ======================================================================

;; Some misc. arithmetic lemmas:

(defthmd loghead-smaller-and-logbitp
  (implies (and (equal (loghead n e1) (loghead n e2))
                (natp n)
                (natp m)
                (< m n))
           (equal (logbitp m e1) (logbitp m e2)))
  :hints (("Goal" :in-theory (e/d* (bitops::ihsext-inductions
                                    bitops::ihsext-recursive-redefs)
                                   ()))))

(defthmd logtail-bigger
  (implies (and (equal (logtail m e1) (logtail m e2))
                (integerp e2)
                (natp n)
                (<= m n))
           (equal (logtail n e1) (logtail n e2)))
  :hints (("Goal" :in-theory (e/d* (bitops::ihsext-inductions
                                    bitops::ihsext-recursive-redefs)
                                   ()))))

(defthmd logtail-bigger-and-logbitp
  (implies (and (equal (logtail m e1) (logtail m e2))
                (integerp e2)
                (natp n)
                (<= m n))
           (equal (logbitp n e1) (logbitp n e2)))
  :hints (("Goal" :in-theory (e/d* (bitops::ihsext-inductions
                                    bitops::ihsext-recursive-redefs)
                                   ()))))

;; ======================================================================

(define qword-paddr-listp (xs)
  :enabled t
  :short "Recognizer for a list of physical addresses that can
  accommodate a quadword"
  (if (consp xs)
      (and (physical-address-p (car xs))
           (physical-address-p (+ 7 (car xs)))
           (qword-paddr-listp (cdr xs)))
    (equal xs nil))

  ///

  (defthm qword-paddr-listp-implies-true-listp
    (implies (qword-paddr-listp xs)
             (true-listp xs))
    :rule-classes :forward-chaining)

  (defthm-usb qword-paddrp-element-of-qword-paddr-listp
    :hyp (and (qword-paddr-listp xs)
              (natp m)
              (< m (len xs)))
    :bound 52
    :concl (nth m xs)
    :gen-linear t
    :gen-type t)

  (defthm nthcdr-qword-paddr-listp
    (implies (qword-paddr-listp xs)
             (qword-paddr-listp (nthcdr n xs)))
    :rule-classes (:rewrite :type-prescription)))

(define qword-paddr-list-listp (xs)
  :enabled t
  (cond ((atom xs) (eq xs nil))
        (t (and (qword-paddr-listp (car xs))
                (qword-paddr-list-listp (cdr xs)))))

  ///

  (defthm append-of-qword-paddr-list-listp
    (implies (and (qword-paddr-list-listp xs)
                  (qword-paddr-list-listp ys))
             (qword-paddr-list-listp (append xs ys))))

  (defthm qword-paddr-list-listp-implies-true-list-listp
    (implies (qword-paddr-list-listp xs)
             (true-list-listp xs))
    :rule-classes :forward-chaining))

(defthm append-of-true-list-listp
  (implies (and (true-list-listp xs)
                (true-list-listp ys))
           (true-list-listp (append xs ys))))

(define create-qword-address-list
  ((count natp)
   (addr :type (unsigned-byte #.*physical-address-size*)))

  :guard (physical-address-p (+ (ash count 3) addr))

  :prepwork
  ((local (include-book "arithmetic-5/top" :dir :system))

   (local (in-theory (e/d* (ash unsigned-byte-p) ()))))

  :enabled t


  (if (or (zp count)
          (not (physical-address-p addr))
          (not (physical-address-p (+ 7 addr))))
      nil
    (cons addr (create-qword-address-list (1- count) (+ 8 addr))))

  ///

  (defthm nat-listp-create-qword-address-list
    (implies (natp addr)
             (nat-listp (create-qword-address-list count addr)))
    :rule-classes :type-prescription)

  (defthm qword-paddr-listp-create-qword-address-list
    (implies (physical-address-p addr)
             (qword-paddr-listp (create-qword-address-list count addr))))

  (defthm create-qword-address-list-1
    (implies (and (physical-address-p (+ 7 addr))
                  (physical-address-p addr))
             (equal (create-qword-address-list 1 addr)
                    (list addr)))
    :hints (("Goal" :expand (create-qword-address-list 1 addr))))

  (defthm non-nil-create-qword-address-list
    (implies (and (posp count)
                  (physical-address-p addr)
                  (physical-address-p (+ 7 addr)))
             (create-qword-address-list count addr)))

  (defthm consp-create-qword-address-list
    (implies (and (physical-address-p addr)
                  (physical-address-p (+ 7 addr))
                  (posp count))
             (consp (create-qword-address-list count addr)))
    :rule-classes (:type-prescription :rewrite))

  (defthm car-of-create-qword-address-list
    (implies (and (posp count)
                  (physical-address-p addr)
                  (physical-address-p (+ 7 addr)))
             (equal (car (create-qword-address-list count addr))
                    addr)))

  (defthm member-p-create-qword-address-list
    (implies (and (<= addr x)
                  (< x (+ (ash count 3) addr))
                  (equal (loghead 3 addr) 0)
                  (equal (loghead 3 x) 0)
                  (physical-address-p x)
                  (physical-address-p addr))
             (equal (member-p x (create-qword-address-list count addr))
                    t))
    :hints (("Goal"
             :induct (create-qword-address-list count addr)
             :in-theory (e/d* (loghead) ())))))

(define mult-8-qword-paddr-listp (xs)
  :enabled t
  :short "Recognizer for a list of physical addresses that can
  accommodate a quadword"
  (if (consp xs)
      (and (physical-address-p (car xs))
           (physical-address-p (+ 7 (car xs)))
           ;; Multiple of 8
           (equal (loghead 3 (car xs)) 0)
           (mult-8-qword-paddr-listp (cdr xs)))
    (equal xs nil))

  ///

  (defthm mult-8-qword-paddr-listp-implies-true-listp
    (implies (mult-8-qword-paddr-listp xs)
             (true-listp xs))
    :rule-classes :forward-chaining)

  (defthm-usb qword-paddrp-element-of-mult-8-qword-paddr-listp
    :hyp (and (mult-8-qword-paddr-listp xs)
              (natp m)
              (< m (len xs)))
    :bound 52
    :concl (nth m xs)
    :gen-linear t
    :gen-type t)

  (local (include-book "std/lists/nthcdr" :dir :system))

  (defthm nthcdr-mult-8-qword-paddr-listp
    (implies (mult-8-qword-paddr-listp xs)
             (mult-8-qword-paddr-listp (nthcdr n xs)))
    :rule-classes (:rewrite :type-prescription)))

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

 (defthm multiples-of-8-and-disjointness-of-physical-addresses-1
   (implies (and (equal (loghead 3 addr-1) 0)
                 (equal (loghead 3 addr-2) 0)
                 (not (equal addr-2 addr-1))
                 (natp addr-1)
                 (natp addr-2))
            (disjoint-p (addr-range 8 addr-2)
                        (addr-range 8 addr-1))))

 (defthm multiples-of-8-and-disjointness-of-physical-addresses-2
   (implies (and (equal (loghead 3 addr-1) 0)
                 (equal (loghead 3 addr-2) 0)
                 (not (equal addr-2 addr-1))
                 (natp addr-1)
                 (natp addr-2))
            (disjoint-p (cons addr-2 nil)
                        (addr-range 8 addr-1)))))

(define mult-8-qword-paddr-list-listp (xs)
  :enabled t
  (cond ((atom xs) (eq xs nil))
        (t (and (mult-8-qword-paddr-listp (car xs))
                (mult-8-qword-paddr-list-listp (cdr xs)))))

  ///

  (defthm append-of-mult-8-qword-paddr-list-listp
    (implies (and (mult-8-qword-paddr-list-listp xs)
                  (mult-8-qword-paddr-list-listp ys))
             (mult-8-qword-paddr-list-listp (append xs ys))))

  (defthm mult-8-qword-paddr-list-listp-implies-true-list-listp
    (implies (mult-8-qword-paddr-list-listp xs)
             (true-list-listp xs))
    :rule-classes :forward-chaining)

  (defthm mult-8-qword-paddr-list-listp-and-append-1
    (implies (and (mult-8-qword-paddr-list-listp (append x y))
                  (true-listp x))
             (mult-8-qword-paddr-list-listp x))
    :rule-classes (:rewrite :forward-chaining))

  (defthm mult-8-qword-paddr-list-listp-and-append-2
    (implies (mult-8-qword-paddr-list-listp (append x y))
             (mult-8-qword-paddr-list-listp y))
    :rule-classes (:rewrite :forward-chaining))

  (defthmd member-list-p-and-mult-8-qword-paddr-list-listp
    (implies (and (mult-8-qword-paddr-list-listp addrs)
                  (member-list-p index addrs))
             (and (physical-address-p index)
                  (equal (loghead 3 index) 0)))))

(local (in-theory (e/d* () (unsigned-byte-p))))

;; ======================================================================

;; Gathering the physical addresses where paging structures are
;; located:

(define gather-pml4-table-qword-addresses (x86)
  :returns (list-of-addresses qword-paddr-listp)
  (b* ((cr3 (ctri *cr3* x86))
       (pml4-table-base-addr (ash (cr3-slice :cr3-pdb cr3) 12))
       ((when (not (physical-address-p
                    (+ (ash 512 3) pml4-table-base-addr))))
        ;; If the PML4 Table does not fit into the physical memory,
        ;; something's wrong --- likely, the paging structures haven't
        ;; been set up correctly.
        nil))
      (create-qword-address-list 512 pml4-table-base-addr))
  ///
  (std::more-returns
   (list-of-addresses true-listp)))

(define gather-qword-addresses-corresponding-to-1-entry
  ((superior-structure-paddr natp)
   x86)

  :guard (and (physical-address-p superior-structure-paddr)
              (physical-address-p (+ 7 superior-structure-paddr)))

  :returns (list-of-addresses qword-paddr-listp)

  :short "Returns a list of all the qword addresses of the inferior
  paging structure referred by a paging entry at address
  @('superior-structure-paddr')"

  (b* ((superior-structure-entry
        (rm-low-64 superior-structure-paddr x86)))
      (if (and
           (equal (ia32e-page-tables-slice :p  superior-structure-entry) 1)
           (equal (ia32e-page-tables-slice :ps superior-structure-entry) 0))
          ;; Gather the qword addresses of a paging structure only if a
          ;; superior structure points to it, i.e., the
          ;; superior-structure-entry should be present (P=1) and it
          ;; should reference an inferior structure (PS=0).
          (b* ((this-structure-base-addr
                (ash (ia32e-page-tables-slice
                      :reference-addr superior-structure-entry) 12))
               ((when (not (physical-address-p
                            (+ (ash 512 3) this-structure-base-addr))))
                ;; If the inferior table doesn't fit into the
                ;; physical memory, something's wrong likely, the
                ;; paging structures haven't been set up correctly.
                nil))
              (create-qword-address-list 512 this-structure-base-addr))
        nil))
  ///
  (std::more-returns
   (list-of-addresses true-listp)))

(define gather-qword-addresses-corresponding-to-entries
  (superior-structure-paddrs x86)

  :guard (qword-paddr-listp superior-structure-paddrs)

  :short "Returns a list of lists of qword addresses of inferior
  paging structures referred by the entries located at addresses
  @('superior-structure-paddrs') of a given superior structure"

  :returns (list-of-lists-of-addresses qword-paddr-list-listp)

  (if (endp superior-structure-paddrs)
      nil
    (b* ((superior-structure-paddr-1 (car superior-structure-paddrs))
         (superior-structure-paddrs-rest (cdr superior-structure-paddrs))
         ((when (not (physical-address-p (+ 7 superior-structure-paddr-1))))
          ;; Each of the superior-structure-paddrs should point to a qword.
          nil)
         (inferior-addresses
          (gather-qword-addresses-corresponding-to-1-entry
           superior-structure-paddr-1 x86))
         ((when (not inferior-addresses))
          (gather-qword-addresses-corresponding-to-entries
           superior-structure-paddrs-rest x86)))
        (cons
         inferior-addresses
         (gather-qword-addresses-corresponding-to-entries
          superior-structure-paddrs-rest x86))))
  ///
  (std::more-returns
   (list-of-lists-of-addresses true-list-listp)))

(define gather-qword-addresses-corresponding-to-list-of-entries
  (list-of-superior-structure-entries x86)

  :guard (qword-paddr-list-listp list-of-superior-structure-entries)

  :short "Returns a list of lists of qword addresses of inferior
  paging structures referred by the entries of a given superior
  structure"

  :returns (list-of-lists-of-addresses qword-paddr-list-listp)

  (if (endp list-of-superior-structure-entries)
      nil
    (append
     (gather-qword-addresses-corresponding-to-entries
      (car list-of-superior-structure-entries) x86)
     (gather-qword-addresses-corresponding-to-list-of-entries
      (cdr list-of-superior-structure-entries) x86)))
  ///
  (std::more-returns
   (list-of-lists-of-addresses true-list-listp)))

(define gather-all-paging-structure-qword-addresses (x86)

  :short "Returns a list of lists of qword addresses of all the active
  paging structures"

  :long "<p>We can use this function to state a common expectation
  from the supervisor-level code that initializes and manages the
  paging data structures: all the addresses of the paging structures
  \(i.e., the output of this function\) are
  @('pairwise-disjoint-p')</p>"

  :returns (list-of-lists-of-addresses qword-paddr-list-listp)

  (b* ( ;; One Page Map Level-4 (PML4) Table:
       (pml4-table-qword-addresses
        (gather-pml4-table-qword-addresses x86))
       ((when (not pml4-table-qword-addresses))
        nil)
       ;; Up to 512 Page Directory Pointer Tables (PDPT):
       (list-of-pdpt-table-qword-addresses
        (gather-qword-addresses-corresponding-to-entries
         pml4-table-qword-addresses x86))
       ;; Up to 512*512 Page Directories (PD):
       (list-of-pd-qword-addresses
        (gather-qword-addresses-corresponding-to-list-of-entries
         list-of-pdpt-table-qword-addresses x86))
       ;; Up to 512*512*512 Page Tables (PT):
       (list-of-pt-qword-addresses
        (gather-qword-addresses-corresponding-to-list-of-entries
         list-of-pd-qword-addresses x86)))
      (append
       ;; Each item below is a qword-paddr-list-listp.
       (list pml4-table-qword-addresses)
       list-of-pdpt-table-qword-addresses
       list-of-pd-qword-addresses
       list-of-pt-qword-addresses))
  ///
  (std::more-returns
   (list-of-lists-of-addresses true-list-listp)))

;; ======================================================================

;; Compare the paging structures in two x86 states:

(define xlate-equiv-entries
  ((entry-1 :type (unsigned-byte 64))
   (entry-2 :type (unsigned-byte 64)))
  :enabled t
  :long "<p>Two paging structure entries are @('xlate-equiv-entries')
  if they are equal for all bits except the accessed and dirty
  bits (bits 5 and 6, respectively).</p>"
  (and (equal (part-select entry-1 :low 0 :high 4)
              (part-select entry-2 :low 0 :high 4))
       ;; Bits 5 (accessed bit) and 6 (dirty bit) missing here.
       (equal (part-select entry-1 :low 7 :high 63)
              (part-select entry-2 :low 7 :high 63)))
  ///
  (defequiv xlate-equiv-entries)

  (defthm xlate-equiv-entries-and-set-accessed-bit
    (implies (xlate-equiv-entries e1 e2)
             (xlate-equiv-entries e1 (set-accessed-bit e2)))
    :hints (("Goal" :in-theory (e/d* (set-accessed-bit) ()))))

  (defthm xlate-equiv-entries-and-set-dirty-bit
    (implies (xlate-equiv-entries e1 e2)
             (xlate-equiv-entries e1 (set-dirty-bit e2)))
    :hints (("Goal" :in-theory (e/d* (set-dirty-bit) ()))))

  (defthmd xlate-equiv-entries-and-loghead
    (implies (and (xlate-equiv-entries e1 e2)
                  (syntaxp (quotep n))
                  (natp n)
                  (<= n 5))
             (equal (loghead n e1) (loghead n e2)))
    :hints (("Goal" :use ((:instance loghead-smaller-equality
                                     (x e1) (y e2) (n 5) (m n))))))

  (defthmd xlate-equiv-entries-and-logtail
    (implies (and (xlate-equiv-entries e1 e2)
                  (unsigned-byte-p 64 e1)
                  (unsigned-byte-p 64 e2)
                  (syntaxp (quotep n))
                  (natp n)
                  (<= 7 n))
             (equal (logtail n e1) (logtail n e2)))
    :hints (("Goal" :use ((:instance logtail-bigger
                                     (n n) (m 7)))))))

(define xlate-equiv-entries-at-qword-addresses-aux?
  (list-of-addresses-1 list-of-addresses-2 x86-1 x86-2)
  :guard (and (qword-paddr-listp list-of-addresses-1)
              (qword-paddr-listp list-of-addresses-2)
              (equal (len list-of-addresses-1)
                     (len list-of-addresses-2))
              (x86p x86-1)
              (x86p x86-2))
  :non-executable t

  (if (endp list-of-addresses-1)
      t
    (b* ((addr-1 (car list-of-addresses-1))
         (addr-2 (car list-of-addresses-2))
         ((when (not (and (physical-address-p (+ 7 addr-1))
                          (physical-address-p (+ 7 addr-2)))))
          nil)
         (qword-1 (rm-low-64 addr-1 x86-1))
         (qword-2 (rm-low-64 addr-2 x86-2))
         ((when (not (xlate-equiv-entries qword-1 qword-2)))
          nil))
        (xlate-equiv-entries-at-qword-addresses-aux?
         (cdr list-of-addresses-1) (cdr list-of-addresses-2)
         x86-1 x86-2)))
  ///

  (defthm xlate-equiv-entries-at-qword-addresses-aux?-reflexive-if-qword-paddr-listp
    (implies (qword-paddr-listp a)
             (xlate-equiv-entries-at-qword-addresses-aux? a a x x)))

  (defthm xlate-equiv-entries-at-qword-addresses-aux?-commutative-if-qword-paddr-listp
    (implies (and (equal (len a) (len b))
                  (xlate-equiv-entries-at-qword-addresses-aux? a b x y))
             (xlate-equiv-entries-at-qword-addresses-aux? b a y x)))

  (defthm xlate-equiv-entries-at-qword-addresses-aux?-transitive-if-qword-paddr-listp
    (implies (and (equal (len a) (len b))
                  (equal (len b) (len c))
                  (xlate-equiv-entries-at-qword-addresses-aux? a b x y)
                  (xlate-equiv-entries-at-qword-addresses-aux? b c y z))
             (xlate-equiv-entries-at-qword-addresses-aux? a c x z))))

(define xlate-equiv-entries-at-qword-addresses?
  (list-of-lists-of-addresses-1 list-of-lists-of-addresses-2 x86-1 x86-2)
  :guard (and (qword-paddr-list-listp list-of-lists-of-addresses-1)
              (qword-paddr-list-listp list-of-lists-of-addresses-2)
              (equal (len list-of-lists-of-addresses-1)
                     (len list-of-lists-of-addresses-2))
              (x86p x86-1)
              (x86p x86-2))
  :non-executable t

  (if (endp list-of-lists-of-addresses-1)
      t
    (b* ((list-of-addresses-1 (car list-of-lists-of-addresses-1))
         (list-of-addresses-2 (car list-of-lists-of-addresses-2))
         ((when (not (equal (len list-of-addresses-1)
                            (len list-of-addresses-2))))
          nil))
        (and (xlate-equiv-entries-at-qword-addresses-aux?
              list-of-addresses-1 list-of-addresses-2
              x86-1 x86-2)
             (xlate-equiv-entries-at-qword-addresses?
              (cdr list-of-lists-of-addresses-1)
              (cdr list-of-lists-of-addresses-2)
              x86-1 x86-2))))
  ///
  (defthm xlate-equiv-entries-at-qword-addresses?-reflexive-if-qword-paddr-list-listp
    (implies (qword-paddr-list-listp a)
             (xlate-equiv-entries-at-qword-addresses? a a x x)))

  (defthm xlate-equiv-entries-at-qword-addresses?-commutative-if-qword-paddr-list-listp
    (implies (and (equal (len a) (len b))
                  (xlate-equiv-entries-at-qword-addresses? a b x y))
             (xlate-equiv-entries-at-qword-addresses? b a y x)))

  (defthm xlate-equiv-entries-at-qword-addresses?-transitive-if-qword-paddr-list-listp
    (implies (and (equal (len a) (len b))
                  (equal (len b) (len c))
                  (xlate-equiv-entries-at-qword-addresses? a b x y)
                  (xlate-equiv-entries-at-qword-addresses? b c y z))
             (xlate-equiv-entries-at-qword-addresses? a c x z)))

  (defthm xlate-equiv-entries-at-qword-addresses?-transitive-if-qword-paddr-list-listp-equal
    (implies (and (equal a b)
                  (equal b c)
                  (xlate-equiv-entries-at-qword-addresses? a b x y)
                  (xlate-equiv-entries-at-qword-addresses? b c y z))
             (xlate-equiv-entries-at-qword-addresses? a c x z))
    :hints (("Goal" :in-theory
             (e/d*
              ()
              (xlate-equiv-entries-at-qword-addresses?-transitive-if-qword-paddr-list-listp))
             :use ((:instance xlate-equiv-entries-at-qword-addresses?-transitive-if-qword-paddr-list-listp)))))

  (defthm xlate-equiv-entries-at-qword-addresses?-implies-xlate-equiv-entries
    (implies (and (xlate-equiv-entries-at-qword-addresses?
                   addrs addrs x86-1 x86-2)
                  (member-list-p index addrs))
             (xlate-equiv-entries (rm-low-64 index x86-1)
                                  (rm-low-64 index x86-2)))
    :hints (("Goal" :in-theory (e/d* (xlate-equiv-entries-at-qword-addresses?
                                      xlate-equiv-entries-at-qword-addresses-aux?
                                      member-list-p
                                      member-p)
                                     (xlate-equiv-entries))))))

(define xlate-equiv-x86s (x86-1 x86-2)
  :non-executable t
  :enabled t
  :long "<p>Two x86 states are @('xlate-equiv-x86s') if their paging
  structures are equal, modulo the accessed and dirty bits (See @(see
  xlate-equiv-entries)). Each of the two states' paging structures
  must satisfy @(see pairwise-disjoint-p).</p>"

  (if (x86p x86-1)

      (if (x86p x86-2)

          (if (equal (ctri *cr3* x86-1) (ctri *cr3* x86-2))

              (if (mult-8-qword-paddr-list-listp (gather-all-paging-structure-qword-addresses x86-1))

                  (if (mult-8-qword-paddr-list-listp (gather-all-paging-structure-qword-addresses x86-2))

                      (if (no-duplicates-list-p (gather-all-paging-structure-qword-addresses x86-1))

                          (if (no-duplicates-list-p (gather-all-paging-structure-qword-addresses x86-2))

                              (if (equal (gather-all-paging-structure-qword-addresses x86-1)
                                         (gather-all-paging-structure-qword-addresses x86-2))

                                  (xlate-equiv-entries-at-qword-addresses?
                                   (gather-all-paging-structure-qword-addresses x86-1)
                                   (gather-all-paging-structure-qword-addresses x86-2)
                                   x86-1 x86-2)

                                nil)

                            nil)

                        (not (no-duplicates-list-p (gather-all-paging-structure-qword-addresses x86-2))))

                    nil)

                (not (mult-8-qword-paddr-list-listp (gather-all-paging-structure-qword-addresses x86-2))))

            nil)

        nil)

    (not (x86p x86-2)))

  ///

  (local
   (defthm xlate-equiv-x86s-is-transitive-helper
     (implies (and (xlate-equiv-x86s x y)
                   (xlate-equiv-x86s y z))
              (xlate-equiv-x86s x z))
     :hints (("Goal" :use
              ((:instance
                xlate-equiv-entries-at-qword-addresses?-transitive-if-qword-paddr-list-listp-equal
                (a (gather-all-paging-structure-qword-addresses x))
                (b (gather-all-paging-structure-qword-addresses y))
                (c (gather-all-paging-structure-qword-addresses z))))))))

  (defequiv xlate-equiv-x86s
    :hints (("Goal" :in-theory (e/d* () (xlate-equiv-x86s-is-transitive-helper))
             :use ((:instance xlate-equiv-x86s-is-transitive-helper))))))

;; =====================================================================
