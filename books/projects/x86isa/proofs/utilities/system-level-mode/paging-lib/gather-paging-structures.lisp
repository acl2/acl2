;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")
(include-book "paging-basics")

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "centaur/bitops/signed-byte-p" :dir :system))

;; ======================================================================

;; Some misc. lemmas:

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

(defthm member-list-p-no-duplicates-list-p-and-member-p
  (implies (and (member-list-p index addrs-2)
                (true-listp addrs-1)
                (true-list-listp addrs-2)
                (no-duplicates-list-p (append (list addrs-1) addrs-2)))
           (not (member-p index addrs-1)))
  :hints (("Goal" :in-theory (e/d* (member-p
                                    member-list-p
                                    acl2::flatten
                                    no-duplicates-p)
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
    :rule-classes (:rewrite :type-prescription))

  (defthm member-p-and-mult-8-qword-paddr-listp
    (implies (and (member-p index addrs)
                  (mult-8-qword-paddr-listp addrs))
             (and (physical-address-p index)
                  (equal (loghead 3 index) 0)))
    :rule-classes (:rewrite :forward-chaining)))

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
                        (addr-range 8 addr-1))))

 (defthm mult-8-qword-paddr-listp-and-disjoint-p
   (implies (and (member-p index addrs)
                 (mult-8-qword-paddr-listp (cons addr addrs))
                 (no-duplicates-p (cons addr addrs)))
            (disjoint-p (addr-range 8 index)
                        (addr-range 8 addr)))
   :hints (("Goal" :in-theory (e/d* () (open-addr-range))))
   :rule-classes :forward-chaining))

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

  (defthm member-list-p-and-mult-8-qword-paddr-list-listp
    (implies (and (member-list-p index addrs)
                  (mult-8-qword-paddr-list-listp addrs))
             (and (physical-address-p index)
                  (equal (loghead 3 index) 0)))
    :rule-classes (:rewrite :forward-chaining)))

(local (in-theory (e/d* () (unsigned-byte-p))))

;; ======================================================================

(define xlate-equiv-entries
  ((entry-1 :type (unsigned-byte 64))
   (entry-2 :type (unsigned-byte 64)))
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

  (defthm xlate-equiv-entries-self-set-accessed-bit
    ;; [Shilpi]: It seems to be that ACL2 never uses this rule, even
    ;; when I have a term that matches exactly --- well, maybe it's
    ;; more accurate to say that ACL2 never uses it outside of
    ;; preprocessing. Since this is a "simple" rule, I can't see it
    ;; firing even when I give a :DO-NOT '(PREPROCESS) hint. If it is
    ;; true that simple rules can't be used apart from in
    ;; preprocessing, it's sad because I often have to relieve hyps
    ;; during rewriting that match this rule exactly. The same comment
    ;; applies to the rule XLATE-EQUIV-ENTRIES-SELF-SET-DIRTY-BIT.
    (and (xlate-equiv-entries e (set-accessed-bit e))
         (xlate-equiv-entries (set-accessed-bit e) e))
    :hints (("Goal" :in-theory (e/d* (set-accessed-bit) ()))))

  (defthm xlate-equiv-entries-self-set-dirty-bit
    (and (xlate-equiv-entries e (set-dirty-bit e))
         (xlate-equiv-entries (set-dirty-bit e) e))
    :hints (("Goal" :in-theory (e/d* (set-dirty-bit) ()))))

  (defun find-xlate-equiv-entries (e1-equiv e2-equiv)
    ;; [Shilpi]: This is a quick and dirty function to bind the
    ;; free-vars of
    ;; xlate-equiv-entries-and-set-accessed-and/or-dirty-bit. It makes
    ;; the assumption that e1-equiv and e2-equiv will have one of the
    ;; following forms:

    ;; e1-equiv == e2-equiv (any form as long as they're both equal)
    ;; (set-accessed-bit (rm-low-64 index x86))
    ;; (set-dirty-bit (rm-low-64 index x86))
    ;; (set-accessed-bit (set-dirty-bit (rm-low-64 index x86)))
    ;; (set-dirty-bit (set-accessed-bit (rm-low-64 index x86)))

    ;; I haven't considered deeper nesting of set-accessed-bit and
    ;; set-dirty-bit, mainly because at this point, I'm reasonably
    ;; confident that that's a situation that won't occur.
    (cond ((equal e1-equiv e2-equiv)
           `((e1 . ,e1-equiv)
             (e2 . ,e2-equiv)))
          ((equal (first e1-equiv) 'rm-low-64)
           (cond ((equal (first e2-equiv) 'rm-low-64)
                  `((e1 . ,e1-equiv)
                    (e2 . ,e2-equiv)))
                 ((equal (first e2-equiv) 'set-accessed-bit)
                  (b* ((e2
                        (if (equal (car (second e2-equiv)) 'set-dirty-bit)
                            (second (second e2-equiv))
                          (second e2-equiv))))
                      `((e1 . ,e1-equiv)
                        (e2 . ,e2))))
                 ((equal (first e2-equiv) 'set-dirty-bit)
                  (b* ((e2
                        (if (equal (car (second e2-equiv)) 'set-accessed-bit)
                            (second (second e2-equiv))
                          (second (second e2-equiv)))))
                      `((e1 . ,e1-equiv)
                        (e2 . ,e2))))
                 (t
                  `((e1 . ,e1-equiv)
                    (e2 . ,e2-equiv)))))
          ((equal (first e2-equiv) 'rm-low-64)
           (cond ((equal (first e1-equiv) 'rm-low-64)
                  `((e2 . ,e2-equiv)
                    (e1 . ,e1-equiv)))
                 ((equal (first e1-equiv) 'set-accessed-bit)
                  (b* ((e1
                        (if (equal (car (second e1-equiv)) 'set-dirty-bit)
                            (second (second e1-equiv))
                          (second e1-equiv))))
                      `((e2 . ,e2-equiv)
                        (e1 . ,e1))))
                 ((equal (first e1-equiv) 'set-dirty-bit)
                  (b* ((e1
                        (if (equal (car (second e1-equiv)) 'set-accessed-bit)
                            (second (second e1-equiv))
                          (second e1-equiv))))
                      `((e2 . ,e2-equiv)
                        (e1 . ,e1))))
                 (t
                  `((e2 . ,e2-equiv)
                    (e1 . ,e1-equiv)))))))

  (defthm xlate-equiv-entries-and-set-accessed-and/or-dirty-bit
    (implies
     (and (bind-free (find-xlate-equiv-entries e1-equiv e2-equiv) (e1 e2))
          (xlate-equiv-entries e1 e2)
          (or (equal e1-equiv e1)
              (equal e1-equiv (set-accessed-bit e1))
              (equal e1-equiv (set-dirty-bit e1))
              (equal e1-equiv
                     (set-dirty-bit (set-accessed-bit e1))))
          (or (equal e2-equiv e2)
              (equal e2-equiv (set-accessed-bit e2))
              (equal e2-equiv (set-dirty-bit e2))
              (equal e2-equiv
                     (set-dirty-bit (set-accessed-bit e2)))))
     (xlate-equiv-entries e1-equiv e2-equiv))
    :hints (("Goal" :in-theory (e/d* (set-accessed-bit
                                      set-dirty-bit)
                                     ()))))

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
   (list-of-addresses true-listp))

  (defthm gather-pml4-table-qword-addresses-xw-fld!=ctr
    (implies (not (equal fld :ctr))
             (equal (gather-pml4-table-qword-addresses (xw fld index val x86))
                    (gather-pml4-table-qword-addresses x86)))
    :hints (("Goal"
             :cases ((equal fld :ctr))
             :in-theory (e/d* (gather-pml4-table-qword-addresses)
                              ()))))

  (defthm gather-pml4-table-qword-addresses-wm-low-64
    (equal (gather-pml4-table-qword-addresses (wm-low-64 index val x86))
           (gather-pml4-table-qword-addresses x86))
    :hints (("Goal"
             :in-theory (e/d* (gather-pml4-table-qword-addresses)
                              ()))))

  (defthm gather-pml4-table-qword-addresses-xw-fld=ctr
    (implies (and (equal fld :ctr)
                  (not (equal index *cr3*)))
             (equal (gather-pml4-table-qword-addresses (xw fld index val x86))
                    (gather-pml4-table-qword-addresses x86)))
    :hints (("Goal"
             :cases ((equal fld :ctr))
             :in-theory (e/d* (gather-pml4-table-qword-addresses)
                              ())))))

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
   (list-of-addresses true-listp))

  (defthm gather-qword-addresses-corresponding-to-1-entry-xw-fld!=mem
    (implies (not (equal fld :mem))
             (equal (gather-qword-addresses-corresponding-to-1-entry
                     n (xw fld index val x86))
                    (gather-qword-addresses-corresponding-to-1-entry n x86)))
    :hints (("Goal"
             :in-theory (e/d* (gather-qword-addresses-corresponding-to-1-entry)
                              ()))))

  (defthm gather-qword-addresses-corresponding-to-1-entry-xw-fld=mem-disjoint
    (implies (and (disjoint-p (addr-range 1 index)
                              (addr-range 8 addr))
                  (natp addr))
             (equal (gather-qword-addresses-corresponding-to-1-entry
                     addr (xw :mem index val x86))
                    (gather-qword-addresses-corresponding-to-1-entry addr x86)))
    :hints (("Goal"
             :in-theory (e/d* (gather-qword-addresses-corresponding-to-1-entry)
                              (addr-range
                               addr-range-1)))))

  (defthm gather-qword-addresses-corresponding-to-1-entry-wm-low-64
    (implies (and (disjoint-p (addr-range 8 index)
                              (addr-range 8 addr))
                  (physical-address-p index)
                  (physical-address-p addr))
             (equal (gather-qword-addresses-corresponding-to-1-entry
                     addr (wm-low-64 index val x86))
                    (gather-qword-addresses-corresponding-to-1-entry addr x86)))
    :hints (("Goal"
             :in-theory (e/d* (gather-qword-addresses-corresponding-to-1-entry)
                              ()))))

  (defthm gather-qword-addresses-corresponding-to-1-entry-xw-fld=mem-superior-entry-addr
    (implies (and (equal index addr)
                  ;; (or
                  ;;  (equal val (set-accessed-bit (rm-low-64 addr x86)))
                  ;;  (equal val (set-dirty-bit (rm-low-64 addr x86)))
                  ;;  (equal val (set-dirty-bit (set-accessed-bit (rm-low-64 addr x86)))))
                  (xlate-equiv-entries val (rm-low-64 addr x86))
                  (unsigned-byte-p 64 val)
                  (physical-address-p index)
                  (physical-address-p (+ 7 index))
                  (x86p x86))
             (equal (gather-qword-addresses-corresponding-to-1-entry
                     addr (wm-low-64 index val x86))
                    (gather-qword-addresses-corresponding-to-1-entry addr x86)))
    :hints (("Goal"
             :in-theory (e/d* (member-p)
                              (xlate-equiv-entries))
             :use ((:instance xlate-equiv-entries-and-loghead
                              (e1 val)
                              (e2 (rm-low-64 addr x86))
                              (n 1))
                   (:instance logtail-bigger-and-logbitp
                              (e1 val)
                              (e2 (rm-low-64 addr x86))
                              (n 7)
                              (m 7))
                   (:instance xlate-equiv-entries-and-logtail
                              (e1 val)
                              (e2 (rm-low-64 addr x86))
                              (n 7))
                   (:instance xlate-equiv-entries-and-logtail
                              (e1 val)
                              (e2 (rm-low-64 addr x86))
                              (n 12))))))

  (defthm gather-qword-addresses-corresponding-to-1-entry-with-different-x86-entries
    (implies (and (xlate-equiv-entries (rm-low-64 addr x86-equiv)
                                       (rm-low-64 addr x86))
                  (x86p x86)
                  (x86p x86-equiv))
             (equal (gather-qword-addresses-corresponding-to-1-entry addr x86-equiv)
                    (gather-qword-addresses-corresponding-to-1-entry addr x86)))
    :hints (("Goal" :in-theory (e/d* (gather-qword-addresses-corresponding-to-1-entry)
                                     (unsigned-byte-p))
             :use ((:instance xlate-equiv-entries-and-loghead
                              (e1 (rm-low-64 addr x86-equiv))
                              (e2 (rm-low-64 addr x86))
                              (n 1))
                   (:instance logtail-bigger-and-logbitp
                              (e1 (rm-low-64 addr x86-equiv))
                              (e2 (rm-low-64 addr x86))
                              (n 7)
                              (m 7))
                   (:instance xlate-equiv-entries-and-logtail
                              (e1 (rm-low-64 addr x86-equiv))
                              (e2 (rm-low-64 addr x86))
                              (n 7))
                   (:instance xlate-equiv-entries-and-logtail
                              (e1 (rm-low-64 addr x86-equiv))
                              (e2 (rm-low-64 addr x86))
                              (n 12))))))

  (defthm gather-qword-addresses-corresponding-to-1-entry-wm-low-64-with-different-x86-disjoint
    (implies (and (disjoint-p (addr-range 8 index) (addr-range 8 addr))
                  (physical-address-p addr)
                  (physical-address-p index)
                  (equal (gather-qword-addresses-corresponding-to-1-entry addr x86-equiv)
                         (gather-qword-addresses-corresponding-to-1-entry addr x86)))
             ;; (xlate-equiv-entries (rm-low-64 addr x86-equiv)
             ;;                      (rm-low-64 addr x86))
             (equal (gather-qword-addresses-corresponding-to-1-entry
                     addr (wm-low-64 index val x86-equiv))
                    (gather-qword-addresses-corresponding-to-1-entry addr x86)))
    :hints (("Goal" :in-theory (e/d* (gather-qword-addresses-corresponding-to-1-entry)
                                     (gather-qword-addresses-corresponding-to-1-entry-wm-low-64
                                      unsigned-byte-p))
             :use ((:instance gather-qword-addresses-corresponding-to-1-entry-wm-low-64
                              (x86 x86-equiv))))))

  (defthm gather-qword-addresses-corresponding-to-1-entry-wm-low-64-with-different-x86
    ;; This is a surprising theorem. Even if we write an
    ;; xlate-equiv-entries value to addr in x86-equiv (a state that may
    ;; be different from x86), there's no guarantee that the qword
    ;; addresses of the inferior structure entry pointed to by this new
    ;; value will be the same in x86 and x86-equiv. However, that's
    ;; exactly what this theorem says, and this is because of the way
    ;; gather-qword-addresses-corresponding-to-1-entry is defined ---
    ;; simply in terms of create-qword-address-list once the entry at
    ;; addr is read from the x86 (or x86-equiv) state.
    (implies (and (xlate-equiv-entries val (rm-low-64 addr x86))
                  (unsigned-byte-p 64 val)
                  (physical-address-p addr)
                  (physical-address-p (+ 7 addr))
                  (x86p x86))
             (equal (gather-qword-addresses-corresponding-to-1-entry
                     addr (wm-low-64 addr val x86-equiv))
                    (gather-qword-addresses-corresponding-to-1-entry addr x86)))
    :hints (("Goal" :in-theory (e/d* (gather-qword-addresses-corresponding-to-1-entry)
                                     ())
             :use ((:instance xlate-equiv-entries-and-loghead
                              (e1 val)
                              (e2 (rm-low-64 addr x86))
                              (n 1))
                   (:instance logtail-bigger-and-logbitp
                              (e1 val)
                              (e2 (rm-low-64 addr x86))
                              (n 7)
                              (m 7))
                   (:instance xlate-equiv-entries-and-logtail
                              (e1 val)
                              (e2 (rm-low-64 addr x86))
                              (n 7))
                   (:instance xlate-equiv-entries-and-logtail
                              (e1 val)
                              (e2 (rm-low-64 addr x86))
                              (n 12)))))))

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
   (list-of-lists-of-addresses true-list-listp))

  (defthm gather-qword-addresses-corresponding-to-entries-xw-fld!=mem
    (implies (not (equal fld :mem))
             (equal (gather-qword-addresses-corresponding-to-entries
                     addrs (xw fld index val x86))
                    (gather-qword-addresses-corresponding-to-entries addrs x86)))
    :hints (("Goal"
             :in-theory (e/d* (gather-qword-addresses-corresponding-to-entries)
                              ()))))

  (defthm gather-qword-addresses-corresponding-to-entries-xw-fld=mem-disjoint
    (implies (and (not (member-p index addrs))
                  (equal (loghead 3 index) 0)
                  (physical-address-p index)
                  (mult-8-qword-paddr-listp addrs))
             (equal (gather-qword-addresses-corresponding-to-entries
                     addrs (xw :mem index val x86))
                    (gather-qword-addresses-corresponding-to-entries addrs x86)))
    :hints (("Goal"
             :in-theory (e/d* (gather-qword-addresses-corresponding-to-entries
                               ifix)
                              (addr-range
                               (addr-range))))))

  (defthm gather-qword-addresses-corresponding-to-entries-wm-low-64
    (implies (and (not (member-p index addrs))
                  (equal (loghead 3 index) 0)
                  (physical-address-p index)
                  (mult-8-qword-paddr-listp addrs))
             (equal (gather-qword-addresses-corresponding-to-entries
                     addrs (wm-low-64 index val x86))
                    (gather-qword-addresses-corresponding-to-entries addrs x86)))
    :hints (("Goal"
             :in-theory (e/d* (gather-qword-addresses-corresponding-to-entries
                               ifix)
                              ()))))

  (local
   (defthm gather-qword-addresses-corresponding-to-entries-xw-fld=mem-superior-entry-addr-helper
     (implies (and (member-p index (cdr addrs))
                   (no-duplicates-p addrs))
              (not (equal index (car addrs))))))

  (defthm gather-qword-addresses-corresponding-to-entries-xw-fld=mem-superior-entry-addr
    (implies (and (member-p index addrs)
                  (mult-8-qword-paddr-listp addrs)
                  (no-duplicates-p addrs)
                  ;; (or
                  ;;  (equal val (set-accessed-bit (rm-low-64 index x86)))
                  ;;  (equal val (set-dirty-bit (rm-low-64 index x86)))
                  ;;  (equal val (set-dirty-bit (set-accessed-bit (rm-low-64 index x86)))))
                  (xlate-equiv-entries val (rm-low-64 index x86))
                  (unsigned-byte-p 64 val)
                  (physical-address-p index)
                  (equal (loghead 3 index) 0)
                  (x86p x86))
             (equal (gather-qword-addresses-corresponding-to-entries
                     addrs (wm-low-64 index val x86))
                    (gather-qword-addresses-corresponding-to-entries addrs x86)))
    :hints (("Goal"
             :in-theory (e/d* (member-p)
                              (xlate-equiv-entries))
             :use ((:instance xlate-equiv-entries-and-loghead
                              (e1 val)
                              (e2 (rm-low-64 addr x86))
                              (n 1))
                   (:instance logtail-bigger-and-logbitp
                              (e1 val)
                              (e2 (rm-low-64 addr x86))
                              (n 7)
                              (m 7))
                   (:instance xlate-equiv-entries-and-logtail
                              (e1 val)
                              (e2 (rm-low-64 addr x86))
                              (n 7))
                   (:instance xlate-equiv-entries-and-logtail
                              (e1 val)
                              (e2 (rm-low-64 addr x86))
                              (n 12))))))

  (defthm gather-qword-addresses-corresponding-to-entries-wm-low-64-with-different-x86-disjoint
    (implies (and (equal (gather-qword-addresses-corresponding-to-entries addrs x86-equiv)
                         (gather-qword-addresses-corresponding-to-entries addrs x86))
                  (not (member-p index addrs))
                  (equal (loghead 3 index) 0)
                  (physical-address-p index)
                  (mult-8-qword-paddr-listp addrs))
             (equal (gather-qword-addresses-corresponding-to-entries
                     addrs (wm-low-64 index val x86-equiv))
                    (gather-qword-addresses-corresponding-to-entries addrs x86)))
    :hints (("Goal"
             :in-theory (e/d* (gather-qword-addresses-corresponding-to-entries
                               ifix)
                              ()))))

  (defthm gather-qword-addresses-corresponding-to-entries-wm-low-64-with-different-x86
    (implies (and (equal (gather-qword-addresses-corresponding-to-entries addrs x86-equiv)
                         (gather-qword-addresses-corresponding-to-entries addrs x86))
                  (member-p index addrs)
                  (mult-8-qword-paddr-listp addrs)
                  (no-duplicates-p addrs)
                  (xlate-equiv-entries val (rm-low-64 index x86-equiv))
                  (unsigned-byte-p 64 val)
                  (x86p x86-equiv))
             (equal (gather-qword-addresses-corresponding-to-entries
                     addrs (wm-low-64 index val x86-equiv))
                    (gather-qword-addresses-corresponding-to-entries addrs x86)))
    :hints (("Goal"
             :in-theory (e/d* (gather-qword-addresses-corresponding-to-entries
                               member-p)
                              (unsigned-byte-p))))))

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
   (list-of-lists-of-addresses true-list-listp))

  (defthm gather-qword-addresses-corresponding-to-list-of-entries-xw-fld!=mem
    (implies (not (equal fld :mem))
             (equal (gather-qword-addresses-corresponding-to-list-of-entries
                     addrs (xw fld index val x86))
                    (gather-qword-addresses-corresponding-to-list-of-entries addrs x86)))
    :hints (("Goal"
             :in-theory (e/d* (gather-qword-addresses-corresponding-to-list-of-entries)
                              ()))))

  (defthm gather-qword-addresses-corresponding-to-list-of-entries-xw-fld=mem-disjoint
    (implies (and (pairwise-disjoint-p-aux (list index) addrs)
                  (mult-8-qword-paddr-list-listp addrs)
                  (physical-address-p index)
                  (equal (loghead 3 index) 0))
             (equal (gather-qword-addresses-corresponding-to-list-of-entries
                     addrs (xw :mem index val x86))
                    (gather-qword-addresses-corresponding-to-list-of-entries addrs x86)))
    :hints (("Goal"
             :in-theory (e/d* (gather-qword-addresses-corresponding-to-list-of-entries)
                              ()))))

  (defthm gather-qword-addresses-corresponding-to-list-of-entries-wm-low-64
    (implies (and (pairwise-disjoint-p-aux (list index) addrs)
                  (mult-8-qword-paddr-list-listp addrs)
                  (physical-address-p index)
                  (equal (loghead 3 index) 0))
             (equal (gather-qword-addresses-corresponding-to-list-of-entries
                     addrs (wm-low-64 index val x86))
                    (gather-qword-addresses-corresponding-to-list-of-entries addrs x86)))
    :hints (("Goal"
             :in-theory (e/d* (gather-qword-addresses-corresponding-to-list-of-entries)
                              ()))))

  (defthm gather-qword-addresses-corresponding-to-list-of-entries-xw-superior-entry-addr
    (implies (and (member-list-p index addrs)
                  (mult-8-qword-paddr-list-listp addrs)
                  (no-duplicates-list-p addrs)
                  ;; (or
                  ;;  (equal val (set-accessed-bit (rm-low-64 index x86)))
                  ;;  (equal val (set-dirty-bit (rm-low-64 index x86)))
                  ;;  (equal val (set-dirty-bit (set-accessed-bit (rm-low-64 index x86)))))
                  (xlate-equiv-entries val (rm-low-64 index x86))
                  (unsigned-byte-p 64 val)
                  (physical-address-p index)
                  (equal (loghead 3 index) 0)
                  (x86p x86))
             (equal (gather-qword-addresses-corresponding-to-list-of-entries
                     addrs (wm-low-64 index val x86))
                    (gather-qword-addresses-corresponding-to-list-of-entries addrs x86)))
    :hints (("Goal"
             :in-theory (e/d* (gather-qword-addresses-corresponding-to-1-entry
                               member-p)
                              (xlate-equiv-entries))
             :use ((:instance xlate-equiv-entries-and-loghead
                              (e1 val)
                              (e2 (rm-low-64 addr x86))
                              (n 1))
                   (:instance logtail-bigger-and-logbitp
                              (e1 val)
                              (e2 (rm-low-64 addr x86))
                              (n 7)
                              (m 7))
                   (:instance xlate-equiv-entries-and-logtail
                              (e1 val)
                              (e2 (rm-low-64 addr x86))
                              (n 7))
                   (:instance xlate-equiv-entries-and-logtail
                              (e1 val)
                              (e2 (rm-low-64 addr x86))
                              (n 12))))))

  (defthm gather-qword-addresses-corresponding-to-list-of-entries-wm-low-64-with-different-x86-disjoint
    (implies (and (equal (gather-qword-addresses-corresponding-to-list-of-entries addrs x86-equiv)
                         (gather-qword-addresses-corresponding-to-list-of-entries addrs x86))
                  (pairwise-disjoint-p-aux (list index) addrs)
                  (mult-8-qword-paddr-list-listp addrs)
                  (physical-address-p index)
                  (equal (loghead 3 index) 0))
             (equal (gather-qword-addresses-corresponding-to-list-of-entries
                     addrs (wm-low-64 index val x86-equiv))
                    (gather-qword-addresses-corresponding-to-list-of-entries addrs x86)))
    :hints (("Goal"
             :in-theory (e/d* (gather-qword-addresses-corresponding-to-list-of-entries
                               member-p)
                              (physical-address-p)))))

  (defthm gather-qword-addresses-corresponding-to-list-of-entries-wm-low-64-with-different-x86
    (implies (and (equal
                   (gather-qword-addresses-corresponding-to-list-of-entries addrs x86-equiv)
                   (gather-qword-addresses-corresponding-to-list-of-entries addrs x86))
                  (member-list-p index addrs)
                  (mult-8-qword-paddr-list-listp addrs)
                  (no-duplicates-list-p addrs)
                  (xlate-equiv-entries val (rm-low-64 index x86-equiv))
                  (unsigned-byte-p 64 val)
                  (x86p x86-equiv))
             (equal (gather-qword-addresses-corresponding-to-list-of-entries
                     addrs (wm-low-64 index val x86-equiv))
                    (gather-qword-addresses-corresponding-to-list-of-entries addrs x86)))
    :hints (("Goal"
             :in-theory (e/d* (gather-qword-addresses-corresponding-to-list-of-entries
                               member-p)
                              (unsigned-byte-p))))))

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
   (list-of-lists-of-addresses true-list-listp))

  (defthm gather-all-paging-structure-qword-addresses-xw-fld!=mem-and-ctr
    (implies (and (not (equal fld :mem))
                  (not (equal fld :ctr)))
             (equal (gather-all-paging-structure-qword-addresses
                     (xw fld index val x86))
                    (gather-all-paging-structure-qword-addresses x86)))
    :hints (("Goal"
             :in-theory (e/d* (gather-all-paging-structure-qword-addresses)
                              ()))))

  (defthm gather-all-paging-structure-qword-addresses-xw-fld=ctr
    (implies (not (equal index *cr3*))
             (equal (gather-all-paging-structure-qword-addresses
                     (xw :ctr index val x86))
                    (gather-all-paging-structure-qword-addresses x86)))
    :hints (("Goal"
             :in-theory (e/d* (gather-all-paging-structure-qword-addresses)
                              ()))))

  (defthm gather-all-paging-structure-qword-addresses-xw-fld=mem-disjoint
    (implies (and (mult-8-qword-paddr-list-listp addrs)
                  (pairwise-disjoint-p-aux (list index) addrs)
                  (physical-address-p index)
                  (equal (loghead 3 index) 0)
                  (equal addrs (gather-all-paging-structure-qword-addresses x86)))
             (equal (gather-all-paging-structure-qword-addresses (xw :mem index val x86))
                    addrs))
    :hints (("Goal"
             :use ((:instance gather-qword-addresses-corresponding-to-list-of-entries-xw-fld=mem-disjoint
                              (addrs (gather-qword-addresses-corresponding-to-list-of-entries
                                      (gather-qword-addresses-corresponding-to-entries
                                       (gather-pml4-table-qword-addresses x86)
                                       x86)
                                      (xw :mem index val x86)))
                              (index index)
                              (val val)
                              (x86 (xw :mem index val x86)))
                   (:instance gather-qword-addresses-corresponding-to-list-of-entries-xw-fld=mem-disjoint
                              (addrs (gather-qword-addresses-corresponding-to-list-of-entries
                                      (gather-qword-addresses-corresponding-to-entries
                                       (gather-pml4-table-qword-addresses x86)
                                       x86)
                                      x86))
                              (index index)
                              (val val)
                              (x86 x86))
                   (:instance gather-qword-addresses-corresponding-to-list-of-entries-xw-fld=mem-disjoint
                              (addrs (gather-qword-addresses-corresponding-to-entries
                                      (gather-pml4-table-qword-addresses x86)
                                      x86))
                              (index index)
                              (val val)
                              (x86 (xw :mem index val x86)))
                   (:instance gather-qword-addresses-corresponding-to-list-of-entries-xw-fld=mem-disjoint
                              (addrs (gather-qword-addresses-corresponding-to-entries
                                      (gather-pml4-table-qword-addresses x86)
                                      x86))
                              (index index)
                              (val val)
                              (x86 x86)))
             :in-theory (e/d* (gather-all-paging-structure-qword-addresses)
                              (gather-qword-addresses-corresponding-to-list-of-entries-xw-fld=mem-disjoint)))))

  (defthm gather-all-paging-structure-qword-addresses-wm-low-64-disjoint
    (implies (and (mult-8-qword-paddr-list-listp addrs)
                  (pairwise-disjoint-p-aux (list index) addrs)
                  (physical-address-p index)
                  (equal (loghead 3 index) 0)
                  (equal addrs (gather-all-paging-structure-qword-addresses x86)))
             (equal (gather-all-paging-structure-qword-addresses
                     (wm-low-64 index val x86))
                    (gather-all-paging-structure-qword-addresses x86)))
    :hints (("Goal"
             :in-theory (e/d* (gather-all-paging-structure-qword-addresses) ()))))

  (local
   (encapsulate
    ()

    (defthm no-duplicates-p-member-p-with-append-and-flatten
      (implies (and (no-duplicates-p (append x (acl2::flatten y)))
                    (true-listp x)
                    (true-list-listp y)
                    (member-list-p i y))
               (not (member-p i x)))
      :rule-classes (:forward-chaining :rewrite))

    (defthm no-duplicates-p-member-list-p-with-append-and-flatten
      (implies (and (no-duplicates-p (acl2::flatten (append x y)))
                    (true-list-listp x)
                    (true-list-listp y)
                    (member-list-p i y))
               (not (member-list-p i x)))
      :hints (("Goal" :in-theory (e/d () (acl2::flattenp-of-append))))
      :rule-classes (:forward-chaining :rewrite))

    (defthm no-duplicates-p-member-list-p-with-append-and-flatten-alt
      (implies (and (no-duplicates-p (append (acl2::flatten x) (acl2::flatten y)))
                    (true-list-listp x)
                    (true-list-listp y)
                    (member-list-p i y))
               (not (member-list-p i x)))
      :hints (("Goal" :in-theory (e/d (member-list-p) ())))
      :rule-classes (:forward-chaining :rewrite))

    (defthmd no-duplicates-p-and-member-list-p-1-top-helper
      (implies (and (no-duplicates-p (append x (acl2::flatten (append y z w))))
                    (or (member-list-p i y)
                        (member-list-p i z)
                        (member-list-p i w))
                    (true-listp x)
                    (true-list-listp y)
                    (true-list-listp z)
                    (true-list-listp w))
               (not (member-p i x)))
      :hints (("Goal" :in-theory (e/d* () (acl2::flattenp-of-append)))))

    (defthm no-duplicates-p-and-member-list-p-1-top
      (implies (and (no-duplicates-p (append x (acl2::flatten y) (acl2::flatten z) (acl2::flatten w)))
                    (or (member-list-p i y)
                        (member-list-p i z)
                        (member-list-p i w))
                    (true-listp x)
                    (true-list-listp y)
                    (true-list-listp z)
                    (true-list-listp w))
               (not (member-p i x)))
      :hints (("Goal" :use ((:instance no-duplicates-p-and-member-list-p-1-top-helper))))
      :rule-classes (:forward-chaining :rewrite))

    (defthmd no-duplicates-p-and-member-list-p-2-top-helper
      (implies (and (no-duplicates-p (append x (acl2::flatten (append y z w))))
                    (or (member-p i x)
                        (member-list-p i z)
                        (member-list-p i w))
                    (true-listp x)
                    (true-list-listp y)
                    (true-list-listp z)
                    (true-list-listp w))
               (not (member-list-p i y)))
      :hints (("Goal" :in-theory (e/d* () (acl2::flattenp-of-append)))))

    (defthm no-duplicates-p-and-member-list-p-2-top
      (implies (and (no-duplicates-p (append x (acl2::flatten y) (acl2::flatten z) (acl2::flatten w)))
                    (or (member-p i x)
                        (member-list-p i z)
                        (member-list-p i w))
                    (true-listp x)
                    (true-list-listp y)
                    (true-list-listp z)
                    (true-list-listp w))
               (not (member-list-p i y)))
      :hints (("Goal" :use ((:instance no-duplicates-p-and-member-list-p-2-top-helper))))
      :rule-classes (:forward-chaining :rewrite))

    (defthmd no-duplicates-p-and-member-list-p-3-top-helper-1
      (implies (and (member-list-p i w)
                    (true-listp x)
                    (true-list-listp y)
                    (true-list-listp z)
                    (true-list-listp w)
                    (no-duplicates-p (append x (acl2::flatten (append y z w)))))
               (not (member-list-p i z))))

    (defthmd no-duplicates-p-and-member-list-p-3-top-helper-2
      (implies (and (no-duplicates-p (append x (acl2::flatten (append y z w))))
                    (or (member-p i x)
                        (member-list-p i y)
                        (member-list-p i w))
                    (true-listp x)
                    (true-list-listp y)
                    (true-list-listp z)
                    (true-list-listp w))
               (not (member-list-p i z)))
      :hints (("Goal" :in-theory (e/d* (no-duplicates-p-and-member-list-p-3-top-helper-1)
                                       (acl2::flattenp-of-append)))))

    (defthm no-duplicates-p-and-member-list-p-3-top
      (implies (and (no-duplicates-p (append x (acl2::flatten y) (acl2::flatten z) (acl2::flatten w)))
                    (or (member-p i x)
                        (member-list-p i y)
                        (member-list-p i w))
                    (true-listp x)
                    (true-list-listp y)
                    (true-list-listp z)
                    (true-list-listp w))
               (not (member-list-p i z)))
      :hints (("Goal" :use ((:instance no-duplicates-p-and-member-list-p-3-top-helper-2))))
      :rule-classes (:forward-chaining :rewrite))

    (defthmd gather-all-paging-structure-qword-addresses-wm-low-64-entry-addr-helper
      (implies (and (equal addrs (gather-all-paging-structure-qword-addresses x86))
                    (mult-8-qword-paddr-list-listp addrs)
                    (no-duplicates-list-p addrs)
                    (member-list-p index addrs)
                    ;; (or (equal val (set-accessed-bit (rm-low-64 index x86)))
                    ;;     (equal val (set-dirty-bit (rm-low-64 index x86)))
                    ;;     (equal val (set-dirty-bit (set-accessed-bit (rm-low-64 index x86)))))
                    (xlate-equiv-entries val (rm-low-64 index x86))
                    (unsigned-byte-p 64 val)
                    (physical-address-p index)
                    (equal (loghead 3 index) 0)
                    (x86p x86))
               (equal (gather-all-paging-structure-qword-addresses
                       (wm-low-64 index val x86))
                      (gather-all-paging-structure-qword-addresses x86)))
      :hints (("Goal"
               :in-theory (e/d* (member-p)
                                (xlate-equiv-entries))
               :use ((:instance xlate-equiv-entries-and-loghead
                                (e1 val)
                                (e2 (rm-low-64 addr x86))
                                (n 1))
                     (:instance logtail-bigger-and-logbitp
                                (e1 val)
                                (e2 (rm-low-64 addr x86))
                                (n 7)
                                (m 7))
                     (:instance xlate-equiv-entries-and-logtail
                                (e1 val)
                                (e2 (rm-low-64 addr x86))
                                (n 7))
                     (:instance xlate-equiv-entries-and-logtail
                                (e1 val)
                                (e2 (rm-low-64 addr x86))
                                (n 12))))))))

  (defthm gather-all-paging-structure-qword-addresses-wm-low-64-entry-addr
    (implies (and (equal addrs (gather-all-paging-structure-qword-addresses x86))
                  (mult-8-qword-paddr-list-listp addrs)
                  (no-duplicates-list-p addrs)
                  (member-list-p index addrs)
                  ;; (or (equal val (set-accessed-bit (rm-low-64 index x86)))
                  ;;     (equal val (set-dirty-bit (rm-low-64 index x86)))
                  ;;     (equal val (set-dirty-bit (set-accessed-bit (rm-low-64 index x86)))))
                  (xlate-equiv-entries val (rm-low-64 index x86))
                  (unsigned-byte-p 64 val)
                  (x86p x86))
             (equal (gather-all-paging-structure-qword-addresses
                     (wm-low-64 index val x86))
                    (gather-all-paging-structure-qword-addresses x86)))
    :hints (("Goal"
             :use ((:instance gather-all-paging-structure-qword-addresses-wm-low-64-entry-addr-helper)
                   (:instance member-list-p-and-mult-8-qword-paddr-list-listp))))))

;; ======================================================================

;; Compare the paging structures in two x86 states:

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

  (defthm xlate-equiv-entries-at-qword-addresses-aux?-reflexive
    (implies (qword-paddr-listp a)
             (xlate-equiv-entries-at-qword-addresses-aux? a a x x)))

  (defthm xlate-equiv-entries-at-qword-addresses-aux?-commutative
    (implies (equal (len a) (len b))
             (equal (xlate-equiv-entries-at-qword-addresses-aux? a b x y)
                    (xlate-equiv-entries-at-qword-addresses-aux? b a y x))))

  (defthm xlate-equiv-entries-at-qword-addresses-aux?-transitive
    (implies (and (equal (len a) (len b))
                  (equal (len b) (len c))
                  (xlate-equiv-entries-at-qword-addresses-aux? a b x y)
                  (xlate-equiv-entries-at-qword-addresses-aux? b c y z))
             (xlate-equiv-entries-at-qword-addresses-aux? a c x z)))

  (defthm xlate-equiv-entries-at-qword-addresses-aux?-with-xw-fld!=mem
    (implies (not (equal fld :mem))
             (equal (xlate-equiv-entries-at-qword-addresses-aux?
                     addrs-1 addrs-2
                     x86-1
                     (xw fld index val x86-2))
                    (xlate-equiv-entries-at-qword-addresses-aux?
                     addrs-1 addrs-2 x86-1 x86-2))))

  (defthm xlate-equiv-entries-at-qword-addresses-aux?-with-wm-low-64-disjoint
    (implies (and (mult-8-qword-paddr-listp addrs)
                  (physical-address-p index)
                  (equal (loghead 3 index) 0)
                  (not (member-p index addrs)))
             (equal (xlate-equiv-entries-at-qword-addresses-aux?
                     addrs addrs
                     x86-1
                     (wm-low-64 index val x86-2))
                    (xlate-equiv-entries-at-qword-addresses-aux?
                     addrs addrs
                     x86-1
                     x86-2)))
    :hints (("Goal" :in-theory (e/d* (member-p) (xlate-equiv-entries)))))

  (defthm xlate-equiv-entries-at-qword-addresses-aux?-with-wm-low-64
    (implies (and (mult-8-qword-paddr-listp addrs)
                  (no-duplicates-p addrs)
                  (member-p index addrs)
                  (xlate-equiv-entries val (rm-low-64 index x86-1))
                  (unsigned-byte-p 64 val)
                  (xlate-equiv-entries-at-qword-addresses-aux? addrs addrs x86-1 x86-2))
             (xlate-equiv-entries-at-qword-addresses-aux?
              addrs addrs
              x86-1
              (wm-low-64 index val x86-2)))
    :hints (("Goal" :in-theory (e/d* (member-p)
                                     (xlate-equiv-entries)))))

  (local
   (defthmd xlate-equiv-entries-at-qword-addresses-aux?-with-wm-low-64-different-x86-helper-1
     (implies
      (and (consp addrs)
           (unsigned-byte-p 52 (+ 7 (car addrs)))
           (xlate-equiv-entries (rm-low-64 (car addrs) x86-1)
                                (rm-low-64 (car addrs) x86-2))
           (unsigned-byte-p 52 index)
           (unsigned-byte-p 52 (car addrs))
           (equal (loghead 3 (car addrs)) 0)
           (mult-8-qword-paddr-listp (cdr addrs))
           (not (member-p (car addrs) (cdr addrs)))
           (no-duplicates-p (cdr addrs))
           (member-p index (cdr addrs))
           (not (xlate-equiv-entries (rm-low-64 (car addrs) x86-1)
                                     (rm-low-64 (car addrs)
                                                (wm-low-64 index val x86-2)))))
      (not (xlate-equiv-entries-at-qword-addresses-aux? (cdr addrs)
                                                        (cdr addrs)
                                                        x86-1 x86-2)))
     :hints (("Goal" :in-theory (e/d* () (mult-8-qword-paddr-listp-and-disjoint-p))
              :use ((:instance mult-8-qword-paddr-listp-and-disjoint-p
                               (index index)
                               (addrs (cdr addrs))
                               (addr (car addrs))))))))

  (local
   (defthmd xlate-equiv-entries-at-qword-addresses-aux?-with-wm-low-64-different-x86-helper-2
     (implies (and (consp addrs)
                   (unsigned-byte-p 52 (+ 7 (car addrs)))
                   (not (xlate-equiv-entries (rm-low-64 (car addrs) x86-1)
                                             (rm-low-64 (car addrs) x86-2)))
                   (unsigned-byte-p 52 index)
                   (unsigned-byte-p 52 (car addrs))
                   (equal (loghead 3 (car addrs)) 0)
                   (mult-8-qword-paddr-listp (cdr addrs))
                   (not (member-p (car addrs) (cdr addrs)))
                   (no-duplicates-p (cdr addrs))
                   (member-p index (cdr addrs))
                   (xlate-equiv-entries (rm-low-64 (car addrs) x86-1)
                                        (rm-low-64 (car addrs)
                                                   (wm-low-64 index val x86-2))))
              (not (xlate-equiv-entries-at-qword-addresses-aux?
                    (cdr addrs)
                    (cdr addrs)
                    x86-1 (wm-low-64 index val x86-2))))
     :hints (("Goal" :in-theory (e/d* () (mult-8-qword-paddr-listp-and-disjoint-p))
              :use ((:instance mult-8-qword-paddr-listp-and-disjoint-p
                               (index index)
                               (addrs (cdr addrs))
                               (addr (car addrs))))))))

  (defthmd xlate-equiv-entries-at-qword-addresses-aux?-with-wm-low-64-different-x86
    (implies (and (mult-8-qword-paddr-listp addrs)
                  (no-duplicates-p addrs)
                  (member-p index addrs)
                  (xlate-equiv-entries val (rm-low-64 index x86-2))
                  (unsigned-byte-p 64 val))
             (equal
              (xlate-equiv-entries-at-qword-addresses-aux?
               addrs addrs
               x86-1
               (wm-low-64 index val x86-2))
              (xlate-equiv-entries-at-qword-addresses-aux? addrs addrs x86-1 x86-2)))
    :hints (("Goal"
             :use ((:instance member-p-and-mult-8-qword-paddr-listp))
             :in-theory (e/d* (member-p
                               xlate-equiv-entries-at-qword-addresses-aux?)
                              (xlate-equiv-entries)))
            ;; Ugh, subgoal hints...
            ("Subgoal *1/4"
             :use
             ((:instance xlate-equiv-entries-at-qword-addresses-aux?-with-wm-low-64-different-x86-helper-1)))
            ("Subgoal *1/3"
             :use
             ((:instance xlate-equiv-entries-at-qword-addresses-aux?-with-wm-low-64-different-x86-helper-2))))))

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

  (defthm xlate-equiv-entries-at-qword-addresses?-reflexive
    (implies (qword-paddr-list-listp a)
             (xlate-equiv-entries-at-qword-addresses? a a x x)))

  (defthm xlate-equiv-entries-at-qword-addresses?-commutative
    (implies (equal (len a) (len b))
             (equal (xlate-equiv-entries-at-qword-addresses? a b x y)
                    (xlate-equiv-entries-at-qword-addresses? b a y x))))

  (defthm xlate-equiv-entries-at-qword-addresses?-transitive-equal-len
    (implies (and (equal (len a) (len b))
                  (equal (len b) (len c))
                  (xlate-equiv-entries-at-qword-addresses? a b x y)
                  (xlate-equiv-entries-at-qword-addresses? b c y z))
             (xlate-equiv-entries-at-qword-addresses? a c x z)))

  (defthm xlate-equiv-entries-at-qword-addresses?-transitive
    (implies (and (equal a b)
                  (equal b c)
                  (xlate-equiv-entries-at-qword-addresses? a b x y)
                  (xlate-equiv-entries-at-qword-addresses? b c y z))
             (xlate-equiv-entries-at-qword-addresses? a c x z))
    :hints (("Goal" :in-theory
             (e/d*
              ()
              (xlate-equiv-entries-at-qword-addresses?-transitive-equal-len))
             :use ((:instance xlate-equiv-entries-at-qword-addresses?-transitive-equal-len)))))

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
                                     (xlate-equiv-entries)))))

  (defthm xlate-equiv-entries-at-qword-addresses?-with-xw-fld!=mem
    (implies (not (equal fld :mem))
             (equal (xlate-equiv-entries-at-qword-addresses?
                     addrs addrs
                     x86
                     (xw fld index val x86))
                    (xlate-equiv-entries-at-qword-addresses?
                     addrs addrs
                     x86
                     x86)))
    :hints (("Goal" :in-theory (e/d* (xlate-equiv-entries-at-qword-addresses?)
                                     ()))))

  ;; (defthm xlate-equiv-entries-at-qword-addresses?-with-wm-low-64-disjoint
  ;;   (implies (and (mult-8-qword-paddr-list-listp addrs)
  ;;                 (not (member-list-p index addrs))
  ;;                 (physical-address-p index)
  ;;                 (equal (loghead 3 index) 0))
  ;;            (equal (xlate-equiv-entries-at-qword-addresses?
  ;;                    addrs addrs
  ;;                    x86
  ;;                    (wm-low-64 index val x86))
  ;;                   (xlate-equiv-entries-at-qword-addresses?
  ;;                    addrs addrs
  ;;                    x86
  ;;                    x86)))
  ;;   :hints (("Goal" :in-theory (e/d* (xlate-equiv-entries-at-qword-addresses?
  ;;                                     member-p member-list-p)
  ;;                                    (xlate-equiv-entries)))))

  (defthm xlate-equiv-entries-at-qword-addresses?-with-wm-low-64-disjoint
    (implies (and (mult-8-qword-paddr-list-listp addrs)
                  (not (member-list-p index addrs))
                  (physical-address-p index)
                  (equal (loghead 3 index) 0))
             (equal (xlate-equiv-entries-at-qword-addresses?
                     addrs
                     addrs x86-1 (wm-low-64 index val x86-2))
                    (xlate-equiv-entries-at-qword-addresses?
                     addrs addrs x86-1 x86-2)))
    :hints (("Goal" :in-theory (e/d* (xlate-equiv-entries-at-qword-addresses?
                                      member-p member-list-p)
                                     (xlate-equiv-entries)))))

  (defthm xlate-equiv-entries-at-qword-addresses?-with-wm-low-64
    (implies (and (mult-8-qword-paddr-list-listp addrs)
                  (no-duplicates-list-p addrs)
                  (member-list-p index addrs)
                  ;; (or (equal val (set-accessed-bit (rm-low-64 index x86)))
                  ;;     (equal val (set-dirty-bit (rm-low-64 index x86)))
                  ;;     (equal val (set-dirty-bit (set-accessed-bit (rm-low-64 index x86)))))
                  (xlate-equiv-entries val (rm-low-64 index x86))
                  (unsigned-byte-p 64 val)
                  (xlate-equiv-entries-at-qword-addresses? addrs addrs x86 x86))
             (xlate-equiv-entries-at-qword-addresses?
              addrs addrs x86 (wm-low-64 index val x86)))
    :hints (("Goal"
             :in-theory (e/d* (xlate-equiv-entries-at-qword-addresses?
                               member-p
                               member-list-p)
                              (xlate-equiv-entries
                               xlate-equiv-entries-at-qword-addresses?-implies-xlate-equiv-entries)))))

  (local
   (defthmd xlate-equiv-entries-at-qword-addresses?-with-wm-low-64-with-different-x86-helper
     (implies (and (mult-8-qword-paddr-list-listp addrs)
                   (no-duplicates-list-p addrs)
                   (member-list-p index addrs)
                   (physical-address-p index)  ;;
                   (equal (loghead 3 index) 0) ;;
                   (xlate-equiv-entries val (rm-low-64 index x86-2))
                   (unsigned-byte-p 64 val)
                   (xlate-equiv-entries-at-qword-addresses? addrs addrs x86-1 x86-2))
              (xlate-equiv-entries-at-qword-addresses?
               addrs addrs
               x86-1
               (wm-low-64 index val x86-2)))
     :hints (("Goal"
              :in-theory (e/d* (member-p
                                xlate-equiv-entries-at-qword-addresses-aux?-with-wm-low-64-different-x86
                                xlate-equiv-entries-at-qword-addresses?)
                               (xlate-equiv-entries
                                physical-address-p
                                unsigned-byte-p))))))

  (defthmd xlate-equiv-entries-at-qword-addresses?-with-wm-low-64-with-different-x86
    (implies (and (mult-8-qword-paddr-list-listp addrs)
                  (no-duplicates-list-p addrs)
                  (member-list-p index addrs)
                  (xlate-equiv-entries val (rm-low-64 index x86-1))
                  (unsigned-byte-p 64 val)
                  (xlate-equiv-entries-at-qword-addresses? addrs addrs x86-1 x86-2))
             (xlate-equiv-entries-at-qword-addresses?
              addrs addrs
              x86-1
              (wm-low-64 index val x86-2)))
    :hints (("Goal"
             :use
             ((:instance member-list-p-and-mult-8-qword-paddr-list-listp)
              (:instance xlate-equiv-entries-at-qword-addresses?-with-wm-low-64-with-different-x86-helper))))))

(define good-paging-structures-x86p (x86)
  (and (x86p x86)
       (let* ((paging-addresses (gather-all-paging-structure-qword-addresses x86)))
         (and (mult-8-qword-paddr-list-listp paging-addresses)
              (no-duplicates-list-p paging-addresses))))
  ///

  (defthm good-paging-structures-x86p-implies-x86p
    (implies (good-paging-structures-x86p x86)
             (x86p x86))
    :hints (("Goal" :in-theory (e/d* (good-paging-structures-x86p) ()))))

  (defthm good-paging-structures-x86p-xw-fld!=mem-and-ctr
    (implies (and (not (equal fld :mem))
                  (not (equal fld :ctr))
                  (x86p x86)
                  (x86p (xw fld index val x86)))
             (equal (good-paging-structures-x86p (xw fld index val x86))
                    (good-paging-structures-x86p x86)))))

(define xlate-equiv-x86s (x86-1 x86-2)
  :guard (and (x86p x86-1)
              (x86p x86-2))
  :non-executable t
  :enabled t
  :long "<p>Two x86 states are @('xlate-equiv-x86s') if their paging
  structures are equal, modulo the accessed and dirty bits (See @(see
  xlate-equiv-entries)). Each of the two states' paging structures
  must satisfy @(see pairwise-disjoint-p).</p>"

  (if (good-paging-structures-x86p x86-1)

      (if (good-paging-structures-x86p x86-2)

          (let* ((paging-qword-addresses-1
                  (gather-all-paging-structure-qword-addresses x86-1))
                 (paging-qword-addresses-2
                  (gather-all-paging-structure-qword-addresses x86-2)))

            (and (equal (ctri *cr3* x86-1) (ctri *cr3* x86-2))
                 (equal paging-qword-addresses-1 paging-qword-addresses-2)
                 (xlate-equiv-entries-at-qword-addresses?
                  paging-qword-addresses-1 paging-qword-addresses-2 x86-1 x86-2)))

        nil)

    (not (good-paging-structures-x86p x86-2)))

  ///

  (local
   (defthm xlate-equiv-x86s-is-transitive-helper
     (implies (and (xlate-equiv-x86s x y)
                   (xlate-equiv-x86s y z))
              (xlate-equiv-x86s x z))
     :hints (("Goal"
              :in-theory (e/d* () (xlate-equiv-entries-at-qword-addresses?-transitive))
              :use
              ((:instance
                xlate-equiv-entries-at-qword-addresses?-transitive
                (a (gather-all-paging-structure-qword-addresses x))
                (b (gather-all-paging-structure-qword-addresses y))
                (c (gather-all-paging-structure-qword-addresses z))))))))

  (defequiv xlate-equiv-x86s
    :hints (("Goal" :in-theory (e/d* () (xlate-equiv-x86s-is-transitive-helper))
             :use ((:instance xlate-equiv-x86s-is-transitive-helper))))))

;; =====================================================================

;; gather-all-paging-structure-qword-addresses and wm-low-64, with
;; equiv x86s:

(defthm gather-all-paging-structure-qword-addresses-wm-low-64-different-x86-disjoint
  (implies (and (xlate-equiv-x86s x86 x86-equiv)
                (good-paging-structures-x86p x86)
                (equal addrs (gather-all-paging-structure-qword-addresses x86))
                (pairwise-disjoint-p-aux (list index) addrs)
                (mult-8-qword-paddr-list-listp addrs)
                (physical-address-p index)
                (equal (loghead 3 index) 0))
           (equal (gather-all-paging-structure-qword-addresses
                   (wm-low-64 index val x86-equiv))
                  (gather-all-paging-structure-qword-addresses x86))))

(defthm gather-all-paging-structure-qword-addresses-wm-low-64-different-x86
  (implies (and (xlate-equiv-x86s x86 x86-equiv)
                (good-paging-structures-x86p x86)
                (equal addrs (gather-all-paging-structure-qword-addresses x86))
                (member-list-p index addrs)
                (xlate-equiv-entries val (rm-low-64 index x86))
                (mult-8-qword-paddr-list-listp addrs)
                (no-duplicates-list-p addrs)
                (unsigned-byte-p 64 val))
           (equal (gather-all-paging-structure-qword-addresses
                   (wm-low-64 index val x86-equiv))
                  (gather-all-paging-structure-qword-addresses x86)))
  :hints (("Goal" :in-theory (e/d* ()
                                   (gather-all-paging-structure-qword-addresses-wm-low-64-entry-addr))
           :use ((:instance gather-all-paging-structure-qword-addresses-wm-low-64-entry-addr
                            (x86 x86-equiv))
                 (:instance gather-all-paging-structure-qword-addresses-wm-low-64-entry-addr
                            (x86 x86))))))

;; ======================================================================
