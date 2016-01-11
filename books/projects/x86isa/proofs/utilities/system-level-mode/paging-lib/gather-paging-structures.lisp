;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")
(include-book "paging-basics")

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "centaur/bitops/signed-byte-p" :dir :system))

;; ======================================================================

(defsection gather-paging-structures
  :parents (reasoning-about-page-tables)

  :short "Gather physical addresses where paging data structures are located"

  :long "<p>WORK IN PROGRESS...</p>

<p>This doc topic will be updated in later commits...</p>"
  )

;; ======================================================================

;; Some misc. lemmas:

(defthmd loghead-smaller-and-logbitp
  (implies (and (equal (loghead n e-1) (loghead n e-2))
                (natp n)
                (natp m)
                (< m n))
           (equal (logbitp m e-1) (logbitp m e-2)))
  :hints (("Goal" :in-theory (e/d* (bitops::ihsext-inductions
                                    bitops::ihsext-recursive-redefs)
                                   ()))))

(defthmd logtail-bigger
  (implies (and (equal (logtail m e-1) (logtail m e-2))
                (integerp e-2)
                (natp n)
                (<= m n))
           (equal (logtail n e-1) (logtail n e-2)))
  :hints (("Goal" :in-theory (e/d* (bitops::ihsext-inductions
                                    bitops::ihsext-recursive-redefs)
                                   ()))))

(defthmd logtail-bigger-and-logbitp
  (implies (and (equal (logtail m e-1) (logtail m e-2))
                (integerp e-2)
                (natp n)
                (<= m n))
           (equal (logbitp n e-1) (logbitp n e-2)))
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
  :parents (reasoning-about-page-tables)
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
  :parents (reasoning-about-page-tables)
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

  :parents (reasoning-about-page-tables)
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
  :parents (reasoning-about-page-tables)
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
  :parents (reasoning-about-page-tables)
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

(define open-qword-paddr-list (xs)
  :guard (qword-paddr-listp xs)
  :enabled t
  (if (endp xs)
      nil
    (append (addr-range 8 (car xs))
            (open-qword-paddr-list (cdr xs))))
  ///

  (defthm open-qword-paddr-list-and-member-p
    (implies (and (mult-8-qword-paddr-listp addrs)
                  (member-p index addrs))
             (member-p index (open-qword-paddr-list addrs)))
    :hints (("Goal" :in-theory (e/d* (member-p) ()))))

  (defthm open-qword-paddr-list-and-append
    (equal (open-qword-paddr-list (append xs ys))
           (append (open-qword-paddr-list xs)
                   (open-qword-paddr-list ys)))))

(define open-qword-paddr-list-list (xs)
  :guard (qword-paddr-list-listp xs)
  :enabled t
  (if (endp xs)
      nil
    (cons (open-qword-paddr-list (car xs))
          (open-qword-paddr-list-list (cdr xs))))
  ///

  (defthm open-qword-paddr-list-list-and-member-list-p
    (implies (and (mult-8-qword-paddr-list-listp addrs)
                  (member-list-p index addrs))
             (member-list-p index (open-qword-paddr-list-list addrs)))
    :hints (("Goal" :in-theory (e/d* (member-list-p member-p) ()))))

  (defthm open-qword-paddr-list-list-and-append
    (equal (open-qword-paddr-list-list (append xs ys))
           (append (open-qword-paddr-list-list xs)
                   (open-qword-paddr-list-list ys))))

  (defthm open-qword-paddr-list-list-pairwise-disjoint-p-aux-and-disjoint-p
    (implies (and
              (pairwise-disjoint-p-aux (list index) (open-qword-paddr-list-list addrs))
              (member-list-p entry-addr addrs))
             (disjoint-p (list index) (addr-range 8 entry-addr)))
    :hints (("Goal" :in-theory (e/d* (pairwise-disjoint-p-aux)
                                     ()))))

  (defthm open-qword-paddr-list-list-pairwise-disjoint-p-aux-and-member-p
    (implies (and (pairwise-disjoint-p-aux (list index) (open-qword-paddr-list-list addrs))
                  (member-list-p entry-addr addrs))
             (not (member-p index (addr-range 8 entry-addr))))
    :hints (("Goal" :in-theory (e/d* (pairwise-disjoint-p-aux) ())))))

(local (in-theory (e/d* () (unsigned-byte-p))))

;; ======================================================================

(define xlate-equiv-entries
  ((e-1 :type (unsigned-byte 64))
   (e-2 :type (unsigned-byte 64)))
  :parents (xlate-equiv-x86s)
  :long "<p>Two paging structure entries are @('xlate-equiv-entries')
  if they are equal for all bits except the accessed and dirty
  bits (bits 5 and 6, respectively).</p>"
  (and (equal (part-select e-1 :low 0 :high 4)
              (part-select e-2 :low 0 :high 4))
       ;; Bits 5 (accessed bit) and 6 (dirty bit) missing here.
       (equal (part-select e-1 :low 7 :high 63)
              (part-select e-2 :low 7 :high 63)))
  ///
  (defequiv xlate-equiv-entries)

  (defthm xlate-equiv-entries-self-set-accessed-bit
    (and (xlate-equiv-entries e (set-accessed-bit (double-rewrite e)))
         (xlate-equiv-entries (set-accessed-bit e) (double-rewrite e)))
    :hints (("Goal" :in-theory (e/d* (set-accessed-bit) ()))))

  (defthm xlate-equiv-entries-self-set-dirty-bit
    (and (xlate-equiv-entries e (set-dirty-bit (double-rewrite e)))
         (xlate-equiv-entries (set-dirty-bit e) (double-rewrite e)))
    :hints (("Goal" :in-theory (e/d* (set-dirty-bit) ()))))

  (defun find-xlate-equiv-entries (e-1-equiv e-2-equiv)
    ;; [Shilpi]: This is a quick and dirty function to bind the
    ;; free-vars of
    ;; xlate-equiv-entries-and-set-accessed-and/or-dirty-bit. It makes
    ;; the assumption that e-1-equiv and e-2-equiv will have one of the
    ;; following forms:

    ;; e-1-equiv == e-2-equiv (any form as long as they're both equal)
    ;; (set-accessed-bit (rm-low-64 index x86))
    ;; (set-dirty-bit (rm-low-64 index x86))
    ;; (set-accessed-bit (set-dirty-bit (rm-low-64 index x86)))
    ;; (set-dirty-bit (set-accessed-bit (rm-low-64 index x86)))

    ;; I haven't considered deeper nesting of set-accessed-bit and
    ;; set-dirty-bit, mainly because at this point, I'm reasonably
    ;; confident that that's a situation that won't occur.
    (cond ((equal e-1-equiv e-2-equiv)
           `((e-1 . ,e-1-equiv)
             (e-2 . ,e-2-equiv)))
          ((equal (first e-1-equiv) 'rm-low-64)
           (cond ((equal (first e-2-equiv) 'rm-low-64)
                  `((e-1 . ,e-1-equiv)
                    (e-2 . ,e-2-equiv)))
                 ((equal (first e-2-equiv) 'set-accessed-bit)
                  (b* ((e-2
                        (if (equal (car (second e-2-equiv)) 'set-dirty-bit)
                            (second (second e-2-equiv))
                          (second e-2-equiv))))
                    `((e-1 . ,e-1-equiv)
                      (e-2 . ,e-2))))
                 ((equal (first e-2-equiv) 'set-dirty-bit)
                  (b* ((e-2
                        (if (equal (car (second e-2-equiv)) 'set-accessed-bit)
                            (second (second e-2-equiv))
                          (second (second e-2-equiv)))))
                    `((e-1 . ,e-1-equiv)
                      (e-2 . ,e-2))))
                 (t
                  `((e-1 . ,e-1-equiv)
                    (e-2 . ,e-2-equiv)))))
          ((equal (first e-2-equiv) 'rm-low-64)
           (cond ((equal (first e-1-equiv) 'rm-low-64)
                  `((e-2 . ,e-2-equiv)
                    (e-1 . ,e-1-equiv)))
                 ((equal (first e-1-equiv) 'set-accessed-bit)
                  (b* ((e-1
                        (if (equal (car (second e-1-equiv)) 'set-dirty-bit)
                            (second (second e-1-equiv))
                          (second e-1-equiv))))
                    `((e-2 . ,e-2-equiv)
                      (e-1 . ,e-1))))
                 ((equal (first e-1-equiv) 'set-dirty-bit)
                  (b* ((e-1
                        (if (equal (car (second e-1-equiv)) 'set-accessed-bit)
                            (second (second e-1-equiv))
                          (second e-1-equiv))))
                    `((e-2 . ,e-2-equiv)
                      (e-1 . ,e-1))))
                 (t
                  `((e-2 . ,e-2-equiv)
                    (e-1 . ,e-1-equiv)))))))

  (defthm xlate-equiv-entries-and-set-accessed-and/or-dirty-bit
    (implies
     (and (bind-free (find-xlate-equiv-entries e-1-equiv e-2-equiv) (e-1 e-2))
          (xlate-equiv-entries e-1 e-2)
          (or (equal e-1-equiv e-1)
              (equal e-1-equiv (set-accessed-bit e-1))
              (equal e-1-equiv (set-dirty-bit e-1))
              (equal e-1-equiv
                     (set-dirty-bit (set-accessed-bit e-1))))
          (or (equal e-2-equiv e-2)
              (equal e-2-equiv (set-accessed-bit e-2))
              (equal e-2-equiv (set-dirty-bit e-2))
              (equal e-2-equiv
                     (set-dirty-bit (set-accessed-bit e-2)))))
     (xlate-equiv-entries e-1-equiv e-2-equiv))
    :hints (("Goal" :in-theory (e/d* (set-accessed-bit
                                      set-dirty-bit)
                                     ()))))

  (defthmd xlate-equiv-entries-and-loghead
    (implies (and (xlate-equiv-entries e-1 e-2)
                  (syntaxp (quotep n))
                  (natp n)
                  (<= n 5))
             (equal (loghead n e-1) (loghead n e-2)))
    :hints (("Goal" :use ((:instance loghead-smaller-equality
                                     (x e-1) (y e-2) (n 5) (m n))))))

  (defthm xlate-equiv-entries-and-page-present
    (implies (xlate-equiv-entries e-1 e-2)
             (equal (page-present e-1) (page-present e-2)))
    :hints (("Goal"
             :use ((:instance xlate-equiv-entries-and-loghead
                              (e-1 e-1) (e-2 e-2) (n 1)))
             :in-theory (e/d* (page-present) ())))
    :rule-classes :congruence)

  (defthm xlate-equiv-entries-and-page-read-write
    (implies (xlate-equiv-entries e-1 e-2)
             (equal (page-read-write e-1) (page-read-write e-2)))
    :hints (("Goal"
             :use ((:instance loghead-smaller-and-logbitp
                              (e-1 e-1) (e-2 e-2) (m 1) (n 5)))
             :in-theory (e/d* (page-read-write) ())))
    :rule-classes :congruence)

  (defthm xlate-equiv-entries-and-page-user-supervisor
    (implies (xlate-equiv-entries e-1 e-2)
             (equal (page-user-supervisor e-1) (page-user-supervisor e-2)))
    :hints (("Goal"
             :use ((:instance loghead-smaller-and-logbitp
                              (e-1 e-1) (e-2 e-2) (m 2) (n 5)))
             :in-theory (e/d* (page-user-supervisor) ())))
    :rule-classes :congruence)

  (defthmd xlate-equiv-entries-and-logtail
    (implies (and (xlate-equiv-entries e-1 e-2)
                  (unsigned-byte-p 64 e-1)
                  (unsigned-byte-p 64 e-2)
                  (syntaxp (quotep n))
                  (natp n)
                  (<= 7 n)
                  (< n 64))
             (equal (logtail n e-1) (logtail n e-2)))
    :hints (("Goal" :use ((:instance logtail-bigger (n n) (m 7))))))

  (defthmd xlate-equiv-entries-and-page-size
    (implies (and (xlate-equiv-entries e-1 e-2)
                  (unsigned-byte-p 64 e-1)
                  (unsigned-byte-p 64 e-2))
             (equal (page-size e-1) (page-size e-2)))
    :hints (("Goal"
             :use ((:instance logtail-bigger-and-logbitp
                              (e-1 e-1) (e-2 e-2) (m 7) (n 7)))
             :in-theory (e/d* (page-size) ()))))

  (defthmd xlate-equiv-entries-and-page-execute-disable
    (implies (and (xlate-equiv-entries e-1 e-2)
                  (unsigned-byte-p 64 e-1)
                  (unsigned-byte-p 64 e-2))
             (equal (page-execute-disable e-1) (page-execute-disable e-2)))
    :hints (("Goal"
             :use ((:instance logtail-bigger-and-logbitp
                              (e-1 e-1) (e-2 e-2) (m 7) (n 63)))
             :in-theory (e/d* (page-execute-disable) ()))))

  (defthm xlate-equiv-entries-with-loghead-64
    (implies (xlate-equiv-entries e-1 e-2)
             (xlate-equiv-entries (loghead 64 e-1) (loghead 64 e-2)))
    :rule-classes :congruence))

;; ======================================================================

;; Gathering the physical addresses where paging structures are
;; located:

(define gather-pml4-table-qword-addresses (x86)
  :parents (gather-paging-structures)
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

  :parents (gather-paging-structures)

  :guard (and (not (xr :programmer-level-mode 0 x86))
              (physical-address-p superior-structure-paddr)
              (physical-address-p (+ 7 superior-structure-paddr)))

  :returns (list-of-addresses qword-paddr-listp)

  :short "Returns a list of all the qword addresses of the inferior
  paging structure referred by a paging entry at address
  @('superior-structure-paddr')"

  (b* ((superior-structure-entry
        (rm-low-64 superior-structure-paddr x86)))
    (if (and
         (equal (page-present  superior-structure-entry) 1)
         (equal (page-size superior-structure-entry) 0))
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
              ;; physical memory, something's wrong. Likely, the
              ;; paging structures haven't been set up correctly.
              nil))
          (create-qword-address-list 512 this-structure-base-addr))
      nil))
  ///
  (std::more-returns
   (list-of-addresses true-listp))

  (defthm gather-qword-addresses-corresponding-to-1-entry-xw-fld!=mem
    (implies (and (not (equal fld :mem))
                  (not (equal fld :programmer-level-mode)))
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

  (defthm gather-qword-addresses-corresponding-to-1-entry-wm-low-64-disjoint
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

  (defthm gather-qword-addresses-corresponding-to-1-entry-wm-low-64-superior-entry-addr
    (implies (and (equal index addr)
                  (xlate-equiv-entries (double-rewrite val) (rm-low-64 addr x86))
                  (unsigned-byte-p 64 val)
                  (physical-address-p index)
                  (physical-address-p (+ 7 index))
                  (not (xr :programmer-level-mode 0 x86))
                  (x86p x86))
             (equal (gather-qword-addresses-corresponding-to-1-entry
                     addr (wm-low-64 index val x86))
                    (gather-qword-addresses-corresponding-to-1-entry addr x86)))
    :hints (("Goal"
             :in-theory (e/d* (member-p)
                              (xlate-equiv-entries))
             :use ((:instance xlate-equiv-entries-and-page-present
                              (e-1 val)
                              (e-2 (rm-low-64 addr x86)))
                   (:instance xlate-equiv-entries-and-page-size
                              (e-1 val)
                              (e-2 (rm-low-64 addr x86)))
                   (:instance xlate-equiv-entries-and-logtail
                              (e-1 val)
                              (e-2 (rm-low-64 addr x86))
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
             :use ((:instance xlate-equiv-entries-and-page-size
                              (e-1 (rm-low-64 addr x86-equiv))
                              (e-2 (rm-low-64 addr x86)))
                   (:instance xlate-equiv-entries-and-page-present
                              (e-1 (rm-low-64 addr x86-equiv))
                              (e-2 (rm-low-64 addr x86)))
                   (:instance xlate-equiv-entries-and-logtail
                              (e-1 (rm-low-64 addr x86-equiv))
                              (e-2 (rm-low-64 addr x86))
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
                                     (gather-qword-addresses-corresponding-to-1-entry-wm-low-64-disjoint
                                      unsigned-byte-p))
             :use ((:instance gather-qword-addresses-corresponding-to-1-entry-wm-low-64-disjoint
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
    (implies (and (xlate-equiv-entries (double-rewrite val) (rm-low-64 addr x86))
                  (unsigned-byte-p 64 val)
                  (physical-address-p addr)
                  (physical-address-p (+ 7 addr))
                  (x86p x86)
                  (not (xr :programmer-level-mode 0 x86-equiv)))
             (equal (gather-qword-addresses-corresponding-to-1-entry
                     addr (wm-low-64 addr val x86-equiv))
                    (gather-qword-addresses-corresponding-to-1-entry addr x86)))
    :hints (("Goal" :in-theory (e/d* (gather-qword-addresses-corresponding-to-1-entry)
                                     ())
             :use ((:instance xlate-equiv-entries-and-page-size
                              (e-1 val)
                              (e-2 (rm-low-64 addr x86)))
                   (:instance xlate-equiv-entries-and-page-present
                              (e-1 val)
                              (e-2 (rm-low-64 addr x86)))
                   (:instance xlate-equiv-entries-and-logtail
                              (e-1 val)
                              (e-2 (rm-low-64 addr x86))
                              (n 12)))))))


(local
 (defthm member-p-member-list-p-mult-8-qword-paddr-list-listp-lemma
   (implies (and (member-list-p index (cdr addrs))
                 (mult-8-qword-paddr-list-listp addrs)
                 (no-duplicates-list-p addrs))
            (not (member-p index (car addrs))))
   :hints (("Goal" :in-theory (e/d* (disjoint-p
                                     member-list-p
                                     member-p)
                                    ())))))

(local
 (defthm member-p-mult-8-qword-paddr-listp-lemma
   (implies (and (mult-8-qword-paddr-listp addrs)
                 (not (member-p index addrs))
                 (physical-address-p index)
                 (equal (loghead 3 index) 0))
            (disjoint-p (addr-range 8 index)
                        (open-qword-paddr-list addrs)))
   :hints (("Goal" :in-theory (e/d* (disjoint-p
                                     member-p)
                                    ())))))

(local
 (defthm member-p-no-duplicates-p-lemma
   (implies (and (member-p index (cdr addrs))
                 (no-duplicates-p addrs))
            (not (equal index (car addrs))))))

(local
 (defthm member-list-p-mult-8-qword-paddr-list-listp-lemma
   (implies (and (mult-8-qword-paddr-list-listp addrs)
                 (not (member-list-p index addrs))
                 (physical-address-p index)
                 (equal (loghead 3 index) 0))
            (pairwise-disjoint-p-aux
             (addr-range 8 index)
             (open-qword-paddr-list-list addrs)))
   :hints (("Goal" :in-theory (e/d* (open-qword-paddr-list-list
                                     member-list-p)
                                    ())))))

(define gather-qword-addresses-corresponding-to-entries
  (superior-structure-paddrs x86)

  :parents (gather-paging-structures)

  :guard (and (not (xr :programmer-level-mode 0 x86))
              (qword-paddr-listp superior-structure-paddrs))

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
    (implies (and (not (equal fld :mem))
                  (not (equal fld :programmer-level-mode)))
             (equal (gather-qword-addresses-corresponding-to-entries
                     addrs (xw fld index val x86))
                    (gather-qword-addresses-corresponding-to-entries addrs x86)))
    :hints (("Goal"
             :in-theory (e/d* (gather-qword-addresses-corresponding-to-entries)
                              ()))))

  (defthm gather-qword-addresses-corresponding-to-entries-xw-fld=mem-disjoint
    (implies (and (not (member-p index (open-qword-paddr-list addrs)))
                  (physical-address-p index)
                  (mult-8-qword-paddr-listp addrs))
             (equal (gather-qword-addresses-corresponding-to-entries
                     addrs (xw :mem index val x86))
                    (gather-qword-addresses-corresponding-to-entries addrs x86)))
    :hints (("Goal"
             :in-theory (e/d* (gather-qword-addresses-corresponding-to-entries
                               ifix
                               pairwise-disjoint-p-aux
                               disjoint-p)
                              (addr-range
                               (addr-range))))))

  (defthm gather-qword-addresses-corresponding-to-entries-wm-low-64-disjoint
    (implies (and (disjoint-p (addr-range 8 index) (open-qword-paddr-list addrs))
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
   (defthm gather-qword-addresses-corresponding-to-entries-wm-low-64-superior-entry-addr-helper-2
     (implies (and (member-p index addrs)
                   (mult-8-qword-paddr-listp addrs)
                   (no-duplicates-p addrs)
                   (xlate-equiv-entries val (rm-low-64 index x86))
                   (unsigned-byte-p 64 val)
                   (physical-address-p index)
                   (x86p x86)
                   (not (xr :programmer-level-mode 0 x86)))
              (equal (gather-qword-addresses-corresponding-to-entries
                      addrs (wm-low-64 index val x86))
                     (gather-qword-addresses-corresponding-to-entries addrs x86)))
     :hints (("Goal"
              :in-theory (e/d* (member-p) (xlate-equiv-entries))))))

  (defthm gather-qword-addresses-corresponding-to-entries-wm-low-64-superior-entry-addr
    (implies (and (member-p index addrs)
                  (mult-8-qword-paddr-listp addrs)
                  (no-duplicates-p addrs)
                  (xlate-equiv-entries val (rm-low-64 index x86))
                  (unsigned-byte-p 64 val)
                  (x86p x86)
                  (not (xr :programmer-level-mode 0 x86)))
             (equal (gather-qword-addresses-corresponding-to-entries
                     addrs (wm-low-64 index val x86))
                    (gather-qword-addresses-corresponding-to-entries addrs x86)))
    :hints (("Goal"
             :in-theory (e/d* ()
                              (xlate-equiv-entries
                               gather-qword-addresses-corresponding-to-entries
                               member-p-and-mult-8-qword-paddr-listp))
             :use ((:instance member-p-and-mult-8-qword-paddr-listp
                              (index index)
                              (addrs addrs))))))

  (defthm gather-qword-addresses-corresponding-to-entries-wm-low-64-with-different-x86-disjoint
    (implies (and (equal (gather-qword-addresses-corresponding-to-entries addrs x86-equiv)
                         (gather-qword-addresses-corresponding-to-entries addrs x86))
                  (disjoint-p (addr-range 8 index) (open-qword-paddr-list addrs))
                  (physical-address-p index)
                  (mult-8-qword-paddr-listp addrs))
             (equal (gather-qword-addresses-corresponding-to-entries
                     addrs (wm-low-64 index val x86-equiv))
                    (gather-qword-addresses-corresponding-to-entries addrs x86)))
    :hints (("Goal"
             :in-theory (e/d* (gather-qword-addresses-corresponding-to-entries
                               ifix
                               pairwise-disjoint-p-aux
                               disjoint-p)
                              ()))))

  (defthm gather-qword-addresses-corresponding-to-entries-wm-low-64-with-different-x86
    (implies (and (equal (gather-qword-addresses-corresponding-to-entries addrs x86-equiv)
                         (gather-qword-addresses-corresponding-to-entries addrs x86))
                  (member-p index addrs)
                  (mult-8-qword-paddr-listp addrs)
                  (no-duplicates-p addrs)
                  (xlate-equiv-entries (double-rewrite val) (rm-low-64 index x86-equiv))
                  (unsigned-byte-p 64 val)
                  (x86p x86-equiv)
                  (not (xr :programmer-level-mode 0 x86-equiv)))
             (equal (gather-qword-addresses-corresponding-to-entries
                     addrs (wm-low-64 index val x86-equiv))
                    (gather-qword-addresses-corresponding-to-entries addrs x86)))
    :hints (("Goal"
             :in-theory (e/d* (gather-qword-addresses-corresponding-to-entries
                               member-p)
                              (unsigned-byte-p))))))

(define gather-qword-addresses-corresponding-to-list-of-entries
  (list-of-superior-structure-entries x86)

  :parents (gather-paging-structures)

  :guard (and (not (xr :programmer-level-mode 0 x86))
              (qword-paddr-list-listp list-of-superior-structure-entries))

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
    (implies (and (not (equal fld :mem))
                  (not (equal fld :programmer-level-mode)))
             (equal (gather-qword-addresses-corresponding-to-list-of-entries
                     addrs (xw fld index val x86))
                    (gather-qword-addresses-corresponding-to-list-of-entries addrs x86)))
    :hints (("Goal"
             :in-theory (e/d* (gather-qword-addresses-corresponding-to-list-of-entries)
                              ()))))

  (defthm gather-qword-addresses-corresponding-to-list-of-entries-xw-fld=mem-disjoint
    (implies (and (pairwise-disjoint-p-aux (list index) (open-qword-paddr-list-list addrs))
                  (mult-8-qword-paddr-list-listp addrs)
                  (physical-address-p index))
             (equal (gather-qword-addresses-corresponding-to-list-of-entries
                     addrs (xw :mem index val x86))
                    (gather-qword-addresses-corresponding-to-list-of-entries addrs x86)))
    :hints (("Goal" :in-theory (e/d* (disjoint-p) ()))))

  (defthm gather-qword-addresses-corresponding-to-list-of-entries-wm-low-64-disjoint
    (implies (and (pairwise-disjoint-p-aux
                   (addr-range 8 index)
                   (open-qword-paddr-list-list addrs))
                  (mult-8-qword-paddr-list-listp addrs)
                  (physical-address-p index))
             (equal (gather-qword-addresses-corresponding-to-list-of-entries
                     addrs (wm-low-64 index val x86))
                    (gather-qword-addresses-corresponding-to-list-of-entries addrs x86))))

  (defthm gather-qword-addresses-corresponding-to-list-of-entries-wm-low-64-superior-entry-addr
    (implies (and (member-list-p index addrs)
                  (mult-8-qword-paddr-list-listp addrs)
                  (no-duplicates-list-p addrs)
                  (xlate-equiv-entries (double-rewrite val) (rm-low-64 index x86))
                  (unsigned-byte-p 64 val)
                  (x86p x86)
                  (not (xr :programmer-level-mode 0 x86)))
             (equal (gather-qword-addresses-corresponding-to-list-of-entries
                     addrs (wm-low-64 index val x86))
                    (gather-qword-addresses-corresponding-to-list-of-entries addrs x86)))
    :hints (("Goal"
             :in-theory (e/d* (member-list-p)
                              (xlate-equiv-entries)))))

  (defthm gather-qword-addresses-corresponding-to-list-of-entries-wm-low-64-with-different-x86-disjoint
    (implies (and (equal (gather-qword-addresses-corresponding-to-list-of-entries addrs x86-equiv)
                         (gather-qword-addresses-corresponding-to-list-of-entries addrs x86))
                  (pairwise-disjoint-p-aux (addr-range 8 index)
                                           (open-qword-paddr-list-list addrs))
                  (mult-8-qword-paddr-list-listp addrs)
                  (physical-address-p index))
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
                  (xlate-equiv-entries (double-rewrite val) (rm-low-64 index x86-equiv))
                  (unsigned-byte-p 64 val)
                  (x86p x86-equiv)
                  (not (xr :programmer-level-mode 0 x86-equiv)))
             (equal (gather-qword-addresses-corresponding-to-list-of-entries
                     addrs (wm-low-64 index val x86-equiv))
                    (gather-qword-addresses-corresponding-to-list-of-entries addrs x86)))
    :hints (("Goal"
             :in-theory (e/d* (gather-qword-addresses-corresponding-to-list-of-entries
                               member-p)
                              (unsigned-byte-p))))))

(define gather-all-paging-structure-qword-addresses (x86)

  :parents (gather-paging-structures)

  :short "Returns a list of lists of qword addresses of all the active
  paging structures"

  :long "<p>We can use this function to state a common expectation
  from the supervisor-level code that initializes and manages the
  paging data structures: all the addresses of the paging structures
  \(i.e., the output of this function\) are
  @('pairwise-disjoint-p')</p>"

  :guard (not (xr :programmer-level-mode 0 x86))

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
                  (not (equal fld :ctr))
                  (not (equal fld :programmer-level-mode)))
             (equal (gather-all-paging-structure-qword-addresses
                     (xw fld index val x86))
                    (gather-all-paging-structure-qword-addresses x86))))

  (defthm gather-all-paging-structure-qword-addresses-xw-fld=ctr
    (implies (not (equal index *cr3*))
             (equal (gather-all-paging-structure-qword-addresses
                     (xw :ctr index val x86))
                    (gather-all-paging-structure-qword-addresses x86))))

  (defthm gather-all-paging-structure-qword-addresses-xw-fld=mem-disjoint
    (implies (and (equal addrs (gather-all-paging-structure-qword-addresses x86))
                  (mult-8-qword-paddr-list-listp addrs)
                  (pairwise-disjoint-p-aux (list index) (open-qword-paddr-list-list addrs))
                  (physical-address-p index))
             (equal (gather-all-paging-structure-qword-addresses (xw :mem index val x86))
                    addrs)))

  (defthm gather-all-paging-structure-qword-addresses-wm-low-64-disjoint
    (implies (and (equal addrs (gather-all-paging-structure-qword-addresses x86))
                  (mult-8-qword-paddr-list-listp addrs)
                  (pairwise-disjoint-p-aux
                   (addr-range 8 index)
                   (open-qword-paddr-list-list addrs))
                  (physical-address-p index))
             (equal (gather-all-paging-structure-qword-addresses
                     (wm-low-64 index val x86))
                    (gather-all-paging-structure-qword-addresses x86))))

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
       (implies (and (no-duplicates-p
                      (append x (acl2::flatten y) (acl2::flatten z) (acl2::flatten w)))
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
       (implies (and (no-duplicates-p
                      (append x (acl2::flatten y) (acl2::flatten z) (acl2::flatten w)))
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
       (implies (and (no-duplicates-p
                      (append x (acl2::flatten y) (acl2::flatten z) (acl2::flatten w)))
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

     (defthm member-list-p-and-pairwise-disjoint-p-aux-lemma-1
       (implies (and (no-duplicates-p
                      (append x (acl2::flatten y) (acl2::flatten z) (acl2::flatten w)))
                     (or (member-p i x)
                         (member-list-p i z)
                         (member-list-p i w))
                     (physical-address-p i)
                     (mult-8-qword-paddr-listp x)
                     (mult-8-qword-paddr-list-listp y)
                     (mult-8-qword-paddr-list-listp z)
                     (mult-8-qword-paddr-list-listp w))
                (pairwise-disjoint-p-aux
                 (addr-range 8 i)
                 (open-qword-paddr-list-list y)))
       :hints (("Goal"
                :use ((:instance no-duplicates-p-and-member-list-p-2-top))
                :in-theory (e/d* (pairwise-disjoint-p-aux)
                                 (no-duplicates-p-and-member-list-p-2-top)))))

     (defthm member-list-p-and-pairwise-disjoint-p-aux-lemma-2
       (implies (and (no-duplicates-p
                      (append x (acl2::flatten y) (acl2::flatten z) (acl2::flatten w)))
                     (or (member-p i x)
                         (member-list-p i y)
                         (member-list-p i w))
                     (physical-address-p i)
                     (mult-8-qword-paddr-listp x)
                     (mult-8-qword-paddr-list-listp y)
                     (mult-8-qword-paddr-list-listp z)
                     (mult-8-qword-paddr-list-listp w))
                (pairwise-disjoint-p-aux
                 (addr-range 8 i)
                 (open-qword-paddr-list-list z)))
       :hints (("Goal" :in-theory (e/d* (pairwise-disjoint-p-aux)
                                        ()))))))

  (defthm gather-all-paging-structure-qword-addresses-wm-low-64-entry-addr
    (implies (and (equal addrs (gather-all-paging-structure-qword-addresses x86))
                  (mult-8-qword-paddr-list-listp addrs)
                  (no-duplicates-list-p addrs)
                  (member-list-p index addrs)
                  (xlate-equiv-entries (double-rewrite val) (rm-low-64 index x86))
                  (unsigned-byte-p 64 val)
                  (x86p x86)
                  (not (xr :programmer-level-mode 0 x86)))
             (equal (gather-all-paging-structure-qword-addresses
                     (wm-low-64 index val x86))
                    (gather-all-paging-structure-qword-addresses x86)))))

;; ======================================================================

;; Compare the paging structures in two x86 states:

(define xlate-equiv-entries-at-qword-addresses-aux?
  (list-of-addresses-1 list-of-addresses-2 x86-1 x86-2)
  :parents (xlate-equiv-x86s)
  :non-executable t
  :guard (and (qword-paddr-listp list-of-addresses-1)
              (qword-paddr-listp list-of-addresses-2)
              (equal (len list-of-addresses-1)
                     (len list-of-addresses-2))
              (x86p x86-1)
              (x86p x86-2))

  (if (not (xr :programmer-level-mode 0 x86-1))
      (if (not (xr :programmer-level-mode 0 x86-2))

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

        nil)
    (xr :programmer-level-mode 0 x86-2))

  ///

  (defthm xlate-equiv-entries-at-qword-addresses-aux?-reflexive
    (implies (qword-paddr-listp a)
             (xlate-equiv-entries-at-qword-addresses-aux? a a x x)))

  (defthm xlate-equiv-entries-at-qword-addresses-aux?-commutative
    (implies (and (equal (len a) (len b))
                  (x86p x)
                  (x86p y))
             (equal (xlate-equiv-entries-at-qword-addresses-aux? a b x y)
                    (xlate-equiv-entries-at-qword-addresses-aux? b a y x))))

  (defthm xlate-equiv-entries-at-qword-addresses-aux?-transitive
    (implies (and (equal (len a) (len b))
                  (equal (len b) (len c))
                  (xlate-equiv-entries-at-qword-addresses-aux? a b x y)
                  (xlate-equiv-entries-at-qword-addresses-aux? b c y z))
             (xlate-equiv-entries-at-qword-addresses-aux? a c x z)))

  (defthm xlate-equiv-entries-at-qword-addresses-aux?-with-xw-fld!=mem
    (implies (and (not (equal fld :mem))
                  (not (equal fld :programmer-level-mode)))
             (equal (xlate-equiv-entries-at-qword-addresses-aux?
                     addrs-1 addrs-2
                     x86-1
                     (xw fld index val x86-2))
                    (xlate-equiv-entries-at-qword-addresses-aux?
                     addrs-1 addrs-2 x86-1 x86-2))))

  (defthm xlate-equiv-entries-at-qword-addresses-aux?-with-xw-mem-disjoint
    (implies (and (mult-8-qword-paddr-listp addrs)
                  (physical-address-p index)
                  (disjoint-p (list index)
                              (open-qword-paddr-list addrs)))
             (equal (xlate-equiv-entries-at-qword-addresses-aux?
                     addrs addrs
                     x86-1
                     (xw :mem index val x86-2))
                    (xlate-equiv-entries-at-qword-addresses-aux?
                     addrs addrs
                     x86-1
                     x86-2)))
    :hints (("Goal" :in-theory (e/d* (member-p) (xlate-equiv-entries)))))

  (defthm xlate-equiv-entries-at-qword-addresses-aux?-with-wm-low-64-disjoint
    (implies (and (mult-8-qword-paddr-listp addrs)
                  (physical-address-p index)
                  (disjoint-p (addr-range 8 index)
                              (open-qword-paddr-list addrs)))
             (equal (xlate-equiv-entries-at-qword-addresses-aux?
                     addrs addrs
                     x86-1
                     (wm-low-64 index val x86-2))
                    (xlate-equiv-entries-at-qword-addresses-aux?
                     addrs addrs
                     x86-1
                     x86-2)))
    :hints (("Goal" :in-theory (e/d* (member-p) (xlate-equiv-entries)))))

  (defthm xlate-equiv-entries-at-qword-addresses-aux?-with-wm-low-64-entry-addr
    (implies (and (mult-8-qword-paddr-listp addrs)
                  (no-duplicates-p addrs)
                  (member-p index addrs)
                  (xlate-equiv-entries (double-rewrite val) (rm-low-64 index x86-1))
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
                  (xlate-equiv-entries (double-rewrite val) (rm-low-64 index x86-2))
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
  :parents (xlate-equiv-x86s)
  :guard (and (qword-paddr-list-listp list-of-lists-of-addresses-1)
              (qword-paddr-list-listp list-of-lists-of-addresses-2)
              (equal (len list-of-lists-of-addresses-1)
                     (len list-of-lists-of-addresses-2))
              (x86p x86-1)
              (x86p x86-2))

  :non-executable t

  (if (not (xr :programmer-level-mode 0 x86-1))
      (if (not (xr :programmer-level-mode 0 x86-2))

          (if (endp list-of-lists-of-addresses-1)
              t
            (b* ((list-of-addresses-1 (car list-of-lists-of-addresses-1))
                 (list-of-addresses-2 (car list-of-lists-of-addresses-2))
                 ((when (not (equal (len list-of-addresses-1)
                                    (len list-of-addresses-2))))
                  nil))
              (and (xlate-equiv-entries-at-qword-addresses-aux?
                    list-of-addresses-1 list-of-addresses-2 x86-1
                    x86-2)
                   (xlate-equiv-entries-at-qword-addresses?
                    (cdr list-of-lists-of-addresses-1)
                    (cdr list-of-lists-of-addresses-2)
                    x86-1 x86-2))))
        nil)

    (xr :programmer-level-mode 0 x86-2))

  ///

  (defthm booleanp-xlate-equiv-entries-at-qword-addresses?
    (implies (x86p y)
             (booleanp (xlate-equiv-entries-at-qword-addresses? addrs addrs x y)))
    :rule-classes :type-prescription)

  (defthm xlate-equiv-entries-at-qword-addresses?-reflexive
    (implies (qword-paddr-list-listp a)
             (xlate-equiv-entries-at-qword-addresses? a a x x)))

  (defthm xlate-equiv-entries-at-qword-addresses?-commutative
    (implies (and (equal (len a) (len b))
                  (x86p x)
                  (x86p y))
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
                  (member-list-p index addrs)
                  (not (xr :programmer-level-mode 0 x86-1)))
             (xlate-equiv-entries (rm-low-64 index x86-1)
                                  (rm-low-64 index x86-2)))
    :hints (("Goal" :in-theory (e/d* (xlate-equiv-entries-at-qword-addresses?
                                      xlate-equiv-entries-at-qword-addresses-aux?
                                      member-list-p
                                      member-p)
                                     (xlate-equiv-entries)))))

  (defthm xlate-equiv-entries-at-qword-addresses?-with-xw-fld!=mem
    (implies (and (not (equal fld :mem))
                  (not (equal fld :programmer-level-mode)))
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

  (defthm xlate-equiv-entries-at-qword-addresses?-with-xw-mem-disjoint
    (implies (and (mult-8-qword-paddr-list-listp addrs)
                  (pairwise-disjoint-p-aux
                   (list index)
                   (open-qword-paddr-list-list addrs))
                  (physical-address-p index))
             (equal (xlate-equiv-entries-at-qword-addresses?
                     addrs
                     addrs x86-1 (xw :mem index val x86-2))
                    (xlate-equiv-entries-at-qword-addresses?
                     addrs addrs x86-1 x86-2)))
    :hints (("Goal" :in-theory (e/d* (xlate-equiv-entries-at-qword-addresses?
                                      member-p)
                                     (xlate-equiv-entries)))))

  (defthm xlate-equiv-entries-at-qword-addresses?-with-wm-low-64-disjoint
    (implies (and (mult-8-qword-paddr-list-listp addrs)
                  (pairwise-disjoint-p-aux
                   (addr-range 8 index)
                   (open-qword-paddr-list-list addrs))
                  (physical-address-p index))
             (equal (xlate-equiv-entries-at-qword-addresses?
                     addrs
                     addrs x86-1 (wm-low-64 index val x86-2))
                    (xlate-equiv-entries-at-qword-addresses?
                     addrs addrs x86-1 x86-2)))
    :hints (("Goal" :in-theory (e/d* (xlate-equiv-entries-at-qword-addresses?
                                      member-p member-list-p)
                                     (xlate-equiv-entries)))))

  (defthm xlate-equiv-entries-at-qword-addresses?-with-wm-low-64-entry-addr
    (implies (and (mult-8-qword-paddr-list-listp addrs)
                  (no-duplicates-list-p addrs)
                  (member-list-p index addrs)
                  (xlate-equiv-entries (double-rewrite val) (rm-low-64 index x86))
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
                  (xlate-equiv-entries (double-rewrite val) (rm-low-64 index x86-1))
                  (unsigned-byte-p 64 val)
                  (xlate-equiv-entries-at-qword-addresses? addrs addrs x86-1 x86-2)
                  (not (xr :programmer-level-mode 0 x86-1)))
             (xlate-equiv-entries-at-qword-addresses?
              addrs addrs
              x86-1
              (wm-low-64 index val x86-2)))
    :hints (("Goal"
             :use
             ((:instance member-list-p-and-mult-8-qword-paddr-list-listp)
              (:instance xlate-equiv-entries-at-qword-addresses?-with-wm-low-64-with-different-x86-helper))))))

(define good-paging-structures-x86p (x86)
  :parents (xlate-equiv-x86s reasoning-about-page-tables)
  (and (x86p x86)
       (not (xr :programmer-level-mode 0 x86))
       (let* ((paging-addresses (gather-all-paging-structure-qword-addresses x86)))
         (and (mult-8-qword-paddr-list-listp paging-addresses)
              (no-duplicates-list-p paging-addresses))))
  ///

  (defthm good-paging-structures-x86p-implies-mult-8-qword-paddr-list-listp-paging-structure-addrs
    (implies (good-paging-structures-x86p x86)
             (mult-8-qword-paddr-list-listp
              (gather-all-paging-structure-qword-addresses x86))))

  (defthm good-paging-structures-x86p-implies-x86p
    (implies (good-paging-structures-x86p x86)
             (x86p x86))
    :rule-classes (:rewrite :forward-chaining))

  (defthm good-paging-structures-x86p-implies-system-level-mode
    (implies (good-paging-structures-x86p x86)
             (not (xr :programmer-level-mode 0 x86)))
    :rule-classes (:rewrite :forward-chaining))

  (defthm good-paging-structures-x86p-xw-fld!=mem-and-ctr
    (implies (and (not (equal fld :mem))
                  (not (equal fld :ctr))
                  (not (equal fld :programmer-level-mode))
                  (x86p x86)
                  (x86p (xw fld index val x86)))
             (equal (good-paging-structures-x86p (xw fld index val x86))
                    (good-paging-structures-x86p x86))))

  (defthm good-paging-structures-x86p-and-xw-mem-disjoint
    (implies (and (pairwise-disjoint-p-aux
                   (list index)
                   (open-qword-paddr-list-list
                    (gather-all-paging-structure-qword-addresses x86)))
                  (good-paging-structures-x86p x86)
                  (physical-address-p index)
                  (unsigned-byte-p 8 val))
             (good-paging-structures-x86p (xw :mem index val x86))))

  (defthm good-paging-structures-x86p-and-wm-low-64-disjoint
    (implies (and (pairwise-disjoint-p-aux
                   (addr-range 8 index)
                   (open-qword-paddr-list-list
                    (gather-all-paging-structure-qword-addresses x86)))
                  (good-paging-structures-x86p x86)
                  (physical-address-p index))
             (good-paging-structures-x86p (wm-low-64 index val x86))))

  (defthm good-paging-structures-x86p-and-wm-low-64-entry-addr
    (implies (and (equal addrs (gather-all-paging-structure-qword-addresses x86))
                  (member-list-p index addrs)
                  (xlate-equiv-entries val (rm-low-64 index x86))
                  (unsigned-byte-p 64 val)
                  (x86p (wm-low-64 index val x86))
                  (good-paging-structures-x86p x86))
             (good-paging-structures-x86p (wm-low-64 index val x86)))))

;; ======================================================================

;; Defining xlate-equiv-x86s:

(define all-rgfs-equal (x86-1 x86-2)
  :parents (xlate-equiv-x86s)
  :guard (and (x86p x86-1)
              (x86p x86-2))
  :non-executable t

  :prepwork
  ((define all-rgfs-equal-aux (i x86-1 x86-2)
     :parents (all-rgfs-equal)
     :guard (and (natp i)
                 (<= i *64-bit-general-purpose-registers-len*)
                 (x86p x86-1)
                 (x86p x86-2))
     :non-executable t
     :enabled t
     (if (zp i)
         (equal (xr :rgf i x86-1) (xr :rgf i x86-2))
       (and (equal (xr :rgf (1- i) x86-1) (xr :rgf (1- i) x86-2))
            (all-rgfs-equal-aux (1- i) x86-1 x86-2)))

     ///

     (defthm all-rgfs-equal-aux-open
       (implies (and (all-rgfs-equal-aux i x86-1 x86-2)
                     (natp i)
                     (natp j)
                     (< j i))
                (equal (xr :rgf j x86-1) (xr :rgf j x86-2))))

     (defthm all-rgfs-equal-aux-is-reflexive
       (all-rgfs-equal-aux i x x))

     (defthm all-rgfs-equal-aux-is-commutative
       (implies (all-rgfs-equal-aux i x y)
                (all-rgfs-equal-aux i y x)))

     (defthm all-rgfs-equal-aux-is-transitive
       (implies (and (all-rgfs-equal-aux i x y)
                     (all-rgfs-equal-aux i y z))
                (all-rgfs-equal-aux i x z)))

     (defthm all-rgfs-equal-aux-and-xw
       (implies (not (equal fld :rgf))
                (equal (all-rgfs-equal-aux i (xw fld index val x) y)
                       (all-rgfs-equal-aux i x y))))

     (defthm all-rgfs-equal-aux-and-wm-low-64
       (equal (all-rgfs-equal-aux i (wm-low-64 index val x) y)
              (all-rgfs-equal-aux i x y)))))

  (if (good-paging-structures-x86p x86-1)
      (if (good-paging-structures-x86p x86-2)
          (all-rgfs-equal-aux *64-bit-general-purpose-registers-len* x86-1 x86-2)
        nil)
    (not (good-paging-structures-x86p x86-2)))

  ///

  (defequiv all-rgfs-equal)

  (defthm all-rgfs-equal-and-xw
    (implies (and (not (equal fld :rgf))
                  (good-paging-structures-x86p x)
                  (good-paging-structures-x86p (xw fld index val x)))
             (equal (all-rgfs-equal (xw fld index val x) y)
                    (all-rgfs-equal (double-rewrite x) y))))

  (defthm all-rgfs-equal-and-wm-low-64
    (implies (and (good-paging-structures-x86p x)
                  (good-paging-structures-x86p (wm-low-64 index val x)))
             (equal (all-rgfs-equal (wm-low-64 index val x) y)
                    (all-rgfs-equal (double-rewrite x) y)))))

(define all-seg-visibles-equal (x86-1 x86-2)
  :parents (xlate-equiv-x86s)
  :guard (and (x86p x86-1)
              (x86p x86-2))
  :non-executable t

  :prepwork
  ((define all-seg-visibles-equal-aux (i x86-1 x86-2)
     :parents (all-seg-visibles-equal)
     :guard (and (natp i)
                 (<= i *segment-register-names-len*)
                 (x86p x86-1)
                 (x86p x86-2))
     :non-executable t
     :enabled t
     (if (zp i)
         (equal (xr :seg-visible i x86-1) (xr :seg-visible i x86-2))
       (and (equal (xr :seg-visible (1- i) x86-1) (xr :seg-visible (1- i) x86-2))
            (all-seg-visibles-equal-aux (1- i) x86-1 x86-2)))

     ///

     (defthm all-seg-visibles-equal-aux-open
       (implies (and (all-seg-visibles-equal-aux i x86-1 x86-2)
                     (natp i)
                     (natp j)
                     (< j i))
                (equal (xr :seg-visible j x86-1) (xr :seg-visible j x86-2))))

     (defthm all-seg-visibles-equal-aux-is-reflexive
       (all-seg-visibles-equal-aux i x x))

     (defthm all-seg-visibles-equal-aux-is-commutative
       (implies (all-seg-visibles-equal-aux i x y)
                (all-seg-visibles-equal-aux i y x)))

     (defthm all-seg-visibles-equal-aux-is-transitive
       (implies (and (all-seg-visibles-equal-aux i x y)
                     (all-seg-visibles-equal-aux i y z))
                (all-seg-visibles-equal-aux i x z)))

     (defthm all-seg-visibles-equal-aux-and-xw
       (implies (not (equal fld :seg-visible))
                (equal (all-seg-visibles-equal-aux i (xw fld index val x) y)
                       (all-seg-visibles-equal-aux i x y))))

     (defthm all-seg-visibles-equal-aux-and-wm-low-64
       (equal (all-seg-visibles-equal-aux i (wm-low-64 index val x) y)
              (all-seg-visibles-equal-aux i x y)))))

  (if (good-paging-structures-x86p x86-1)
      (if (good-paging-structures-x86p x86-2)
          (all-seg-visibles-equal-aux *segment-register-names-len* x86-1 x86-2)
        nil)
    (not (good-paging-structures-x86p x86-2)))

  ///

  (defequiv all-seg-visibles-equal)

  (defthm all-seg-visibles-equal-and-xw
    (implies (and (not (equal fld :seg-visible))
                  (good-paging-structures-x86p x)
                  (good-paging-structures-x86p (xw fld index val x)))
             (equal (all-seg-visibles-equal (xw fld index val x) y)
                    (all-seg-visibles-equal (double-rewrite x) y))))

  (defthm all-seg-visibles-equal-and-wm-low-64
    (implies (and (good-paging-structures-x86p x)
                  (good-paging-structures-x86p (wm-low-64 index val x)))
             (equal (all-seg-visibles-equal (wm-low-64 index val x) y)
                    (all-seg-visibles-equal (double-rewrite x) y)))))

(define all-seg-hiddens-equal (x86-1 x86-2)
  :parents (xlate-equiv-x86s)
  :guard (and (x86p x86-1)
              (x86p x86-2))
  :non-executable t

  :prepwork
  ((define all-seg-hiddens-equal-aux (i x86-1 x86-2)
     :parents (all-seg-hiddens-equal)
     :guard (and (natp i)
                 (<= i *segment-register-names-len*)
                 (x86p x86-1)
                 (x86p x86-2))
     :non-executable t
     :enabled t
     (if (zp i)
         (equal (xr :seg-hidden i x86-1) (xr :seg-hidden i x86-2))
       (and (equal (xr :seg-hidden (1- i) x86-1) (xr :seg-hidden (1- i) x86-2))
            (all-seg-hiddens-equal-aux (1- i) x86-1 x86-2)))

     ///

     (defthm all-seg-hiddens-equal-aux-open
       (implies (and (all-seg-hiddens-equal-aux i x86-1 x86-2)
                     (natp i)
                     (natp j)
                     (< j i))
                (equal (xr :seg-hidden j x86-1) (xr :seg-hidden j x86-2))))

     (defthm all-seg-hiddens-equal-aux-is-reflexive
       (all-seg-hiddens-equal-aux i x x))

     (defthm all-seg-hiddens-equal-aux-is-commutative
       (implies (all-seg-hiddens-equal-aux i x y)
                (all-seg-hiddens-equal-aux i y x)))

     (defthm all-seg-hiddens-equal-aux-is-transitive
       (implies (and (all-seg-hiddens-equal-aux i x y)
                     (all-seg-hiddens-equal-aux i y z))
                (all-seg-hiddens-equal-aux i x z)))

     (defthm all-seg-hiddens-equal-aux-and-xw
       (implies (not (equal fld :seg-hidden))
                (equal (all-seg-hiddens-equal-aux i (xw fld index val x) y)
                       (all-seg-hiddens-equal-aux i x y))))

     (defthm all-seg-hiddens-equal-aux-and-wm-low-64
       (equal (all-seg-hiddens-equal-aux i (wm-low-64 index val x) y)
              (all-seg-hiddens-equal-aux i x y)))))

  (if (good-paging-structures-x86p x86-1)
      (if (good-paging-structures-x86p x86-2)
          (all-seg-hiddens-equal-aux *segment-register-names-len* x86-1 x86-2)
        nil)
    (not (good-paging-structures-x86p x86-2)))

  ///

  (defequiv all-seg-hiddens-equal)

  (defthm all-seg-hiddens-equal-and-xw
    (implies (and (not (equal fld :seg-hidden))
                  (good-paging-structures-x86p x)
                  (good-paging-structures-x86p (xw fld index val x)))
             (equal (all-seg-hiddens-equal (xw fld index val x) y)
                    (all-seg-hiddens-equal (double-rewrite x) y))))

  (defthm all-seg-hiddens-equal-and-wm-low-64
    (implies (and (good-paging-structures-x86p x)
                  (good-paging-structures-x86p (wm-low-64 index val x)))
             (equal (all-seg-hiddens-equal (wm-low-64 index val x) y)
                    (all-seg-hiddens-equal (double-rewrite x) y)))))

(define all-strs-equal (x86-1 x86-2)
  :parents (xlate-equiv-x86s)
  :guard (and (x86p x86-1)
              (x86p x86-2))
  :non-executable t

  :prepwork
  ((define all-strs-equal-aux (i x86-1 x86-2)
     :parents (all-strs-equal)
     :guard (and (natp i)
                 (<= i *gdtr-idtr-names-len*)
                 (x86p x86-1)
                 (x86p x86-2))
     :non-executable t
     :enabled t
     (if (zp i)
         (equal (xr :str i x86-1) (xr :str i x86-2))
       (and (equal (xr :str (1- i) x86-1) (xr :str (1- i) x86-2))
            (all-strs-equal-aux (1- i) x86-1 x86-2)))

     ///

     (defthm all-strs-equal-aux-open
       (implies (and (all-strs-equal-aux i x86-1 x86-2)
                     (natp i)
                     (natp j)
                     (< j i))
                (equal (xr :str j x86-1) (xr :str j x86-2))))

     (defthm all-strs-equal-aux-is-reflexive
       (all-strs-equal-aux i x x))

     (defthm all-strs-equal-aux-is-commutative
       (implies (all-strs-equal-aux i x y)
                (all-strs-equal-aux i y x)))

     (defthm all-strs-equal-aux-is-transitive
       (implies (and (all-strs-equal-aux i x y)
                     (all-strs-equal-aux i y z))
                (all-strs-equal-aux i x z)))

     (defthm all-strs-equal-aux-and-xw
       (implies (not (equal fld :str))
                (equal (all-strs-equal-aux i (xw fld index val x) y)
                       (all-strs-equal-aux i x y))))

     (defthm all-strs-equal-aux-and-wm-low-64
       (equal (all-strs-equal-aux i (wm-low-64 index val x) y)
              (all-strs-equal-aux i x y)))))

  (if (good-paging-structures-x86p x86-1)
      (if (good-paging-structures-x86p x86-2)
          (all-strs-equal-aux *gdtr-idtr-names-len* x86-1 x86-2)
        nil)
    (not (good-paging-structures-x86p x86-2)))

  ///

  (defequiv all-strs-equal)

  (defthm all-strs-equal-and-xw
    (implies (and (not (equal fld :str))
                  (good-paging-structures-x86p x)
                  (good-paging-structures-x86p (xw fld index val x)))
             (equal (all-strs-equal (xw fld index val x) y)
                    (all-strs-equal (double-rewrite x) y))))

  (defthm all-strs-equal-and-wm-low-64
    (implies (and (good-paging-structures-x86p x)
                  (good-paging-structures-x86p (wm-low-64 index val x)))
             (equal (all-strs-equal (wm-low-64 index val x) y)
                    (all-strs-equal (double-rewrite x) y)))))

(define all-ssr-visibles-equal (x86-1 x86-2)
  :parents (xlate-equiv-x86s)
  :guard (and (x86p x86-1)
              (x86p x86-2))
  :non-executable t

  :prepwork
  ((define all-ssr-visibles-equal-aux (i x86-1 x86-2)
     :parents (all-ssr-visibles-equal)
     :guard (and (natp i)
                 (<= i *ldtr-tr-names-len*)
                 (x86p x86-1)
                 (x86p x86-2))
     :non-executable t
     :enabled t
     (if (zp i)
         (equal (xr :ssr-visible i x86-1) (xr :ssr-visible i x86-2))
       (and (equal (xr :ssr-visible (1- i) x86-1) (xr :ssr-visible (1- i) x86-2))
            (all-ssr-visibles-equal-aux (1- i) x86-1 x86-2)))

     ///

     (defthm all-ssr-visibles-equal-aux-open
       (implies (and (all-ssr-visibles-equal-aux i x86-1 x86-2)
                     (natp i)
                     (natp j)
                     (< j i))
                (equal (xr :ssr-visible j x86-1) (xr :ssr-visible j x86-2))))

     (defthm all-ssr-visibles-equal-aux-is-reflexive
       (all-ssr-visibles-equal-aux i x x))

     (defthm all-ssr-visibles-equal-aux-is-commutative
       (implies (all-ssr-visibles-equal-aux i x y)
                (all-ssr-visibles-equal-aux i y x)))

     (defthm all-ssr-visibles-equal-aux-is-transitive
       (implies (and (all-ssr-visibles-equal-aux i x y)
                     (all-ssr-visibles-equal-aux i y z))
                (all-ssr-visibles-equal-aux i x z)))

     (defthm all-ssr-visibles-equal-aux-and-xw
       (implies (not (equal fld :ssr-visible))
                (equal (all-ssr-visibles-equal-aux i (xw fld index val x) y)
                       (all-ssr-visibles-equal-aux i x y))))

     (defthm all-ssr-visibles-equal-aux-and-wm-low-64
       (equal (all-ssr-visibles-equal-aux i (wm-low-64 index val x) y)
              (all-ssr-visibles-equal-aux i x y)))))

  (if (good-paging-structures-x86p x86-1)
      (if (good-paging-structures-x86p x86-2)
          (all-ssr-visibles-equal-aux *ldtr-tr-names-len* x86-1 x86-2)
        nil)
    (not (good-paging-structures-x86p x86-2)))

  ///

  (defequiv all-ssr-visibles-equal)

  (defthm all-ssr-visibles-equal-and-xw
    (implies (and (not (equal fld :ssr-visible))
                  (good-paging-structures-x86p x)
                  (good-paging-structures-x86p (xw fld index val x)))
             (equal (all-ssr-visibles-equal (xw fld index val x) y)
                    (all-ssr-visibles-equal (double-rewrite x) y))))

  (defthm all-ssr-visibles-equal-and-wm-low-64
    (implies (and (good-paging-structures-x86p x)
                  (good-paging-structures-x86p (wm-low-64 index val x)))
             (equal (all-ssr-visibles-equal (wm-low-64 index val x) y)
                    (all-ssr-visibles-equal (double-rewrite x) y)))))

(define all-ssr-hiddens-equal (x86-1 x86-2)
  :parents (xlate-equiv-x86s)
  :guard (and (x86p x86-1)
              (x86p x86-2))
  :non-executable t

  :prepwork
  ((define all-ssr-hiddens-equal-aux (i x86-1 x86-2)
     :parents (all-ssr-hiddens-equal)
     :guard (and (natp i)
                 (<= i *ldtr-tr-names-len*)
                 (x86p x86-1)
                 (x86p x86-2))
     :non-executable t
     :enabled t
     (if (zp i)
         (equal (xr :ssr-hidden i x86-1) (xr :ssr-hidden i x86-2))
       (and (equal (xr :ssr-hidden (1- i) x86-1) (xr :ssr-hidden (1- i) x86-2))
            (all-ssr-hiddens-equal-aux (1- i) x86-1 x86-2)))

     ///

     (defthm all-ssr-hiddens-equal-aux-open
       (implies (and (all-ssr-hiddens-equal-aux i x86-1 x86-2)
                     (natp i)
                     (natp j)
                     (< j i))
                (equal (xr :ssr-hidden j x86-1) (xr :ssr-hidden j x86-2))))

     (defthm all-ssr-hiddens-equal-aux-is-reflexive
       (all-ssr-hiddens-equal-aux i x x))

     (defthm all-ssr-hiddens-equal-aux-is-commutative
       (implies (all-ssr-hiddens-equal-aux i x y)
                (all-ssr-hiddens-equal-aux i y x)))

     (defthm all-ssr-hiddens-equal-aux-is-transitive
       (implies (and (all-ssr-hiddens-equal-aux i x y)
                     (all-ssr-hiddens-equal-aux i y z))
                (all-ssr-hiddens-equal-aux i x z)))

     (defthm all-ssr-hiddens-equal-aux-and-xw
       (implies (not (equal fld :ssr-hidden))
                (equal (all-ssr-hiddens-equal-aux i (xw fld index val x) y)
                       (all-ssr-hiddens-equal-aux i x y))))

     (defthm all-ssr-hiddens-equal-aux-and-wm-low-64
       (equal (all-ssr-hiddens-equal-aux i (wm-low-64 index val x) y)
              (all-ssr-hiddens-equal-aux i x y)))))

  (if (good-paging-structures-x86p x86-1)
      (if (good-paging-structures-x86p x86-2)
          (all-ssr-hiddens-equal-aux *ldtr-tr-names-len* x86-1 x86-2)
        nil)
    (not (good-paging-structures-x86p x86-2)))

  ///

  (defequiv all-ssr-hiddens-equal)

  (defthm all-ssr-hiddens-equal-and-xw
    (implies (and (not (equal fld :ssr-hidden))
                  (good-paging-structures-x86p x)
                  (good-paging-structures-x86p (xw fld index val x)))
             (equal (all-ssr-hiddens-equal (xw fld index val x) y)
                    (all-ssr-hiddens-equal (double-rewrite x) y))))

  (defthm all-ssr-hiddens-equal-and-wm-low-64
    (implies (and (good-paging-structures-x86p x)
                  (good-paging-structures-x86p (wm-low-64 index val x)))
             (equal (all-ssr-hiddens-equal (wm-low-64 index val x) y)
                    (all-ssr-hiddens-equal (double-rewrite x) y)))))

(define all-ctrs-equal (x86-1 x86-2)
  :parents (xlate-equiv-x86s)
  :guard (and (x86p x86-1)
              (x86p x86-2))
  :non-executable t

  :prepwork
  ((define all-ctrs-equal-aux (i x86-1 x86-2)
     :parents (all-ctrs-equal)
     :guard (and (natp i)
                 (<= i *control-register-names-len*)
                 (x86p x86-1)
                 (x86p x86-2))
     :non-executable t
     :enabled t
     (if (zp i)
         (equal (xr :ctr i x86-1) (xr :ctr i x86-2))
       (and (equal (xr :ctr (1- i) x86-1) (xr :ctr (1- i) x86-2))
            (all-ctrs-equal-aux (1- i) x86-1 x86-2)))

     ///

     (defthm all-ctrs-equal-aux-open
       (implies (and (all-ctrs-equal-aux i x86-1 x86-2)
                     (natp i)
                     (natp j)
                     (< j i))
                (equal (xr :ctr j x86-1) (xr :ctr j x86-2))))

     (defthm all-ctrs-equal-aux-is-reflexive
       (all-ctrs-equal-aux i x x))

     (defthm all-ctrs-equal-aux-is-commutative
       (implies (all-ctrs-equal-aux i x y)
                (all-ctrs-equal-aux i y x)))

     (defthm all-ctrs-equal-aux-is-transitive
       (implies (and (all-ctrs-equal-aux i x y)
                     (all-ctrs-equal-aux i y z))
                (all-ctrs-equal-aux i x z)))

     (defthm all-ctrs-equal-aux-and-xw
       (implies (not (equal fld :ctr))
                (equal (all-ctrs-equal-aux i (xw fld index val x) y)
                       (all-ctrs-equal-aux i x y))))

     (defthm all-ctrs-equal-aux-and-wm-low-64
       (equal (all-ctrs-equal-aux i (wm-low-64 index val x) y)
              (all-ctrs-equal-aux i x y)))))

  (if (good-paging-structures-x86p x86-1)
      (if (good-paging-structures-x86p x86-2)
          (all-ctrs-equal-aux *control-register-names-len* x86-1 x86-2)
        nil)
    (not (good-paging-structures-x86p x86-2)))

  ///

  (defequiv all-ctrs-equal)

  (defthm all-ctrs-equal-and-xw
    (implies (and (not (equal fld :ctr))
                  (good-paging-structures-x86p x)
                  (good-paging-structures-x86p (xw fld index val x)))
             (equal (all-ctrs-equal (xw fld index val x) y)
                    (all-ctrs-equal (double-rewrite x) y))))

  (defthm all-ctrs-equal-and-wm-low-64
    (implies (and (good-paging-structures-x86p x)
                  (good-paging-structures-x86p (wm-low-64 index val x)))
             (equal (all-ctrs-equal (wm-low-64 index val x) y)
                    (all-ctrs-equal (double-rewrite x) y)))))

(define all-dbgs-equal (x86-1 x86-2)
  :parents (xlate-equiv-x86s)
  :guard (and (x86p x86-1)
              (x86p x86-2))
  :non-executable t

  :prepwork
  ((define all-dbgs-equal-aux (i x86-1 x86-2)
     :parents (all-dbgs-equal)
     :guard (and (natp i)
                 (<= i *debug-register-names-len*)
                 (x86p x86-1)
                 (x86p x86-2))
     :non-executable t
     :enabled t
     (if (zp i)
         (equal (xr :dbg i x86-1) (xr :dbg i x86-2))
       (and (equal (xr :dbg (1- i) x86-1) (xr :dbg (1- i) x86-2))
            (all-dbgs-equal-aux (1- i) x86-1 x86-2)))

     ///

     (defthm all-dbgs-equal-aux-open
       (implies (and (all-dbgs-equal-aux i x86-1 x86-2)
                     (natp i)
                     (natp j)
                     (< j i))
                (equal (xr :dbg j x86-1) (xr :dbg j x86-2))))

     (defthm all-dbgs-equal-aux-is-reflexive
       (all-dbgs-equal-aux i x x))

     (defthm all-dbgs-equal-aux-is-commutative
       (implies (all-dbgs-equal-aux i x y)
                (all-dbgs-equal-aux i y x)))

     (defthm all-dbgs-equal-aux-is-transitive
       (implies (and (all-dbgs-equal-aux i x y)
                     (all-dbgs-equal-aux i y z))
                (all-dbgs-equal-aux i x z)))

     (defthm all-dbgs-equal-aux-and-xw
       (implies (not (equal fld :dbg))
                (equal (all-dbgs-equal-aux i (xw fld index val x) y)
                       (all-dbgs-equal-aux i x y))))

     (defthm all-dbgs-equal-aux-and-wm-low-64
       (equal (all-dbgs-equal-aux i (wm-low-64 index val x) y)
              (all-dbgs-equal-aux i x y)))))

  (if (good-paging-structures-x86p x86-1)
      (if (good-paging-structures-x86p x86-2)
          (all-dbgs-equal-aux *debug-register-names-len* x86-1 x86-2)
        nil)
    (not (good-paging-structures-x86p x86-2)))

  ///

  (defequiv all-dbgs-equal)

  (defthm all-dbgs-equal-and-xw
    (implies (and (not (equal fld :dbg))
                  (good-paging-structures-x86p x)
                  (good-paging-structures-x86p (xw fld index val x)))
             (equal (all-dbgs-equal (xw fld index val x) y)
                    (all-dbgs-equal (double-rewrite x) y))))

  (defthm all-dbgs-equal-and-wm-low-64
    (implies (and (good-paging-structures-x86p x)
                  (good-paging-structures-x86p (wm-low-64 index val x)))
             (equal (all-dbgs-equal (wm-low-64 index val x) y)
                    (all-dbgs-equal (double-rewrite x) y)))))

(define all-fp-datas-equal (x86-1 x86-2)
  :parents (xlate-equiv-x86s)
  :guard (and (x86p x86-1)
              (x86p x86-2))
  :non-executable t

  :prepwork
  ((define all-fp-datas-equal-aux (i x86-1 x86-2)
     :parents (all-fp-datas-equal)
     :guard (and (natp i)
                 (<= i *fp-data-register-names-len*)
                 (x86p x86-1)
                 (x86p x86-2))
     :non-executable t
     :enabled t
     (if (zp i)
         (equal (xr :fp-data i x86-1) (xr :fp-data i x86-2))
       (and (equal (xr :fp-data (1- i) x86-1) (xr :fp-data (1- i) x86-2))
            (all-fp-datas-equal-aux (1- i) x86-1 x86-2)))

     ///

     (defthm all-fp-datas-equal-aux-open
       (implies (and (all-fp-datas-equal-aux i x86-1 x86-2)
                     (natp i)
                     (natp j)
                     (< j i))
                (equal (xr :fp-data j x86-1) (xr :fp-data j x86-2))))

     (defthm all-fp-datas-equal-aux-is-reflexive
       (all-fp-datas-equal-aux i x x))

     (defthm all-fp-datas-equal-aux-is-commutative
       (implies (all-fp-datas-equal-aux i x y)
                (all-fp-datas-equal-aux i y x)))

     (defthm all-fp-datas-equal-aux-is-transitive
       (implies (and (all-fp-datas-equal-aux i x y)
                     (all-fp-datas-equal-aux i y z))
                (all-fp-datas-equal-aux i x z)))

     (defthm all-fp-datas-equal-aux-and-xw
       (implies (not (equal fld :fp-data))
                (equal (all-fp-datas-equal-aux i (xw fld index val x) y)
                       (all-fp-datas-equal-aux i x y))))

     (defthm all-fp-datas-equal-aux-and-wm-low-64
       (equal (all-fp-datas-equal-aux i (wm-low-64 index val x) y)
              (all-fp-datas-equal-aux i x y)))))

  (if (good-paging-structures-x86p x86-1)
      (if (good-paging-structures-x86p x86-2)
          (all-fp-datas-equal-aux *fp-data-register-names-len* x86-1 x86-2)
        nil)
    (not (good-paging-structures-x86p x86-2)))

  ///

  (defequiv all-fp-datas-equal)

  (defthm all-fp-datas-equal-and-xw
    (implies (and (not (equal fld :fp-data))
                  (good-paging-structures-x86p x)
                  (good-paging-structures-x86p (xw fld index val x)))
             (equal (all-fp-datas-equal (xw fld index val x) y)
                    (all-fp-datas-equal (double-rewrite x) y))))

  (defthm all-fp-datas-equal-and-wm-low-64
    (implies (and (good-paging-structures-x86p x)
                  (good-paging-structures-x86p (wm-low-64 index val x)))
             (equal (all-fp-datas-equal (wm-low-64 index val x) y)
                    (all-fp-datas-equal (double-rewrite x) y)))))

(define all-xmms-equal (x86-1 x86-2)
  :parents (xlate-equiv-x86s)
  :guard (and (x86p x86-1)
              (x86p x86-2))
  :non-executable t

  :prepwork
  ((define all-xmms-equal-aux (i x86-1 x86-2)
     :parents (all-xmms-equal)
     :guard (and (natp i)
                 (<= i *xmm-register-names-len*)
                 (x86p x86-1)
                 (x86p x86-2))
     :non-executable t
     :enabled t
     (if (zp i)
         (equal (xr :xmm i x86-1) (xr :xmm i x86-2))
       (and (equal (xr :xmm (1- i) x86-1) (xr :xmm (1- i) x86-2))
            (all-xmms-equal-aux (1- i) x86-1 x86-2)))

     ///

     (defthm all-xmms-equal-aux-open
       (implies (and (all-xmms-equal-aux i x86-1 x86-2)
                     (natp i)
                     (natp j)
                     (< j i))
                (equal (xr :xmm j x86-1) (xr :xmm j x86-2))))

     (defthm all-xmms-equal-aux-is-reflexive
       (all-xmms-equal-aux i x x))

     (defthm all-xmms-equal-aux-is-commutative
       (implies (all-xmms-equal-aux i x y)
                (all-xmms-equal-aux i y x)))

     (defthm all-xmms-equal-aux-is-transitive
       (implies (and (all-xmms-equal-aux i x y)
                     (all-xmms-equal-aux i y z))
                (all-xmms-equal-aux i x z)))

     (defthm all-xmms-equal-aux-and-xw
       (implies (not (equal fld :xmm))
                (equal (all-xmms-equal-aux i (xw fld index val x) y)
                       (all-xmms-equal-aux i x y))))

     (defthm all-xmms-equal-aux-and-wm-low-64
       (equal (all-xmms-equal-aux i (wm-low-64 index val x) y)
              (all-xmms-equal-aux i x y)))))

  (if (good-paging-structures-x86p x86-1)
      (if (good-paging-structures-x86p x86-2)
          (all-xmms-equal-aux *xmm-register-names-len* x86-1 x86-2)
        nil)
    (not (good-paging-structures-x86p x86-2)))

  ///

  (defequiv all-xmms-equal)

  (defthm all-xmms-equal-and-xw
    (implies (and (not (equal fld :xmm))
                  (good-paging-structures-x86p x)
                  (good-paging-structures-x86p (xw fld index val x)))
             (equal (all-xmms-equal (xw fld index val x) y)
                    (all-xmms-equal (double-rewrite x) y))))

  (defthm all-xmms-equal-and-wm-low-64
    (implies (and (good-paging-structures-x86p x)
                  (good-paging-structures-x86p (wm-low-64 index val x)))
             (equal (all-xmms-equal (wm-low-64 index val x) y)
                    (all-xmms-equal (double-rewrite x) y)))))

(define all-msrs-equal (x86-1 x86-2)
  :parents (xlate-equiv-x86s)
  :guard (and (x86p x86-1)
              (x86p x86-2))
  :non-executable t

  :prepwork
  ((define all-msrs-equal-aux (i x86-1 x86-2)
     :parents (all-msrs-equal)
     :guard (and (natp i)
                 (<= i *model-specific-register-names-len*)
                 (x86p x86-1)
                 (x86p x86-2))
     :non-executable t
     :enabled t
     (if (zp i)
         (equal (xr :msr i x86-1) (xr :msr i x86-2))
       (and (equal (xr :msr (1- i) x86-1) (xr :msr (1- i) x86-2))
            (all-msrs-equal-aux (1- i) x86-1 x86-2)))

     ///

     (defthm all-msrs-equal-aux-open
       (implies (and (all-msrs-equal-aux i x86-1 x86-2)
                     (natp i)
                     (natp j)
                     (< j i))
                (equal (xr :msr j x86-1) (xr :msr j x86-2))))

     (defthm all-msrs-equal-aux-is-reflexive
       (all-msrs-equal-aux i x x))

     (defthm all-msrs-equal-aux-is-commutative
       (implies (all-msrs-equal-aux i x y)
                (all-msrs-equal-aux i y x)))

     (defthm all-msrs-equal-aux-is-transitive
       (implies (and (all-msrs-equal-aux i x y)
                     (all-msrs-equal-aux i y z))
                (all-msrs-equal-aux i x z)))

     (defthm all-msrs-equal-aux-and-xw
       (implies (not (equal fld :msr))
                (equal (all-msrs-equal-aux i (xw fld index val x) y)
                       (all-msrs-equal-aux i x y))))

     (defthm all-msrs-equal-aux-and-wm-low-64
       (equal (all-msrs-equal-aux i (wm-low-64 index val x) y)
              (all-msrs-equal-aux i x y)))))

  (if (good-paging-structures-x86p x86-1)
      (if (good-paging-structures-x86p x86-2)
          (all-msrs-equal-aux *model-specific-register-names-len* x86-1 x86-2)
        nil)
    (not (good-paging-structures-x86p x86-2)))

  ///

  (defequiv all-msrs-equal)

  (defthm all-msrs-equal-and-xw
    (implies (and (not (equal fld :msr))
                  (good-paging-structures-x86p x)
                  (good-paging-structures-x86p (xw fld index val x)))
             (equal (all-msrs-equal (xw fld index val x) y)
                    (all-msrs-equal (double-rewrite x) y))))

  (defthm all-msrs-equal-and-wm-low-64
    (implies (and (good-paging-structures-x86p x)
                  (good-paging-structures-x86p (wm-low-64 index val x)))
             (equal (all-msrs-equal (wm-low-64 index val x) y)
                    (all-msrs-equal (double-rewrite x) y)))))

(define all-mem-except-paging-structures-equal
  (x86-1 x86-2)
  :parents (xlate-equiv-x86s)
  :guard (and (x86p x86-1)
              (x86p x86-2))
  :non-executable t

  :prepwork
  ((define all-mem-except-paging-structures-equal-aux
     (i paging-qword-addresses x86-1 x86-2)
     :parents (all-mem-except-paging-structures-equal)
     :guard (and (natp i)
                 (<= i *mem-size-in-bytes*)
                 (mult-8-qword-paddr-list-listp paging-qword-addresses)
                 (x86p x86-1)
                 (x86p x86-2))
     :non-executable t
     :enabled t

     (if (zp i)

         (if (pairwise-disjoint-p-aux
              (list i)
              (open-qword-paddr-list-list paging-qword-addresses))
             ;; i does not point to paging data, hence the contents of i
             ;; must be exactly equal.

             (equal (xr :mem i x86-1) (xr :mem i x86-2))

           t)

       (if (pairwise-disjoint-p-aux
            (list (1- i))
            (open-qword-paddr-list-list paging-qword-addresses))

           ;; i does not point to paging data, hence the contents of i
           ;; must be exactly equal.
           (and (equal (xr :mem (1- i) x86-1) (xr :mem (1- i) x86-2))
                (all-mem-except-paging-structures-equal-aux
                 (1- i) paging-qword-addresses x86-1 x86-2))

         ;; i points to paging data, and hence we can't expect its
         ;; contents to be exactly equal. This case is dealt with by the
         ;; function xlate-equiv-entries-at-qword-addresses?.
         (all-mem-except-paging-structures-equal-aux
          (1- i) paging-qword-addresses x86-1 x86-2)))

     ///

     (defthm all-mem-except-paging-structures-equal-aux-open
       (implies (and (all-mem-except-paging-structures-equal-aux i addrss x86-1 x86-2)
                     (pairwise-disjoint-p-aux (list j) (open-qword-paddr-list-list addrss))
                     (natp i)
                     (natp j)
                     (< j i))
                (equal (xr :mem j x86-1) (xr :mem j x86-2))))

     (defthm all-mem-except-paging-structures-equal-aux-is-reflexive
       (all-mem-except-paging-structures-equal-aux i addrss x x))

     (defthm all-mem-except-paging-structures-equal-aux-is-commutative
       (implies (all-mem-except-paging-structures-equal-aux i addrss x y)
                (all-mem-except-paging-structures-equal-aux i addrss y x)))

     (defthm all-mem-except-paging-structures-equal-aux-is-transitive
       (implies (and (all-mem-except-paging-structures-equal-aux i addrss x y)
                     (all-mem-except-paging-structures-equal-aux i addrss y z))
                (all-mem-except-paging-structures-equal-aux i addrss x z)))

     (defthm all-mem-except-paging-structures-equal-aux-and-xw-not-mem
       (implies (not (equal fld :mem))
                (equal (all-mem-except-paging-structures-equal-aux i addrss (xw fld index val x) y)
                       (all-mem-except-paging-structures-equal-aux i addrss x y))))

     (defthm xr-mem-wm-low-64
       (implies (and (disjoint-p (list index) (addr-range 8 addr))
                     (physical-address-p addr))
                (equal (xr :mem index (wm-low-64 addr val x86))
                       (xr :mem index x86)))
       :hints (("Goal" :in-theory (e/d* (wm-low-64
                                         wm-low-32
                                         ifix)
                                        (force (force))))))

     (defthm all-mem-except-paging-structures-equal-aux-and-wm-low-64-paging-entry
       (implies (and (member-list-p index addrss)
                     (mult-8-qword-paddr-list-listp addrss))
                (equal (all-mem-except-paging-structures-equal-aux i addrss (wm-low-64 index val x) y)
                       (all-mem-except-paging-structures-equal-aux i addrss x y)))
       :hints (("Goal" :in-theory (e/d* (member-list-p) ()))))))

  (if (good-paging-structures-x86p x86-1)

      (if (good-paging-structures-x86p x86-2)

          (and (equal (gather-all-paging-structure-qword-addresses x86-1)
                      (gather-all-paging-structure-qword-addresses x86-2))
               (all-mem-except-paging-structures-equal-aux
                *mem-size-in-bytes*
                (gather-all-paging-structure-qword-addresses x86-1)
                x86-1 x86-2))

        nil)

    (not (good-paging-structures-x86p x86-2)))

  ///

  (defequiv all-mem-except-paging-structures-equal)

  (defthm all-mem-except-paging-structures-equal-and-xw
    (implies (and (not (equal fld :mem))
                  (not (equal fld :ctr))
                  (not (equal fld :programmer-level-mode))
                  (good-paging-structures-x86p x)
                  (good-paging-structures-x86p (xw fld index val x)))
             (equal (all-mem-except-paging-structures-equal (xw fld index val x) y)
                    (all-mem-except-paging-structures-equal (double-rewrite x) y)))
    :hints (("Goal" :in-theory (e/d* () (all-mem-except-paging-structures-equal-aux)))))

  (defthm all-mem-except-paging-structures-equal-and-wm-low-64-paging-entry
    (implies (and (member-list-p index (gather-all-paging-structure-qword-addresses x))
                  (good-paging-structures-x86p x)
                  (good-paging-structures-x86p (wm-low-64 index val x))
                  (equal (gather-all-paging-structure-qword-addresses (wm-low-64 index val x))
                         (gather-all-paging-structure-qword-addresses x)))
             (equal (all-mem-except-paging-structures-equal (wm-low-64 index val x) y)
                    (all-mem-except-paging-structures-equal (double-rewrite x) y)))
    :hints (("Goal" :in-theory (e/d* () (all-mem-except-paging-structures-equal-aux))))))

(define xlate-equiv-structures (x86-1 x86-2)
  :parents (xlate-equiv-x86s)
  :guard (and (x86p x86-1)
              (x86p x86-2))
  :non-executable t
  :long "<p>Two x86 states are @('xlate-equiv-structures') if their
  paging structures are equal, modulo the accessed and dirty bits (See
  @(see xlate-equiv-entries)).</p>"

  (if (good-paging-structures-x86p x86-1)

      (if (good-paging-structures-x86p x86-2)

          (let* ((paging-qword-addresses-1
                  (gather-all-paging-structure-qword-addresses x86-1))
                 (paging-qword-addresses-2
                  (gather-all-paging-structure-qword-addresses x86-2)))

            (and (equal (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86-1))
                        (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86-2)))
                 (equal (cr0-slice :cr0-wp (n32 (ctri *cr0* x86-1)))
                        (cr0-slice :cr0-wp (n32 (ctri *cr0* x86-2))))
                 (equal (cr3-slice :cr3-pdb (ctri *cr3* x86-1))
                        (cr3-slice :cr3-pdb (ctri *cr3* x86-2)))
                 (equal (cr4-slice :cr4-smep (n21 (ctri *cr4* x86-1)))
                        (cr4-slice :cr4-smep (n21 (ctri *cr4* x86-2))))
                 (equal (ia32_efer-slice :ia32_efer-nxe (n12 (msri *ia32_efer-idx* x86-1)))
                        (ia32_efer-slice :ia32_efer-nxe (n12 (msri *ia32_efer-idx* x86-2))))
                 (equal paging-qword-addresses-1 paging-qword-addresses-2)
                 (xlate-equiv-entries-at-qword-addresses?
                  paging-qword-addresses-1 paging-qword-addresses-2 x86-1 x86-2)))

        nil)

    (not (good-paging-structures-x86p x86-2)))

  ///

  (local
   (defthm xlate-equiv-structures-is-transitive-helper
     (implies (and (xlate-equiv-structures x y)
                   (xlate-equiv-structures y z))
              (xlate-equiv-structures x z))
     :hints (("Goal"
              :in-theory (e/d* () (xlate-equiv-entries-at-qword-addresses?-transitive))
              :use
              ((:instance
                xlate-equiv-entries-at-qword-addresses?-transitive
                (a (gather-all-paging-structure-qword-addresses x))
                (b (gather-all-paging-structure-qword-addresses y))
                (c (gather-all-paging-structure-qword-addresses z))))))))

  (defequiv xlate-equiv-structures
    :hints (("Goal" :in-theory (e/d* () (xlate-equiv-structures-is-transitive-helper))
             :use ((:instance xlate-equiv-structures-is-transitive-helper))))))

(define xlate-equiv-x86s (x86-1 x86-2)
  :parents (reasoning-about-page-tables)
  :guard (and (x86p x86-1)
              (x86p x86-2))
  :non-executable t
  :long "<p>Two x86 states are @('xlate-equiv-x86s') if their paging
  structures are equal, modulo the accessed and dirty bits (See @(see
  xlate-equiv-structures)). Other memory locations not containing the
  paging structures must be exactly equal (See @(see
  all-mem-except-paging-structures-equal)).  Other components of the
  two states, excluding @('MS') and @('FAULT') fields, must be exactly
  equal.</p>"


  (if (good-paging-structures-x86p x86-1)

      (if (good-paging-structures-x86p x86-2)

          (and
           ;; Array Fields are Equal.
           (all-rgfs-equal          x86-1 x86-2)
           (all-seg-visibles-equal  x86-1 x86-2)
           (all-seg-hiddens-equal   x86-1 x86-2)
           (all-strs-equal          x86-1 x86-2)
           (all-ssr-visibles-equal  x86-1 x86-2)
           (all-ssr-hiddens-equal   x86-1 x86-2)
           (all-ctrs-equal          x86-1 x86-2)
           (all-dbgs-equal          x86-1 x86-2)
           (all-fp-datas-equal      x86-1 x86-2)
           (all-xmms-equal          x86-1 x86-2)
           (all-msrs-equal          x86-1 x86-2)
           ;; Paging structures are equivalent.
           (xlate-equiv-structures  x86-1 x86-2)
           ;; All memory except from that containing paging structures
           ;; is equal.
           (all-mem-except-paging-structures-equal x86-1 x86-2)
           ;; Simple Fields are Equal.
           (equal (xr :rip          0 x86-1) (xr :rip          0 x86-2))
           (equal (xr :rflags       0 x86-1) (xr :rflags       0 x86-2))
           (equal (xr :fp-ctrl      0 x86-1) (xr :fp-ctrl      0 x86-2))
           (equal (xr :fp-status    0 x86-1) (xr :fp-status    0 x86-2))
           (equal (xr :fp-tag       0 x86-1) (xr :fp-tag       0 x86-2))
           (equal (xr :fp-last-inst 0 x86-1) (xr :fp-last-inst 0 x86-2))
           (equal (xr :fp-last-data 0 x86-1) (xr :fp-last-data 0 x86-2))
           (equal (xr :fp-opcode    0 x86-1) (xr :fp-opcode    0 x86-2))
           (equal (xr :mxcsr        0 x86-1) (xr :mxcsr        0 x86-2))
           (equal (xr :undef        0 x86-1) (xr :undef        0 x86-2))

           ;; Equality of programmer-level-mode is ensured by
           ;; good-paging-structures-x86p.

           ;; MS and FAULT fields are excluded from this list so that
           ;; theorems like
           ;; xlate-equiv-x86s-with-mv-nth-2-ia32e-la-to-pa-PT can be
           ;; proved without any hypotheses that say that the page
           ;; traversal didn't return an error. This might be a bad
           ;; decision --- maybe having those hyps in rules llike
           ;; xlate-equiv-x86s-with-mv-nth-2-ia32e-la-to-pa-PT is a
           ;; good idea. We'll find out, I guess.

           ;; (equal (xr :ms           0 x86-1) (xr :ms           0 x86-2))
           ;; (equal (xr :fault        0 x86-1) (xr :fault        0 x86-2))

           ;; Fields like ENV and OS-INFO are meaningful only in the
           ;; programmer-level mode.
           ;; (equal (xr :env          0 x86-1) (xr :env          0 x86-2))
           ;; (equal (xr :os-info      0 x86-1) (xr :os-info      0 x86-2))
           )

        nil)

    (not (good-paging-structures-x86p x86-2)))

  ///

  (defequiv xlate-equiv-x86s
    :hints (("Goal"
             :in-theory
             (e/d* ()
                   (member-list-p-and-pairwise-disjoint-p-aux
                    pairwise-disjoint-p-aux))))))


;; (define xlate-equiv-x86s (x86-1 x86-2)
;;   :parents (reasoning-about-page-tables)
;;   :guard (and (x86p x86-1)
;;               (x86p x86-2))
;;   :non-executable t
;;   :enabled t
;;   :long "<p>Two x86 states are @('xlate-equiv-x86s') if their paging
;;   structures are equal, modulo the accessed and dirty bits (See @(see
;;   xlate-equiv-structures)). Other memory locations not containing the
;;   paging structures must be exactly equal (See @(see
;;   all-mem-except-paging-structures-equal)).  Other components of the
;;   two states, excluding @('MS') and @('FAULT') fields, must be exactly
;;   equal.</p>"


;;   (if (good-paging-structures-x86p x86-1)

;;       (if (good-paging-structures-x86p x86-2)

;;           (and
;;            ;; Array Fields are Equal.
;;            (all-rgfs-equal          x86-1 x86-2)
;;            (all-seg-visibles-equal  x86-1 x86-2)
;;            (all-seg-hiddens-equal   x86-1 x86-2)
;;            (all-strs-equal          x86-1 x86-2)
;;            (all-ssr-visibles-equal  x86-1 x86-2)
;;            (all-ssr-hiddens-equal   x86-1 x86-2)
;;            (all-ctrs-equal          x86-1 x86-2)
;;            (all-dbgs-equal          x86-1 x86-2)
;;            (all-fp-datas-equal      x86-1 x86-2)
;;            (all-xmms-equal          x86-1 x86-2)
;;            (all-msrs-equal          x86-1 x86-2)
;;            ;; Simple Fields are Equal.
;;            (equal (xr :rip          0 x86-1) (xr :rip          0 x86-2))
;;            (equal (xr :rflags       0 x86-1) (xr :rflags       0 x86-2))
;;            (equal (xr :fp-ctrl      0 x86-1) (xr :fp-ctrl      0 x86-2))
;;            (equal (xr :fp-status    0 x86-1) (xr :fp-status    0 x86-2))
;;            (equal (xr :fp-tag       0 x86-1) (xr :fp-tag       0 x86-2))
;;            (equal (xr :fp-last-inst 0 x86-1) (xr :fp-last-inst 0 x86-2))
;;            (equal (xr :fp-last-data 0 x86-1) (xr :fp-last-data 0 x86-2))
;;            (equal (xr :fp-opcode    0 x86-1) (xr :fp-opcode    0 x86-2))
;;            (equal (xr :mxcsr        0 x86-1) (xr :mxcsr        0 x86-2))
;;            (equal (xr :undef        0 x86-1) (xr :undef        0 x86-2))
;;            ;; Equality of programmer-level-mode is ensured by
;;            ;; good-paging-structures-x86p.

;;            ;; MS and FAULT fields are excluded from this list so that
;;            ;; theorems like
;;            ;; xlate-equiv-x86s-with-mv-nth-2-ia32e-la-to-pa-PT can be
;;            ;; proved without any hypotheses that say that the page
;;            ;; traversal didn't return an error. This might be a bad
;;            ;; decision --- maybe having those hyps in rules llike
;;            ;; xlate-equiv-x86s-with-mv-nth-2-ia32e-la-to-pa-PT is a
;;            ;; good idea. We'll find out, I guess.

;;            ;; (equal (xr :ms           0 x86-1) (xr :ms           0 x86-2))
;;            ;; (equal (xr :fault        0 x86-1) (xr :fault        0 x86-2))

;;            ;; Fields like ENV and OS-INFO are meaningful only in the
;;            ;; programmer-level mode.
;;            ;; (equal (xr :env          0 x86-1) (xr :env          0 x86-2))
;;            ;; (equal (xr :os-info      0 x86-1) (xr :os-info      0 x86-2))

;;            ;; All Memory is Almost Equal.
;;            (let* ((paging-qword-addresses-1
;;                    (gather-all-paging-structure-qword-addresses x86-1))
;;                   (paging-qword-addresses-2
;;                    (gather-all-paging-structure-qword-addresses x86-2)))
;;              (and (equal paging-qword-addresses-1 paging-qword-addresses-2)
;;                   (all-mem-except-paging-structures-equal x86-1 x86-2)
;;                   (xlate-equiv-entries-at-qword-addresses?
;;                    paging-qword-addresses-1 paging-qword-addresses-2 x86-1 x86-2))))

;;         nil)

;;     (not (good-paging-structures-x86p x86-2)))

;;   ///

;;   (local
;;    (defthm xlate-equiv-x86s-is-transitive-helper
;;      (implies (and (xlate-equiv-x86s x y)
;;                    (xlate-equiv-x86s y z))
;;               (xlate-equiv-x86s x z))
;;      :hints (("Goal"
;;               :in-theory (e/d* () (xlate-equiv-entries-at-qword-addresses?-transitive))
;;               :use
;;               ((:instance
;;                 xlate-equiv-entries-at-qword-addresses?-transitive
;;                 (a (gather-all-paging-structure-qword-addresses x))
;;                 (b (gather-all-paging-structure-qword-addresses y))
;;                 (c (gather-all-paging-structure-qword-addresses z))))))))

;;   (defequiv xlate-equiv-x86s
;;     :hints (("Goal"
;;              :in-theory
;;              (e/d* ()
;;                    (xlate-equiv-x86s-is-transitive-helper
;;                     member-list-p-and-pairwise-disjoint-p-aux
;;                     pairwise-disjoint-p-aux
;;                     all-dbgs-equal
;;                     all-fp-datas-equal
;;                     all-msrs-equal))
;;              :use ((:instance xlate-equiv-x86s-is-transitive-helper))))))

;; ======================================================================

;; Recording some refinement relationships and congruence rules:

;; Refinement: When trying to maintain the equivalence relation in the
;; conclusion, the rewrite rules of xlate-equiv-x86s may be used.

(local (in-theory (e/d (xlate-equiv-x86s) ())))

(defthm xlate-equiv-structures-and-good-paging-structures-x86p
  (implies (xlate-equiv-structures x86-1 x86-2)
           (equal (good-paging-structures-x86p x86-1)
                  (good-paging-structures-x86p x86-2)))
  :hints (("Goal" :in-theory (e/d* (xlate-equiv-structures) ())))
  :rule-classes :congruence)

(defthm xlate-equiv-x86s-and-good-paging-structures-x86p
  (implies (xlate-equiv-x86s x86-1 x86-2)
           (equal (good-paging-structures-x86p x86-1)
                  (good-paging-structures-x86p x86-2)))
  :rule-classes :congruence)

(defthm xlate-equiv-x86s-refines-all-rgfs-equal
  (implies (xlate-equiv-x86s x86-1 x86-2)
           (all-rgfs-equal x86-1 x86-2))
  :hints (("Goal" :in-theory (e/d* (all-rgfs-equal) ())))
  :rule-classes :refinement)

(defthm xlate-equiv-x86s-refines-all-seg-visibles-equal
  (implies (xlate-equiv-x86s x86-1 x86-2)
           (all-seg-visibles-equal x86-1 x86-2))
  :hints (("Goal" :in-theory (e/d* (all-seg-visibles-equal) ())))
  :rule-classes :refinement)

(defthm xlate-equiv-x86s-refines-all-seg-hiddens-equal
  (implies (xlate-equiv-x86s x86-1 x86-2)
           (all-seg-hiddens-equal x86-1 x86-2))
  :hints (("Goal" :in-theory (e/d* (all-seg-hiddens-equal) ())))
  :rule-classes :refinement)

(defthm xlate-equiv-x86s-refines-all-strs-equal
  (implies (xlate-equiv-x86s x86-1 x86-2)
           (all-strs-equal x86-1 x86-2))
  :hints (("Goal" :in-theory (e/d* (all-strs-equal) ())))
  :rule-classes :refinement)

(defthm xlate-equiv-x86s-refines-all-ssr-visibles-equal
  (implies (xlate-equiv-x86s x86-1 x86-2)
           (all-ssr-visibles-equal x86-1 x86-2))
  :hints (("Goal" :in-theory (e/d* (all-ssr-visibles-equal) ())))
  :rule-classes :refinement)

(defthm xlate-equiv-x86s-refines-all-ssr-hiddens-equal
  (implies (xlate-equiv-x86s x86-1 x86-2)
           (all-ssr-hiddens-equal x86-1 x86-2))
  :hints (("Goal" :in-theory (e/d* (all-ssr-hiddens-equal) ())))
  :rule-classes :refinement)

(defthm xlate-equiv-x86s-refines-all-ctrs-equal
  (implies (xlate-equiv-x86s x86-1 x86-2)
           (all-ctrs-equal x86-1 x86-2))
  :hints (("Goal" :in-theory (e/d* (all-ctrs-equal) ())))
  :rule-classes :refinement)

(defthm xlate-equiv-x86s-refines-all-dbgs-equal
  (implies (xlate-equiv-x86s x86-1 x86-2)
           (all-dbgs-equal x86-1 x86-2))
  :hints (("Goal" :in-theory (e/d* (all-dbgs-equal) ())))
  :rule-classes :refinement)

(defthm xlate-equiv-x86s-refines-all-fp-datas-equal
  (implies (xlate-equiv-x86s x86-1 x86-2)
           (all-fp-datas-equal x86-1 x86-2))
  :hints (("Goal" :in-theory (e/d* (all-fp-datas-equal) ())))
  :rule-classes :refinement)

(defthm xlate-equiv-x86s-refines-all-xmms-equal
  (implies (xlate-equiv-x86s x86-1 x86-2)
           (all-xmms-equal x86-1 x86-2))
  :hints (("Goal" :in-theory (e/d* (all-xmms-equal) ())))
  :rule-classes :refinement)

(defthm xlate-equiv-x86s-refines-all-msrs-equal
  (implies (xlate-equiv-x86s x86-1 x86-2)
           (all-msrs-equal x86-1 x86-2))
  :hints (("Goal" :in-theory (e/d* (all-msrs-equal) ())))
  :rule-classes :refinement)

(defthm xlate-equiv-x86s-refines-all-mem-except-paging-structures-equal
  (implies (xlate-equiv-x86s x86-1 x86-2)
           (all-mem-except-paging-structures-equal x86-1 x86-2))
  :hints (("Goal" :in-theory (e/d* (all-mem-except-paging-structures-equal) ())))
  :rule-classes :refinement)

(defthm xlate-equiv-x86s-refines-xlate-equiv-structures
  (implies (xlate-equiv-x86s x86-1 x86-2)
           (xlate-equiv-structures x86-1 x86-2))
  :hints (("Goal" :in-theory (e/d* (xlate-equiv-structures) ())))
  :rule-classes :refinement)

;; =====================================================================

;; gather-all-paging-structure-qword-addresses and wm-low-64, with
;; equiv x86s:

(defun find-an-xlate-equiv-x86-aux (thm-name x86-term)
  ;; Finds a "smaller" x86 that is xlate-equiv to x86-term.
  (if (atom x86-term)
      x86-term
    (b* ((outer-fn (car x86-term))
         ((when (and (not (equal outer-fn 'MV-NTH))
                     (not (equal outer-fn 'WM-LOW-64))
                     (not (and (equal outer-fn 'XW)
                               (equal (second x86-term) '':MEM)))))
          (cw "~%~p0: Unexpected x86-term encountered:~p1~%" thm-name x86-term)
          x86-term))
      (cond ((equal outer-fn 'MV-NTH)
             ;; We expect x86-term to be a function related to page
             ;; traversals.
             (b* ((mv-nth-index (second x86-term))
                  (inner-fn-call (third x86-term))
                  (inner-fn (first inner-fn-call))
                  ((when (if (equal mv-nth-index ''2)
                             (not (member-p inner-fn
                                            '(IA32E-LA-TO-PA-PT
                                              IA32E-LA-TO-PA-PD
                                              IA32E-LA-TO-PA-PDPT
                                              IA32E-LA-TO-PA-PML4T
                                              IA32E-ENTRIES-FOUND-LA-TO-PA
                                              PAGE-TABLE-ENTRY-NO-PAGE-FAULT-P$INLINE
                                              PAGING-ENTRY-NO-PAGE-FAULT-P$INLINE
                                              RM08
                                              RB)))
                           (if (equal mv-nth-index ''1)
                               (not (member-p inner-fn '(WM08 WB)))
                             t)))
                   (cw "~%~p0: Unexpected mv-nth x86-term encountered:~p1~%" thm-name x86-term)
                   x86-term)
                  (sub-x86 (first (last inner-fn-call))))
               sub-x86))
            ((or (equal outer-fn 'WM-LOW-64)
                 (equal outer-fn 'XW))
             ;; We expect x86-term to be of the form (wm-low-64 index
             ;; val sub-x86) or (xw :mem val index).
             (b* ((sub-x86 (first (last x86-term))))
               sub-x86))))))

(defun find-an-xlate-equiv-x86 (thm-name x86-var x86-term)
  ;; bind-free for an x86 in xlate-equiv-x86s or
  ;; xlate-equiv-structures: should check just for the page traversal
  ;; functions and wm-low-64.
  ;; TO-DO: Logic mode...
  (declare (xargs :mode :program))
  (b* ((equiv-x86-1 (find-an-xlate-equiv-x86-aux thm-name x86-term))
       (equiv-x86-2 (find-an-xlate-equiv-x86-aux thm-name equiv-x86-1)))
    (if (equal equiv-x86-1 equiv-x86-2)
        `((,x86-var . ,equiv-x86-1))
      (find-an-xlate-equiv-x86 thm-name x86-var equiv-x86-2))))

(defthm gather-all-paging-structure-qword-addresses-wm-low-64-different-x86-disjoint
  (implies (and (bind-free
                 (find-an-xlate-equiv-x86
                  'gather-all-paging-structure-qword-addresses-wm-low-64-different-x86-disjoint
                  'x86 x86-equiv)
                 (x86))
                (equal addrs (gather-all-paging-structure-qword-addresses x86))
                (xlate-equiv-structures (double-rewrite x86) (double-rewrite x86-equiv))
                (good-paging-structures-x86p x86)
                (pairwise-disjoint-p-aux
                 (addr-range 8 index)
                 (open-qword-paddr-list-list addrs))
                (physical-address-p index))
           (equal (gather-all-paging-structure-qword-addresses
                   (wm-low-64 index val x86-equiv))
                  (gather-all-paging-structure-qword-addresses x86)))
  :hints (("Goal"
           :use ((:instance gather-all-paging-structure-qword-addresses-wm-low-64-disjoint
                            (x86 x86-equiv)))
           :in-theory (e/d*
                       (good-paging-structures-x86p
                        xlate-equiv-structures)
                       (pairwise-disjoint-p-aux
                        open-qword-paddr-list-list
                        gather-all-paging-structure-qword-addresses-wm-low-64-disjoint
                        gather-all-paging-structure-qword-addresses)))))

(defthm gather-all-paging-structure-qword-addresses-wm-low-64-different-x86
  (implies (and (xlate-equiv-structures x86 (double-rewrite x86-equiv))
                (good-paging-structures-x86p x86)
                (equal addrs (gather-all-paging-structure-qword-addresses x86))
                (member-list-p index addrs)
                (xlate-equiv-entries (double-rewrite val) (rm-low-64 index x86))
                (mult-8-qword-paddr-list-listp addrs)
                (no-duplicates-list-p addrs)
                (unsigned-byte-p 64 val))
           (equal (gather-all-paging-structure-qword-addresses
                   (wm-low-64 index val x86-equiv))
                  (gather-all-paging-structure-qword-addresses x86)))
  :hints (("Goal" :in-theory (e/d* (xlate-equiv-structures)
                                   (gather-all-paging-structure-qword-addresses-wm-low-64-entry-addr))
           :use ((:instance gather-all-paging-structure-qword-addresses-wm-low-64-entry-addr
                            (x86 x86-equiv))
                 (:instance gather-all-paging-structure-qword-addresses-wm-low-64-entry-addr
                            (x86 x86))))))

;; ======================================================================
