;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")

(include-book "x86-row-wow-thms" :ttags :all :dir :proof-utils)
(include-book "general-memory-utils" :ttags :all :dir :proof-utils)
(include-book "clause-processors/find-subterms" :dir :system)

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "arithmetic/top" :dir :system))

;; ======================================================================

(defsection programmer-level-memory-utils
  :parents (proof-utilities)

  :short "Helper lemmas for reasoning about operations done on regions
  of memory in programmer-level mode"

  :long "<p>Here, we prove some useful lemmas that facilitate
reasoning about the behavior of @(see wb) and @(see rb) when they
operate in disjoint or overlapping regions of memory in the
programmer-level mode.</p>" )

(local (xdoc::set-default-parents programmer-level-memory-utils))

;; ----------------------------------------------------------------------
;; Debugging:
;; ----------------------------------------------------------------------

;; If you think some rules from this book should fire when you are
;; unwinding your (x86-run ... x86) expression, monitoring the
;; following rules (maybe using Jared Davis's why macro) can tell you
;; (maybe) what's going on.

;; (acl2::why x86-run-opener-not-ms-not-zp-n)
;; (acl2::why x86-fetch-decode-execute-opener)
;; (acl2::why get-prefixes-opener-lemma-2)
;; (acl2::why rb-in-terms-of-nth-and-pos)
;; (acl2::why program-at-wb-disjoint)
;; (acl2::why member-p-canonical-address-listp)

;; ======================================================================

;; RoW and WoW theorems useful in the programmer-level mode:
;; I need more theorems for when addr1 and addr2 overlap.

(local (in-theory (enable rvm08 rvm16 wvm08 wvm16 rvm32 rvm64 wvm32 wvm64)))

;; Theorems about rvm08 and wvm08:

;; rvm08 and wmw08 RoW:

(defthm |(rvm08 addr2 (wvm08 addr1 val x86)) --- same addr|
  (implies (and (equal addr1 addr2)
                (n08p val)
                (canonical-address-p addr1))
           (equal (rvm08 addr2 (mv-nth 1 (wvm08 addr1 val x86)))
                  (mv nil val (mv-nth 1 (wvm08 addr1 val x86))))))

(defthm |(rvm08 addr2 (wvm08 addr1 val x86)) --- disjoint addr|
  (implies (not (equal addr1 addr2))
           (equal (rvm08 addr2 (mv-nth 1 (wvm08 addr1 val x86)))
                  (mv (mv-nth 0 (rvm08 addr2 x86))
                      (mv-nth 1 (rvm08 addr2 x86))
                      (mv-nth 1 (wvm08 addr1 val x86)))))
  :hints (("Goal" :in-theory (e/d ()
                                  ((force) force)))))

;; wvm08 WoW:

(defthm |(wvm08 addr2 val2 (wvm08 addr1 val1 x86)) --- same addr|
  (implies (equal addr1 addr2)
           (equal (wvm08 addr2 val2 (mv-nth 1 (wvm08 addr1 val1 x86)))
                  (wvm08 addr2 val2 x86))))

(defthm |(wvm08 addr2 val2 (wvm08 addr1 val1 x86)) --- disjoint addr|
  (implies (not (equal addr1 addr2))
           (equal (mv-nth 1 (wvm08 addr2 val2 (mv-nth 1 (wvm08 addr1 val1 x86))))
                  (mv-nth 1 (wvm08 addr1 val1 (mv-nth 1 (wvm08 addr2 val2 x86))))))
  :hints (("Goal" :in-theory (e/d () ())))
  :rule-classes ((:rewrite :loop-stopper ((addr2 addr1)))))

;; Theorems about rvm16 and wvm16:

;; rvm16 and wvm16 RoW:

(defthm |(rvm16 addr2 (wvm16 addr1 val x86)) --- same addr|
  (implies (and (equal addr1 addr2)
                (n16p val)
                (canonical-address-p addr1)
                (canonical-address-p (1+ addr1)))
           (equal (rvm16 addr2 (mv-nth 1 (wvm16 addr1 val x86)))
                  (mv nil val (mv-nth 1 (wvm16 addr1 val x86))))))

(defthm |(rvm16 addr2 (wvm16 addr1 val x86)) --- disjoint addr|
  (implies (disjoint-p (addr-range 2 addr1)
                       (addr-range 2 addr2))
           (equal (rvm16 addr2 (mv-nth 1 (wvm16 addr1 val x86)))
                  (mv (mv-nth 0 (rvm16 addr2 x86))
                      (mv-nth 1 (rvm16 addr2 x86))
                      (mv-nth 1 (wvm16 addr1 val x86))))))

;; wvm16 WoW:

(defthm |(wvm16 addr2 val2 (wvm16 addr1 val1 x86)) --- same addr|
  (implies (equal addr1 addr2)
           (equal (wvm16 addr2 val2 (mv-nth 1 (wvm16 addr1 val1 x86)))
                  (wvm16 addr2 val2 x86))))

(defthm |(wvm16 addr2 val2 (wvm16 addr1 val1 x86)) --- disjoint addr|
  (implies (disjoint-p (addr-range 2 addr1)
                       (addr-range 2 addr2))
           (equal (mv-nth 1 (wvm16 addr2 val2 (mv-nth 1 (wvm16 addr1 val1 x86))))
                  (mv-nth 1 (wvm16 addr1 val1 (mv-nth 1 (wvm16 addr2 val2 x86))))))
  :hints (("Goal" :in-theory (e/d (n48 n48-to-i48) ())))
  :rule-classes ((:rewrite :loop-stopper ((addr2 addr1)))))

;; Theorems about rvm32 and wvm32:

;; rvm32 and wvm32 RoW:

(defthm |(rvm32 addr2 (wvm32 addr1 val x86)) --- same addr|
  (implies (and (equal addr1 addr2)
                (n32p val)
                (canonical-address-p addr2)
                (canonical-address-p (+ 3 addr2)))
           (equal (rvm32 addr2 (mv-nth 1 (wvm32 addr1 val x86)))
                  (mv nil val (mv-nth 1 (wvm32 addr1 val x86))))))

(defthm |(rvm32 addr2 (wvm32 addr1 val x86)) --- disjoint addr|
  (implies (disjoint-p (addr-range 4 addr1)
                       (addr-range 4 addr2))
           (equal (rvm32 addr2 (mv-nth 1 (wvm32 addr1 val x86)))
                  (mv (mv-nth 0 (rvm32 addr2 x86))
                      (mv-nth 1 (rvm32 addr2 x86))
                      (mv-nth 1 (wvm32 addr1 val x86)))))
  :hints (("Goal" :in-theory (e/d () (force (force))))))

;; wvm32 WoW:

(defthm |(wvm32 addr2 val2 (wvm32 addr1 val1 x86)) --- same addr|
  (implies (equal addr1 addr2)
           (equal (wvm32 addr2 val2 (mv-nth 1 (wvm32 addr1 val1 x86)))
                  (wvm32 addr2 val2 x86)))
  :hints (("Goal" :in-theory (e/d () (force (force))))))

(defthm |(wvm32 addr2 val2 (wvm32 addr1 val1 x86)) --- disjoint addr|
  (implies (disjoint-p (addr-range 4 addr1)
                       (addr-range 4 addr2))
           (equal (mv-nth 1 (wvm32 addr2 val2 (mv-nth 1 (wvm32 addr1 val1 x86))))
                  (mv-nth 1 (wvm32 addr1 val1 (mv-nth 1 (wvm32 addr2 val2 x86))))))
  :hints (("Goal" :in-theory (e/d (n48) ())))
  :rule-classes ((:rewrite :loop-stopper ((addr2 addr1)))))

;; Theorems about rm64 and wm64:

;; rvm64 and wvm64:

(defthm |(rvm64 addr2 (wvm64 addr1 val x86)) --- same addr|
  (implies (and (equal addr1 addr2)
                (n64p val)
                (canonical-address-p addr2)
                (canonical-address-p (+ 7 addr2)))
           (equal (rvm64 addr2 (mv-nth 1 (wvm64 addr1 val x86)))
                  (mv nil val (mv-nth 1 (wvm64 addr1 val x86)))))
  :hints (("Goal" :in-theory (e/d () (rvm32 wvm32 mv-nth)))))

(defthm |(rvm64 addr2 (wvm64 addr1 val x86)) --- disjoint addr|
  (implies (disjoint-p (addr-range 8 addr1)
                       (addr-range 8 addr2))
           (equal (rvm64 addr2 (mv-nth 1 (wvm64 addr1 val x86)))
                  (mv (mv-nth 0 (rvm64 addr2 x86))
                      (mv-nth 1 (rvm64 addr2 x86))
                      (mv-nth 1 (wvm64 addr1 val x86)))))
  :hints (("Goal" :in-theory (e/d () (rvm32 wvm32 mv-nth)))))

;; wvm64 WoW:

(defthm |(wvm64 addr2 val2 (wvm64 addr1 val1 x86)) --- same addr|
  (implies (equal addr1 addr2)
           (equal (wvm64 addr2 val2 (mv-nth 1 (wvm64 addr1 val1 x86)))
                  (wvm64 addr2 val2 x86)))
  :hints (("Goal" :in-theory (e/d () (rvm32 wvm32 mv-nth)))))

(defthm |(wvm64 addr2 val2 (wvm64 addr1 val1 x86)) --- disjoint addr|
  (implies (disjoint-p (addr-range 8 addr1)
                       (addr-range 8 addr2))
           (equal (mv-nth 1 (wvm64 addr2 val2 (mv-nth 1 (wvm64 addr1 val1 x86))))
                  (mv-nth 1 (wvm64 addr1 val1 (mv-nth 1 (wvm64 addr2 val2 x86))))))
  :hints (("Goal" :in-theory (e/d () (rvm32 wvm32 mv-nth))))
  :rule-classes ((:rewrite :loop-stopper ((addr2 addr1)))))

(local (in-theory (disable rvm08 rvm16 wvm08 wvm16 rvm32 rvm64 wvm32 wvm64)))

;; ======================================================================

;; Theorems about rb and wb:

(defthm rb-returns-true-listp
  (implies (x86p x86)
           (true-listp (mv-nth 1 (rb addresses r-w-x x86))))
  :rule-classes (:rewrite :type-prescription))

(local
 (defthm rm08-wb-not-member-p
   (implies (and (not (member-p addr (strip-cars addr-lst)))
                 (programmer-level-mode x86))
            (equal (mv-nth 1 (rm08 addr r-w-x (mv-nth 1 (wb addr-lst x86))))
                   (mv-nth 1 (rm08 addr r-w-x x86))))
   :hints (("Goal" :in-theory (e/d (rm08 wm08) ())))))

(local
 (defthm rvm08-wb-not-member-p
   (implies (and (not (member-p addr (strip-cars addr-lst)))
                 (programmer-level-mode x86))
            (equal (mv-nth 1 (rvm08 addr (mv-nth 1 (wb addr-lst x86))))
                   (mv-nth 1 (rvm08 addr x86))))
   :hints (("Goal" :in-theory (e/d (wm08) ())))))

(defthm rb-wb-disjoint
  (implies (and (disjoint-p addresses (strip-cars addr-lst))
                (programmer-level-mode x86))
           (equal (mv-nth 1 (rb addresses r-w-x (mv-nth 1 (wb addr-lst x86))))
                  (mv-nth 1 (rb addresses r-w-x x86))))
  :hints (("Goal" :in-theory (e/d (disjoint-p) ()))))


(local
  (defthm rb-wb-equal-assoc-helper-1
    (implies (and (alistp xs)
                  (member-p a (cdr (strip-cars xs))))
             (equal (assoc a (acl2::rev (cdr xs)))
                    (assoc a (acl2::rev xs))))))

(local
 (defthm rb-wb-equal-assoc-list-helper-1
   (implies (and (alistp xs)
                 (subset-p as (strip-cars (cdr xs))))
            (equal (assoc-list as (acl2::rev (cdr xs)))
                   (assoc-list as (acl2::rev xs))))
   :hints (("Goal"
            :in-theory (e/d (subset-p)
                            (rb-wb-equal-assoc-helper-1))
            :use ((:instance rb-wb-equal-assoc-helper-1
                             (a (car as))
                             (xs xs)))))))

(local
 (defthm rb-wb-equal-assoc-list-helper-2
   (implies (addr-byte-alistp addr-lst)
            (equal (assoc-list (strip-cars (remove-duplicate-keys (cdr addr-lst)))
                               (acl2::rev (cdr addr-lst)))
                   (assoc-list (strip-cars (remove-duplicate-keys (cdr addr-lst)))
                               (acl2::rev addr-lst))))
   :hints (("Goal"
            :expand (assoc-list (strip-cars (remove-duplicate-keys (cdr addr-lst)))
                                (acl2::rev addr-lst))))))

(local
 (defthm not-member-assoc-equal-with-rev-and-strip-cars-alt
   (implies (and (alistp xs)
                 (not (member-p (car (car xs)) (strip-cars (cdr xs)))))
            (equal (cdr (assoc (car (car xs)) (acl2::rev xs)))
                   (cdr (car xs))))
   :hints (("Goal" :in-theory (e/d* ()
                                    (not-member-assoc-equal-with-rev-and-strip-cars))
            :use ((:instance not-member-assoc-equal-with-rev-and-strip-cars
                             (xs (cdr xs))
                             (a (car (car xs)))
                             (b (cdr (car xs)))))))))

(defthmd rb-wb-equal
  (implies (and (equal addresses (strip-cars (remove-duplicate-keys addr-lst)))
                (programmer-level-mode x86)
                (addr-byte-alistp addr-lst))
           (equal (mv-nth 1 (rb addresses r-w-x (mv-nth 1 (wb addr-lst x86))))
                  (assoc-list addresses (reverse addr-lst))))
  :hints (("Goal" :in-theory (e/d (wm08 rm08) ()))))

(local
 (defthm rvm08-wb-member-p-helper
   (implies (and (member-p addr (strip-cars (remove-duplicate-keys addr-lst)))
                 (programmer-level-mode x86)
                 (addr-byte-alistp addr-lst))
            (equal (mv-nth 1 (rm08 addr r-w-x (mv-nth 1 (wb addr-lst x86))))
                   (cdr (assoc-equal addr (reverse addr-lst)))))
   :hints (("Goal" :in-theory (e/d (rm08 wm08) ())))))

(local
 (defthm rvm08-wb-member-p
   (implies (and (member-p addr (strip-cars addr-lst))
                 (programmer-level-mode x86)
                 (addr-byte-alistp addr-lst))
            (equal (mv-nth 1 (rm08 addr r-w-x (mv-nth 1 (wb addr-lst x86))))
                   (cdr (assoc-equal addr (reverse addr-lst)))))))

(local
 (defthm rb-wb-subset-helper
   (implies (and (equal (mv-nth 1
                                (rb-1 (cdr addresses)
                                      r-w-x (mv-nth 1 (wb addr-lst x86))
                                      nil))
                        (assoc-list (cdr addresses)
                                    (acl2::rev addr-lst)))
                 (subset-p addresses (strip-cars addr-lst))
                 (xr :programmer-level-mode 0 x86)
                 (integerp (car addresses))
                 (<= -140737488355328 (car addresses))
                 (< (car addresses) 140737488355328)
                 (canonical-address-listp (cdr addresses))
                 (addr-byte-alistp addr-lst))
            (equal (mv-nth 1
                           (rb-1 addresses
                                 r-w-x (mv-nth 1 (wb addr-lst x86))
                                 nil))
                   (cons (cdr (assoc-equal (car addresses)
                                           (acl2::rev addr-lst)))
                         (assoc-list (cdr addresses)
                                     (acl2::rev addr-lst)))))
   :hints (("Goal" :expand (rb-1 addresses r-w-x (mv-nth 1 (wb addr-lst x86)) nil)
            :in-theory (e/d (subset-p) ())))))

(defthm rb-wb-subset
  (implies (and (subset-p addresses (strip-cars addr-lst))
                (programmer-level-mode x86)
                ;; [Shilpi]: Ugh, this hyp. below is so annoying. I
                ;; could remove it if I proved something like
                ;; subset-p-strip-cars-of-remove-duplicate-keys,
                ;; commented out below.
                (canonical-address-listp addresses)
                (addr-byte-alistp addr-lst))
           (equal (mv-nth 1 (rb addresses r-w-x (mv-nth 1 (wb addr-lst x86))))
                  (assoc-list addresses (reverse addr-lst))))
  :hints (("Goal" :induct (assoc-list addresses (reverse addr-lst)))))

;; (skip-proofs
;;  (defthm subset-p-strip-cars-of-remove-duplicate-keys
;;    (equal (subset-p x (strip-cars (remove-duplicate-keys xs)))
;;           (subset-p x (strip-cars xs)))
;;    :hints (("Goal" :in-theory (e/d* (subset-p) ())))))

;; (defthm canonical-address-listp-strip-cars-addr-bytes-alistp
;;   ;; See canonical-address-listp-strip-cars-remove-duplicate-keys-addr-bytes-alistp
;;   (implies (and (subset-p addresses (strip-cars addr-lst))
;;                 (addr-byte-alistp addr-lst))
;;            (canonical-address-listp addresses))
;;   :hints (("Goal"
;;            :do-not-induct t
;;            :use ((:instance canonical-address-listp-strip-cars-remove-duplicate-keys-addr-bytes-alistp))
;;            :in-theory (e/d* ()
;;                             (canonical-address-listp-strip-cars-remove-duplicate-keys-addr-bytes-alistp
;;                              addr-byte-alistp
;;                              canonical-address-listp))))
;;   :rule-classes :forward-chaining)

;; (defthm rb-wb-subset-new
;;   (implies (and (subset-p addresses (strip-cars addr-lst))
;;                 (addr-byte-alistp addr-lst)
;;                 (programmer-level-mode x86))
;;            (equal (mv-nth 1 (rb addresses r-w-x (mv-nth 1 (wb addr-lst x86))))
;;                   (assoc-list addresses (reverse addr-lst))))
;;   :hints (("Goal"
;;            :do-not-induct t
;;            :use ((:instance rb-wb-subset)))))

(defthmd rb-rb-subset
  ;; [Shilpi]: This theorem can be generalized so that the conclusion mentions
  ;; addr1, where addr1 <= addr.  Also, this is an expensive rule. Keep it
  ;; disabled generally.
  (implies (and (equal (mv-nth 1 (rb (create-canonical-address-list i addr) r-w-x x86))
                       bytes)
                (canonical-address-p (+ -1 i addr))
                (canonical-address-p addr)
                (xr :programmer-level-mode 0 x86)
                (posp i)
                (< j i))
           (equal (mv-nth 1 (rb (create-canonical-address-list j addr) r-w-x x86))
                  (take j bytes)))
  :hints (("Goal" :in-theory (e/d* (rb canonical-address-p signed-byte-p) ()))))

(defthm take-and-rb
  (implies (and (canonical-address-p (+ -1 i addr))
                (canonical-address-p addr)
                (xr :programmer-level-mode 0 x86)
                (< k i))
           (equal (take k (mv-nth 1 (rb (create-canonical-address-list i addr) r-w-x x86)))
                  (mv-nth 1 (rb (create-canonical-address-list k addr) r-w-x x86))))
  :hints (("Goal" :in-theory (e/d* (canonical-address-p signed-byte-p rb) ((:meta acl2::mv-nth-cons-meta))))))

(defthm rb-rb-split-reads
  (implies (and (canonical-address-p addr)
                (xr :programmer-level-mode 0 x86)
                (natp j)
                (natp k))
           (equal (mv-nth 1 (rb (create-canonical-address-list (+ k j) addr) r-w-x x86))
                  (append (mv-nth 1 (rb (create-canonical-address-list k addr) r-w-x x86))
                          (mv-nth 1 (rb (create-canonical-address-list j (+ k addr)) r-w-x x86)))))
  :hints (("Goal" :in-theory (e/d* (rb canonical-address-p signed-byte-p)
                                   ((:meta acl2::mv-nth-cons-meta))))))

(defthm program-at-wb-disjoint
  (implies (and (programmer-level-mode x86)
                (canonical-address-listp addresses)
                (disjoint-p addresses (strip-cars addr-lst)))
           (equal (program-at addresses r-w-x (mv-nth 1 (wb addr-lst x86)))
                  (program-at addresses r-w-x x86)))
  :hints (("Goal" :in-theory (e/d (program-at) (rb)))))

(defthm program-at-write-x86-file-des
  (implies (programmer-level-mode x86)
           (equal (program-at addresses r-w-x (write-x86-file-des i v x86))
                  (program-at addresses r-w-x x86)))
  :hints (("Goal" :in-theory (e/d (program-at write-x86-file-des write-x86-file-des-logic)
                                  (rb)))))

(defthm program-at-delete-x86-file-des
  (implies (programmer-level-mode x86)
           (equal (program-at addresses r-w-x (delete-x86-file-des i x86))
                  (program-at addresses r-w-x x86)))
  :hints (("Goal" :in-theory (e/d (program-at delete-x86-file-des delete-x86-file-des-logic)
                                  (rb)))))

(defthm program-at-write-x86-file-contents
  (implies (programmer-level-mode x86)
           (equal (program-at addresses r-w-x (write-x86-file-contents i v x86))
                  (program-at addresses r-w-x x86)))
  :hints (("Goal" :in-theory (e/d (program-at write-x86-file-contents write-x86-file-contents-logic)
                                  (rb)))))

(defthm program-at-delete-x86-file-contents
  (implies (programmer-level-mode x86)
           (equal (program-at addresses r-w-x (delete-x86-file-contents i x86))
                  (program-at addresses r-w-x x86)))
  :hints (("Goal" :in-theory (e/d (program-at delete-x86-file-contents delete-x86-file-contents-logic)
                                  (rb)))))

(defthm program-at-pop-x86-oracle
  (implies (programmer-level-mode x86)
           (equal (program-at addresses r-w-x (mv-nth 1 (pop-x86-oracle x86)))
                  (program-at addresses r-w-x x86)))
  :hints (("Goal" :in-theory (e/d (program-at pop-x86-oracle pop-x86-oracle-logic)
                                  (rb)))))

(defthm program-at-write-user-rflags
  (implies (programmer-level-mode x86)
           (equal (program-at addresses r-w-x (write-user-rflags flags mask x86))
                  (program-at addresses r-w-x x86)))
  :hints (("Goal" :in-theory (e/d (write-user-rflags)
                                  (force (force))))))

;; ======================================================================

;; Events related to WB:

(defthm wb-nil
  (implies (x86p x86)
           (equal (mv-nth 1 (wb nil x86)) x86)))

(defthmd wb-not-consp-addr-byte-alistp
  (implies (and (addr-byte-alistp addr-lst)
                (not (consp addr-lst)))
           (equal (wb addr-lst x86)
                  (mv nil x86))))

(defthm wb-and-wb-combine-wbs
  (implies (and (addr-byte-alistp addr-list1)
                (addr-byte-alistp addr-list2)
                (programmer-level-mode x86))
           (equal (mv-nth 1 (wb addr-list2 (mv-nth 1 (wb addr-list1 x86))))
                  (mv-nth 1 (wb (append addr-list1 addr-list2) x86))))
  :hints (("Goal" :do-not '(generalize)
           :in-theory (e/d (wb-and-wm08) (append acl2::mv-nth-cons-meta)))))

(defthmd member-and-member-p
  (iff (member-p e x)
       (member e x)))

(defthmd wb-over-wb-same-address
  (implies (and (member addr (strip-cars addr-list))
                (canonical-address-p addr)
                (n08p val)
                (programmer-level-mode x86))
           (equal (wb (acons addr val addr-list) x86)
                  (wb addr-list x86)))
  :hints (("Goal" :do-not '(generalize)
           :in-theory (e/d (wb wm08 mv-nth) ()))))

(defun-nx wb-duplicate-writes-induct (addr-list x86)
  (if (endp addr-list)
      nil
    (if (member-p (car (car addr-list)) (strip-cars (cdr addr-list)))
        (wb-duplicate-writes-induct (cdr addr-list) x86)
      (wb-duplicate-writes-induct
       (cdr addr-list)
       (mv-nth 1 (wb (list (car addr-list)) x86))))))

(local
 (defthm wb-remove-duplicate-writes-helper
   (implies (and (member-p (car (car addr-list))
                           (strip-cars (cdr addr-list)))
                 (canonical-address-p (car (car addr-list)))
                 (n08p (cdr (car addr-list)))
                 (programmer-level-mode x86))
            (equal (wb addr-list x86)
                   (wb (cdr addr-list) x86)))
   :hints (("Goal"
            :in-theory (e/d () (wb-over-wb-same-address))
            :use ((:instance member-and-member-p
                             (e (car (car addr-list)))
                             (x (strip-cars (cdr addr-list))))
                  (:instance wb-over-wb-same-address
                             (addr (car (car addr-list)))
                             (val  (cdr (car addr-list)))
                             (addr-list (cdr addr-list))))))))

(defthmd wb-remove-duplicate-writes
  (implies (and (syntaxp
                 (not
                  (and (consp addr-list)
                       (eq (car addr-list) 'remove-duplicate-keys))))
                (addr-byte-alistp addr-list)
                (programmer-level-mode x86))
           (equal (wb addr-list x86)
                  (wb (remove-duplicate-keys addr-list) x86)))
  :hints (("Goal" :do-not '(generalize)
           :in-theory (e/d (wm08)
                           (acl2::mv-nth-cons-meta))
           :induct (wb-duplicate-writes-induct addr-list x86))))

;; Write-bytes-to-memory and wb:

(defthmd create-addr-bytes-alist-acons
  (implies
   (and (< 0 (len bytes))
        (canonical-address-p (+ lin-addr (len bytes)))
        (canonical-address-p lin-addr))
   (equal
    (create-addr-bytes-alist (create-canonical-address-list (len bytes) lin-addr) bytes)
    (acons
     lin-addr (car bytes)
     (create-addr-bytes-alist (create-canonical-address-list
                               (1- (len bytes))
                               (1+ lin-addr))
                              (cdr bytes))))))

(defthm write-bytes-to-memory-is-wb
  (implies (and (canonical-address-p (+ (len bytes) lin-addr))
                (byte-listp bytes)
                (canonical-address-p lin-addr))
           (equal (write-bytes-to-memory lin-addr bytes x86)
                  (wb (create-addr-bytes-alist
                       (create-canonical-address-list (len bytes) lin-addr)
                       bytes)
                      x86)))
  :hints (("Goal" :in-theory (e/d (write-bytes-to-memory
                                   wb-and-wm08)
                                  (acl2::mv-nth-cons-meta)))))

;; ======================================================================

;; Events related to RB:

(defthm rb-nil
  (implies (x86p x86)
           (equal (mv-nth 1 (rb nil r-w-x x86)) nil)))

;; The following theorems help in relieving the hypotheses of
;; get-prefixes opener lemmas.

(defthmd rm08-in-terms-of-nth-pos-and-rb
  ;; addresses is free.  Hopefully, (member-p addr addresses) will
  ;; help ACL2 find the right binding.
  (implies (and (member-p addr addresses)
                (canonical-address-listp addresses)
                (equal bytes (mv-nth 1 (rb addresses r-w-x x86)))
                (programmer-level-mode x86))
           (equal (mv-nth 1 (rm08 addr r-w-x x86))
                  (nth (pos addr addresses) bytes)))
  :hints (("Goal" :in-theory (e/d (pos rb)
                                  (signed-byte-p)))))

(defthm rm08-in-terms-of-rb
  ;; Also see rb-and-rm08.
  (implies (and (canonical-address-p addr)
                (programmer-level-mode x86))
           (equal (mv-nth 1 (rm08 addr r-w-x x86))
                  (car (mv-nth 1 (rb (list addr) r-w-x x86))))))

(defun find-info-from-program-at-term (thm mfc state)
  (declare (xargs :stobjs (state) :mode :program)
           (ignorable thm state))
  (b* ((call (acl2::find-call-lst 'program-at (acl2::mfc-clause mfc)))
       ((when (not call))
        ;; (cw "~%~p0: Program-At term not encountered.~%" thm)
        nil)
       (addresses (cadr call))
       ((when (not (equal (car addresses)
                          'create-canonical-address-list)))
        ;; (cw "~%~p0: Program-At without Create-Canonical-Address-List encountered.~%" thm)
        nil)
       (n (cadr addresses))
       (prog-addr (caddr addresses))
       (bytes (caddr call)))
      `((n . ,n)
        (prog-addr . ,prog-addr)
        (bytes . ,bytes))))

(defthm rb-in-terms-of-nth-and-pos
  (implies (and (bind-free (find-info-from-program-at-term
                            'rb-in-terms-of-nth-and-pos
                            mfc state)
                           (n prog-addr bytes))
                (program-at (create-canonical-address-list n prog-addr) bytes x86)
                (member-p addr (create-canonical-address-list n prog-addr))
                (syntaxp (quotep n))
                (programmer-level-mode x86))
           (equal (car (mv-nth 1 (rb (list addr) :x x86)))
                  (nth (pos addr (create-canonical-address-list n prog-addr)) bytes)))
  :hints (("Goal" :in-theory (e/d (program-at)
                                  (acl2::mv-nth-cons-meta
                                   rm08-in-terms-of-rb
                                   member-p-canonical-address-p-canonical-address-listp
                                   rb))
           :use ((:instance rm08-in-terms-of-rb
                            (r-w-x :x))
                 (:instance member-p-canonical-address-p-canonical-address-listp
                            (e addr))
                 (:instance rm08-in-terms-of-nth-pos-and-rb
                            (r-w-x :x)
                            (addresses (create-canonical-address-list n prog-addr)))))))

(encapsulate
 ()

 (local (include-book "std/lists/append" :dir :system))

 (defthmd rb-1-unwinding-thm
   (implies (and (canonical-address-listp addresses)
                 (programmer-level-mode x86)
                 (byte-listp acc))
            (equal (mv-nth 1 (rb-1 addresses r-w-x x86 acc))
                   (append acc
                           (mv-nth 1 (rb-1 (list (car addresses)) r-w-x x86 nil))
                           (mv-nth 1 (rb-1 (cdr addresses) r-w-x x86 nil)))))
   :hints (("Goal" :in-theory (e/d () (acl2::mv-nth-cons-meta force (force))))))

 (defthmd rb-unwinding-thm
   (implies (and (canonical-address-listp addresses)
                 (programmer-level-mode x86))
            (equal (mv-nth 1 (rb addresses r-w-x x86))
                   (append (mv-nth 1 (rb (list (car addresses)) r-w-x x86))
                           (mv-nth 1 (rb (cdr addresses) r-w-x x86)))))
   :hints (("Goal" :in-theory (e/d (rb append) (acl2::mv-nth-cons-meta rb-1))
            :use ((:instance rb-1-unwinding-thm (acc nil))))))

 )

(defthm rb-in-terms-of-rb-subset-p
  (implies
   (and (bind-free (find-info-from-program-at-term
                    'rb-in-terms-of-rb-subset-p
                    mfc state)
                   (n prog-addr bytes))
        (program-at (create-canonical-address-list n prog-addr) bytes x86)
        (subset-p addresses (create-canonical-address-list n prog-addr))
        (consp addresses)
        (syntaxp (quotep n))
        (programmer-level-mode x86))
   (equal (mv-nth 1 (rb addresses :x x86))
          (append (list (nth (pos
                              (car addresses)
                              (create-canonical-address-list n prog-addr))
                             bytes))
                  (mv-nth 1 (rb (cdr addresses) :x x86)))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (subset-p)
                           (canonical-address-p
                            acl2::mv-nth-cons-meta
                            rb-in-terms-of-nth-and-pos))
           :use ((:instance rb-unwinding-thm
                            (r-w-x :x))
                 (:instance rb-in-terms-of-nth-and-pos
                            (addr (car addresses)))))))

(defthm combine-bytes-rb-in-terms-of-rb-subset-p
  (implies
   (and (bind-free (find-info-from-program-at-term
                    'combine-bytes-rb-in-terms-of-rb-subset-p
                    mfc state)
                   (n prog-addr bytes))
        (program-at (create-canonical-address-list n prog-addr) bytes x86)
        (subset-p addresses (create-canonical-address-list n prog-addr))
        (consp addresses)
        (syntaxp (quotep n))
        (programmer-level-mode x86))
   (equal
    (combine-bytes (mv-nth 1 (rb addresses :x x86)))
    (combine-bytes
     (append (list (nth (pos (car addresses)
                             (create-canonical-address-list n prog-addr))
                        bytes))
             (mv-nth 1 (rb (cdr addresses) :x x86))))))
  :hints (("Goal" :in-theory (union-theories
                              '()
                              (theory 'minimal-theory))
           :use ((:instance rb-in-terms-of-rb-subset-p)))))

;; ======================================================================

(globally-disable '(rb wb canonical-address-p program-at
                       unsigned-byte-p signed-byte-p))

;; ======================================================================
