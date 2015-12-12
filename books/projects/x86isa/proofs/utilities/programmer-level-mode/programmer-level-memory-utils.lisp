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

;; Relating rip and canonical-address-p:

;; We don't want the rule rip-is-i48p to be active anymore. Anything
;; to do with rip and !rip should now be reasoned about in terms of
;; canonical-address-p, even though canonical-address-p and i48p are
;; the same, really.

(defthm canonical-address-p-rip
  (implies (x86p x86)
           (canonical-address-p (xr :rip index x86)))
  :rule-classes (:type-prescription :rewrite))

(defthm rip-is-integerp
  (implies (x86p x86)
           (integerp (xr :rip index x86)))
  :rule-classes :type-prescription)

(defthm x86p-!rip-when-val-is-canonical-address-p
  (implies (forced-and (x86p x86)
                       (canonical-address-p v))
           (x86p (xw :rip index v x86)))
  :hints (("Goal" :in-theory (enable ripp))))

(in-theory (disable (:type-prescription rip-is-i48p)))

;; ======================================================================

;; Lemmas about canonical-address-p, canonical-address-listp, and
;; create-canonical-address-list:

(defthm canonical-address-p-to-integerp-thm
  (implies (canonical-address-p x)
           (integerp x))
  :hints (("Goal" :in-theory (e/d* (canonical-address-p) ())))
  :rule-classes :forward-chaining)

(defthm canonical-address-listp-fwd-chain-true-listp
  (implies (canonical-address-listp x)
           (true-listp x))
  :rule-classes (:forward-chaining))

(defthm member-p-canonical-address-p
  (implies (and (canonical-address-listp x)
                (member-p e x))
           (canonical-address-p e))
  :rule-classes (:forward-chaining))

(defthm create-canonical-address-list-of-0
  (equal (create-canonical-address-list 0 addr) nil))

(defthm car-create-canonical-address-list
  (implies (and (canonical-address-p addr)
                (posp count))
           (equal (car (create-canonical-address-list count addr))
                  addr)))

(defthm cdr-create-canonical-address-list
  (implies (and (canonical-address-p addr)
                (posp count))
           (equal (cdr (create-canonical-address-list count addr))
                  (create-canonical-address-list (1- count) (1+ addr)))))

(defthm consp-of-create-canonical-address-list
  (implies (and (canonical-address-p addr)
                (natp count)
                (< 0 count))
           (consp (create-canonical-address-list count addr)))
  :hints (("Goal" :in-theory (e/d (create-canonical-address-list
                                   canonical-address-p
                                   signed-byte-p)
                                  ()))))

(defthm member-p-canonical-address-p-canonical-address-listp
  (implies (member-p e (create-canonical-address-list n prog-addr))
           (canonical-address-p e))
  :rule-classes :forward-chaining)

(defthm subset-p-canonical-address-listp
  (implies (and (canonical-address-listp y)
                (subset-p x y))
           (canonical-address-listp x))
  :hints (("Goal" :in-theory (e/d (subset-p) ())))
  :rule-classes :forward-chaining)

(defthm subset-p-canonical-address-listp-create-canonical-address-list
  (implies (subset-p x (create-canonical-address-list n prog-addr))
           (canonical-address-listp x))
  :hints (("Goal" :in-theory (e/d ()
                                  (subset-p-canonical-address-listp))
           :use ((:instance subset-p-canonical-address-listp
                            (y
                             (create-canonical-address-list
                              n prog-addr))))))
  :rule-classes :forward-chaining)

(local
 (defthmd member-p-canonical-address-listp-helper
   (implies (and (< 0 n)
                 (canonical-address-p prog-addr)
                 (canonical-address-p (+ -1 n prog-addr)))
            (equal (member-p addr
                             (create-canonical-address-list n prog-addr))
                   (and (integerp addr)
                        (<= prog-addr addr)
                        (< addr (+ n prog-addr)))))))

(defthm member-p-canonical-address-listp

  ;; Relieving the hypotheses of this rule will require some
  ;; arithmetic reasoning.  To establish whether addr is a member of
  ;; the canonical address list, we'd have to see whether it falls in
  ;; the range described by the first two hypotheses.

  (implies (and (<= prog-addr addr)
                (< addr (+ n prog-addr))
                (canonical-address-p prog-addr)
                (canonical-address-p (+ -1 n prog-addr))
                (integerp addr))
           (equal (member-p addr (create-canonical-address-list n prog-addr))
                  t))
  :hints (("Goal" :in-theory (e/d (member-p-canonical-address-listp-helper)
                                  ()))))

(defthm not-member-p-canonical-address-listp
  (implies (or (< addr prog-addr)
               (<= (+ n prog-addr) addr))
           (equal (member-p addr (create-canonical-address-list n prog-addr))
                  nil)))

(defthm not-member-p-canonical-address-listp-when-disjoint-p
  (implies (and (disjoint-p (create-canonical-address-list n prog-addr)
                            (create-canonical-address-list m addr))
                (member-p e (create-canonical-address-list m addr)))
           (equal (member-p e (create-canonical-address-list n prog-addr))
                  nil)))

(defthm no-duplicates-p-create-canonical-address-list
  (no-duplicates-p (create-canonical-address-list n x)))

(defthm subset-p-two-create-canonical-address-lists-general
  (implies (and (canonical-address-p y)
                (canonical-address-p (+ -1 j y))
                (<= y x)
                (<= (+ i x) (+ j y)))
           (subset-p (create-canonical-address-list i x)
                     (create-canonical-address-list j y)))
  :hints (("Goal" :in-theory (e/d (subset-p) nil))))

(defthm subset-p-two-create-canonical-address-lists-same-base-address
  (implies (and (canonical-address-p (+ m x))
                (natp m)
                (<= i m))
           (subset-p (create-canonical-address-list i x)
                     (create-canonical-address-list m x)))
  :hints (("Goal" :in-theory (e/d* (subset-p) ()))))

(defthm subset-p-addr-range-of-create-canonical-address-list
  (implies (and (canonical-address-p val2)
                (canonical-address-p (+ -1 m val2))
                (integerp val1)
                (<= val2 val1)
                (<= (+ n val1) (+ m val2)))
           (subset-p (addr-range n val1)
                     (create-canonical-address-list m val2)))
  :hints (("Goal" :in-theory (e/d (subset-p) nil))))

(defthm disjoint-p-two-create-canonical-address-lists-thm-0
  (implies (and (canonical-address-p y)
                (canonical-address-p (+ -1 j y))
                (< 0 j)
                (<= (+ i x) y))
           (disjoint-p (create-canonical-address-list i x)
                       (create-canonical-address-list j y)))
  :hints (("Goal" :in-theory (e/d (disjoint-p member-p) ()))))

(defthm disjoint-p-two-create-canonical-address-lists-thm-1
  (implies (and (canonical-address-p y)
                (integerp j)
                (< 0 j)
                (<= (+ j y) x))
           (disjoint-p (create-canonical-address-list i x)
                       (create-canonical-address-list j y)))
  :hints (("Goal" :in-theory (e/d (disjoint-p member-p) ()))))

(defthm disjoint-p-create-canonical-address-list-and-append
  (equal (disjoint-p (create-canonical-address-list i x)
                     (append (create-canonical-address-list j y)
                             (create-canonical-address-list k z)))
         (and (disjoint-p (create-canonical-address-list i x)
                          (create-canonical-address-list j y))
              (disjoint-p (create-canonical-address-list i x)
                          (create-canonical-address-list k z))))
  :hints (("Goal" :in-theory (e/d (disjoint-p
                                   create-canonical-address-list)
                                  ()))))

(defthm canonical-address-p-limits-thm-0
  ;; addr <= (+ k addr) < (+ i addr)
  ;; i is positive, k is positive, k < i
  (implies (and (canonical-address-p (+ i addr))
                (canonical-address-p addr)
                (< k i)
                (<= 0 k)
                (integerp k))
           (canonical-address-p (+ k addr))))

(defthm canonical-address-p-limits-thm-1
  ;; (+ -i addr) < (+ -k addr) < addr
  ;; i is negative, k is negative, k > i
  (implies (and (< k 0)
                (canonical-address-p (+ i addr))
                (< i 0)
                (< i k)
                (canonical-address-p addr)
                (integerp k))
           (canonical-address-p (+ k addr))))

(defthm canonical-address-p-limits-thm-2
  ;; (+ i addr) < (+ k addr) < (+ j addr)
  ;; i < k < j
  (implies (and (canonical-address-p (+ i addr))
                (canonical-address-p (+ j addr))
                (< i k)
                (< k j)
                (integerp addr)
                (integerp k))
           (canonical-address-p (+ k addr))))

(defthm canonical-address-p-limits-thm-3
  ;; (+ -i addr) <= addr <= (+ j addr)
  (implies (and (canonical-address-p (+ j addr))
                (canonical-address-p (+ (- i) addr))
                (natp i)
                (natp j)
                (integerp addr))
           (canonical-address-p addr))
  :hints (("Goal" :in-theory (e/d* (canonical-address-p signed-byte-p) ())))
  :rule-classes (:rewrite :forward-chaining))

(defthm canonical-address-p-limits-thm-4
  ;; addr <= (+ -j i addr) <= (addr + i)
  (implies (and (canonical-address-p (+ i addr))
                (canonical-address-p addr)
                (< j 0)
                (<= (- i) j)
                (natp i)
                (integerp j))
           (canonical-address-p (+ j (+ i addr))))
  :hints (("Goal" :in-theory (e/d* (canonical-address-p signed-byte-p) ())))
  :rule-classes (:rewrite :forward-chaining))

(encapsulate

 ()

 ;; The following rules come in useful when we know that a canonical
 ;; memory address is stored in a register.  These rules establish
 ;; that the value being written to a register is signed-byte-p 64, a fact we need
 ;; to know to relieve the hypotheses of rules like x86p-!rgfi.

 (defthm canonical-address-p-and-signed-byte-p-64-limits-0
   (implies (and (syntaxp (and (consp x)
                               (eq (car x) 'rgfi)))
                 (canonical-address-p x))
            (signed-byte-p 64 x))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (e/d (canonical-address-p) ()))))

 (defthm canonical-address-p-and-signed-byte-p-64p-limits-1
   (implies (and (syntaxp (and (consp x)
                               (eq (car x) 'rgfi)))
                 (canonical-address-p (+ a x)))
            (signed-byte-p 64 (+ a x)))
   :hints (("Goal" :in-theory (e/d (canonical-address-p) ()))))

 (defthm canonical-address-p-+-signed-byte-p-16-is-signed-byte-p-64
   (implies (and (canonical-address-p y)
                 (signed-byte-p 16 x))
            (signed-byte-p 64 (+ x y)))
   :hints (("Goal" :in-theory (e/d (canonical-address-p) ()))))

 (local (include-book "centaur/gl/gl" :dir :system))

 (local
  (def-gl-thm canonical-address-p-+-signed-byte-p-16-with-loghead-and-n64-to-i64-helper
    :hyp (and (canonical-address-p y)
              (signed-byte-p 16 x))
    :concl (equal (n64-to-i64
                   (part-select
                    (+ x (part-select
                          y
                          :low 0
                          :width 64))
                    :low 0 :width 64))
                  (+ x y))
    :g-bindings
    `((x   (:g-number ,(gl-int 0 2 64)))
      (y   (:g-number ,(gl-int 1 2 64))))))

 (defthm canonical-address-p-+-signed-byte-p-16-with-loghead-and-n64-to-i64
   (implies (and (canonical-address-p y)
                 (signed-byte-p 16 x))
            (equal (n64-to-i64
                    (part-select
                     (+ x (part-select
                           y
                           :low 0
                           :width 64))
                     :low 0 :width 64))
                   (+ x y)))
   :hints (("Goal" :use
            canonical-address-p-+-signed-byte-p-16-with-loghead-and-n64-to-i64-helper)))

 (defthm loghead-64-n64-to-i64-canonical-address
   (implies (canonical-address-p x)
            (equal (n64-to-i64 (loghead 64 x))
                   x))
   :hints (("Goal" :in-theory (e/d (canonical-address-p n64-to-i64) ()))))

 (defthm n64-to-i64-logead-64-x
   (implies (signed-byte-p 64 x)
            (equal (n64-to-i64 (loghead 64 x))
                   x))
   :hints (("Goal" :in-theory (e/d (canonical-address-p n64-to-i64) ()))))

 )

(defthmd create-canonical-address-list-split
  (implies (and (canonical-address-p addr)
                (canonical-address-p (+ k addr))
                (natp j)
                (natp k))
           (equal (create-canonical-address-list (+ k j) addr)
                  (append (create-canonical-address-list k addr)
                          (create-canonical-address-list j (+ k addr)))))
  :hints (("Goal" :in-theory (e/d* (canonical-address-p signed-byte-p)
                                   ()))))

;; ======================================================================

;; Pos and create-canonical-address-list:

(local
 (defthm instance-of-pos-1-accumulator-thm
   (implies (and (member-p e x)
                 (natp acc))
            (equal (pos-1 e x (+ 1 acc))
                   (+ 1 (pos-1 e x acc))))))

(defthm pos-and-create-canonical-address-list
  (implies (member-p addr
                     (create-canonical-address-list n prog-addr))
           (equal (pos addr
                       (create-canonical-address-list n prog-addr))
                  (- addr prog-addr)))
  :hints (("Goal" :in-theory (e/d (pos) ()))))


;; ======================================================================

;; Remove duplicate keys:

(define remove-duplicate-keys
  ((alst (alistp alst)))

  :parents (programmer-level-memory-utils)
  :enabled t

  (if (endp alst)
      nil
    (if (member-p (caar alst) (strip-cars (cdr alst)))
        (remove-duplicate-keys (cdr alst))
      (cons (car alst) (remove-duplicate-keys (cdr alst)))))

  ///

  (defthm addr-byte-alistp-remove-duplicate-keys
    (implies (addr-byte-alistp alst)
             (addr-byte-alistp (remove-duplicate-keys alst)))
    :rule-classes (:rewrite :type-prescription))

  (defthm member-p-remove-duplicate-keys
    (implies (and (addr-byte-alistp alst)
                  (member-p addr (strip-cars alst)))
             (member-p addr (strip-cars (remove-duplicate-keys alst))))
    :hints (("Goal" :in-theory (e/d (member-p) ()))))

  (defthm canonical-address-listp-of-strip-cars-remove-duplicate-keys
    (implies (addr-byte-alistp addr-lst)
             (canonical-address-listp
              (strip-cars (remove-duplicate-keys addr-lst))))
    :rule-classes (:rewrite :forward-chaining)))

(encapsulate
 ()

 (local (include-book "std/lists/reverse" :dir :system))

 (defthm member-p-and-strip-cars-of-remove-duplicate-keys
   (implies (member-p a (strip-cars xs))
            (member-p a (strip-cars (remove-duplicate-keys xs)))))

 (defthm member-p-and-remove-duplicate-keys-and-car
   (implies (consp xs)
            (member-p (car (car (remove-duplicate-keys xs)))
                      (strip-cars xs))))

 (defthm consp-remove-duplicate-keys
   (implies (consp (remove-duplicate-keys xs))
            (consp xs))
   :rule-classes :forward-chaining)

 (defthm subset-p-strip-cars-and-remove-duplicate-keys
   (subset-p (strip-cars (cdr (remove-duplicate-keys xs)))
             (strip-cars xs))
   :hints (("Goal" :in-theory (e/d (subset-p) ()))))

 (defthm member-p-strip-cars-of-remove-duplicate-keys
   ;; implies, equal, or iff?
   (implies (member-p a (strip-cars (remove-duplicate-keys xs)))
            (member-p a (strip-cars xs)))
   :rule-classes (:forward-chaining :rewrite))

 (defthm member-p-strip-cars-remove-duplicate-keys-and-rev
   ;; implies, equal, or iff?
   (implies (member-p a (strip-cars (remove-duplicate-keys xs)))
            (member-p a (strip-cars (acl2::rev xs))))
   :rule-classes (:forward-chaining :rewrite))

 (defthm canonical-address-listp-strip-cars-remove-duplicate-keys-addr-bytes-alistp
   (implies (and (subset-p addresses (strip-cars (remove-duplicate-keys addr-lst)))
                 (addr-byte-alistp addr-lst))
            (canonical-address-listp addresses))
   :hints (("Goal" :in-theory (e/d* (subset-p
                                     canonical-address-listp
                                     addr-byte-alistp)
                                    ())))
   :rule-classes :forward-chaining)

 )

;; ======================================================================

;; Lemmas about assoc-list:

(defthm assoc-list-of-append-with-subset-p
  (implies (subset-p xs (strip-cars term1))
           (equal (assoc-list xs (append term1 term2))
                  (assoc-list xs term1)))
  :hints (("Goal" :in-theory (e/d* (subset-p) ()))))


(defthm assoc-list-append-and-rev-lemma-helper-1
  (implies (and (canonical-address-listp x)
                (byte-listp y)
                (no-duplicates-p x)
                (equal (len x) (len y)))
           (equal (assoc-list x (append (acl2::rev (create-addr-bytes-alist x y)) term))
                  y)))


(defthm assoc-list-append-and-rev-lemma-helper-2
  (implies (and (canonical-address-listp a)
                (equal (len a) (len b))
                (disjoint-p x a)
                (consp term))
           (equal (assoc-list x (append (acl2::rev (create-addr-bytes-alist a b)) term))
                  (assoc-list x term)))
  :hints (("Goal" :in-theory (e/d* (disjoint-p) ()))))

;; (defthm assoc-list-append-and-rev-lemma
;;   ;; Bad lemma --- can cause stack overflows and looping.
;;   (implies (and (canonical-address-listp a)
;;              (byte-listp b)
;;              (no-duplicates-p a)
;;              (equal (len a) (len b))
;;              (consp term))
;;         (equal (assoc-list
;;                 x
;;                 (append (acl2::rev (create-addr-bytes-alist a b))
;;                         term))
;;                (if (disjoint-p x a)
;;                    (assoc-list x term)
;;                  (if (equal x a)
;;                      b
;;                    ;; Maybe another branch here that deals with
;;                    ;; when x is a subset of a?
;;                    (assoc-list x
;;                                (append (acl2::rev (create-addr-bytes-alist a b))
;;                                        term)))))))

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
  :hints (("Goal" :in-theory (e/d (program-at write-user-rflags !flgi-undefined !flgi)
                                  (rb)))))

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
  :hints (("Goal" :in-theory (e/d (pos rb) ()))))

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
