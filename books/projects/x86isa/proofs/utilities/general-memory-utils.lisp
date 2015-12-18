;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")

(include-book "basics" :ttags :all :dir :proof-utils)
(include-book "disjoint" :dir :proof-utils)

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))

;; ======================================================================

(defsection general-memory-utils
  :parents (proof-utilities)
  )

(local (xdoc::set-default-parents general-memory-utils))

;; ===================================================================

;; Some lemmas for constructing a number from its constituent parts:

(defthm combining-logior-of-loghead-and-ash-logtail
  (implies (and (natp x)
                (natp n))
           (equal (logior (loghead n x)
                          (ash (logtail n x) n))
                  x))
  :hints (("Goal" :in-theory (e/d* (ihsext-inductions
                                    ihsext-recursive-redefs)
                                   ()))))

(defthmd combining-logior-of-loghead-and-ash-loghead-logtail-1
  (implies (and (natp n)
                (natp m))
           (equal (loghead m (logtail n x))
                  (ash (loghead (+ m n) x) (- n))))
  :hints (("Goal" :in-theory (e/d* (ihsext-inductions
                                    ihsext-recursive-redefs
                                    zip)
                                   ()))))

(defthmd combining-logior-of-loghead-and-ash-loghead-logtail-2
  (implies (and (natp n)
                (natp m))
           (equal (loghead n x)
                  (loghead n (loghead (+ m n) x))))
  :hints (("Goal" :in-theory (e/d* ()
                                   (ihsext-recursive-redefs
                                    ihsext-inductions)))))


(defthm combining-logior-of-loghead-and-ash-loghead-logtail
  (implies (and (natp n)
                (natp m))
           (equal (logior (loghead n x)
                          (ash (loghead m (logtail n x)) n))
                  (loghead (+ m n) x)))
  :hints (("Goal"
           :use ((:instance combining-logior-of-loghead-and-ash-loghead-logtail-2))
           :in-theory (e/d* (combining-logior-of-loghead-and-ash-loghead-logtail-1)
                            (bitops::logtail-of-loghead
                             bitops::loghead-of-loghead-1)))))

(defthm combining-logior-of-loghead-logtail-and-ash-logtail
  (implies (and (natp n)
                (natp m)
                (equal m+n (+ m n))
                (integerp x))
           (equal (logior (loghead n (logtail m x))
                          (ash (logtail m+n x) n))
                  (logtail m x)))
  :hints (("Goal" :in-theory (e/d* (ihsext-inductions
                                    ihsext-recursive-redefs)
                                   ()))))

(defthm combining-logior-of-loghead-logtail-and-ash-loghead-logtail
  (implies (and (natp m)
                (natp n)
                (natp o)
                (equal m+n (+ m n)))
           (equal (logior (loghead n (logtail m x))
                          (ash (loghead o (logtail m+n x)) n))
                  (loghead (+ n o) (logtail m x))))
  :hints (("Goal" :in-theory (e/d* (ihsext-inductions
                                    ihsext-recursive-redefs
                                    zip)
                                   ()))))


(defthm greater-logbitp-of-unsigned-byte-p
  (implies (and (unsigned-byte-p n x)
                (natp m)
                (< n m))
           (equal (logbitp m x) nil))
  :hints (("Goal" :in-theory (e/d* (ihsext-inductions
                                    ihsext-recursive-redefs
                                    unsigned-byte-p)
                                   ())))
  :rule-classes ((:rewrite)
                 (:rewrite :corollary
                           (implies (and (< x (expt 2 m))
                                         (natp x)
                                         (natp m))
                                    (equal (logbitp m x) nil)))))

(defthm loghead-of-non-integerp
  (implies (not (integerp x))
           (equal (loghead n x) 0))
  :hints (("Goal" :in-theory (e/d* (loghead mod) ()))))

(local
 (encapsulate
  ()

  (local (include-book "arithmetic-3/top" :dir :system))

  (defthm ash-and-plus
    (implies (posp n)
             (equal (+ 8 (ash (+ -1 n) 3))
                    (ash n 3)))
    :hints (("Goal" :in-theory (e/d* (ash) ()))))

  (defthm ash-and-minus
    (implies (posp n)
             (equal (+ -8 (ash n 3))
                    (ash (+ -1 n) 3)))
    :hints (("Goal" :in-theory (e/d* (ash) ()))))

  (defthm ash-n-3-bound
    (implies (and (not (zp n))
                  (natp n))
             (<= 8 (ash n 3)))
    :hints (("Goal" :in-theory (e/d* (ash) ())))
    :rule-classes :linear)

  (defthm ash-separate-out
    (implies (natp n)
             (equal (ash (+ 1 n) 3)
                    (+ 8 (ash n 3))))
    :hints (("Goal" :in-theory (e/d* (ash) ()))))))

;; ======================================================================

;; Lemmas about byte-ify and combine-bytes:

(local
 (defthmd byte-ify-general-acc-helper-thm
   (implies (and (byte-listp acc1)
                 (byte-listp acc2)
                 (integerp val)
                 (natp n))
            (equal (byte-ify-general n val (append acc1 acc2))
                   (append (acl2::rev acc2) (byte-ify-general n val acc1))))
   :hints (("Goal" :in-theory (e/d* (byte-ify-general) ())))))

(defthm byte-ify-general-acc-thm
  (implies (and (syntaxp (not (and (quotep acc)
                                   (eq (car (unquote acc)) nil))))
                (byte-listp acc)
                (integerp val)
                (natp n))
           (equal (byte-ify-general n val acc)
                  (append (acl2::rev acc) (byte-ify-general n val nil))))
  :hints (("Goal" :use ((:instance byte-ify-general-acc-helper-thm
                                   (acc2 acc)
                                   (acc1 nil))))))


(defthm combine-bytes-and-byte-ify
  (implies (natp n)
           (equal (combine-bytes (byte-ify n x))
                  (loghead (ash n 3) x)))
  :hints (("Goal" :in-theory (e/d* (combine-bytes
                                    byte-ify-and-byte-ify-general
                                    byte-ify-general)
                                   ()))))

(defthmd remove-loghead-from-byte-ify
  ;; We keep this rule disabled because most of the times, removing loghead
  ;; from within byte-ify isn't really necessary.
  (implies (equal m (ash n 3))
           (equal (byte-ify n (loghead m x))
                  (byte-ify n x)))
  :hints (("Goal" :in-theory (e/d* (byte-ify-and-byte-ify-general
                                    byte-ify-general
                                    ihsext-recursive-redefs
                                    ihsext-inductions)
                                   ()))))

(defthmd combine-bytes-and-byte-ify-inequality-lemma
  ;; This is an expensive rule, so we keep it disabled. As it is, we don't need
  ;; this rule very often.
  (implies (and (equal bytes (byte-ify n x))
                (natp n)
                (not (equal (loghead (ash n 3) x) val)))
           (equal (equal (combine-bytes bytes) val) nil))
  :hints (("Goal" :in-theory (e/d* (combine-bytes
                                    byte-ify-and-byte-ify-general
                                    byte-ify-general)
                                   ()))))

(defthmd remove-loghead-from-combine-bytes
  ;; This is an expensive rule, so we keep it disabled. As it is, we don't need
  ;; this rule very often.
  (implies (and (equal m (ash (len bytes) 3))
                (byte-listp bytes))
           (equal (loghead m (combine-bytes bytes))
                  (combine-bytes bytes)))
  :hints (("Goal" :in-theory (e/d* (combine-bytes
                                    ihsext-recursive-redefs
                                    ihsext-inductions)
                                   ()))))

(defthm byte-ify-and-combine-bytes
  ;; [Shilpi]: Generalize this to remove the len hyp...
  (implies (and (equal (len byte-list) n)
                (byte-listp byte-list))
           (equal (byte-ify n (combine-bytes byte-list))
                  byte-list))
  :hints (("Goal"
           :in-theory (e/d* (combine-bytes
                             byte-ify-and-byte-ify-general
                             byte-ify-general)
                            ()))))

;; ======================================================================

;; Since reasoning about memory is largely list-based, here are some
;; utilities to reason about lists:

;; Some misc. lemmas:

(defthm append-x-nil-is-x
  (equal (append nil x) x))

(defthm cdr-append-is-append-cdr
  (implies (consp x)
           (equal (cdr (append x y))
                  (append (cdr x) y))))

(defthm car-of-append
  (implies (consp x)
           (equal (car (append x y))
                  (car x))))

(defthm consp-append
  (implies (consp x)
           (consp (append x y)))
  :rule-classes :type-prescription)

(local
 (defthm append-equal
   (implies (equal (append x a) (append x b))
            (equal a b))
   :rule-classes :forward-chaining))

(local
 (defthm append-3
   (equal (append (append x y) z)
          (append x y z))))

(defthm canonical-address-listp-append
  (implies (and (canonical-address-listp x)
                (canonical-address-listp y))
           (canonical-address-listp (append x y)))
  :rule-classes (:rewrite :type-prescription))

(defthm addr-byte-alistp-append
  (implies (and (addr-byte-alistp x)
                (addr-byte-alistp y))
           (addr-byte-alistp (append x y)))
  :rule-classes (:rewrite :type-prescription))

(defthm addr-byte-alistp-rev
  (implies (addr-byte-alistp alst)
           (addr-byte-alistp (acl2::rev alst))))

(defthm strip-cdrs-addr-byte-alistp-is-byte-listp
  (implies (addr-byte-alistp addr-lst)
           (byte-listp (strip-cdrs addr-lst)))
  :rule-classes (:type-prescription :rewrite))

(defthm strip-cars-addr-byte-alistp-is-canonical-address-listp
  (implies (addr-byte-alistp alst)
           (canonical-address-listp (strip-cars alst)))
  :rule-classes (:type-prescription :rewrite))

(defthm-usb addr-byte-alistp-assoc-bound
  :hyp (and (addr-byte-alistp addr-lst)
            (member-p addr (strip-cars addr-lst)))
  :bound 8
  :concl (cdr (assoc-equal addr addr-lst)))

(defthm canonical-address-p-addr-byte-alistp
  (implies (and (addr-byte-alistp addr-lst)
                (member-p addr (strip-cars addr-lst)))
           (canonical-address-p addr))
  :rule-classes :forward-chaining)

;; ----------------------------------------------------------------------

(define assoc-list ((slst true-listp)
                    (blst alistp))

  :enabled t

  ;; (assoc-list  '(a b c) '((a . 1) (b . 2) (c . 3) (d . 4))) =>
  ;; '(1 2 3)

  (if (or (endp slst)
          (endp blst))
      nil
    (cons (cdr (assoc-equal (car slst) blst))
          (assoc-list (cdr slst) blst)))

  ///

  (local (include-book "std/lists/nthcdr" :dir :system))

  (defthm assoc-list-and-cons
    (implies (and (not (member-p ax cx))
                  (consp term))
             (equal (assoc-list cx (cons (cons ax ay) term))
                    (assoc-list cx term))))

  (defthm assoc-list-and-create-addr-bytes-alist
    (implies (and (true-listp y)
                  ;; (consp (create-addr-bytes-alist (cdr x) (cdr y)))
                  (equal (len x) (len y))
                  ;; (not (zp (len (cdr y))))
                  (<= 2 (len y))
                  (no-duplicates-p x))
             (equal (assoc-list x (create-addr-bytes-alist x y))
                    y)))

  (defthm assoc-and-append-with-list-cons
    (implies (not (equal ax cx))
             (equal (assoc-equal cx (append term (list (cons ax ay))))
                    (assoc-equal cx term))))

  (defthm assoc-list-of-append-with-list-cons
    (implies (and (not (member-p ax cx))
                  (consp term))
             (equal (assoc-list cx (append term (list (cons ax ay))))
                    (assoc-list cx term))))

  (defthm assoc-list-of-rev-of-create-addr-bytes-alist
    (implies (and (true-listp y)
                  (equal (len x) (len y))
                  (<= 2 (len y))
                  (no-duplicates-p x))
             (equal (assoc-list x (acl2::rev (create-addr-bytes-alist x y)))
                    y)))

  )

;; ----------------------------------------------------------------------

;; Some lemmas about addr-range:

(defthm member-p-addr-range
  (implies (and (<= prog-addr addr)
                (< addr (+ n prog-addr))
                (integerp n)
                (integerp addr)
                (integerp prog-addr))
           (equal (member-p addr (addr-range n prog-addr))
                  t)))

(defthm member-p-addr-range-from-member-p-addr-range
  (implies (and (member-p x (addr-range j y))
                (integerp l)
                (< j l))
           (equal (member-p x (addr-range l y))
                  t)))

(defthm not-member-p-addr-range
  (implies (and (or (< addr prog-addr)
                    (<= (+ n prog-addr) addr))
                (integerp n)
                (< 0 n)
                (integerp prog-addr))
           (equal (member-p addr (addr-range n prog-addr))
                  nil)))

(defthm not-member-p-addr-range-from-not-member-p-addr-range
  (implies (and (not (member-p x (addr-range j y)))
                (integerp j)
                (<= l j))
           (equal (member-p x (addr-range l y))
                  nil)))

(defthm subset-p-two-addr-ranges
  (implies (and (integerp x)
                (integerp y)
                (<= y x)
                (<= (+ i x) (+ j y))
                (integerp j))
           (subset-p (addr-range i x)
                     (addr-range j y)))
  :hints (("Goal" :in-theory (e/d (subset-p) nil))))

(defthm not-disjoint-p-two-addr-ranges-thm
  (implies (and (integerp x)
                (integerp y)
                (integerp i)
                (integerp j)
                (<= x y)
                (< y (+ i x))
                (<= (+ i x) (+ j y)))
           (equal (disjoint-p (addr-range i x)
                              (addr-range j y))
                  nil))
  :hints (("Goal" :in-theory (e/d (disjoint-p member-p) ()))))

(defthm disjoint-p-two-addr-ranges-thm-0
  (implies (and (integerp x)
                (integerp y)
                (integerp j)
                (< 0 j)
                (<= (+ i x) y))
           (disjoint-p (addr-range i x)
                       (addr-range j y)))
  :hints (("Goal" :in-theory (e/d (disjoint-p member-p) ()))))

(defthm disjoint-p-two-addr-ranges-thm-1
  (implies (and (integerp x)
                (integerp y)
                (integerp j)
                (< 0 j)
                (<= (+ j y) x))
           (disjoint-p (addr-range i x)
                       (addr-range j y)))
  :hints (("Goal" :in-theory (e/d (disjoint-p member-p) ()))))

;; (defthm disjoint-p-two-addr-ranges-thm-2
;;   (implies (and (disjoint-p (addr-range i x)
;;                             (addr-range j y))
;;                 (integerp i)
;;                 (integerp j)
;;                 (<= k i)
;;                 (<= l j))
;;            (disjoint-p (addr-range k x)
;;                        (addr-range l y)))
;;   :hints (("Goal" :in-theory (e/d (disjoint-p member-p) ()))))

(defthm disjoint-p-two-addr-ranges-thm-2
  (implies (and (disjoint-p (addr-range i x)  (addr-range j y))
                (subset-p   (addr-range ia a) (addr-range i x))
                (subset-p   (addr-range jb b) (addr-range j y)))
           (disjoint-p (addr-range ia a) (addr-range jb b)))
  :hints (("Goal" :in-theory (e/d (disjoint-p member-p) ()))))

(defthm disjoint-p-two-addr-ranges-thm-3
  (implies (and (disjoint-p (addr-range j y)  (addr-range i x))
                (subset-p   (addr-range ia a) (addr-range i x))
                (subset-p   (addr-range jb b) (addr-range j y)))
           (disjoint-p (addr-range ia a) (addr-range jb b)))
  :hints (("Goal" :use ((:instance disjoint-p-commutative
                                   (a (addr-range j y))
                                   (b (addr-range i x)))))))

(defthm consp-addr-range
  (implies (posp n)
           (consp (addr-range n val)))
  :rule-classes (:type-prescription :rewrite))

(defthm car-addr-range
  (implies (posp n)
           (equal (car (addr-range n val))
                  (ifix val))))

(defthm cdr-addr-range
  (implies (and (posp n)
                (integerp val))
           (equal (cdr (addr-range n val))
                  (addr-range (1- n) (1+ val)))))


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

(defthm instance-of-pos-1-accumulator-thm
  (implies (and (member-p e x)
                (natp acc))
           (equal (pos-1 e x (+ 1 acc))
                  (+ 1 (pos-1 e x acc)))))

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
