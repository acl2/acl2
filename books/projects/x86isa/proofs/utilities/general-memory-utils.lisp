;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")

(include-book "basics" :ttags :all :dir :proof-utils)
(include-book "disjoint" :dir :proof-utils)

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))

;; ===================================================================

;; Some lemmas for combine-bytes and byte-ify:

(local (include-book "arithmetic/top-with-meta" :dir :system))

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

(local
 (defthm combine-bytes-and-byte-ify-specific
   (implies (and (or (equal n 2)
                     (equal n 4)
                     (equal n 8)
                     (equal n 16)))
            (equal (combine-bytes (byte-ify n x))
                   (loghead (ash n 3) x)))
   :hints (("Goal" :in-theory (e/d* (combine-bytes byte-ify)
                                    ())))))

(defthm loghead-of-non-integerp
  (implies (not (integerp x))
           (equal (loghead n x) 0))
  :hints (("Goal" :in-theory (e/d* (loghead mod) ()))))

(encapsulate
 ()

 (local (include-book "arithmetic-3/top" :dir :system))

 (defthm ash-and-plus
   (implies (posp n)
            (equal (+ 8 (ash (+ -1 n) 3))
                   (ash n 3)))
   :hints (("Goal" :in-theory (e/d* (ash) ())))))

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

(local
 (defthm combine-bytes-and-byte-ify-general
   (implies (natp n)
            (equal (combine-bytes (byte-ify-general n x nil))
                   (loghead (ash n 3) x)))
   :hints (("Goal" :in-theory (e/d* (combine-bytes byte-ify byte-ify-general)
                                    ())))))

(defthm combine-bytes-and-byte-ify
  (implies (natp n)
           (equal (combine-bytes (byte-ify n x))
                  (loghead (ash n 3) x)))
  :hints (("Goal" :in-theory (e/d* (byte-ify) ()))))

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
