;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")

(include-book "basics" :ttags :all :dir :proof-utils)
(include-book "disjoint" :dir :proof-utils)

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))

;; ===================================================================

;; First, some arithmetic lemmas useful for both linear and physical
;; memory: these rules are disabled --- enable them locally when
;; needed.

(encapsulate
 ()

 (local (include-book "arithmetic-5/top" :dir :system))

 (local (in-theory (disable logior-expt-to-plus-quotep)))

 (defthm n32p-lower-16-val-logior-loghead-ash-helper
   (implies (n32p val)
            (equal (logior (loghead 8 val)
                           (ash (loghead 8 (logtail 8 val)) 8))
                   (+ (loghead 8 val)
                      (ash (loghead 8 (logtail 8 val)) 8))))
   :hints (("Goal" :in-theory
            (e/d (logior-expt-to-plus-quotep) ()))))

 (defthm n32p-lower-16-val-logior-loghead-ash
   (implies (n32p val)
            (equal (logior (loghead 8 val)
                           (ash (loghead 8 (logtail 8 val)) 8))
                   (loghead 16 val)))
   :hints (("Goal" :in-theory
            (e/d (loghead logtail)
                 (acl2::normalize-factors-gather-exponents
                  n32p-lower-16-val-logior-loghead-ash-helper))
            :use ((:instance
                   n32p-lower-16-val-logior-loghead-ash-helper)))))

 (defthm n32p-upper-16-val-logior-loghead-ash-helper
   (implies (n32p val)
            (equal (logior (loghead 8 (logtail 16 val))
                           (ash (logtail 24 val) 8))
                   (+ (loghead 8 (logtail 16 val))
                      (ash (logtail 24 val) 8))))
   :hints (("Goal" :in-theory
            (e/d (logior-expt-to-plus-quotep) ()))))

 (defthm n32p-upper-16-val-logior-loghead-ash
   (implies (n32p val)
            (equal (logior (loghead 8 (logtail 16 val))
                           (ash (logtail 24 val) 8))
                   (logtail 16 val)))
   :hints (("Goal" :in-theory
            (e/d (loghead logtail)
                 (acl2::normalize-factors-gather-exponents
                  n32p-upper-16-val-logior-loghead-ash-helper))
            :use ((:instance n32p-upper-16-val-logior-loghead-ash-helper)))))

 )

(defthm n32p-upper-16-in-8s-val-logior-loghead-ash-helper
  (implies (n32p val)
           (equal (logior (loghead 8 val)
                          (ash (logtail 16 val) 16)
                          (ash (loghead 8 (logtail 8 val)) 8))
                  (logior (loghead 16 val)
                          (ash (logtail 16 val) 16))))
  :hints (("Goal"
           :in-theory (e/d ()
                           (n32p-lower-16-val-logior-loghead-ash
                            n32p-lower-16-val-logior-loghead-ash-helper
                            putting-logior-loghead-ash-logtail-together))
           :use ((:instance n32p-lower-16-val-logior-loghead-ash)))))

(defthm n32p-upper-16-in-8s-val-logior-loghead-ash
  (implies (n32p val)
           (equal (logior (loghead 8 val)
                          (ash (logtail 16 val) 16)
                          (ash (loghead 8 (logtail 8 val)) 8))
                  val)))

(in-theory (disable n32p-upper-16-in-8s-val-logior-loghead-ash-helper
                    n32p-upper-16-in-8s-val-logior-loghead-ash
                    n32p-lower-16-val-logior-loghead-ash-helper
                    n32p-lower-16-val-logior-loghead-ash
                    n32p-upper-16-val-logior-loghead-ash-helper
                    n32p-upper-16-val-logior-loghead-ash))

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

(defun assoc-list (slst blst)

  ;; (assoc-list  '(a b c) '((a . 1) (b . 2) (c . 3) (d . 4))) =>
  ;; '(1 2 3)

  (declare (xargs :guard (and (true-listp slst)
                              (alistp blst))))
  (if (endp slst)
      nil
    (cons (cdr (assoc-equal (car slst) blst))
          (assoc-list (cdr slst) blst))))

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

;; (i-am-here)

;; (defthm disjoint-p-wart-lemma-1
;;   (implies (and (integerp addr1)
;;                 (integerp addr2)
;;                 (disjoint-p (addr-range 8 addr1)
;;                             (addr-range 8 addr2)))
;;            (disjoint-p (addr-range 4 addr2)
;;                        (addr-range 4 (+ 4 addr1))))
;;   :hints (("Goal" :use ((:instance disjoint-p-commutative
;;                                    (a (addr-range 4 addr2))
;;                                    (b (addr-range 4 (+ 4 addr1))))))))

;; (defaxiom check-1
;;   (implies (disjoint-p (addr-range 8 addr1)
;;                        (addr-range 8 addr2))
;;            (and (disjoint-p (addr-range 4 addr1)
;;                             (addr-range 4 addr2))
;;                 (disjoint-p (addr-range 4 addr1)
;;                             (addr-range 4 (+ 4 addr2)))
;;                 (disjoint-p (addr-range 4 (+ 4 addr2))
;;                             (addr-range 4 addr1))
;;                 (disjoint-p (addr-range 4 (+ 4 addr1))
;;                             (addr-range 4 addr2))
;;                 (disjoint-p (addr-range 4 addr2)
;;                             (addr-range 4 (+ 4 addr1)))
;;                 (disjoint-p (addr-range 4 (+ 4 addr1))
;;                             (addr-range 4 (+ 4 addr2)))
;;                 (disjoint-p (addr-range 4 (+ 4 addr2))
;;                             (addr-range 4 (+ 4 addr1))))))

;; (defaxiom check-2
;;   (implies (disjoint-p (addr-range 8 addr1)
;;                        (addr-range 8 addr2))
;;            (disjoint-p (addr-range 4 addr2)
;;                        (addr-range 4 (+ 4 addr1)))))

;; (defaxiom check-3
;;   (disjoint-p (addr-range 4 addr1)
;;               (addr-range 4 (+ 4 addr1))))
