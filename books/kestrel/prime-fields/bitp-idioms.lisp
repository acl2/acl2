(in-package "PFIELD")

(include-book "prime-fields")
(local (include-book "prime-fields-rules"))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))

;; This book collects idioms for using prime field operations to express the
;; fact that a value is a bit.  These are useful for verifying R1CSes, etc.

;; The basic patterns for expressing (bitp x) are:
;; 0 = x*(x-1)
;; 0 = x*(1-x)
;; where * and - are of course modulo the prime.

;; 0 = x*(x-1) iff (x is 0 or 1)
(defthm bitp-idiom-1
  (implies (and (syntaxp (and (quotep p-1)
                              (quotep p)))
                (equal p-1 (+ -1 p))
                (fep x p)
                (rtl::primep p))
           (equal (equal 0 (mul x (add p-1 x p) p))
                  (bitp x)))
  :hints (("Goal" :in-theory (e/d (unsigned-byte-p)
                                  (pfield::MUL-OF-ADD-ARG2)))))

(defthm bitp-idiom-2
  (implies (and (syntaxp (and (quotep p-1)
                              (quotep p)))
                (equal p-1 (+ -1 p))
                (fep x p)
                (rtl::primep p))
           (equal (equal 0 (mul (add p-1 x p) x p))
                  (bitp x)))
  :hints (("Goal" :in-theory (e/d (unsigned-byte-p)
                                  (pfield::MUL-OF-ADD-ARG2)))))

(defthm bitp-idiom-with-constant-1
  (implies (and (syntaxp (and (quotep k1)
                              (quotep k2)))
                (equal k1 (+ 1 k2))
                (fep k2 p) ;(integerp k2)
                (fep x p)
                (rtl::primep p))
           (equal (equal 0 (mul (add k1 x p) (add k2 x p) p))
                  (bitp (add k1 x p))))
  :hints (("Goal" :use (:instance bitp-idiom-1
                                  (p-1 (+ -1 p))
                                  (x (add k1 x p)))
           :in-theory (e/d (pfield::add-of-+-arg2)
                           (bitp-idiom-1
                            pfield::mul-of-add-arg2
                            pfield::mul-of-add-arg1
                            ;; prevent loops:
                            ;;acl2::+-of-minus
                            acl2::mod-of-minus-arg1)))))

(defthm bitp-idiom-with-constant-2
  (implies (and (syntaxp (and (quotep k1)
                              (quotep k2)))
                (equal k1 (+ 1 k2))
                (fep k2 p) ;(integerp k2)
                (fep x p)
                (rtl::primep p))
           (equal (equal 0 (mul (add k2 x p) (add k1 x p) p))
                  (bitp (add k1 x p))))
  :hints (("Goal" :use (:instance bitp-idiom-with-constant-1)
           :in-theory '(mul-commutative))))

;; Or pull the neg out of the mul
(defthm bitp-idiom
  (implies (and (rtl::primep p)
                (fep x p))
           (equal (equal 0 (mul (add 1 (neg x p) p)
                                (neg x p)
                                p))
                  (bitp x)))
  :hints (("Goal" :in-theory (e/d (bitp) (pfield::mul-of-add-arg1
                                          pfield::mul-of-add-arg2)))))

(defthm bitp-idiom-with-added-constant
  (implies (and (syntaxp (and (quotep k)
                              (quotep k-1)))
                (equal k-1 (pfield::sub k 1 p))
;                (fep k p)
                (primep p))
           (equal (equal 0 (mul (add k x p) (add k-1 x p) p))
                  (bitp (add k x p))))
  :hints (("Goal" :use (:instance PFIELD::BITP-IDIOM-1
                                  (x (add k x p))
                                  (p-1 -1)
                                  (p p))
           :in-theory (disable PFIELD::BITP-IDIOM-1
;                               ACL2::BITP-BECOMES-UNSIGNED-BYTE-P
                               PFIELD::MUL-OF-ADD-ARG1
                               PFIELD::MUL-OF-ADD-ARG2))))

(defthm bitp-idiom-with-added-constant-alt
  (implies (and (syntaxp (and (quotep k)
                              (quotep k-1)))
                (equal k-1 (pfield::sub k 1 p))
;                (fep k p)
                (primep p))
           (equal (equal 0 (mul (add k-1 x p) (add k x p) p))
                  (bitp (add k x p))))
  :hints (("Goal" :use (:instance bitp-idiom-with-added-constant)
           :in-theory '(mul-commutative))))
