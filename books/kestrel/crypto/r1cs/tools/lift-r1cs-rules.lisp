(in-package "R1CS")

;; todo: reduce:
(include-book "../gadgets")
(include-book "../gadgets/xor-rules")
(include-book "kestrel/axe/axe-syntax" :dir :system)
(include-book "kestrel/axe/axe-syntax-functions-bv" :dir :system) ;for bind-bv-size-axe (todo: separate out the axe rules)
(include-book "kestrel/prime-fields/prime-fields-rules" :dir :system)
(include-book "kestrel/prime-fields/bv-rules" :dir :system)
(include-book "kestrel/bv/bvcat" :dir :system)
(include-book "kestrel/arithmetic-light/ceiling-of-lg" :dir :system)
(include-book "kestrel/arithmetic-light/lg" :dir :system)
(local (include-book "kestrel/bv/rules" :dir :system)) ;for acl2::slice-of-sum-cases, make local?
(local (include-book "kestrel/alists-light/assoc-equal" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
;(local (include-book "kestrel/arithmetic-light/mod2" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
;(local (include-book "kestrel/arithmetic-light/expt2" :dir :system))
(local (include-book "kestrel/arithmetic-light/minus" :dir :system))

;dup
;rename
(defthm bvcat-upper-bound-linear
  (implies (and (natp lowsize)
                (natp highsize))
           (< (acl2::bvcat highsize highval lowsize lowval) (expt 2 (+ highsize lowsize))))
  :rule-classes (:linear :rewrite)
  :hints (("Goal" :use (:instance ACL2::UNSIGNED-BYTE-P-OF-BVCAT
                                  (highsize highsize)
                                  (lowsize lowsize)
                                  (highval highval)
                                  (lowval lowval)
                                  (n (+ highsize lowsize)))
           :in-theory (disable ACL2::UNSIGNED-BYTE-P-OF-BVCAT ;todo: get rid of some of these
                               ACL2::UNSIGNED-BYTE-P-OF-BVCAT-GEN
                               ACL2::UNSIGNED-BYTE-P-OF-BVCAT-GEN2
                               ACL2::UNSIGNED-BYTE-P-OF-BVCAT-ALL-CASES
                               ACL2::UNSIGNED-BYTE-P-OF-BVCAT2))))

;; Turn large constants into more readable negative constants
(defthm mul-normalize-constant-arg1
  (implies (and (syntaxp (and (quotep x)
                              (quotep p)))
                (< (floor p 2) x) ;gets computed
                )
           (equal (mul x y p)
                  (mul (- x p) ;gets computed
                       y
                       p)))
  :hints (("Goal" :in-theory (enable mul acl2::mod-sum-cases))))

(defthm mul-normalize-constant-arg1-alt
  (implies (and (syntaxp (and (quotep x)
                              (quotep p)))
                (< x (- (floor p 2))) ;gets computed
                )
           (equal (mul x y p)
                  (mul (+ x p) ;gets computed
                       y
                       p)))
  :hints (("Goal" :in-theory (enable mul acl2::mod-sum-cases))))

(defthm add-of-+-of--1
  (implies (integerp x)
           (equal (add x (+ -1 p) p)
                  (add x -1 p)))
  :hints (("Goal" :in-theory (enable add))))

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
           :in-theory (disable bitp-idiom-with-constant-1))))

(defthm add-of-+-of-p-arg2
  (equal (add x (+ y p) p)
         (add x y p))
  :hints (("Goal" :in-theory (enable add))))

(defthm add-of---of-p-arg2
  (implies (posp p)
           (equal (add x (- p) p)
                  (mod (ifix x) p)))
  :hints (("Goal" :in-theory (enable add))))

(defthm add-of---same-arg2
  (equal (add k (- k) p)
         0)
  :hints (("Goal" :in-theory (enable add))))

(defthm equal-of-add-of---and-0
 (implies (and (posp p)
               (integerp x)
               (integerp k))
          (equal (equal (add x (- k) p) 0)
                 (equal (mod (ifix x) p)
                        (mod (ifix k) p))))
 :hints (("Goal" :in-theory (enable add acl2::mod-sum-cases))))

(defthmd add-of-unary---arg2
  (equal (add x (- k) p)
         (add x (neg k p) p))
  :hints (("Goal" :in-theory (enable add neg))))

(include-book "kestrel/prime-fields/equal-of-add-move-negs-bind-free" :dir :system)
(include-book "kestrel/prime-fields/equal-of-add-cancel-bind-free" :dir :system)

(defthm bitp-of-add-of-constant
  (implies (and (fep x p)
                (fep k p)
;                (equal k (+ -1 p))
                (posp p)
                (< 1 p))
           (equal (bitp (add k (neg x p) p))
                  (bitp (add (+ 1 (- k)) x p))))
  :hints (("Goal" :in-theory (e/d (pfield::add-of-+-arg2 add-of-unary---arg2)
                                  (acl2::bitp-becomes-unsigned-byte-p
                                   acl2::mod-of-minus-arg1)))))

(defthmd bitp-of-add-of-constant-negated
  (implies (and (fep x p)
                (fep k p)
                (posp p)
                (< 1 p))
           (equal (bitp (add k x p))
                  (bitp (add (+ 1 (- k)) (neg x p) p))))
  :hints (("Goal" :use (:instance bitp-of-add-of-constant
                                  (x (neg x p)))
           :in-theory (disable bitp-of-add-of-constant))))

;fairly agressive
(defthmd bitp-of-add-of-constant-negated-special
  (implies (and (syntaxp (and (quotep k)
                              (quotep k2)))
                (< k2 0) ;prevent loops
                (fep x p)
                (fep k p)
                (posp p)
                (< 1 p))
           (equal (bitp (add k (add (mul k2 x p) y p) p))
                  (bitp (add (+ 1 (- k)) (neg (add (mul k2 x p) y p) p) p))))
  :hints (("Goal" :use (:instance bitp-of-add-of-constant-negated
                                  (x (add (mul k2 x p) y p)))
           :in-theory (disable bitp-of-add-of-constant-negated))))

(local (in-theory (disable ACL2::BITP-BECOMES-UNSIGNED-BYTE-P)))

;; Note that there is no digit in the 1's place, likely because the
;; multiplication of that bit by 1 gets simplified, making that addend
;; "lighter".  So this is sort of a base case when creating a big BVCAT of
;; several bits.
(defthm bvcat-intro-2-4
  (implies (and (acl2::bitp x)
                (acl2::bitp y)
                (posp p))
           (equal (add
                   (mul 2 x p)
                   (add
                    (mul 4 y p)
                    z
                    p)
                   p)
                  (add (acl2::bvcat 1 y 2 (acl2::bvcat 1 x 1 0))
                       z
                       p)))
  :hints (("Goal" :in-theory (enable acl2::bitp))))

(defthm bvcat-intro-4-2
  (implies (and (acl2::bitp x)
                (acl2::bitp y)
                (posp p))
           (equal (add
                   (mul 4 x p)
                   (add
                    (mul 2 y p)
                    z
                    p)
                   p)
                  (add (acl2::bvcat 1 x 2 (acl2::bvcat 1 y 1 0))
                       z
                       p)))
  :hints (("Goal" :in-theory (enable acl2::bitp))))

(defthm bvcat-intro-4-2-simple
  (implies (and (acl2::bitp x)
                (acl2::bitp y)
                (POSP P))
           (equal (ADD
                   (MUL '4 x p)
                   (MUL '2 y p)
                   p)
                  (mod (acl2::bvcat 1 x 2 (acl2::bvcat 1 y 1 0)) p)))
  :hints (("Goal" :in-theory (enable acl2::bitp))))

;might need a commuted version
(defthm add-of-bvcat-of-add-of-mul-combine
  (implies (and (syntaxp (and (quotep k)
                              (quotep highsize)
                              (quotep lowsize)))
                (equal k (expt 2 (+ highsize lowsize)))
                (acl2::bitp z)
                (posp p)
                (posp highsize)
                (posp lowsize)
                )
           (equal (add (acl2::bvcat highsize x lowsize y) (add (mul k z p) w p) p)
                  (add (acl2::bvcat 1 z (+ highsize lowsize) (acl2::bvcat highsize x lowsize y)) w p)))
  :hints (("Goal" :in-theory (e/d (bitp ACL2::LOGAPP add)
                                  (;ACL2::<-OF-BVCAT
                                   ACL2::UNSIGNED-BYTE-P-OF-+-WHEN-<-OF-LOGTAIL-AND-EXPT
                                   ACL2::MOD-WHEN-INTEGERP-OF-QUOTIENT
                                   ))
           :expand ((:free (z) (ACL2::BVCAT 1 z (+ HIGHSIZE lowsize) (ACL2::BVCAT highsize X lowsize Y)))))))

;; no w term
;todo: generalize or use something like add-of-mul-of-power-of-2-and-add?
;rename
(defthm add-of-bvcat-of-add-of-mul-combine-simp
  (implies (and (syntaxp (and (quotep k)
                              (quotep highsize)
                              (quotep lowsize)))
                (equal k (expt 2 (+ highsize lowsize)))
                (acl2::bitp z)
                (posp p)
                (posp highsize)
                (posp lowsize)
                )
           (equal (add (acl2::bvcat highsize x lowsize y) (mul k z p) p)
                  (mod (acl2::bvcat 1 z (+ highsize lowsize) (acl2::bvcat highsize x lowsize y)) p)))
  :hints (("Goal" :use (:instance add-of-bvcat-of-add-of-mul-combine (w 0))
           :in-theory (disable add-of-bvcat-of-add-of-mul-combine))))

;commuted
(defthm add-of-bvcat-of-add-of-mul-combine-simp-alt
  (implies (and (syntaxp (and (quotep k)
                              (quotep highsize)
                              (quotep lowsize)))
                (equal k (expt 2 (+ highsize lowsize)))
                (acl2::bitp z)
                (posp p)
                (posp highsize)
                (posp lowsize)
                )
           (equal (add (mul k z p) (acl2::bvcat highsize x lowsize y) p)
                  (mod (acl2::bvcat 1 z (+ highsize lowsize) (acl2::bvcat highsize x lowsize y)) p)))
  :hints (("Goal" :use (:instance add-of-bvcat-of-add-of-mul-combine-simp)
           :in-theory (disable add-of-bvcat-of-add-of-mul-combine-simp))))

(defthm mod-of-bvcat
  (implies (and (< (expt 2 (+ highsize lowsize)) p)
                (natp highsize)
                (natp lowsize)
                (posp p))
           (equal (mod (acl2::bvcat highsize highval lowsize lowval) p)
                  (acl2::bvcat highsize highval lowsize lowval))))

;; TODO: Consider normalizing small "negative" constants to negative numbers.
(defthmd add-of-constant-normalize-to-fep
  (implies (and (syntaxp (quotep k))
                (not (fep k p))
                (posp p))
           (equal (add k x p)
                  (add (mod (ifix k) p) x p))))

(defthm not-fep-when-negative-cheap
  (implies (< x 0)
           (not (fep x p)))
  :rule-classes ((:rewrite :backchain-limit-lst (0))))

(defthm mod-when-<-of-0
  (implies (and (< (- y) x)
                (< x 0)
                (integerp x)
                (posp y))
           (equal (mod x y)
                  (+ x y)))
  :hints (("Goal" :use (:instance ACL2::MOD-WHEN-<
                                  (x (+ X Y))
                                  (y y))
           :in-theory (disable ACL2::MOD-WHEN-<
                               PFIELD::MOD-WHEN-FEP))))

(defthmd bitp-of-add-of-constant-2
  (implies (and (unsigned-byte-p 32 x)
                (unsigned-byte-p 32 (- k))
                (< k 0)
;               (equal k -100)
;(fep (- k) p)
                (posp p)
                (< (expt 2 32) p)
                )
           (equal (bitp (add k x p))
                  (or (equal (- k) x)
                      (equal (+ 1 (- k)) x))))
  :hints (("Goal"
           :cases ((equal (mod k p) (+ k p)))
           :in-theory (enable bitp add-of-constant-normalize-to-fep ADD
                              acl2::mod-sum-cases))))

(defthm slice-of-+-of-1-when-even
  (implies (and (equal 0 (acl2::getbit 0 k))
                (integerp k))
           (equal (acl2::slice 31 1 (+ 1 k))
                  (acl2::slice 31 1 k)))
  :hints (("Goal" :in-theory (e/d (acl2::slice-of-sum-cases
                                   acl2::evenp-becomes-mod-fact
                                   acl2::bvchop)
                                  (acl2::slice-becomes-getbit
                                   acl2::bvchop-1-becomes-getbit)))))


;; (thm
;;  (implies (and (equal (acl2::slice 31 1 x)
;;                       (acl2::slice 31 1 k))
;;                (unsigned-byte-p 32 x)
;;                (unsigned-byte-p 32 k))
;;           (<= (- x y) 1))
;;  :hints (("Goal" :use ( (:instance ACL2::SPLIT-BV (y x) (n 32) (m 1))
;;                         (:instance ACL2::SPLIT-BV (y k) (n 32) (m 1))
;;                         )
;;           :in-theory (disable ACL2::BVCAT-OF-SLICE-AND-X-ADJACENT
;;                               ACL2::BVCAT-SLICE-SAME
;;                               ACL2::BVCAT-EQUAL-REWRITE-ALT
;;                               ACL2::BVCAT-EQUAL-REWRITE
;;                               )
;;           )))

(defthmd equal-of-slices-helper
  (implies (and (unsigned-byte-p 32 x)
                (unsigned-byte-p 32 k)
                (equal 0 (acl2::getbit 0 k)))
           (equal (or (equal k x)
                      (equal (+ 1 k) x))
                  (equal (acl2::slice 31 1 x)
                         (acl2::slice 31 1 k))))
  :hints (("Goal" :use ((:instance ACL2::SPLIT-BV (y x) (n 32) (m 1))
                        (:instance ACL2::SPLIT-BV (y k) (n 32) (m 1)))
           :cases ((equal 0 (acl2::getbit 0 x)))
           :in-theory (e/d (acl2::bvcat acl2::logapp)
                           ( ACL2::BVCAT-OF-SLICE-AND-X-ADJACENT
                             ACL2::BVCAT-SLICE-SAME
                             ACL2::BVCAT-EQUAL-REWRITE-ALT
                             ACL2::BVCAT-EQUAL-REWRITE)))))

(defthm bitp-of-add-of-even-constant
  (implies (and (unsigned-byte-p 32 x)
                (unsigned-byte-p 32 (- k)) ;(fep (- k) p)
                (< k 0)
                (equal 0 (acl2::getbit 0 k))
                (integerp k)
                (posp p)
                (< (expt 2 32) p))
           (equal (bitp (add k x p))
                  (equal (acl2::slice 31 1 (- k))
                         (acl2::slice 31 1 x))))
  :hints (("Goal"
           :use (:instance equal-of-slices-helper (k (- k)))
           :in-theory (enable bitp add-of-constant-normalize-to-fep ADD
                              bitp-of-add-of-constant-2
                              acl2::mod-sum-cases))))

;; (defthm bitp-of-add-of-odd-constant
;;   (implies (and (unsigned-byte-p 32 x)
;;                 (unsigned-byte-p 32 (- k)) ;(fep (- k) p)
;;                 (< k 0)
;;                 (equal 1 (acl2::getbit 0 k)) ;odd constant
;;                 (integerp k)
;;                 (posp p)
;;                 (< (expt 2 32) p))
;;            (equal (bitp (add k x p))
;;                   (equal (acl2::slice 31 1 (- k))
;;                          (acl2::slice 31 1 x))))
;;   :hints (("Goal"
;; ;           :use (:instance equal-of-slices-helper (k (- k)))
;;            :in-theory (enable bitp add-of-constant-normalize-to-fep ADD
;;                               bitp-of-add-of-constant-2
;;                               acl2::mod-sum-cases))))

;needed?
(defthmd if-of-nil-becomes-booland
  (implies (and (booleanp x)
                (booleanp y))
           (equal (if x y nil)
                  (acl2::booland x y))))

(defthm bvchop-of-1-when-bitp
  (implies (bitp x)
           (equal (acl2::bvchop 1 x)
                  x))
  :hints (("Goal" :in-theory (enable bitp))))

;; gen the above to handle odd constants

;for axe, or build in bitp, or add a constant opener rule
(defthmd bitp-of-1
  (bitp 1))

;for axe, or build in bitp, or add a constant opener rule
(defthmd bitp-of-0
  (bitp 0))

;move
(acl2::add-known-boolean bitp)

;improve the other
(defthm pfield::mul-of--1-becomes-neg-gen
  (implies (and ;(integerp pfield::x)
            (posp p))
           (equal (mul -1 x p)
                  (neg x p)))
  :hints
  (("Goal"
    :in-theory (enable mul neg pfield::sub))))

(defthm bitp-idiom
  (implies (and (rtl::primep p)
                (fep x p))
           (equal (equal 0 (mul (add 1 (neg x p) p)
                                        (neg x p)
                                        p))
                  (bitp x)))
  :hints (("Goal" :in-theory (e/d (bitp) (pfield::mul-of-add-arg1
                                          pfield::mul-of-add-arg2)))))


(defthm bitp-of-bitxor
  (bitp (acl2::bitxor x y)))

(local (in-theory (disable pfield::fep-holds
                           pfield::mod-when-fep)))

(defthm mod-of-+-of-mod-arg3
  (implies (and (integerp y)
                (integerp p)
                (< 0 p)
                (integerp z)
                (integerp x))
           (equal (mod (+ x y (mod z p)) p)
                  (mod (+ x y z) p)))
  :hints (("Goal" :in-theory (enable acl2::mod-sum-cases))))

(defthm add-of-mul-of-power-of-2-and-add
  (implies (and (syntaxp (quotep k))
                (acl2::power-of-2p k)
                (bitp x)
                (unsigned-byte-p (+ -1 (acl2::integer-length k)) y)
                (posp p)
                (integerp z)
                )
           (equal (add (mul k x p) (add y z p) p)
                  (add (acl2::bvcat 1 x (+ -1 (acl2::integer-length k)) y)
                       z
                       p)))
  :hints (("Goal" :in-theory (enable bitp acl2::bvcat acl2::logapp add
                                     ACL2::POWER-OF-2P))))

(defthm add-of-mul-of-power-of-2
  (implies (and (syntaxp (quotep k))
                (acl2::power-of-2p k)
                (bitp x)
                (unsigned-byte-p (+ -1 (acl2::integer-length k)) y)
                (posp p))
           (equal (add (mul k x p) y p)
                  (mod (acl2::bvcat 1 x (+ -1 (acl2::integer-length k)) y)
                       p)))
  :hints (("Goal" :in-theory (enable bitp acl2::bvcat acl2::logapp add
                                     ACL2::POWER-OF-2P))))

(defthm bvcat-intro--4--2-simple
  (implies (and (acl2::bitp x)
                (acl2::bitp y)
                (POSP P)
                (<= 8 p) ;gen?
                )
           (equal (ADD
                   (MUL -4 x p)
                   (MUL -2 y p)
                   p)
                  (mod (neg (acl2::bvcat 1 x 2 (acl2::bvcat 1 y 1 0)) p) p)))
  :hints (("Goal" :in-theory (enable acl2::bitp))))

(defthm bvcat-intro--4--2
  (implies (and (acl2::bitp x)
                (acl2::bitp y)
                (POSP P)
                (<= 8 p) ;gen?
                )
           (equal (ADD (MUL -4 x p) (add (MUL -2 y p) z p) p)
                  (add (neg (acl2::bvcat 1 x 2 (acl2::bvcat 1 y 1 0)) p) z p)))
  :hints (("Goal" :in-theory (enable acl2::bitp))))

(defthm bvcat-intro--2--4
  (implies (and (acl2::bitp x)
                (acl2::bitp y)
                (POSP P)
                (<= 8 p) ;gen?
                )
           (equal (ADD (MUL -2 x p) (add (MUL -4 y p) z p) p)
                  (add (neg (acl2::bvcat 1 y 2 (acl2::bvcat 1 x 1 0)) p) z p)))
  :hints (("Goal" :in-theory (enable acl2::bitp))))

;; (thm
;;  (implies (integerp x)
;;           (equal (INTEGER-LENGTH (- x))
;;                  (INTEGER-LENGTH x)))
;;  :hints (("Goal" :in-theory (enable INTEGER-LENGTH))))

(defthm mod-of-+-of-mod-same-arg2+
  (implies (and (rationalp z)
                (rationalp k)
                (rationalp y)
                (< 0 p)
                (rationalp p))
           (equal (mod (+ z (mod k p) y) p)
                  (mod (+ z k y) p)))
  :hints (("Goal" :in-theory (enable acl2::mod-sum-cases))))

(defthm mod-of-+-of---of-mod-same-arg3
  (implies (and (rationalp z)
                (rationalp k)
                (rationalp y)
                (< 0 p)
                (rationalp p))
           (equal (mod (+ z y (- (mod k p))) p)
                  (mod (+ z y (- k)) p)))
  :hints (("Goal" :in-theory (enable acl2::mod-sum-cases))))

(defthm add-of-mul-of-negated-power-of-2-and-add
  (implies (and (syntaxp (quotep k))
                (acl2::power-of-2p (- k))
                (bitp x)
                (unsigned-byte-p (+ -1 (acl2::integer-length (- k))) y)
                (posp p)
                (integerp z))
           (equal (add (mul k x p) (add (neg y p) z p) p)
                  (add (neg (acl2::bvcat 1 x (+ -1 (acl2::integer-length (- k))) y) p)
                               z
                               p)))
  :hints (("Goal"
           :use (:instance ACL2::MOD-OF-MINUS-ARG1 (x (+ K P (- Y))) (y p))
           :in-theory (e/d (bitp acl2::bvcat acl2::logapp add NEG
                                 ACL2::POWER-OF-2P
                                 ) (ACL2::MOD-OF-MINUS-ARG1)))))

;slow
(defthm add-of-mul-of-negated-power-of-2-and-add-alt
  (implies (and (syntaxp (quotep k))
                (acl2::power-of-2p (- k))
                (bitp x)
                (unsigned-byte-p (+ -1 (acl2::integer-length (- k))) y)
                (posp p)
                (integerp z))
           (equal (add (neg y p) (add (mul k x p) z p) p)
                  (add (neg (acl2::bvcat 1 x (+ -1 (acl2::integer-length (- k))) y) p)
                               z
                               p)))
  :hints (("Goal" :use (:instance add-of-mul-of-negated-power-of-2-and-add)
           :in-theory (disable add-of-mul-of-negated-power-of-2-and-add))))

(defthm add-of-mul-of-negated-power-of-2
  (implies (and (syntaxp (quotep k))
                (acl2::power-of-2p (- k))
                (bitp x)
                (unsigned-byte-p (+ -1 (acl2::integer-length (- k))) y)
                (posp p))
           (equal (add (mul k x p) (neg y p) p)
                  (neg (acl2::bvcat 1 x (+ -1 (acl2::integer-length (- k))) y) p)))
  :hints (("Goal" :in-theory (enable bitp acl2::bvcat acl2::logapp add NEG
                                     ACL2::POWER-OF-2P))))

(defthm add-of-mul-of-negated-power-of-2-alt
  (implies (and (syntaxp (quotep k))
                (acl2::power-of-2p (- k))
                (bitp x)
                (unsigned-byte-p (+ -1 (acl2::integer-length (- k))) y)
                (posp p))
           (equal (add (neg y p) (mul k x p) p)
                  (neg (acl2::bvcat 1 x (+ -1 (acl2::integer-length (- k))) y) p)))
  :hints (("Goal" :use (:instance add-of-mul-of-negated-power-of-2)
           :in-theory (disable add-of-mul-of-negated-power-of-2))))

(defthm equal-of-add-and-mod-same-arg1
  (implies (and (fep y p)
                (integerp x)
                (posp p))
           (equal (EQUAL (ADD x Y P) (MOD x P))
                  (equal 0 y)))
  :hints (("Goal" :in-theory (enable add FEP acl2::mod-sum-cases))))

(defthm equal-of-xor-idiom
  (implies (and (bitp x)
                (bitp z)
                (fep y p)
                (rtl::primep p))
           (equal (equal (mul 2 (mul x z p) p) (add z (add (neg y p) x p) p))
                  (equal y (acl2::bitxor x z)))))

(defthm equal-of-xor-idiom-alt
  (implies (and (bitp x)
                (bitp z)
                (fep y p)
                (rtl::primep p))
           (equal (equal (mul 2 (mul z x p) p)
                         (add z (add (neg y p) x p) p))
                  (equal y (acl2::bitxor x z)))))

(defthm equal-of-xor-idiom-b
  (implies (and (bitp x)
                (bitp z)
                (fep y p)
                (rtl::primep p))
           (equal (equal (mul 2 (mul x z p) p) (add (neg y p) (add z x p) p))
                  (equal y (acl2::bitxor x z)))))

(defthm equal-of-xor-idiom-b-alt
  (implies (and (bitp x)
                (bitp z)
                (fep y p)
                (rtl::primep p))
           (equal (equal (mul 2 (mul z x p) p) (add (neg y p) (add z x p) p))
                  (equal y (acl2::bitxor x z)))))

;; base case for making a bvcat nest (with extra addend z)
(defthm add-of-add-of-mul-of-2-becomes-add-of-bvcat
  (implies (and (acl2::bitp x)
                (acl2::bitp y)
                (posp p))
           (equal (add x (add (mul 2 y p) z p) p)
                  (add (acl2::bvcat 1 y 1 x) z p))))

;; base case for making a bvcat nest (without extra addend)
(defthm add-of-mul-of-2-becomes-bvcat
  (implies (and (acl2::bitp x)
                (acl2::bitp y)
                (posp p))
           (equal (add x (mul 2 y p) p)
                  (mod (acl2::bvcat 1 y 1 x) p))))

;; not sure about this..
(defthmd acl2::unsigned-byte-p-becomes-bitp
  (equal (unsigned-byte-p 1 acl2::x)
         (bitp acl2::x)))

;; more standard hyps
(defthm pfield::equal-of-0-and-add-of-neg-2
  (implies (and (fep x p)
                (fep y p)
                (posp p))
           (equal (equal 0 (add (neg x p) y p))
                  (equal x y))))

(defthm mul-when-constants
  (implies (and (syntaxp (and (quotep x)
                              (quotep y)))
                (integerp x)
                (integerp y)
                (posp p))
           (equal (mul x y p)
                  (mod (* x y) p)))
  :hints (("Goal" :in-theory (enable mul))))

(defthm mod-of-+-cancel-arg2+-arg1+
  (implies (and (integerp k)
                (integerp z)
                (integerp y)
                (integerp w)
                (posp p))
           (equal (equal (mod (+ k z y) p)
                         (mod (+ z w) p))
                  (equal (mod (+ k y) p)
                         (mod w p))))
  :hints (("Goal" :in-theory (enable acl2::mod-sum-cases))))

(defthm +-of-*-same-constant
 (implies (syntaxp (quotep k))
          (equal (+ x (* K x))
                 (* (+ 1 k) x))))

(defthmd triple
  (equal (* 3 x)
         (+ x x x)))

(defthmd double
  (equal (* 2 x)
         (+ x x)))

(defthmd double-neg
  (equal (* -2 x)
         (+ (- x) (- x))))

(defthm add-of-mul-of-add-of-mul-when-double
  (implies (and (syntaxp (and (quotep k)
                              (quotep k2)))
                ;;(acl2::power-of-2p k)
                (equal k2 (* 2 k))
                (integerp k)
                (bitp x)
                (bitp y)
                (posp p))
           (equal (ADD (MUL k x p) (ADD (MUL k2 y p) z p) p)
                  (ADD (MUL k (acl2::bvcat 1 y 1 x) p) z p)))
  :hints (("Goal" :in-theory (enable bitp MUL ADD triple double))))

(defthm expt-of-CEILING-OF-LG-when-power-of-2p
  (implies (acl2::power-of-2p x)
           (equal (EXPT 2 (ACL2::CEILING-OF-LG x))
                  x))
  :hints (("Goal" :in-theory (enable acl2::power-of-2p
                                     ACL2::CEILING-OF-LG))))

(local (include-book "kestrel/arithmetic-light/expt2" :dir :system))

(defthm floor-of-expt-2
  (implies (integerp n)
           (equal (floor (expt 2 n) 2)
                  (if (posp n)
                      (expt 2 (+ -1 n))
                    0)))
  :hints (("Goal" :in-theory (e/d (expt) (ACL2::EXPT-HACK)))))

(defun sub1-induct (n)
  (if (zp n)
      n
    (sub1-induct (+ -1 n))))

(defthm acl2::integer-length-of-*-of-expt2
  (implies (and (natp n)
                (integerp x))
           (equal (integer-length (* x (expt 2 n)))
                  (if (equal 0 x)
                      0
                    (+ n (integer-length x)))))
  :hints (("Goal" ;:expand (INTEGER-LENGTH (* X (EXPT 2 (+ -1 N))))
           :induct (sub1-induct n)
           :in-theory (e/d (integer-length expt)
                           (acl2::expt-hack
                            ;ACL2::INTEGER-LENGTH-OF-FLOOR-BY-2
                            ;;ACL2::EXPT-COLLECT-HACK
                            )))))

(local (include-book "kestrel/arithmetic-light/divides" :dir :system))

(defthm power-of-2p-when-equal-of-expt
  (implies (and (equal x (expt 2 n))
                (natp n))
           (acl2::power-of-2p x))
  :hints (("Goal" :in-theory (enable acl2::power-of-2p))))

;; (thm
;;  (implies (posp x)
;;           (equal (integer-length (* 1/2 x))
;;                  (+ -1 (integer-length x))))
;;  :hints (("Goal" :in-theory (enable integer-length))))

;; (thm
;;  (implies (posp x)
;;           (equal (ACL2::LG (* 1/2 x))
;;                  (+ -1 (ACL2::LG x))))
;;  :hints (("Goal" :in-theory (enable ACL2::LG))))


;; (thm
;;  (implies ..
;;           (< (ACL2::CEILING-OF-LG K2)
;;              (ACL2::CEILING-OF-LG K1))

(defthm lg-of-*-of-1/2-and-expt
  (implies (natp n)
           (equal (ACL2::LG (* 1/2 (EXPT 2 n)))
                  (+ -1 n)))
  :hints (("Goal" :use (:instance ACL2::LG-OF-EXPT
                                  (n (+ -1 n)))
           :in-theory (e/d (ACL2::EXPT-OF-+) (;ACL2::LG-OF-EXPT-GEN
                                              ACL2::LG-OF-EXPT)))))

(defthm power-of-2p-of-*-of-/
  (implies (and (< k1 k2)
                (acl2::power-of-2p k1)
                (acl2::power-of-2p k2))
           (acl2::power-of-2p (* (/ k1) k2)))
  :hints (("Goal" :use (:instance power-of-2p-when-equal-of-expt
                                  (x (* (/ k1) k2))
                                  (n (- (acl2::lg k2)
                                        (acl2::lg k1))))
           :expand ((ACL2::POWER-OF-2P K1)
                    (ACL2::POWER-OF-2P K2))
           :in-theory (e/d (ACL2::EXPT-OF-+)
                           (power-of-2p-when-equal-of-expt)))))

(defthm integerp-of-*-of-/-when-POWER-OF-2P-and-POWER-OF-2P
  (implies (and (< K1 K2)
                (ACL2::POWER-OF-2P K1)
                (ACL2::POWER-OF-2P K2))
           (INTEGERP (* (/ K1) K2)))
  :hints (("Goal" :in-theory (enable ACL2::POWER-OF-2P))))

(local (include-book "kestrel/arithmetic-light/times-and-divides" :dir :system))

(defthm add-of-mul-and-mul-combine
  (implies (and (syntaxp (and (quotep k1)
                              (quotep k2)))
                (acl2::axe-bind-free (acl2::bind-bv-size-axe bv2 'bv2size dag-array) '(bv2size))
                (< k1 k2)
                (acl2::power-of-2p k1)
                (acl2::power-of-2p k2)
                (unsigned-byte-p (acl2::lg (/ k2 k1)) bv1)
                (unsigned-byte-p bv2size bv2)
                (integerp k1)
                (integerp k2)
                (natp bv2size)
                (posp p))
           (equal (add (mul k1 bv1 p) (mul k2 bv2 p) p)
                  ;; todo: associate the bvcat nest (or gen the bvcat in the lhs)
                  (mul k1 (acl2::bvcat bv2size
                                               bv2
                                               (acl2::lg (/ k2 k1))
                                               bv1)
                               p)))
  :hints (("Goal" :in-theory (e/d (ACL2::BVCAT acl2::logapp ADD mul acl2::power-of-2p)
                                  (ACL2::UNSIGNED-BYTE-P-OF-+-WHEN-<-OF-LOGTAIL-AND-EXPT
                                   PFIELD::MOD-WHEN-FEP
                                   ACL2::<-OF-*-SAME-LINEAR-SPECIAL
                                   PFIELD::MOD-WHEN-FEP)))))

(defthm add-of-mul-and-mul-combine-extra
  (implies (and (syntaxp (and (quotep k1)
                              (quotep k2)))
                (acl2::axe-bind-free (acl2::bind-bv-size-axe bv2 'bv2size dag-array) '(bv2size))
                (< k1 k2)
                (acl2::power-of-2p k1)
                (acl2::power-of-2p k2)
                (unsigned-byte-p (acl2::lg (/ k2 k1)) bv1)
                (unsigned-byte-p bv2size bv2)
                (integerp k1)
                (integerp k2)
                (integerp z)
                (natp bv2size)
                (posp p))
           (equal (add (mul k1 bv1 p) (add (mul k2 bv2 p) z p) p)
                  ;; todo: associate the bvcat nest (or gen the bvcat in the lhs)
                  (add (mul k1 (acl2::bvcat bv2size
                                                             bv2
                                                             (acl2::lg (/ k2 k1))
                                                             bv1)
                                             p)
                               z p)))
  :hints (("Goal" :use (:instance add-of-mul-and-mul-combine)
           :in-theory (disable add-of-mul-and-mul-combine))))

;todo: use lg instead of ceiling-of-lg more in this file?

(defthm add-of-mul-of-2-when-bitp
  (implies (and (acl2::axe-bind-free (acl2::bind-bv-size-axe bv 'bvsize dag-array) '(bvsize))
                (unsigned-byte-p bvsize bv)
                (bitp x)
                (posp p))
           (equal (add x (mul 2 bv p) p)
                  (mod (acl2::bvcat bvsize bv 1 x) p)))
  :hints (("Goal" :in-theory (enable bitp acl2::bvcat acl2::logapp add mul))))

(defthm add-of-mul-of-2-when-bitp-extra
  (implies (and (acl2::axe-bind-free (acl2::bind-bv-size-axe bv 'bvsize dag-array) '(bvsize))
                (unsigned-byte-p bvsize bv)
                (bitp x)
                (posp p))
           (equal (add x (add (mul 2 bv p) z p) p)
                  (add (acl2::bvcat bvsize bv 1 x) z p)))
  :hints (("Goal" :use (:instance add-of-mul-of-2-when-bitp)
           :in-theory (disable add-of-mul-of-2-when-bitp))))

;; (defthm add-of-mul-of--2-when-bitp
;;   (implies (and (acl2::axe-bind-free (acl2::bind-bv-size-axe bv 'bvsize dag-array) '(bvsize))
;;                 (unsigned-byte-p bvsize bv)
;;                 (bitp x)
;;                 (posp p))
;;            (equal (add x (mul -2 bv p) p)
;;                   (mod (acl2::bvcat bvsize bv 1 x) p)))
;;   :hints (("Goal" :in-theory (enable bitp acl2::bvcat acl2::logapp add mul))))

;; (defthm add-of-mul-of--2-when-bitp-extra
;;   (implies (and (acl2::axe-bind-free (acl2::bind-bv-size-axe bv 'bvsize dag-array) '(bvsize))
;;                 (unsigned-byte-p bvsize bv)
;;                 (bitp x)
;;                 (posp p))
;;            (equal (add x (add (mul -2 bv p) z p) p)
;;                   (add (acl2::bvcat bvsize bv 1 x) z p)))
;;   :hints (("Goal" :use (:instance add-of-mul-of-2-when-bitp)
;;            :in-theory (disable add-of-mul-of-2-when-bitp))))

(defthm mul-of---arg2
  (implies (syntaxp (not (quotep y))) ;defeat ACL2's overly aggressive matching
           (equal (mul x (- y) p)
                  (neg (mul x y p) p)))
  :hints (("Goal" :in-theory (enable mul add))))

(defthm mul-of---arg1
  (implies (syntaxp (not (quotep y))) ;defeat acl2's overly aggressive matching
           (equal (mul (- y) x p)
                  (neg (mul y x p) p)))
  :hints (("Goal" :in-theory (enable MUL add))))

(local (include-book "kestrel/arithmetic-light/times-and-divides" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus-and-minus" :dir :system))

;move
(defthm /-of--
  (equal (/ (- x))
         (- (/ x)))
  :hints (("Goal" :in-theory (e/d (acl2::--becomes-*-of--1) (ACL2::*-OF--1)))))

(local
 (defthm power-of-2p-helper
   (implies (and (acl2::power-of-2p (- k1))
                 (acl2::power-of-2p (- k2))
                 (< k2 k1))
            (acl2::power-of-2p (* (/ k1) k2)))
   :hints (("Goal" :use (:instance power-of-2p-of-*-of-/
                                   (k1 (- k1))
                                   (k2 (- k2)))
            :in-theory (disable power-of-2p-of-*-of-/)))))

(defthm add-of-mul-and-mul-combine-negated
  (implies (and (syntaxp (and (quotep k1)
                              (quotep k2)))
                (acl2::axe-bind-free (acl2::bind-bv-size-axe bv2 'bv2size dag-array) '(bv2size))
                (< k1 0)
                (< k2 0)
                (< (- k1) (- k2))
                (acl2::power-of-2p (- k1))
                (acl2::power-of-2p (- k2))
                (unsigned-byte-p (acl2::lg (/ k2 k1)) bv1)
                (unsigned-byte-p bv2size bv2)
                (integerp k1)
                (integerp k2)
                (natp bv2size)
                (posp p))
           (equal (add (mul k1 bv1 p) (mul k2 bv2 p) p)
                  ;; todo: associate the bvcat nest (or gen the bvcat in the lhs)
                  (mul k1 (acl2::bvcat bv2size
                                               bv2
                                               (acl2::lg (/ k2 k1))
                                               bv1)
                               p)))
  :hints (("Goal" :use (:instance ACL2::EXPT-OF-LG
                                  (ACL2::X (* (/ K1) K2)))
           :in-theory (e/d (ACL2::BVCAT acl2::logapp ADD mul)
                           (ACL2::UNSIGNED-BYTE-P-OF-+-WHEN-<-OF-LOGTAIL-AND-EXPT
                            PFIELD::MOD-WHEN-FEP
                            ACL2::<-OF-*-SAME-LINEAR-SPECIAL
                            PFIELD::MOD-WHEN-FEP
                            ACL2::EXPT-OF-LG)))))

(defthm add-of-mul-and-mul-combine-negated-special-case-for-bitp
  (implies (and (syntaxp (and (quotep k1)
                              (quotep k2)))
                (< k1 0)
                (< k2 0)
                (< (- k1) (- k2))
                (acl2::power-of-2p (- k1))
                (acl2::power-of-2p (- k2))
                (unsigned-byte-p (acl2::lg (/ k2 k1)) bv1)
                (unsigned-byte-p 1 bv2)
                (integerp k1)
                (integerp k2)
                (posp p))
           (equal (add (mul k1 bv1 p) (mul k2 bv2 p) p)
                  ;; todo: associate the bvcat nest (or gen the bvcat in the lhs)
                  (mul k1 (acl2::bvcat 1
                                               bv2
                                               (acl2::lg (/ k2 k1))
                                               bv1)
                               p)))
  :hints (("Goal" :use (:instance add-of-mul-and-mul-combine-negated (bv2size 1))
           :in-theory (disable add-of-mul-and-mul-combine-negated))))

(defthm add-of-mul-and-mul-combine-negated-extra
  (implies (and (syntaxp (and (quotep k1)
                              (quotep k2)))
                (acl2::axe-bind-free (acl2::bind-bv-size-axe bv2 'bv2size dag-array) '(bv2size))
                (< k1 0)
                (< k2 0)
                (< (- k1) (- k2))
                (acl2::power-of-2p (- k1))
                (acl2::power-of-2p (- k2))
                (unsigned-byte-p (acl2::lg (/ k2 k1)) bv1)
                (unsigned-byte-p bv2size bv2)
                (integerp k1)
                (integerp k2)
                (natp bv2size)
                (posp p))
           (equal (add (mul k1 bv1 p) (add (mul k2 bv2 p) z p) p)
                  ;; todo: associate the bvcat nest (or gen the bvcat in the lhs)
                  (add (mul k1 (acl2::bvcat bv2size
                                                            bv2
                                                            (acl2::lg (/ k2 k1))
                                                            bv1)
                                            p)
                               z
                               p)))
  :hints (("Goal" :use add-of-mul-and-mul-combine-negated
           :in-theory (disable add-of-mul-and-mul-combine-negated))))

(defthm add-of-neg-of-mul-of--2
  (implies (and (bitp bit)
                (acl2::axe-bind-free (acl2::bind-bv-size-axe bv 'bv-size dag-array) '(bv-size))
                (unsigned-byte-p bv-size bv))
           (equal (add (neg bit p) (mul -2 bv p) p)
                  (neg (acl2::bvcat bv-size bv 1 bit) p)))
  :hints (("Goal" :in-theory (e/d (add neg acl2::bvcat acl2::logapp mul acl2::mod-sum-cases
                                       double
                                       double-neg)
                                  (ACL2::BITP-BECOMES-UNSIGNED-BYTE-P)))))

(defthm add-of-neg-of-mul-of--2-extra
  (implies (and (bitp bit)
                (acl2::axe-bind-free (acl2::bind-bv-size-axe bv 'bv-size dag-array) '(bv-size))
                (unsigned-byte-p bv-size bv))
           (equal (add (neg bit p) (add (mul -2 bv p) z p) p)
                  (add (neg (acl2::bvcat bv-size bv 1 bit) p) z p)))
  :hints (("Goal" :use (:instance add-of-neg-of-mul-of--2)
           :in-theory (disable add-of-neg-of-mul-of--2))))

(defthm equal-of-0-and-add-of-add-of-neg-and-neg
  (implies (and (fep out p)
                (fep in0 p)
                (fep in1 p)
                (posp p))
           (equal (EQUAL 0 (ADD out (ADD (NEG in0 p) (NEG in1 p) p) p))
                  (EQUAL out (ADD in0 in1 p)))))
