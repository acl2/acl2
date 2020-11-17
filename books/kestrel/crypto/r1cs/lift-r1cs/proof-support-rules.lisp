(in-package "PFIELD")

;; TODO: Are some of these specific to idioms of certain compilers?

(include-book "kestrel/prime-fields/prime-fields-rules" :dir :system)
(include-book "kestrel/booleans/booland" :dir :system)
(include-book "kestrel/booleans/boolor" :dir :system)
(local (include-book "kestrel/prime-fields/equal-of-add-move-negs-bind-free" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))

;; (defthm solve-1
;;   (implies (and (pfield::fep z p)
;;                 (integerp x)
;;                 (integerp y)
;;                 (posp p))
;;            (equal (equal (pfield::mul (pfield::neg x p) y p)
;;                          (pfield::neg z p))
;;                   ;; keep the z on the RHS:
;;                   (equal (pfield::mul x y p) z)))
;;   :hints (("Goal" :in-theory (enable PFIELD::NEG pfield::mul PFIELD::SUB))))

;move
(defthm mul-when-not-integerp-arg1-cheap
  (implies (not (integerp x))
           (equal (mul x y p)
                  0))
  :rule-classes ((:rewrite :backchain-limit-lst (1)))
  :hints (("Goal" :in-theory (enable mul))))

;; x = -y becomes -x = y
;;quite strong
;; This solves for y.
(defthmd equal-of-neg-arg2
  (implies (posp p)
           (equal (equal x (pfield::neg y p))
                  ;; keep y on the RHS:
                  (and (equal (pfield::neg x p) (mod (ifix y) p))
                       (pfield::fep x p)))))

;; x = y - z becomes -x + y = z
;; This solves for z but departs from our usual normal form.
(defthmd equal-of-add-of-neg-arg2
  (implies (posp p)
           (equal (equal x (pfield::add y (pfield::neg z p) p))
                  ;; keep z on the RHS:
                  (and (equal (pfield::add (pfield::neg x p) y p)
                              (mod (ifix z) p))
                       (pfield::fep x p)))))

;; x = y + w - z becomes -x + y + w = z
;; This solves for z but departs from our usual normal form.
(defthmd equal-of-add-of-add-of-neg-arg2-arg2
  (implies (posp p)
           (equal (equal x (pfield::add y (pfield::add w (pfield::neg z p) p) p))
                  ;; keep z on the RHS
                  (and (equal (pfield::add (pfield::neg x p) (pfield::add y w p) p)
                              (mod (ifix z) p))
                       (pfield::fep x p)
                       ))))

;move
;; We could push the NEG into either argument of the MUL, and here it is clear
;; that the first argument is the right choice.
(defthm neg-of-mul-of-neg-arg1
  (implies (posp p)
           (equal (pfield::neg (pfield::mul (pfield::neg x p) y p) p)
                  (pfield::mul x y p)))
  :hints (("Goal" :in-theory (enable pfield::neg pfield::mul pfield::sub))))

(defthm neg-of-mul-of-neg-arg2
  (implies (posp p)
           (equal (pfield::neg (pfield::mul y (pfield::neg x p) p) p)
                  (pfield::mul x y p)))
  :hints (("Goal" :in-theory (enable pfield::neg pfield::mul pfield::sub))))

;; We usually don't want this, because it is not clear which argument of the mul should get the neg.
(defthmd neg-of-mul-arg1
  (equal (pfield::neg (pfield::mul x y p) p)
         (pfield::mul (pfield::neg x p) y p))
  :hints (("Goal" :in-theory (enable pfield::neg pfield::mul))))

;; We usually don't want this, because it is not clear which argument of the mul should get the neg.
(defthmd neg-of-mul-arg2
  (equal (pfield::neg (pfield::mul x y p) p)
         (pfield::mul x (pfield::neg y p) p))
  :hints (("Goal" :in-theory (enable pfield::neg pfield::mul))))

(theory-invariant (incompatible (:rewrite neg-of-mul-arg1) (:rewrite pfield::mul-of-neg-arg1)))
(theory-invariant (incompatible (:rewrite neg-of-mul-arg1) (:rewrite pfield::mul-of-neg-arg2)))
(theory-invariant (incompatible (:rewrite neg-of-mul-arg2) (:rewrite pfield::mul-of-neg-arg1)))
(theory-invariant (incompatible (:rewrite neg-of-mul-arg2) (:rewrite pfield::mul-of-neg-arg2)))

;move
;; We could push the NEG into either argument of the MUL, and here it seems
;; that the first argument is the right choice.
(defthm neg-of-mul-of-add-of-neg-arg1-arg2
  (implies (posp p)
           (equal (pfield::neg (pfield::mul (pfield::add k (pfield::neg x p) p) y p) p)
                  (pfield::mul (pfield::add (pfield::neg k p) x p) y p)))
  :hints (("Goal" :in-theory (e/d (neg-of-mul-arg1)
                                  (pfield::mul-commutative
                                   pfield::mul-of-neg-arg1
                                   pfield::mul-of-neg-arg2)))))


(defthm neg-of-mul-of-add-of-add-of-neg-arg1-arg2-arg2
  (implies (and (integerp x)
                (integerp y)
                (integerp k) ;may often be a constant
                (integerp w)
                (posp p))
           (equal (pfield::neg (pfield::mul (pfield::add k (pfield::add w (pfield::neg x p) p) p) y p) p)
                  (pfield::mul (pfield::add (pfield::neg k p) (pfield::add (pfield::neg w p) x p) p) y p)))
  :hints (("Goal" :in-theory (e/d (neg-of-mul-arg1)
                                  (pfield::mul-commutative
                                   pfield::mul-of-neg-arg1
                                   pfield::mul-of-neg-arg2)))))

(defthm neg-of-mul-of-add-of-neg-arg2-arg2
  (implies (and (integerp x)
                (integerp y)
                (integerp k) ;may often be a constant
                (posp p))
           (equal (pfield::neg (pfield::mul y (pfield::add k (pfield::neg x p) p) p) p)
                  (pfield::mul y (pfield::add (pfield::neg k p) x p) p)))
  :hints (("Goal" :in-theory (e/d (neg-of-mul-arg2)
                                  (pfield::mul-commutative
                                   pfield::mul-of-neg-arg1
                                   pfield::mul-of-neg-arg2)))))

(defthmd acl2::acl2-numberp-when-integerp
  (implies (integerp x)
           (acl2-numberp x)))

;; ;not used
;; (defthm fix-of-mod
;;   (equal (fix (mod x y))
;;          (mod x y)))

(defthm mul-of-ifix-arg1
  (equal (mul (ifix x) y p)
         (mul x y p))
  :hints (("Goal" :in-theory (enable mul))))

(defthm mul-of-ifix-arg2
  (equal (mul x (ifix y) p)
         (mul x y p))
  :hints (("Goal" :in-theory (enable mul))))

(defthm add-of-ifix-arg1
  (equal (add (ifix x) y p)
         (add x y p))
  :hints (("Goal" :in-theory (enable add))))

(defthm add-of-ifix-arg2
  (equal (add x (ifix y) p)
         (add x y p))
  :hints (("Goal" :in-theory (enable add))))

;dup?
(defthm acl2::integerp-of-ifix
  (integerp (ifix p)))

(defthm fep-of-ifix
  (implies (fep x p)
           (fep (ifix x) p))
  :hints (("Goal" :in-theory (enable fep))))

;; todo: introduce a fep-fix?
(defthm ifix-when-fep
  (implies (fep x p)
           (equal (ifix x)
                  x))
  :hints (("Goal" :in-theory (enable fep))))

;dup
(defthmd acl2::if-of-nil-becomes-booland
  (implies (and (booleanp x)
                (booleanp y))
           (equal (if x y nil)
                  (acl2::booland x y))))

(defthmd acl2::if-of-t-arg3
  (implies (and (booleanp x)
                (booleanp y))
           (equal (if x y t)
                  (acl2::boolor (not x) y))))
