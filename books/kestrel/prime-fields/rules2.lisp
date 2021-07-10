(in-package "PFIELD")

;; TODO: Are some of these specific to idioms of certain R1CS compilers?

(include-book "prime-fields-rules")
(include-book "kestrel/booleans/booland" :dir :system)
(include-book "kestrel/booleans/boolor" :dir :system)
(local (include-book "kestrel/prime-fields/equal-of-add-move-negs-bind-free" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))

;; (defthm solve-1
;;   (implies (and (fep z p)
;;                 (integerp x)
;;                 (integerp y)
;;                 (posp p))
;;            (equal (equal (mul (neg x p) y p)
;;                          (neg z p))
;;                   ;; keep the z on the RHS:
;;                   (equal (mul x y p) z)))
;;   :hints (("Goal" :in-theory (enable NEG mul SUB))))

;; x = -y becomes -x = y
;;quite strong
;; This solves for y.
(defthmd equal-of-neg-arg2
  (implies (posp p)
           (equal (equal x (neg y p))
                  ;; keep y on the RHS:
                  (and (equal (neg x p) (mod (ifix y) p))
                       (fep x p))))
  :hints (("Goal" :use (:instance equal-of-neg
                                  (x y)
                                  (y x)))))

;; x = y - z becomes -x + y = z
;; This solves for z but departs from our usual normal form.
(defthmd equal-of-add-of-neg-arg2
  (implies (posp p)
           (equal (equal x (add y (neg z p) p))
                  ;; keep z on the RHS:
                  (and (equal (add (neg x p) y p)
                              (mod (ifix z) p))
                       (fep x p)))))

;; x = y + w - z becomes -x + y + w = z
;; This solves for z but departs from our usual normal form.
(defthmd equal-of-add-of-add-of-neg-arg2-arg2
  (implies (posp p)
           (equal (equal x (add y (add w (neg z p) p) p))
                  ;; keep z on the RHS
                  (and (equal (add (neg x p) (add y w p) p)
                              (mod (ifix z) p))
                       (fep x p)
                       ))))

;move
;; We could push the NEG into either argument of the MUL, and here it is clear
;; that the first argument is the right choice.
(defthm neg-of-mul-of-neg-arg1
  (implies (posp p)
           (equal (neg (mul (neg x p) y p) p)
                  (mul x y p)))
  :hints (("Goal" :in-theory (enable neg mul sub))))

(defthm neg-of-mul-of-neg-arg2
  (implies (posp p)
           (equal (neg (mul y (neg x p) p) p)
                  (mul x y p)))
  :hints (("Goal" :in-theory (enable neg mul sub))))

;; We usually don't want this, because it is not clear which argument of the mul should get the neg.
(defthmd neg-of-mul-arg1
  (equal (neg (mul x y p) p)
         (mul (neg x p) y p))
  :hints (("Goal" :in-theory (enable neg mul))))

;; We usually don't want this, because it is not clear which argument of the mul should get the neg.
(defthmd neg-of-mul-arg2
  (equal (neg (mul x y p) p)
         (mul x (neg y p) p))
  :hints (("Goal" :in-theory (enable neg mul))))

(theory-invariant (incompatible (:rewrite neg-of-mul-arg1) (:rewrite mul-of-neg-arg1)))
(theory-invariant (incompatible (:rewrite neg-of-mul-arg1) (:rewrite mul-of-neg-arg2)))
(theory-invariant (incompatible (:rewrite neg-of-mul-arg2) (:rewrite mul-of-neg-arg1)))
(theory-invariant (incompatible (:rewrite neg-of-mul-arg2) (:rewrite mul-of-neg-arg2)))

;move
;; We could push the NEG into either argument of the MUL, and here it seems
;; that the first argument is the right choice.
(defthm neg-of-mul-of-add-of-neg-arg1-arg2
  (implies (posp p)
           (equal (neg (mul (add k (neg x p) p) y p) p)
                  (mul (add (neg k p) x p) y p)))
  :hints (("Goal" :in-theory (e/d (neg-of-mul-arg1)
                                  (mul-commutative
                                   mul-of-neg-arg1
                                   mul-of-neg-arg2)))))


(defthm neg-of-mul-of-add-of-add-of-neg-arg1-arg2-arg2
  (implies (and (integerp x)
                (integerp y)
                (integerp k) ;may often be a constant
                (integerp w)
                (posp p))
           (equal (neg (mul (add k (add w (neg x p) p) p) y p) p)
                  (mul (add (neg k p) (add (neg w p) x p) p) y p)))
  :hints (("Goal" :in-theory (e/d (neg-of-mul-arg1)
                                  (mul-commutative
                                   mul-of-neg-arg1
                                   mul-of-neg-arg2)))))

(defthm neg-of-mul-of-add-of-neg-arg2-arg2
  (implies (and (integerp x)
                (integerp y)
                (integerp k) ;may often be a constant
                (posp p))
           (equal (neg (mul y (add k (neg x p) p) p) p)
                  (mul y (add (neg k p) x p) p)))
  :hints (("Goal" :in-theory (e/d (neg-of-mul-arg2)
                                  (mul-commutative
                                   mul-of-neg-arg1
                                   mul-of-neg-arg2)))))

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
