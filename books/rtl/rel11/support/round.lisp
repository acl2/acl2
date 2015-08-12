(in-package "RTL")

(include-book "../rel9-rtl-pkg/lib/util")

(local (include-book "arithmetic-5/top" :dir :system))

;; The following lemmas from arithmetic-5 have given me trouble:

(local-in-theory #!acl2(disable |(mod (+ x y) z) where (<= 0 z)| |(mod (+ x (- (mod a b))) y)| |(mod (mod x y) z)| |(mod (+ x (mod a b)) y)|
                    simplify-products-gather-exponents-equal mod-cancel-*-const cancel-mod-+ reduce-additive-constant-< 
                    |(floor x 2)| |(equal x (if a b c))| |(equal (if a b c) x)|))

(include-book "basic")
(include-book "bits")
(include-book "float")
(include-book "old-round")

(local-defthmd drnd-exactp-c-1
  (implies (and (formatp f)
                (rationalp x)
                (<= (expo x) (- (bias f)))
                (>= (expo x) (+ 2 (- (bias f)) (- (prec f))))
                (exactp x (+ (1- (prec f)) (bias f) (expo x)))
                (common-mode-p mode))
           (drepp x f))
  :hints (("Goal" :in-theory (enable drepp bias prec formatp expw))))

(local-defthmd drnd-exactp-c-2
  (implies (and (formatp f)
                (rationalp x)
                (<= (expo x) (- (bias f)))
                (>= (expo x) (+ 2 (- (bias f)) (- (prec f))))
                (exactp x (+ (1- (prec f)) (bias f) (expo x)))
                (common-mode-p mode))
           (= (drnd x mode f) x))
  :hints (("Goal" :use (drnd-exactp-c-1 drnd-exactp-b))))

(local-defthmd drnd-exactp-c-3
  (implies (and (formatp f)
                (rationalp x)
                (<= (expo x) (- (bias f)))
                (>= (expo x) (+ 2 (- (bias f)) (- (prec f))))
                (common-mode-p mode))
           (< (abs x) (spn f)))
  :hints (("Goal" :use ((:instance expo>= (x (abs x)) (n (- 1 (bias f)))))
                  :in-theory (enable spn bias expw formatp))))

(local-defthmd drnd-exactp-c-4
  (implies (and (formatp f)
                (rationalp x)
                (<= (expo x) (- (bias f)))
                (>= (expo x) (+ 2 (- (bias f)) (- (prec f))))
                (= (drnd x mode f) x)
                (common-mode-p mode))
           (drepp x f))
  :hints (("Goal" :use (drnd-exactp-a drnd-exactp-c-3)
                  :in-theory (enable drepp bias prec formatp expw))))

(local-defthmd drnd-exactp-c-5
  (implies (and (formatp f)
                (rationalp x)
                (<= (expo x) (- (bias f)))
                (>= (expo x) (+ 2 (- (bias f)) (- (prec f))))
                (= (drnd x mode f) x)
                (common-mode-p mode))
           (exactp x (+ (1- (prec f)) (bias f) (expo x))))
  :hints (("Goal" :use (drnd-exactp-c-4)
                  :in-theory (enable drepp bias prec formatp expw))))

(defthmd drnd-exactp-c
  (implies (and (formatp f)
                (rationalp x)
                (<= (expo x) (- (bias f)))
                (>= (expo x) (+ 2 (- (bias f)) (- (prec f))))
                (common-mode-p mode))
           (iff (equal x (drnd x mode f))
                (exactp x (+ (1- (prec f)) (bias f) (expo x)))))
  :hints (("Goal" :use (drnd-exactp-c-2 drnd-exactp-c-5))))

(local-defthmd rnd-drnd-up-1
  (implies (and (rationalp x)
                (integerp k)
                (not (zp n))
                (< (abs x) (expt 2 k))
                (common-mode-p mode)
                (= (abs (rnd x mode n)) (expt 2 k)))
           (<= (expo x) (1- k)))
  :hints (("Goal" :use ((:instance expo<= (x (abs x)) (n (1- k)))))))

(local-defthmd rnd-drnd-up-2
  (implies (and (rationalp x)
                (integerp k)
                (not (zp n))
                (< (abs x) (expt 2 k))
                (common-mode-p mode)
                (= (abs (rnd x mode n)) (expt 2 k)))
           (equal (expo x) (1- k)))
  :hints (("Goal" :in-theory (enable flip-mode common-mode-p)
                  :use (rnd-minus rnd-drnd-up-1 expo-rnd
                        (:instance rnd-minus (mode (flip-mode mode)))
                        (:instance expo-rnd (mode (flip-mode mode)))))))

(defthmd rnd-drnd-up
  (implies (and (formatp f)
                (rationalp x)
                (< (abs x) (spn f))
                (common-mode-p mode)
                (= (abs (rnd x mode (prec f))) (spn f)))
           (equal (abs (drnd x mode f)) (spn f)))
  :hints (("Goal" :in-theory (e/d (drnd spn prec formatp expw bias sigw) (abs))
                  :use ((:instance rnd-up (k (- 1 (bias f))) (n (prec f)) (m (+ (prec f) (expo x) (1- (bias f)))))
                        (:instance rnd-drnd-up-2 (k (- 1 (bias f))) (n (prec f)))))))

(local-defthm rnd-drnd-exactp-1
  (implies (and (formatp f)
                (rationalp x)
                (<= (abs x) (spn f))
                (common-mode-p mode))
           (or (<= (- 2 (prec f)) (+ (expo (drnd x mode f)) (bias f)))
               (= (drnd x mode f) 0)))
  :rule-classes ()
  :hints (("Goal" :use (drnd-exactp-a)
                  :in-theory (enable drepp spn sgn bias expw formatp prec))))

(defthmd rnd-drnd-exactp
  (implies (and (formatp f)
                (rationalp x)
                (< (abs x) (spn f))
                (common-mode-p mode)
                (= (drnd x mode f) x))
           (equal (rnd x mode (prec f)) x))
  :hints (("Goal" :in-theory (enable common-mode-p drnd spn prec formatp expw bias sigw)
                  :use (rnd-drnd-exactp-1
                        (:instance expo<= (x (abs x)) (n (1- (expo (spn f)))))
                        (:instance rnd-exactp-b (n (+ (prec f) (expo x) (1- (bias f)))))
                        (:instance rnd-exactp-b (n (prec f)))
                        (:instance exactp-<= (m (+ (prec f) (expo x) (1- (bias f)))) (n (prec f)))))))

