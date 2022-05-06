(in-package "PFIELD")

(include-book "nonstd/polynomials/polynomial-defuns" :dir :system)
(local (include-book "nonstd/polynomials/polynomial-lemmas" :dir :system))
(include-book "kestrel/prime-fields/prime-fields" :dir :system)
(local (include-book "kestrel/prime-fields/rules2" :dir :system))
(local (include-book "projects/quadratic-reciprocity/euclid" :dir :system))
(local (include-book "arithmetic-5/top" :dir :system))

(defund non-trivial-pfield-polynomial-p (poly p)
  (and (acl2::integer-polynomial-p poly)
       ;; (< 1 (len poly))
       (not (equal 0 (fep-fix (car (last poly)) p)))))


;; (defund non-constant-pfield-polynomial-p (poly p)
;;   (and (acl2::integer-polynomial-p poly)
;;        (non-zero-pfield-polynomial-p (cdr poly) p)))

(defund eval-pfield-polynomial (poly x p)
  (mod (acl2::eval-polynomial poly x) p))

(defund pfield-polynomial-root-p (poly x p)
  (and (fep x p)
       (equal (eval-pfield-polynomial poly x p) 0)))

(local
 (defthmd integerp-eval-polynomial
   (implies (and (acl2::integer-polynomial-p poly)
                 (integerp x))
            (integerp (acl2::eval-polynomial poly x)))))

(defthm fep-eval-pfield-polynomial
  (implies (and (acl2::integer-polynomial-p poly)
                (integerp x)
                (integerp p)
                (fep x p))
           (fep (eval-pfield-polynomial poly x p) p))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance integerp-eval-polynomial))
           :in-theory (enable eval-pfield-polynomial
                              fep
                              ))))

(local
 (defthm integer-polynomial-fw-rational-polynomial
   (implies (acl2::integer-polynomial-p poly)
            (acl2::rational-polynomial-p poly))))

(defthm eval-pfield-polynomial-*
  (implies (and (acl2::integer-polynomial-p poly1)
                (acl2::integer-polynomial-p poly2)
                (integerp p)
                (fep x p))
           (equal (eval-pfield-polynomial (acl2::polynomial-* poly1 poly2) x p)
                  (mul (eval-pfield-polynomial poly1 x p)
                       (eval-pfield-polynomial poly2 x p)
                       p)))
  :rule-classes nil
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance acl2::eval-polynomial-*
                            (acl2::poly1 poly1)
                            (acl2::poly2 poly2)
                            (acl2::x x)))
           :in-theory (e/d (eval-pfield-polynomial
                            mul
                            integerp-eval-polynomial)
                           (acl2::eval-polynomial-*)))))

(defthm fep-euclidean
  (implies (and (rtl::primep p)
                (fep a p)
                (fep b p)
                (not (equal 0 a))
                (not (equal 0 b)))
           (not (equal (mul a b p) 0)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance rtl::euclid
                            (rtl::p p)
                            (rtl::a a)
                            (rtl::b b))
                 (:instance rtl::divides-mod-0
                            (rtl::n p)
                            (rtl::a a))
                 (:instance rtl::divides-mod-0
                            (rtl::n p)
                            (rtl::a b))
                 (:instance rtl::divides-mod-0
                            (rtl::n p)
                            (rtl::a (* a b)))
                 )
           :in-theory (enable mul))))

(defthm pfield-polynomial-root-of-product
  (implies (and (acl2::integer-polynomial-p poly1)
                (acl2::integer-polynomial-p poly2)
                (rtl::primep p)
                (fep x p))
           (equal (pfield-polynomial-root-p (acl2::polynomial-* poly1 poly2) x p)
                  (or (pfield-polynomial-root-p poly1 x p)
                      (pfield-polynomial-root-p poly2 x p))))
  :rule-classes nil
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance eval-pfield-polynomial-*)
                 (:instance fep-euclidean
                            (a (eval-pfield-polynomial poly1 x p))
                            (b (eval-pfield-polynomial poly2 x p))
                            (p p))
                 )
           :in-theory (enable pfield-polynomial-root-p))))

(defund pfield-polynomial-num-roots-aux (poly x p)
  (if (zp x)
      0
    (if (pfield-polynomial-root-p poly x p)
        (1+ (pfield-polynomial-num-roots-aux poly (1- x) p))
      (pfield-polynomial-num-roots-aux poly (1- x) p))))

(defund pfield-polynomial-num-roots (poly p)
  (pfield-polynomial-num-roots-aux poly (1- p) p))

(local
 (defun natural-induction (n)
   (if (zp n)
       1
     (1+ (natural-induction (1- n))))))

(defthm pfield-polynbomial-num-roots-aux-of-product
  (implies (and (acl2::integer-polynomial-p poly1)
                (acl2::integer-polynomial-p poly2)
                (rtl::primep p)
                (fep x p))
           (<= (pfield-polynomial-num-roots-aux (acl2::polynomial-* poly1 poly2) x p)
               (+ (pfield-polynomial-num-roots-aux poly1 x p)
                  (pfield-polynomial-num-roots-aux poly2 x p))))
  :rule-classes nil
  :hints (("Goal"
           :do-not-induct t
           :in-theory (enable pfield-polynomial-num-roots-aux)
           :induct (natural-induction x))
          ("Subgoal *1/2"
           :use ((:instance pfield-polynomial-root-of-product))
           :in-theory (enable fep
                              pfield-polynomial-num-roots-aux))))

(defthm pfield-polynbomial-num-roots-of-product
  (implies (and (acl2::integer-polynomial-p poly1)
                (acl2::integer-polynomial-p poly2)
                (rtl::primep p))
           (<= (pfield-polynomial-num-roots (acl2::polynomial-* poly1 poly2) p)
               (+ (pfield-polynomial-num-roots poly1 p)
                  (pfield-polynomial-num-roots poly2 p))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance pfield-polynbomial-num-roots-aux-of-product
                            (poly1 poly1)
                            (poly2 poly2)
                            (x (1- p))
                            (p p)))
           :in-theory (enable pfield-polynomial-num-roots))))


(defthmd eval-linear-polynomial
  (implies (and (acl2::integer-polynomial-p poly)
                (equal (len poly) 2)
                (integerp x))
           (equal (acl2::eval-polynomial poly x)
                  (+ (* (second poly) x) (first poly))))
  :hints (("Goal"
           :in-theory (enable acl2::eval-polynomial)))
  )

(defthmd eval-linear-pfield-polynomial
  (implies (and (acl2::integer-polynomial-p poly)
                (equal (len poly) 2)
                (posp p)
                (integerp x))
           (equal (eval-pfield-polynomial poly x p)
                  (add (mul (second poly) x p)
                       (first poly)
                       p)))
  :hints (("Goal"
           :use ((:instance eval-linear-polynomial))
           :in-theory (enable eval-pfield-polynomial
                              add
                              mul)))
  )

;; Turn these into iffs instead of implies?

(defthm cancel-add-arg2
  (implies (and (posp p)
                (fep x p))
           (iff (equal (add x y p) 0)
                (equal x (neg y p))))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (enable fep add neg))))

(defthm cancel-mul-arg2
  (implies (and (rtl::primep p)
                (fep y p)
                (fep z p)
                (integerp x)
                (not (= (fep-fix x p) 0)))
           (iff (equal (mul x y p) z)
                (equal y (mul (inv x p) z p))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance mul-associative
                            (x (inv x p))
                            (y x)
                            (z y)
                            (p p))
                 (:instance mul-of-inv-arg2
                            (x x)
                            (p p))
                 (:instance mul-commutative
                            (x (inv x p))
                            (y x)
                            (p p))
                 (:instance mul-associative
                            (x x)
                            (y (inv x p))
                            (z z)
                            (p p))
                 )
           :in-theory (disable mul-of-inv-arg2
                               mul-associative
                               mul-commutative))))

(defthmd car-last-of-len-2
  (implies (equal (len poly) 2)
           (equal (car (last poly)) (cadr poly))))

(defthm root-of-linear-pfield-polynomial
  (implies (and (rtl::primep p)
                (non-trivial-pfield-polynomial-p poly p)
                (equal (len poly) 2)
                (fep x p))
           (equal (pfield-polynomial-root-p poly x p)
                  (equal x (neg (div (first poly)
                                     (second poly)
                                     p)
                                p))))
  :rule-classes nil
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance eval-linear-pfield-polynomial)
                 (:instance cancel-add-arg2
                            (x (mul (second poly) x p))
                            (y (first poly))
                            (p p))
                 (:instance cancel-mul-arg2
                            (x (second poly))
                            (y x)
                            (z (neg (first poly) p))
                            (p p))
                 (:instance neg-of-mul-arg2
                            (x (inv (cadr poly) p))
                            (y (car poly))
                            (p p))
                 (:instance car-last-of-len-2)
                 )
           :in-theory (enable pfield-polynomial-root-p
                              non-trivial-pfield-polynomial-p
                              div)))
  )

(defthm num-roots-aux-of-linear-pfield-polynomial-part1
  (implies (and (rtl::primep p)
                (non-trivial-pfield-polynomial-p poly p)
                (equal (len poly) 2)
                (fep x p)
                (< x (neg (div (first poly)
                               (second poly)
                               p)
                          p)))
           (equal (pfield-polynomial-num-roots-aux poly x p)
                  0))
  :rule-classes nil
  :hints (("Goal"
           :do-not-induct t
           :induct (natural-induction x)
           :in-theory (e/d (fep
                            pfield-polynomial-num-roots-aux)
                           (equal-of-neg)))
          ("Subgoal *1/2"
           :use ((:instance root-of-linear-pfield-polynomial)))
          )
  )

(local
 (defthm num-roots-aux-of-0-arg2
   (equal (pfield-polynomial-num-roots-aux poly 0 p)
          0)
   :hints (("Goal"
            :in-theory (enable pfield-polynomial-num-roots-aux)))))

(local
 (defthm fep-neg-div-minus-1
   (implies (and (posp p)
                 (fep x p)
                 (not (= 0 x))
                 )
            (fep (1- (neg x p)) p))
   :rule-classes nil
   :hints (("Goal"
            :in-theory (enable fep neg)))))

(defthm num-roots-aux-of-linear-pfield-polynomial-part2
  (implies (and (rtl::primep p)
                (non-trivial-pfield-polynomial-p poly p)
                (equal (len poly) 2)
                (fep x p)
                (= x (neg (div (first poly)
                               (second poly)
                               p)
                          p)))
           (equal (pfield-polynomial-num-roots-aux poly x p)
                  (if (and (pfield-polynomial-root-p poly x p)
                           (< 0 x))
                      1
                    0)))
  :rule-classes nil
  :hints (("Goal"
           :do-not-induct t
           :expand (pfield-polynomial-num-roots-aux poly x p)
           :use ((:instance root-of-linear-pfield-polynomial)
                 (:instance num-roots-aux-of-linear-pfield-polynomial-part1
                            (poly poly)
                            (x (1- x))
                            (p p))
                 (:instance fep-neg-div-minus-1
                            (x (div (car poly) (cadr poly) p))
                            (p p))
                 )
           :in-theory (enable pfield-polynomial-num-roots-aux))))

(defthm num-roots-aux-of-linear-pfield-polynomial-part3a
  (implies (and (rtl::primep p)
                (non-trivial-pfield-polynomial-p poly p)
                (equal (len poly) 2)
                (fep x p)
                (> x (neg (div (first poly)
                               (second poly)
                               p)
                          p)))
           (equal (pfield-polynomial-num-roots-aux poly x p)
                  (pfield-polynomial-num-roots-aux poly (1- x) p)))
  :rule-classes nil
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance root-of-linear-pfield-polynomial))
           :in-theory (e/d (pfield-polynomial-num-roots-aux)
                           (equal-of-neg))
           )))

(local
 (defun induct-from-n-down-to-k (n k)
   (if (or (zp n) (= n k))
       1
     (1+ (induct-from-n-down-to-k (1- n) k)))))

(local
 (defthm num-roots-zero-when-root-is-zero
  (implies (and (rtl::primep p)
                (non-trivial-pfield-polynomial-p poly p)
                (equal (len poly) 2)
                (fep x p)
                (= 0 (div (car poly) (cadr poly) p)))
           (= (pfield-polynomial-num-roots-aux poly x p) 0))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (enable pfield-polynomial-num-roots-aux))
          ("Subgoal *1/2"
           :use ((:instance root-of-linear-pfield-polynomial)))
          )))

(encapsulate
  nil

  (local
   (defthm lemma-1
     (implies (and (posp p)
                   (fep x p)
                   (fep y p)
                   (< y x))
              (not (zp x)))
     :rule-classes nil
     :hints (("Goal"
              :in-theory (enable fep)))))

  (defthm num-roots-aux-of-linear-pfield-polynomial-part3
    (implies (and (rtl::primep p)
                  (non-trivial-pfield-polynomial-p poly p)
                  (equal (len poly) 2)
                  (fep x p)
                  (> x (neg (div (first poly)
                                 (second poly)
                                 p)
                            p)))
             (equal (pfield-polynomial-num-roots-aux poly x p)
                    (if (and (pfield-polynomial-root-p poly
                                                       (neg (div (first poly)
                                                                 (second poly)
                                                                 p)
                                                            p)
                                                       p)
                             (< 0 (neg (div (first poly)
                                            (second poly)
                                            p)
                                       p)))
                        1
                      0)))
    :rule-classes nil
    :hints (("Goal"
             :induct (induct-from-n-down-to-k x (neg (div (first poly)
                                                          (second poly)
                                                          p)
                                                     p))
             )
            ("Subgoal *1/2"
             :use ((:instance num-roots-aux-of-linear-pfield-polynomial-part2
                              (x  (neg (div (first poly)
                                            (second poly)
                                            p)
                                       p)))
                   (:instance num-roots-aux-of-linear-pfield-polynomial-part3a)
                   )
             )
            ("Subgoal *1/1"
             :use ((:instance lemma-1
                              (x x)
                              (y (neg (div (car poly) (cadr poly) p) p))
                              (p p))
                   )
             :in-theory (disable equal-of-neg)
             )
            ))
  )

(defthm num-roots-aux-of-linear-pfield-polynomial-upper-bound
  (implies (and (rtl::primep p)
                (non-trivial-pfield-polynomial-p poly p)
                (equal (len poly) 2)
                (fep x p))
           (<= (pfield-polynomial-num-roots-aux poly x p)
               1))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance num-roots-aux-of-linear-pfield-polynomial-part1)
                 (:instance num-roots-aux-of-linear-pfield-polynomial-part2)
                 (:instance num-roots-aux-of-linear-pfield-polynomial-part3)))))

(defthm num-roots-of-linear-pfield-polynomial-upper-bound
  (implies (and (rtl::primep p)
                (non-trivial-pfield-polynomial-p poly p)
                (equal (len poly) 2))
           (<= (pfield-polynomial-num-roots poly p)
               1))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance
                  num-roots-aux-of-linear-pfield-polynomial-upper-bound
                  (p p)
                  (poly poly)
                  (x (1- p))))
           :in-theory (enable pfield-polynomial-num-roots))))


;;; These belong in the book about transcendental numbers


(defun divide-polynomial-with-remainder-by-x+a (poly a)
  (if (consp poly)
    (let ((rest (divide-polynomial-with-remainder-by-x+a (cdr poly) a)))
        (if (consp rest)
            (cons (- (car poly)
                     (* a (car rest)))
                  rest)
          (list (car poly))))
    nil))


;; (defthm rationalp-divide-polynomial
;;   (implies (and (acl2::rational-polynomial-p poly)
;;                 (rationalp a))
;;            (acl2::rational-polynomial-p (divide-polynomial-with-remainder-by-x+a
;;   poly a))))

(defthmd integer-polynomialp-divide-polynomial
  (implies (and (acl2::integer-polynomial-p poly)
                (integerp a))
           (acl2::integer-polynomial-p (divide-polynomial-with-remainder-by-x+a
  poly a))))

(defthm eval-divide-poly
  (implies (and (acl2::integer-polynomial-p poly)
                (integerp a)
                (integerp x))
           (equal (+ (* (acl2::eval-polynomial (cdr (divide-polynomial-with-remainder-by-x+a poly a)) x)
                        (+ x a))
                     (car (divide-polynomial-with-remainder-by-x+a poly a)))
                  (acl2::eval-polynomial poly x)))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (enable integer-polynomialp-divide-polynomial))))

(encapsulate
  nil

  (local
   (defthm lemma-1
     (implies (and (integerp a)
                   (integerp x))
              (equal (acl2::eval-polynomial `(,a 1) x)
                     (+ x a)))
     :rule-classes nil))

  (local
   (defthm lemma-2
     (implies (and (acl2::integer-polynomial-p poly)
                   (integerp a)
                   (integerp x))
              (equal (* (acl2::eval-polynomial poly x)
                        (+ x a))
                     (acl2::eval-polynomial (acl2::polynomial-* `(,a 1) poly)
                                            x)))
     :rule-classes nil
     :hints (("Goal"
              :use ((:instance lemma-1)
                    (:instance acl2::eval-polynomial-*
                               (acl2::poly1 `(,a 1))
                               (acl2::poly2 poly)
                               (acl2::x x))
                    )
              ))))

  (defthm eval-divide-poly-2
    (implies (and (acl2::integer-polynomial-p poly)
                  (integerp a)
                  (integerp x))
             (equal (+ (acl2::eval-polynomial
                        (acl2::polynomial-*
                         `(,a 1)
                         (cdr (divide-polynomial-with-remainder-by-x+a
                               poly
                               a)))
                        x)
                       (car (divide-polynomial-with-remainder-by-x+a poly a)))
                    (acl2::eval-polynomial poly x)))
    :rule-classes nil
    :hints (("Goal"
             :do-not-induct t
             :use ((:instance eval-divide-poly)
                   (:instance lemma-2
                              (poly (cdr
                                     (divide-polynomial-with-remainder-by-x+a poly a)))
                              (x x)
                              (a a))
                   (:instance integer-polynomialp-divide-polynomial)
                   )
             )))
  )


(defthm root-remainder
  (implies (and (acl2::integer-polynomial-p poly)
                (integerp a)
                (rtl::primep p)
                (pfield-polynomial-root-p poly a p))
           (equal (mod (car (divide-polynomial-with-remainder-by-x+a poly (- a)))
                       p)
                  0))
  :rule-classes nil
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance eval-divide-poly-2
                            (x a)
                            (a (- a))
                            (poly poly))
                 (:instance integer-polynomialp-divide-polynomial
                            (a (- a))
                            (poly poly))
                 )
           :in-theory (e/d (pfield-polynomial-root-p
                            eval-pfield-polynomial)
                           ()))))

(defthm integer-polynomialp-poly-+
  (implies (and (acl2::integer-polynomial-p poly1)
                (acl2::integer-polynomial-p poly2))
           (acl2::integer-polynomial-p (acl2::polynomial-+ poly1 poly2))))

(defthm integer-polynomialp-scale-polynomial
  (implies (and (acl2::integer-polynomial-p poly)
                (integerp k))
           (acl2::integer-polynomial-p (acl2::scale-polynomial poly k))))

(defthm integer-polynomialp-poly-*
  (implies (and (acl2::integer-polynomial-p poly1)
                (acl2::integer-polynomial-p poly2))
           (acl2::integer-polynomial-p (acl2::polynomial-* poly1 poly2))))

(defthm consp-divide-polynomial-with-remainder-by-x+a
  (equal (consp (divide-polynomial-with-remainder-by-x+a poly (- a)))
         (consp poly)))

(encapsulate
  nil

  (local
   (defthmd lemma-1
     (implies (and (integerp a)
                   (integerp x))
              (integerp (acl2::eval-polynomial (acl2::polynomial-* `(,(- a) 1)
                                                                   nil)
                                               x)))
     ))

  (local
   (defthm lemma-2
     (implies (and (acl2::integer-polynomial-p poly)
                   (integerp a)
                   (integerp x)
                   (rtl::primep p)
                   (pfield-polynomial-root-p poly a p))
              (equal (eval-pfield-polynomial poly x p)
                     (eval-pfield-polynomial
                      (acl2::polynomial-*
                       `(,(- a) 1)
                       (cdr (divide-polynomial-with-remainder-by-x+a
                             poly
                             (- a))))
                      x
                      p)))
     :rule-classes nil
     :hints (("Goal"
              :do-not-induct t
              :use ((:instance root-remainder)
                    (:instance eval-divide-poly-2
                               (x x)
                               (a (- a))
                               (poly poly))
                    (:instance integer-polynomialp-divide-polynomial
                               (a (- a))
                               (poly poly))
                    (:instance lemma-1)
                    )
              :in-theory (e/d (eval-pfield-polynomial)
                              (acl2::polynomial-*
                               acl2::eval-polynomial-*
                               acl2::eval-polynomial))
              ))))

  (local
   (defthm lemma-3
     (equal (eval-pfield-polynomial nil x p) 0)
     :hints (("Goal"
              :in-theory (enable eval-pfield-polynomial
                                 acl2::eval-polynomial)))))

  (defthm eval-poly-with-root
    (implies (and (acl2::integer-polynomial-p poly)
                  (rtl::primep p)
                  (integerp a)
                  (fep x p)
                  (pfield-polynomial-root-p poly a p))
             (equal (eval-pfield-polynomial poly x p)
                    (mul (eval-pfield-polynomial
                          `(,(- a) 1)
                          x
                          p)
                         (eval-pfield-polynomial
                          (cdr (divide-polynomial-with-remainder-by-x+a
                                poly
                                (- a)))
                          x
                          p)
                         p)))
    :rule-classes nil
    :hints (("Goal"
             :do-not-induct t
             :use ((:instance lemma-1)
                   (:instance lemma-2)
                   (:instance integer-polynomialp-divide-polynomial
                              (poly poly)
                              (a (- a)))
                   (:instance eval-pfield-polynomial-*
                              (poly1 `(,(- a) 1))
                              (poly2 (cdr (divide-polynomial-with-remainder-by-x+a
                                           poly
                                           (- a))))
                              (x x)
                              (p p)))
             :in-theory (disable divide-polynomial-with-remainder-by-x+a
                                 acl2::eval-polynomial
                                 acl2::polynomial-*
                                 acl2::polynomial-+
                                 acl2::scale-polynomial)
             )))

  )


;; (defthm roots-of-x-a
;;   (implies (and (rtl::primep p)
;;                 (fep a p)
;;                 (fep b p))
;;            (equal (pfield-polynomial-root-p `(,(- a) 1) b p)
;;                   (equal b a)))
;;   :rule-classes nil
;;   :hints (("Goal"
;;            :in-theory (enable pfield-polynomial-root-p
;;                               eval-pfield-polynomial
;;                               acl2::eval-polynomial)))
;;   )

;; (defthm num-roots-aux-of-x-a-part1
;;   (implies (and (rtl::primep p)
;;                 (fep a p)
;;                 (fep b p)
;;                 (< b a))
;;            (equal (pfield-polynomial-num-roots-aux `(,(- a) 1) b p)
;;                   0))
;;   :rule-classes nil
;;   :hints (("Goal"
;;            :do-not-induct t
;;            :induct (natural-induction b)
;;            :in-theory (enable fep
;;                               pfield-polynomial-num-roots-aux))
;;           ("Subgoal *1/2"
;;            :use ((:instance roots-of-x-a)))
;;           )
;;   )


;; (defthm num-roots-aux-of-x-a-part2
;;   (implies (and (rtl::primep p)
;;                 (fep a p)
;;                 (not (= 0 a))
;;                 (fep b p))
;;            (equal (pfield-polynomial-num-roots-aux `(,(- a) 1) b p)
;;                   (if (or (zp b) (< b a))
;;                       0
;;                     1)))
;;   :rule-classes nil
;;   :hints (("Goal"
;;            :do-not-induct t
;;            :induct (natural-induction b)
;;            :in-theory (enable fep
;;                               pfield-polynomial-num-roots-aux))
;;           ("Subgoal *1/2"
;;            :cases ((< b a) (= b a) (> b a)))
;;           ("Subgoal *1/2.3"
;;            :use ((:instance num-roots-aux-of-x-a-part1)))
;;           ("Subgoal *1/2.2"
;;            :use ((:instance roots-of-x-a)))
;;           ("Subgoal *1/2.1"
;;            :use ((:instance roots-of-x-a)))
;;           )
;;   )

;; (defthm num-roots-aux-of-x-a-part3
;;   (implies (and (rtl::primep p)
;;                 (fep a p)
;;                 (= 0 a)
;;                 (fep b p))
;;            (equal (pfield-polynomial-num-roots-aux `(,(- a) 1) b p)
;;                   0))
;;   :rule-classes nil
;;   :hints (("Goal"
;;            :do-not-induct t
;;            :induct (natural-induction b)
;;            :in-theory (enable fep
;;                               pfield-polynomial-num-roots-aux))
;;           ("Subgoal *1/2"
;;            :use ((:instance roots-of-x-a)))
;;           ))

;; (defthm num-roots-aux-of-x-a
;;   (implies (and (rtl::primep p)
;;                 (fep a p)
;;                 (fep b p))
;;            (equal (pfield-polynomial-num-roots-aux `(,(- a) 1) b p)
;;                   (if (or (zp a) (zp b) (< b a))
;;                       0
;;                     1)))
;;   :rule-classes nil
;;   :hints (("Goal"
;;            :use ((:instance num-roots-aux-of-x-a-part2)
;;                  (:instance num-roots-aux-of-x-a-part3))
;;            :in-theory (enable fep))))


;; (defthm num-roots-of-x-a-upper-bound
;;   (implies (and (rtl::primep p)
;;                 (fep a p))
;;            (<= (pfield-polynomial-num-roots `(,(- a) 1) p) 1))
;;   :rule-classes nil
;;   :hints (("Goal"
;;            :use ((:instance num-roots-aux-of-x-a
;;                             (a a)
;;                             (b (1- p))
;;                             (p p)))
;;            :in-theory (enable fep pfield-polynomial-num-roots))))

(defund find-polynomial-root-aux (poly x p)
  (if (zp x)
      nil
    (if (pfield-polynomial-root-p poly x p)
        x
      (find-polynomial-root-aux poly (1- x) p))))

(defund find-polynomial-root (poly p)
  (find-polynomial-root-aux poly (1- p) p))

(defthmd find-polynomial-root-aux-not-nil-iff-num-roots-gt-0
  (iff (< 0 (pfield-polynomial-num-roots-aux poly x p))
       (integerp (find-polynomial-root-aux poly x p)))
  :hints (("Goal"
           :in-theory (enable pfield-polynomial-num-roots-aux
                              find-polynomial-root-aux))))

(defthmd find-polynomial-root-not-nil-iff-num-roots-gt-0
  (iff (< 0 (pfield-polynomial-num-roots poly p))
       (integerp (find-polynomial-root poly p)))
  :hints (("Goal"
           :use ((:instance find-polynomial-root-aux-not-nil-iff-num-roots-gt-0
                            (poly poly)
                            (x (1- p))
                            (p p)))
           :in-theory (enable pfield-polynomial-num-roots
                              find-polynomial-root))))

(defthmd find-polynomial-root-aux-finds-root-if-not-nil
  (implies (integerp (find-polynomial-root-aux poly x p))
           (pfield-polynomial-root-p poly (find-polynomial-root-aux poly x p) p))
  :hints (("Goal"
           :in-theory (enable find-polynomial-root-aux))))

(defthmd find-polynomial-root-finds-root-if-not-nil
  (implies (integerp (find-polynomial-root poly p))
           (pfield-polynomial-root-p poly (find-polynomial-root poly p) p))
  :hints (("Goal"
           :use ((:instance find-polynomial-root-aux-finds-root-if-not-nil
                            (poly poly)
                            (x (1- p))
                            (p p)))
           :in-theory (enable pfield-polynomial-num-roots
                              find-polynomial-root))))

(defthmd find-polynomial-root-aux-is-largest-root
  (implies (and (< (find-polynomial-root-aux poly x p) y)
                (fep x p)
                (fep y p)
                (<= y x))
           (not (pfield-polynomial-root-p poly y p)))
  :hints (("Goal"
           :in-theory (enable find-polynomial-root-aux
                              fep))))


(defthmd find-polynomial-root-is-largest-root
  (implies (and (< (find-polynomial-root poly p) y)
                (rtl::primep p)
                (fep y p))
           (not (pfield-polynomial-root-p poly y p)))
  :hints (("Goal"
           :use ((:instance find-polynomial-root-aux-is-largest-root
                            (poly poly)
                            (x (1- p))
                            (p p)))
           :in-theory (enable fep
                              find-polynomial-root))))

(defthmd len-divide-polynomial-with-remainder-by-x+a
  (implies (consp poly)
           (equal (len (divide-polynomial-with-remainder-by-x+a poly a))
                  (len poly))))

(defthmd last-divide-polynomial-with-remainder-by-x+a
  (implies (and (acl2::integer-polynomial-p poly)
                (consp poly))
           (equal (last (divide-polynomial-with-remainder-by-x+a poly a))
                  (last poly))))

(defun num-roots-of-poly-upper-bound-induction-hint (poly p)
  (declare (xargs :measure (len poly)
                  :hints (("Subgoal *2/3"
                           :use ((:instance
                                  find-polynomial-root-not-nil-iff-num-roots-gt-0)))
                          ("Subgoal *2/2"
                           :use ((:instance
                                  find-polynomial-root-not-nil-iff-num-roots-gt-0)))
                          ("Subgoal *2/1"
                           :use ((:instance
                                  find-polynomial-root-not-nil-iff-num-roots-gt-0)))
                          ("Subgoal *1/4"
                           :use ((:instance
                                  len-divide-polynomial-with-remainder-by-x+a
                                  (poly poly)
                                  (a (- (find-polynomial-root poly p))))))
                          ("Subgoal *1/3"
                           :use ((:instance
                                  len-divide-polynomial-with-remainder-by-x+a
                                  (poly poly)
                                  (a (- (find-polynomial-root poly p))))))
                          ("Subgoal *1/2"
                           :use ((:instance
                                  len-divide-polynomial-with-remainder-by-x+a
                                  (poly poly)
                                  (a (- (find-polynomial-root poly p))))))
                          )))
  (if (<= (len poly) 2)
      0
    (if (zp (pfield-polynomial-num-roots poly p))
        1
      (num-roots-of-poly-upper-bound-induction-hint
       (cdr (divide-polynomial-with-remainder-by-x+a
             poly
             (- (find-polynomial-root poly p))))
       p))))

(defthm consp-divide-polynomial
  (equal (consp (divide-polynomial-with-remainder-by-x+a poly a))
         (consp poly)))

;; (defthm zero-car-of-non-empty-zero-pfield-polynomial
;;   (implies (and (posp p)
;;                 (zero-pfield-polynomial-p poly P)
;;                 (consp poly))
;;            (equal (mod (car poly) p) 0))
;;   :rule-classes nil
;;   :hints (("Goal"
;;            :do-not-induct t
;;            :expand (zero-pfield-polynomial-p poly p))))

;; (defthm zero-of-remainder-when-zero-polynomials
;;   (implies (and (acl2::integer-polynomial-p poly)
;;                 (consp poly)
;;                 (rtl::primep p)
;;                 (zero-pfield-polynomial-p poly P)
;;                 (acl2::integer-polynomial-p poly2)
;;                 (consp poly2)
;;                 (zero-pfield-polynomial-p poly2 P)
;;                 (integerp a))
;;            (equal 0 (fep-fix (+ (car poly)
;;                                 (- (* a (car poly2))))
;;                              p)))
;;   :rule-classes nil
;;   :hints (("Goal"
;;            :do-not-induct t
;;            :use ((:instance zero-car-of-non-empty-zero-pfield-polynomial)
;;                  (:instance zero-car-of-non-empty-zero-pfield-polynomial
;;                             (poly poly2)
;;                             (p p)))
;;            ))
;;   )

(defthm integer-car-divide-polynomial-with-remainder-by-x+a
  (implies (and (acl2::integer-polynomial-p poly)
                (consp poly)
                (integerp a))
           (integerp (car (divide-polynomial-with-remainder-by-x+a poly a))))
  :rule-classes nil
  )

;; (defthm zero-polynomial-divide-zero-polynomial
;;   (implies (and (acl2::integer-polynomial-p poly)
;;                 (rtl::primep p)
;;                 (zero-pfield-polynomial-p poly P)
;;                 (integerp a))
;;            (zero-pfield-polynomial-p
;;             (divide-polynomial-with-remainder-by-x+a poly a)
;;             P))
;;   :rule-classes nil
;;   :hints (("Goal"
;;            :in-theory (enable acl2::integer-polynomial-p
;;                               zero-pfield-polynomial-p))
;;            ("Subgoal *1/3"
;;            :use ((:instance integer-car-divide-polynomial-with-remainder-by-x+a
;;                             (poly (cdr poly))
;;                             (a a))
;;                  (:instance zero-of-remainder-when-zero-polynomials
;;                             (poly poly)
;;                             (poly2 (divide-polynomial-with-remainder-by-x+a (cdr poly)
;;                                                                             a))
;;                             (a a)
;;                             (p p))
;;                  )
;;            )
;;           ("Subgoal *1/2"
;;            :use ((:instance integer-car-divide-polynomial-with-remainder-by-x+a)))
;;           )
;;   )

;; (defthm not-zero-pfield-polynomia-len0-contradiction
;;   (implies (= 0 (len poly))
;;            (zero-pfield-polynomial-p poly p))
;;   :rule-classes nil
;;   :hints (("Goal"
;;            :do-not-induct t
;;            :expand (zero-pfield-polynomial-p poly p)
;;            :in-theory (enable zero-pfield-polynomial-p))))

;; (defthm not-zero-pfield-polynomia-len1-has-non-zero-coeffs
;;   (implies (and (rtl::primep p)
;;                 (acl2::integer-polynomial-p poly)
;;                 (not (zero-pfield-polynomial-p poly p))
;;                 (= 1 (len poly)))
;;            (not (= 0 (fep-fix (car poly) p))))
;;   :rule-classes nil
;;   :hints (("Goal"
;;            :do-not-induct t
;;            :expand (zero-pfield-polynomial-p poly p)
;;            :use ((:instance not-zero-pfield-polynomia-len0-contradiction
;;                             (poly (cdr poly))))
;;            :in-theory (enable zero-pfield-polynomial-p))))

;; (defthm not-zero-pfield-linear-polynomia-has-non-zero-coeffs
;;   (implies (and (rtl::primep p)
;;                 (acl2::integer-polynomial-p poly)
;;                 (not (zero-pfield-polynomial-p poly p))
;;                 (= 2 (len poly)))
;;            (or (not (= 0 (fep-fix (car poly) p)))
;;                (not (= 0 (fep-fix (cadr poly) p)))))
;;   :rule-classes nil
;;   :hints (("Goal"
;;            :do-not-induct t
;;            :expand (zero-pfield-polynomial-p poly p)
;;            :use ((:instance not-zero-pfield-polynomia-len1-has-non-zero-coeffs
;;                             (poly (cdr poly))
;;                             (p p)))
;;            :in-theory (enable zero-pfield-polynomial-p))))

;; (defthm len0-into-consp
;;   (equal (equal 0 (len poly))
;;          (not (consp poly))))

;; (defthm open-divide-poynomial-when-constant-poly
;;   (implies (and (= 1 (len poly)))
;;            (equal (divide-polynomial-with-remainder-by-x+a poly a)
;;                   (list (car poly))))
;;   :rule-classes nil
;;   :hints (("Goal"
;;            :do-not-induct t
;;            :expand ((divide-polynomial-with-remainder-by-x+a poly a))
;;            )))

;; (defthm non-zero-divide-polynomial-with-remainder-by-x+a-base
;;   (implies (and (rtl::primep p)
;;                 (acl2::integer-polynomial-p poly)
;;                 (not (zero-pfield-polynomial-p poly p))
;;                 (= 2 (len poly))
;;                 (integerp a))
;;            (not (zero-pfield-polynomial-p
;;                  (divide-polynomial-with-remainder-by-x+a poly a)
;;                  p)))
;;   :rule-classes nil
;;   :hints (("Goal"
;;            :do-not-induct t
;;            :cases ((not (= 0 (fep-fix (cadr poly) p))))
;;            :in-theory (enable zero-pfield-polynomial-p))
;;           ))


;; (defund non-zero-divide-polynomial-with-remainder-by-x+a-induction-hint (poly p)
;;   (if (consp poly)
;;       (if (integerp (car poly))
;;           (if (equal 0 (fep-fix (car poly) p))
;;                (1+
;;                 (non-zero-divide-polynomial-with-remainder-by-x+a-induction-hint
;;                  (cdr poly)
;;                  p))
;;             (if (zero-pfield-polynomial-p (cdr poly) p)
;;                 10
;;               (1+
;;                (non-zero-divide-polynomial-with-remainder-by-x+a-induction-hint
;;                 (cdr poly)
;;                 p))))
;;         0)
;;     0))


(defthm non-trivial-divide-polynomial-with-remainder-by-x+a
  (implies (and (rtl::primep p)
                (non-trivial-pfield-polynomial-p poly p)
                (<= 2 (len poly))
                (consp poly)
                (integerp a))
           (non-trivial-pfield-polynomial-p
                 (cdr (divide-polynomial-with-remainder-by-x+a poly a))
                 p))
  :rule-classes nil
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance last-divide-polynomial-with-remainder-by-x+a
                            (a a)
                            (poly poly))
                 (:instance len-divide-polynomial-with-remainder-by-x+a
                            (a a)
                            (poly poly))
                 (:instance integer-polynomialp-divide-polynomial
                            (a a)
                            (poly poly))
                 (:instance find-polynomial-root-aux-not-nil-iff-num-roots-gt-0)
                 )
           :in-theory (enable non-trivial-pfield-polynomial-p)
           )))

(defthm nil-is-not-non-trivial
  (not (non-trivial-pfield-polynomial-p nil p))
  :hints (("Goal"
           :in-theory (enable non-trivial-pfield-polynomial-p))))

(defthm acl2-numberp-divide-polynomial-with-remainder-by-x+a
  (equal (acl2-numberp (car (divide-polynomial-with-remainder-by-x+a poly a)))
         (or (consp (cdr poly))
             (acl2-numberp (car poly)))))

(in-theory (disable divide-polynomial-with-remainder-by-x+a))

(defthm obvious-root-of-x-a
  (implies (and (posp p)
                (fep a p))
           (equal (eval-pfield-polynomial (list (- a) 1) a p)
                  0))
  :hints (("Goal"
           :in-theory (enable eval-pfield-polynomial
                              acl2::eval-polynomial))))

(defthm root-of-x-a
  (implies (and (rtl::primep p)
                (fep a p)
                (fep x p))
           (iff (equal 0 (eval-pfield-polynomial (list (- a) 1) x p))
                (equal x a)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance root-of-linear-pfield-polynomial
                            (p p)
                            (poly (list (- a) 1))
                            (x x)))
           :in-theory (e/d (pfield-polynomial-root-p
                            non-trivial-pfield-polynomial-p
                            neg
                            )
                           (equal-of-neg)
                              ))))


(defthm roots-of-divide-polynomial-with-remainder-by-x+a
  (implies (and (acl2::integer-polynomial-p poly)
                (rtl::primep p)
                (integerp a)
                (fep x p)
                (pfield-polynomial-root-p poly a p))
           (iff (pfield-polynomial-root-p poly x p)
                (or (equal x a)
                    (pfield-polynomial-root-p
                     (cdr (divide-polynomial-with-remainder-by-x+a
                           poly
                           (- a)))
                     x
                     p))))
  :rule-classes nil
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance fep-euclidean
                            (a (eval-pfield-polynomial
                                `(,(- a) 1)
                                x
                                p))
                            (b (eval-pfield-polynomial
                                (cdr (divide-polynomial-with-remainder-by-x+a
                                      poly
                                      (- a)))
                                x
                                p))
                            (p p))
                 (:instance eval-poly-with-root)
                 (:instance integer-polynomialp-divide-polynomial
                            (poly poly)
                            (a (- a)))
                 (:instance root-of-x-a)
                 )
           :in-theory (enable pfield-polynomial-root-p))))


(defthm num-roots-aux-of-divide-polynomial-with-remainder-by-x+a-part1
  (implies (and (acl2::integer-polynomial-p poly)
                (rtl::primep p)
                (integerp a)
                (pfield-polynomial-root-p poly a p)
                (fep x p)
                (< x a))
           (= (pfield-polynomial-num-roots-aux poly x p)
              (pfield-polynomial-num-roots-aux
               (cdr (divide-polynomial-with-remainder-by-x+a
                     poly
                     (- a)))
               x
               p)))
  :rule-classes nil
  :hints (("Goal"
           :do-not-induct t
           :induct (pfield-polynomial-num-roots-aux poly x p)
           :in-theory (enable pfield-polynomial-num-roots-aux))
          ("Subgoal *1/3"
           :use ((:instance roots-of-divide-polynomial-with-remainder-by-x+a)))
          ("Subgoal *1/2"
           :use ((:instance roots-of-divide-polynomial-with-remainder-by-x+a)))
          )
  )

(defthm num-roots-aux-of-divide-polynomial-with-remainder-by-x+a-part2
  (implies (and (acl2::integer-polynomial-p poly)
                (rtl::primep p)
                (integerp a)
                (pfield-polynomial-root-p poly a p)
                (fep x p)
                (= x a))
           (<= (pfield-polynomial-num-roots-aux poly x p)
               (1+ (pfield-polynomial-num-roots-aux
                    (cdr (divide-polynomial-with-remainder-by-x+a
                          poly
                          (- a)))
                    x
                    p))))
  :rule-classes nil
  :hints (("Goal"
           :do-not-induct t
           :in-theory (enable pfield-polynomial-num-roots-aux)
           :use ((:instance roots-of-divide-polynomial-with-remainder-by-x+a)
                 (:instance
                  num-roots-aux-of-divide-polynomial-with-remainder-by-x+a-part1
                  (x (1- x))
                  (a a)
                  (poly poly))))))

(defthm num-roots-aux-of-divide-polynomial-with-remainder-by-x+a-part3
  (implies (and (acl2::integer-polynomial-p poly)
                (rtl::primep p)
                (integerp a)
                (pfield-polynomial-root-p poly a p)
                (fep x p)
                (> x a))
           (<= (pfield-polynomial-num-roots-aux poly x p)
               (1+ (pfield-polynomial-num-roots-aux
                    (cdr (divide-polynomial-with-remainder-by-x+a
                          poly
                          (- a)))
                    x
                    p))))
  :rule-classes nil
  :hints (("Goal"
           :do-not-induct t
           :induct (pfield-polynomial-num-roots-aux poly x p)
           :in-theory (enable pfield-polynomial-num-roots-aux))
          ("Subgoal *1/3"
           :use ((:instance roots-of-divide-polynomial-with-remainder-by-x+a)
                 (:instance
                  num-roots-aux-of-divide-polynomial-with-remainder-by-x+a-part2
                  (x a))))
          ("Subgoal *1/2"
           :use ((:instance roots-of-divide-polynomial-with-remainder-by-x+a)
                 (:instance
                  num-roots-aux-of-divide-polynomial-with-remainder-by-x+a-part2
                  (x a))))
          )
  )

(defthm num-roots-aux-of-divide-polynomial-with-remainder-by-x+a
  (implies (and (acl2::integer-polynomial-p poly)
                (rtl::primep p)
                (integerp a)
                (pfield-polynomial-root-p poly a p)
                (fep x p))
           (<= (pfield-polynomial-num-roots-aux poly x p)
               (1+ (pfield-polynomial-num-roots-aux
                    (cdr (divide-polynomial-with-remainder-by-x+a
                          poly
                          (- a)))
                    x
                    p))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance
                  num-roots-aux-of-divide-polynomial-with-remainder-by-x+a-part1)
                 (:instance
                  num-roots-aux-of-divide-polynomial-with-remainder-by-x+a-part2)
                 (:instance
                  num-roots-aux-of-divide-polynomial-with-remainder-by-x+a-part3)
                 ))))


(defthm num-roots-of-divide-polynomial-with-remainder-by-x+a
  (implies (and (acl2::integer-polynomial-p poly)
                (rtl::primep p)
                (integerp a)
                (pfield-polynomial-root-p poly a p))
           (<= (pfield-polynomial-num-roots poly p)
               (1+ (pfield-polynomial-num-roots
                    (cdr (divide-polynomial-with-remainder-by-x+a
                          poly
                          (- a)))
                    p))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance
                  num-roots-aux-of-divide-polynomial-with-remainder-by-x+a
                  (a a)
                  (p p)
                  (x (1- p))
                  (poly poly)))
           :in-theory (enable pfield-polynomial-num-roots))))

(defthmd non-trivial-polynomials-are-integer-polynomials
  (implies (non-trivial-pfield-polynomial-p poly p)
           (acl2::integer-polynomial-p poly))
  :hints (("Goal"
           :in-theory (enable non-trivial-pfield-polynomial-p))))

(defthm num-roots-of-poly-upper-bound
  (implies (and (rtl::primep p)
                (non-trivial-pfield-polynomial-p poly p)
                (<= 2 (len poly))
                )
           (<= (pfield-polynomial-num-roots poly p)
               (len (cdr poly))))
  :rule-classes nil
  :hints (("Goal"
           :do-not-induct t
           :induct (num-roots-of-poly-upper-bound-induction-hint poly p))
          ("Subgoal *1/3"
           :use ((:instance
                  non-trivial-divide-polynomial-with-remainder-by-x+a
                            (poly poly)
                            (a (- (find-polynomial-root poly p))))
                 (:instance find-polynomial-root-not-nil-iff-num-roots-gt-0)
                 (:instance
                  num-roots-of-divide-polynomial-with-remainder-by-x+a
                  (a (find-polynomial-root poly p)))
                 (:instance non-trivial-polynomials-are-integer-polynomials)
                 (:instance len-divide-polynomial-with-remainder-by-x+a
                            (poly poly)
                            (a (- (find-polynomial-root poly p))))
                 (:instance find-polynomial-root-finds-root-if-not-nil)
                 ))
          ("Subgoal *1/1"
           :use ((:instance num-roots-of-linear-pfield-polynomial-upper-bound)))))

;;-----------------------------------------


(defun fermat-poly-aux (n)
  (if (zp n)
      nil
    (if (= n 1)
        (list 1)
      (cons 0 (fermat-poly-aux (1- n))))))


(defun fermat-poly (n)
  (cons (if (zp n) 0 -1)
        (fermat-poly-aux n)))

(defthm len-fermat-poly-aux
  (equal (len (fermat-poly-aux n))
         (nfix n))
  :hints (("Goal"
           :induct (fermat-poly-aux n)))
  )

(defthm len-fermat-poly
  (equal (len (fermat-poly n))
         (1+ (nfix n)))
  )

(defun x^k-1-polynomial-aux-p (poly)
  (if (consp poly)
      (if (consp (cdr poly))
          (and (= 0 (car poly))
               (x^k-1-polynomial-aux-p (cdr poly)))
        (equal poly (list 1)))
    nil))

(defun x^k-1-polynomial-p (poly)
  (and (= -1 (car poly))
       (x^k-1-polynomial-aux-p (cdr poly))))

(defthm fermat-poly-aux-is-x^k-1
  (implies (posp n)
           (x^k-1-polynomial-aux-p (fermat-poly-aux n))))

(defthm fermat-poly-is-x^k-1
  (implies (posp n)
           (x^k-1-polynomial-p (fermat-poly n))))

(defthm x^k-1-is-integer-polynomial
  (implies (x^k-1-polynomial-aux-p poly)
           (acl2::integer-polynomial-p poly)))

(defthm eval-polynomial-aux-x^k-1
  (implies (and (x^k-1-polynomial-aux-p poly)
                (integerp x))
           (equal (acl2::eval-polynomial poly x)
                  (expt x (1- (len poly))))))

(defthm eval-polynomial-x^k-1
  (implies (and (x^k-1-polynomial-p poly)
                (integerp x))
           (equal (acl2::eval-polynomial poly x)
                  (1- (expt x (1- (len poly)))))))

(defthmd eval-pfield-polynomial-x^k-1
  (implies (and (x^k-1-polynomial-p poly)
                (integerp x)
                (posp p))
           (equal (eval-pfield-polynomial poly x p)
                  (sub (pow x (1- (len poly)) p)
                       1
                       p)))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance eval-polynomial-x^k-1)
                 (:instance pow-rewrite
                            (a x)
                            (b (1- (len poly)))
                            (p p))
                 )
           :in-theory (e/d (eval-pfield-polynomial
                            add
                            neg
                            sub)
                           (acl2::eval-polynomial)))))
(defthm roots-of-x^k-1
  (implies (and (rtl::primep p)
                (x^k-1-polynomial-p poly)
                (equal (len poly) p)
                (fep x p)
                (not (= 0 x)))
           (pfield-polynomial-root-p poly x p))
  :rule-classes nil
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance eval-pfield-polynomial-x^k-1)
                 (:instance my-fermat-little
                            (a x)
                            (p p))
                 )
           :in-theory (e/d (pfield-polynomial-root-p
                            minus1)
                           (my-fermat-little)))))

(defthm num-roots-aux-of-x^k-1
  (implies (and (rtl::primep p)
                (x^k-1-polynomial-p poly)
                (equal (len poly) p)
                (fep x p))
           (equal (pfield-polynomial-num-roots-aux poly x p)
                  x))
  :rule-classes nil
  :hints (("Goal"
           :do-not-induct t
           :induct (pfield-polynomial-num-roots-aux poly x p)
           :in-theory (enable pfield-polynomial-num-roots-aux))
          ("Subgoal *1/3"
           :use ((:instance roots-of-x^k-1)))
          ))

(defthm num-roots-of-x^k-1
  (implies (and (rtl::primep p)
                (x^k-1-polynomial-p poly)
                (equal (len poly) p))
           (equal (pfield-polynomial-num-roots poly p)
                  (1- p)))
  :rule-classes nil
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance num-roots-aux-of-x^k-1
                            (p p)
                            (poly poly)
                            (x (1- p))))
           :in-theory (enable pfield-polynomial-num-roots))))

(defthm num-roots-of-fermat-poly
  (implies (rtl::primep p)
           (equal (pfield-polynomial-num-roots (fermat-poly (1- p)) p)
                  (1- p)))
  :rule-classes nil
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance num-roots-of-x^k-1
                            (p p)
                            (poly (fermat-poly (1- p)))))
           )))

(defun fermat-poly-aux-k-times (n k)
  (if (zp k)
      nil
    (append (fermat-poly-aux n)
            (fermat-poly-aux-k-times n (1- k)))))

(defun fermat-poly-aux-k-times+1 (n k)
  (cons 1 (fermat-poly-aux-k-times n k)))

(defthm len-fermat-poly-aux-k-times
  (equal (len (fermat-poly-aux-k-times n k))
         (* (nfix n) (nfix k))))

(defthm len-fermat-poly-aux-k-times+1
  (equal (len (fermat-poly-aux-k-times+1 n k))
         (1+ (* (nfix n) (nfix k)))))

(defthm scale-polynomial-append
  (equal (acl2::scale-polynomial (append poly1 poly2) c)
         (append (acl2::scale-polynomial poly1 c)
                 (acl2::scale-polynomial poly2 c))))

(defun n-zeros (n)
  (if (zp n)
      nil
    (cons 0 (n-zeros (1- n)))))

(defthm polynomial-+-scale-minus1
  (implies (acl2::integer-polynomial-p poly)
           (equal (acl2::polynomial-+ (acl2::scale-polynomial poly -1) poly)
                  (n-zeros (len poly)))))

(defthm polynomial-+-append
  (implies (and (acl2::integer-polynomial-p poly1)
                (acl2::integer-polynomial-p poly2)
                (acl2::integer-polynomial-p poly3)
                (acl2::integer-polynomial-p poly4)
                (equal (len poly1) (len poly3))
                )
           (equal (acl2::polynomial-+ (append poly1 poly2)
                                      (append poly3 poly4))
                  (append (acl2::polynomial-+ poly1 poly3)
                          (acl2::polynomial-+ poly2 poly4)))))


(defthm polynomial-+-append-scale-minus1
  (implies (and (acl2::integer-polynomial-p poly1)
                (acl2::integer-polynomial-p poly2))
           (equal (acl2::polynomial-+ (acl2::scale-polynomial poly1 -1)
                                      (append poly1 poly2))
                  (append (n-zeros (len poly1)) poly2))))



(defthm scale-poly-by-1
  (implies (acl2::integer-polynomial-p poly)
           (equal (acl2::scale-polynomial poly 1)
                  poly)))

(defthm scale-poly-by-0
  (implies (acl2::integer-polynomial-p poly)
           (equal (acl2::scale-polynomial poly 0)
                  (n-zeros (len poly)))))

(defthm add-poly-0
  (implies (acl2::integer-polynomial-p poly)
           (equal (acl2::polynomial-+ poly '(0))
                  (if (consp poly)
                      poly
                    '(0)))))

(defthm len-scale-polynomial
  (equal (len (acl2::scale-polynomial poly c))
         (len poly)))

(defthm len-polynomial-+
  (equal (len (acl2::polynomial-+ poly1 poly2))
         (max (len poly1) (len poly2))))

(defthm len-polynomial-*
  (equal (len (acl2::polynomial-* poly1 poly2))
         (if (consp poly1)
             (if (consp poly2)
                 (+ -1 (len poly1) (len poly2))
               (len poly1))
           0)))

(defun polynomial-+-n-zeros-arg1-induction-hint (poly n)
  (if (or (zp n) (endp poly))
      1
    (1+ (polynomial-+-n-zeros-arg1-induction-hint (cdr poly) (1- n)))))

(defthm append-polynomial-nil
  (implies (acl2::integer-polynomial-p poly)
           (equal (append poly nil) poly)))

(defthm polynomial-+-n-zeros-arg1
  (implies (and (natp n)
                (acl2::integer-polynomial-p poly))
           (equal (acl2::polynomial-+ (n-zeros n) poly)
                  (append poly (n-zeros (- n (len poly))))))
  :hints (("Goal"
           :do-not-induct t
           :induct (polynomial-+-n-zeros-arg1-induction-hint poly n))
          ("Subgoal *1/1"
           :in-theory (enable acl2::integer-polynomial-p)))
  )

(encapsulate
  nil

  (local
   (defthm lemma-1
     (implies (acl2::integer-polynomial-p poly)
              (equal (equal (len poly) 0)
                     (not (consp poly))))))

  (defthm polynomial-*-x^k-1-aux-arg1
    (implies (and (x^k-1-polynomial-aux-p poly1)
                  (acl2::integer-polynomial-p poly2)
                  (consp poly2)
                  )
             (equal (acl2::polynomial-* poly1 poly2)
                    (append (n-zeros (1- (len poly1)))
                            poly2)))
    :rule-classes nil
    :hints (("Goal"
             :do-not-induct t
             :induct (x^k-1-polynomial-aux-p poly1)
             )
            ("Subgoal *1/1"
             :use ((:instance lemma-1
                              (poly (cdr poly1)))))
            )
    )
  )

(defthm append-cons-arg2
  (equal (append xs (cons y ys))
         (append (append xs (list y)) ys))
  :rule-classes nil)

(defthmd fermat-poly-aux-into-n-zeros
  (implies (and (integerp n)
                (posp n))
           (equal (fermat-poly-aux n)
                  (append (n-zeros (- n 1)) (list 1))))
  :hints (("Goal"
           :induct (fermat-poly-aux n))))

(defthm integer-polynomial-fermat-poly-aux
  (acl2::integer-polynomial-p (fermat-poly-aux p)))

(defthm integer-polynomial-append
  (implies (and (acl2::integer-polynomial-p poly1)
                (acl2::integer-polynomial-p poly2))
           (acl2::integer-polynomial-p (append poly1 poly2))))

(defthm integer-polynomial-fermat-poly-aux-k-times
  (acl2::integer-polynomial-p (fermat-poly-aux-k-times p k)))

(defthm integer-polynomial-n-zeros
  (acl2::integer-polynomial-p (n-zeros n)))

(defthm polynomial-*-1-arg2
  (implies (acl2::integer-polynomial-p poly)
           (equal (acl2::polynomial-* poly '(1))
                  poly)))

(defthm len-n-zeros
  (equal (len (n-zeros n))
         (nfix n)))

(defthm len-append
  (equal (len (append x y))
         (+ (len x) (len y))))

(defthm consp-fermat-poly-aux
  (equal (consp (fermat-poly-aux n))
         (not (zp n))))

(defthm polynomial-*-x^k-1-aux-times-fermat-poly-aux-k-times
  (implies (and (integerp n)
                (posp n)
                (natp k))
           (equal (acl2::polynomial-* (fermat-poly-aux n)
                                      (fermat-poly-aux-k-times+1 n k))
                  (fermat-poly-aux-k-times n (1+ k))))
  :rule-classes nil
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance polynomial-*-x^k-1-aux-arg1
                            (poly1 (fermat-poly-aux n))
                            (poly2 (fermat-poly-aux-k-times+1 n k)))
                 (:instance append-cons-arg2
                            (xs (n-zeros (+ -1 n)))
                            (y 1)
                            (ys (fermat-poly-aux-k-times n k)))
                 (:instance fermat-poly-aux-into-n-zeros)
                 )
            ))

  )

(defthm append-associative
  (equal (append (append a b) c)
         (append a b c)))

(defthmd fermat-poly-aux-k-in-reverse-order
  (implies (natp k)
           (equal (append (fermat-poly-aux p)
                          (fermat-poly-aux-k-times p (1- k)))
                  (append (fermat-poly-aux-k-times p (1- k))
                          (fermat-poly-aux p))))
  :hints (("Goal"
           ;:do-not-induct t
           :induct (fermat-poly-aux-k-times p k))
           ))

(defthmd append-n-zeros-n-zeros
  (equal (append (n-zeros m) (n-zeros n))
         (n-zeros (+ (nfix m) (nfix n)))))

(encapsulate
  nil

  (local
   (defthm lemma-1
     (implies (and (posp n)
                   (posp k))
              (equal (append (n-zeros (+ (- n) (* k n)))
                             (fermat-poly-aux n))
                     (fermat-poly-aux (* k n))))
     :hints (("Goal"
              :do-not-induct t
              :use ((:instance fermat-poly-aux-into-n-zeros)
                    (:instance fermat-poly-aux-into-n-zeros
                               (n (* k n)))
                    (:instance append-n-zeros-n-zeros
                               (m (+ (- n) (* k n)))
                               (n (+ -1 n)))
                    )
              :in-theory (disable fermat-poly-aux)
              ))))


  (defthm polynomial-*-x^k-1-times-fermat-poly-aux-k-times
    (implies (and (posp n)
                  (posp k))
             (equal (acl2::polynomial-* (fermat-poly n)
                                        (fermat-poly-aux-k-times+1 n (1- k)))
                    (fermat-poly (* n k))))
    :rule-classes nil
    :hints (("Goal"
             :use ((:instance
                    polynomial-*-x^k-1-aux-times-fermat-poly-aux-k-times
                    (n n)
                    (k (1- k)))
                   )
             :in-theory (enable fermat-poly-aux-k-in-reverse-order)
             )))

  )

(defthm num-roots-fermat-poly-n*k
  (implies (and (posp n)
                (posp k)
                (rtl::primep p)
                (equal (* n k) (1- p)))
           (equal (pfield-polynomial-num-roots (fermat-poly (* n k)) p)
                  (* n k)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance num-roots-of-fermat-poly)))))

(defthm num-roots-fermat-poly-product
  (implies (and (posp n)
                (posp k)
                (rtl::primep p)
                (equal (* n k) (1- p)))
           (<= (* n k)
               (+ (pfield-polynomial-num-roots (fermat-poly n) p)
                  (pfield-polynomial-num-roots (fermat-poly-aux-k-times+1 n (1- k)) p))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance polynomial-*-x^k-1-times-fermat-poly-aux-k-times)
                 (:instance num-roots-fermat-poly-n*k)
                 (:instance pfield-polynbomial-num-roots-of-product
                            (poly1 (fermat-poly n))
                            (poly2 (fermat-poly-aux-k-times+1 n (1- k)))
                            (p p))))))


(defthm car-last-fermat-poly-aux
  (implies (posp n)
           (equal (car (last (fermat-poly-aux n))) 1)))

(defthmd non-trivial-polynomial-fermat-poly
  (implies (and (posp n)
                (posp p)
                (<= 2 p))
           (non-trivial-pfield-polynomial-p (fermat-poly n) p))
  :hints (("Goal"
           :in-theory (enable non-trivial-pfield-polynomial-p)))
  )

(defthm num-roots-fermat-poly-upper-bound
  (implies (and (rtl::primep p)
                (posp n))
           (<= (pfield-polynomial-num-roots (fermat-poly n) p)
               n))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance num-roots-of-poly-upper-bound
                            (poly (fermat-poly n))
                            (p p))
                 (:instance non-trivial-polynomial-fermat-poly)))))

(defthm last-fermat-poly-aux
  (implies (posp n)
           (equal (last (fermat-poly-aux n)) (list 1))))

(defthm last-fermat-poly
  (implies (posp n)
           (equal (last (fermat-poly n)) (list 1))))

(defthm last-fermat-poly-aux-k-times
  (implies (and (posp n)
                (posp k))
           (equal (last (fermat-poly-aux-k-times n k)) (list 1))))

(defthm last-fermat-poly-aux-k-times+1
  (implies (and (posp n)
                (posp k))
           (equal (last (fermat-poly-aux-k-times+1 n k)) (list 1))))

(defthm non-trivial-last-fermat-poly-aux-k-times+1
  (implies (and (posp n)
                (posp k)
                (posp p)
                (<= 2 p))
           (non-trivial-pfield-polynomial-p
            (fermat-poly-aux-k-times+1 n k)
            p))
  :hints (("Goal"
           :in-theory (enable non-trivial-pfield-polynomial-p)))
  )

(encapsulate
  nil

  (local
   (defthmd lemma-1
     (implies (and (posp n))
              (<= (1+ n) (+ n n)))))

  (local
   (defthmd lemma-2
     (implies (and (posp n)
                   (posp k)
                   (<= 2 k))
              (<= (1+ n) (* k n)))
     :hints (("Goal"
              :use ((:instance
                     (:theorem (implies (and (<= a b) (<= b c)) (<= a c)))
                     (a (1+ n))
                     (b (* 2 n))
                     (c (* k n)))
                    (:instance lemma-1))))))

  (defthm num-roots-fermat-poly-aux-k-times+1-upper-bound
    (implies (and (rtl::primep p)
                  (posp k)
                  (<= 2 k)
                  (posp n))
             (<= (pfield-polynomial-num-roots
                  (fermat-poly-aux-k-times+1 n (1- k))
                  p)
                 (* n (1- k))))
    :rule-classes nil
    :hints (("Goal"
             :use ((:instance num-roots-of-poly-upper-bound
                              (poly (fermat-poly-aux-k-times+1 n (1- k)))
                              (p p))
                   (:instance non-trivial-polynomial-fermat-poly)
                   (:instance non-trivial-last-fermat-poly-aux-k-times+1
                              (n n)
                              (k (1- k))
                              (p p))
                   (:instance lemma-2)
                   ))))
  )

(defthm num-roots-fermat-poly-divisor-part1
  (implies (and (posp n)
                (posp k)
                (<= 2 k)
                (rtl::primep p)
                (equal (* n k) (1- p)))
           (equal (pfield-polynomial-num-roots (fermat-poly n) p) n))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance num-roots-fermat-poly-product)
                 (:instance num-roots-fermat-poly-upper-bound)
                 (:instance num-roots-fermat-poly-aux-k-times+1-upper-bound)))))

(defthm num-roots-fermat-poly-divisor-part2
  (implies (and (posp n)
                (posp k)
                (= 1 k)
                (rtl::primep p)
                (equal (* n k) (1- p)))
           (equal (pfield-polynomial-num-roots (fermat-poly n) p) n))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance num-roots-of-fermat-poly)))))

(defthm num-roots-fermat-poly-divisor
  (implies (and (posp n)
                (posp k)
                (rtl::primep p)
                (equal (* n k) (1- p)))
           (equal (pfield-polynomial-num-roots (fermat-poly n) p) n))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance num-roots-fermat-poly-divisor-part1)
                 (:instance num-roots-fermat-poly-divisor-part2)))))

(defthm num-roots-fermat-poly-divisor-implicit
  (implies (and (posp n)
                (rtl::primep p)
                (rtl::divides n (1- p)))
           (equal (pfield-polynomial-num-roots (fermat-poly n) p) n))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance num-roots-fermat-poly-divisor
                            (n n)
                            (k (/ (1- p) n))
                            (p p)))
           :in-theory (enable rtl::divides)
           )))
