(in-package "RTL")

(include-book "reduce")

;; [Jared] These rules were causing some proofs to be really slow.

(local (deftheory jared-disables
         #!acl2
         '((:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE)
           (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE)
           (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A)
           (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B)
           (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT)
           (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT)
           (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT)
           (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT)
           (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-RATIONALP-BASE)
           (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-0-BASE)
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3B)
           (:TYPE-PRESCRIPTION NOT-INTEGERP-1B)
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2B)
           (:TYPE-PRESCRIPTION NOT-INTEGERP-4E)
           (:TYPE-PRESCRIPTION NOT-INTEGERP-4B)
           (:TYPE-PRESCRIPTION NOT-INTEGERP-4B-EXPT)
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT)
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT)
           (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT)
           (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION)
           not-integerp-1a-expt
           not-integerp-2a-expt
           not-integerp-3a-expt
           not-integerp-4a-expt
           not-integerp-1d-expt
           not-integerp-2d-expt
           not-integerp-3d-expt
           not-integerp-4d-expt
           not-integerp-1a
           not-integerp-2a
           not-integerp-3a
           not-integerp-4a
           not-integerp-1d
           not-integerp-2d
           not-integerp-3d
           not-integerp-4d
           not-integerp-1f
           not-integerp-2f
           not-integerp-3f
           not-integerp-4f
           default-plus-1
           default-plus-2
           default-times-1
           default-times-2
           default-less-than-1
           default-less-than-2
           default-expt-2
           default-expt-1
           default-minus
           default-mod-ratio
           mod-zero
           |(mod (if a b c) x)|
           rtl::mod-bnd-1
           rtl::mod-bnd-2
           (:type-prescription rtl::natp-dx)
           rtl::mod-does-nothing
           )))

(local (in-theory (disable jared-disables)))

(defund tripp$ (x)
  (and (true-listp x)
       (= (len x) 3)
       (polyp$ (car x))
       (polyp$ (cadr x))
       (polyp$ (caddr x))
       (not (= (mod (evalp$ (caddr x)) (p)) 0))))

(defun eval3$ (p)
  (list (evalp$ (car p))
        (evalp$ (cadr p))
        (evalp$ (caddr p))))

(defun decode3$ (p)
  (decode3 (eval3$ p)))

(defthm integerp-evalp$
  (implies (polyp$ x)
           (integerp (evalp$ x)))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :use ((:instance integerp-evalp (vals (vals)) (vars (vars))))
                  :in-theory (enable vlist))))

(in-theory (disable polyp$ evalp$ (eval3$) (decode3$)))

(defthm tripp$tripp
  (implies (tripp$ x)
           (tripp (eval3$ x)))
  :hints (("Goal" :in-theory (enable tripp tripp$))))

(defund p0$ () (list 'x0 'y0 1))
(defund p1$ () (list 'x1 'y1 1))
(defund p2$ () (list 'x2 'y2 1))

(defthm decode3$p$
  (and (equal (decode3$ (p0$)) (p0))
       (equal (decode3$ (p1$)) (p1))
       (equal (decode3$ (p2$)) (p2)))
  :hints (("Goal" :use (ecp-assumption)
                  :in-theory (enable ecp vals dx dy vlist decode3 evalp$))))
  
;; Inverse:

(defun neg$ (p)
  (list (car p) (list '- (cadr p)) (caddr p)))

;; Doubling:

(defun zdbl$ (p)
  (let ((v (cadr p))
        (z (caddr p)))
    `(* 2 (* ,v ,z))))

(defun wdbl$ (p)
  (let ((u (car p))
        (z (caddr p)))
    `(+ (* 3 (expt ,u 2))
        (+ (* 2 (* ,(a) (* ,u (expt ,z 2))))
           (expt ,z 4)))))

(defun udbl$ (p)
  (let ((u (car p))
        (v (cadr p))
        (z (caddr p)))
    `(- (expt ,(wdbl$ p) 2)
        (* 4
           (* (expt ,v 2)
              (+ (* ,(a) (expt ,z 2))
                 (* 2 ,u)))))))

(defun vdbl$ (p)
  (let ((u (car p))
        (v (cadr p)))
    `(- (* ,(wdbl$ p)
           (- (* 4 (* ,u (expt ,v 2)))
              ,(udbl$ p)))
        (* 8 (expt ,v 4)))))

(defun dbl$ (p)
  (list (udbl$ p)
        (vdbl$ p)
        (zdbl$ p)))

;; Addition of distinct points:

(defun zsum$ (p1 p2)
  (let ((u (car p2))
        (z (caddr p2))
        (x (car p1)))
    `(* ,z
        (- (* ,x (expt ,z 2))
           ,u))))

(defun usum$ (p1 p2)
  (let ((u (car p2))
        (v (cadr p2))
        (z (caddr p2))
        (x (car p1))
        (y (cadr p1)))
    `(- (expt (- (* (expt ,z 3) ,y)
                 ,v)
              2)
        (* (+ (* (expt ,z 2) (+ ,(a) ,x))
              ,u)
           (expt (- (* (expt ,z 2) ,x)
                    ,u)
                 2)))))

(defun vsum$ (p1 p2)
  (let ((v (cadr p2))
        (z (caddr p2))
        (x (car p1))
        (y (cadr p1)))
    `(- (* (- (* (expt ,z 3) ,y)
              ,v)
           (- (* (expt ,(zsum$ p1 p2) 2) ,x)
              ,(usum$ p1 p2)))
        (* (expt ,(zsum$ p1 p2) 3)
           ,y))))

(defun sum$ (p1 p2)
  (list (usum$ p1 p2)
        (vsum$ p1 p2)
        (zsum$ p1 p2)))

(local-defthm car-cons-open
  (equal (car (cons x y)) x))

(local-defthm cdr-cons-open
  (equal (cdr (cons x y)) y))

(local (deftheory theory$
  (union-theories '(car-cons-open cdr-cons-open eval3$ evalp$ evalp a wdbl wdbl$ 
                    vdbl vdbl$ udbl udbl$ zdbl zdbl$ vsum vsum$ usum usum$ zsum zsum$)
                  (theory 'minimal-theory))))

(defthm zdbl$-rewrite
  (equal (evalp$ (zdbl$ p))
         (zdbl (eval3$ p)))
  :hints (("Goal" :in-theory (theory 'theory$))))

(defthm udbl$-rewrite
  (equal (evalp$ (udbl$ p))
         (udbl (eval3$ p)))
  :hints (("Goal" :in-theory (theory 'theory$))))

(defthm vdbl$-rewrite
  (equal (evalp$ (vdbl$ p))
         (vdbl (eval3$ p)))
  :hints (("Goal" :in-theory (theory 'theory$))))
                   
(defthm zsum$-rewrite
  (equal (evalp$ (zsum$ p1 p2))
         (zsum (eval3$ p1) (eval3$ p2)))
  :hints (("Goal" :in-theory (theory 'theory$))))

(defthm usum$-rewrite
  (equal (evalp$ (usum$ p1 p2))
         (usum (eval3$ p1) (eval3$ p2)))
  :hints (("Goal" :in-theory (theory 'theory$))))

(defthm vsum$-rewrite
  (equal (evalp$ (vsum$ p1 p2))
         (vsum (eval3$ p1) (eval3$ p2)))
  :hints (("Goal" :in-theory (theory 'theory$))))

(in-theory (disable zdbl$ udbl$ vdbl$ zsum$ usum$ vsum$)) 

(in-theory (disable decode3))

(local-defthm tripp$-dbl$-1
  (implies (and (tripp$ p)
                (not (= (mod (evalp$ (cadr p)) (p)) 0)))
           (not (= (mod (evalp$ (zdbl$ p)) (p)) 0)))
  :hints (("Goal" :in-theory (enable tripp$ zdbl)
                  :use ((:instance mod*0 (m (* 2 (evalp$ (cadr p)))) (n (evalp$ (caddr p))))
                        (:instance mod*0 (m 2) (n (evalp$ (cadr p))))))))

(local-defthm tripp$-dbl$-2
  (implies (and (tripp$ p)
                (not (= (mod (evalp$ (cadr p)) (p)) 0)))
           (and (polyp$ (udbl$ p))
                (polyp$ (vdbl$ p))
                (polyp$ (zdbl$ p))))
  :hints (("Goal" :in-theory (enable polyp$ tripp$ zdbl$ udbl$ vdbl$))))

(local-defthm tripp$-dbl$-3
  (implies (and (tripp$ p)
                (not (= (mod (evalp$ (cadr p)) (p)) 0)))
           (tripp$ (dbl$ p)))
  :hints (("Goal" :in-theory (enable tripp$ dbl)
                  :use (tripp$-dbl$-1 tripp$-dbl$-2))))

(local-defthmd tripp$-dbl$-4
  (implies (and (tripp$ p)
                (= (mod (evalp$ (cadr p)) (p)) 0))
           (= (y (decode3$ p)) 0))
  :hints (("goal" :in-theory (enable eval3$ dy decode3$ decode3 tripp$)
                  :use ((:instance mod*rewrite-1 (a (evalp$ (cadr p)))
                                                 (b (frcp (expt (evalp$ (caddr p)) 3))))))))
(local-defthmd tripp$-dbl$-5
  (implies (and (tripp$ p)
                (ecp (decode3$ p))
                (not (equal (y (decode3$ p)) 0)))
           (tripp$ (dbl$ p)))
  :hints (("Goal" :in-theory (enable tripp$)
                  :use (tripp$-dbl$-3 tripp$-dbl$-4
                        (:instance ec-x-0 (x (x (decode3$ p))))))))

(local-defthm tripp$-dbl$-6
  (implies (and (ecp p) (= (y p) 0))
           (= p (o)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance ec-x-0 (x (x p)))))))

(defthmd tripp$-dbl$
  (implies (and (tripp$ p)
                (ecp (decode3$ p))
                (not (equal (decode3$ p) (o))))
           (tripp$ (dbl$ p)))
  :hints (("Goal" :in-theory (enable tripp$)
                  :use (tripp$-dbl$-5
                        (:instance tripp$-dbl$-6 (p (decode3$ p)))))))

(local-defthmd dbl$-dbl
  (implies (tripp$ p)
           (equal (decode3$ (dbl$ p))
                  (decode3 (dbl (eval3$ p)))))
  :hints (("Goal" :in-theory (enable dbl))))

(local-defthm eval3$cadr
  (equal (cadr (eval3$ p))
         (evalp$ (cadr p)))
  :hints (("Goal" :in-theory (enable evalh$))))

(local-defthmd dbl$-formula-1
  (implies (and (tripp$ p)
                (not (= (mod (evalp$ (cadr p)) (p)) 0)))
           (equal (decode3$ (dbl$ p))
                  (ec+ (decode3$ p) (decode3$ p))))
  :hints (("Goal" :in-theory '(eval3$ decode3$ evalp$)
                  :use (dbl$-dbl
                        eval3$cadr
                        (:instance tripp$tripp (x p))
                        (:instance dbl-formula (p (eval3$ p)))))))

(local-defthmd dbl$-formula-2
  (implies (and (tripp$ p)
                (= (mod (evalp$ (cadr p)) (p)) 0))
           (= (y (decode3$ p)) 0))
  :hints (("goal" :in-theory (enable eval3$ dy decode3$ decode3 tripp$)
                  :use ((:instance mod*rewrite-1 (a (evalp$ (cadr p)))
                                                 (b (frcp (expt (evalp$ (caddr p)) 3))))))))

(local-defthmd dbl$-formula-3
  (implies (and (tripp$ p)
                (ecp (decode3$ p))
                (not (equal (y (decode3$ p)) 0)))
           (equal (decode3$ (dbl$ p))
                  (ec+ (decode3$ p) (decode3$ p))))
  :hints (("Goal" :in-theory (enable tripp$)
                  :use (dbl$-formula-1 dbl$-formula-2
                        (:instance ec-x-0 (x (x (decode3$ p))))))))

(local-defthm dbl$-formula-4
  (implies (and (ecp p) (= (y p) 0))
           (= p (o)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance ec-x-0 (x (x p)))))))

(defthmd dbl$-formula
  (implies (and (tripp$ p)
                (ecp (decode3$ p))
                (not (equal (decode3$ p) (o))))
           (equal (decode3$ (dbl$ p))
                  (ec+ (decode3$ p) (decode3$ p))))
  :hints (("Goal" :in-theory (enable tripp$)
                  :use (dbl$-formula-3
                        (:instance dbl$-formula-4 (p (decode3$ p)))))))

(local-defthmd sum$-sum
  (implies (and (tripp$ p1)
                (tripp$ p2))
           (equal (decode3$ (sum$ p1 p2))
                  (decode3 (sum (eval3$ p1) (eval3$ p2)))))
  :hints (("Goal" :in-theory (enable sum))))

(local-defthm decode3$dx
  (equal (x (decode3$ p))
         (dx (eval3$ p)))
  :hints (("Goal" :in-theory (enable decode3))))

(local-defthm caddr-decode3$
  (implies (equal (caddr p) 1)
           (equal (caddr (eval3$ p)) 1))
  :hints (("Goal" :in-theory (enable evalp$)))) 

(local-defthmd tripp$-sum$-1
  (implies (and (tripp$ p1)
                (tripp$ p2)
                (not (= (x (decode3$ p1)) (x (decode3$ p2))))
                (= (caddr p1) 1))
           (not (= (mod (evalp$ (car p1)) (p))
                   (mod (* (evalp$ (car p2)) (frcp (expt (evalp$ (caddr p2)) 2))) (p)))))
  :hints (("Goal" :expand ((EVALP$ 1)) :in-theory (enable decode3 dx tripp$))))

(local-defthmd tripp$-sum$-2
  (implies (and (tripp$ p1)
                (tripp$ p2)
                (not (= (x (decode3$ p1)) (x (decode3$ p2))))
                (= (caddr p1) 1))
           (= (mod (evalp$ (car p1)) (p))
              (mod (* (evalp$ (car p1)) (frcp (expt (evalp$ (caddr p2)) 2)) (expt (evalp$ (caddr p2)) 2)) (p))))
  :hints (("Goal" :in-theory (enable tripp$)
                  :use ((:instance mod-expt-0 (p (p)) (n (evalp$ (caddr p2))) (k 2))
                        (:instance frcp-cor (m (evalp$ (car p1))) (n (expt (evalp$ (caddr p2)) 2)))))))

(local-defthmd tripp$-sum$-3
  (implies (and (tripp$ p1)
                (tripp$ p2)
                (not (= (x (decode3$ p1)) (x (decode3$ p2))))
                (= (caddr p1) 1))
           (not (= (mod (* (evalp$ (car p1)) (frcp (expt (evalp$ (caddr p2)) 2)) (expt (evalp$ (caddr p2)) 2)) (p))
                   (mod (* (evalp$ (car p2)) (frcp (expt (evalp$ (caddr p2)) 2))) (p)))))
  :hints (("Goal" :use (tripp$-sum$-1 tripp$-sum$-2))))

(local-defthmd tripp$-sum$-4
  (implies (and (tripp$ p1)
                (tripp$ p2)
                (not (= (x (decode3$ p1)) (x (decode3$ p2))))
                (= (caddr p1) 1))
           (not (= (mod (* (evalp$ (car p1)) (expt (evalp$ (caddr p2)) 2)) (p))
                   (mod (evalp$ (car p2)) (p)))))
  :hints (("Goal" :use (tripp$-sum$-3
                        (:instance mod-times-mod (a (evalp$ (car p2)))
                                                 (b (* (evalp$ (car p1)) (expt (evalp$ (caddr p2)) 2)))
                                                 (c (frcp (expt (evalp$ (caddr p2)) 2)))
                                                 (n (p))))
                  :in-theory (enable tripp$))))

(local-defthmd tripp$-sum$-5
  (implies (and (tripp$ p1)
                (tripp$ p2)
                (not (= (x (decode3$ p1)) (x (decode3$ p2))))
                (= (caddr p1) 1))
           (not (= (mod (- (* (evalp$ (car p1)) (expt (evalp$ (caddr p2)) 2))
                           (evalp$ (car p2)))
                        (p))
                   0)))
  :hints (("Goal" :use (tripp$-sum$-4
                        (:instance mod-equal-0 (a (* (evalp$ (car p1)) (expt (evalp$ (caddr p2)) 2)))
                                               (b (evalp$ (car p2)))
                                               (n (p)))) 
                  :in-theory (enable tripp$))))

(local-defthm tripp$-sum$-6
  (implies (and (tripp$ p1)
                (tripp$ p2)
                (not (= (x (decode3$ p1)) (x (decode3$ p2))))
                (= (caddr p1) 1))
           (not (= (mod (evalp$ (zsum$ p1 p2)) (p)) 0)))
  :hints (("Goal" :in-theory (enable tripp$ zsum)
                  :use (tripp$-sum$-5
                        (:instance mod*0 (m (- (* (evalp$ (car p1)) (expt (evalp$ (caddr p2)) 2))
                                               (evalp$ (car p2))))
                                         (n (evalp$ (caddr p2))))))))

(local-defthm tripp$-sum$-7
  (implies (and (tripp$ p1)
                (tripp$ p2)
                (not (= (x (decode3$ p1)) (x (decode3$ p2))))
                (= (caddr p1) 1))
           (and (polyp$ (usum$ p1 p2))
                (polyp$ (vsum$ p1 p2))
                (polyp$ (zsum$ p1 p2))))
  :hints (("Goal" :in-theory (enable polyp$ tripp$ zsum$ usum$ vsum$))))

(defthm tripp$-sum$
  (implies (and (tripp$ p1)
                (tripp$ p2)
                (not (= (x (decode3$ p1)) (x (decode3$ p2))))
                (= (caddr p1) 1))
           (tripp$ (sum$ p1 p2)))
  :hints (("Goal" :in-theory (enable tripp$ sum)
                  :use (tripp$-sum$-6 tripp$-sum$-7))))

(defthmd sum$-formula
  (implies (and (tripp$ p1)
                (tripp$ p2)
                (not (= (x (decode3$ p1)) (x (decode3$ p2))))
                (= (caddr p1) 1))
           (equal (decode3$ (sum$ p1 p2))
                  (ec+ (decode3$ p1) (decode3$ p2))))
  :hints (("Goal" :in-theory '(eval3$ decode3$ evalp$)
                  :use (sum$-sum
                        eval3$cadr
                        (:instance caddr-decode3$ (p p1))
                        (:instance decode3$dx (p p1))
                        (:instance decode3$dx (p p2))
                        (:instance tripp$tripp (x p1))
                        (:instance tripp$tripp (x p2))
                        (:instance sum-formula (p1 (eval3$ p1)) (p2 (eval3$ p2)))))))

(defun ecp$-term (p)
  (let* ((u (car p))
         (v (cadr p))
         (z (caddr p)))
    `(- (expt ,v 2)
        (+ (expt ,u 3)
           (+ (* ,(a) (expt (* ,u ,z) 2))
              (* ,u (expt ,z 4)))))))

(defun ecp-term (p)
  (let* ((u (car p))
         (v (cadr p))
         (z (caddr p)))
    (- (expt v 2)
       (+ (expt u 3)
          (+ (* (a) (expt (* u z) 2))
             (* u (expt z 4)))))))

(local-defthm ecp$-term-rewrite
  (equal (evalp$ (ecp$-term p))
         (ecp-term (eval3$ p)))
  :hints (("Goal" :expand ((ecp$-term p) (:free (p) (ecp-term p)))
                  :in-theory (theory 'theory$))))

(local-defthm polyp$-ecp$-term
  (implies (tripp$ p)
           (polyp$ (ecp$-term p)))
  :hints (("Goal" :in-theory (enable polyp$)
                  :expand ((tripp$ p) (ecp$-term p)))))
 
(defun ecp$ (p)
  (equal (reduce$ (ecp$-term p))
         0))

(in-theory (disable ecp$-term ecp-term reduce$))

(local-defthm ecp$ecp-term 
  (implies (and (tripp$ p)
                (ecp$ p))
           (equal (mod (ecp-term (eval3$ p)) (p))
                  0))
  :hints (("Goal" :use ((:instance reduce$-correct (x (ecp$-term p)))))))

(local-defthm integerp-ecp-term
  (implies (tripp$ p)
           (integerp (ecp-term (eval3$ p))))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :expand ((:free (p) (ecp-term p)))
                  :in-theory (enable tripp$ eval3$))))

(local-defthm ecp-term-frcp 
  (implies (and (tripp$ p)
                (ecp$ p))
           (equal (mod (* (ecp-term (eval3$ p)) (expt (frcp (evalp$ (caddr p))) 6)) (p))
                  0))
  :hints (("Goal" :in-theory (e/d (tripp$) (ACL2::MOD-THEOREM-ONE-B mod*rewrite-1 mod*rewrite-2))
                  :use (integerp-ecp-term 
                        ecp$ecp-term 
                        (:instance mod*rewrite-1 (a (ecp-term (eval3$ p))) (b (expt (frcp (evalp$ (caddr p))) 6)))))))

(defund ecp-term-1 (p)
  (expt (cadr p) 2))

(defund ecp-term-2 (p)
  (let ((u (car p))
        (z (caddr p)))
    (+ (expt u 3)
       (+ (* (a) (expt (* u z) 2))
          (* u (expt z 4))))))

(local-defthm ecp-term-frcp-2 
  (implies (tripp$ p)
           (equal (* (ecp-term (eval3$ p)) (expt (frcp (evalp$ (caddr p))) 6))
                  (- (* (ecp-term-1 (eval3$ p)) (expt (frcp (evalp$ (caddr p))) 6))
                     (* (ecp-term-2 (eval3$ p)) (expt (frcp (evalp$ (caddr p))) 6)))))
  :hints (("Goal" :in-theory (enable tripp$ ecp-term ecp-term-1 ecp-term-2)
                  :use (integerp-ecp-term))))

(local-defthm ecp-term-frcp-3 
  (implies (and (tripp$ p)
                (ecp$ p))
           (equal (mod (- (* (ecp-term-1 (eval3$ p)) (expt (frcp (evalp$ (caddr p))) 6))
                          (* (ecp-term-2 (eval3$ p)) (expt (frcp (evalp$ (caddr p))) 6)))
                       (p))
                  0))
  :hints (("Goal" :use (ecp-term-frcp ecp-term-frcp-2)
                  :in-theory (theory 'minimal-theory))))

(local-defthm ecp-term-frcp-4 
  (implies (tripp$ p)
           (and (integerp (* (ecp-term-1 (eval3$ p)) (expt (frcp (evalp$ (caddr p))) 6)))
                (integerp (* (ecp-term-2 (eval3$ p)) (expt (frcp (evalp$ (caddr p))) 6)))))
  :hints (("Goal" :in-theory (enable tripp$ ecp-term-1 ecp-term-2))))

(local-defthmd ecp-term-frcp-5
  (implies (and (integerp a) (integerp b) (= (mod (- a b) (p)) 0))
           (equal (mod a (p)) (mod b (p))))
  :hints (("Goal" :use ((:instance mod-equal-0 (n (p)))))))

(local-defthmd ecp-term-frcp-6
  (implies (and (tripp$ p)
                (ecp$ p))
           (equal (mod (* (ecp-term-1 (eval3$ p)) (expt (frcp (evalp$ (caddr p))) 6)) (p))
                  (mod (* (ecp-term-2 (eval3$ p)) (expt (frcp (evalp$ (caddr p))) 6)) (p))))
  :hints (("Goal" :use (ecp-term-frcp-3 ecp-term-frcp-4
                        (:instance ecp-term-frcp-5 (a (* (ecp-term-1 (eval3$ p)) (expt (frcp (evalp$ (caddr p))) 6)))
                                                  (b (* (ecp-term-2 (eval3$ p)) (expt (frcp (evalp$ (caddr p))) 6)))))
                  :in-theory (theory 'minimal-theory))))

(local-defthmd ecp-term-frcp-7
  (implies (tripp$ p)
           (equal (mod (* (ecp-term-1 (eval3$ p)) (expt (frcp (evalp$ (caddr p))) 6)) (p))
                  (fexpt (dy (eval3$ p)) 2)))
  :hints (("Goal" :in-theory (enable frcp-expt dy tripp$ ecp-term-1))))

(local-defthmd ecp-term-frcp-8
  (implies (tripp$ p)
           (equal (mod (* (ecp-term-2 (eval3$ p)) (expt (frcp (evalp$ (caddr p))) 6)) (p))
                  (mod (+ (* (expt (evalp$ (car p)) 3)
                             (expt (frcp (evalp$ (caddr p))) 6))
                          (mod (* (evalp$ (car p))
                                  (expt (evalp$ (caddr p)) 4)
                                  (expt (frcp (evalp$ (caddr p))) 6))
                               (p))
                          (mod (* 486662 (expt (evalp$ (car p)) 2)
                                  (expt (evalp$ (caddr p)) 2)
                                  (expt (frcp (evalp$ (caddr p))) 6))
                               (p)))
                       (p))))
  :hints (("goal" :in-theory (enable frcp-expt dx tripp$ ecp-term-2))))

(local-defthmd ecp-term-frcp-9
  (implies (tripp$ p)
           (and (equal (mod (* (evalp$ (car p))
                               (expt (evalp$ (caddr p)) 4)
                               (expt (frcp (evalp$ (caddr p))) 6))
                            (p))
                       (mod (* (evalp$ (car p))
                               (expt (frcp (evalp$ (caddr p))) 2))
                            (p)))
                (equal (mod (* 486662 (expt (evalp$ (car p)) 2)
                               (expt (evalp$ (caddr p)) 2)
                               (expt (frcp (evalp$ (caddr p))) 6))
                            (p))
                       (mod (* 486662 (expt (evalp$ (car p)) 2)
                               (expt (frcp (evalp$ (caddr p))) 4))
                            (p)))))
  :hints (("goal" :in-theory (enable frcp-expt tripp$)
                  :use ((:instance mod-expt-0 (p (p)) (n (evalp$ (caddr p))) (k 2)) 
                        (:instance mod-expt-0 (p (p)) (n (evalp$ (caddr p))) (k 4))
                        (:instance frcp-cor (m (* (evalp$ (car p)) (expt (frcp (evalp$ (caddr p))) 2)))
                                           (n (expt (evalp$ (caddr p)) 4)))
                        (:instance frcp-cor (m (* 486662 (expt (evalp$ (car p)) 2) (expt (frcp (evalp$ (caddr p))) 4)))
                                           (n (expt (evalp$ (caddr p)) 2)))))))

(local-defthmd ecp-term-frcp-10
  (implies (tripp$ p)
           (equal (mod (* (ecp-term-2 (eval3$ p)) (expt (frcp (evalp$ (caddr p))) 6)) (p))
                  (mod (+ (* (expt (evalp$ (car p)) 3)
                             (expt (frcp (evalp$ (caddr p))) 6))
                          (mod (* (evalp$ (car p))
                                  (expt (frcp (evalp$ (caddr p))) 2))
                               (p))
                          (mod (* 486662 (expt (evalp$ (car p)) 2)
                                  (expt (frcp (evalp$ (caddr p))) 4))
                               (p)))
                       (p))))
  :hints (("goal" :in-theory (theory 'minimal-theory)
                  :use (ecp-term-frcp-8 ecp-term-frcp-9))))

(local-defthmd ecp-term-frcp-11
  (implies (tripp$ p)
           (equal (mod (* (ecp-term-2 (eval3$ p)) (expt (frcp (evalp$ (caddr p))) 6)) (p))
                  (mod (+ (* (expt (evalp$ (car p)) 3)
                             (expt (frcp (evalp$ (caddr p))) 6))
                          (* (evalp$ (car p)) (expt (frcp (evalp$ (caddr p))) 2))
                          (* 486662 (expt (evalp$ (car p)) 2) (expt (frcp (evalp$ (caddr p))) 4)))
                       (p))))
  :hints (("goal" :use (ecp-term-frcp-10)
                  :in-theory (enable tripp$))))

(local-defthmd ecp-term-frcp-12
  (implies (tripp$ p)
           (equal (mod (* (ecp-term-2 (eval3$ p)) (expt (frcp (evalp$ (caddr p))) 6)) (p))
                  (f+ (f+ (fexpt (dx (eval3$ p)) 3) 
                          (f* (a) (fexpt (dx (eval3$ p)) 2)))
                      (dx (eval3$ p)))))
  :hints (("Goal" :use (ecp-term-frcp-11)
           :in-theory (e/d (frcp-expt dx tripp$)
                           (jared-disables)))))

(local-defthmd ecp-term-frcp-13
  (implies (and (tripp$ p)
                (ecp$ p))
           (equal (fexpt (dy (eval3$ p)) 2)
                  (f+ (f+ (fexpt (dx (eval3$ p)) 3) 
                          (f* (a) (fexpt (dx (eval3$ p)) 2)))
                      (dx (eval3$ p)))))
  :hints (("Goal" :use (ecp-term-frcp-6 ecp-term-frcp-7 ecp-term-frcp-12) :in-theory (theory 'minimal-theory))))

(local-defthmd ecp-term-frcp-14
  (implies (tripp$ p)
           (and (fp (dx (eval3$ p)))
                (fp (dy (eval3$ p)))))  
  :hints (("Goal" :in-theory (enable dx dy tripp$))))

(defthmd ecp$ecp 
  (implies (and (tripp$ p)
                (ecp$ p))
           (ecp (decode3$ p)))
  :hints (("Goal" :use (ecp-term-frcp-13 ecp-term-frcp-14)
                  :in-theory (enable ecp decode3 decode3$))))

(defun eq$ (p1 p2)
  (let ((u1 (car p1))
        (v1 (cadr p1))
        (z1 (caddr p1))
        (u2 (car p2))
        (v2 (cadr p2))
        (z2 (caddr p2)))
    (and (equal (reduce$ `(* ,u1 (expt ,z2 2)))
                (reduce$ `(* ,u2 (expt ,z1 2))))
         (equal (reduce$ `(* ,v1 (expt ,z2 3)))
                (reduce$ `(* ,v2 (expt ,z1 3)))))))

(local-defthmd eq$-term-rewrite
  (and (equal (evalp$ `(* ,(car p1) (expt ,(caddr p2) 2)))
              (* (evalp$ (car p1)) (expt (evalp$ (caddr p2)) 2)))
       (equal (evalp$ `(* ,(car p2) (expt ,(caddr p1) 2)))
              (* (evalp$ (car p2)) (expt (evalp$ (caddr p1)) 2)))
       (equal (evalp$ `(* ,(cadr p1) (expt ,(caddr p2) 3)))
              (* (evalp$ (cadr p1)) (expt (evalp$ (caddr p2)) 3)))
       (equal (evalp$ `(* ,(cadr p2) (expt ,(caddr p1) 3)))
              (* (evalp$ (cadr p2)) (expt (evalp$ (caddr p1)) 3))))
  :hints (("Goal" :in-theory (theory 'theory$))))

(local-defthmd eq$-term-polyp
  (implies (and (tripp$ p1)
                (tripp$ p2))
           (and (polyp$ `(* ,(car p1) (expt ,(caddr p2) 2)))
                (polyp$ `(* ,(car p2) (expt ,(caddr p1) 2)))
                (polyp$ `(* ,(cadr p1) (expt ,(caddr p2) 3)))
                (polyp$ `(* ,(cadr p2) (expt ,(caddr p1) 3)))))
  :hints (("Goal" :in-theory (enable polyp$ tripp$))))

(local-defthmd eq$eq-2
  (implies (and (tripp$ p1)
                (tripp$ p2)
                (eq$ p1 p2))
           (and (equal (mod (* (evalp$ (car p1)) (expt (evalp$ (caddr p2)) 2)) (p))
                       (mod (* (evalp$ (car p2)) (expt (evalp$ (caddr p1)) 2)) (p)))
                (equal (mod (* (evalp$ (cadr p1)) (expt (evalp$ (caddr p2)) 3)) (p))
                       (mod (* (evalp$ (cadr p2)) (expt (evalp$ (caddr p1)) 3)) (p)))))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                  :expand ((tripp$ p1) (tripp$ p2) (eq$ p1 p2))
                  :use (eq$-term-rewrite eq$-term-polyp
                        (:instance reduce$-correct (x `(* ,(car p1) (expt ,(caddr p2) 2))))
                        (:instance reduce$-correct (x `(* ,(car p2) (expt ,(caddr p1) 2))))
                        (:instance reduce$-correct (x `(* ,(cadr p1) (expt ,(caddr p2) 3))))
                        (:instance reduce$-correct (x `(* ,(cadr p2) (expt ,(caddr p1) 3))))))))

(local-defthmd eq$eq-3
  (implies (and (tripp$ p1)
                (tripp$ p2)
                (eq$ p1 p2))
           (and (equal (mod (* (evalp$ (car p1)) (expt (evalp$ (caddr p2)) 2)
                               (frcp (expt (evalp$ (caddr p1)) 2)) (frcp (expt (evalp$ (caddr p2)) 2))) 
                            (p))
                       (mod (* (evalp$ (car p2)) (expt (evalp$ (caddr p1)) 2)
                               (frcp (expt (evalp$ (caddr p1)) 2)) (frcp (expt (evalp$ (caddr p2)) 2))) 
                            (p)))
                (equal (mod (* (evalp$ (cadr p1)) (expt (evalp$ (caddr p2)) 3)
                               (frcp (expt (evalp$ (caddr p1)) 3)) (frcp (expt (evalp$ (caddr p2)) 3))) 
                            (p))
                       (mod (* (evalp$ (cadr p2)) (expt (evalp$ (caddr p1)) 3)
                               (frcp (expt (evalp$ (caddr p1)) 3)) (frcp (expt (evalp$ (caddr p2)) 3))) 
                            (p)))))
  :hints (("Goal" :in-theory (enable tripp$)
                  :use (eq$eq-2
                        (:instance mod-times-mod (a (* (evalp$ (car p1)) (expt (evalp$ (caddr p2)) 2)))
                                                 (b (* (evalp$ (car p2)) (expt (evalp$ (caddr p1)) 2)))
                                                 (c (* (frcp (expt (evalp$ (caddr p1)) 2)) (frcp (expt (evalp$ (caddr p2)) 2))))
                                                 (n (p)))
                        (:instance mod-times-mod (a (* (evalp$ (cadr p1)) (expt (evalp$ (caddr p2)) 3)))
                                                 (b (* (evalp$ (cadr p2)) (expt (evalp$ (caddr p1)) 3)))
                                                 (c (* (frcp (expt (evalp$ (caddr p1)) 3)) (frcp (expt (evalp$ (caddr p2)) 3))))
                                                 (n (p)))))))

(local-defthmd eq$eq-4
  (implies (and (tripp$ p1)
                (tripp$ p2))
           (equal (mod (* (evalp$ (car p1)) (expt (evalp$ (caddr p2)) 2)
                          (frcp (expt (evalp$ (caddr p1)) 2)) (frcp (expt (evalp$ (caddr p2)) 2))) 
                       (p))
                  (mod (* (evalp$ (car p1)) (frcp (expt (evalp$ (caddr p1)) 2)))
                       (p))))
  :hints (("Goal" :in-theory (enable tripp$)
                  :use ((:instance mod-expt-0 (p (p)) (n (evalp$ (caddr p2))) (k 2))
                        (:instance frcp-cor (m (* (evalp$ (car p1)) (frcp (expt (evalp$ (caddr p1)) 2))))
                                           (n (expt (evalp$ (caddr p2)) 2)))))))

(local-defthmd eq$eq-5
  (implies (and (tripp$ p1)
                (tripp$ p2))
           (equal (mod (* (evalp$ (car p2)) (expt (evalp$ (caddr p1)) 2)
                          (frcp (expt (evalp$ (caddr p1)) 2)) (frcp (expt (evalp$ (caddr p2)) 2))) 
                       (p))
                  (mod (* (evalp$ (car p2)) (frcp (expt (evalp$ (caddr p2)) 2)))
                       (p))))
  :hints (("Goal" :in-theory (enable tripp$)
                  :use ((:instance mod-expt-0 (p (p)) (n (evalp$ (caddr p1))) (k 2))
                        (:instance frcp-cor (m (* (evalp$ (car p2)) (frcp (expt (evalp$ (caddr p2)) 2))))
                                           (n (expt (evalp$ (caddr p1)) 2)))))))

(local-defthmd eq$eq-6
  (implies (and (tripp$ p1)
                (tripp$ p2))
           (equal (mod (* (evalp$ (cadr p1)) (expt (evalp$ (caddr p2)) 3)
                          (frcp (expt (evalp$ (caddr p1)) 3)) (frcp (expt (evalp$ (caddr p2)) 3))) 
                       (p))
                  (mod (* (evalp$ (cadr p1)) (frcp (expt (evalp$ (caddr p1)) 3)))
                       (p))))
  :hints (("Goal" :in-theory (enable tripp$)
                  :use ((:instance mod-expt-0 (p (p)) (n (evalp$ (caddr p2))) (k 3))
                        (:instance frcp-cor (m (* (evalp$ (cadr p1)) (frcp (expt (evalp$ (caddr p1)) 3))))
                                           (n (expt (evalp$ (caddr p2)) 3)))))))

(local-defthmd eq$eq-7
  (implies (and (tripp$ p1)
                (tripp$ p2))
           (equal (mod (* (evalp$ (cadr p2)) (expt (evalp$ (caddr p1)) 3)
                          (frcp (expt (evalp$ (caddr p1)) 3)) (frcp (expt (evalp$ (caddr p2)) 3))) 
                       (p))
                  (mod (* (evalp$ (cadr p2)) (frcp (expt (evalp$ (caddr p2)) 3)))
                       (p))))
  :hints (("Goal" :in-theory (enable tripp$)
                  :use ((:instance mod-expt-0 (p (p)) (n (evalp$ (caddr p1))) (k 3))
                        (:instance frcp-cor (m (* (evalp$ (cadr p2)) (frcp (expt (evalp$ (caddr p2)) 3))))
                                           (n (expt (evalp$ (caddr p1)) 3)))))))

(local-defthmd eq$eq-8
  (implies (and (tripp$ p1)
                (tripp$ p2)
                (eq$ p1 p2))
           (and (equal (mod (* (evalp$ (car p1)) (frcp (expt (evalp$ (caddr p1)) 2))) (p))
                       (mod (* (evalp$ (car p2)) (frcp (expt (evalp$ (caddr p2)) 2))) (p)))
                (equal (mod (* (evalp$ (cadr p1)) (frcp (expt (evalp$ (caddr p1)) 3))) (p))
                       (mod (* (evalp$ (cadr p2)) (frcp (expt (evalp$ (caddr p2)) 3))) (p)))))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                  :use (eq$eq-3 eq$eq-4 eq$eq-5 eq$eq-6 eq$eq-7))))

(defthmd eq$eq
  (implies (and (tripp$ p1)
                (tripp$ p2)
                (eq$ p1 p2))
           (equal (decode3$ p1) (decode3$ p2)))
  :hints (("Goal" :use (eq$eq-8)
                  :in-theory (enable tripp$ decode3$ decode3 dx dy))))


