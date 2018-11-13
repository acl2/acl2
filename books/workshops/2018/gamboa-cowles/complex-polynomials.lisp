(in-package "ACL2")
  
; cert_param: (uses-acl2r)

(local (include-book "arithmetic-5/top" :dir :system))
(include-book "nonstd/nsa/intervals" :dir :system)

(include-book "complex-continuity")
(include-book "de-moivre")

(defun polynomial-p (poly)
  (if (consp poly)
      (and (acl2-numberp (car poly))
           (polynomial-p (cdr poly)))
    (null poly)))

(defun non-trivial-complex-polynomial-p (poly)
  (and (polynomial-p poly)
       (< 1 (len poly))
       (not (equal 0 (car (last poly))))))

(defun eval-polynomial (poly x)
  (if (consp poly)
      (+ (* x (eval-polynomial (cdr poly) x))
         (car poly))
    0))

(defun complex-polynomial-root-p (poly x)
  (and (acl2-numberp x)
       (equal (eval-polynomial poly x) 0)))

(defun non-trivial-complex-polynomial-root-p (poly x)
  (and (non-trivial-complex-polynomial-p poly)
       (complex-polynomial-root-p poly x)))

(defun eval-poly-domain ()
   (cons (interval nil nil)
         (interval nil nil)))

(defthm regionp-eval-poly-domain
  (region-p (eval-poly-domain)))

(defthm eval-poly-domain-complex
  (implies (inside-region-p z (eval-poly-domain))
           (acl2-numberp z))
  :rule-classes (:forward-chaining))

(defthm eval-poly-domain-non-trivial
  (or (or (null (interval-left-endpoint (car (eval-poly-domain))))
          (null (interval-right-endpoint (car (eval-poly-domain))))
          (< (interval-left-endpoint (car (eval-poly-domain)))
             (interval-right-endpoint (car (eval-poly-domain)))))
      (or (null (interval-left-endpoint (cdr (eval-poly-domain))))
          (null (interval-right-endpoint (cdr (eval-poly-domain))))
          (< (interval-left-endpoint (cdr (eval-poly-domain)))
             (interval-right-endpoint (cdr (eval-poly-domain))))))
  :rule-classes nil)

(defthm eval-poly-complex
  (acl2-numberp (eval-polynomial poly x))
  :rule-classes (:rewrite :type-prescription))

(defthm-std standardp-eval-poly
  (implies (and (standardp poly)
                (standardp z))
           (standardp (eval-polynomial poly z))))

(defthm limited-eval-poly
  (implies (and (standardp poly)
                (standardp z))
           (i-limited (eval-polynomial poly z)))
  :hints (("Goal"
           :use ((:instance standards-are-limited
                            (x (eval-polynomial poly z)))))))

(defthm eval-poly-continuous-lemma
  (implies (and (i-close b1 b2)
                (i-close c1 c2)
                (i-limited b1)
                (i-limited c1))
           (i-close (+ a (* b1 c1))
                    (+ a (* b2 c2))))
  :hints (("Goal"
           :use ((:instance close-plus
                            (x1 a)
                            (x2 a)
                            (y1 (* b1 c1))
                            (y2 (* b2 c2)))
                 (:instance close-times-2
                            (x1 b1)
                            (x2 b2)
                            (y1 c1)
                            (y2 c2)))))
  :rule-classes nil)


(defthm eval-poly-continuous
  (implies (and (standardp poly)
                (standardp z)
                (inside-region-p z (eval-poly-domain))
                (i-close z z2)
                (inside-region-p z2 (eval-poly-domain)))
           (i-close (eval-polynomial poly z) (eval-polynomial poly z2)))
  :hints (("Subgoal *1/1"
           :use ((:instance eval-poly-continuous-lemma
                            (a (car poly))
                            (b1 z)
                            (b2 z2)
                            (c1 (eval-polynomial (cdr poly) z))
                            (c2 (eval-polynomial (cdr poly) z2))))))
  :rule-classes nil)

(defun norm-eval-polynomial (poly z)
  (norm2 (eval-polynomial poly z)))

(defun-sk norm-eval-poly-is-minimum-point-in-region (poly zmin z0 s)
  (forall (z)
	  (implies (and (acl2-numberp z)
                        (acl2-numberp z0)
                        (realp s)
                        (< 0 s)
			(inside-region-p z (cons (interval (realpart z0)
                                                           (+ s (realpart z0)))
                                                 (interval (imagpart z0)
                                                           (+ s (imagpart z0))))))
		   (<= (norm-eval-polynomial poly zmin)
                       (norm-eval-polynomial poly z)))))

(defun-sk norm-eval-poly-achieves-minimum-point-in-region (poly z0 s)
  (exists (zmin)
          (implies (and (acl2-numberp z0)
                        (realp s)
                        (< 0 s))
                   (and (inside-region-p zmin (cons (interval (realpart z0)
                                                              (+ s (realpart z0)))
                                                    (interval (imagpart z0)
                                                              (+ s (imagpart z0)))))
                        (norm-eval-poly-is-minimum-point-in-region poly zmin z0 s)))))


(defthm norm-eval-poly-minimum-point-in-region-theorem-sk
  (implies (and (acl2-numberp z0)
                (realp s)
                (< 0 s)
                (inside-region-p z0 (eval-poly-domain))
		(inside-region-p (+ z0 (complex s s)) (eval-poly-domain)))
	   (norm-eval-poly-achieves-minimum-point-in-region context z0 s))
  :hints (("Goal"
	   :by (:functional-instance norm-ccfn-minimum-point-in-region-theorem-sk
                                     (norm-ccfn norm-eval-polynomial)
                                     (ccfn eval-polynomial)
                                     (ccfn-domain eval-poly-domain)
                                     (norm-ccfn-achieves-minimum-point-in-region norm-eval-poly-achieves-minimum-point-in-region)
                                     (norm-ccfn-achieves-minimum-point-in-region-witness norm-eval-poly-achieves-minimum-point-in-region-witness)
                                     (norm-ccfn-is-minimum-point-in-region norm-eval-poly-is-minimum-point-in-region)
                                     (norm-ccfn-is-minimum-point-in-region-witness norm-eval-poly-is-minimum-point-in-region-witness)
                                     ))
          ("Subgoal 5"
           :use ((:instance norm-eval-poly-achieves-minimum-point-in-region-suff
                            (poly context))))
          ("Subgoal 3"
           :use ((:instance norm-eval-poly-is-minimum-point-in-region-necc
                            (poly context))))
          ("Subgoal 1"
           :use ((:instance eval-poly-continuous
                            (poly context))))
          ))

;;; --------------------------------


(defun leading-coeff (poly)
  (first (last poly)))

(defthm split-eval-polynomial
  (equal (eval-polynomial poly z)
         (+ (* (leading-coeff poly)
               (expt z (1- (len poly))))
            (eval-polynomial (all-but-last poly) z)))
  :rule-classes nil)

(defun eval-poly-with-expt (poly z)
  (if (consp poly)
      (+ (* (leading-coeff poly)
            (expt z (1- (len poly))))
         (eval-poly-with-expt (all-but-last poly) z))
    0))

(defthm eval-poly-with-expt-is-eval-poly
  (equal (eval-poly-with-expt poly z)
         (eval-polynomial poly z))
  :hints (("Goal"
           :induct (eval-poly-with-expt poly z))
          ("Subgoal *1/1"
           :use ((:instance split-eval-polynomial))))
  :rule-classes nil)

(defun minus-poly (poly)
  (if (consp poly)
      (cons (- (car poly))
            (minus-poly (cdr poly)))
    nil))

(defthm eval-poly-minus-poly
  (equal (eval-polynomial (minus-poly poly) z)
         (- (eval-polynomial poly z)))
  )                                      
                

(defun a_n/2 (poly)
  (/ (norm2 (leading-coeff poly)) 2))

(defun max-norm2-coeffs (poly)
  (if (consp poly)
      (if (consp (cdr poly))
          (max (norm2 (car poly))
               (max-norm2-coeffs (cdr poly)))
        (norm2 (car poly)))
    0))

(defthm member-max-norm2-coeffs
  (implies (member coeff poly)
           (<= (norm2 coeff)
               (max-norm2-coeffs poly))))

(defun sum-norm2-monomials (poly z)
  (if (consp poly)
      (+ (norm2 (* (leading-coeff poly)
                   (expt z (1- (len poly)))))
         (sum-norm2-monomials (all-but-last poly) z))
    0))

(defthm norm-poly-<=-sum-norm2-monomials
  (<= (norm2 (eval-poly-with-expt poly z))
      (sum-norm2-monomials poly z))
  :hints (("Goal"
           :induct (eval-poly-with-expt poly z)
           :do-not-induct t)
          ("Subgoal *1/1"
           :use ((:instance norm2-triangle-inequality
                            (x (* (leading-coeff poly)
                                  (expt z (1- (len poly)))))
                            (y (eval-poly-with-expt (all-but-last poly) z))))
           :in-theory (disable norm2-triangle-inequality))))


(defun sum-norm2-monomials-2 (poly z)
  (if (consp poly)
      (+ (* (norm2 (leading-coeff poly))
            (norm2 (expt z (1- (len poly)))))
         (sum-norm2-monomials-2 (all-but-last poly) z))
    0))

(defthm sum-norm2-monomials-2-is-sum-norm2-monomials
  (equal (sum-norm2-monomials-2 poly z)
         (sum-norm2-monomials poly z))
  :rule-classes nil)

(defun sum-norm2-expts-only (poly z)
  (if (consp poly)
      (+ (norm2 (expt z (1- (len poly))))
         (sum-norm2-expts-only (all-but-last poly) z))
    0))

(defthm max-norm2-coeffs-all-but-last
  (<= (max-norm2-coeffs (all-but-last poly))
      (max-norm2-coeffs poly)))

(defthm last-max-norm2-coeffs
  (implies (consp poly)
           (<= (norm2 (car (last poly)))
               (max-norm2-coeffs poly)))
  :rule-classes nil)

(local
 (defthm lemma-1
   (implies (and (realp x1)
                 (realp x2)
                 (<= x1 x2)
                 (realp y1) (<= 0 y1)
                 (realp y2) 
                 (<= y1 y2)
                 (realp z)  (<= 0 z))
            (<= (+ x1 (* y1 z))
                (+ x2 (* y2 z))))
   :hints (("Goal"
            :use ((:instance (:theorem (implies (and (realp x1) (realp x2)
                                                     (realp y1) (realp y2)
                                                     (<= x1 x2) (<= y1 y2))
                                                (<= (+ x1 y1) (+ x2 y2))))
                             (x1 x1)
                             (x2 x2)
                             (y1 (* y1 z))
                             (y2 (* y2 z))))))
   :rule-classes nil))

(defthm bound-using-sum-norm2-expts-only-lemma
  (implies (and (realp M)
                (<= (max-norm2-coeffs poly) M))
           (<= (sum-norm2-monomials-2 poly z)
               (* M (sum-norm2-expts-only poly z))))
  :hints (("Goal"
           :induct (sum-norm2-expts-only poly z)
           :do-not-induct t)
          ("Subgoal *1/1"
           :use ((:instance max-norm2-coeffs-all-but-last)
                 (:instance last-max-norm2-coeffs)
                 (:instance lemma-1
                            (x1 (sum-norm2-monomials-2 (all-but-last poly) z))
                            (x2 (* M (sum-norm2-expts-only (all-but-last poly) z)))
                            (y1 (norm2 (car (last poly))))
                            (y2 M)
                            (z (norm2 (expt z (+ -1 (len poly))))))
                 )
           :in-theory (disable max-norm2-coeffs-all-but-last))
          )
  :rule-classes nil)

(defthm bound-using-sum-norm2-expts-only
  (<= (sum-norm2-monomials-2 poly z)
      (* (max-norm2-coeffs poly) (sum-norm2-expts-only poly z)))
  :hints (("Goal"
           :use ((:instance bound-using-sum-norm2-expts-only-lemma
                            (M (max-norm2-coeffs poly)))))))

(defthm expt-monotonic
  (implies (and (realp z)
                (<= 1 z)
                (natp i)
                (natp j)
                (<= i j))
           (<= (expt z i)
               (expt z j)))
  :hints (("Goal"
           :in-theory (enable expt))))

(defun sum-norm2-expts-only-bound (poly z n)
  (if (consp poly)
      (+ (norm2 (expt z n))
         (sum-norm2-expts-only-bound (all-but-last poly) z n))
    0))

(defthm len-poly-when-consp
  (implies (consp poly)
           (equal (< (+ -1 (len poly)) 0) nil))
  )

(defthm len-all-but-last
  (implies (consp poly)
           (equal (len (all-but-last poly))
                  (1- (len poly)))))

(defthm sum-norm2-expts-only-upper-bound-is-bound-lemma
  (implies (and (acl2-numberp z)
                (<= 1 (norm2 z))
                (natp n)
                (<= (1- (len poly)) n)
                )
           (<= (sum-norm2-expts-only poly z)
               (sum-norm2-expts-only-bound poly z n)))
  :hints (("Subgoal *1/2"
           :use ((:instance expt-monotonic
                            (z (norm2 z))
                            (i (+ -1 (len poly)))
                            (j n))
                 (:instance norm2-expt
                            (z z)
                            (n (+ -1 (len poly))))
                 (:instance norm2-expt
                            (z z)
                            (n n))
                 )
           :in-theory (disable expt-monotonic
                               norm2-expt
                               expt-is-weakly-increasing-for-base->-1
                               SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<)
           :do-not-induct t
           )
          )
  :rule-classes nil)

(defthm sum-norm2-expts-only-upper-bound-is-bound
  (implies (and (acl2-numberp z)
                (<= 1 (norm2 z))
                (consp poly)
                )
           (<= (sum-norm2-expts-only poly z)
               (sum-norm2-expts-only-bound poly z (1- (len poly)))))
  :hints (("Goal"
           :use ((:instance sum-norm2-expts-only-upper-bound-is-bound-lemma
                            (n (1- (len poly)))))))
  :rule-classes nil)



(defthm sum-norm2-expts-only-bound-direct
  (implies (natp n)
           (<= (sum-norm2-expts-only-bound poly z n)
               (* (len poly)
                  (expt (norm2 z) n))))
  :hints (("Subgoal *1/1"
           :use ((:instance len-all-but-last)
                 (:instance norm2-expt
                            (z z)
                            (n n))
                 )
           :in-theory (disable norm2-expt)
           )
          )
  :rule-classes nil
  )
           


(defthm <=-transitive
  (implies (and (<= a b)
                (<= b c))
           (<= a c))
  :rule-classes nil)

(defthm <=-lemma-1
  (implies (and (<= a (* b c1))
                (<= c1 c2)
                (acl2-numberp a)
                (realp b)
                (<= 0 b)
                (acl2-numberp c1)
                (acl2-numberp c2)
                )
           (<= a (* b c2)))
  :hints (("Goal"
           :use ((:instance <=-transitive
                            (a a)
                            (b (* b c1))
                            (c (* b c2)))
                 )
           )
          )
  :rule-classes nil)

(defthm norm-eval-poly-lower-bound-on-extremes
  (implies (and (acl2-numberp z)
                (<= 1 (norm2 z))
                (consp poly)
                )
           (<= (norm2 (eval-polynomial poly z))
               (* (max-norm2-coeffs poly)
                  (len poly)
                  (expt (norm2 z) (1- (len poly))))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance eval-poly-with-expt-is-eval-poly)
                 (:instance norm-poly-<=-sum-norm2-monomials)
                 (:instance sum-norm2-monomials-2-is-sum-norm2-monomials)
                 (:instance bound-using-sum-norm2-expts-only)
                 (:instance sum-norm2-expts-only-upper-bound-is-bound)
                 (:instance sum-norm2-expts-only-bound-direct
                            (n (1- (len poly))))
                 (:instance <=-transitive
                            (a (norm2 (eval-poly-with-expt poly z)))
                            (b (sum-norm2-monomials poly z))
                            (c (* (max-norm2-coeffs poly)
                                  (sum-norm2-expts-only poly z))))
                 (:instance <=-transitive
                            (a (sum-norm2-expts-only poly z))
                            (b (sum-norm2-expts-only-bound poly z (+ -1 (len poly))))
                            (c (* (len poly)
                                  (expt (norm2 z) (+ -1 (len poly))))))
                 (:instance <=-lemma-1
                            (a (norm2 (eval-poly-with-expt poly z)))
                            (b (max-norm2-coeffs poly))
                            (c1 (sum-norm2-expts-only poly z))
                            (c2 (* (len poly)
                                   (expt (norm2 z) (+ -1 (len poly))))))
                 )
           :in-theory (disable bound-using-sum-norm2-expts-only
                               norm-poly-<=-sum-norm2-monomials)
           )
          )
  :rule-classes nil)

(defthm norm-eval-poly-lower-bound-on-extremes-better
  (implies (and (acl2-numberp z)
                (<= 1 (norm2 z))
                (realp K)
                (< 0 K)
                (<= (/ (* (max-norm2-coeffs poly)
                          (len poly))
                       K)
                    (norm2 z))
                (consp poly)
                )
           (<= (norm2 (eval-polynomial poly z))
               (* K
                  (expt (norm2 z) (len poly)))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance norm-eval-poly-lower-bound-on-extremes)
                 (:instance <=-transitive
                            (a (norm2 (eval-polynomial poly z)))
                            (b (* (len poly)
                                  (max-norm2-coeffs poly)
                                  (expt (norm2 z) (+ -1 (len poly)))))
                            (c (* k (expt (norm2 z) (len poly)))))
                 (:instance
                  (:theorem (implies (and (realp x) (< 0 x)
                                          (realp y) (realp z)
                                          (<= y z))
                                     (<= (* x y) (* x z))))
                  (x (/ k (norm2 z)))
                  (y (* (/ k) (len poly) (max-norm2-coeffs poly)))
                  (z (norm2 z)))
                 )
           )
          )
  :rule-classes nil)

(defthm upper-bound-for-norm-poly-lemma-1
  (implies (consp poly)
           (<= (norm2 (eval-polynomial poly z))
               (+ (norm2 (* (leading-coeff poly)
                            (expt z (1- (len poly)))))
                  (norm2 (eval-polynomial (all-but-last poly) z)))))
  :hints (("Goal"
           :use ((:instance norm2-triangle-inequality
                            (x (* (leading-coeff poly)
                                  (expt z (1- (len poly)))))
                            (y (eval-polynomial (all-but-last poly) z)))
                 (:instance split-eval-polynomial)
                 )
           :in-theory (disable norm2-triangle-inequality
                               )
           ))
  :rule-classes nil)

(defthm upper-bound-for-norm-poly-lemma-2
  (implies (consp poly) 
           (equal (norm2 (* (leading-coeff poly)
                            (expt z (1- (len poly)))))
                  (* (norm2 (leading-coeff poly))
                     (expt (norm2 z) (1- (len poly))))))
  :hints (("Goal"
           :use ((:instance norm2-expt
                            (z z)
                            (n (1- (len poly))))
                 (:instance norm2-product
                            (a (leading-coeff poly))
                            (b (expt z (1- (len poly)))))
                 )
           :in-theory (disable norm2-triangle-inequality
                               norm2-expt
                               norm2-product
                               leading-coeff
                               )))
  :rule-classes nil)

(defthm upper-bound-for-norm-poly-lemma-3
  (implies (consp poly)
           (<= (norm2 (eval-polynomial poly z))
               (+ (* (norm2 (leading-coeff poly))
                     (expt (norm2 z) (1- (len poly))))
                  (norm2 (eval-polynomial (all-but-last poly) z)))))
  :hints (("Goal"
           :use ((:instance upper-bound-for-norm-poly-lemma-1)
                 (:instance upper-bound-for-norm-poly-lemma-2))
           )
          )
  :rule-classes nil)
  
(defthm numberp-leading-coeff
  (implies (and (polynomial-p poly)
                (consp poly))
           (acl2-numberp (leading-coeff poly))))

(defthm upper-bound-for-norm-poly-lemma-4
  (implies (and (polynomial-p poly)
                (consp poly)
                (consp (all-but-last poly))
                (not (equal (leading-coeff poly) 0))
                (acl2-numberp z)
                (<= 1 (norm2 z))
                (<= (/ (* (max-norm2-coeffs (all-but-last poly))
                          (len (all-but-last poly)))
                       (/ (norm2 (leading-coeff poly)) 2))
                    (norm2 z)))
           (<= (norm2 (eval-polynomial poly z))
               (* 3/2
                  (norm2 (leading-coeff poly))
                  (expt (norm2 z) (1- (len poly))))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance upper-bound-for-norm-poly-lemma-3)
                 (:instance norm-eval-poly-lower-bound-on-extremes-better
                            (poly (all-but-last poly))
                            (K (/ (norm2 (leading-coeff poly)) 2)))
                 )
           :in-theory (disable leading-coeff
                               eval-polynomial))
          )
  :rule-classes nil)

(defthm consp-all-but-last-poly
  (implies (< 1 (len poly))
           (and (consp poly)
                (consp (all-but-last poly)))))

(defthm upper-bound-for-norm-poly
  (implies (and (polynomial-p poly)
                (< 1 (len poly))
                (not (equal (leading-coeff poly) 0))
                (acl2-numberp z)
                (<= 1 (norm2 z))
                (<= (/ (* 2
                          (max-norm2-coeffs (all-but-last poly))
                          (1- (len poly)))
                       (norm2 (leading-coeff poly)))
                    (norm2 z)))
           (<= (norm2 (eval-polynomial poly z))
               (* 3/2
                  (norm2 (leading-coeff poly))
                  (expt (norm2 z) (1- (len poly))))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance upper-bound-for-norm-poly-lemma-4)
                 )
           :in-theory (disable leading-coeff
                               eval-polynomial))
          )
  :rule-classes nil)

(defun scale-polynomial (poly c)
  (if (consp poly)
      (cons (* c (car poly))
            (scale-polynomial (cdr poly) c))
    nil))

(defthm eval-scale-polynomial
  (equal (eval-polynomial (scale-polynomial poly c) x)
         (* c (eval-polynomial poly x))))

(defthm polynomial-p-scale-polynomial
  (polynomial-p (scale-polynomial poly c)))

(defthm lower-bound-for-norm-poly-lemma-1
  (implies (consp poly)
           (<= (- (norm2 (* (leading-coeff poly)
                            (expt z (1- (len poly)))))
                  (norm2 (eval-polynomial (all-but-last poly) z)))
               (norm2 (eval-polynomial poly z))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance norm2-triangle-inequality-2
                            (x (* (leading-coeff poly)
                                  (expt z (1- (len poly)))))
                            (y (eval-polynomial (scale-polynomial (all-but-last poly) -1) z)))
                 (:instance split-eval-polynomial)
                 )
           :in-theory (disable norm2-triangle-inequality-2)
           ))
  :rule-classes nil)

(defthm lower-bound-for-norm-poly-lemma-2
  (implies (consp poly)
           (<= (- (* (norm2 (leading-coeff poly))
                     (expt (norm2 z) (1- (len poly))))
                  (norm2 (eval-polynomial (all-but-last poly) z)))
               (norm2 (eval-polynomial poly z))))
  :hints (("Goal"
           :use ((:instance lower-bound-for-norm-poly-lemma-1)
                 (:instance upper-bound-for-norm-poly-lemma-2))
           )
          )
  :rule-classes nil)

(defthm lower-bound-for-norm-poly-lemma-3
  (implies (and (polynomial-p poly)
                (consp poly)
                (consp (all-but-last poly))
                (not (equal (leading-coeff poly) 0))
                (acl2-numberp z)
                (<= 1 (norm2 z))
                (<= (/ (* (max-norm2-coeffs (all-but-last poly))
                          (len (all-but-last poly)))
                       (/ (norm2 (leading-coeff poly)) 2))
                    (norm2 z)))
           (<= (* 1/2
                  (norm2 (leading-coeff poly))
                  (expt (norm2 z) (1- (len poly))))
               (norm2 (eval-polynomial poly z))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance lower-bound-for-norm-poly-lemma-2)
                 (:instance norm-eval-poly-lower-bound-on-extremes-better
                            (poly (all-but-last poly))
                            (K (/ (norm2 (leading-coeff poly)) 2)))
                 )
           :in-theory (disable leading-coeff
                               eval-polynomial))
          )
  :rule-classes nil)

;;; IMPORTANT

(defthm lower-bound-for-norm-poly
  (implies (and (polynomial-p poly)
                (< 1 (len poly))
                (not (equal (leading-coeff poly) 0))
                (acl2-numberp z)
                (<= 1 (norm2 z))
                (<= (/ (* 2
                          (max-norm2-coeffs (all-but-last poly))
                          (1- (len poly)))
                       (norm2 (leading-coeff poly)))
                    (norm2 z)))
           (<= (* 1/2
                  (norm2 (leading-coeff poly))
                  (expt (norm2 z) (1- (len poly))))
               (norm2 (eval-polynomial poly z))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance lower-bound-for-norm-poly-lemma-3)
                 )
           :in-theory (disable leading-coeff
                               eval-polynomial))
          )
  :rule-classes nil)

(defun critical-radius (poly)
  (max (max 1
            (/ (* 2
                  (max-norm2-coeffs (all-but-last poly))
                  (1- (len poly)))
               (norm2 (leading-coeff poly))))
       (norm2 (car poly))))

(defthm critical-radius-1
  (<= 1 (critical-radius poly)))

(defthm critical-radius-2
  (<= (/ (* 2
            (max-norm2-coeffs (all-but-last poly))
            (1- (len poly)))
         (norm2 (leading-coeff poly)))
      (critical-radius poly)))

(defthm critical-radius-3
  (<= (norm2 (car poly))
      (critical-radius poly)))

(in-theory (disable critical-radius))

(defthm car-poly-is-lower-bound-for-norm-poly-lemma-1
  (implies (and (consp poly)
                (< 1 (len poly)))
           (<= (norm2 (car poly))
               (max-norm2-coeffs (all-but-last poly))))
  :rule-classes nil)

(defthm car-poly-is-lower-bound-for-norm-poly-lemma-2
  (implies (and (polynomial-p poly)
                (consp poly)
                (< 1 (len poly))
                (not (equal (leading-coeff poly) 0)))
           (<= (norm2 (car poly))
               (* 1/2
                  (norm2 (leading-coeff poly))
                  (/ (* 2
                        (max-norm2-coeffs (all-but-last poly))
                        (1- (len poly)))
                     (norm2 (leading-coeff poly))))))
  :hints (("Goal"
           :use ((:instance car-poly-is-lower-bound-for-norm-poly-lemma-1)
                 (:instance (:theorem (implies (<= a b) (<= (+ a b) (* 2 b))))
                            (a (norm2 (car poly)))
                            (b (max-norm2-coeffs (all-but-last poly))))
                 (:instance <=-transitive
                            (a (+ (max-norm2-coeffs (all-but-last poly))
                                  (norm2 (car poly))))
                            (b (* 2 (max-norm2-coeffs (all-but-last poly))))
                            (c (* (len poly) (max-norm2-coeffs (all-but-last poly))))))
           :in-theory (disable leading-coeff
                               all-but-last
                               max-norm2-coeffs)
           :do-not-induct t
           )
          )
  :rule-classes nil)



(defthm car-poly-is-lower-bound-for-norm-poly-lemma-3
  (implies (and (polynomial-p poly)
                (consp poly)
                (< 1 (len poly))
                (not (equal (leading-coeff poly) 0))
                (<= (critical-radius poly) (norm2 z))
                )
           (<= (norm2 (car poly))
               (* 1/2
                  (norm2 (leading-coeff poly))
                  (norm2 z))))
  :hints (("Goal"
           :use ((:instance car-poly-is-lower-bound-for-norm-poly-lemma-2)
                 (:instance critical-radius-2)
                 (:instance
                  (:theorem (implies (and (realp x) (<= 0 x)
                                          (realp y) (realp z)
                                          (<= y z))
                                     (<= (* x y) (* x z))))
                  (x (* 1/2 (norm2 (leading-coeff poly))))
                  (y (/ (* 2
                           (max-norm2-coeffs (all-but-last poly))
                           (1- (len poly)))
                        (norm2 (leading-coeff poly))))
                  (z (norm2 z)))
                 )
           :in-theory (disable leading-coeff
                               all-but-last
                               max-norm2-coeffs)
           :do-not-induct t
           )
          )
  :rule-classes nil)

(defthm car-poly-is-lower-bound-for-norm-poly-lemma-4
  (implies (and (polynomial-p poly)
                (consp poly)
                (< 1 (len poly))
                (not (equal (leading-coeff poly) 0))
                (acl2-numberp z)
                (<= (critical-radius poly) (norm2 z))
                )
           (<= (norm2 (car poly))
                (* 1/2
                  (norm2 (leading-coeff poly))
                  (expt (norm2 z) (1- (len poly))))))
  :hints (("Goal"
           :use ((:instance car-poly-is-lower-bound-for-norm-poly-lemma-3)
                 (:instance
                  (:theorem (implies (and (realp x) (<= 0 x)
                                          (realp y) (realp z)
                                          (<= y z))
                                     (<= (* x y) (* x z))))
                  (x (* 1/2 (norm2 (leading-coeff poly))))
                  (y (expt (norm2 z) 1))
                  (z (expt (norm2 z) (1- (len poly)))))
                 (:instance <=-transitive
                            (a (norm2 (car poly)))
                            (b (* 1/2
                                  (norm2 (leading-coeff poly))
                                  (norm2 z)))
                            (c (* 1/2
                                  (norm2 (leading-coeff poly))
                                  (expt (norm2 z) (1- (len poly))))))
                 (:instance expt-monotonic
                            (z (norm2 z))
                            (i 1)
                            (j (1- (len poly))))
                 (:instance critical-radius-1)
                 )
           :in-theory (disable leading-coeff
                               expt-monotonic)
           :do-not-induct t
           )
          )
  :rule-classes nil)

(defthm car-poly-is-lower-bound-for-norm-poly
  (implies (and (polynomial-p poly)
                (< 1 (len poly))
                (not (equal (leading-coeff poly) 0))
                (acl2-numberp z)
                (<= (critical-radius poly) (norm2 z)))
           (<= (norm2 (car poly))
               (norm2 (eval-polynomial poly z))))
  :hints (("Goal"
           :use ((:instance <=-transitive
                            (a (norm2 (car poly)))
                            (b (* 1/2
                                  (norm2 (leading-coeff poly))
                                  (expt (norm2 z) (1- (len poly)))))
                            (c (norm2 (eval-polynomial poly z))))
                 (:instance lower-bound-for-norm-poly)
                 (:instance car-poly-is-lower-bound-for-norm-poly-lemma-4)
                 (:instance critical-radius-1)
                 (:instance critical-radius-2)
                 )
           :in-theory (disable critical-radius-1
                               critical-radius-2
                               eval-polynomial
                               max-norm2-coeffs)
           :do-not-induct t
           )
          )
  :rule-classes nil)

(defthm outside-square-means-outside-norm2
  (implies (and (realp s)
                (< 0 s)
                (acl2-numberp z)
                (<= (norm2 z) s))
           (inside-region-p z (cons (interval (- s) s)
                                    (interval (- s) s))))
  :hints (("Goal"
           :use ((:instance abs-realpart-imagpart-<=-norm2 (x z))
                 )
           :in-theory (e/d (interval-definition-theory)
                           (abs-realpart-imagpart-<=-norm2))
           )
          )
  :rule-classes nil)

(defthm outside-square-means-outside-norm2-corollary
  (implies (and (realp s)
                (< 0 s)
                (acl2-numberp z)
                (<= (norm2 z) s))
           (and (inside-interval-p (realpart z)
                                   (interval (- s) s))
                (inside-interval-p (imagpart z)
                                   (interval (- s) s))))
  :hints (("Goal"
           :use ((:instance outside-square-means-outside-norm2))))
  :rule-classes nil)

(local
 (defthm inside-interval-nil
   (implies (realp x)
            (inside-interval-p x '(nil)))
   :hints (("Goal"
            :in-theory (enable interval-definition-theory)))))

(defthm local-minimum-is-global-minimum-in-big-enough-region-lemma-1
  (implies (and (polynomial-p poly)
                (< 1 (len poly))
                (not (equal (leading-coeff poly) 0))
                (acl2-numberp z)
                (<= (norm2 z) (critical-radius poly))
                )
           (and (acl2-numberp (norm-eval-poly-achieves-minimum-point-in-region-witness
                               poly
                               (complex (- (critical-radius poly)) (- (critical-radius poly)))
                               (* 2 (critical-radius poly))))
                (<= (norm-eval-polynomial poly
                                          (norm-eval-poly-achieves-minimum-point-in-region-witness
                                           poly
                                           (complex (- (critical-radius poly)) (- (critical-radius poly)))
                                           (* 2 (critical-radius poly))))
                    (norm-eval-polynomial poly z))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance norm-eval-poly-minimum-point-in-region-theorem-sk
                            (context poly)
                            (z0 (complex (- (critical-radius poly)) (- (critical-radius poly))))
                            (s (* 2 (critical-radius poly))))
                 (:instance norm-eval-poly-achieves-minimum-point-in-region
                            (z0 (complex (- (critical-radius poly)) (- (critical-radius poly))))
                            (s (* 2 (critical-radius poly))))
                 (:instance norm-eval-poly-is-minimum-point-in-region-necc
                            (zmin (norm-eval-poly-achieves-minimum-point-in-region-witness
                                   poly
                                   (complex (- (critical-radius poly)) (- (critical-radius poly)))
                                   (* 2 (critical-radius poly))))
                            (z0 (complex (- (critical-radius poly)) (- (critical-radius poly))))
                            (s (* 2 (critical-radius poly))))
                 (:instance outside-square-means-outside-norm2-corollary
                            (z z)
                            (s (critical-radius poly)))
                 )
           )
          )
  :rule-classes nil)

(defthm local-minimum-is-global-minimum-in-big-enough-region-lemma-2
  (implies (and (polynomial-p poly)
                (< 1 (len poly))
                (not (equal (leading-coeff poly) 0))
                (acl2-numberp z)
                (<= (critical-radius poly) (norm2 z))
                )
           (and (acl2-numberp (norm-eval-poly-achieves-minimum-point-in-region-witness
                               poly
                               (complex (- (critical-radius poly)) (- (critical-radius poly)))
                               (* 2 (critical-radius poly))))
                (<= (norm-eval-polynomial poly
                                          (norm-eval-poly-achieves-minimum-point-in-region-witness
                                           poly
                                           (complex (- (critical-radius poly)) (- (critical-radius poly)))
                                           (* 2 (critical-radius poly))))
                    (norm-eval-polynomial poly z))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance local-minimum-is-global-minimum-in-big-enough-region-lemma-1
                            (z 0))
                 (:instance car-poly-is-lower-bound-for-norm-poly)
                 (:instance <=-transitive
                            (a (norm-eval-polynomial poly
                                                     (norm-eval-poly-achieves-minimum-point-in-region-witness
                                                      poly
                                                      (complex (- (critical-radius poly)) (- (critical-radius poly)))
                                                      (* 2 (critical-radius poly)))))
                            (b (car poly))
                            (c (norm-eval-polynomial poly z)))
                 )
           )
          )
  :rule-classes nil)


(defthm local-minimum-is-global-minimum-in-big-enough-region-lemma-3
  (implies (and (polynomial-p poly)
                (< 1 (len poly))
                (not (equal (leading-coeff poly) 0))
                (acl2-numberp z)
                )
           (and (acl2-numberp (norm-eval-poly-achieves-minimum-point-in-region-witness
                               poly
                               (complex (- (critical-radius poly)) (- (critical-radius poly)))
                               (* 2 (critical-radius poly))))
                (<= (norm-eval-polynomial poly
                                          (norm-eval-poly-achieves-minimum-point-in-region-witness
                                           poly
                                           (complex (- (critical-radius poly)) (- (critical-radius poly)))
                                           (* 2 (critical-radius poly))))
                    (norm-eval-polynomial poly z))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance local-minimum-is-global-minimum-in-big-enough-region-lemma-1)
                 (:instance local-minimum-is-global-minimum-in-big-enough-region-lemma-2))))
  :rule-classes nil)


(defun-sk norm-eval-poly-is-minimum-point-globally (poly zmin)
  (forall (z)
	  (implies (acl2-numberp z)
		   (<= (norm-eval-polynomial poly zmin)
                       (norm-eval-polynomial poly z)))))

(defun-sk norm-eval-poly-achieves-minimum-point-globally (poly)
  (exists (zmin)
          (and (acl2-numberp zmin)
               (norm-eval-poly-is-minimum-point-globally poly zmin))))


(defthm norm-eval-poly-minimum-point-globally-theorem-sk-lemma
  (implies (and (polynomial-p poly)
                (< 1 (len poly))
                (not (equal (leading-coeff poly) 0)))
           (and (acl2-numberp (norm-eval-poly-achieves-minimum-point-in-region-witness
                               poly
                               (complex (- (critical-radius poly)) (- (critical-radius poly)))
                               (* 2 (critical-radius poly))))
                (norm-eval-poly-is-minimum-point-globally poly (norm-eval-poly-achieves-minimum-point-in-region-witness
                                                                poly
                                                                (complex (- (critical-radius poly)) (- (critical-radius poly)))
                                                                (* 2 (critical-radius poly))))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance norm-eval-poly-is-minimum-point-globally
                            (zmin (norm-eval-poly-achieves-minimum-point-in-region-witness
                                   poly
                                   (complex (- (critical-radius poly)) (- (critical-radius poly)))
                                   (* 2 (critical-radius poly)))))
                 (:instance local-minimum-is-global-minimum-in-big-enough-region-lemma-3
                            (z (norm-eval-poly-is-minimum-point-globally-witness
                                poly
                                (norm-eval-poly-achieves-minimum-point-in-region-witness
                                 poly
                                 (complex (- (critical-radius poly))
                                          (- (critical-radius poly)))
                                 (* 2 (critical-radius poly)))))
                            )
                 (:instance local-minimum-is-global-minimum-in-big-enough-region-lemma-3
                            (z 0))
                 )
           )
          )
  :rule-classes nil)
                            
;;; IMPORTANT

(defthm norm-eval-poly-minimum-point-globally-theorem-sk
  (implies (and (polynomial-p poly)
                (< 1 (len poly))
                (not (equal (leading-coeff poly) 0)))
	   (norm-eval-poly-achieves-minimum-point-globally poly))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance norm-eval-poly-achieves-minimum-point-globally-suff
                            (zmin (norm-eval-poly-achieves-minimum-point-in-region-witness
                                   poly
                                   (complex (- (critical-radius poly)) (- (critical-radius poly)))
                                   (* 2 (critical-radius poly)))))
                 (:instance norm-eval-poly-minimum-point-globally-theorem-sk-lemma)
                 )
           )
          )
  :rule-classes nil)


;;; ---------------------

(defun add-polynomials (poly1 poly2)
  (if (consp poly1)
      (cons (+ (car poly1)
               (car poly2))
            (add-polynomials (cdr poly1) (cdr poly2)))
    nil))

(defthm add-polynomials-is-sum
  (implies (and (polynomial-p poly1)
                (polynomial-p poly2)
                (equal (len poly1) (len poly2)))
           (equal (eval-polynomial (add-polynomials poly1 poly2) z)
                  (+ (eval-polynomial poly1 z)
                     (eval-polynomial poly2 z))))
  )


(defun append-leading-zero (poly)
  (if (consp poly)
      (cons (car poly)
            (append-leading-zero (cdr poly)))
    (list 0)))

(defthm eval-poly-append-leading-zero
  (equal (eval-polynomial (append-leading-zero poly) z)
         (eval-polynomial poly z)))

(defun add-const-polynomial (poly k)
  (if (consp poly)
      (cons (+ k (car poly))
            (cdr poly))
    (list k)))

(defthm eval-poly-add-const-polynomial
  (equal (eval-polynomial (add-const-polynomial poly k) z)
         (+ (eval-polynomial poly z) k)))

(defun shift-polynomial (poly dx)
  (if (consp poly)
      (add-const-polynomial
       (add-polynomials (append-leading-zero (scale-polynomial
                                              (shift-polynomial (cdr poly) dx) dx))
                        (cons 0 (shift-polynomial (cdr poly) dx)))
       (car poly))
    nil))

(defthm consp-add-polynomials
  (equal (consp (add-polynomials poly1 poly2))
         (consp poly1)))

(defthm polynomial-p-shift-polynomial
  (polynomial-p (shift-polynomial poly dx)))

(defthm len-scale-polynomial
  (equal (len (scale-polynomial poly k))
         (len poly)))

(defthm eval-poly-cons-0
  (equal (eval-polynomial (cons 0 poly) z)
         (* z (eval-polynomial poly z))))




(defthm shift-polynomial-is-shift-lemma-1
  (equal (car (add-polynomials (append-leading-zero poly)
                               (cons 0 other-poly)))
         (if (consp poly)
             (fix (car poly))
           0))
  :hints (("Goal"
           :do-not-induct t
           :expand (add-polynomials (append-leading-zero poly)
                                    (cons 0 other-poly)))
          )
  )

(defthm consp-scale-polynomial
  (equal (consp (scale-polynomial poly k))
         (consp poly)))
                
(defthm consp-shift-polynomial
  (equal (consp (shift-polynomial poly dx))
         (consp poly)))

(defthm acl2-numberp-car-scale-poly
  (equal (acl2-numberp (car (scale-polynomial poly k)))
         (consp poly)))

(defthm eval-shift-polynomial
  (implies (and (polynomial-p poly)
                (acl2-numberp dx)
                (acl2-numberp z))
           (equal (eval-polynomial (shift-polynomial poly dx) z)
                  (eval-polynomial poly (+ z dx)))))

(defthm len-shift-polynomial
  (equal (len (shift-polynomial poly dx))
         (len poly)))

(defthm last-add-polynomial
  (implies (and (polynomial-p poly2)
                (equal (len poly2)
                       (1+ (len poly1)))
                )
           (equal (last (add-polynomials (append-leading-zero poly1)
                                         poly2))
                  (last poly2)))
  :hints (("Goal"
           :induct (add-polynomials poly1 poly2)
           )))

(defthm consp-cdr-append-leading-zero
  (equal (consp (cdr (append-leading-zero poly)))
         (consp poly))
  )

(defthm consp-cdr-add-append-leading-zero
  (equal (consp (cdr (add-polynomials (append-leading-zero poly1)
                                      poly2)))
         (consp poly1))
  :hints (("Goal"
           :do-not-induct t
           :expand (add-polynomials (append-leading-zero poly1)
                                    poly2))
          )
  )

(defthm last-cdr
  (implies (consp (cdr x))
           (equal (last (cdr x))
                  (last x)))
  :rule-classes nil)

(defthm last-cdr-add-polynomial
  (implies (and (polynomial-p poly2)
                (consp poly1)
                (equal (len poly2)
                       (1+ (len poly1)))
                )
           (equal (last (cdr (add-polynomials (append-leading-zero poly1)
                                              poly2)))
                  (last poly2)))
  :hints (("Goal"
           :induct (add-polynomials poly1 poly2)
           )))

(defthm leading-coeff-shift-polynomial
  (implies (and (polynomial-p poly)
                (acl2-numberp dx))
           (equal (leading-coeff (shift-polynomial poly dx))
                  (leading-coeff poly)))
  )

  
(defun lowest-exponent (poly)
  (if (consp poly)
      (if (equal (car poly) 0)
          (1+ (lowest-exponent (cdr poly)))
        0)
    0))

(defthm lowest-exponent-split
  (equal (eval-polynomial poly z)
         (* (expt z (lowest-exponent poly))
            (eval-polynomial (nthcdr (lowest-exponent poly) poly) z)))
  :rule-classes nil)

(defthm lowest-exponent-split-2
  (implies (consp poly)
           (equal (eval-polynomial poly z)
                  (+ (car poly)
                     (* (expt z (1+ (lowest-exponent (cdr poly))))
                        (eval-polynomial (nthcdr (lowest-exponent (cdr poly)) (cdr poly)) z)))))
  :hints (("Goal"
           :do-not-induct t
           :expand (eval-polynomial poly z)
           :use ((:instance lowest-exponent-split
                            (poly (cdr poly)))
                 )
           )
          )
  :rule-classes nil)

(defthm lowest-exponent-when-leading-coeff-not-zero
  (implies (and (consp poly)
                (not (equal (leading-coeff poly) 0)))
           (< (lowest-exponent poly) (len poly))))

(defthm nthcdr-not-null
  (implies (and (natp n)
                (< n (len poly)))
           (consp (nthcdr n poly))))

(defthm car-nthcdr-split-not-zero
  (implies (and (polynomial-p poly)
                (consp poly)
                (not (equal (leading-coeff poly) 0)))
           (and (acl2-numberp (car (nthcdr (lowest-exponent poly) poly)))
                (not (equal (car (nthcdr (lowest-exponent poly) poly)) 0))))
  )

(defthm lowest-exponent-split-3
  (implies (consp poly)
           (equal (eval-polynomial poly z)
                  (+ (car poly)
                     (* (expt z (1+ (lowest-exponent (cdr poly))))
                        (car (nthcdr (lowest-exponent (cdr poly)) (cdr poly))))
                     (* (expt z (+ 2 (lowest-exponent (cdr poly))))
                        (eval-polynomial (cdr (nthcdr (lowest-exponent (cdr poly)) (cdr poly))) z)))))
  :hints (("Goal"
           :do-not-induct t
           :expand (eval-polynomial (nthcdr (lowest-exponent (cdr poly)) (cdr poly)) z)
           :use ((:instance lowest-exponent-split-2
                            (poly (cdr poly)))
                 )
           )
          )
  :rule-classes nil)

(defthm lowest-exponent-split-4
  (implies (consp poly)
           (<= (norm2 (eval-polynomial poly z))
               (+ (norm2 (+ (car poly)
                            (* (expt z (1+ (lowest-exponent (cdr poly))))
                               (car (nthcdr (lowest-exponent (cdr poly)) (cdr poly))))))
                  (norm2 (* (expt z (+ 2 (lowest-exponent (cdr poly))))
                            (eval-polynomial (cdr (nthcdr (lowest-exponent (cdr poly)) (cdr poly))) z))))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance lowest-exponent-split-3)
                 (:instance norm2-triangle-inequality
                            (x (+ (car poly)
                                  (* (expt z (1+ (lowest-exponent (cdr poly))))
                                     (car (nthcdr (lowest-exponent (cdr poly)) (cdr poly))))))
                            (y (* (expt z (+ 2 (lowest-exponent (cdr poly))))
                                  (eval-polynomial (cdr (nthcdr (lowest-exponent (cdr poly)) (cdr poly))) z))))
                 )
           :in-theory (disable eval-polynomial norm2-product norm2-expt)
           )
          )
  :rule-classes nil)

(defun fta-bound-1 (poly s)
  (nth-root (- (/ s (car (nthcdr (lowest-exponent (cdr poly)) (cdr poly)))))
            (1+ (lowest-exponent (cdr poly)))))

(local
 (defthm expt-fta-bound-1-lemma
   (implies (and (realp s)
                 (<= 0 s)
                 (<= s (norm2 z))
                 (natp n))
            (<= (expt s n) (expt (norm2 z) n)))
   :hints (("Goal"
            :use ((:instance EXPT-IS-NON-DECREASING-FOR-NON-NEGATIVES
                             (x s)
                             (y (norm2 z))
                             (n n)))
            :in-theory (disable EXPT-IS-NON-DECREASING-FOR-NON-NEGATIVES)))
   :rule-classes nil))

(local
 (defthm leading-coeff-cdr-poly
   (implies (and (consp poly)
                 (< 1 (len poly)))
            (equal (leading-coeff (cdr poly))
                   (leading-coeff poly)))
   :rule-classes nil))

(defthm lowest-exponent-split-5-lemma-1
  (implies (and (polynomial-p poly)
                (equal (car poly) 1)
                (< 1 (len poly))
                (not (equal (leading-coeff poly) 0)))
           (equal (EXPT (FTA-BOUND-1 POLY s)
                        (+ 1 (LOWEST-EXPONENT (CDR POLY))))
                  (- (/ s (car (nthcdr (lowest-exponent (cdr poly)) (cdr poly)))))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance de-moivre-2
                            (z (- (/ s (car (nthcdr (lowest-exponent (cdr poly)) (cdr poly))))))
                            (n (+ 1 (LOWEST-EXPONENT (CDR POLY)))))
                 )
           :in-theory (disable de-moivre-2
                               nth-root))
          )
  :rule-classes nil)

(defthm lowest-exponent-split-5-lemma-2
  (implies (and (polynomial-p poly)
                (equal (car poly) 1)
                (< 1 (len poly))
                (not (equal (leading-coeff poly) 0))
                (realp s)
                (<= 0 s)
                (<= s 1)
                )
           (equal (* (EXPT (FTA-BOUND-1 POLY s)
                           (+ 1 (LOWEST-EXPONENT (CDR POLY))))
                     (car (nthcdr (lowest-exponent (cdr poly)) (cdr poly))))
                  (- s)))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance lowest-exponent-split-5-lemma-1)
                 (:instance car-nthcdr-split-not-zero
                            (poly (cdr poly)))
                 (:instance leading-coeff-cdr-poly)
                 )
           :in-theory (disable leading-coeff
                               fta-bound-1
                               lowest-exponent
                               car-nthcdr-split-not-zero))
          )
  :rule-classes nil)

(defthm lowest-exponent-split-5-lemma-3
  (implies (and (polynomial-p poly)
                (equal (car poly) 1)
                (< 1 (len poly))
                (not (equal (leading-coeff poly) 0))
                (equal (car poly) 1)
                (realp s)
                (<= 0 s)
                (<= s 1)
                )
           (and (realp (* (EXPT (FTA-BOUND-1 POLY s)
                                (+ 1 (LOWEST-EXPONENT (CDR POLY))))
                          (car (nthcdr (lowest-exponent (cdr poly)) (cdr poly)))))
                (<= (* (EXPT (FTA-BOUND-1 POLY s)
                             (+ 1 (LOWEST-EXPONENT (CDR POLY))))
                       (car (nthcdr (lowest-exponent (cdr poly)) (cdr poly))))
                    0)
                (<= -1
                    (* (EXPT (FTA-BOUND-1 POLY s)
                             (+ 1 (LOWEST-EXPONENT (CDR POLY))))
                       (car (nthcdr (lowest-exponent (cdr poly)) (cdr poly)))))))
  :Hints (("Goal"
           :use ((:instance lowest-exponent-split-5-lemma-2)
                 )
           :in-theory nil))
  :rule-classes nil)

(defthm lowest-exponent-split-5-lemma-4
  (implies (and (realp s)
                (<= s 0)
                (<= -1 s))
           (equal (norm2 (+ 1 s)) (+ 1 s)))
  :hints (("Goal"
           :use ((:instance norm2-abs
                            (x (+ 1 s)))
                 )
           :in-theory (disable norm2-abs)
           )
          )
  :rule-classes nil)

(defthm lowest-exponent-split-5-lemma-5
  (implies (and (polynomial-p poly)
                (equal (car poly) 1)
                (< 1 (len poly))
                (not (equal (leading-coeff poly) 0))
                (equal (car poly) 1)
                (realp s)
                (<= 0 s)
                (<= s 1))
           (equal (norm2 (+ 1
                            (* (expt (fta-bound-1 poly s)
                                     (1+ (lowest-exponent (cdr poly))))
                               (car (nthcdr (lowest-exponent (cdr poly)) (cdr poly))))))
                  (+ 1 (* (expt (fta-bound-1 poly s)
                                (1+ (lowest-exponent (cdr poly))))
                          (car (nthcdr (lowest-exponent (cdr poly)) (cdr poly)))))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance lowest-exponent-split-5-lemma-3)
                 (:instance lowest-exponent-split-5-lemma-4
                            (s (* (expt (fta-bound-1 poly s)
                                        (1+ (lowest-exponent (cdr poly))))
                                  (car (nthcdr (lowest-exponent (cdr poly)) (cdr poly))))))
                 )
           :in-theory (disable lowest-exponent leading-coeff fta-bound-1
                               DEFAULT-EXPT-1)))
  :rule-classes nil)


(defthm lowest-exponent-split-5-lemma-6
  (implies (and (polynomial-p poly)
                (equal (car poly) 1)
                (< 1 (len poly))
                (not (equal (leading-coeff poly) 0))
                (equal (car poly) 1)
                (realp s)
                (<= 0 s)
                (<= s 1))
           (equal (norm2 (+ 1
                            (* (expt (fta-bound-1 poly s)
                                     (1+ (lowest-exponent (cdr poly))))
                               (car (nthcdr (lowest-exponent (cdr poly)) (cdr poly))))))
                  (+ 1 (- s))))
  :hints (("Goal"
           :use ((:instance lowest-exponent-split-5-lemma-5)
                 (:instance lowest-exponent-split-5-lemma-2))
           :in-theory nil))
  :rule-classes nil)


(defthm lowest-exponent-split-5
  (implies (and (polynomial-p poly)
                (equal (car poly) 1)
                (< 1 (len poly))
                (not (equal (leading-coeff poly) 0))
                (equal (car poly) 1)
                (realp s)
                (<= 0 s)
                (<= s 1))
           (<= (norm2 (eval-polynomial poly (fta-bound-1 poly s)))
               (+ 1
                  (- s)
                  (* (norm2 (expt (fta-bound-1 poly s)
                                  (+ 2 (lowest-exponent (cdr poly)))))
                     (norm2 (eval-polynomial (cdr (nthcdr (lowest-exponent (cdr poly)) (cdr poly))) (fta-bound-1 poly s)))))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance lowest-exponent-split-4
                            (z (fta-bound-1 poly s)))
                 (:instance lowest-exponent-split-5-lemma-6)
                 )
           :in-theory (disable eval-polynomial
                               fta-bound-1
                               lowest-exponent
                               nthcdr)
           )
          )
  :rule-classes nil)

(defthm lowest-exponent-split-6-lemma-1
  (implies (and (polynomial-p poly)
                (equal (car poly) 1)
                (< 1 (len poly))
                (not (equal (leading-coeff poly) 0)))
           (equal (EXPT (FTA-BOUND-1 POLY s)
                        (+ 2 (LOWEST-EXPONENT (CDR POLY))))
                  (* (- s)
                     (/ (FTA-BOUND-1 POLY s)
                        (car (nthcdr (lowest-exponent (cdr poly)) (cdr poly)))))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance lowest-exponent-split-5-lemma-1)
                 )
           :expand (EXPT (FTA-BOUND-1 POLY s)
                         (+ 2 (LOWEST-EXPONENT (CDR POLY))))
           :in-theory (e/d (expt)
                           (fta-bound-1
                            lowest-exponent
                            nthcdr
                            polynomial-p
                            leading-coeff)))
          )
  :rule-classes nil)

(local
 (defthm norm2-divide
   (implies (and (acl2-numberp z)
                 (not (equal z 0)))
            (equal (norm2 (/ z))
                   (/ (norm2 z))))
   :hints (("Goal"
            :use ((:instance norm2-product
                             (a z)
                             (b (/ z))))
            :in-theory (disable norm2-product))
           )
   ))

(defthm lowest-exponent-split-6-lemma-2
  (implies (and (polynomial-p poly)
                (equal (car poly) 1)
                (< 1 (len poly))
                (not (equal (leading-coeff poly) 0)))
           (equal (norm2 (* (- s)
                            (/ (fta-bound-1 poly s)
                               (car (nthcdr (lowest-exponent (cdr poly)) (cdr poly))))))
                  (* (norm2 s)
                     (/ (norm2 (FTA-BOUND-1 POLY s))
                        (norm2 (car (nthcdr (lowest-exponent (cdr poly)) (cdr poly))))))))
  :hints (("Goal"
           :do-not-induct t
           :use (;(:instance lowest-exponent-split-6-lemma-1)
                 (:instance norm2-divide
                            (z (car (nthcdr (lowest-exponent (cdr poly))
                                            (cdr poly)))))
                 )
           :in-theory (disable fta-bound-1
                               norm2-divide
                               leading-coeff
                               polynomial-p
                               lowest-exponent
                               norm2
                               norm2-expt))
          )
  :rule-classes nil)

(defthm lowest-exponent-split-6-lemma-3
  (implies (and (polynomial-p poly)
                (equal (car poly) 1)
                (< 1 (len poly))
                (not (equal (leading-coeff poly) 0)))
           (equal (norm2 (EXPT (FTA-BOUND-1 POLY s)
                               (+ 2 (LOWEST-EXPONENT (CDR POLY)))))
                  (* (norm2 s)
                     (/ (norm2 (FTA-BOUND-1 POLY s))
                        (norm2 (car (nthcdr (lowest-exponent (cdr poly)) (cdr poly))))))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance lowest-exponent-split-6-lemma-1)
                 (:instance lowest-exponent-split-6-lemma-2)
                 )
           :in-theory nil)
          )
  :rule-classes nil)

(defthm lowest-exponent-split-6-lemma-4
  (implies (and (realp s)
                (<= 0 s))
           (equal (norm2 s) s))
  :hints (("Goal"
           :use ((:instance NORM2-ABS
                            (x s))
                 )
           :in-theory (disable NORM2-ABS))
          )
  )

(defthm lowest-exponent-split-6
  (implies (and (polynomial-p poly)
                (equal (car poly) 1)
                (< 1 (len poly))
                (not (equal (leading-coeff poly) 0))
                (equal (car poly) 1)
                (realp s)
                (<= 0 s)
                (<= s 1))
           (<= (norm2 (eval-polynomial poly (fta-bound-1 poly s)))
               (+ 1
                  (- s)
                  (* s
                     (norm2 (FTA-BOUND-1 POLY s))
                     (/ (norm2 (car (nthcdr (lowest-exponent (cdr poly)) (cdr poly)))))
                     (norm2 (eval-polynomial (cdr (nthcdr (lowest-exponent (cdr poly)) (cdr poly))) (fta-bound-1 poly s)))))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance lowest-exponent-split-5)
                 (:instance lowest-exponent-split-6-lemma-3)
                 )
           :in-theory (disable eval-polynomial
                               fta-bound-1
                               lowest-exponent
                               nthcdr
                               leading-coeff
                               NORM2-EXPT
                               )
           )
          )
  :rule-classes nil)

(defthm lowest-exponent-split-7
  (implies (and (polynomial-p poly)
                (equal (car poly) 1)
                (< 1 (len poly))
                (not (equal (leading-coeff poly) 0))
                (equal (car poly) 1)
                (realp s)
                (<= 0 s)
                (<= s 1))
           (<= (norm2 (eval-polynomial poly (fta-bound-1 poly s)))
               (- 1
                  (* s
                     (- 1
                        (* (norm2 (FTA-BOUND-1 POLY s))
                           (/ (norm2 (car (nthcdr (lowest-exponent (cdr poly)) (cdr poly)))))
                           (norm2 (eval-polynomial (cdr (nthcdr (lowest-exponent (cdr poly)) (cdr poly))) (fta-bound-1 poly s)))))))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance lowest-exponent-split-6)
                 )
           :in-theory (disable eval-polynomial
                               fta-bound-1
                               lowest-exponent
                               nthcdr
                               leading-coeff
                               NORM2-EXPT
                               )
           )
          )
  :rule-classes nil)


(defun sum-norm2-coeffs (poly)
  (if (consp poly)
      (+ (norm2 (leading-coeff poly))
         (sum-norm2-coeffs (all-but-last poly)))
    0))

(defthm expt-found-for-small-x
  (implies (and (acl2-numberp x)
                (<= 0 (norm2 x))
                (<= (norm2 x) 1)
                (natp n))
           (<= (norm2 (expt x n)) 1)))

(defthm eval-poly-sum-norm2-coeffs-bound
  (implies (and (acl2-numberp x)
                (<= 0 (norm2 x))
                (<= (norm2 x) 1))
           (<= (sum-norm2-monomials poly x)
               (sum-norm2-coeffs poly)))
  :hints (("Subgoal *1/1"
           :use ((:instance expt-found-for-small-x
                            (n (+ -1 (LEN POLY))))
                 (:instance (:theorem
                             (implies (and (realp x1) (realp x2) (realp y1) (realp y2) (<= x1 x2) (<= y1 y2))
                                      (<= (+ x1 y1) (+ x2 y2))))
                            (x1 (sum-norm2-monomials (all-but-last poly) x))
                            (x2 (sum-norm2-coeffs (all-but-last poly)))
                            (y1 (* (NORM2 (CAR (LAST POLY)))
                                   (norm2 (EXPT X (+ -1 (LEN POLY))))))
                            (y2 (NORM2 (CAR (LAST POLY)))))
                 )
           :in-theory (disable expt-found-for-small-x)
           )
          )
  )


(defthm upper-bound-eval-poly-for-small-x
  (implies (and (acl2-numberp x)
                (<= 0 (norm2 x))
                (<= (norm2 x) 1))
           (<= (norm2 (eval-polynomial poly x))
               (sum-norm2-coeffs poly)))
  :hints (("Goal"
           :use ((:instance norm-poly-<=-sum-norm2-monomials (z x))
                 (:instance eval-poly-sum-norm2-coeffs-bound (x x))
                 (:instance eval-poly-with-expt-is-eval-poly (z x))
                 (:instance <=-TRANSITIVE
                            (a (norm2 (eval-polynomial poly x)))
                            (b (sum-norm2-monomials poly x))
                            (c (sum-norm2-coeffs poly)))
                 )
           :in-theory nil )
          )
  )

(defthm lowest-exponent-split-8-lemma-1
  (implies (and (polynomial-p poly)
                (equal (car poly) 1)
                (< 1 (len poly))
                (not (equal (leading-coeff poly) 0))
                (acl2-numberp x)
                (<= 0 (norm2 x))
                (<= (norm2 x) 1))
           (<= (* (norm2 x)
                  (/ (norm2 (car (nthcdr (lowest-exponent (cdr poly)) (cdr poly)))))
                  (norm2 (eval-polynomial (cdr (nthcdr (lowest-exponent (cdr poly)) (cdr poly))) x)))
               (* (norm2 x)
                  (/ (norm2 (car (nthcdr (lowest-exponent (cdr poly)) (cdr poly)))))
                  (sum-norm2-coeffs (cdr (nthcdr (lowest-exponent (cdr poly)) (cdr poly)))))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance upper-bound-eval-poly-for-small-x
                            (poly (cdr (nthcdr (lowest-exponent (cdr poly)) (cdr poly)))))
                 (:instance car-nthcdr-split-not-zero)
                 (:instance car-nthcdr-split-not-zero (poly (cdr poly)))
                 )
           :in-theory (disable upper-bound-eval-poly-for-small-x
                               car-nthcdr-split-not-zero
                               eval-polynomial
                               lowest-exponent
                               SUM-NORM2-COEFFS
                               LOWEST-EXPONENT-SPLIT-6-LEMMA-4)
           )
          )
  )

(defun useful-poly-bound (poly)
  (if (consp (cdr (nthcdr (lowest-exponent (cdr poly)) (cdr poly))))
      (* (norm2 (car (nthcdr (lowest-exponent (cdr poly)) (cdr poly))))
         (/ (sum-norm2-coeffs (cdr (nthcdr (lowest-exponent (cdr poly)) (cdr poly))))))
    1))  


(defthm useful-poly-bound-is-real
  (implies (and (polynomial-p poly)
                (equal (car poly) 1)
                (< 1 (len poly))
                (not (equal (leading-coeff poly) 0))
                )
           (realp (useful-poly-bound poly)))
  )

(defthm snum-norm2-coeffs-not-zero
  (implies (and (polynomial-p poly)
                (consp poly)
                (not (equal (leading-coeff poly) 0)))
           (not (equal (sum-norm2-coeffs poly) 0)))
  :hints (("Goal"
           :in-theory (disable leading-coeff)))
  )

(defthm nthcdr-nil
  (equal (nthcdr n nil) nil))

(defthm polynomial-p-nthcdr
  (implies (polynomial-p poly)
           (polynomial-p (cdr (nthcdr n (cdr poly)))))
  :hints (("Goal"
           :induct (nthcdr n poly)))
  )

(defthm last-nthcdr
  (implies (consp (cdr (nthcdr n (cdr poly))))
           (equal (last (cdr (nthcdr n (cdr poly))))
                  (last poly)))
  :hints (("Goal"
           :induct (nthcdr n poly)))
  )

(defthm leading-coeff-nthcdr
  (implies (consp (cdr (nthcdr n (cdr poly))))
           (equal (leading-coeff (cdr (nthcdr n (cdr poly))))
                  (leading-coeff poly)))
  :hints (("Goal"
           :induct (nthcdr n poly)))
  )

(defthm useful-poly-bound-is-positive
  (implies (and (polynomial-p poly)
                (equal (car poly) 1)
                (< 1 (len poly))
                (not (equal (leading-coeff poly) 0))
                )
           (< 0 (useful-poly-bound poly)))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance car-nthcdr-split-not-zero)
                 (:instance car-nthcdr-split-not-zero (poly (cdr poly)))
                 (:instance norm2-zero-for-zero-only
                            (x (car (nthcdr (lowest-exponent (cdr poly)) (cdr poly)))))
                 (:instance (:theorem (implies (and (realp x) (realp y) (< 0 x) (< 0 y)) (< 0 (* x y))))
                            (x (norm2 (car (nthcdr (lowest-exponent (cdr poly)) (cdr poly)))))
                            (y (sum-norm2-coeffs (cdr (nthcdr (lowest-exponent (cdr poly)) (cdr poly))))))
                 (:instance snum-norm2-coeffs-not-zero
                            (poly (cdr (nthcdr (lowest-exponent (cdr poly)) (cdr poly)))))
                 )
           :in-theory (disable car-nthcdr-split-not-zero
                               norm2-zero-for-zero-only
                               leading-coeff))
          ("Subgoal 3"
           :in-theory (enable leading-coeff))
          ("Subgoal 2"
           :in-theory (enable leading-coeff))
          )
  )



(local
 (defthm silly-algebra-lemma-1
   (implies (and (realp x)
                 (realp y1)
                 (realp y2)
                 (< 0 x)
                 (< 0 y1)
                 (<= y1 y2)
                 (< x (/ y2)))
            (< (* x y1) 1))
   :hints (("Goal"
            :use ((:instance (:theorem (implies (and (realp x) (realp y1) (realp y2) (<= y1 y2) (<= 0 x)) (<= (* x y1) (* x y2))) ))
                  (:instance (:theorem (implies (and (realp x) (realp y1) (realp y2) (< y1 y2) (< 0 x)) (< (* x y1) (* x y2))))
                             (x y2)
                             (y1 x)
                             (y2 (/ y2)))
                  (:instance (:theorem (implies (and (realp x) (realp y) (realp z) (<= x y) (< y z)) (< x z)))
                             (x (* x y1))
                             (y (* x y2))
                             (z 1))
                  )
            )
           )
   :rule-classes nil))

(defthm eval-poly-of-nil
  (implies (not (consp poly))
           (equal (eval-polynomial poly z) 0)))

(defthm lowest-exponent-split-8-lemma-2
  (implies (and (polynomial-p poly)
                (equal (car poly) 1)
                (< 1 (len poly))
                (not (equal (leading-coeff poly) 0))
                (acl2-numberp x)
                (<= 0 (norm2 x))
                (<= (norm2 x) 1)
                (< (norm2 x)
                   (useful-poly-bound poly)))
           (< (* (norm2 x)
                 (/ (norm2 (car (nthcdr (lowest-exponent (cdr poly)) (cdr poly)))))
                 (norm2 (eval-polynomial (cdr (nthcdr (lowest-exponent (cdr poly)) (cdr poly))) x)))
              1))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance lowest-exponent-split-8-lemma-1)
                 (:instance silly-algebra-lemma-1
                            (x (norm2 x))
                            (y1 (* (/ (norm2 (car (nthcdr (lowest-exponent (cdr poly))
                                                          (cdr poly)))))
                                   (norm2 (eval-polynomial (cdr (nthcdr (lowest-exponent (cdr poly))
                                                                        (cdr poly)))
                                                           x))))
                            (y2 (* (/ (norm2 (car (nthcdr (lowest-exponent (cdr poly))
                                                          (cdr poly)))))
                                   (sum-norm2-coeffs (cdr (nthcdr (lowest-exponent (cdr poly))
                                                                  (cdr poly)))))))
                 )
           :in-theory (disable upper-bound-eval-poly-for-small-x
                               car-nthcdr-split-not-zero
                               eval-polynomial
                               lowest-exponent
                               SUM-NORM2-COEFFS
                               LOWEST-EXPONENT-SPLIT-6-LEMMA-4)
           )
          )
  )


(defthm lowest-exponent-split-8-lemma-3
  (implies (and (polynomial-p poly)
                (equal (car poly) 1)
                (< 1 (len poly))
                (not (equal (leading-coeff poly) 0))
                (acl2-numberp x)
                (<= 0 (norm2 x))
                (<= (norm2 x) 1)
                (< (norm2 x)
                   (useful-poly-bound poly)))
           (< 0
              (- 1
                 (* (norm2 x)
                    (/ (norm2 (car (nthcdr (lowest-exponent (cdr poly)) (cdr poly)))))
                    (norm2 (eval-polynomial (cdr (nthcdr (lowest-exponent (cdr poly)) (cdr poly))) x))))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance lowest-exponent-split-8-lemma-2)
                 )
           :in-theory (disable upper-bound-eval-poly-for-small-x
                               car-nthcdr-split-not-zero
                               eval-polynomial
                               lowest-exponent
                               SUM-NORM2-COEFFS
                               LOWEST-EXPONENT-SPLIT-6-LEMMA-4)
           )
          )
  )

(defthm lowest-exponent-split-8-lemma-4
  (implies (and (polynomial-p poly)
                (equal (car poly) 1)
                (< 1 (len poly))
                (not (equal (leading-coeff poly) 0))
                (acl2-numberp x)
                (<= 0 (norm2 x))
                (<= (norm2 x) 1)
                (< (norm2 x)
                   (useful-poly-bound poly))
                (realp s)
                (< 0 s)
                (<= s 1))
           (< 0
              (* s
                 (- 1
                    (* (norm2 x)
                       (/ (norm2 (car (nthcdr (lowest-exponent (cdr poly)) (cdr poly)))))
                       (norm2 (eval-polynomial (cdr (nthcdr (lowest-exponent (cdr poly)) (cdr poly))) x)))))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance lowest-exponent-split-8-lemma-3)
                 )
           :in-theory (disable upper-bound-eval-poly-for-small-x
                               car-nthcdr-split-not-zero
                               eval-polynomial
                               lowest-exponent
                               SUM-NORM2-COEFFS
                               LOWEST-EXPONENT-SPLIT-6-LEMMA-4)
           )
          )
  )

(defthm lowest-exponent-split-8-lemma-5
  (implies (and (polynomial-p poly)
                (equal (car poly) 1)
                (< 1 (len poly))
                (not (equal (leading-coeff poly) 0))
                (acl2-numberp x)
                (<= 0 (norm2 x))
                (<= (norm2 x) 1)
                (< (norm2 x)
                   (useful-poly-bound poly))
                (realp s)
                (< 0 s)
                (<= s 1))
           (< (- 1
                 (* s
                    (- 1
                       (* (norm2 x)
                          (/ (norm2 (car (nthcdr (lowest-exponent (cdr poly)) (cdr poly)))))
                          (norm2 (eval-polynomial (cdr (nthcdr (lowest-exponent (cdr poly)) (cdr poly))) x))))))
              1))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance lowest-exponent-split-8-lemma-4)
                 )
           :in-theory (disable upper-bound-eval-poly-for-small-x
                               car-nthcdr-split-not-zero
                               eval-polynomial
                               lowest-exponent
                               SUM-NORM2-COEFFS
                               LOWEST-EXPONENT-SPLIT-6-LEMMA-4)
           )
          )
  )

(defthm lowest-exponent-split-8
  (implies (and (polynomial-p poly)
                (equal (car poly) 1)
                (< 1 (len poly))
                (not (equal (leading-coeff poly) 0))
                (equal (car poly) 1)
                (<= (norm2 (fta-bound-1 poly s)) 1)
                (< (norm2 (fta-bound-1 poly s))
                   (useful-poly-bound poly))
                (realp s)
                (< 0 s)
                (<= s 1))
           (< (norm2 (eval-polynomial poly (fta-bound-1 poly s)))
              1))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance lowest-exponent-split-7)
                 (:instance lowest-exponent-split-8-lemma-5
                            (x (fta-bound-1 poly s)))
                 (:instance (:theorem (implies (and (realp x) (realp y) (realp z) (<= x y) (< y z)) (< x z)))
                            (x (norm2 (eval-polynomial poly (fta-bound-1 poly s))))
                            (y (- 1
                                  (* s
                                     (- 1
                                        (* (norm2 x)
                                           (/ (norm2 (car (nthcdr (lowest-exponent (cdr poly)) (cdr poly)))))
                                           (norm2 (eval-polynomial (cdr (nthcdr (lowest-exponent (cdr poly)) (cdr poly))) x)))))))
                            (z 1))
                 )
           :in-theory (disable eval-polynomial
                               fta-bound-1
                               lowest-exponent
                               nthcdr
                               leading-coeff
                               NORM2-EXPT
                               )
           )
          )
  :rule-classes nil)






(defun fta-bound-2 (poly eps)
  (* (norm2 (car (nthcdr (lowest-exponent (cdr poly)) (cdr poly))))
     (raise eps (1+ (lowest-exponent (cdr poly))))))


(defthm norm2-acl2-exp
  (implies (acl2-numberp z)
           (equal (norm2 (acl2-exp z))
                  (acl2-exp (realpart z))))
  :hints (("Goal"
           :use ((:instance complex-definition
                            (x (realpart z))
                            (y (imagpart z)))
                 (:instance exp-sum
                            (x (realpart z))
                            (y (* #c(0 1) (imagpart z))))
                 (:instance norm2-product
                            (a (acl2-exp (realpart z)))
                            (b (acl2-exp (* #c(0 1) (imagpart z)))))
                 (:instance radiuspart-e-i-theta
                            (theta (imagpart z)))
                 (:instance equal-radiuspart-norm2
                            (z (ACL2-EXP (* #C(0 1) (imagpart z)))))
                 (:instance norm2-abs
                            (x (acl2-exp (realpart z))))
                 )
           :in-theory (disable complex-definition
                               exp-sum
                               norm2-product
                               radiuspart
                               norm2-abs
                               E^IX-COS-I-SIN)
           )
          )
  :rule-classes nil)

(local
 (defthm norm2-of-e^ix
   (implies (realp x)
            (equal (norm2 (acl2-exp (* #c(0 1) x))) 1))
   :hints (("Goal"
            :use ((:instance sin**2+cos**2)
                  )
            :in-theory (e/d (norm2) (sin**2+cos**2)))
           )
   ))

(local
 (defthm norm2-of-e^ix-COROLLARY-1
   (implies (realp x)
            (equal (norm2 (acl2-exp (* #c(0 -1) x))) 1))
   :hints (("Goal"
            :use ((:instance norm2-of-e^ix (X (- X)))
                  )
            :in-theory (disable norm2-of-e^ix)
            )
           )
   ))

(local
 (defthm norm2-of-e^ix-COROLLARY-2
   (implies (realp x)
            (equal (norm2 (acl2-exp (* #c(0 2) x))) 1))
   :hints (("Goal"
            :use ((:instance norm2-of-e^ix (X (* 2 X)))
                  )
            :in-theory (disable norm2-of-e^ix)
            )
           )
   ))

(defthm norm-nth-root
  (implies (and (realp n)
                (< 0 n))
           (equal (norm2 (nth-root z n))
                  (norm2 (raise (norm2 z) (/ n)))))
  :hints (("Goal"
           :use ((:instance equal-radiuspart-norm2)
                 (:instance anglepart-e-i-theta
                            (theta (* (/ N)
                                      (ACL2-ACOS (* (/ (NORM2 Z)) (REALPART Z))))))
                 (:instance (:instance norm2-of-e^ix
                                       (X (* (/ N)
                                             (ACL2-ACOS (* (/ (NORM2 Z)) (REALPART Z)))))))
                 )
           :in-theory (disable norm2
                               radiuspart)))
  :rule-classes nil)

(defthm norm-nth-root-prod-unity
  (implies (and (realp n)
                (< 0 n)
                (acl2-numberp x)
                (acl2-numberp z)
                (equal (norm2 x) 1))
           (equal (norm2 (nth-root (* z x) n))
                  (norm2 (raise (norm2 z) (/ n)))))
  :hints (("Goal"
           :use ((:instance norm-nth-root (z (* z x)))
                 (:instance norm2-product (a z) (b x))
                 )
           :in-theory (disable norm2-product
                               raise nth-root)))
  :rule-classes nil
  )

(defthm norm-nth-root-uminus
  (implies (and (realp n)
                (< 0 n))
           (equal (norm2 (nth-root (- z) n))
                  (norm2 (nth-root z n))))
  :hints (("Goal"
           :use ((:instance norm-nth-root)
                 (:instance norm-nth-root (z (- z)))
                 )
           :in-theory '(norm2-uminus))))

(defthm raise-not-zero
  (implies (and (realp eps)
                (< 0 eps)
                (realp n)
                (< 0 n))
           (< 0 (raise eps n)))
  :hints (("Goal"
           :use ((:instance acl2-exp->-0-for-reals (x (* eps (acl2-ln n))))
                 )
           :in-theory (disable acl2-exp->-0-for-reals
                               E^IX-COS-I-SIN
                               RADIUSPART)))
  )

(defthm realp-raise
  (implies (and (realp eps)
                (< 0 eps)
                (realp n)
                (< 0 n))
           (realp (raise eps n)))
  )

(defthm raise-exp
  (implies (and (realp x)
                (realp y)
                )
           (equal (raise (acl2-exp x) y)
                  (acl2-exp (* x y))))
  )

(defthm raise-raise
  (implies (and (realp a)
                (< 0 a)
                (realp x)
                (realp y)
                )
           (equal (raise (raise a x) y)
                  (raise a (* x y))))
  :hints (("Goal"
           :use ((:instance ln-exp
                            (x (* x (acl2-ln a))))
                 (:instance realp-ln (y a))
                 )
           :in-theory (disable ln-exp realp-ln)
           )
          )
  )
  
(defthm nth-root-raise-lemma-1
  (implies (and (realp eps)
                (< 0 eps)
                (realp n)
                (< 0 n))
           (equal (nth-root (raise eps n) n)
                  eps))
  :hints (("Goal"
           :use ((:instance acl2-exp->-0-for-reals (x eps))
                 (:instance anglepart-of-realp
                            (x (raise eps n)))
                 )
           :in-theory (disable raise
                               acl2-exp->-0-for-reals
                               E^IX-COS-I-SIN
                               anglepart-of-realp
                               RADIUSPART
                               ANGLEPART)))
  )


(defthm norm-fta-bound-2-lemma-1
  (implies (and (realp eps)
                (< 0 eps)
                (realp n)
                (< 0 n))
           (equal (norm2 (nth-root (raise eps n) n))
                  eps))
  :hints (("Goal"
           :use ((:instance nth-root-raise-lemma-1)
                 (:instance norm2-abs (x eps))
                 )
           :in-theory (disable nth-root-raise-lemma-1 norm2-abs)
           )
          )
  )

(defthm norm-of-unit
  (implies (and (acl2-numberp z)
                (not (equal z 0)))
           (equal (norm2 (* (/ z) (norm2 z))) 1))
  )

(defthm norm2-raise-pos-args
  (implies (and (realp eps)
                (< 0 eps)
                (realp n)
                (< 0 n))
           (equal (norm2 (raise eps n))
                  (raise eps n)))
  :hints (("Goal"
           :use ((:instance realp-raise)
                 (:instance norm2-abs
                            (x (raise eps n)))
                 )
           :in-theory (disable realp-raise
                               norm2-abs
                               raise))))

(defthm raise-to-the-1
  (implies (acl2-numberp z)
           (equal (raise z 1) z))
  )

(defthm norm-fta-bound-2-lemma
  (implies (and (realp eps)
                (< 0 eps)
                (polynomial-p poly)
                (< 1 (len poly))
                (not (equal (leading-coeff poly) 0)))
           (<= (norm2 (fta-bound-1 poly (fta-bound-2 poly eps))) eps))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (disable norm2-expt norm2-product expt-x*y^n
                               nth-root raise raise-expt
                               POWER-OF-SUMS
                               LEADING-COEFF
                               E^IX-COS-I-SIN NTH-ROOT raise))
          ("Subgoal 2"
           :use ((:instance norm-nth-root-uminus
                            (z (raise eps (+ 1 (lowest-exponent (cdr poly)))))
                            (n (1+ (lowest-exponent (cdr poly)))))
                 (:instance norm-fta-bound-2-lemma-1
                            (n (1+ (lowest-exponent (cdr poly)))))
                 (:instance norm-nth-root-prod-unity
                            (x (* (/ (CAR (NTHCDR (LOWEST-EXPONENT (CDR POLY))
                                                  (CDR POLY))))
                                  (NORM2 (CAR (NTHCDR (LOWEST-EXPONENT (CDR POLY))
                                                      (CDR POLY))))))
                            (z (RAISE EPS (+ 1 (LOWEST-EXPONENT (CDR POLY)))))
                            (n (+ 1 (LOWEST-EXPONENT (CDR POLY)))))
                 (:instance norm-of-unit
                            (z (CAR (NTHCDR (LOWEST-EXPONENT (CDR POLY))
                                            (CDR POLY)))))
                 (:instance car-nthcdr-split-not-zero (poly (cdr poly)))
                 (:instance leading-coeff-cdr-poly)
                 )
           :in-theory (disable norm2-expt norm2-product expt-x*y^n
                               nth-root raise raise-expt
                               norm-of-unit
                               car-nthcdr-split-not-zero
                               POWER-OF-SUMS
                               E^IX-COS-I-SIN NTH-ROOT raise
                               lowest-exponent
                               leading-coeff
                               norm-fta-bound-2-lemma-1
                               ;polynomial-p
                               NORM-FTA-BOUND-2-LEMMA-1
                               NTH-ROOT-RAISE-LEMMA-1))
          ("Subgoal 1"
           :use ((:instance car-nthcdr-split-not-zero (poly (cdr poly)))
                 (:instance leading-coeff-cdr-poly))
           :in-theory (disable norm2-expt norm2-product expt-x*y^n
                               nth-root raise raise-expt
                               norm-of-unit
                               car-nthcdr-split-not-zero
                               POWER-OF-SUMS
                               E^IX-COS-I-SIN NTH-ROOT raise
                               lowest-exponent
                               leading-coeff
                               norm-fta-bound-2-lemma-1
                               ;polynomial-p
                               NORM-FTA-BOUND-2-LEMMA-1
                               NTH-ROOT-RAISE-LEMMA-1))
          )
  :rule-classes nil)
    
(defthm imagpart-acl2-ln
  (equal (imagpart (acl2-ln z))
         (anglepart z))
  :hints (("Goal"
           :expand (acl2-ln z))
          )
  )

(defthm ln-product-lemma-1
  (equal (IMAGPART (* #C(0 -2) (ACL2-PI)))
         (- (* 2 (acl2-pi))))
  :hints (("Goal"
           :use ((:instance complex-definition
                            (x 0)
                            (y (- (* 2 (acl2-pi)))))
                 )
           :in-theory (disable complex-definition
                               complex-0-b))
          )
  )

(defthm ln-product-lemma-2
  (equal (ACL2-COSINE (* -2 (ACL2-PI))) 1)
  :hints (("Goal"
           :use ((:instance cos-uminus
                            (x (* 2 (ACL2-PI))))
                 )
           :in-theory (disable cos-uminus)
           )
          )
  )

(defthm ln-product-lemma-3
  (equal (ACL2-SINE (* -2 (ACL2-PI))) 0)
  :hints (("Goal"
           :use ((:instance sin-uminus
                            (x (* 2 (ACL2-PI))))
                 )
           :in-theory (disable sin-uminus)
           )
          )
  )

(defthm ln-product-lemma-4
  (equal (ACL2-EXP (* #C(0 -2) (ACL2-PI))) 1)
  :hints (("Goal"
           :use ((:instance E^IX-COS-I-SIN
                            (x (* -2 (acl2-pi))))
                 )
           :in-theory (disable  E^IX-COS-I-SIN)
           )
          )
  )


(defthm ln-product
  (implies (and (acl2-numberp x)
                (acl2-numberp y)
                (not (equal (* x y) 0)))
           (equal (acl2-ln (* x y))
                  (if (< (+ (anglepart x)
                            (anglepart y))
                         (* 2 (acl2-pi)))
                      (+ (acl2-ln x)
                         (acl2-ln y))
                    (- (+ (acl2-ln x)
                          (acl2-ln y))
                       (complex 0 (* 2 (acl2-pi)))))))
  :hints (("Goal"
           :use ((:instance uniqueness-of-ln
                            (x (+ (acl2-ln x)
                                  (acl2-ln y)))
                            (y (* x y)))
                 (:instance uniqueness-of-ln
                            (x (- (+ (acl2-ln x)
                                     (acl2-ln y))
                                  (complex 0 (* 2 (acl2-pi)))))
                            (y (* x y)))
                 (:instance anglepart-between-0-and-2pi
                            (x x))
                 (:instance anglepart-between-0-and-2pi
                            (x y))
                 )
           :in-theory (disable uniqueness-of-ln
                               anglepart-between-0-and-2pi
                               radiuspart
                               anglepart
                               )
           )
          )
  )

  
(encapsulate
 ()

 (local
  (defun induction-hint (n)
    (if (and (integerp n)
	     (< 0 n))
	(1+ (induction-hint (+ n -1)))
      1)))

 (local
  (defthm cos-2npi-n>=0
    (implies (and (integerp n)
		  (<= 0 n))
	     (equal (acl2-cosine (* 2 (acl2-pi) n))
		    1))
    :hints (("Goal"
	     :induct (induction-hint n)))))

 (defthm cos-2npi
   (implies (integerp n)
	    (equal (acl2-cosine (* 2 (acl2-pi) n))
		   1))
   :hints (("Goal"
	    :cases ((< n 0)
		    (= n 0)
		    (> n 0)))
	   ("Subgoal 3"
	    :use ((:instance cos-uminus
			     (x (* 2 (acl2-pi) n)))
		  (:instance cos-2npi-n>=0 (n (- n))))
	    :in-theory (disable cos-uminus cos-2npi-n>=0))))

 )


(defthm raise-product-lemma
  (implies (integerp n)
           (equal (ACL2-EXP (* (COMPLEX 0 (* 2 (ACL2-PI))) N)) 1))
  :hints (("Goal"
           :use ((:instance complex-definition
                            (x 0)
                            (y (* 2 (ACL2-PI) n)))
                 (:instance E^IX-COS-I-SIN
                            (x (* 2 (acl2-pi) n)))
                 )
           :in-theory (disable complex-definition E^IX-COS-I-SIN SINE-2X))
          )
  )
  
         

(defthm raise-product
  (implies (integerp n)
           (equal (raise (* x y) n)
                  (* (raise x n)
                     (raise y n))))
  :hints (("Goal"
           :use ((:instance exp-sum
                            (x (* n (acl2-ln x)))
                            (y (* n (acl2-ln y))))
                 (:instance exp-sum
                            (x (- (* (COMPLEX 0 (* 2 (ACL2-PI))) N)))
                            (y (+ (* N (ACL2-LN X)) (* N (ACL2-LN Y)))))
                 )
           :in-theory (disable exp-sum
                               COMPLEX-0-B
                               radiuspart
                               anglepart)
           )
          )
  :rule-classes nil
  )


(defthm norm2-raise-product-lemma
  (implies (realp n)
           (equal (norm2 (ACL2-EXP (* (COMPLEX 0 (* 2 (ACL2-PI))) N))) 1))
  :hints (("Goal"
           :use ((:instance norm2-of-e^ix
                            (x (* 2 (acl2-pi) n)))
                 )
           :in-theory (disable norm2-of-e^ix))))

(defthm norm2-exp-sum
  (implies (and (acl2-numberp x)
                (acl2-numberp y))
           (equal (norm2 (acl2-exp (+ x y)))
                  (* (norm2 (acl2-exp x))
                     (norm2 (acl2-exp y)))))
  )

(defthm norm2-raise-product
  (implies (realp n)
           (equal (norm2 (raise (* x y) n))
                  (* (norm2 (raise x n))
                     (norm2 (raise y n)))))
  :hints (("Goal"
           :use ((:instance norm2-exp-sum
                            (x (* n (acl2-ln x)))
                            (y (* n (acl2-ln y))))
                 (:instance norm2-exp-sum
                            (x (- (* (COMPLEX 0 (* 2 (ACL2-PI))) N)))
                            (y (+ (* N (ACL2-LN X)) (* N (ACL2-LN Y)))))
                 )
           :in-theory (disable exp-sum
                               norm2-exp-sum
                               COMPLEX-0-B
                               radiuspart
                               anglepart)
           )
          )
  :rule-classes nil
  )
  

(defthm norm2-bound-1-lemma-1
  (equal (norm2 (fta-bound-1 poly s))
         (norm2 (raise (norm2 (- (* S
                                    (/ (CAR (NTHCDR (LOWEST-EXPONENT (CDR POLY))
                                                    (CDR POLY)))))))
                       (/ (1+ (LOWEST-EXPONENT (CDR POLY)))))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance equal-radiuspart-norm2
                            (z (- (* S
                                     (/ (CAR (NTHCDR (LOWEST-EXPONENT (CDR POLY))
                                                     (CDR POLY))))))))
                 (:instance car-nthcdr-split-not-zero (poly (cdr poly)))
                 )
           :in-theory (disable lowest-exponent
                               car-nthcdr-split-not-zero
                               raise
                               RADIUSPART
                               LOWEST-EXPONENT-SPLIT-6-LEMMA-4
                               E^IX-COS-I-SIN))))

(defthm norm2-bound-1-lemma-2
  (equal (norm2 (- (* S
                      (/ (CAR (NTHCDR (LOWEST-EXPONENT (CDR POLY))
                                      (CDR POLY)))))))
         (* (norm2 s)
            (norm2 (/ (CAR (NTHCDR (LOWEST-EXPONENT (CDR POLY))
                                   (CDR POLY)))))))
  )

(defthm norm2-bound-1-lemma-3
  (implies (and (polynomial-p poly)
                (equal (car poly) 1)
                (< 1 (len poly))
                (not (equal (leading-coeff poly) 0)))
           (equal (norm2 (fta-bound-1 poly s))
                  (norm2 (raise (* (norm2 S)
                                   (norm2 (/ (CAR (NTHCDR (LOWEST-EXPONENT (CDR POLY))
                                                          (CDR POLY))))))
                                (/ (1+ (LOWEST-EXPONENT (CDR POLY))))))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance norm2-bound-1-lemma-1)
                 (:instance norm2-bound-1-lemma-2)         
                 )
           :in-theory (disable norm2-bound-1-lemma-1
                               norm2-bound-1-lemma-1
                               ))))

(defthm norm2-bound-1-lemma-4
  (implies (and (polynomial-p poly)
                (equal (car poly) 1)
                (< 1 (len poly))
                (not (equal (leading-coeff poly) 0)))
           (equal (norm2 (fta-bound-1 poly s))
                  (* (norm2 (raise (norm2 S) (/ (1+ (LOWEST-EXPONENT (CDR POLY))))))
                     (norm2 (raise (norm2 (/ (CAR (NTHCDR (LOWEST-EXPONENT (CDR POLY))
                                                          (CDR POLY)))))
                                   (/ (1+ (LOWEST-EXPONENT (CDR POLY)))))))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance norm2-bound-1-lemma-3)
                 (:instance norm2-raise-product
                            (x (norm2 S))
                            (y (norm2 (/ (CAR (NTHCDR (LOWEST-EXPONENT (CDR POLY))
                                                      (CDR POLY))))))
                            (n (/ (1+ (LOWEST-EXPONENT (CDR POLY))))))
                 )
           :in-theory (disable norm2-bound-1-lemma-3
                               ANGLEPART
                               raise
                               FTA-BOUND-1
                               LEADING-COEFF
                               LOWEST-EXPONENT
                               RADIUSPART
                               ))))
         

(defthm ln-monotonic
  (implies (and (realp x)
                (realp y)
                (< 0 x)
                (< x y))
           (< (acl2-ln x)
              (acl2-ln y)))
  :hints (("Goal"
           :use ((:instance acl2-exp-is-non-decreasing
                            (x (acl2-ln y))
                            (y (acl2-ln x)))
                 (:instance exp-ln (y x))
                 (:instance exp-ln (y y))
                 )
           :in-theory (disable acl2-exp-is-non-decreasing exp-ln))
          )
  )


(defthm raise-monotonic
  (implies (and (realp s1)
                (realp s2)
                (< 0 s1)
                (< s1 s2)
                (realp n)
                (< 0 n))
           (< (raise s1 n)
              (raise s2 n)))
  :hints (("Goal"
           :use ((:instance acl2-exp-is-non-decreasing
                            (x (* n (acl2-ln s1)))
                            (y (* n (acl2-ln s2))))
                 (:instance ln-monotonic
                            (x s1)
                            (y s2))
                 )
           :in-theory (disable acl2-exp-is-non-decreasing ln-monotonic)
           )
          )
  )

(defthm raise-is-positive-for-positive-args
  (implies (and (realp x)
                (realp n)
                (< 0 x)
                (< 0 n))
           (< 0 (raise x n))))

(defthm fta-bound-1-has-positive-norm
  (implies (and (polynomial-p poly)
                (equal (car poly) 1)
                (< 1 (len poly))
                (not (equal (leading-coeff poly) 0))
                (acl2-numberp s)
                (not (equal s 0)))
           (< 0 (norm2 (fta-bound-1 poly s))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance norm2-bound-1-lemma-4)
                 (:instance car-nthcdr-split-not-zero (poly (cdr poly)))
                 )
           :in-theory (disable norm2-bound-1-lemma-1
                               norm2-bound-1-lemma-2
                               norm2-bound-1-lemma-3
                               norm2-bound-1-lemma-4
                               car-nthcdr-split-not-zero
                               fta-bound-1)
           )
          )
  )

(defthm fta-bound-1-non-zero
  (implies (and (polynomial-p poly)
                (equal (car poly) 1)
                (< 1 (len poly))
                (not (equal (leading-coeff poly) 0))
                (acl2-numberp s)
                (not (equal s 0)))
           (not (equal (fta-bound-1 poly s) 0)))
  :hints (("Goal"
           :use ((:instance fta-bound-1-has-positive-norm)
                 (:instance norm2-zero-for-zero-only (x (fta-bound-1 poly s)))
                 )
           :in-theory (disable fta-bound-1-has-positive-norm
                               norm2-zero-for-zero-only
                               norm2-bound-1-lemma-1
                               norm2-bound-1-lemma-2
                               norm2-bound-1-lemma-3
                               norm2-bound-1-lemma-4
                               car-nthcdr-split-not-zero
                               fta-bound-1)
           )
          )
  )


(defthm bound-1-monotonic
  (implies (and (polynomial-p poly)
                (equal (car poly) 1)
                (< 1 (len poly))
                (not (equal (leading-coeff poly) 0))
                (acl2-numberp s1)
                (acl2-numberp s2)
                (< 0 (norm2 s1))
                (< (norm2 s1) (norm2 s2)))
           (< (norm2 (fta-bound-1 poly s1))
              (norm2 (fta-bound-1 poly s2))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance norm2-bound-1-lemma-4 (s s1))
                 (:instance norm2-bound-1-lemma-4 (s s2))
                 (:instance car-nthcdr-split-not-zero)
                 (:instance car-nthcdr-split-not-zero (poly (cdr poly)))
                 (:instance leading-coeff-cdr-poly)
                 (:instance fta-bound-1-non-zero (s s1))
                 (:instance fta-bound-1-non-zero (s s2))
                 (:instance norm2-zero-for-zero-only
                            (x (FTA-BOUND-1 POLY S1)))
                 (:instance norm2-zero-for-zero-only
                            (x (FTA-BOUND-1 POLY S2)))
                 (:instance raise-is-positive-for-positive-args
                            (x (norm2 s1))
                            (n (/ (+ 1 (LOWEST-EXPONENT (CDR POLY))))))
                 (:instance raise-is-positive-for-positive-args
                            (x (norm2 s2))
                            (n (/ (+ 1 (LOWEST-EXPONENT (CDR POLY))))))
                 (:instance raise-monotonic
                            (s1 (norm2 s1))
                            (s2 (norm2 s2))
                            (n (/ (1+ (LOWEST-EXPONENT (CDR POLY))))))
                 (:instance realp-raise
                            (eps (norm2 s1))
                            (n (/ (+ 1 (LOWEST-EXPONENT (CDR POLY))))))
                 (:instance realp-raise
                            (eps (norm2 s2))
                            (n (/ (+ 1 (LOWEST-EXPONENT (CDR POLY))))))
                 (:instance norm2-abs
                            (x (raise (norm2 s1) (/ (+ 1 (LOWEST-EXPONENT (CDR POLY)))))))
                 (:instance norm2-abs
                            (x (raise (norm2 s2) (/ (+ 1 (LOWEST-EXPONENT (CDR POLY)))))))
                 (:instance (:theorem
                             (implies (and (realp x1) (realp x2) (realp y) (< x1 x2) (< 0 y)) (< (* x1 y) (* x2 y))))
                            (x1 (raise (norm2 s1)
                                       (/ (+ 1 (lowest-exponent (cdr poly))))))
                            (x2 (raise (norm2 s2)
                                       (/ (+ 1 (lowest-exponent (cdr poly))))))
                            (y (norm2 (raise (norm2 (/ (car (nthcdr (lowest-exponent (cdr poly))
                                                                    (cdr poly)))))
                                             (/ (+ 1 (lowest-exponent (cdr poly)))))))
                            )
                 )
           :in-theory (disable raise
                               LEADING-COEFF
                               RAISE-NOT-ZERO
                               RAISE-IS-POSITIVE-FOR-POSITIVE-ARGS
                               norm2-zero-for-zero-only
                               fta-bound-1-non-zero
                               lowest-exponent
                               nth-root
                               fta-bound-1
                               realp-raise
                               raise-expt
                               norm2-abs
                               car-nthcdr-split-not-zero
                               NORM2-ZERO-FOR-ZERO-ONLY
                               NORM2-BOUND-1-LEMMA-1
                               NORM2-BOUND-1-LEMMA-2
                               NORM2-BOUND-1-LEMMA-3
                               norm2-bound-1-lemma-4
                               raise-monotonic)
           )
          )
  )

(defthm norm-fta-bound-2
  (implies (and (realp eps)
                (< 0 eps)
                (polynomial-p poly)
                (< 1 (len poly))
                (equal (car poly) 1)
                (not (equal (leading-coeff poly) 0))
                (realp s)
                (< 0 s)
                (< s (norm2 (fta-bound-2 poly eps))))
           (< (norm2 (fta-bound-1 poly s)) eps))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance norm-fta-bound-2-lemma)
                 (:instance bound-1-monotonic
                            (s1 s)
                            (s2 (fta-bound-2 poly eps)))
                 )
           :in-theory (disable fta-bound-1
                               FTA-BOUND-2
                               LEADING-COEFF
                               LOWEST-EXPONENT
                               RAISE
                               NORM2-BOUND-1-LEMMA-1
                               NORM2-BOUND-1-LEMMA-2
                               NORM2-BOUND-1-LEMMA-3
                               NORM2-BOUND-1-LEMMA-4
                               bound-1-monotonic))
          )
  )


(defthm realp-fta-bound-2
  (implies (realp eps)
           (realp (fta-bound-2 poly eps))))

(defthm posp-fta-bound-2
  (implies (and (polynomial-p poly)
                (equal (car poly) 1)
                (< 1 (len poly))
                (not (equal (leading-coeff poly) 0))
                (realp eps)
                (< 0 eps))
           (< 0 (fta-bound-2 poly eps)))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance norm2-zero-for-zero-only
                            (x (car (nthcdr (lowest-exponent (cdr poly))
                                            (cdr poly)))))
                 (:instance car-nthcdr-split-not-zero (poly (cdr poly)))
                 (:instance leading-coeff-cdr-poly)
                 (:instance realp-raise
                            (eps eps)
                            (n (1+ (LOWEST-EXPONENT (CDR POLY)))))
                 )
           :in-theory (disable norm2-zero-for-zero-only
                               car-nthcdr-split-not-zero
                               realp-raise
                               leading-coeff
                               lowest-exponent
                               )
           )
          )
  )

(defthm lowest-exponent-split-9
  (implies (and (polynomial-p poly)
                (equal (car poly) 1)
                (< 1 (len poly))
                (not (equal (leading-coeff poly) 0))
                (equal (car poly) 1)
                (realp s)
                (< 0 s)
                (< s 1)
                (< s (fta-bound-2 poly (useful-poly-bound poly)))
                (< s (fta-bound-2 poly 1))
                )
           (< (norm2 (eval-polynomial poly (fta-bound-1 poly s)))
              1))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance lowest-exponent-split-8)
                 (:instance norm-fta-bound-2
                            (eps (useful-poly-bound poly)))
                 (:instance norm-fta-bound-2
                            (eps 1))
                 (:instance norm-fta-bound-2
                            (eps (fta-bound-2 poly (useful-poly-bound poly))))
                 (:instance useful-poly-bound-is-real)
                 )
           :in-theory (disable useful-poly-bound
                               useful-poly-bound-is-real
                               norm-fta-bound-2
                               fta-bound-1
                               FTA-BOUND-2
                               LEADING-COEFF
                               LOWEST-EXPONENT
                               RAISE
                               NORM2-BOUND-1-LEMMA-1
                               NORM2-BOUND-1-LEMMA-2
                               NORM2-BOUND-1-LEMMA-3
                               NORM2-BOUND-1-LEMMA-4
                               bound-1-monotonic))
          )
  :rule-classes nil)

(defun input-with-smaller-value (poly)
  (let ((m1 1)
        (m2 (fta-bound-2 poly (useful-poly-bound poly)))
        (m3 (fta-bound-2 poly 1)))
    (/ (min (min m1 m2) m3) 2)))

(defthm realp-input-with-smaller-value
  (realp (input-with-smaller-value poly)))

(defthm input-with-smaller-value-is-positive
  (implies (and (polynomial-p poly)
                (equal (car poly) 1)
                (< 1 (len poly))
                (not (equal (leading-coeff poly) 0)))
           (< 0 (input-with-smaller-value poly)))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance posp-fta-bound-2 (eps 1))
                 (:instance posp-fta-bound-2 (eps (fta-bound-2 poly (useful-poly-bound poly))))
                 (:instance posp-fta-bound-2 (eps (useful-poly-bound poly)))
                 (:instance posp-fta-bound-2 (eps (fta-bound-2 poly 1)))
                 (:instance useful-poly-bound-is-positive)
                 )
           :in-theory (disable fta-bound-2
                               posp-fta-bound-2
                               useful-poly-bound-is-positive)
           )
          )
  )

(defthm lowest-exponent-split-10
  (implies (and (polynomial-p poly)
                (equal (car poly) 1)
                (< 1 (len poly))
                (not (equal (leading-coeff poly) 0))
                (equal (car poly) 1)
                )
           (< (norm2 (eval-polynomial poly (fta-bound-1 poly (input-with-smaller-value poly))))
              1))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance realp-input-with-smaller-value)
                 (:instance input-with-smaller-value-is-positive)
                 (:instance lowest-exponent-split-9
                            (s (input-with-smaller-value poly)))
                 )
           :in-theory (disable realp-input-with-smaller-value
                               input-with-smaller-value-is-positive
                               leading-coeff
                               polynomial-p
                               fta-bound-1
                               fta-bound-2
                               useful-poly-bound)
           )
          )
  :rule-classes nil)

(in-theory (disable input-with-smaller-value))
  
(defthm lowest-exponent-split-11
  (implies (and (polynomial-p poly)
                (equal (car poly) 1)
                (< 1 (len poly))
                (not (equal (leading-coeff poly) 0))
                (equal (car poly) 1)
                )
           (< (norm2 (eval-polynomial poly (fta-bound-1 poly (input-with-smaller-value poly))))
              (norm2 (eval-polynomial poly 0))))
  :hints (("Goal"
           :expand (eval-polynomial poly 0)
           :use ((:instance lowest-exponent-split-10))))
  :rule-classes nil)


(defun minimum-counter-example (poly)
  (fta-bound-1 poly (input-with-smaller-value poly)))

(defthm leading-coeff-scale-poly
  (implies (and (polynomial-p poly)
                (acl2-numberp z)
                (not (equal z 0))
                (not (equal (leading-coeff poly) 0)))
           (not (equal (leading-coeff (scale-polynomial poly z)) 0)))
  )

(defthm car-scale-polynomial
  (implies (and (polynomial-p poly)
                (< 1 (len poly))
                (not (equal (car poly) 0)))
           (EQUAL (CAR (SCALE-POLYNOMIAL POLY (/ (CAR POLY))))
                  1))
  :hints (("Goal"
           :do-not-induct t
           :expand (SCALE-POLYNOMIAL POLY (/ (CAR POLY)))
           )
          ))

(defthm lowest-exponent-split-12
  (implies (and (polynomial-p poly)
                (not (equal (car poly) 0))
                (< 1 (len poly))
                (not (equal (leading-coeff poly) 0))
                )
           (< (norm2 (eval-polynomial poly
                                      (minimum-counter-example (scale-polynomial poly
                                                                                 (/ (car poly))))))
              (norm2 (eval-polynomial poly 0))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance lowest-exponent-split-11
                            (poly (scale-polynomial poly (/ (car poly)))))
                 (:instance eval-scale-polynomial
                            (poly poly)
                            (c (/ (car poly)))
                            (x (eval-polynomial poly
                                      (minimum-counter-example (scale-polynomial poly
                                                                                 (/ (car poly)))))))
                 (:instance eval-scale-polynomial
                            (poly poly)
                            (c (/ (car poly)))
                            (x 0))
                 )
           :in-theory (disable leading-coeff
                               eval-polynomial
                               scale-polynomial
                               ;minimum-counter-example
                               fta-bound-1)))
  :rule-classes nil)

(defthm lowest-exponent-split-13
  (implies (and (polynomial-p poly)
                (not (equal (eval-polynomial poly 0) 0))
                (< 1 (len poly))
                (not (equal (leading-coeff poly) 0))
                )
           (< (norm2 (eval-polynomial poly
                                      (minimum-counter-example (scale-polynomial poly
                                                                                 (/ (car poly))))))
              (norm2 (eval-polynomial poly 0))))
  :hints (("Goal"
           :do-not-induct t
           :expand (eval-polynomial poly 0)
           :use ((:instance lowest-exponent-split-12))))
  :rule-classes nil)

(defthm lowest-exponent-split-14
  (implies (and (polynomial-p poly)
                (acl2-numberp z)
                (not (equal (eval-polynomial poly z) 0))
                (< 1 (len poly))
                (not (equal (leading-coeff poly) 0))
                )
           (< (norm2 (eval-polynomial poly
                                      (+ (minimum-counter-example (scale-polynomial (shift-polynomial poly z)
                                                                                    (/ (car (shift-polynomial poly z)))))
                                         z)))
              (norm2 (eval-polynomial poly z))))
  :hints (("Goal"
           :do-not-induct t
           :expand (eval-polynomial poly 0)
           :use ((:instance lowest-exponent-split-13
                            (poly (shift-polynomial poly z))
                            )
                 (:instance EVAL-SHIFT-POLYNOMIAL
                            (z (minimum-counter-example (scale-polynomial (shift-polynomial poly z)
                                                                          (/ (car (shift-polynomial poly z)))))
                                  )
                            (dx z))
                 (:instance EVAL-SHIFT-POLYNOMIAL
                            (z 0)
                            (dx z))
                 (:instance leading-coeff-shift-polynomial
                            (dx z))
                 )
           :in-theory (disable EVAL-SHIFT-POLYNOMIAL
                               leading-coeff-shift-polynomial
                               norm2
                               anglepart
                               minimum-counter-example
                               eval-polynomial
                               scale-polynomial
                               shift-polynomial)
           ))
  :rule-classes nil)


(defun minimum-counter-example-general (poly z)
  (+ (minimum-counter-example (scale-polynomial (shift-polynomial poly z)
                                                (/ (car (shift-polynomial poly z)))))
     z))

(defthm lowest-exponent-split-15
  (implies (and (polynomial-p poly)
                (acl2-numberp z)
                (not (equal (eval-polynomial poly z) 0))
                (< 1 (len poly))
                (not (equal (leading-coeff poly) 0))
                )
           (< (norm2 (eval-polynomial poly (minimum-counter-example-general poly z)))
              (norm2 (eval-polynomial poly z))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance lowest-exponent-split-14)
                 )
           :in-theory '(minimum-counter-example-general)
           ))
  :rule-classes nil)


(defun zero-polynomial-p (poly)
  (if (consp poly)
      (and (equal (car poly) 0)
           (zero-polynomial-p (cdr poly)))
    (null poly)))

(defthm eval-zero-polynomial-p
  (implies (zero-polynomial-p poly)
           (equal (eval-polynomial poly z) 0)))

(defun truncate-polynomial (poly)
  (if (consp poly)
      (if (zero-polynomial-p poly)
          nil
        (cons (car poly)
              (truncate-polynomial (cdr poly))))
    nil))

(defthm eval-truncate-polynomial
  (equal (eval-polynomial (truncate-polynomial poly) z)
         (eval-polynomial poly z)))

(defthm leading-coeff-truncate-polynomial
  (implies (and (polynomial-p poly)
                (not (zero-polynomial-p poly)))
           (not (equal (leading-coeff (truncate-polynomial poly)) 0))))

(defun constant-polynomial-p (poly)
  (and (polynomial-p poly)
       (or (not (consp poly))
           (zero-polynomial-p (cdr poly)))))

(defthm not-constant-polynomial-has-len-2+
  (implies (and (polynomial-p poly)
                (not (constant-polynomial-p poly)))
           (< 1 (len poly))))
        
(defthm polynomial-p-truncate-polynomial
  (implies (polynomial-p poly)
           (polynomial-p (truncate-polynomial poly))))

(defthm leading-coeff-len-1
  (equal (LEADING-COEFF (LIST (CAR POLY))) (car poly)))

(defthm len-truncate-polynomial
  (implies (and (polynomial-p poly)
                (not (constant-polynomial-p poly)))
           (< 1 (len (truncate-polynomial poly)))))



(defthm lowest-exponent-split-16
  (implies (and (polynomial-p poly)
                (not (constant-polynomial-p poly))
                (acl2-numberp z)
                (not (equal (eval-polynomial poly z) 0)))
           (< (norm2 (eval-polynomial poly
                                      (minimum-counter-example-general (truncate-polynomial poly) z)))
              (norm2 (eval-polynomial poly z))))
  :hints (("Goal"
           :do-not-induct t
           :expand (eval-polynomial poly 0)
           :use ((:instance lowest-exponent-split-15
                            (poly (truncate-polynomial poly)))
                 (:instance not-constant-polynomial-has-len-2+)
                 (:instance len-truncate-polynomial)
                 )
           :in-theory (disable leading-coeff
                               not-constant-polynomial-has-len-2+
                               EVAL-POLYNOMIAL
                               len-truncate-polynomial
                               minimum-counter-example
                               scale-polynomial
                               truncate-polynomial))
          )
  :rule-classes nil)

(defun minimum-counter-example-trunc (poly z)
  (minimum-counter-example-general (truncate-polynomial poly) z))

(defthm lowest-exponent-split-17
  (implies (and (polynomial-p poly)
                (not (constant-polynomial-p poly))
                (acl2-numberp z)
                (not (equal (eval-polynomial poly z) 0)))
           (< (norm2 (eval-polynomial poly
                                      (minimum-counter-example-trunc poly z)))
              (norm2 (eval-polynomial poly z))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance lowest-exponent-split-16)
                 )
           :in-theory '(minimum-counter-example-trunc))
          )
  :rule-classes nil)

(defthm not-a-minimum-point-for-non-constant-polynomial
    (implies (and (polynomial-p poly)
                (not (constant-polynomial-p poly))
                (acl2-numberp z)
                (not (equal (eval-polynomial poly z) 0)))
             (not (norm-eval-poly-is-minimum-point-globally poly z)))
    :hints (("Goal"
             :use ((:instance norm-eval-poly-is-minimum-point-globally-necc
                                (z (minimum-counter-example-trunc poly z))
                                (zmin z))
                     (:instance lowest-exponent-split-17))
             :in-theory (disable norm-eval-poly-is-minimum-point-globally-necc
                                 eval-polynomial
                                 minimum-counter-example-trunc norm2))))

(defthm constant-polynomial-conditions
    (implies (and (polynomial-p poly)
                  (not (constant-polynomial-p poly)))
             (and (polynomial-p (truncate-polynomial poly))
                  (< 1 (len (truncate-polynomial poly)))
                  (not (equal (leading-coeff (truncate-polynomial poly)) 0))))
    )

(defthm norm-eval-poly-truncate-poly
  (equal (norm-eval-polynomial (truncate-polynomial poly) z)
         (norm-eval-polynomial poly z))
  :hints (("Goal" :in-theory (disable eval-polynomial))))

(defthm norm-eval-poly-is-minimum-point-globally-truncate-poly-1
  (implies (and (norm-eval-poly-is-minimum-point-globally
                 (truncate-polynomial poly)
                 zmin)
                (acl2-numberp z))
           (<= (norm-eval-polynomial poly zmin)
               (norm-eval-polynomial poly z)))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance norm-eval-poly-is-minimum-point-globally-necc
                            (poly (truncate-polynomial poly))
                            (zmin zmin)
                            (z z))
                 )
           :in-theory (disable norm-eval-polynomial
                               norm-eval-poly-is-minimum-point-globally-necc))
          )
  :rule-classes nil
  )

(defthm norm-eval-poly-is-minimum-point-globally-truncate-poly-2
  (implies (norm-eval-poly-is-minimum-point-globally
            (truncate-polynomial poly)
            zmin)
           (norm-eval-poly-is-minimum-point-globally poly zmin))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance norm-eval-poly-is-minimum-point-globally-truncate-poly-1
                            (z (norm-eval-poly-is-minimum-point-globally-witness poly zmin)))
                 )
           :in-theory (disable norm-eval-polynomial
                               norm-eval-poly-is-minimum-point-globally-necc))
          )
  :rule-classes nil
  )

(defthm norm-eval-poly-is-minimum-point-globally-truncate-poly-3
  (implies (and (norm-eval-poly-is-minimum-point-globally poly zmin)
                (acl2-numberp z))
           (<= (norm-eval-polynomial (truncate-polynomial poly) zmin)
               (norm-eval-polynomial (truncate-polynomial poly) z)))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance norm-eval-poly-is-minimum-point-globally-necc
                            (poly poly)
                            (zmin zmin)
                            (z z))
                 )
           :in-theory (disable norm-eval-polynomial
                               norm-eval-poly-is-minimum-point-globally-necc))
          )
  :rule-classes nil
  )

(defthm norm-eval-poly-is-minimum-point-globally-truncate-poly-4
  (implies (norm-eval-poly-is-minimum-point-globally poly zmin)
           (norm-eval-poly-is-minimum-point-globally (truncate-polynomial poly) zmin))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance norm-eval-poly-is-minimum-point-globally-truncate-poly-3
                            (z (norm-eval-poly-is-minimum-point-globally-witness (truncate-polynomial poly) zmin)))
                 )
           :in-theory (disable norm-eval-polynomial
                               norm-eval-poly-is-minimum-point-globally-necc))
          )
  :rule-classes nil
  )

(defthm norm-eval-poly-is-minimum-point-globallytruncate-poly
  (equal (norm-eval-poly-is-minimum-point-globally (truncate-polynomial poly) zmin)
         (norm-eval-poly-is-minimum-point-globally poly zmin))
  :hints (("Goal"
           :use ((:instance norm-eval-poly-is-minimum-point-globally-truncate-poly-2)
                 (:instance norm-eval-poly-is-minimum-point-globally-truncate-poly-4)
                 )))
  )

(defthm fta-lemma-1
    (implies (and (polynomial-p poly)
                  (not (constant-polynomial-p poly)))
             (norm-eval-poly-achieves-minimum-point-globally (truncate-polynomial poly)))
    :hints (("Goal"
             :use ((:instance norm-eval-poly-minimum-point-globally-theorem-sk
                              (poly (truncate-polynomial poly)))
                   (:instance constant-polynomial-conditions)
                   (:instance not-a-minimum-point-for-non-constant-polynomial))
             ))
    :rule-classes nil)

(defthm fta-lemma-2
  (implies (and (polynomial-p poly)
                (not (constant-polynomial-p poly)))
           (norm-eval-poly-is-minimum-point-globally (truncate-polynomial poly)
                                                     (norm-eval-poly-achieves-minimum-point-globally-witness (truncate-polynomial poly))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance fta-lemma-1)
                 (:instance norm-eval-poly-achieves-minimum-point-globally
                            (poly (truncate-polynomial poly)))
                 )
           )
          )
  :rule-classes nil)

(defthm fta-lemma-3
  (implies (and (polynomial-p poly)
                (not (constant-polynomial-p poly)))
           (norm-eval-poly-is-minimum-point-globally poly
                                                     (norm-eval-poly-achieves-minimum-point-globally-witness (truncate-polynomial poly))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance fta-lemma-2)
                 )
           :in-theory '(norm-eval-poly-is-minimum-point-globallytruncate-poly)
           )
          )
  :rule-classes nil)

(defun fta-witness (poly)
  (norm-eval-poly-achieves-minimum-point-globally-witness (truncate-polynomial poly)))
                   
(defthm fta-lemma-4
  (implies (and (polynomial-p poly)
                (not (constant-polynomial-p poly)))
           (norm-eval-poly-is-minimum-point-globally poly (fta-witness poly)))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance fta-lemma-3)
                 )
           :in-theory '(fta-witness)
           )
          )
  :rule-classes nil)

(defthm numberp-fta-witness
  (implies (and (polynomial-p poly)
                (not (constant-polynomial-p poly)))
           (acl2-numberp (fta-witness poly)))
  :hints (("Goal"
           :use ((:instance fta-lemma-1)
                 (:instance NORM-EVAL-POLY-ACHIEVES-MINIMUM-POINT-GLOBALLY
                            (poly (truncate-polynomial poly))))
           :do-not-induct t)
          )
  )

(defthm fundamental-theorem-of-algebra
  (implies (and (polynomial-p poly)
                (not (constant-polynomial-p poly)))
           (equal (eval-polynomial poly (fta-witness poly)) 0))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance fta-lemma-4)
                 (:instance not-a-minimum-point-for-non-constant-polynomial
                            (z (fta-witness poly))))
           :in-theory (disable fta-witness
                               eval-polynomial
                               constant-polynomial-p))))

(defun-sk polynomial-has-a-root (poly)
  (exists (z)
          (equal (eval-polynomial poly z) 0)))


(defthm fundamental-theorem-of-algebra-sk
  (implies (and (polynomial-p poly)
                (not (constant-polynomial-p poly)))
           (polynomial-has-a-root poly))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance polynomial-has-a-root-suff
                            (z (fta-witness poly)))
                 (:instance fundamental-theorem-of-algebra))
           :in-theory (disable fta-witness
                               eval-polynomial
                               constant-polynomial-p
                               fundamental-theorem-of-algebra))))
