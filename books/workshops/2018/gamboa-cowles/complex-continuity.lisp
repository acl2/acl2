(in-package "ACL2")
  
; cert_param: (uses-acl2r)


(include-book "nonstd/nsa/intervals" :dir :system)
(include-book "nonstd/nsa/continuity" :dir :system)
(include-book "arithmetic-5/top" :dir :system)

(include-book "complex-lemmas")
(include-book "norm2")

(defun region-p (region)
  (and (consp region)
       (interval-p (car region))
       (interval-p (cdr region))))

(defun inside-region-p (z region)
  (and (acl2-numberp z)
       (inside-interval-p (realpart z) (car region))
       (inside-interval-p (imagpart z) (cdr region))))

(defun subregion-p (subregion region)
  (and (subinterval-p (car subregion) (car region))
       (subinterval-p (cdr subregion) (cdr region))))

(defun closed-region-p (region)
  (and (region-p region)
       (or (equal (interval-left-endpoint (car region)) nil)
           (interval-left-inclusive-p (car region)))
       (or (equal (interval-right-endpoint (car region)) nil)
           (interval-right-inclusive-p (car region)))
       (or (equal (interval-left-endpoint (cdr region)) nil)
           (interval-left-inclusive-p (cdr region)))
       (or (equal (interval-right-endpoint (cdr region)) nil)
           (interval-right-inclusive-p (cdr region)))))

(encapsulate
 ((ccfn (context z) t)
  (ccfn-domain () t))

 ;; Our witness continuous function is the identity function.

 (local (defun ccfn (context z) (declare (ignore context)) (fix z)))
 (local (defun ccfn-domain () (cons (interval nil nil)
                                    (interval nil nil))))

 ;; The region really is a rectangular region

 (defthm regionp-ccfn-domain
   (region-p (ccfn-domain))
   :rule-classes (:type-prescription :rewrite))

 ;; The interval is complex

 (defthm ccfn-domain-complex
     (implies (inside-region-p z (ccfn-domain))
	      (acl2-numberp z))
   :rule-classes (:forward-chaining))

 ;; The interval is non-trivial

 (defthm ccfn-domain-non-trivial
   (or (or (null (interval-left-endpoint (car (ccfn-domain))))
           (null (interval-right-endpoint (car (ccfn-domain))))
           (< (interval-left-endpoint (car (ccfn-domain)))
              (interval-right-endpoint (car (ccfn-domain)))))
       (or (null (interval-left-endpoint (cdr (ccfn-domain))))
           (null (interval-right-endpoint (cdr (ccfn-domain))))
           (< (interval-left-endpoint (cdr (ccfn-domain)))
              (interval-right-endpoint (cdr (ccfn-domain))))))
   :rule-classes nil)

 ;; The function returns complex values (even for improper arguments).

 (defthm ccfn-complex
     (acl2-numberp (ccfn context x))
   :rule-classes (:rewrite :type-prescription))

 ;; If x is a standard number and y is a number close to x, then ccfn(x)
 ;; is close to ccfn(y).

 (defthm ccfn-continuous
   (implies (and (standardp context)
                 (standardp z)
		 (inside-region-p z (ccfn-domain))
		 (i-close z z2)
		 (inside-region-p z2 (ccfn-domain)))
	    (i-close (ccfn context z) (ccfn context z2))))
 )


;;;-------------------

(encapsulate
 ((crvcfn (context z) t)
  (crvcfn-domain () t))

 ;; Our witness continuous function is the identity function.

 (local (defun crvcfn (context z) (declare (ignore context z)) 0))
 (local (defun crvcfn-domain () (cons (interval nil nil)
                                      (interval nil nil))))

 ;; The region really is a rectangular region

 (defthm regionp-crvcfn-domain
   (region-p (crvcfn-domain))
   :rule-classes (:type-prescription :rewrite))

 ;; The interval is complex

 (defthm crvcfn-domain-complex
     (implies (inside-region-p z (crvcfn-domain))
	      (acl2-numberp z))
   :rule-classes (:forward-chaining))

 ;; The interval is non-trivial

 (defthm crvcfn-domain-non-trivial
   (or (or (null (interval-left-endpoint (car (crvcfn-domain))))
           (null (interval-right-endpoint (car (crvcfn-domain))))
           (< (interval-left-endpoint (car (crvcfn-domain)))
              (interval-right-endpoint (car (crvcfn-domain)))))
       (or (null (interval-left-endpoint (cdr (crvcfn-domain))))
           (null (interval-right-endpoint (cdr (crvcfn-domain))))
           (< (interval-left-endpoint (cdr (crvcfn-domain)))
              (interval-right-endpoint (cdr (crvcfn-domain))))))
   :rule-classes nil)

 ;; The function returns complex values (even for improper arguments).

 (defthm crvcfn-real
     (real/rationalp (crvcfn context x))
   :rule-classes (:rewrite :type-prescription))

 ;; If x is a standard number and y is a number close to x, then crvcfn(x)
 ;; is close to crvcfn(y).

 (defthm crvcfn-continuous
   (implies (and (standardp context)
                 (standardp z)
		 (inside-region-p z (crvcfn-domain))
		 (i-close z z2)
		 (inside-region-p z2 (crvcfn-domain)))
	    (i-close (crvcfn context z) (crvcfn context z2))))
 )


;;;-------------------

(defun norm-ccfn (context x)
  (norm2 (ccfn context x)))

(defthm norm-ccfn-real
  (real/rationalp (norm-ccfn context x))
  :rule-classes (:rewrite :type-prescription))

(defthm-std ccfn-standard
  (implies (and (standardp context)
                (standardp z))
           (standardp (ccfn context z)))
  :rule-classes (:rewrite :type-prescription))

(defthm-std standardp-ccfn-domain
  (standardp (ccfn-domain))
  :rule-classes (:rewrite :type-prescription))

;; If x is a standard number and y is a number close to x, then crvcfn(x)
;; is close to crvcfn(y).

(defthm norm-ccfn-continuous
  (implies (and (standardp context)
                (standardp z)
                (inside-region-p z (ccfn-domain))
                (i-close z z2)
                (inside-region-p z2 (ccfn-domain)))
           (i-close (norm-ccfn context z) (norm-ccfn context z2)))
  :hints (("Goal"
           :use ((:instance ccfn-continuous)
                 (:instance close-norm
                            (x (ccfn context z2))
                            (y (ccfn context z)))
                 (:instance ccfn-standard)
                 )
           :in-theory (disable ccfn-continuous close-norm ccfn-standard))
          )
  :rule-classes nil)

;; Now we need to show that crvcfn (and hence norm-ccfn) achieves its minimum on a closed region

(defun find-min-crvcfn-z-n (x0 y0 context min-z i j n eps)
  (declare (xargs :measure (+ (* (nfix (1+ n)) (nfix (+ 1 (- n i))))
                              (nfix (- n j)))))
  (if (and (natp i)
           (natp j)
           (posp n)
           (<= i n)
           (<= j n)
           (realp x0)
           (realp y0)
           (realp eps)
           (< 0 eps))
      (let* ((cur-z (+ (complex x0 y0) (complex (* i eps) (* j eps))))
             (next-min-z (if (< (crvcfn context cur-z) (crvcfn context min-z))
                             cur-z
                           min-z)))
        (if (< j n)
            (find-min-crvcfn-z-n x0 y0 context next-min-z i (1+ j) n eps)
          (if (< i n)
              (find-min-crvcfn-z-n x0 y0 context next-min-z (1+ i) 0 n eps)
          next-min-z)))
      min-z))
      


(local
 (defun natural-induction (n)
   (if (zp n)
       n
     (natural-induction (1- n)))))

(encapsulate nil
  
  (local
   (defthm find-min-crvcfn-z-n-is-monotone
     (<= (crvcfn context (find-min-crvcfn-z-n x0 y0 context min-z i j n eps))
         (crvcfn context min-z))))

  (local
   (defun ind-hint (x0 y0 context min-z1 min-z2 i j n eps)
     (declare (xargs :measure (+ (* (nfix (1+ n)) (nfix (+ 1 (- n i))))
                                 (nfix (- n j)))))
     (if (and (natp i)
              (natp j)
              (posp n)
              (<= i n)
              (<= j n)
              (realp x0)
              (realp y0)
              (realp eps)
              (< 0 eps))
         (let* ((cur-z (+ (complex x0 y0) (complex (* i eps) (* j eps)))))
           (if (< (crvcfn context cur-z) (crvcfn context min-z1))
               (list x0 y0 context min-z1 min-z2 i j n eps)
             (if (< (crvcfn context cur-z) (crvcfn context min-z2))
                 (if (< j n)
                     (ind-hint  x0 y0 context min-z1 cur-z i (1+ j) n eps)
                   (if (< i n)
                       (ind-hint x0 y0 context min-z1 cur-z (1+ i) 0 n eps)
                     (list x0 y0 context min-z1 min-z2 i j n eps)))
               (if (< j n)
                   (ind-hint  x0 y0 context min-z1 min-z2 i (1+ j) n eps)
                 (if (< i n)
                     (ind-hint x0 y0 context min-z1 min-z2 (1+ i) 0 n eps)
                   (list x0 y0 context min-z1 min-z2 i j n eps))))))
       (list x0 y0 context min-z1 min-z2 i j n eps))))

  (local
   (defthm find-min-crvcfn-z-n-is-monotone-2
     (implies (<= (crvcfn context min-z1)
                  (crvcfn context min-z2))
              (<= (crvcfn context (find-min-crvcfn-z-n x0 y0 context min-z1 i j n eps))
                  (crvcfn context (find-min-crvcfn-z-n x0 y0 context min-z2 i j n eps))))
     :hints (("Goal"
              :induct (ind-hint x0 y0 context min-z1 min-z2 i j n eps)
              :do-not-induct t)
             ("Subgoal *1/1"
              :expand ((FIND-MIN-CRVCFN-Z-N X0 Y0 CONTEXT MIN-Z1 I J N EPS)
                       (FIND-MIN-CRVCFN-Z-N X0 Y0 CONTEXT MIN-Z2 I J N EPS)))
             )
     ))

  (local
   (defthm find-min-crvcfn-z-n-minimum-in-grid-lemma-1
     (implies (and (natp i)
                   (natp j)
                   (posp n)
                   (<= i n)
                   (<= j n)
                   (realp x0)
                   (realp y0)
                   (realp eps)
                   (< 0 eps))
              (<= (crvcfn context (find-min-crvcfn-z-n x0 y0 context min-z i j n eps))
                  (crvcfn context (+ (complex x0 y0) (complex (* i eps) (* j eps))))))
     :hints (("Goal"
              :use ((:instance find-min-crvcfn-z-n-is-monotone)
                    (:instance find-min-crvcfn-z-n-is-monotone
                               (j (1+ j))
                               (min-z (+ (complex x0 y0) (complex (* i eps) (* j eps)))))
                    (:instance find-min-crvcfn-z-n-is-monotone
                               (i (1+ i))
                               (j 0)
                               (min-z (+ (complex x0 y0) (complex (* i eps) (* j eps)))))
                    )
              :expand (FIND-MIN-CRVCFN-Z-N X0 Y0 CONTEXT MIN-Z I J N EPS)
              :in-theory (disable  find-min-crvcfn-z-n-is-monotone)
              :do-not-induct t
              )
             )
     :rule-classes nil))

  (local
   (defthm find-min-crvcfn-z-n-minimum-in-grid-lemma-2
     (implies (and (natp i)
                   (natp j)
                   (posp n)
                   (<= i n)
                   (< j n)
                   (realp x0)
                   (realp y0)
                   (realp eps)
                   (< 0 eps))
              (<= (crvcfn context (find-min-crvcfn-z-n x0 y0 context min-z i j n eps))
                  (crvcfn context (find-min-crvcfn-z-n x0 y0 context min-z i (1+ j) n eps))))
     :hints (("Goal"
              :expand  (find-min-crvcfn-z-n x0 y0 context min-z i j n eps)
              :use ((:instance find-min-crvcfn-z-n-is-monotone-2
                               (j (1+ j))
                               (min-z1 (+ (complex x0 y0) (complex (* i eps) (* j eps))))
                               (min-z2 min-z))
                    )
              :in-theory (disable find-min-crvcfn-z-n find-min-crvcfn-z-n-is-monotone-2)
              :do-not-induct t
              )
             )
     :rule-classes nil))


  (local
   (defthm find-min-crvcfn-z-n-minimum-in-grid-lemma-3
     (implies (and (natp i)
                   (natp j)
                   (natp jstar)
                   (posp n)
                   (<= i n)
                   (< j jstar)
                   (<= jstar n)
                   (realp x0)
                   (realp y0)
                   (realp eps)
                   (< 0 eps))
              (<= (crvcfn context (find-min-crvcfn-z-n x0 y0 context min-z i j n eps))
                  (crvcfn context (find-min-crvcfn-z-n x0 y0 context min-z i jstar n eps))))
     :hints (("Goal"
              :induct (natural-induction jstar)
              :in-theory (disable find-min-crvcfn-z-n)
              :do-not-induct t)
             ("Subgoal *1/2"
              :use ((:instance find-min-crvcfn-z-n-minimum-in-grid-lemma-2
                               (j (1- jstar))))
              :in-theory (disable  find-min-crvcfn-z-n)))
     :rule-classes nil))

  (local
   (defthm find-min-crvcfn-z-n-minimum-in-grid-lemma-4
     (implies (and (natp i)
                   (natp jstar)
                   (posp n)
                   (<= i n)
                   (<= jstar n)
                   (realp x0)
                   (realp y0)
                   (realp eps)
                   (< 0 eps))
              (<= (crvcfn context (find-min-crvcfn-z-n x0 y0 context min-z i 0 n eps))
                  (crvcfn context (find-min-crvcfn-z-n x0 y0 context min-z i jstar n eps))))
     :hints (("Goal"
              :use ((:instance find-min-crvcfn-z-n-minimum-in-grid-lemma-3 (j 0)))
              :in-theory (disable find-min-crvcfn-z-n)
              :do-not-induct t))
     :rule-classes nil))

  (local
   (defthm find-min-crvcfn-z-n-minimum-in-grid-lemma-5
     (implies (and (natp i)
                   (posp n)
                   (< i n)
                   (realp x0)
                   (realp y0)
                   (realp eps)
                   (< 0 eps))
              (<= (crvcfn context (find-min-crvcfn-z-n x0 y0 context min-z i n n eps))
                  (crvcfn context (find-min-crvcfn-z-n x0 y0 context min-z (1+ i) 0 n eps))))
     :hints (("Goal"
              :expand  (find-min-crvcfn-z-n x0 y0 context min-z i n n eps)
              :use ((:instance find-min-crvcfn-z-n-is-monotone-2
                               (i (1+ i))
                               (j 0)
                               (min-z1 (+ (complex x0 y0) (complex (* i eps) (* n eps))))
                               (min-z2 min-z))
                    )
              :in-theory (disable find-min-crvcfn-z-n find-min-crvcfn-z-n-is-monotone-2)
              :do-not-induct t
              )
             )
     :rule-classes nil))

  (local
   (defthm find-min-crvcfn-z-n-minimum-in-grid-lemma-6
     (implies (and (natp i)
                   (posp n)
                   (< i n)
                   (realp x0)
                   (realp y0)
                   (realp eps)
                   (< 0 eps))
              (<= (crvcfn context (find-min-crvcfn-z-n x0 y0 context min-z i 0 n eps))
                  (crvcfn context (find-min-crvcfn-z-n x0 y0 context min-z (1+ i) 0 n eps))))
     :hints (("Goal"
              :use ((:instance find-min-crvcfn-z-n-minimum-in-grid-lemma-5)
                    (:instance find-min-crvcfn-z-n-minimum-in-grid-lemma-4
                               (jstar n))
                    )
              :in-theory (disable find-min-crvcfn-z-n)
              :do-not-induct t
              )
             )
     :rule-classes nil))

  (local
   (defthm find-min-crvcfn-z-n-minimum-in-grid-lemma-7
     (implies (and (natp i)
                   (natp istar)
                   (posp n)
                   (< i istar)
                   (<= istar n)
                   (realp x0)
                   (realp y0)
                   (realp eps)
                   (< 0 eps))
              (<= (crvcfn context (find-min-crvcfn-z-n x0 y0 context min-z i 0 n eps))
                  (crvcfn context (find-min-crvcfn-z-n x0 y0 context min-z istar 0 n eps))))
     :hints (("Goal"
              :induct (natural-induction istar)
              :in-theory (disable find-min-crvcfn-z-n)
              :do-not-induct t)
             ("Subgoal *1/2"
              :use ((:instance find-min-crvcfn-z-n-minimum-in-grid-lemma-6
                               (i (1- istar)))
                    )
              :in-theory (disable find-min-crvcfn-z-n)
              :do-not-induct t
              )
             )
     :rule-classes nil))

  (local
   (defthm find-min-crvcfn-z-n-minimum-in-grid-lemma-8
     (implies (and (natp istar)
                   (posp n)
                   (<= istar n)
                   (realp x0)
                   (realp y0)
                   (realp eps)
                   (< 0 eps))
              (<= (crvcfn context (find-min-crvcfn-z-n x0 y0 context min-z 0 0 n eps))
                  (crvcfn context (find-min-crvcfn-z-n x0 y0 context min-z istar 0 n eps))))
     :hints (("Goal"
              :use ((:instance find-min-crvcfn-z-n-minimum-in-grid-lemma-7
                               (i 0))
                    )
              :in-theory (disable find-min-crvcfn-z-n)
              :do-not-induct t
              )
             )
     :rule-classes nil))

  (local
   (defthm find-min-crvcfn-z-n-minimum-in-grid-lemma-9
     (implies (and (natp i)
                   (natp j)
                   (posp n)
                   (<= i n)
                   (<= j n)
                   (realp x0)
                   (realp y0)
                   (realp eps)
                   (< 0 eps))
              (<= (crvcfn context (find-min-crvcfn-z-n x0 y0 context min-z 0 0 n eps))
                  (crvcfn context (find-min-crvcfn-z-n x0 y0 context min-z i j n eps))))
     :hints (("Goal"
              :use ((:instance find-min-crvcfn-z-n-minimum-in-grid-lemma-8
                               (istar i))
                    (:instance find-min-crvcfn-z-n-minimum-in-grid-lemma-4
                               (jstar j))
                    )
              :in-theory (disable find-min-crvcfn-z-n)
              :do-not-induct t
              )
             )
     :rule-classes nil))

  (defthm find-min-crvcfn-z-n-minimum-in-grid
    (implies (and (natp i)
                  (natp j)
                  (posp n)
                  (<= i n)
                  (<= j n)
                  (realp x0)
                  (realp y0)
                  (realp eps)
                  (< 0 eps))
             (<= (crvcfn context (find-min-crvcfn-z-n x0 y0 context min-z 0 0 n eps))
                 (crvcfn context (+ (complex x0 y0)
                                    (complex (* eps i) (* eps j))))))
    :hints (("Goal"
             :use ((:instance find-min-crvcfn-z-n-minimum-in-grid-lemma-9)
                   (:instance find-min-crvcfn-z-n-minimum-in-grid-lemma-1)
                   )
             :in-theory (disable find-min-crvcfn-z-n)
             :do-not-induct t
             )
            )
    :rule-classes nil)
)

(local
 (defthm lemma-1
   (implies (and (realp r) (realp s))
            (equal (complex r s)
                   (+ r (* #c(0 1) s))))
   :hints (("Goal" :by (:instance complex-definition (x r) (y s))))
   :rule-classes nil))

(local
 (defthm lemma-2
   (implies (and (realp a)
                 (realp b)
                 (realp c)
                 (< 0 a))
            (equal (* (/ a)
                      (complex (* a b) (* a c)))
                   (complex b c)))
   :hints (("Goal"
            :use ((:instance lemma-1
                             (r (* a b))
                             (s (* a c)))
                  (:instance lemma-1
                             (r b)
                             (s c)))))
   ))

(defthm inside-region-lemma-1
  (implies (and (acl2-numberp z1)
                (acl2-numberp z2)
                (region-p region)
                (inside-region-p z1 region)
                (inside-region-p z2 region)
                (acl2-numberp z)
                (<= (realpart z1) (realpart z))
                (<= (realpart z) (realpart z2))
                (<= (imagpart z1) (imagpart z))
                (<= (imagpart z) (imagpart z2))
                )
           (inside-region-p z region))
  :hints (("Goal"
           :use ((:instance inside-interval-p-squeeze
                            (a (realpart z1))
                            (b (realpart z2))
                            (c (realpart z))
                            (interval (car region)))
                 (:instance inside-interval-p-squeeze
                            (a (imagpart z1))
                            (b (imagpart z2))
                            (c (imagpart z))
                            (interval (cdr region)))
                 )
           :in-theory (disable inside-interval-p-squeeze)))
  :rule-classes nil)


(defthm inside-region-lemma-2 
  (implies (and (natp i)
                (natp j)
                (posp n)
                (<= i n)
                (<= j n)
                (realp x0)
                (realp y0)
                (realp eps)
                (< 0 eps)
                (region-p region)
                (inside-region-p (complex x0 y0) region)
                (inside-region-p (complex (+ x0 (* n eps)) (+ y0 (* n eps))) region))
           (inside-region-p (complex (+ x0 (* i eps)) (+ y0 (* j eps))) region))
  :hints (("Goal"
           :use ((:instance inside-region-lemma-1
                            (z1 (complex x0 y0))
                            (z2 (complex (+ x0 (* n eps)) (+ y0 (* n eps))))
                            (z  (complex (+ x0 (* i eps)) (+ y0 (* j eps))))
                            (region region))))))

(defthm inside-region-lemma-3
  (implies (realp y)
           (equal (realpart (* #c(0 1) y)) 0))
   :hints (("Goal" :use ((:instance complex-definition (x 0) (y y)))))
   :rule-classes nil)

(defthm inside-region-lemma-4
  (implies (and (realp a)
                (realp x)
                (realp y))
           (equal (realpart (* a (complex x y)))
                  (* a (realpart (complex x y)))))
  :hints (("Goal"
           :use ((:instance complex-definition (x x) (y y))
                 (:instance inside-region-lemma-3
                            (y (* a y)))
                 ))))

(defthm inside-region-lemma-5
  (implies (realp y)
           (equal (imagpart (* #c(0 1) y)) y))
   :hints (("Goal" :use ((:instance complex-definition (x 0) (y y)))))
   :rule-classes nil)

(defthm inside-region-lemma-6
  (implies (and (realp a)
                (realp x)
                (realp y))
           (equal (imagpart (* a (complex x y)))
                  (* a (imagpart (complex x y)))))
  :hints (("Goal"
           :use ((:instance complex-definition (x x) (y y))
                 (:instance inside-region-lemma-5
                            (y (* a y)))
                 ))))

(defthm inside-region-lemma-7
  (implies (and (realp x)
                (realp y))
           (equal (realpart (- (complex x y)))
                  (- (realpart (complex x y)))))
  :hints (("Goal"
           :use ((:instance complex-definition (x x) (y y))
                 (:instance complex-definition (x (- x)) (y (- y)))
                 ))))

(defthm inside-region-lemma-8
  (implies (and (realp a)
                (realp x)
                (realp y))
           (equal (realpart (- (* a (complex x y))))
                  (- (* a (realpart (complex x y))))))
  :hints (("Goal"
           :use ((:instance inside-region-lemma-4
                            (a (- a)))))))

(defthm inside-region-lemma-9
  (implies (and (realp a)
                (realp x)
                (realp y))
           (equal (imagpart (- (* a (complex x y))))
                  (- (* a (imagpart (complex x y))))))
  :hints (("Goal"
           :use ((:instance inside-region-lemma-6
                            (a (- a)))))))

(defthm find-min-crvcfn-z-n-minimum-inside-region-lemma
  (implies (and (natp i)
                (natp j)
                (posp n)
                (<= i n)
                (<= j n)
                (realp x0)
                (realp y0)
                (realp eps)
                (< 0 eps)
                (inside-region-p min-z (crvcfn-domain))
                (inside-region-p (complex x0 y0) (crvcfn-domain))
                (inside-region-p (complex (+ x0 (* n eps)) (+ y0 (* n eps))) (crvcfn-domain)))
           (let* ((found-min (find-min-crvcfn-z-n x0 y0 context min-z i j n eps))
                  (gridded-min (/ (- found-min (complex x0 y0)) eps))
                  (istar (realpart gridded-min))
                  (jstar (imagpart gridded-min)))
             (or (equal found-min min-z)
                 (and (natp istar)
                      (natp jstar)
                      (<= istar n)
                      (<= jstar n)))))
  :hints (("Goal"
           :induct (find-min-crvcfn-z-n x0 y0 context min-z i j n eps)
           ; :in-theory (disable find-min-crvcfn-z-n)
           :do-not-induct t
           )
          ("Subgoal *1/2"
           :use ((:instance inside-region-lemma-2 (region (crvcfn-domain))))
           :in-theory (disable inside-region-lemma-2))
          ("Subgoal *1/1"
           :use ((:instance inside-region-lemma-2 (region (crvcfn-domain))))
           :in-theory (disable inside-region-lemma-2))
          )
  :rule-classes nil)

(defthm find-min-crvcfn-z-n-minimum-inside-region
  (implies (and (natp i)
                (natp j)
                (posp n)
                (<= i n)
                (<= j n)
                (realp x0)
                (realp y0)
                (realp eps)
                (< 0 eps)
                (inside-region-p (complex x0 y0) (crvcfn-domain))
                (inside-region-p (complex (+ x0 (* n eps)) (+ y0 (* n eps))) (crvcfn-domain)))
           (let* ((found-min (find-min-crvcfn-z-n x0 y0 context (complex x0 y0) i j n eps))
                  (gridded-min (/ (- found-min (complex x0 y0)) eps))
                  (istar (realpart gridded-min))
                  (jstar (imagpart gridded-min)))
             (and (natp istar)
                  (natp jstar)
                  (<= istar n)
                  (<= jstar n))))
  :hints (("Goal"
           :use ((:instance find-min-crvcfn-z-n-minimum-inside-region-lemma
                            (min-z (complex x0 y0))))
           :in-theory (disable find-min-crvcfn-z-n)
           :do-not-induct t
           )
          )
  :rule-classes nil)

(defthm lemma-3
  (implies (and (realp a)
                (< 0 a)
                (acl2-numberp z))
           (equal (* a (realpart (* (/ a) z)))
                  (realpart z)))
  )


(defthm lemma-4
  (implies (and (realp a)
                (< 0 a)
                (acl2-numberp z))
           (equal (* a (imagpart (* (/ a) z)))
                  (imagpart z)))
  )
                

(defthm inside-interval-left-endpoint
  (implies (and (realp a)
                (realp b)
                (< a b))
           (inside-interval-p a (interval a b)))
  :hints (("Goal"
           :in-theory (enable interval-definition-theory))))

(defthm inside-interval-right-endpoint
  (implies (and (realp a)
                (realp b)
                (< a b))
           (inside-interval-p b (interval a b)))
  :hints (("Goal"
           :in-theory (enable interval-definition-theory))))

(defthm find-min-crvcfn-z-n-minimum-inside-region-corollary-1
  (implies (and (natp i)
                (natp j)
                (posp n)
                (<= i n)
                (<= j n)
                (realp x0)
                (realp y0)
                (realp eps)
                (< 0 eps)
                (inside-region-p (complex x0 y0) (crvcfn-domain))
                (inside-region-p (complex (+ x0 (* n eps)) (+ y0 (* n eps))) (crvcfn-domain)))
           (inside-region-p (find-min-crvcfn-z-n x0 y0 context (complex x0 y0) i j n eps)
                            (cons (interval x0 (+ x0 (* n eps)))
                                  (interval y0 (+ y0 (* n eps))))
                            ))
  :hints (("Goal"
           :use ((:instance find-min-crvcfn-z-n-minimum-inside-region)
                 (:instance inside-region-lemma-2
                            (i (realpart (/ (- (find-min-crvcfn-z-n x0 y0 context (complex x0 y0) i j n eps) (complex x0 y0)) eps)))
                            (j (imagpart (/ (- (find-min-crvcfn-z-n x0 y0 context (complex x0 y0) i j n eps) (complex x0 y0)) eps)))
                            (region (cons (interval x0 (+ x0 (* n eps)))
                                          (interval y0 (+ y0 (* n eps)))))
                            )
                 )
           :in-theory (disable find-min-crvcfn-z-n inside-region-lemma-2)
           :do-not-induct t
           )
          )
  :rule-classes nil)

(defthm find-min-crvcfn-z-n-minimum-inside-region-corollary-2
  (implies (and (natp i)
                (natp j)
                (posp n)
                (<= i n)
                (<= j n)
                (realp x0)
                (realp y0)
                (realp eps)
                (< 0 eps)
                (inside-region-p (complex x0 y0) (crvcfn-domain))
                (inside-region-p (complex (+ x0 (* n eps)) (+ y0 (* n eps))) (crvcfn-domain)))
           (inside-region-p (find-min-crvcfn-z-n x0 y0 context (complex x0 y0) i j n eps)
                            (crvcfn-domain)
                            ))
  :hints (("Goal"
           :use ((:instance find-min-crvcfn-z-n-minimum-inside-region)
                 (:instance inside-region-lemma-2
                            (i (realpart (/ (- (find-min-crvcfn-z-n x0 y0 context (complex x0 y0) i j n eps) (complex x0 y0)) eps)))
                            (j (imagpart (/ (- (find-min-crvcfn-z-n x0 y0 context (complex x0 y0) i j n eps) (complex x0 y0)) eps)))
                            (region (crvcfn-domain))
                            )
                 )
           :in-theory (disable find-min-crvcfn-z-n inside-region-lemma-2)
           :do-not-induct t
           )
          )
  :rule-classes nil)

(defthm-std limited-if-in-standard-region-lemma-1
  (implies (standardp region)
           (standardp (interval-left-endpoint (car region)))))

(defthm-std limited-if-in-standard-region-lemma-2
  (implies (standardp region)
           (standardp (interval-left-endpoint (cdr region)))))

(defthm-std limited-if-in-standard-region-lemma-3
  (implies (standardp region)
           (standardp (interval-right-endpoint (car region)))))

(defthm-std limited-if-in-standard-region-lemma-4
  (implies (standardp region)
           (standardp (interval-right-endpoint (cdr region)))))

(defthm limited-if-in-standard-region-lemma-5
  (implies (and (standardp region)
                (region-p region))
           (not (i-large (interval-left-endpoint (car region)))))
  :hints (("Goal"
           :use ((:instance standards-are-limited (x (interval-left-endpoint (car region))))
                 )
           :in-theory (disable standards-are-limited))))

(defthm limited-if-in-standard-region-lemma-6
  (implies (and (standardp region)
                (region-p region))
           (not (i-large (interval-left-endpoint (cdr region)))))
  :hints (("Goal"
           :use ((:instance standards-are-limited (x (interval-left-endpoint (cdr region))))
                 )
           :in-theory (disable standards-are-limited))))

(defthm limited-if-in-standard-region-lemma-7
  (implies (and (standardp region)
                (region-p region))
           (not (i-large (interval-right-endpoint (car region)))))
  :hints (("Goal"
           :use ((:instance standards-are-limited (x (interval-right-endpoint (car region))))
                 )
           :in-theory (disable standards-are-limited))))

(defthm limited-if-in-standard-region-lemma-8
  (implies (and (standardp region)
                (region-p region))
           (not (i-large (interval-right-endpoint (cdr region)))))
  :hints (("Goal"
           :use ((:instance standards-are-limited (x (interval-right-endpoint (cdr region))))
                 )
           :in-theory (disable standards-are-limited))))


(defthm limited-if-in-standard-region-lemma-9
  (implies (interval-left-inclusive-p interval)
           (realp (interval-left-endpoint interval)))
  :hints (("Goal"
           :in-theory (enable interval-definition-theory)))
  :rule-classes (:type-prescription :rewrite))

(defthm limited-if-in-standard-region-lemma-10
  (implies (interval-right-inclusive-p interval)
           (realp (interval-right-endpoint interval)))
  :hints (("Goal"
           :in-theory (enable interval-definition-theory)))
  :rule-classes (:type-prescription :rewrite))
  
(defthm limited-if-in-standard-region
  (implies (and (standardp region)
                (region-p region)
                (acl2-numberp z)
                (interval-left-inclusive-p (car region))
                (interval-right-inclusive-p (car region))
                (interval-left-inclusive-p (cdr region))
                (interval-right-inclusive-p (cdr region))
                (inside-region-p z region))
           (i-limited z))
  :hints (("Goal"
           :use ((:instance limited-squeeze
                            (a (interval-left-endpoint (car region)))
                            (b (interval-right-endpoint (car region)))
                            (x (realpart z)))
                 (:instance limited-squeeze
                            (a (interval-left-endpoint (cdr region)))
                            (b (interval-right-endpoint (cdr region)))
                            (x (imagpart z)))
                 (:instance inside-interval-p->=-left-endpoint
                            (x (realpart z))
                            (interval (car region)))
                 (:instance inside-interval-p-<=-right-endpoint
                            (x (realpart z))
                            (interval (car region)))
                 (:instance inside-interval-p->=-left-endpoint
                            (x (imagpart z))
                            (interval (cdr region)))
                 (:instance inside-interval-p-<=-right-endpoint
                            (x (imagpart z))
                            (interval (cdr region)))
                 (:instance complex-large-2
                            (x z))
                 )
           :in-theory (disable limited-squeeze
                               NOT-COMPLEX-IMAGPART-IS-0
                               inside-interval-p->=-left-endpoint
                               inside-interval-p-<=-right-endpoint
                               complex-large-1))
          )
  :rule-classes nil) 

(defthm-std find-min-crvcfn-z-limited-lemma
  (implies (and (standardp z)
                (standardp s))
           (standardp (cons (interval (realpart z)
                                      (+ s (realpart z)))
                            (interval (imagpart z)
                                      (+ s (imagpart z)))))))

(defthm find-min-crvcfn-z-limited
  (implies
   (and (standardp context)
        (standardp z)
        (standardp s)
        (acl2-numberp z)
        (inside-interval-p (realpart z)
                           (car (crvcfn-domain)))
        (inside-interval-p (imagpart z)
                           (cdr (crvcfn-domain)))
        (inside-interval-p (+ s (realpart z))
                           (car (crvcfn-domain)))
        (inside-interval-p (+ s (imagpart z))
                           (cdr (crvcfn-domain)))
        (realp s)
        (< 0 s))
   (standardp
    (standard-part (find-min-crvcfn-z-n (realpart z)
                                        (imagpart z)
                                        context z 0 0 (i-large-integer)
                                        (* (/ (i-large-integer)) s)))))
  :hints (("Goal"
           :use ((:instance standardp-standard-part
                            (x (find-min-crvcfn-z-n (realpart z)
                                                    (imagpart z)
                                                    context z 0 0 (i-large-integer)
                                                    (* (/ (i-large-integer)) s))))
                 (:instance limited-if-in-standard-region
                            (z (find-min-crvcfn-z-n (realpart z)
                                                    (imagpart z)
                                                    context z 0 0 (i-large-integer)
                                                    (* (/ (i-large-integer)) s)))
                            (region (cons (interval (realpart z) (+ (realpart z) s))
                                          (interval (imagpart z) (+ (imagpart z) s)))))
                 (:instance find-min-crvcfn-z-n-minimum-inside-region-corollary-1
                            (i 0)
                            (j 0)
                            (n (i-large-integer))
                            (x0 (realpart z))
                            (y0 (imagpart z))
                            (eps (* (/ (i-large-integer)) s)))
                 )
           :in-theory (disable standardp-standard-part)))
  )

(defun-std find-min-crvcfn-z (context z s)
  (if (and (inside-region-p z (crvcfn-domain))
           (inside-region-p (+ z (complex s s)) (crvcfn-domain))
           (realp s)
           (< 0 s))
      (let* ((n (i-large-integer))
             (eps (/ s n))
             (x0 (realpart z))
             (y0 (imagpart z)))
      (standard-part (find-min-crvcfn-z-n x0 y0 context z 0 0 n eps)))
    0))

(defthm two-points-make-an-interval
  (implies (and (realp x1)
                (realp x2)
                (<= x1 x2)
                (interval-p interval)
                (inside-interval-p x1 interval)
                (inside-interval-p x2 interval))
           (subinterval-p (interval x1 x2) interval))
  :hints (("Goal"
           :in-theory (enable interval-definition-theory)))
  )

(defthm two-points-make-a-subregion
  (implies (and (inside-region-p z1 region)
                (inside-region-p z2 region)
                (region-p region)
                (<= (realpart z1) (realpart z2))
                (<= (imagpart z1) (imagpart z2)))
           (subregion-p (cons (interval (realpart z1) (realpart z2))
                              (interval (imagpart z1) (imagpart z2)))
                        region))
  :hints (("Goal"
           :in-theory (enable interval-definition-theory))))

(defthm inside-subregion
  (implies (and (subregion-p subregion region)
                (inside-region-p z subregion))
           (inside-region-p z region)))



(defthm-std standard-interval
  (implies (and (standardp a)
                (standardp b))
           (standardp (interval a b))))

;;; IMPORTANT
(defthm-std find-min-crvcfn-z-inside-region-1
  (implies (and (inside-region-p z (crvcfn-domain))
                (inside-region-p (+ z (complex s s)) (crvcfn-domain))
                (realp s)
                (< 0 s))
           (inside-region-p (find-min-crvcfn-z context z s)
                            (cons (interval (realpart z) (+ (realpart z) s))
                                  (interval (imagpart z) (+ (imagpart z) s)))))
  :hints (("Goal"
           :use ((:instance find-min-crvcfn-z-n-minimum-inside-region-corollary-1
                            (i 0)
                            (j 0)
                            (x0 (realpart z))
                            (y0 (imagpart z))
                            (n (i-large-integer))
                            (eps (/ s (i-large-integer))))
                 (:instance complex-large-1
                            (x  (find-min-crvcfn-z-n (realpart z)
                                                     (imagpart z)
                                                     context z 0 0 (i-large-integer)
                                                     (* (/ (i-large-integer)) s))))
                 (:instance limited-if-in-standard-region
                            (z (find-min-crvcfn-z-n (realpart z)
                                                    (imagpart z)
                                                    context z 0 0 (i-large-integer)
                                                    (* (/ (i-large-integer)) s)))
                            (region (cons (interval (realpart z) (+ (realpart z) s))
                                          (interval (imagpart z) (+ (imagpart z) s)))))
                 (:instance standard-part-inside-interval
                            (x (realpart (find-min-crvcfn-z-n (realpart z)
                                                              (imagpart z)
                                                              context z 0 0 (i-large-integer)
                                                              (* (/ (i-large-integer)) s))))
                            (interval (interval (realpart z) (+ (realpart z) s))))
                 (:instance standard-part-inside-interval
                            (x (imagpart (find-min-crvcfn-z-n (realpart z)
                                                              (imagpart z)
                                                              context z 0 0 (i-large-integer)
                                                              (* (/ (i-large-integer)) s))))
                            (interval (interval (imagpart z) (+ (imagpart z) s))))
                 (:instance standard-part-of-complex-2
                            (x  (find-min-crvcfn-z-n (realpart z)
                                                     (imagpart z)
                                                     context z 0 0 (i-large-integer)
                                                     (* (/ (i-large-integer)) s))))
                 )
           :in-theory (disable complex-large-1
                               standard-part-inside-interval
                               standard-part-of-complex)
           ))
  )

;;; IMPORTANT
(defthm-std find-min-crvcfn-z-inside-region-2
  (implies (and (inside-region-p z (crvcfn-domain))
                (inside-region-p (+ z (complex s s)) (crvcfn-domain))
                (realp s)
                (< 0 s))
           (inside-region-p (find-min-crvcfn-z context z s)
                            (crvcfn-domain)))
  :hints (("Goal"
           :use ((:instance find-min-crvcfn-z-inside-region-1)
                 (:instance inside-subregion
                            (subregion (cons (interval (realpart z) (+ (realpart z) s))
                                             (interval (imagpart z) (+ (imagpart z) s))))
                            (region (crvcfn-domain)))
                 (:instance two-points-make-a-subregion
                            (z1 z)
                            (z2 (+ z (complex s s)))
                            (region (crvcfn-domain)))
                 )
           :in-theory (disable find-min-crvcfn-z-inside-region-1
                               inside-subregion)
           ))
  )

(defun find-eps-coefficient (x a n eps)
  (if (zp n)
      0
    (if (< (+ a (* n eps)) x)
        n
      (find-eps-coefficient x a (1- n) eps))))

(defthm find-eps-coefficient-upper-bound
    (implies (natp n)
             (<= (find-eps-coefficient x a n eps) n)))

(defthm find-eps-coefficient-lower-bound
    (implies (natp n)
             (<= 0 (find-eps-coefficient x a n eps))))

(defthm find-eps-coefficient-inside-interval
  (implies (and (inside-interval-p a interval)
                (inside-interval-p (+ a (* n eps)) interval)
                (natp n)
                (realp eps)
                (<= 0 eps))
           (inside-interval-p (+ a (* eps (find-eps-coefficient x a n eps)))
                              interval))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance inside-interval-p-squeeze
                            (a a)
                            (b (+ a (* n eps)))
                            (c (+ a (* eps (find-eps-coefficient x a n eps))))
                            (interval interval))
                 (:instance find-eps-coefficient-upper-bound)
                 (:instance find-eps-coefficient-lower-bound))
           :in-theory (disable inside-interval-p-squeeze
                               find-eps-coefficient-upper-bound
                               find-eps-coefficient-lower-bound))))

(defthm find-eps-coefficient-useful
  (implies (and (realp x)
                (realp a)
                (natp n)
                (realp eps)
                (<= 0 eps)
                (<= a x)
                (<= x (+ a (* n eps))))
           (and (<= (+ a (* (find-eps-coefficient x a n eps) eps))
                    x)
                (<= x (+ a (* (1+ (find-eps-coefficient x a n eps)) eps)))))
  )

(defthm find-eps-coefficient-even-more-useful 
  (implies (and (realp x)
                (realp a)
                (natp n)
                (realp eps)
                (<= 0 eps)
                (<= a x)
                (<= x (+ a (* n eps))))
           (and (<= 0 (- x (+ a (* (find-eps-coefficient x a n eps) eps))))
                (<= (- x (+ a (* (find-eps-coefficient x a n eps) eps)))
                    eps)))
  :rule-classes nil
  )

(defthm find-eps-coefficient-most-useful
  (implies (and (realp x)
                (realp a)
                (natp n)
                (realp eps)
                (<= 0 eps)
                (i-small eps)
                (<= a x)
                (<= x (+ a (* n eps))))
           (i-close x (+ a (* (find-eps-coefficient x a n eps) eps))))
  :hints (("Goal"
           :use ((:instance find-eps-coefficient-even-more-useful )
                 (:instance small-if-<-small
                            (x eps)
                            (y (+ (- A)
                                  X
                                  (- (* EPS (FIND-EPS-COEFFICIENT X A N EPS))))))
                 )
           :in-theory (e/d (i-close)
                           (find-eps-coefficient
                            small-if-<-small
                            |(- (+ x y))|
                            PREFER-POSITIVE-ADDENDS-<
                            ))
           )
          )
  )


(defun find-close-in-grid (z z0 n eps)
  (complex (+ (realpart z0)
              (* eps (find-eps-coefficient (realpart z) (realpart z0) n eps)))
           (+ (imagpart z0)
              (* eps (find-eps-coefficient (imagpart z) (imagpart z0) n eps)))))

(defthm find-close-in-grid-inside-region
  (implies (and (acl2-numberp z0)
                (natp n)
                (realp eps)
                (<= 0 eps)
                (i-small eps)
                (region-p region)
                (inside-region-p z0 region)
                (inside-region-p (+ z0 (complex (* n eps) (* n eps))) region))
           (inside-region-p (find-close-in-grid z z0 n eps)
                            region))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance find-eps-coefficient-inside-interval
                            (x (realpart z))
                            (a (realpart z0))
                            (interval (car region)))
                 (:instance find-eps-coefficient-inside-interval
                            (a (imagpart z0))
                            (x (imagpart z))
                            (interval (cdr region))))
           :in-theory (disable find-eps-coefficient-inside-interval))))


(defthm find-close-in-grid-is-close
  (implies (and (acl2-numberp z)
                (acl2-numberp z0)
                (natp n)
                (realp eps)
                (<= 0 eps)
                (i-small eps)
                (<= (realpart z0)
                    (realpart z))
                (<= (imagpart z0)
                    (imagpart z))
                (<= (realpart z)
                    (+ (realpart z0)
                       (* n eps)))
                (<= (imagpart z)
                    (+ (imagpart z0)
                       (* n eps))))
           (i-close z (find-close-in-grid z z0 n eps)))
  :hints (("Goal"
           :use ((:instance find-eps-coefficient-most-useful
                            (x (realpart z))
                            (a (realpart z0)))
                 (:instance find-eps-coefficient-most-useful
                            (x (imagpart z))
                            (a (imagpart z0)))
                 (:instance complex-close
                            (z1 z)
                            (z2 (find-close-in-grid z z0 n eps))))))
  :rule-classes nil)

(defthm find-close-in-grid-is-more-than-min-lemma-0
  (implies (and (realp x1)
                (realp x2)
                (REALP y1)
                (REALP Y2))
           (EQUAL (+ (complex x1 y1) (COMPLEX x2 y2))
                  (COMPLEX (+ x1 x2)
                           (+ y1 y2))))
  :hints (("Goal"
           :use ((:instance complex-definition
                            (x x1)
                            (y y1))
                 (:instance complex-definition
                            (x x2)
                            (y y2))
                 (:instance complex-definition
                            (x (+ x1 x2))
                            (y (+ y1 y2))))))
  :rule-classes nil)
  
(defthm find-close-in-grid-is-more-than-min-lemma-1
  (implies (and (acl2-numberp z0)
                (realp x)
                (realp y))
           (equal (+ z0 (complex x y))
                  (complex (+ x (realpart z0))
                           (+ y (imagpart z0)))))
  :hints (("Goal"
           :use ((:instance find-close-in-grid-is-more-than-min-lemma-0
                            (x1 (realpart z0))
                            (y1 (imagpart z0))
                            (x2 x)
                            (y2 y)))
           ))
  )

(defthm find-close-in-grid-is-more-than-min-lemma-2
  (implies (and (acl2-numberp z)
                (acl2-numberp z0)
                (natp n)
                (realp eps)
                (<= 0 eps)
                (i-small eps)
                (<= (realpart z0)
                    (realpart z))
                (<= (imagpart z0)
                    (imagpart z))
                (<= (realpart z)
                    (+ (realpart z0)
                       (* n eps)))
                (<= (imagpart z)
                    (+ (imagpart z0)
                       (* n eps))))
           (<= (crvcfn context (find-min-crvcfn-z-n (realpart z0) (imagpart z0) context z0 0 0 n eps))
               (crvcfn context (find-close-in-grid z z0 n eps))))
  :hints (("Goal"
           :use ((:instance find-min-crvcfn-z-n-minimum-in-grid
                            (i (find-eps-coefficient (realpart z) (realpart z0) n eps))
                            (j (find-eps-coefficient (imagpart z) (imagpart z0) n eps))
                            (x0 (realpart z0))
                            (y0 (imagpart z0))
                            (min-z z0)))))
  :rule-classes nil)

(defthm find-close-in-grid-is-more-than-min-lemma-3
  (implies (and (acl2-numberp z)
                (acl2-numberp z0)
                (natp n)
                (realp eps)
                (<= 0 eps)
                (i-small eps)
                (<= (realpart z0)
                    (realpart z))
                (<= (imagpart z0)
                    (imagpart z))
                (<= (realpart z)
                    (+ (realpart z0)
                       (* n eps)))
                (<= (imagpart z)
                    (+ (imagpart z0)
                       (* n eps))))
           (<= (standard-part (crvcfn context (find-min-crvcfn-z-n (realpart z0) (imagpart z0) context z0 0 0 n eps)))
               (standard-part (crvcfn context (find-close-in-grid z z0 n eps)))))
  :hints (("Goal"
           :use ((:instance find-close-in-grid-is-more-than-min-lemma-2)
                 (:instance standard-part-<=
                            (x (crvcfn context (find-min-crvcfn-z-n (realpart z0) (imagpart z0) context z0 0 0 n eps)))
                            (y (crvcfn context (find-close-in-grid z z0 n eps))))
                 )
           :in-theory (disable standard-part-<=)
           )
          )
  :rule-classes nil)

(defthm find-close-in-grid-is-more-than-min-lemma-4
  (implies (and (acl2-numberp z)
                (standardp z)
                (acl2-numberp z0)
                (natp n)
                (realp eps)
                (<= 0 eps)
                (i-small eps)
                (<= (realpart z0)
                    (realpart z))
                (<= (imagpart z0)
                    (imagpart z))
                (<= (realpart z)
                    (+ (realpart z0)
                       (* n eps)))
                (<= (imagpart z)
                    (+ (imagpart z0)
                       (* n eps))))
           (inside-region-p z (cons (interval (realpart z0) (+ (realpart z0) (* n eps)))
                                    (interval (imagpart z0) (+ (imagpart z0) (* n eps))))))
  :hints (("Goal"
           :use ((:instance inside-interval-p-squeeze
                            (a (realpart z0))
                            (b (+ (realpart z0) (* n eps)))
                            (c z)
                            (interval (interval (realpart z0) (+ (realpart z0) (* n eps)))))
                 (:instance inside-interval-p-squeeze
                            (a (imagpart z0))
                            (b (+ (imagpart z0) (* n eps)))
                            (c z)
                            (interval (interval (imagpart z0) (+ (imagpart z0) (* n eps))))))
           :in-theory (e/d (interval-definition-theory) (inside-interval-p-squeeze))
           ))
  :rule-classes nil
  )

(defthm find-close-in-grid-is-more-than-min-lemma-5
  (implies (and (acl2-numberp z)
                (standardp z)
                (acl2-numberp z0)
                (natp n)
                (realp eps)
                (<= 0 eps)
                (i-small eps)
                (region-p region)
                (inside-region-p z0 region)
                (inside-region-p (+ z0 (complex (* n eps) (* n eps))) region)
                (<= (realpart z0)
                    (realpart z))
                (<= (imagpart z0)
                    (imagpart z))
                (<= (realpart z)
                    (+ (realpart z0)
                       (* n eps)))
                (<= (imagpart z)
                    (+ (imagpart z0)
                       (* n eps))))
           (inside-region-p z region))
  :hints (("Goal"
           :use ((:instance find-close-in-grid-is-more-than-min-lemma-4)
                 )
           ))
  :rule-classes nil
  )
           
(defthm-std standard-crvcfn
  (implies (and (standardp context)
                (standardp z))
           (standardp (crvcfn context z))))

(defthm limited-crvcfn
  (implies (and (standardp context)
                (standardp z))
           (not (i-large (crvcfn context z))))
  :hints (("Goal"
           :use ((:instance STANDARDS-ARE-LIMITED
                            (x (crvcfn context z))))
           :in-theory (disable STANDARDS-ARE-LIMITED))))

(defthm find-close-in-grid-is-more-than-min-lemma-6
  (implies (and (acl2-numberp z)
                (standardp z)
                (acl2-numberp z0)
                (natp n)
                (realp eps)
                (<= 0 eps)
                (i-small eps)
                (standardp context)
                (inside-region-p z0 (crvcfn-domain))
                (inside-region-p (+ z0 (complex (* n eps) (* n eps))) (crvcfn-domain))
                (<= (realpart z0)
                    (realpart z))
                (<= (imagpart z0)
                    (imagpart z))
                (<= (realpart z)
                    (+ (realpart z0)
                       (* n eps)))
                (<= (imagpart z)
                    (+ (imagpart z0)
                       (* n eps))))
           (equal (standard-part (crvcfn context (find-close-in-grid z z0 n eps)))
                  (standard-part (crvcfn context z))))
  :hints (("Goal"
           :use ((:instance find-close-in-grid-is-close)
                 (:instance crvcfn-continuous
                            (z z)
                            (z2  (find-close-in-grid z z0 n eps)))
                 (:instance close-x-y->same-standard-part
                            (x (crvcfn context z))
                            (y (crvcfn context (find-close-in-grid z z0 n eps)))
                 )
                 (:instance standard-part-<=
                            (x (crvcfn context (find-min-crvcfn-z-n (realpart z0) (imagpart z0) context z0 0 0 n eps)))
                            (y (crvcfn context (find-close-in-grid z z0 n eps))))
                 (:instance find-close-in-grid-is-more-than-min-lemma-4)
                 (:instance find-close-in-grid-is-more-than-min-lemma-5
                            (region (crvcfn-domain)))
                 (:instance two-points-make-a-subregion
                            (z1 z0)
                            (z2 (+ z0 (complex (* n eps) (* n eps))))
                            (region (crvcfn-domain)))
                 (:instance find-close-in-grid-inside-region
                            (region (crvcfn-domain)))
                 )
           :in-theory (disable standard-part-<=
                               crvcfn-continuous
                               close-x-y->same-standard-part
                               find-close-in-grid
                               find-close-in-grid-inside-region)
          )
  )
  :rule-classes nil)
  
(defthm find-close-in-grid-is-more-than-min-lemma-7
  (implies (and (acl2-numberp z)
                (standardp z)
                (acl2-numberp z0)
                (natp n)
                (realp eps)
                (<= 0 eps)
                (i-small eps)
                (standardp context)
                (inside-region-p z0 (crvcfn-domain))
                (inside-region-p (+ z0 (complex (* n eps) (* n eps))) (crvcfn-domain))
                (<= (realpart z0)
                    (realpart z))
                (<= (imagpart z0)
                    (imagpart z))
                (<= (realpart z)
                    (+ (realpart z0)
                       (* n eps)))
                (<= (imagpart z)
                    (+ (imagpart z0)
                       (* n eps))))
           (<= (standard-part (crvcfn context (find-min-crvcfn-z-n (realpart z0) (imagpart z0) context z0 0 0 n eps)))
               (crvcfn context z)))
  :hints (("Goal"
           :use ((:instance find-close-in-grid-is-more-than-min-lemma-3)
                 (:instance find-close-in-grid-is-more-than-min-lemma-6)
                 (:instance standard-part-of-standardp
                            (x (crvcfn context z)))
                 )
           :in-theory (disable standard-part-<=
                               standard-part-of-standardp
                               FIND-CLOSE-IN-GRID)
           )
          )
  :rule-classes nil)

(defthm-std standard-car-crvcfn-domain
  (standardp (car (crvcfn-domain))))

(defthm-std standard-cdr-crvcfn-domain
  (standardp (cdr (crvcfn-domain))))

(defthm-std standard-car-region
  (implies (standardp region)
           (standardp (car region))))

(defthm-std standard-cdr-region
  (implies (standardp region)
           (standardp (cdr region))))


(defthm crvcfn-standard-part
  (implies (and (i-limited z)
                (standardp context)
                (inside-region-p z region)
                (standardp region)
                (closed-region-p region)
                (subregion-p region (crvcfn-domain))
                )
           (equal (crvcfn context (standard-part z))
                  (standard-part (crvcfn context z))))
  :hints (("Goal"
           :use ((:instance crvcfn-continuous
                            (z (standard-part z))
                            (z2 z))
                 (:instance close-x-y->same-standard-part
                            (x (crvcfn context (standard-part z)))
                            (y (crvcfn context z)))
                 (:instance standard-part-inside-interval
                            (x (realpart z))
                            (interval (car region)))
                 (:instance standard-part-inside-interval
                            (x (imagpart z))
                            (interval (cdr region)))
                 (:instance regionp-crvcfn-domain)
                 (:instance complex-large-1
                            (x z))
                 (:instance weak-interval-inclusive-right-endpoint-type-prescription
                            (interval (car region)))
                 )
           :in-theory (disable crvcfn-continuous
                               close-x-y->same-standard-part
                               standard-part-inside-interval
                               regionp-crvcfn-domain
                               weak-interval-inclusive-right-endpoint-type-prescription
                               complex-large-1))
          )
  :rule-classes nil)

(defthm find-min-crvcfn-z-limited-direct
  (implies
   (and (standardp context)
        (standardp z)
        (standardp s)
        (acl2-numberp z)
        (inside-interval-p (realpart z)
                           (car (crvcfn-domain)))
        (inside-interval-p (imagpart z)
                           (cdr (crvcfn-domain)))
        (inside-interval-p (+ s (realpart z))
                           (car (crvcfn-domain)))
        (inside-interval-p (+ s (imagpart z))
                           (cdr (crvcfn-domain)))
        (realp s)
        (< 0 s))
    (i-limited (find-min-crvcfn-z-n (realpart z)
                                    (imagpart z)
                                    context z 0 0 (i-large-integer)
                                    (* (/ (i-large-integer)) s))))
  :hints (("Goal"
           :use ((:instance limited-if-in-standard-region
                            (z (find-min-crvcfn-z-n (realpart z)
                                                    (imagpart z)
                                                    context z 0 0 (i-large-integer)
                                                    (* (/ (i-large-integer)) s)))
                            (region (cons (interval (realpart z) (+ (realpart z) s))
                                          (interval (imagpart z) (+ (imagpart z) s)))))
                 (:instance find-min-crvcfn-z-n-minimum-inside-region-corollary-1
                            (i 0)
                            (j 0)
                            (n (i-large-integer))
                            (x0 (realpart z))
                            (y0 (imagpart z))
                            (eps (* (/ (i-large-integer)) s)))
                 )))
  )

(defthm subinterval-if-endpoints-in-interval
  (implies (and (inside-interval-p x1 interval)
                (inside-interval-p x2 interval)
                (<= x1 x2)
                (interval-p interval))
           (subinterval-p (interval x1 x2)
                          interval))
  :hints (("Goal"
           :in-theory (enable interval-definition-theory))))

(defthm interval-p-car-crvcfn-domain
  (interval-p (car (crvcfn-domain)))
  :hints (("Goal"
           :use ((:instance regionp-crvcfn-domain))
           :in-theory (disable regionp-crvcfn-domain))))

(defthm interval-p-cdr-crvcfn-domain
  (interval-p (cdr (crvcfn-domain)))
  :hints (("Goal"
           :use ((:instance regionp-crvcfn-domain))
           :in-theory (disable regionp-crvcfn-domain))))

;;; IMPORTANT
(defthm-std find-min-crvcfn-is-min
  (implies (and (acl2-numberp z)
                (acl2-numberp z0)
                (realp s)
                (< 0 s)
                (inside-region-p z0 (crvcfn-domain))
                (inside-region-p (+ z0 (complex s s)) (crvcfn-domain))
                (<= (realpart z0) (realpart z))
                (<= (imagpart z0) (imagpart z))
                (<= (realpart z) (+ (realpart z0) s))
                (<= (imagpart z) (+ (imagpart z0) s)))
           (<= (crvcfn context (find-min-crvcfn-z context z0 s))
               (crvcfn context z)))
  :hints (("Goal"
           :use ((:instance find-close-in-grid-is-more-than-min-lemma-7
                            (n (i-large-integer))
                            (eps (/ s (i-large-integer)))
                            )
                 (:instance crvcfn-standard-part
                            (z (FIND-MIN-CRVCFN-Z-N (REALPART Z0)
                                            (IMAGPART Z0)
                                            CONTEXT Z0 0 0 (I-LARGE-INTEGER)
                                            (* (/ (I-LARGE-INTEGER)) S)))
                            (region (cons (interval (realpart z0)
                                                    (+ (realpart z0) s))
                                          (interval (imagpart z0)
                                                    (+ (imagpart z0) s)))))
                 (:instance find-min-crvcfn-z-n-minimum-inside-region-corollary-1
                            (i 0)
                            (j 0)
                            (x0 (realpart z0))
                            (y0 (imagpart z0))
                            (n (i-large-integer))
                            (eps (/ s (i-large-integer))))
                 (:instance subinterval-if-endpoints-in-interval
                            (x1 (realpart z0))
                            (x2 (+ s (realpart z0)))
                            (interval (car (crvcfn-domain))))
                 (:instance subinterval-if-endpoints-in-interval
                            (x1 (imagpart z0))
                            (x2 (+ s (imagpart z0)))
                            (interval (cdr (crvcfn-domain))))
                 )
           :in-theory (disable subinterval-if-endpoints-in-interval)
           )
          )
  :rule-classes nil)


(defun-sk is-minimum-point-in-region (context zmin z0 s)
  (forall (z)
	  (implies (and (acl2-numberp z)
                        (acl2-numberp z0)
                        (realp s)
                        (< 0 s)
			(inside-region-p z (cons (interval (realpart z0)
                                                           (+ s (realpart z0)))
                                                 (interval (imagpart z0)
                                                           (+ s (imagpart z0))))))
		   (<= (crvcfn context zmin) (crvcfn context z)))))

(defun-sk achieves-minimum-point-in-region (context z0 s)
  (exists (zmin)
          (implies (and (acl2-numberp z0)
                        (realp s)
                        (< 0 s))
                   (and ;(acl2-numberp zmin)
                        (inside-region-p zmin (cons (interval (realpart z0)
                                                              (+ s (realpart z0)))
                                                    (interval (imagpart z0)
                                                              (+ s (imagpart z0)))))
                        (is-minimum-point-in-region context zmin z0 s)))))


;; (defthm minimum-point-in-region-theorem-sk
;;   (implies (and (acl2-numberp z0)
;;                 (realp s)
;;                 (< 0 s)
;;                 (inside-region-p z0 (crvcfn-domain))
;; 		(inside-region-p (+ z0 (complex s s)) (crvcfn-domain)))
;; 	   (achieves-minimum-point-in-region context z0 s))
;;   :hints (("Goal"
;; 	   :use ((:instance achieves-minimum-point-in-region-suff
;; 			    (zmin (find-min-crvcfn-z context z0 s))
;;                             )
;;                  (:instance find-min-crvcfn-z-inside-region-1
;;                             (z z0))
;; 		 (:instance find-min-crvcfn-is-min
;; 			    (z (is-minimum-point-in-region-witness context (find-min-crvcfn-z context z0 s) z0 s))))
;; 	   :in-theory (disable achieves-minimum-point-in-region-suff))))

(defthm minimum-point-in-region-theorem-sk-lemma
  (implies (and (acl2-numberp z0)
                (realp s)
                (< 0 s)
                (inside-region-p z0 (crvcfn-domain))
		(inside-region-p (+ z0 (complex s s)) (crvcfn-domain)))
	   (is-minimum-point-in-region context (find-min-crvcfn-z context z0 s) z0 s))
  :hints (("Goal"
           :use ((:instance is-minimum-point-in-region
                            (zmin  (find-min-crvcfn-z context z0 s)))
                 (:instance find-min-crvcfn-is-min
                            (z (is-minimum-point-in-region-witness context (find-min-crvcfn-z context z0 s) z0 s)))))
          ("Subgoal 4"
           :in-theory (enable interval-definition-theory))
          ("Subgoal 3"
           :in-theory (enable interval-definition-theory))
          ("Subgoal 2"
           :in-theory (enable interval-definition-theory))
          ("Subgoal 1"
           :in-theory (enable interval-definition-theory))
          ))

;;; IMPORTANT

(defthm minimum-point-in-region-theorem-sk
  (implies (and (acl2-numberp z0)
                (realp s)
                (< 0 s)
                (inside-region-p z0 (crvcfn-domain))
		            (inside-region-p (+ z0 (complex s s)) (crvcfn-domain)))
	   (achieves-minimum-point-in-region context z0 s))
  :hints (("Goal"
	   :use ((:instance achieves-minimum-point-in-region-suff
			    (zmin (find-min-crvcfn-z context z0 s))
                            )
                 (:instance minimum-point-in-region-theorem-sk-lemma)
                 (:instance find-min-crvcfn-z-inside-region-1
                            (z z0)))
	   :in-theory (disable achieves-minimum-point-in-region-suff
                               find-min-crvcfn-z-inside-region-1))))


;;; And now we specialize this result for norm-ccfn

(defun-sk norm-ccfn-is-minimum-point-in-region (context zmin z0 s)
  (forall (z)
	  (implies (and (acl2-numberp z)
                        (acl2-numberp z0)
                        (realp s)
                        (< 0 s)
			(inside-region-p z (cons (interval (realpart z0)
                                                           (+ s (realpart z0)))
                                                 (interval (imagpart z0)
                                                           (+ s (imagpart z0))))))
		   (<= (norm-ccfn context zmin) (norm-ccfn context z)))))

(defun-sk norm-ccfn-achieves-minimum-point-in-region (context z0 s)
  (exists (zmin)
          (implies (and (acl2-numberp z0)
                        (realp s)
                        (< 0 s))
                   (and ;(acl2-numberp zmin)
                        (inside-region-p zmin (cons (interval (realpart z0)
                                                              (+ s (realpart z0)))
                                                    (interval (imagpart z0)
                                                              (+ s (imagpart z0)))))
                        (norm-ccfn-is-minimum-point-in-region context zmin z0 s)))))


(defthm norm-ccfn-minimum-point-in-region-theorem-sk
  (implies (and (acl2-numberp z0)
                (realp s)
                (< 0 s)
                (inside-region-p z0 (ccfn-domain))
		            (inside-region-p (+ z0 (complex s s)) (ccfn-domain)))
	   (norm-ccfn-achieves-minimum-point-in-region context z0 s))
  :hints (("Goal"
	   :by (:functional-instance minimum-point-in-region-theorem-sk
                                     (crvcfn norm-ccfn)
                                     (crvcfn-domain ccfn-domain)
                                     (achieves-minimum-point-in-region norm-ccfn-achieves-minimum-point-in-region)
                                     (achieves-minimum-point-in-region-witness norm-ccfn-achieves-minimum-point-in-region-witness)
                                     (is-minimum-point-in-region norm-ccfn-is-minimum-point-in-region)
                                     (is-minimum-point-in-region-witness norm-ccfn-is-minimum-point-in-region-witness)
                                     ))
          ("Subgoal 6"
           :use ((:instance NORM-CCFN-ACHIEVES-MINIMUM-POINT-IN-REGION-SUFF)))
          ("Subgoal 4"
           :use ((:instance NORM-CCFN-IS-MINIMUM-POINT-IN-REGION-NECC)))
          ("Subgoal 2"
           :use ((:instance norm-ccfn-continuous)))
          ("Subgoal 1"
           :use ((:instance ccfn-domain-non-trivial)))
          ))
                                       
