#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#
(in-package "ACL2")
(include-book "logpair")

(local (in-theory (enable FALSIFY-UNSIGNED-BYTE-P)))

;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;           
;; signed-byte-p, unsigned-byte-p
;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;


(defthm unsigned-byte-p-+-helper
  (implies (and (unsigned-byte-p n x)
                (unsigned-byte-p n y)
                (unsigned-byte-p 1 c)
                (integerp n)
                (< 0 n)
                )
           (equal (unsigned-byte-p n (+ x y c))
                  (not (logbitp n (+ x y c)))))
  :rule-classes nil
  :hints (("goal" :in-theory (enable ash LRDT open-logcons))))

;; included in overflow-bits theory
(defthm unsigned-byte-p-+
  (implies (and (unsigned-byte-p n x)
                (unsigned-byte-p n y)
                (integerp n)
                (< 0 n)
                )
           (equal (unsigned-byte-p n (+ x y))
                  (not (logbitp n (+ x y)))))
  :hints (("goal" :use (:instance unsigned-byte-p-+-helper (c 0)))))

;; included in overflow-bits theory
(defthm unsigned-byte-p-+-bridge2
  (implies (and (integerp x)
                (integerp z)
                (integerp n)
                (< 0 n)
                (unsigned-byte-p n x)
                (unsigned-byte-p n y))
           (equal (unsigned-byte-p n (+ 1 x y))
                  (not (logbitp n (+ 1 x y)))))
  :hints (("goal" :use (:instance unsigned-byte-p-+-helper (c 1)))))

(defthm signed-byte-p-+
  (implies (and (signed-byte-p (1- n) x)
                (signed-byte-p (1- n) y)
                (integerp n)
                (< 0 n)
                )
           (signed-byte-p n (+ x y)))
  :hints (("goal" :in-theory (enable signed-byte-p EXPONENTS-ADD-UNRESTRICTED))))

(defthm signed-byte-p-unsigned-byte-p
  (implies (and (unsigned-byte-p free x) ;free is a free variable
                (< free n)
                )
           (equal (signed-byte-p n x)
                  (integerp n)))
  :hints (("goal" 
           :in-theory (enable signed-byte-p unsigned-byte-p)
           :use ((:instance EXPT-IS-INCREASING-FOR-BASE>1
                            (r 2)
                            (i free)
                            (j (1- n)))))))
           
(defthm unsigned-byte-p-subtype
  (implies (and (unsigned-byte-p free x) ;free is a free variable
                (<= free n)
                )
           (equal (unsigned-byte-p n x)
                  (integerp n)  
                  ))
  :hints (("goal" 
           :in-theory (enable signed-byte-p unsigned-byte-p)
           :use ((:instance EXPT-IS-INCREASING-FOR-BASE>1
                            (r 2)
                            (i free)
                            (j n))))))


(encapsulate
 ()
 (local (defthmd signed-byte-p-subtype-helper
          (implies (and (signed-byte-p free x)
                        (integerp free)
                        (integerp n)
                        (integerp x)
                        (<= free n))
                   (signed-byte-p n x))
          :hints (("goal" 
                   :in-theory (enable signed-byte-p unsigned-byte-p)
                   :use ((:instance EXPT-IS-INCREASING-FOR-BASE>1
                                    (r 2)
                                    (i (1- free))
                                    (j (1- n))))))))

 (defthm signed-byte-p-subtype
   (implies (and (signed-byte-p free x)
                 (<= free n)
                 )
            (equal (signed-byte-p n x)
                   (integerp n)))
   :hints (("Goal" :use (:instance signed-byte-p-subtype-helper)))))

;make a version that matches on constants?
(defthm sbp-bound
  (implies (signed-byte-p (1+ n) x)
           (and (<= (- (expt 2 n)) x)
                (<= x (+ -1 (expt 2 n)))))
  :hints (("goal" :in-theory (enable signed-byte-p))))

;disable?
(defthm sbp-bound-1
  (implies (and (signed-byte-p n x)
                (<= (expt 2 (1- n)) m))
           (and (<= (- m) x)
                (<= x (+ -1 m))))
  :hints (("goal" :in-theory (enable signed-byte-p))))
 
(defthm unsigned-byte-p-logcdr-bridge5
  (implies (and (unsigned-byte-p (1+ n) (1+ x))
                (equal (logcar x) 1)
                (integerp x)
                (integerp n)
                (<= 0 x)
                (<= 0 n)
                )
           (unsigned-byte-p n (1+ (logcdr x))))
  :hints (("goal"
           :use ((:instance unsigned-byte-p-of-logcdr (x (1+ x))))))
  )

(defthm signed-byte-p--1
 (implies (and (signed-byte-p (1- n) x)
               (integerp n)
               (integerp x)
               (< 0 n))
          (signed-byte-p n (- x)))
 :hints (("goal" :in-theory (enable signed-byte-p EXPONENTS-ADD-UNRESTRICTED)))
 :rule-classes ((:forward-chaining :trigger-terms ((- x)))))

(defthm signed-byte-p--2
 (implies (and (signed-byte-p n x)
               (integerp n)
               (integerp x)
               (<= 0 n)
               (not (equal x (- (expt 2 (1- n))))))
          (signed-byte-p n (- x)))
 :hints (("goal" :in-theory (enable signed-byte-p expt))))

(defthm unsigned-byte-p-ash-neg
  (implies (and (<= m 0)
                (integerp n)
                (integerp m)
                (integerp x)
                (<= 0 n)
                )
           (equal (unsigned-byte-p n (ash x m))
                  (unsigned-byte-p (- n m) x)))
  :hints (("goal" :in-theory (enable LRDT))))

(defthm unsigned-byte-p-ash-pos
  (implies (and (<= 0 m)
                (integerp n)
                (integerp m)
                (<= 0 n)
                (integerp x))
           (equal (unsigned-byte-p n (ash x m))
                  (unsigned-byte-p (max 0 (- n m)) x)))
  :hints (("goal" 
           :in-theory (e/d (LRDT 
                            unsigned-byte-p*) 
                           (ash* ;fixes a loop that manifested itself in the move to 3.0
                            open-logcons)))))


(defthm arith-cancel
  (implies (and (rationalp x)
                (rationalp y)
                (< 0 y)
                )
           (equal (< (* 2 X y) y)
                  (< (* 2 X) 1)))
  :hints (("Goal" :nonlinearp t)))


;gen
;make alt
(defthm signed-byte-p-of-shift
  (implies (and (integerp x)
                (integerp m)
                (integerp n)
                (< 0 n)
                (<= 0 m)
                (<= 0 x)
                (<= m n)
                )
           (equal (SIGNED-BYTE-P N (* X (EXPT 2 M)))
                  (if (equal 0 x)
                      t
                    (SIGNED-BYTE-P (- N m) X))))
 
  :otf-flg t
  :hints (("Goal" ; :induct (logcdr-induction x)
;:nonlinearp t
           :cases ((< x 0))
           :in-theory (enable ;lrdt 
                       SIGNED-BYTE-P
                       EXPONENTS-ADD-UNRESTRICTED
                       ))))

;; (defthm signed-byte-p-of-shift2
;;   (implies (and (integerp x)
;;                 (integerp m)
;;                 (integerp n)
;;                 (< 0 n)
;;                 (<= 0 m)
;; ;'                (<= 0 x)
;;                 (<= m n)
;;                 )
;;            (equal (SIGNED-BYTE-P N (* X (EXPT 2 M)))
;;                   (if (equal 0 x)
;;                       t
;;                     (SIGNED-BYTE-P (- N m) X))))
;;   :hints (("Goal" :in-theory (disable signed-byte-p-of-shift)
;;            :use ((:instance signed-byte-p-of-shift)
;;                  (:instance signed-byte-p-of-shift (x (- x)))))))
           

;;   :otf-flg t
;;   :hints (("Goal" ; :induct (logcdr-induction x)
;; ;:nonlinearp t
;;            :cases ((< x 0))
;;            :in-theory (enable ;lrdt 
;;                        SIGNED-BYTE-P
;;                        EXPONENTS-ADD-UNRESTRICTED
;;                        ))))
        


(encapsulate
 ()

 (local (defthm signed-byte-p-ash-pos
          (implies (and (integerp n)
                        (integerp m)
                        (integerp x)
                        (< m n)
                        (< 0 m))
                   (equal (signed-byte-p n (ash x m))
                          (signed-byte-p (- n m) x)))
          :hints (("goal" :in-theory (e/d (;ash 
                                             LRDT 
                                             even-odd-different-2
                                             even-odd-different-1 
                                             ) 
                                          (logcdr-ash logcons-of-0 
                                                      ))))))

 (local (defthm signed-byte-p-ash-neg
          (implies (and (integerp n)
                        (integerp m)
                        (< 0 n)
                        (<= m 0)
                        (integerp x))
                   (equal (signed-byte-p n (ash x m))
                          (signed-byte-p (- n m) x)))
          :hints (("goal" :in-theory (enable LRDT)))))

 (local (defthm signed-byte-p-ash-big
          (implies (and (<= n m)
                        (< 0 n)
                        (integerp n)
                        (integerp m)
                        (integerp x)
                        )
                   (equal (signed-byte-p n (ash x m))
                          (equal x 0)))
          :hints (("goal" :induct (sub1-sub1-induction n m)
                   :in-theory (enable expt ash LOGOPS-RECURSIVE-DEFINITIONS-THEORY signed-byte-p*)))))

;bzo do something similar for the unsigned-byte-p case?
 (defthm signed-byte-p-ash
   (equal (signed-byte-p n (ash x m))
          (and (integerp n)
               (< 0 n)
               (if (integerp x)
                   (if (integerp m)
                       (if (< m n)
                           (signed-byte-p (- n m) x) ;usual case
                         (equal x 0)
                         )
                     (signed-byte-p n x))
                 t)))
   :hints (("Goal" :use (SIGNED-BYTE-P-ASH-NEG
                         SIGNED-BYTE-P-ASH-POS)
            :in-theory (disable acl2::signed-byte-p-ash-neg 
                                acl2::signed-byte-p-ash-pos
                                )))))




(defthm unsigned-byte-p-1+
  (implies (and (syntaxp (not (quotep x))) ;keeps this from firing on, e.g., (unsigned-byte-p n 500)
                (unsigned-byte-p n x)
                (integerp n)
                (<= 0 n)
                )
           (equal (unsigned-byte-p n (+ 1 x))
                  (not (equal x (1- (expt 2 n)))))) ; should this be (loghead n -1) ?
  :hints (("goal" :in-theory (enable LRDT unsigned-byte-p))))

;see unsigned-byte-p-+-helper
(defthm unsigned-byte-p-+-bridge-helper
  (implies (and (integerp n)
                (< 0 n)
                (unsigned-byte-p (1- n) x)
                (unsigned-byte-p (1- n) y)
                (unsigned-byte-p 1 c))
           (unsigned-byte-p n (+ c x y)))
  :rule-classes nil
  :hints (("goal" :in-theory (e/d (unsigned-byte-p EXPONENTS-ADD-UNRESTRICTED) 
                                  (unsigned-byte-p-+)))))

(defthm unsigned-byte-p-+-bridge
  (implies (unsigned-byte-p (1- n) x)
           (equal (unsigned-byte-p n (+ 1 x (loghead (1- n) y)))
                  (integerp n)
                  ))
  :hints (("goal" :use ((:instance unsigned-byte-p-+-bridge-helper (y (loghead (1- n) y)) (c 1)))
           :in-theory (e/d (FALSIFY-UNSIGNED-BYTE-P) ( UNSIGNED-BYTE-P-1+)))))

;more general than unsigned-byte-p-+-bridge
(defthm unsigned-byte-p-+-bridge-eric
  (implies (and (unsigned-byte-p (1- n) x)
                (unsigned-byte-p (1- n) y))
           (equal (unsigned-byte-p n (+ 1 x y))
                  (integerp n)
                  ))
  :hints (("goal" :use ((:instance unsigned-byte-p-+-bridge-helper (y y) (c 1)))
           :in-theory (e/d (FALSIFY-UNSIGNED-BYTE-P) ( UNSIGNED-BYTE-P-1+)))))

(defthm signed-byte-p-+----simple
  (implies (and (unsigned-byte-p (1- n) x)
                (unsigned-byte-p (1- n) y)
                (integerp n)
                (< 0 n)
                )
           (signed-byte-p n (+ x (- y))))
  :hints (("goal" :in-theory (enable unsigned-byte-p signed-byte-p))))

(local (in-theory (disable <-+-NEGATIVE-0-1))) ;why?

(defthm unsigned-byte-p-+-expt---simple
  (implies (and (unsigned-byte-p (1- n) x)
                (unsigned-byte-p (1- n) y)
                (integerp n)
                (< 0 n)
                )
           (unsigned-byte-p n (+ x (- y) (expt 2 (1- n)))))
  :hints (("goal" :in-theory (enable EXPONENTS-ADD-UNRESTRICTED
                                     unsigned-byte-p signed-byte-p))))

(defthm unsigned-byte-p-+-expt---simple-rewrite
  (implies (and (syntaxp (quotep k))
                (equal k (expt 2 (1- n)))
                ;(integerp k)
                (integerp n)
                (equal n (integer-length k))
                (unsigned-byte-p (1- n) x)
                (unsigned-byte-p (1- n) y))
           (unsigned-byte-p n (+ k x (- y))))
  :hints (("goal" :use (:instance unsigned-byte-p-+-expt---simple))))

(defthm unsigned-byte-p-logbit
  (equal (unsigned-byte-p n (logbit m x))
         (and (integerp n)
              (<= 0 n)
              (or (not (equal n 0))
                  (not (logbitp m x)))))
  :hints (("goal" :in-theory (enable logbit unsigned-byte-p))))




