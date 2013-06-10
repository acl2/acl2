#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#
(in-package "ACL2")

(include-book "ihs/ihs-lemmas" :dir :system)

(local (include-book "arithmetic"))
(include-book "evenp")
(include-book "unsigned-byte-p")
(include-book "ash")

(defthm logcdr-equal-0-rewrite
  (equal (equal (logcdr c) 0)
         (or (not (integerp c))
             (equal 0 c) (equal 1 c)))
  :hints (("Goal" :in-theory (enable logcdr))))

(defthmd logcdr-of-zero
  (equal (logcdr 0) 
         0)
  :hints (("goal" :in-theory (enable logcdr ifix))))

(defthm logcdr-when-i-is-not-an-integerp
  (implies (not (integerp i))
           (equal (logcdr i) 
                  0))
  :hints (("goal" :in-theory (enable logcdr ifix))))

;more like this?
(defthm logcdr-greater-than-0-rewrite
  (equal (< 0 (logcdr x))        
         (and (integerp x)
              (<= 2 x))))

(defthm integer-length-of-logcdr
  (equal (integer-length (logcdr x))
         (if (and (integerp x)
                  (not (equal -1 x))
                  (not (equal 0 x)))
             (+ -1  (integer-length x))
           0))
  :hints (("Goal" :in-theory (e/d (logcdr) (FLOOR-OF-SHIFT-RIGHT-2
                                            FLOOR-BY-TWICE-HACK))
           :do-not '(generalize eliminate-destructors))))

(defthm unsigned-byte-p-of-logcdr
  (equal (unsigned-byte-p n (logcdr x))
         (and (integerp n)
              (<= 0 n)
              (if (integerp x)
                  (unsigned-byte-p (1+ n) x)
                t)))
  :hints (("goal" 
           :in-theory (e/d (logcdr unsigned-byte-p ; expt
                                   EXPONENTS-ADD-UNRESTRICTED
                                   )
                           (FLOOR-OF-SHIFT-RIGHT-2
                            )))))

(defthm logcdr--
  (implies (integerp x)
           (equal (logcdr (- x))
                  (if (evenp x)
                      (- (logcdr x))
                    (+ -1 (- (logcdr x))))))
  :hints (("goal" :in-theory (enable logcdr))))

(encapsulate
 ()

 (local
  (defthm logcdr-ash-pos
    (implies (and (integerp n)
                  ;(integerp x)
                  (<= 0 n))
             (equal (logcdr (ash x n)) (ash x (1- n))))
    :hints (("goal" :in-theory (enable ash* ash
                                       EXPONENTS-ADD-UNRESTRICTED)))))

 (local
  (defthm logcdr-ash-neg
    (implies (and (integerp n)
;                  (integerp x)
                  (<= n 0))
             (equal (logcdr (ash x n))
                    (ash x (1- n))))
    :hints (("goal" :in-theory (enable 
                                ash 
                                EXPONENTS-ADD-UNRESTRICTED
                                )))))
             
 (defthm logcdr-ash
   (implies (and (integerp n)
                 ;(integerp x)
                 )
            (equal (logcdr (ash x n))
                   (ash x (1- n))))
   :hints (("goal" :in-theory (enable EXPONENTS-ADD-UNRESTRICTED ash)
            :cases ((< n 0))))))

;enable?
(defthmd logcdr-of-sum
  (implies (and (integerp x)
                (integerp y))
           (equal (LOGCDR (+ x y))
                  (+ (logcdr x)
                     (logcdr y)
                     (if (and (oddp x)
                              (oddp y))
                         1
                       0))))
  :hints (("Goal" :in-theory (enable LOGCDR))))

(defthm logcdr-+-1-x
  (implies (and (integerp n)
                (< 0 n))
           (equal (logcdr (+ -1 (expt 2 n)))
                  (+ -1 (expt 2 (1- n)))))
  :hints (("goal" :in-theory (enable logcdr))))

(defthm logcdr-+-1-x-v2
  (implies (integerp n)
           (equal (logcdr (+ -1 (* 2 n)))
                  (+ -1 n)))
  :hints (("goal" :in-theory (enable logcdr))))

(defthm logcdr-+-1-x-bridge
  (implies (integerp n)
           (equal (logcdr (+ -1 (- (* 2 n))))
                  (+ -1 (- n))))
  :hints (("goal" :in-theory (enable logcdr))))

(defthm logcdr---*2
  (implies (integerp x)
           (equal (logcdr (- (* 2 x)))
                  (- x)))
  :hints (("goal" :in-theory (enable logcdr))))


(defthm logcdr-expt
  (implies (and (integerp n)
                (< 0 n))
           (equal (logcdr (expt 2 n))
                  (expt 2 (1- n))))
  :hints (("goal" :in-theory (enable logcdr))))
           
(defthm logcdr---expt
  (implies (and (integerp n)
                (<= 0 n))
           (equal (logcdr (- (expt 2 n)))
                  (if (equal n 0) 
                      -1 
                    (- (expt 2 (1- n))))))
  :hints (("goal" :in-theory (enable logcdr))))

(defthm logcdr-+2
  (implies (integerp x)
           (equal (logcdr (+ 2 x)) 
                  (1+ (logcdr x))))
  :hints (("goal" :in-theory (enable logcdr))))

(defthm logcdr-*-x-expt-bridge
  (implies (and (integerp x)
                (integerp n)
                (< 0 n))
           (equal (LOGCDR (* X (EXPT 2 N)))
                  (* x (expt 2 (1- n)))))
  :hints (("goal" :in-theory (enable logcdr))))

(defthm logcdr-+--1-expt
  (implies (and (integerp n)
                (<= 0 n))
           (equal (logcdr (+ -1 (- (expt 2 n))))
                  (if (zp n)
                      -1
                    (+ -1 (- (expt 2 (1- n)))))))
  :hints (("goal" :in-theory (enable logcdr))))


(defthmd logcdr-*-1/2-expt
  (implies (and (syntaxp (quotep n))
                (integerp (* n m)))
           (equal (logcdr (* n m)) 
                  (floor (* n m) 2)))
  :hints (("goal" :in-theory (enable logcdr))))

(defthm ash-logcdr-1
  (implies (equal (logcar x) 0)
           (equal (ash (logcdr x) 1)
                  (ifix x)))
  :hints (("goal" :in-theory (enable logcdr ash))))
