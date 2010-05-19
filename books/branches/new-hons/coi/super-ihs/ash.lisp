#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#
(in-package "ACL2")

;make the inclusion of arithmetic stuff local?
(include-book "arithmetic")
(include-book "evenp")

(in-theory (disable ash))
(local (in-theory (disable evenp-collapse))) ;bzo

(defthm ash-when-c-is-not-an-integerp
  (implies (not (integerp c))
           (equal (ash i c)
                  (ifix i)))
  :hints (("goal" :in-theory (enable ash ifix))))

(defthm ash-when-c-is-zero
  (equal (ash i 0)
         (ifix i))
  :hints (("goal" :in-theory (enable ash ifix))))

;(in-theory (disable ash-0)) ;bzo move this to a place where ash-0 is defined

(defthm ash-when-i-is-not-an-integerp
  (implies (not (integerp i))
           (equal (ash i c)
                  0))
  :hints (("Goal" :in-theory (enable ash))))

(defthm ash-when-i-is-zero
  (equal (ash 0 count)
         0)
  :hints (("Goal" :in-theory (enable ash))))

(defthm ifix-ash
  (equal (ifix (ash x y))
         (ash x y)))

(defthm ash-negative-rewrite
  (implies (and (<= 0 n)
                (integerp n)
                )
           (equal (< (ash x n) 0)
                  (< (ifix x) 0)))
  :hints (("Goal" :in-theory (enable ash))))

;bzo think more about the type of ash
                 
(defthm equal-ash-pos-0
  (implies (<= 0 c)
           (equal (equal (ash i c) 0)
                  (equal (ifix i) 0)))
  :hints (("goal" :in-theory (enable ash))))


(defthm ash-bound1
  (implies (and (<= s 0)
                (<= x b)
                (<= 0 b)
                (integerp s)
                (integerp b)
                (integerp x)
                )
           (<= (ash x s) b))
  :hints (("goal" :in-theory (enable ash expt))))

(defthm ash-bound1a
  (implies (and (<= s 0)
                (< x b)
                (<= 0 b)
                (integerp s)
                (integerp b)
                (integerp x)
                )
           (< (ash x s) b))
  :hints (("goal" :in-theory (enable ash expt))))

(local (in-theory (disable FLOOR-OF-SHIFT-RIGHT-2)))

(defthm ash-bound2
  (implies (and (<= s 0)
                (<= b x)
                (<= b 0)
                (integerp s)
                (integerp b)
                (integerp x)
                )
           (<= b (ash x s)))
  :hints (("goal" :in-theory (enable ash expt))))




(defthm ash-bound2a
  (implies (and (<= s 0)
                (< b x)
                (< b 0)
                (integerp s)
                (integerp b)
                (integerp x)
                )
           (< b (ash x s)))
  :hints (("goal" :in-theory (e/d (ash expt) 
                                  (FLOOR-OF-SHIFT-RIGHT-2)))))

(defthm ash-bound3
  (implies (and (<= (* x (expt 2 s)) b)
                (<= 0 b)
                (integerp s)
                (integerp b)
                (integerp x)
                )
           (<= (ash x s) b))
  :hints (("goal" :in-theory (enable ash expt))))

(defthm ash-bound3a
  (implies (and (< (* x (expt 2 s)) b)
                (<= 0 b)
                (integerp s)
                (integerp b)
                (integerp x)
                )
           (< (ash x s) b))
  :hints (("goal" :in-theory (enable ash expt))))

(defthm ash-bound4
  (implies (and (<= b (* x (expt 2 s)))
                (<= b 0)
                (integerp s)
                (integerp b)
                (integerp x)
                )
           (<= b (ash x s)))
  :hints (("goal" :in-theory (enable  ash expt))))

(defthm ash-bound4a
  (implies (and (<= 0 s)
                (< b (* x (expt 2 s)))
                (< b 0)
                (integerp s)
                (integerp b)
                (integerp x)
                )
           (< b (ash x s)))
  :hints (("goal" :in-theory (enable  ash expt))))




;can't quite combine with ASH-ASH-RIGHT-TO-ASH because of the case where m<0
(defthm *ark*-ash-ash-left
  (implies (and (<= 0 m)
                (<= 0 n)
                (integerp n)
                (integerp m)
                (integerp x)
                )
           (equal (ASH (ASH x m) n)
                  (ash x (+ m n))))
  :hints (("goal" :in-theory (enable ash ; LOGOPS-RECURSIVE-DEFINITIONS-THEORY 
                                     expt
                                     ))))

;generalize?
(defthm ash-expt-neg
  (implies (and (integerp n)
                (< 0 n))
           (equal (ash (expt 2 n) (- n))
                  1))
  :hints (("goal" :in-theory (enable ;LRDT
                              ash
                              ))))

(defthm ash--1-neg
  (implies (and (<= n 0)
                (integerp n)
                )
           (equal (ash -1 n) 
                  -1))
  :hints (("goal" :in-theory (enable ash ;LRDT
                                     ))))

(defthm ash-non-decreasing 
  (implies (and (integerp k)
                (<= 0 k)
                (integerp n)
                (<= 0 n))
           (<= k (ASH k n)))
  :hints (("goal" :in-theory (enable ash expt))))

(defthm ash-1-when-c-is-negative
  (implies (< c 0)
           (equal (ASH 1 c)
                  (if (integerp c)
                      0
                    1)))
  :hints (("Goal" :in-theory (enable ash expt))))

(defthmd ash-1-expt-rewrite
  (equal (ash 1 c)
         (if (<= 0 c)
             (expt 2 c)
           (if (integerp c)
               0
             1)))
  :hints (("Goal" :in-theory (enable ash expt))))

;improve?
(defthmd ash-1-lessp
  (implies (and (integerp k)
                (<= 0 k))
           (< 0 (ASH 1 k)))
  :hints (("Goal" :in-theory (enable ash acl2::commutativity-of-* expt))))

;bzo drop hyps and generalize
(defthm ash-of-1-equal-65536
  (implies (and (integerp c)
                (<= 0 c))
           (equal (equal (ash 1 c) 65536)
                  (equal c 16)))
  :hints (("Goal" :cases ((< c 16) (> c 16))
           :in-theory (enable ash))))

(defthm ash-to-0
  (implies (unsigned-byte-p n x)
           (equal (ash x (- n))
                  0))
  :hints (("Goal" :in-theory (enable ash))))


;; (defthm ash-ash-right-to-ash
;;   (implies (and (<= n 0)
;;                 (integerp n)
;;                 (integerp m)
;;                 (integerp x)
;;                 )
;;            (equal (ash (ash x m) n)
;;                   (ash x (+ m n))))
;;   :hints (("goal" 
;;            :in-theory (e/d (;LRDT expt2* ;ash-as-logtail ash-as-logapp open-logcons
;;                             expt
;;                             ash
;;                                  ) (EXPT-2-CRUNCHER)))))



;bzo make a version without the free variable
;; (DEFTHM ASH-GOES-TO-0
;;   (IMPLIES (AND (UNSIGNED-BYTE-P SIZE I)
;;                 (INTEGERP COUNT)
;;                 (<= COUNT 0)
;;                 (<= SIZE (- COUNT)))
;;            (EQUAL (ASH I COUNT) 0))
;; )

(defthm ash-not-equal
  (implies (and (integerp i)
                (integerp j)
                (not (equal i j)))
           (not (equal (ash i 1) (ash j 1))))
  :hints (("Goal" :in-theory (enable ash))))

;generalize
(defthm ash-evenp
  (evenp (ash i 1))
  :hints (("Goal" :in-theory (enable ash))))

(defthm ash-not-equal
  (implies (and (integerp i)
                (integerp j)
                (not (equal i j)))
           (not (equal (ash i 1) (ash j 1))))
  :hints (("Goal" :in-theory (enable ash))))

;bzo gen
(defthm ash-1-monotonic
  (implies (and (integerp i)
                (integerp j))
           (equal (< (ash i 1) (ash j 1))
                  (< i j)))
  :hints (("Goal" :in-theory (enable ash))))


;can we get rid of this?
;or generalize?  ash isn't equal to something odd?
;foward chain to evenp/oddp facts?
(defthm ash-plus1-not-equal
  (implies (and (integerp i)
                (integerp j)
                (not (equal i j)))
           (not (equal (ash i 1) (+ 1 (ash j 1)))))
  :hints (("Goal" :in-theory (enable ACL2::EVEN-ODD-DIFFERENT-1
                                     ACL2::EVEN-ODD-DIFFERENT-2))))

(defthm ash-plus-addr2
  ;; notice this is rule-classes nil because it loops with
  ;; several lemmas in the ash theory.
  (implies (and (integerp addr)
                (integerp k))
           (equal (+ (* 2 k) (ash addr 1))
                  (ash (+ k addr) 1)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable ash acl2::commutativity-of-*))))



;generalize the 1
(defthm ash-equal-constant
  (implies (and (syntaxp (quotep k))
                (acl2-numberp k)
                (integerp x) ;drop?
                )
           (equal (EQUAL (ASH x 1) k)
                  (EQUAL x (/ k 2))))
  :hints (("Goal" :in-theory (enable ash))))

(defthmd ash-+-pos
  (implies (and (integerp x)
                (integerp y)
                (integerp m)
                (<= 0 m))
           (equal (ash (+ x y) m)
                  (+ (ash x m) (ash y m))))
  :hints (("goal" :in-theory (enable ash))))

;handle  (< 0 (ash v n))?

;move
(defthm <=-0-ash
  (implies (and (integerp v)
                (integerp n)
                )
           (equal (< (ash v n) 0)
                  (< v 0)))
  :hints (("goal" :in-theory (enable ASH-BOUND3A
                                     ASH-BOUND4
                                     ))))

(defthm half-ash-by-two
  (equal (* 1/2 (ash x 1))
         (ifix x))
  :hints (("Goal" :in-theory (enable ash))))

(defthm evenp-of-ash
  (equal (evenp (ash 1 n))
         (and (integerp n)
              (not (equal 0 n))))
  :hints (("Goal" :cases ((< 0 n))
           :in-theory (e/d (oddp evenp ;bzo prove a rule for evenp
                                 ash) (acl2::evenp-collapse)))))

(defthm oddp-of-ash
  (equal (oddp (ash 1 n))
         (or (not (integerp n))
             (equal 0 n)))
  :hints (("Goal" :cases ((< 0 n))
           :in-theory (e/d (oddp) ()))))


(defthm ash-recollapse
  (implies (and (< 0 n)
                (integerp n))
           (equal (* 2 (ash x (+ -1 n)))
                  (ash x n)))
  :hints (("Goal" :in-theory (enable ash))))

;bzo decide whether to use ash or *2
(defthm ash-times-2-hack
  (implies (integerp j)
           (equal (equal (ash j 1) (* 2 j))
                  t))
  :hints (("Goal" :in-theory (enable ash))))
