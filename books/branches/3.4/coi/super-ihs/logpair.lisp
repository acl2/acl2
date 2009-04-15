#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#
(in-package "ACL2")
(include-book "basics")

(include-book "loghead")
(include-book "logtail")
(include-book "logcons")
(include-book "logcdr")
(include-book "logtail")
(include-book "logbitp")
(include-book "logbit")
(include-book "unsigned-byte-p")

(defthm logcar-lognot
  (equal (logcar (lognot a)) 
         (b-not (logcar a)))
  :hints (("Goal" :in-theory (enable  logops-recursive-definitions-theory))))

(defthm logcar-logand
  (equal (logcar (logand a b))
         (b-and (logcar a) (logcar b)))
  :hints (("goal" :in-theory (enable logops-recursive-definitions-theory)
           :use (:instance logand* (i a) (j b)))))

(defthm logcar-logior
  (equal (logcar (logior a b))
         (b-ior (logcar a) (logcar b)))
  :hints (("goal" 
           :in-theory (enable logior logops-recursive-definitions-theory))))

;move 3rd hyp to conclusion?
(defthm logcar-logext
  (implies (and (integerp n)
                (integerp x)
                (< 0 n))
           (equal (logcar (logext n x)) 
                  (logcar x)))
  :hints (("goal" :in-theory (enable logext logbitp oddp; evenp
                                     ))))


(defthm logcar-ash-neg
  (implies (and (<= n 0)
                (integerp n)
        ;        (integerp x)
                )
           (equal (logcar (ash x n)) 
                  (logbit (- n) x)))
  :hints (("goal" :in-theory (e/d (LRDT logbit) (logtail* ;was forcing
                                                 )))))

(defthm logcar-ash-both
  (implies (integerp n)
           (equal (logcar (ash x n)) 
                  (if (< 0 n)
                      0
                    (logbit (- n) x))))
  :hints (("Goal" :in-theory (disable ASH-AS-LOGTAIL))))

(defthm logcar-logtail
  (implies (and ;(integerp x)
                (integerp n)
                (<= 0 n)
                )
           (equal (logcar (logtail n x))
                  (logbit n x)))
  :hints (("goal" :in-theory (e/d (LRDT
                                     logbit) (logtail*)))))


;; (defthm logcar-+-carry-bit
;;  (implies (and (integerp a)
;;                (integerp b)
;;                (unsigned-byte-p 1 c))
;;           (equal (logcar (+ a b c))
;;                  (b-xor (logcar a) (b-xor (logcar b) c)))))

;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;
;; logcdr
;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;


;move this stuff?


;do we need this?
(defthm unsigned-byte-p-logcdr-fc
  (implies (and (unsigned-byte-p n x)
                (integerp n)
                (< 0 n))
           (unsigned-byte-p (1- n) (logcdr x)))
  :rule-classes ((:forward-chaining :trigger-terms ((logcdr x)))))

(defthm signed-byte-p-of-logcdr
  (equal (signed-byte-p n (logcdr x))
         (and (< 0 n)
              (integerp n)
              (if (integerp x)
                  (signed-byte-p (1+ n) x)
                t)))
  :hints (("goal"
           :cases ((evenp x))
           :in-theory (e/d (logcdr 
                            signed-byte-p 
                            expt
                            ) 
                           (expt-2-cruncher
                            FLOOR-OF-SHIFT-RIGHT-2
                            )))))

;do we need this?
(defthm signed-byte-p-logcdr-fc
  (implies (and (signed-byte-p n x)
                (integerp n)
                (< 1 n))
           (signed-byte-p (1- n) (logcdr x)))
  :rule-classes ((:forward-chaining :trigger-terms ((logcdr x)))))


(encapsulate
 ()
 
 (local (in-theory (enable LRDT)))

 (defthm logcdr-lognot
   (equal (logcdr (lognot a)) 
          (lognot (logcdr a))))

 (defthm logcdr-logand
   (equal (logcdr (logand a b))
          (logand (logcdr a) (logcdr b))))

 (defthm logcdr-logior
   (equal (logcdr (logior a b))
          (logior (logcdr a) (logcdr b))))

 (defthm logcdr-logxor
   (equal (logcdr (logxor i j))
          (logxor (logcdr i) (logcdr j)))))

(encapsulate
 ()
 (local
  (defthm logcdr-evenp-*-l1
    (implies (and (integerp x)
                  (evenp x))
             (equal (logcdr x) (* 1/2 x)))))

 (defthm logcdr-evenp-*
   (implies (and (evenp (* x y))
                 (integerp x)
                 (integerp y)
                 )
            (equal (logcdr (* x y))
                   (* 1/2 x y)))))
           
;see LOGCDR-EVENP-*
(defthmd *ark*-logcdr-*4
  (implies (integerp x)
           (equal (logcdr (* 4 x))
                  (* 2 x)))
  :hints (("goal" :in-theory (enable logcdr))))  


(defthm logcdr-logcar
  (equal (logcdr (logcar x))
         0)
  :hints (("goal" :in-theory (enable logcdr logcar))))


;move some of this stuff to logcdr

;split into several rules
;mixes logcdr and logcar
(defthm logcdr-+1
  (implies (integerp x)
           (and (implies (equal (logcar x) 0)
                         (equal (logcdr (+ 1 x)) 
                                (logcdr x)))
                (implies (equal (logcar x) 1)
                         (equal (logcdr (+ 1 x)) 
                                (+ 1 (logcdr x))))
                (implies (and (integerp y)
                              (equal (logcar x) 1))
                         (equal (logcdr (+ 1 x y)) 
                                (+ 1 (logcdr x) (logcdr y))))
                (implies (and (integerp y)
                              (equal (logcar x) 1))
                         (equal (logcdr (+ 1 y x)) 
                                (+ 1 (logcdr x) (logcdr y))))))
  :hints (("Goal" :in-theory (enable logcons))))

(defthm logcdr-+3
  (and (implies (and (integerp x)
                     (equal (logcar x) 0))
                (equal (logcdr (+ 3 x)) 
                       (+ 1 (logcdr x))))
       (implies (and (integerp x)
                     (equal (logcar x) 1))
                (equal (logcdr (+ 3 x)) 
                       (+ 2 (logcdr x)))))
  :hints (("goal" :in-theory (enable logcar logcdr))))

(defthm logcdr-loghead
  (implies (< 0 n)
           (equal (logcdr (loghead n x))
                  (loghead (1- n) (logcdr x))))
  :hints (("goal" :in-theory (enable LRDT))))

(defthm logcdr-logext
  (implies (and (integerp n)
                ;(integerp x)
                (< 1 n))
           (equal (logcdr (logext n x)) 
                  (logext (1- n) (logcdr x))))
  :hints (("goal" :in-theory (enable LRDT))))
           
(defthm logcdr-bitop
  (and (equal (logcdr (b-and x y)) 0)
       (equal (logcdr (b-ior x y)) 0)
       (equal (logcdr (b-xor x y)) 0)
       (equal (logcdr (b-not x)) 0))
  :hints (("goal" :in-theory (enable logcdr b-and b-ior b-xor b-not))))

(defthm equal-logcdr-constant-bridge
  (implies (and (syntaxp (quotep x))
                (not (equal (logcar y) 0))
                (integerp x)
                (integerp y)
                )
           (equal (equal (logcdr y) x)
                  (equal y (1+ (* 2 x))))))



;; ;doing more harm than good?
;; (defthm logcdr-+
;;   (implies (and (integerp a)
;;                 (integerp b))
;;            (equal (logcdr (+ a b))
;;                   (+ (logcdr a)
;;                      (logcdr b)
;;                      (b-maj (logcar a) (logcar b) 0)))))
  
;; (defthm logcdr-+-carry-bit
;;   (implies (and (integerp a)
;;                 (integerp b)
;;                 (unsigned-byte-p 1 c))
;;            (equal (logcdr (+ a b c))
;;                   (+ (logcdr a)
;;                      (logcdr b)
;;                      (b-maj (logcar a) (logcar b) c)))))
