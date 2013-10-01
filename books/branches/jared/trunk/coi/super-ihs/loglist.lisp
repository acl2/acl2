#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#
(in-package "ACL2")
(include-book "byte-p")
(include-book "logapp")

;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;
;; logapp
;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;

(encapsulate
 ()
 (local (defthmd equal-logapp-x-y-z-helper
          (implies (and (integerp n) 
                        (integerp x) 
                        (integerp y) 
                        (integerp z) 
                        (<= 0 n))
                   (equal (equal (logapp n x y) z)
                          (and (equal (loghead n x) (loghead n z))
                               (equal y (logtail n z)))))
          :hints (("goal" :in-theory (enable LRDT
                                             )))))

;clean up the RHS?
 (defthm equal-logapp-x-y-z
   (equal (equal (logapp n x y) z)
          (and (integerp z)
               (if (integerp x)
                   (equal (loghead n x) (loghead n z))
                 (equal (ASH Y (NFIX N)) z)
                 )
               (if (integerp y)
                   (equal y (logtail n z))
                 (equal z (loghead n x)) ;bzo clean this up?
                 )))
   :otf-flg t
   :hints (("Goal" :use (equal-logapp-x-y-z-helper)))))

(defthm equal-logapp-x-y-z-constants
  (implies (and (syntaxp (quotep z))
                (syntaxp (quotep n)))
           (equal (equal (logapp n x y) z)
                  (and (integerp z)
                       (if (integerp x)
                           (equal (loghead n x) (loghead n z))
                         (equal (ash y (nfix n)) z))
                       (if (integerp y)
                           (equal y (logtail n z))
                         (equal z (loghead n x))))))
  :hints (("Goal" :in-theory (enable equal-logapp-x-y-z))))

(defthm logapp-logior
  (implies (and (integerp w)
                (integerp x)
                (integerp y)
                (integerp z)
                (integerp n)
                (<= 0 n))
           (equal (logapp n (logior w y) (logior x z))
                  (logior (logapp n w x) (logapp n y z))))
  :hints (("goal" :in-theory (enable LRDT)))) 

(defthm logapp-logand
  (implies (and (integerp w)
                (integerp x)
                (integerp y)
                (integerp z)
                (integerp n)
                (<= 0 n))
           (equal (logapp n (logand w y) (logand x z))
                  (logand (logapp n w x) (logapp n y z))))
  :hints (("goal" :in-theory (enable LRDT))))

(defthm logapp-lognot
  (implies (and (integerp x)
                (integerp y)
                (integerp n)
                (<= 0 n))
           (equal (logapp n (lognot x) (lognot y))
                  (lognot (logapp n x y))))
  :hints (("goal" :in-theory (enable LRDT))))

;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;
;; loghead
;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;


(defthm loghead-subsumes-+-logext
  (implies (and (< n m)
                (integerp n)
                (integerp m)
                (integerp x)
                (integerp a)
                (< 0 m)
                (<= 0 n)
                )
           (equal (loghead n (+ a (logext m x)))
                  (loghead n (+ a x)))))

(defthm loghead-logior
  (implies (and (integerp n)
                (integerp x) 
                (integerp y)
                (<= 0 n))
           (equal (loghead n (logior x y))
                  (logior (loghead n x) (loghead n y))))
  :hints (("goal" :in-theory (enable LRDT))))

(defthm loghead-logand
  (implies (and (integerp n)
                (integerp x)
                (integerp y)
                (<= 0 n))
           (equal (loghead n (logand x y))
                  (logand (loghead n x) (loghead n y))))
  :hints (("goal" :in-theory (enable LRDT))))

(defthm loghead-ash-pos-rewrite
  (implies (and (integerp n2)
                (<= 0 n2))
           (equal (loghead n1 (ash x n2))
                  (if (or (<= n1 n2)
                          (not (integerp n1)))
                      0
                    (ash (loghead (- n1 n2) x) n2))))
  :hints (("goal" :in-theory (e/d (loghead*-better ash* LRDT
                                                   zp
                                                   ) 
                                  ( ;LOGHEAD-OF-*-EXPT-ALT
                                   )))))



(defthm loghead-*4
  (implies (and (integerp n)
                (integerp x)
                (< 0 n))
           (equal (loghead n (* 4 x))
                  (logcons 0 (loghead (1- n) (logcdr (* 4 x))))))
  :hints (("goal" :in-theory (enable loghead*)
           :use (:instance loghead* (size n) (i (* 4 x))))))

(defthm loghead-+-logior
  (implies (and (equal (loghead n y) 0)
                (integerp y)
                (integerp x)
                (integerp n)
                (<= 0 n)
                (integerp a))
           (equal (loghead n (+ a (logior x y)))
                  (loghead n (+ a x)))))

(defthm equal-loghead-ash-pos
  (implies (and (integerp n)
                (integerp m)
                (integerp y)
                (integerp x)
                (integerp p)
                (<= 0 p)
                (<= p n))
           (equal (equal (loghead n x) (ash (loghead m y) p))
                  (and (equal (loghead p x) 0)
                       (equal (logtail p (loghead n x)) (loghead m y)))))
  :hints (("goal" :in-theory (e/d (LRDT) (ash* ;change for acl2 3.0
                                          )))))

;; ;move to loghead.lisp
;; ;trying disabled
;; (defthmd loghead-almost
;;   (implies (and (not (unsigned-byte-p n x))
;;                 (unsigned-byte-p (1+ n) x)
;;                 )
;;            (equal (loghead n x)
;;                   (if (integerp n)
;;                       (- x (ash 1 n)) ;use expt here?
;;                     0
;;                     )))
;;   :hints (("goal" :in-theory (e/d (LRDT open-logcons
;;                                         ) (evenp-of-logcons
;;                                         expt-2-cruncher)))))



(defthm loghead-+-logext
  (implies (and (integerp n)
                (integerp m)
                (integerp x)
                (integerp y)
                (< 0 n)
                (<= n m))
           (and (equal (loghead n (+ (logext m x) y))
                       (loghead n (+ x y)))
                (equal (loghead n (+ x (logext m y)))
                       (loghead n (+ x y)))
                (implies (integerp z)
                         (equal (loghead n (+ x (logext m z) y))
                                (loghead n (+ x y z))))
                (implies (integerp z)
                         (equal (loghead n (+ x y (logext m z)))
                                (loghead n (+ x y z))))))
  :hints (("goal" :use ((:instance logextu-as-loghead (final-size n) (ext-size m) (i (+ (logext m x) y)))
                        (:instance logextu-as-loghead (final-size n) (ext-size m) (i (+ (logext m y) z)))
                        (:instance logextu-as-loghead (final-size n) (ext-size m) (i (+ (logext m x) y z)))
                        (:instance logextu-as-loghead (final-size n) (ext-size m) (i (+ (logext m z) y x)))))))

;move
(defthm equal-loghead-almost-0-helper
  (implies (and (unsigned-byte-p (+ 1 n) x)
                (integerp n)
                (< 0 n)
                )
           (equal (equal (loghead n x) 0)
                  (or (equal x (expt 2 n))
                      (equal x 0))))
  :rule-classes nil
  :hints (("goal" 
           :induct (loghead n x)
           :expand (logcdr x)
           :in-theory (e/d (lrdt expt ;logcdr
                                 )
                           (unsigned-byte-p-of-logcdr ;why was this necessary?
                            LOGCAR-0-REWRITE
                            )))))

(defthm equal-loghead-almost-0
  (implies (and (unsigned-byte-p n x)
                (unsigned-byte-p n y)
;                (integerp n)
                (< 0 n)
                )
           (equal (equal (loghead n (+ x y)) 0)
                  (or (equal (+ x y) (expt 2 n))
                      (and (equal x 0) (equal y 0)))))
  :hints (("goal" :use (:instance equal-loghead-almost-0-helper (x (+ x y))))))

(local (in-theory (disable UNSIGNED-BYTE-P-OF-LOGCDR))) ;this doesn't play well with LRDT

(defthm equal-loghead-lognot-all-ones
  (implies (and (integerp n)    
                (integerp x)
                (<= 0 n))
           (equal (equal (loghead n (lognot x)) (1- (expt 2 n)))
                  (equal (loghead n x) 0)))
  :hints (("goal" :in-theory (enable LRDT))))

(defthm loghead-lognot-in-+
  (implies (and (integerp n)
                (<= 0 n)
                (unsigned-byte-p n x))
           (and (equal (+ (loghead n (lognot x)) y)
                       (+ (- (expt 2 n) (1+ x)) y))
                (equal (+ y (loghead n (lognot x)))
                       (+ y (- (expt 2 n) (1+ x))))
                (equal (+ y z (loghead n (lognot x)))
                       (+ y z (- (expt 2 n) (1+ x))))))
  :hints (("goal" :in-theory (enable lognot loghead unsigned-byte-p nfix))))

(defthm equal-loghead-0-sbp
  (implies (and (signed-byte-p n x)
;                (integerp n)
        ;        (<= 0 n)
                )
           (equal (equal (loghead n x) 0)
                  (equal x 0)))
  :hints (("goal" :in-theory (enable LRDT))))



(defthm equal-loghead-0-sbp-v2
  (implies (and (signed-byte-p (1+ n) x)
                (integerp n))
           (equal (equal (loghead n x) 0)
                  (or (equal x 0)
                      (equal x (- (expt 2 n))))))
  :hints (("goal" :in-theory (e/d (LRDT expt ash) (loghead-of-minus
                                                   LOGCAR-0-REWRITE)))))

(defthm loghead-neg-logext
  (implies (and (integerp n)
                (<= 0 n)
                (unsigned-byte-p n x))
           (equal (loghead n (- (logext n x))) 
                  (loghead n (- x))))
  :hints (("goal" :in-theory (e/d (LRDT open-logcons) (LOGEXTU-AS-LOGHEAD ;forcing
                                                       LOGHEAD-OF-MINUS
                                                       )))))

(defthm loghead-logxor
  (implies (and (integerp n)
                (integerp x)
                (integerp y)
                (<= 0 n))
           (equal (loghead n (logxor x y))
                  (logxor (loghead n x) (loghead n y))))
  :hints (("goal" :in-theory (enable LRDT)))) 

(defthm loghead-lognot-loghead
  (implies (and (integerp n1)
                (integerp n2)
                (integerp x)
                (<= n1 n2)
                (<= 0 n1))
           (equal (loghead n1 (lognot (loghead n2 x)))
                  (loghead n1 (lognot x))))
  :hints (("goal" 
           :in-theory (e/d (LRDT logendp) (LOGHEAD-OF-MINUS 
                                           )))))
           ;:induct (sub1-sub1-logcdr-induction n2 n1 x))))

(defthm loghead-lognot-ash-pos
  (implies (and (integerp x)
                (integerp n)
                (integerp p)
                (<= 0 p)
                (<= p n))
           (equal (loghead p (lognot (ash x n)))
                  (loghead p -1)))
  :hints (("goal"
           :in-theory (enable LRDT))))
           ;; :induct (sub1-sub1-induction p n)

(encapsulate
 ()
 
 (local
  (defthm loghead-lognot-logext-helper
    (implies (and (equal (logcar x) 1)
                  (integerp x)
                  (not (equal x 0))
                  (not (equal x -1))
                  (integerp p)
                  (<= 0 p)
                  (<= p 1))
             (equal (loghead p (lognot x)) 0))
    :hints (("goal" :cases ((equal p 0))))))

 (defthm loghead-lognot-logext
   (implies (and (integerp p)
                 (integerp n)
                 (integerp x)
                 (<= 0 p)
                 (< 0 n)
                 (<= p n))
            (equal (loghead p (lognot (logext n x)))
                   (loghead p (lognot x))))
   :hints (("goal" :in-theory (enable LRDT logendp)))))
           ;; :induct (sub1-sub1-logcdr-induction p n x))))

(local (in-theory (disable LOGCONS-OF-0))) ;for acl2 3.0

(defthm loghead-lognot-ash-pos-logext
  (implies (and (integerp x)
                (integerp n)
                (integerp p)
                (integerp m)
                (<= 0 m)
                (<= 0 p)
                (< 0 n)
                (<= p (+ m n)))
           (equal (loghead p (lognot (ash (logext n x) m)))
                  (loghead p (lognot (ash x m)))))
  :hints (("goal" :in-theory (enable LRDT))))
           ;; :induct (sub1-sub1-induction p m))))

;we already have ash-as-logtail
(defthm loghead-ash-neg
  (implies (and (<= n2 0)
                (integerp n2) ;drop?
                )
           (equal (loghead n1 (ash x n2))
                  (loghead n1 (logtail (- n2) x))))
  :hints (("goal" :use ((:instance ash-as-logtail
                                   (n n2))))))

(defthm loghead-logapp-better
  (implies (<= size1 size)
           (equal (loghead size1 (logapp size i j))
                  (if (integerp size)
                      (loghead size1 i) ;usual case
                    (loghead size1 j)
                    )))
  :hints (("Goal" :use (:instance loghead-logapp (size (ifix size)))
           :in-theory (disable loghead-logapp))))

(in-theory (disable loghead-logapp)) 

(defthmd logtail-loghead-better
  (equal (logtail size1 (loghead size i))
         (loghead (max 0 (- size (nfix size1)))
                  (logtail size1 i)))
  :hints (("Goal" :use (:instance logtail-loghead)
           :in-theory (disable logtail-loghead))))

(in-theory (disable logtail-loghead)) 

(defthm loghead-logtail
  (equal (loghead i (logtail j x))
         (logtail j (loghead (+ i (nfix j)) x)))
  :hints (("Goal" :in-theory (enable logtail-loghead-better))))

;It's not clear whether we want to bring the loghead or the logtail inside.
;I'm trying things out with the policy of bringing the loghead inside. -ews

(theory-invariant (incompatible (:rewrite logtail-loghead-better) (:rewrite loghead-logtail)))
(theory-invariant (incompatible (:rewrite logtail-loghead) (:rewrite loghead-logtail)))

(defthm logtail-logapp-better
  (implies (and (integerp size1)
                (<= 0 size1)
                (integerp size)
                (<= 0 size)
                )
           (equal (logtail size (logapp size1 i j))
                  (if (< size size1)
                      (logapp (- size1 size)
                              (logtail size i)
                              j)
                    (logtail (- size size1)
                             j))))
  :hints (("Goal" :use (:instance logtail-logapp)
           :in-theory (disable logtail-logapp))))

(in-theory (disable logtail-logapp)) 

(encapsulate
 ()

 (local (defthmd loghead-logapp-2-helper-1
          (implies (< size size1)
                   (equal (loghead size1 (logapp size i j))
                          (if (integerp size1)
                              (logapp size i (loghead (- (ifix size1) (nfix size)) j))
                            0)))
          :hints (("Goal" :use (:instance loghead-logapp (i (ifix i)))
                   :in-theory (e/d (logtail-loghead-better) 
                                   (loghead-logapp
                                    LOGHEAD-LOGTAIL))))))

 (local (defthmd loghead-logapp-2-helper-2
          (implies (and (= size size1)
                        (<= 0 SIZE)
                        (INTEGERP SIZE)
                        )
                   (equal (loghead size1 (logapp size i j))
                          (if (integerp size1)
                              (logapp size i (loghead (- size1 size) j))
                            0)))))

 ;;bzo make a "both" version?
 (defthm loghead-logapp-2
   (implies (<= size size1)
            (equal (loghead size1 (logapp size i j))
                   (if (integerp size1)
                       (logapp size i (loghead (- size1 (nfix size)) j))
                     0)))
   :hints (("Goal" :use ((:instance loghead-logapp-2-helper-2)
                         (:instance loghead-logapp-2-helper-1))))))

;move to logapp.lisp?
(defthm associativity-of-logapp-better
  (implies (and (integerp size1)
                (<= 0 size1)
                (integerp size)
                (<= 0 size)
                )
           (equal (logapp size i (logapp size1 j k))
                  (logapp (+ size size1) (logapp size i j) k)))
  :hints (("Goal" :use (:instance associativity-of-logapp)
           :in-theory (disable associativity-of-logapp))))

(in-theory (disable associativity-of-logapp)) 
  
;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;
;; logtail
;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;

(defthm logtail-logior
  (implies (and (integerp x)
                (integerp y)
                (integerp n)
                (<= 0 n))
           (equal (logtail n (logior x y))
                  (logior (logtail n x) (logtail n y))))
  :hints (("goal" 
           :in-theory (disable logapp-logior)
           :use ((:instance logapp-logior
                            (w (loghead n x))
                            (x (logtail n x))
                            (y (loghead n y))
                            (z (logtail n y)))))))

(defthm logtail-logand
  (implies (and (integerp x)
                (integerp y)
                (integerp n)
                (<= 0 n))
           (equal (logtail n (logand x y))
                  (logand (logtail n x) (logtail n y))))
  :hints (("goal" 
           :in-theory (disable logapp-logand)
           :use ((:instance logapp-logand
                            (w (loghead n x))
                            (x (logtail n x))
                            (y (loghead n y))
                            (z (logtail n y)))))))

(defthm logtail-lognot
  (implies (and (integerp x)
                (integerp n)
                (<= 0 n))
           (equal (logtail n (lognot x))
                  (lognot (logtail n x))))
  :hints (("goal" 
           :in-theory (disable logapp-lognot)
           :use ((:instance logapp-lognot
                            (x (loghead n x))
                            (y (logtail n x)))))))



