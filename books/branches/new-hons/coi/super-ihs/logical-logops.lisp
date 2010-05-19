#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#
(in-package "ACL2")
(include-book "loglist")
(include-book "logext")

(defthmd expt2*
  (implies (and (equal x 2)
                (integerp n)
                (<= 0 n))
           (equal (expt x n)
                  (if (equal n 0)
                      1
                    (logcons 0 (expt x (1- n))))))
  :hints (("goal" :in-theory (enable expt ash)))
  :rule-classes :definition)

(in-theory (disable expt))

;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;
;; lognot
;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;



(defthm signed-byte-p-lognot
  (implies (signed-byte-p size i)
           (signed-byte-p size (lognot i)))
  :rule-classes ((:rewrite)
                 (:forward-chaining :trigger-terms ((lognot i)))))

(defthm lognot-neg 
  (implies (integerp a)
           (equal (< (lognot a) 0)
                  (<= 0 a)))
  :hints (("goal" :in-theory (enable lognot))))

(defthm lognot-logior
  (implies (and (integerp x)
                (integerp y))
           (equal (lognot (logior x y))
                  (logand (lognot x) (lognot y))))
  :hints (("goal" :in-theory (enable LRDT logendp))))

;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;
;; logand
;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;

(defthm logand-logior-2
  (implies (and (force (integerp i))
                (force (integerp j))
                (force (integerp k)))
           (equal (logand (logior i j) k)
                  (logior (logand i k) (logand j k)))))


(defthmd logand-zip
  (implies (zip a)
           (and (equal (logand a b) 0)
                (equal (logand b a) 0)))
  :hints (("goal" :in-theory (enable logand ifix))))

;; taken from logops-lemmas.lisp, where it's a local theorem
(defthm signed-byte-p-logand
  (implies (and (signed-byte-p size i)
                (signed-byte-p size j))
           (signed-byte-p size (logand i j)))
  :rule-classes ((:forward-chaining :trigger-terms ((logand i j)))))

(defthm logand-neg
  (implies (and (integerp a)
                (integerp b))
           (equal (< (logand a b) 0)
                  (and (< a 0) (< b 0))))
  :hints (("goal" :in-theory (enable logand))))

(defthm ifix-logand
  (equal (ifix (logand x y))
         (logand x y)))


;should 0 really count as a logmaskp?
;bzo add the other commutative form of this rule?
(defthm logand-with-mask-eric
  (implies (logmaskp mask)
           (equal (logand mask i)
                  (loghead (integer-length mask) i)))
  :hints (("Goal" :use (:instance logand-with-mask (size  (INTEGER-LENGTH MASK)))
           :in-theory (e/d () (logand-with-mask)))))

(in-theory (disable logand-with-mask)) 




;disable the other one?
(defthm my-logextu-as-loghead
  (implies (and ;(FORCE (INTEGERP FINAL-SIZE))
;                (FORCE (>= FINAL-SIZE 0))
                (FORCE (INTEGERP EXT-SIZE))
                (FORCE (>= EXT-SIZE 0))
                (<= final-size ext-size)
                )
           (equal (loghead final-size (logext ext-size i))
                  (loghead final-size i)))
  :hints
  (("Goal" :in-theory (e/d (
;                            LOGHEAD-WITH-SIZE-NON-POSITIVE
                            ) 
                           (logextu-as-loghead))
    :use  logextu-as-loghead)))

(defthm logand-bit-0
  (implies (unsigned-byte-p 1 x)
           (equal (logand x y) 
                  (b-and x (logcar y))))
  :hints (("goal" :in-theory (e/d (LRDT logand-zip) (LOGHEAD* logand*))))
  :rule-classes ((:rewrite :backchain-limit-lst 1)))

;prove from the other
(defthm logand-bit-1
  (implies (unsigned-byte-p 1 x)
           (equal (logand y x) 
                  (b-and x (logcar y))))
  :hints (("goal" :in-theory (e/d (LRDT logand-zip) (LOGHEAD* logand*))))
  :rule-classes ((:rewrite :backchain-limit-lst 1)))

(defthm logand-lognot
  (equal (logand x (lognot x))
         0)
  :hints (("goal" :in-theory (enable LRDT logand-zip logendp))))



;drop or redo?
(defthmd logand-commutative-2-helper
   (implies (and (integerp b)
                 (not (equal b 0))
                 (not (equal b -1))
                 (equal (logand a c) 0)
                 (integerp a)
                 (integerp c))
            (equal (logand a b c) 
                   0))
   :hints (("goal" :in-theory (enable LRDT
                                      logendp
                                      even-odd-different-1 
                                      even-odd-different-2
                                      ))))



(defthm equal-logand-logcons
  (implies (and (integerp b)
                (integerp x)
                (integerp y)
                (unsigned-byte-p 1 a))
           (equal (equal (logand (logcons a b) x) y)
                  (and (equal (b-and a (logcar x)) (logcar y))
                       (equal (logand b (logcdr x)) (logcdr y)))))
  :hints (("goal" :in-theory (enable LRDT))))


(encapsulate
 ()
 (local (defthmd logand-expt-helper
          (implies (and (integerp x)
                        (integerp n)
                        (<= 0 n))
                   (equal (logand (expt 2 n) x)
                          (if (logbitp n x)
                              (expt 2 n)
                            0)))
          :hints (("goal" 
                   :in-theory (enable LRDT expt2*)
                   :induct (sub1-logcdr-logcdr-induction n x k)))))

 (defthm logand-expt
   (implies (<= 0 n)
            (equal (logand (expt 2 n) x)
                   (if (logbitp n x)
                       (expt 2 n)
                     0)))
   :hints (("Goal" :use (:instance  logand-expt-helper)))))

;bzo move
(defthm integer-length-<-1-rewrite
  (equal (< (integer-length n) 1)
         (or (equal n 0)
             (equal n -1)
             (not (integerp n)))
         )
  :hints (("Goal" :in-theory (enable integer-length))))

(defthm logand-expt-constant-version
  (implies (and (syntaxp (quotep n)) 
                (equal (expt 2 (1- (integer-length n))) n)
                (integerp n))
           (equal (logand n x)
                  (if (logbitp (1- (integer-length n)) x)
                      (expt 2 (1- (integer-length n)))
                    0)))
  :hints (("Goal" :use (:instance logand-expt (n (1- (integer-length n)))))))

;bzo just use logand-expt ?
(defthm equal-logand-expt
  (implies (<= 0 n) ;bzo
           (equal (equal (logand (expt 2 n) x) k)
                  (if (logbitp n x)
                      (equal k (expt 2 n))
                    (equal k 0)))))

;just use logand-expt-constant-version?
(defthm equal-logand-expt-rewrite
  (implies (and (syntaxp (quotep n)) 
                (equal (expt 2 (1- (integer-length n))) n)
                (integerp n)
                )
           (equal (equal (logand n x) k)
                  (if (logbitp (1- (integer-length n)) x) 
                      (equal k n) 
                    (equal k 0))))
  :hints (("goal" 
           :in-theory (e/d (LRDT) (logand*))
           :use (:instance equal-logand-expt 
                           (n (1- (integer-length n)))))))

(defthm logand---expt
  (implies (and (integerp n)
                (<= 0 n)
                (signed-byte-p (1+ n) x))
           (equal (logand (- (expt 2 n)) x)
                  (if (logbitp n x) (- (expt 2 n)) 0)))
  :hints (("goal" 
           :in-theory (enable LRDT expt2* ash open-logcons))))

(defthm logand---expt-rewrite
  (implies (and (syntaxp (quotep k)) 
                (integerp k) 
                (equal (- (expt 2 (1- (integer-length (- k))))) k)
                (signed-byte-p (integer-length (- k)) x))
           (equal (logand k x)
                  (if (logbitp (1- (integer-length (- k))) x) k 0)))
  :hints (("goal" :use (:instance logand---expt (n (1- (integer-length (- k))))))))

(defthm equal-0-logand-bit
  (implies (and (unsigned-byte-p 1 x)
                (integerp y))
           (and (equal (equal 0 (logand y x))
                       (or (equal x 0) (equal (logcar y) 0)))
                (equal (equal 0 (logand x y))
                       (or (equal x 0) (equal (logcar y) 0)))))
  :hints (("goal" :in-theory (enable LRDT))))

(defthm equal-bit-logand-bit
  (implies (and (integerp y)
                (unsigned-byte-p 1 x))
           (and (equal (equal x (logand y x))
                       (or (equal x 0) (equal (logcar y) 1)))
                (equal (equal x (logand x y))
                       (or (equal x 0) (equal (logcar y) 1)))))
  :hints (("goal" :in-theory (enable LRDT))))

(defthm logand-logand-const
  (implies (and (syntaxp (quotep a))
                (syntaxp (quotep b))
                ;(integerp a)
                ;(integerp b)
                ;(integerp c)
                )
           (equal (logand a (logand b c))
                  (logand (logand a b) c))))

(defthm equal-logand-ash-0
  (implies (and (unsigned-byte-p n x)
;                (integerp y)
                (integerp n)
                (<= 0 n)
                )
           (and (equal (logand (ash y n) x) 0)
                (equal (logand x (ash y n)) 0)))
  :hints (("goal" :in-theory (enable LRDT))))

(defthm logand-bfix
  (and (equal (logand (bfix x) y) 
              (b-and (bfix x) (logcar y)))
       (equal (logand y (bfix x)) 
              (b-and (bfix x) (logcar y)))))

(defthm *ash*-equal-logand-ash-pos-0
  (implies (and (integerp n)
                (integerp x)
                (integerp y)
                (< 0 n))
           (equal (equal (logand x (ash y n)) 0)
                  (equal (logand (ash x (- n)) y) 0)))
  :hints (("goal" :in-theory (enable LRDT)
           :induct (sub1-logcdr-induction n x))))

(defthm *ash*-equal-logand---expt---expt-helper
  (implies (and (integerp n)
                (integerp x)
                (<= 0 n))
           (equal (equal (- (expt 2 n)) (logand (- (expt 2 n)) x))
                  (equal (ash x (- n)) -1)))
  :rule-classes nil
  :hints (("goal" 
           :in-theory (e/d (LRDT expt2*
                                 ) 
                           (LOGCONS-OF-0 
                            )))))

(defthm equal-logand---expt---expt
  (implies (and (syntaxp (quotep k))
                (integerp k)
                (integerp x)
                (equal (- (expt 2 (1- (integer-length (- k))))) k))
           (equal (equal k (logand k x))
                  (equal (ash x (- (1- (integer-length (- k))))) -1)))
  :hints (("goal" 
           :use (:instance *ash*-equal-logand---expt---expt-helper 
                           (n (1- (integer-length (- k))))))))

(defthm logand---expt-v2
  (implies (and (integerp n)
                (<= 0 n)
                (unsigned-byte-p (1+ n) x))
           (equal (logand (- (expt 2 n)) x)
                  (if (logbitp n x) (expt 2 n) 0)))
  :hints (("goal" :in-theory (enable LRDT expt2*))))

(defthm logand---expt-rewrite-v2
  (implies (and (syntaxp (quotep k)) 
                (integerp k) 
                (equal (- (expt 2 (1- (integer-length (- k))))) k)
                (unsigned-byte-p (integer-length (- k)) x))
           (equal (logand k x)
                  (if (logbitp (1- (integer-length (- k))) x) 
                      (expt 2 (1- (integer-length (- k)))) 
                    0)))
  :hints (("goal" :use (:instance logand---expt-v2 
                                  (n (1- (integer-length (- k))))))))

(defthm equal-logand---expt-0
  (implies (and (integerp n)
                (integerp x)
                (<= 0 n))
           (equal (equal (logand (- (expt 2 n)) x) 0)
                  (unsigned-byte-p n x)))
  :hints (("goal"
           :in-theory (e/d (LRDT)
                           (logand---expt-v2 
                            logand---expt-rewrite-v2 
                            logand---expt)))))

(defthm equal-logand---expt-0-rewrite
  (implies (and (integerp x)
                (syntaxp (quotep k)) (integerp k) 
                (equal (- (expt 2 (1- (integer-length (- k))))) k))
           (equal (equal (logand k x) 0)
                  (unsigned-byte-p (1- (integer-length (- k))) x)))
  :hints (("goal" :use (:instance equal-logand---expt-0 
                                  (n (1- (integer-length (- k))))))))

;see from-rtl.lisp for more stuff about logand (and perhaps other functions...)

(defthm logand-lognot-1
  (equal (logand x (lognot x) y)
         0)
  :hints (("goal" :use ((:instance logand-associative
                                   (i x)
                                   (j (lognot x))
                                   (k y))))))
(defthm logand-duplicate-1
  (equal (logand x x y)
         (logand x y))
  :hints (("Goal" :in-theory (e/d (LOGAND-ZIP)
                                  (logand 
                                   COMMUTATIVITY-OF-LOGAND
                                   logand-associative))
           :use (:instance logand-associative
                           (i x)
                           (j x)
                           (k y)))))

;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;
;; logior
;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;




(encapsulate
 ()
 (local (defthm logior-neg-helper
          (implies (and (integerp a)
                        (integerp b))
                   (equal (< (logior a b) 0)
                          (or (< a 0) (< b 0))))
          :hints (("goal" :in-theory (enable logior)))))

;better that the version in RTL?
 (defthm logior-neg
   (equal (< (logior a b) 0)
          (or (< (ifix a) 0)
              (< (ifix b) 0)))
   :hints (("Goal" :use (:instance logior-neg-helper) 
            :in-theory (e/d () (logior-neg-helper))))))

(defthm ifix-logior
  (equal (ifix (logior x y))
         (logior x y)))

(defthm signed-byte-p-logior
  (implies (and (signed-byte-p size i)
                (signed-byte-p size j))
           (signed-byte-p size (logior i j)))
  :rule-classes ((:forward-chaining :trigger-terms ((logior i j)))))

(defthm logior-as-b-ior
  (implies (and (unsigned-byte-p 1 x)
                (unsigned-byte-p 1 y))
           (equal (logior x y) (b-ior x y)))
  :hints (("goal" :in-theory (enable LRDT
                                      )))
  :rule-classes ((:rewrite :backchain-limit-lst 2)))






;; (local (include-book "rtl/rel4/arithmetic/expt" :dir :system))

;; (thm
;;  (implies (and (integerp i)
;;                (integerp j))
;;           (equal (FLOOR (EXPT 2 J) (EXPT 2 I))
;;                  (if (<= i j)
;;                      (expt 2 (+ (- i) j))
;;                    0)))
;;  :hints (("Goal" :in-theory (enable  floor-normalizes-to-have-j-be-1))))

;; (thm
;;  (implies (and (integerp i)
;;                (integerp j)
;;                (and (<= 0 j)) ;drop?
;;                (and (<= 0 i))
;;                )
;;           (equal (LOGBITP i (EXPT 2 j))
;;                  (if (equal i j)
;;                      t
;;                    nil)))
;;  :hints (("Goal" :do-not '(preprocess)
;;           :in-theory (enable LOGBITP
;;                                      floor-normalizes-to-have-j-be-1
;;                                      ))))

;; (thm
;;  (implies (integerp x)
;;           (implies (EQUAL (EXPT 2 (+ -1 (INTEGER-LENGTH X))) X)
;;                    (LOGBITP (+ -1 (INTEGER-LENGTH X)) X)))
;;  :hints (("Goal" :do-not '(generalize eliminate-destructors))))


(defthm logcons-0-expt-hack
  (implies (and(integerp n)
               (<= 0 n))
           (equal (logcons 0 (expt 2 n))
                  (expt 2 (+ 1 n)))))

(defthm twice-logcdr-hack
  (equal (equal (* 2 (logcdr x)) x)
         (if  (integerp x)
             (evenp x)
           (equal 0 x))))

(defthm logbitp-of-logcdr
  (implies (and (integerp n)
                (<= 0 n)
                )
           (equal (logbitp n (logcdr y))
                  (logbitp (+ 1 n) y)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (logbitp 
                            logcdr
                            exponents-add-unrestricted) 
                           (FLOOR-OF-SHIFT-RIGHT-2)))))

;similarly for logtail?
;drop the hyps the way i did for logbitp-of-logcdr2?
(defthm logbit-of-logcdr
  (implies (and (integerp n) (<= 0 n))
           (equal (logbit n (logcdr y))
                  (logbit (+ 1 n) y)))
  :hints (("Goal" :in-theory (enable logbit))))


(defthm logbitp-of-logcdr2
  (equal (logbitp n (logcdr y))
         (if (and (integerp n)
                  (<= 0 n))
             (logbitp (+ 1 n) y)
           (logbitp 0 (logcdr y)) ;simplify this?
           ))
  :hints (("Goal" :use (:instance  logbitp-of-logcdr)
           :in-theory (disable  logbitp-of-logcdr))))

;; (thm
;;  (implies (and (not (equal 0 x))
;;                (integerp x))
;;           (equal (INTEGER-LENGTH (* 1/2 X))
;;                  (+ -1  (INTEGER-LENGTH X))))
;;  :hints (("Goal" :in-theory (enable INTEGER-LENGTH))))

;; zz
;; (thm
;;  (implies (and (not (equal 0 x))
;;                (integerp x))
;;           (LOGBITP (+ -1 (INTEGER-LENGTH X)) X))
;;  :hints (("Goal" :do-not '(generalize eliminate-destructors)
;; ;          :induct t
;;           :in-theory (enable logbitp INTEGER-LENGTH
;;                              ;EXPONENTS-ADD-UNRESTRICTED
;;                              ))))

;bzo speed this up?
;trying to improve the proof of this and in the process discover new rules
;gross proof!
(defthm equal-logior-single-bit
  (implies (and (syntaxp (quotep x))
                (equal (expt 2 (1- (integer-length x))) x) ;x is a power of 2
                (integerp x)
                (integerp y)
                (integerp z)
                (< 0 x)
                )
           (equal (equal (logior y z) x)
                  (and (logbitp (1- (integer-length x)) (logior y z))
                       (equal 0 (logand (lognot x) (logior y z))))))
  :hints (("goal" 
           :do-not '(;generalize eliminate-destructors 
                      ;          fertilize ;bzo. why didn't it fertilize completely?
                                )
           :in-theory (e/d (LRDT 
                              even-odd-different-2 
                              even-odd-different-1
                              expt2*
                              EQUAL-B-NOT-LOGCAR
                              ;ash
                              ) 
                           (integer-length*
                            LOGCONS-OF-0
                            ))
           :induct (logcdr-logcdr-logcdr-induction x y z))))

(defthm logior-logior-const
  (implies (and (syntaxp (quotep a))
                (syntaxp (quotep b))
                ;(integerp a)
                ;(integerp b)
                ;(integerp c)
                )
           (equal (logior a (logior b c))
                  (logior (logior a b) c))))

;Trying disabled, since this looked expensive... -ews
(defthmd equal-logior-const-const
  (implies (and (syntaxp (quotep x))
                (syntaxp (quotep z))
                (integerp x)
                (integerp y)
                (integerp z)
                (not (equal x 0)) (not (equal x -1)))
           (equal (equal (logior x y) z)
                  (and (equal (b-ior (logcar x) (logcar y)) (logcar z))
                       (equal (logior (logcdr x) (logcdr y)) (logcdr z)))))
  :hints (("goal" :in-theory (enable LOGOPS-RECURSIVE-DEFINITIONS-THEORY)
           :induct (logcdr-logcdr-logcdr-induction z x y))))

(defthmd equal-logior-*2
  (implies (and (integerp x)
                (integerp y)
                (integerp z))
           (equal (equal (logior x y) (* 2 z))
                  (and (equal (logcar x) 0)
                       (equal (logcar y) 0)
                       (equal (logior (logcdr x) (logcdr y)) z))))
  :hints (("goal" :in-theory (enable LRDT))))

;; The follow bridge lemmas are needed for the PC calculation
(defthm logior-expt-ash-loghead-bridge-helper
  (implies (and (integerp n)
                (integerp x)
                (integerp m)
                (< 0 n)
                (<= 0 m))
           (equal (logior (expt 2 (1- n))
                          (ash (loghead m (logcdr x)) n))
                  (if (equal (logcar x) 0)
                      (ash (loghead (1+ m) (1+ x)) (1- n))
                    (ash (loghead (1+ m) x) (1- n)))))
  :rule-classes nil
  :hints (("goal" 
           :in-theory (e/d (LRDT loghead* equal-logior-*2) (LOGHEAD-SUM-SPLIT-INTO-2-WHEN-I-IS-A-CONSTANT
                                                            LOGCONS-OF-0))
           :induct (sub1-induction n))))

(defthmd logior-expt-ash-loghead-bridge
  (implies (and (integerp x)
                (integerp m)
                (integerp v)
                (<= 0 m)
                (<= 0 n)
                (equal v (expt 2 (1- (integer-length v))))
                (equal n (integer-length v)))
           (equal (logior v (ash (loghead m (logcdr x)) n))
                  (if (equal (logcar x) 0)
                      (ash (loghead (1+ m) (1+ x)) (1- n))
                    (ash (loghead (1+ m) x) (1- n)))))
  :hints (("goal" :use (:instance logior-expt-ash-loghead-bridge-helper 
                                  (n (integer-length v))))))

(defthm logior-expt-ash-loghead-bridge-bridge
  (implies (and (syntaxp (quotep v))
                (integerp x)
                (integerp m)
                (integerp v)
                (integerp a)
                (<= 0 m)
                (<= 0 n)
                (equal v (expt 2 (1- (integer-length v))))
                (equal n (integer-length v)))
           (equal (logior v (logior a (ash (loghead m (logcdr x)) n)))
                  (if (equal (logcar x) 0)
                      (logior a (ash (loghead (1+ m) (1+ x)) (1- n)))
                    (logior a (ash (loghead (1+ m) x) (1- n))))))
  :hints (("goal" :in-theory (enable logior-expt-ash-loghead-bridge))))

;; logior-as-+ - not part of our strategy, but useful for proving rules!
(defthmd logior-as-+
  (implies (and (integerp b)
                (integerp c)
                (equal (logand b c) 0))
           (equal (logior b c) (+ b c)))
  :hints (("goal" :in-theory (e/d (LRDT logendp open-logcons) (LOGCONS-OF-0)))))

;; push a + into a logior if the logior args don't overlap

(defthm +-logior-ash
  (implies (and (integerp v)
                (integerp x)
                (integerp n)
                (<= 0 n)
                (<= 0 x)
                (unsigned-byte-p n a)
                (unsigned-byte-p n (+ v a)))
           (equal (+ v (logior a (ash x n)))
                  (logior (+ v a) (ash x n))))
  :hints (("goal" :in-theory (enable logior-as-+))))



;bzo gross subgoal hint
(defthm +-logior-ash-v2
  (implies (and (integerp v)
                (integerp x)
                (integerp n)
                (< 0 n)
                (<= 0 x)
                (unsigned-byte-p n a)
                (unsigned-byte-p n v)
                (not (unsigned-byte-p n (+ v a))))
           (equal (+ v (logior a (ash x n)))
                  (logior (loghead n (+ v a)) 
                          (ash (1+ x) n))))
  :hints (("goal" :in-theory (e/d (logior-as-+
;                                   ash-+-pos
                                   LOGHEAD-ALMOST
                                   )
                                  ( UNSIGNED-BYTE-P-+-EASY
                                   UNSIGNED-BYTE-P-+)))
          ("goal''" :in-theory (e/d (ash-+-pos 
                                     LOGHEAD-ALMOST
                                     )
                                    ( UNSIGNED-BYTE-P-+)))))




(defthm logior-lognot
  (equal (logior x (lognot x))
         -1)
  :hints (("goal" 
           :in-theory (enable LRDT logendp)))) 

(defthm logor-lognot-1
  (implies (and (integerp x)
                (integerp y))
  (equal (logior x (lognot x) y) -1))
  :hints (("goal" :use ((:instance logior-associative
                                   (i x)
                                   (j (lognot x))
                                   (k y))))))

(defthm logior-duplicate
  (equal (logior x x) 
         (ifix x))
  :hints (("goal" 
           :induct (logcdr-induction x)
           :in-theory (enable LRDT zip 
                              ))))

;add to rtl library?
(defthm logior-duplicate-1
  (equal (logior x x y) 
         (logior x y))
  :hints (("goal" 
           :in-theory (e/d () ( logior-associative))
           :use ((:instance logior-associative
                            (i x)
                            (j x)
                            (k y))))))

;; ;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;
;; ;; logxor
;; ;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;

;; ;; These are Wilding lemmas that seem general-purpose

;; (defthm signed-byte-p-logxor
;;   (implies (and (signed-byte-p size i)
;;                 (signed-byte-p size j))
;;            (signed-byte-p size (logxor i j)))
;;   :rule-classes ((:rewrite)
;;                  (:forward-chaining :trigger-terms ((logxor i j)))))

;; ;; moved to logcar
;; ;; (defthm logcar-logxor
;; ;;   (implies (and (integerp a) 
;; ;;                 (integerp b))
;; ;;            (equal (logcar (logxor a b)) 
;; ;;                   (b-xor (logcar a) (logcar b))))
;; ;;   :hints (("goal" :in-theory (enable
;; ;;                               LOGOPS-RECURSIVE-DEFINITIONS-THEORY
;; ;;                               simplify-bit-functions))))

;; (defthm logxor-lognot
;;   (implies (and (integerp a) 
;;                 (integerp b))
;;            (and (equal (logxor (lognot a) b) (lognot (logxor a b)))
;;                 (equal (logxor a (lognot b)) (lognot (logxor a b)))))
;;   :hints (("goal" 
;;            :in-theory (enable LRDT simplify-bit-functions))))



;; (defthm logxor-cancel2
;;   (implies (and (integerp a) 
;;                 (integerp b))
;;            (equal (logxor b (logxor b a)) a))
;;   :hints (("goal" :use (:instance commutativity-of-logxor
;;                                   (i b) (j (logxor b a))))))

;; (defthm logxor-neg
;;   (implies (and (integerp a)
;;                 (integerp b))
;;            (equal (< (logxor a b) 0)
;;                   (not (equal (< a 0) (< b 0)))))
;;   :hints (("goal" :in-theory (enable logxor logeqv logorc1))))

;; ;; Perhaps we should just open logxor.  But for now, we'll open it
;; ;; only when used in conjuction with logical bit-operations.
;; (defthm logxor-open
;;   (implies (and (integerp x)
;;                 (integerp y))
;;            (equal (logxor x y)
;;                   (logior (logand x (lognot y))
;;                           (logand (lognot x) y))))
;;   :hints (("goal" :in-theory (enable LRDT))))
;;            ;; :in-theory (enable LOGOPS-RECURSIVE-DEFINITIONS-THEORY)
;; ;;            :induct (logcdr-logcdr-induction x y))))

;; (in-theory (disable logxor-open))

;; (defthm logior-logxor
;;   (implies (and (integerp x)
;;                 (integerp y))
;;            (and
;;             (equal (logior z (logxor x y))
;;                    (logior z 
;;                            (logior (logand x (lognot y))
;;                                    (logand (lognot x) y))))
;;             (equal (logior (logxor x y) z)
;;                    (logior (logior (logand x (lognot y))
;;                                    (logand (lognot x) y))
;;                            z))))
;;   :hints (("goal" :in-theory (enable logxor-open))))

;; (defthm logxor-logior
;;   (implies (and (integerp x)
;;                 (integerp y)
;;                 (integerp z))
;;            (and (equal (logxor (logior x y) z)
;;                        (logior (logand (logior x y) (lognot z))
;;                                (logand (lognot (logior x y)) z)))
;;                 (equal (logxor z (logior x y))
;;                        (logior (logand (logior x y) (lognot z))
;;                                (logand (lognot (logior x y)) z)))))
;;   :hints (("goal" :in-theory (enable logxor-open))))


;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;
;; get rid of logops other than logand, logior, and lognot
;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;

(defthm lognot-logand
 (implies (and (integerp x)
               (integerp y))
          (equal (lognot (logand x y))
                 (logior (lognot x) (lognot y))))
 :hints (("goal" :in-theory (enable LRDT logendp))))
          ;; :induct (logcdr-logcdr-induction x y)
;;            :in-theory (enable LOGOPS-RECURSIVE-DEFINITIONS-THEORY))))
 
(defthm lognand-rewrite
 (implies (and (integerp x)
               (integerp y))
          (equal (lognand x y)
                 (logior (lognot x) (lognot y))))
 :hints (("goal" :in-theory (enable lognand))))

(defthm lognor-rewrite
  (implies (and (integerp x)
                (integerp y))
           (equal (lognor x y)
                  (logand (lognot x) (lognot y))))
  :hints (("goal" :in-theory (enable lognor))))

(in-theory (enable logandc1 logandc2 logorc1 logorc2))

(defthm logeqv-rewrite
  (implies (and (integerp x)
                (integerp y))
           (equal (logeqv x y)
                  (logior (logand x y)
                          (logand (lognot x) (lognot y)))))
  :hints (("goal" :in-theory (enable logeqv))))

(defthm logxor-rewrite
  (implies (and (integerp x)
                (integerp y))
           (equal (logxor x y)
                  (logior (logand x (lognot y))
                          (logand (lognot x) y))))
   :hints (("goal" :in-theory (enable logeqv logxor))))

;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;
;; and similarly for binary operations:
;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;


(defthm logand-upper-bound-eric
  (implies (<= 0 i)
           (<= (logand i j) i))
  :hints (("Goal" :cases ((integerp j))))
  :rule-classes
  ((:linear :corollary
            (implies (and (>= i 0))
                     (<= (logand i j) i)))
   (:linear :corollary
            (implies (and (>= i 0))
                     (<= (logand j i) i)))))

(in-theory (disable logand-upper-bound)) 

