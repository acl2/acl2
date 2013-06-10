#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#
(in-package "ACL2")
(include-book "bit-twiddling-logops")
(include-book "eric")


;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;
;; hacks
;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;

;; This theory includes rules that convert logops involving
;; bits to b-functions.  This tends to lead to casesplitting, 
;; so should only be done when needed.  So, we disable the
;; theorems by default.

;; (deftheory single-bit-logops
;;   '(;logand-logcar
;;     ;logand-b-ior
;;     ;logand-b-and
;;     ;logand-b-xor
;;     logand-bit-0
;;     logand-bit-1
;;     logand-bfix
;;     ;logior-as-b-ior
;; ;    LOGAND-C_BIT
;;     ))

(in-theory (disable logand-bit-0
                    logand-bit-1
                    logand-bfix
                    ))

(local (in-theory (enable open-logcons))) ;why?

(encapsulate
 ()
 (local (defthm logior-of-sum-with-negative-of-expt-helper
          (implies (and (unsigned-byte-p n y)
                        (integerp n)
                        (< 0 n)
                        )
                   (equal (logior y (- (expt 2 n)))
                          (+ y (- (expt 2 n)))))
          :hints (("goal" :cases ((and (integerp n) (< 0 n)))
                   :in-theory (e/d (lrdt logendp) (logcons-of-0))))))

 (defthm logior-of-sum-with-negative-of-expt
   (implies (unsigned-byte-p n y)
            (equal (logior y (- (expt 2 n)))
                   (+ y (- (expt 2 n)))))
   :hints (("goal" :in-theory (enable unsigned-byte-p)
            :use logior-of-sum-with-negative-of-expt-helper))))

(defthm logior-of-sum-with-negative-of-expt-alt
  (implies (unsigned-byte-p n y)
           (equal (logior (- (expt 2 n)) y)
                  (+ y (- (expt 2 n)))))
  :hints (("goal" :in-theory (disable logior-of-sum-with-negative-of-expt)
           :use  logior-of-sum-with-negative-of-expt)))

(defthm logior-of-sum-with-negative-of-expt-const-version
   (implies (and (syntaxp (quotep k))
                 (equal k (- (expt 2 (expo k))))
                 (unsigned-byte-p (expo k) y))
            (equal (logior k y)
                   (+ y k)))
   :hints (("Goal" :use (:instance logior-of-sum-with-negative-of-expt-alt (n (expo k)))
            :in-theory (disable  logior-of-sum-with-negative-of-expt-alt))))



;; hack for the microprocessor proofs
;compare to logext-open-logbit-sign-known
;; (defthm if-to-logext
;;   (implies (and (integerp n)
;;                 (< 0 n)
;;                 (unsigned-byte-p n y))
;;            (equal (if (equal 0 (logand (expt 2 (1- n)) y))
;;                       y 
;;                     (logior (- (expt 2 n)) y))
;;                   (logext n y)))
;;   :rule-classes nil
;;   :hints (("goal" :in-theory (e/d (LOGAND---EXPT-REWRITE
;;                                    ;LOGIOR-AS-+ use this and not the "special-case" lemma above?
;;                                    ) (logext-open-logbit-sign-known))
;;            :use ((:instance logior-of-sum-with-negative-of-expt)
;;                  (:instance logext-open-logbit-sign-known (x y) (n2  (+ -1 N)))))))



; get rid of mention of nth?
;; (defthm logbitp-of-bit-bridge
;;   (implies (and (integerp n)
;;                 (< 0 n)
;;                 (unsigned-byte-p 1 (nth a x)))
;;            (not (logbitp n (nth a x))))
;;   :hints (("goal" 
;;            :in-theory (enable unsigned-byte-p logbitp*)
;;            :cases ((equal (nth a x) 0)))))

; These hacks needed for mpc reasoning, since we are concerned about
; carry bit of the lower byte


;bzo ;generalize this?
(defthm unsigned-byte-p-+-*4-bridge
  (implies (and (unsigned-byte-p 2 p)
                (unsigned-byte-p (- n 2) x)
                (< 1 n)
                (integerp n)
                (integerp p)
                )
           (unsigned-byte-p n (+ p (* 4 x))))
  :hints (("Goal" :in-theory (e/d (logapp) ( UNSIGNED-BYTE-P-LOGAPP))
           :use (:instance UNSIGNED-BYTE-P-LOGAPP (size n) (size1 2) (i p) (j x))))) 

;; ;drop??? see next lemma
;; (defthmd logcdr-all-ones-lemma
;;   (implies (and (not (unsigned-byte-p n (1+ x)))
;;                 (unsigned-byte-p n x)
;;                 (integerp n)
;;                 (< 0 n)
;;                 )
;;            (equal (logcdr x) 
;;                   (loghead (1- n) -1)))
;;   :rule-classes nil
;;   :hints (("goal" 
;;            :induct (unsigned-byte-p n x)
;;            :in-theory (enable LRDT))))

;If X is an unsigned-byte of length N, then saying that X+1 is also an unsigned-byte of length N is the same as
;saying that X isn't all ones.
(defthm unsigned-byte-p-of-x+1
  (implies (and (syntaxp (not (quotep x))) ;keeps ACL2 from being fancy with unification
                (unsigned-byte-p n x))
           (equal (unsigned-byte-p n (+ 1 x))
                  (and (integerp n)
                       (<= 0 n)
                       (not (equal x 
                                   (loghead n -1) ;all ones!
                                   )))))
  :hints (("goal" 
           :induct (unsigned-byte-p n x)
           :in-theory (e/d (LRDT) (unsigned-byte-p* ;for acl2 3.0
                                   )))))

(local (in-theory (disable logcons-of-0)))

(defthm logbitp-to-bound-when-usb
  (implies (UNSIGNED-BYTE-P N X)
           (equal (LOGBITP (+ -1 N) x)
                  (<= (expt 2 (+ -1 n)) x)))
  :hints (("Goal" :in-theory (enable LOGBITP))))

(defthm logbitp-to-bound-when-usb
  (implies (UNSIGNED-BYTE-P N X)
           (equal (LOGBITP (+ -1 N) x)
                  (<= (expt 2 (+ -1 n)) x)))
  :hints (("Goal" :in-theory (enable LOGBITP))))

(defthm logbit-to-bound-when-usb
  (implies (UNSIGNED-BYTE-P N X)
           (equal (equal 0 (LOGBIT (+ -1 N) x))
                  (< x (expt 2 (+ -1 n)))))
  :hints (("Goal" :in-theory (disable LOGBITP-TO-BOUND-WHEN-USB)
           :use (:instance logbitp-to-bound-when-usb))))
                 
;; This rule doesn't really have a place.  It involves reasoning about
;; additions that equal exactly a power of two.

(encapsulate
 ()
;make unlocal?

 (local (defthm sum-power-of-two-helper1
          (implies (and (integerp n)
                        (< 0 n)
                        (not (logbitp (1- n) x))
                        (not (logbitp (1- n) y))
                        (unsigned-byte-p n x)
                        (unsigned-byte-p n y)
                        (unsigned-byte-p 1 c))
                   (not (equal (+ x y c) (expt 2 n))))
          :rule-classes nil
          :hints (("goal" ;:do-not '(generalize eliminate-destructors)
                   :do-not-induct t
                   :in-theory (e/d ( ;LRDT ;expt2* 
                                    EVEN-ODD-DIFFERENT-2
                                    EXPONENTS-ADD-UNRESTRICTED
                                    ;logendp
                                    ) 
                                   (LOGBITP-OF-LOGCDR2
                                    LOGCONS-0-EXPT-HACK
;UNSIGNED-BYTE-P-OF-LOGCDR
                                    ))))))

 (defthm sum-power-of-two
   (implies (and (syntaxp (quotep k))
                 (integerp k)
                 (equal k (expt 2 (1- (integer-length k))))
                 (< 1 (integer-length k))
                 (unsigned-byte-p (1- (integer-length k)) x)
                 (unsigned-byte-p (1- (integer-length k)) y)
                 (not (logbitp (1- (1- (integer-length k))) x))
                 (not (logbitp (1- (1- (integer-length k))) y)))
            (not (equal (+ x y) k)))
   :hints (("goal" :use ((:instance sum-power-of-two-helper1 
                                    (c 0) 
                                    (n (1- (integer-length k)))))))))




        
(encapsulate
 ()

;gross proof
;specious simplification!
;make unlocal?
 (local (defthm sum-power-of-two-helper2
          (implies (and (integerp n)
                        (< 0 n)
                        (logbitp (1- n) x)
                        (logbitp (1- n) y)
                        (unsigned-byte-p 1 c)
                        (unsigned-byte-p n x)
                        (unsigned-byte-p n y))
                   (equal (equal (+ x y c) (expt 2 n))
                          (and (equal x (expt 2 (1- n)))
                               (equal y (expt 2 (1- n)))
                               (equal c 0))))
          :rule-classes nil
          :otf-flg t
          :hints (("goal" 
                   :in-theory (e/d (LRDT ;expt2*
                                    EXPONENTS-ADD-UNRESTRICTED
                                         ) (LOGCONS-0-EXPT-HACK))
                   ;:induct (sub1-logcdr-logcdr-carry-induction n x y c)
                   )))) ;not needed, but speeds things up

 (defthmd sum-power-of-two-1
   (implies (and (syntaxp (quotep k))
                 (integerp k)
                 (equal k (expt 2 (1- (integer-length k))))
                 (< 1 (integer-length k))
                 (unsigned-byte-p (1- (integer-length k)) x)
                 (unsigned-byte-p (1- (integer-length k)) y)
                 (logbitp (1- (1- (integer-length k))) x)
                 (logbitp (1- (1- (integer-length k))) y))
            (equal (equal (+ x y) k)
                   (and (equal x (expt 2 (1- (1- (integer-length k)))))
                        (equal y (expt 2 (1- (1- (integer-length k))))))))
   :hints (("goal" :use (
                         (:instance sum-power-of-two-helper2 
                                    (c 0) 
                                    (n (1- (integer-length k)))))))))


