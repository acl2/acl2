#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#
(in-package "ACL2")

;make the inclusion of arithmetic stuff local?
(include-book "ihs/ihs-lemmas" :dir :system)
(local (include-book "arithmetic")) ;bzo this breaks stuff! when loghead is enabled in this book.
(include-book "ash")
(include-book "unsigned-byte-p")
(include-book "logcar")
(include-book "logcdr")
(include-book "logcons")

(in-theory (disable loghead))

(defthm integerp-of-loghead
  (integerp (loghead size i)))

(defthm loghead-nonnegative-rewrite
  (<= 0 (loghead size i)))


;see also LOGHEAD-TYPE
(defthm loghead-nonnegative-linear
  (<= 0 (loghead size i))
  :rule-classes :linear)

(defthm loghead-when-i-is-not-an-integerp
  (implies (not (integerp i))
           (equal (loghead size i)
                  0))
  :hints (("Goal" :in-theory (enable loghead))))

(defthm loghead-when-i-is-0
  (equal (loghead size 0) 
         0) 
  :hints (("Goal" :in-theory (enable loghead))))

(in-theory (disable loghead-size-0)) ;loghead-when-i-is-0 is better

(defthm loghead-when-size-is-not-positive
  (implies (<= size 0)
           (equal (loghead size i)
                  0))
  :hints (("Goal" :in-theory (enable loghead))))

(in-theory (disable loghead-0-i)) ;since we have LOGHEAD-WHEN-SIZE-IS-NON-POSITIVE

(defthm loghead-when-size-is-not-an-integerp
  (implies (not (integerp size))
           (equal (loghead size i)
                  0))
  :hints (("Goal" :in-theory (enable loghead))))

(defthm unsigned-byte-p-loghead-better
  (implies (<= size bits)
           (equal (unsigned-byte-p bits (loghead size i))
                  (and (integerp bits)
                       (<= 0 bits))))
  :hints (("Goal" :use (:instance unsigned-byte-p-loghead (size1 bits) (size size))
           :in-theory (disable unsigned-byte-p-loghead))))

(in-theory (disable unsigned-byte-p-loghead)) ;we'll use unsigned-byte-p-loghead-better instead

(defthm unsigned-byte-p-loghead-forward-chaining
  (implies (and (integerp n)
                (<= 0 n))
           (unsigned-byte-p n (loghead n x)))
  :hints (("goal" :in-theory (enable unsigned-byte-p loghead)))
  :rule-classes ((:forward-chaining :trigger-terms ((loghead n x)))))

;we could use min in the conclusion
(defthm loghead-loghead-better
  (equal (loghead size1 (loghead size i))
         (if (< (nfix size1) (nfix size))
             (loghead (nfix size1) i)
           (loghead (nfix size) i)))
  :hints (("Goal" :in-theory (e/d () 
                                  (loghead-loghead
                                   loghead-leq))
           :use loghead-loghead)))

(in-theory (disable loghead-loghead)) 

(defthm loghead-does-nothing-rewrite
  (equal (equal (loghead n x) x)
         (unsigned-byte-p (nfix n) x))
  :hints (("Goal" :in-theory (enable LOGHEAD UNSIGNED-BYTE-P INTEGER-RANGE-P))))

;gen?
(defthm loghead-1
  (equal (loghead 1 x)
         (logcar x))
  :hints (("goal" :in-theory (enable loghead logcons))))

(defthm loghead-<
  (implies (and (< x y)
                (<= 0 x))
           (< (loghead n x) y))
  :hints (("goal" :in-theory (enable loghead))))

(defthm loghead-<=
  (implies (and (<= x y)
                (<= 0 x))
           (<= (loghead n x) y))
  :hints (("goal" :in-theory (enable loghead))))


;this version doesn't have the FORCEd hyps (or any hyps for that matter)
(defthm logcar-loghead-better
  (equal (logcar (loghead size i))
         (if (or (not (integerp size))
                 (<= size 0))
             0 
           (logcar i)))
  :hints
  (("Goal" :use logcar-loghead
    :in-theory (e/d (
                     ) 
                    (logcar-loghead)))))

(in-theory (disable logcar-loghead)) 



;this really should go in lrdt instead of logehead*??
(defthm loghead*-better
  (implies (and (integerp size)
                (<= 0 size)
                )
           (equal (loghead size i)
                  (if (equal size 0)
                      0
                    (logcons (logcar i)
                             (loghead (1- size) (logcdr i))))))
  :rule-classes
; Matt K.: Changed loghead to loghead$inline 11/10/2012 to accommodate change
; by Jared Davis to define loghead using defun-inline in
; ihs/basic-definitions.lisp.
  ((:definition :clique (loghead$inline)
                :controller-alist ((loghead$inline t t))))
  :hints (("Goal" :use (:instance loghead*) :in-theory (disable loghead*))))

;(in-theory (disable LOGHEAD*)) ;already disabled?

(defthm loghead-+-cancel-better
  (implies (and ;(integerp size)
                ;(>= size 0)
                (integerp i)
                (integerp j)
                (integerp k))
           (equal (equal (loghead size (+ i j))
                         (loghead size (+ i k)))
                  (equal (loghead size j)
                         (loghead size k))))
  :hints (("Goal" :use (:instance loghead-+-cancel)
           :in-theory (disable loghead-+-cancel))))

(in-theory (disable loghead-+-cancel)) 

;make more versions of this
;bzo normalize the leading constant of things like (LOGHEAD 16 (+ 65535 x)).
(defthm loghead-+-cancel-better-alt
  (implies (and ;(integerp size)
                ;(>= size 0)
                (integerp i)
                (integerp j)
                (integerp k))
           (equal (equal (loghead size (+ j i))
                         (loghead size (+ k i)))
                  (equal (loghead size j)
                         (loghead size k))))
  :hints (("Goal" :use (:instance loghead-+-cancel)
           :in-theory (disable loghead-+-cancel))))

;see also the :meta rule about loghead. -ews
(defthm loghead-+-loghead-better
  (equal (loghead size (+ i (loghead size j)))
         (if (integerp j)
             (loghead size (+ i j))
           (loghead size i)))
  :hints (("Goal" :cases ((integerp i) (not (acl2-numberp i)))
           :in-theory (enable loghead-+-loghead))))

(in-theory (disable LOGHEAD-+-LOGHEAD)) ;our rule is better

(defthm loghead-+-loghead-better-alt
  (equal (loghead size (+ (loghead size i) j))
         (if (integerp i)
             (loghead size (+ i j))
           (loghead size j)))
  :hints (("Goal" :use (:instance  loghead-+-loghead-better (i j) (j i)))))

(defthm loghead-+-loghead-better-alt-three-addends
  (equal (loghead size (+ i1 i2 (loghead size j)))
         (if (integerp j)
             (loghead size (+ i1 i2 j))
           (loghead size (+ i1 i2))))
  :hints (("Goal" :use (:instance loghead-+-loghead-better (i (+ i1 i2)) (j j)))))
  
; improve loghead-cancel-better-alt, etc.
(defthm loghead-sum-subst-helper
  (implies (and (equal (loghead n x) y)
                (syntaxp (quotep y))
;                (integerp x)
                (integerp z)  ; could we say (or (integerp x) (integerp z)) ?
                )
           (equal (loghead n (+ x z))
                  (if (integerp x)
                      (loghead n (+ y z))
                    (if (acl2-numberp x)
                        0
                      (loghead n z)
                      ))))
  :hints (("Goal" :in-theory (enable LOGHEAD-+-LOGHEAD-better))))



(defthm loghead-sum-subst
  (implies (and (equal (loghead n x) (loghead n y))
                (syntaxp (and (term-order y x)
                              (not (equal y x))))
;                (integerp x)
                (integerp y)
                (integerp z) ;bzo can we drop this? improve loghead-cancel-better-alt, etc. similarly
                )
           (equal (loghead n (+ x z))
                  (if (integerp y)
                      (if (integerp x)
                          (loghead n (+ y z))
                        (if (acl2-numberp x)
                            0
                          (loghead n z)
                          ))
                    (loghead n z)
                    )))
  :hints (("Goal" :cases ((integerp z) (not (acl2-numberp z))))))


;improve this
(defthm loghead-sum-subst-alt
  (implies (and (equal (loghead n x) (loghead n y))
                (syntaxp (and (term-order y x)
                              (not (equal y x))))
                (case-split (integerp x))
                (case-split (integerp y))
;                (integerp z) ;bzo improve loghead-cancel-better-alt, etc. similarly
                )
           (equal (loghead n (+ z x))
                  (loghead n (+ z y))))
  :hints (("Goal" :cases ((integerp z) (not (acl2-numberp z))))))

(defthm loghead-of-minus
  (equal (loghead n (- x))
         (if (integerp x)
             (if (equal 0 (loghead n x)) 
                 0
               (- (expt 2 n) (loghead n x)) ;the usual case
               )
           0))
  :otf-flg t
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable loghead
                              EXPONENTS-ADD-UNRESTRICTED))))

(defthm loghead-equal-move-minus
  (implies (and (integerp a)
                (integerp j)
                (integerp k))
           (equal (EQUAL (LOGHEAD size A) (LOGHEAD size (+ (- J) K)))
                  (EQUAL (LOGHEAD size (+ j A)) (LOGHEAD size K))))
  :hints (("Goal" :use (:instance LOGHEAD-+-CANCEL-BETTER (size size) (i j) (j a) (k (- k j)))))
  )
        
(defthm loghead-plus-constant-equal-constant
  (implies (and (syntaxp (and (quotep j)
                              (quotep k)))
                (integerp a)
                (integerp j)
                (integerp k)
                (<= 0 size)
                (integerp size)
                )
           (equal (equal (loghead size (+ j a)) k)
                  (and (unsigned-byte-p size k)
                       (equal (loghead size a) (loghead size (- k j)))))))

(encapsulate
 ()
 (local (defthm loghead-of-one-more-than-x-helper
          (implies (and (syntaxp (not (quotep x))) ;don't unify (+ 1 x) with a constant
                        (integerp x)
                        (<= 0 n))
                   (equal (loghead n (+ 1 x))
                          (if (equal (loghead n x) (+ -1 (expt 2 n)))
                              0
                            (+ 1 (loghead n x)))))
          :hints (("Goal" ;:do-not '(generalize eliminate-destructors)
                   :in-theory (enable loghead
                                      unsigned-byte-p 
                                      integer-range-p ;prove a rule for integer-range-p of (+ 1 x)
                                      )))))

;This can lead to case splits, so we disable it by default.
 (defthmd loghead-of-one-more-than-x
   (implies (and (syntaxp (not (quotep x)))
;                (integerp x)
                 (<= 0 n))
            (equal (loghead n (+ 1 x))
                   (if (integerp x)
                       (if (equal (loghead n x)
                                  (+ -1 (expt 2 n)))
                           0 (+ 1 (loghead n x)))
                     (if (acl2-numberp x)
                         0
                       (loghead n 1)
                       ))))
   :hints (("Goal" :in-theory (disable loghead-of-one-more-than-x-helper)
            :use (:instance loghead-of-one-more-than-x-helper)))))

;This can lead to case splits, so we disable it by default.
(defthmd loghead-of-one-less-than-x
  (implies (and (syntaxp (not (quotep x))) ;don't unify (+ 1 x) with a constant
                (integerp x)
                (<= 0 n))
           (equal (loghead n (+ -1 x))
                  (if (equal (loghead n x) 0)
                      (+ -1 (expt 2 n))
                    (+ -1 (loghead n x)))))
  :hints (("Goal" :in-theory (e/d (loghead
                                     UNSIGNED-BYTE-P 
                                     INTEGER-RANGE-P ;prove a rule for integer-range-p of (+ 1 x)
                                     imod
                                     ) 
                                  (mod-cancel
                                   MOD-STRETCH-BASE ;looped!
                                   MOD-STRETCH-BASE-2 ;looped!
                                   )))))

;can this loop?
;generalize?
(defthm loghead-+-reduce
  (implies (and (equal (loghead size y) z) ;z is a free variable
                (syntaxp (and (quotep z) (not (quotep y))))
                (integerp x)
                (integerp y)
                )
           (equal (loghead size (+ x y))
                  (loghead size (+ x z)))))

(defthm LOGHEAD-of-*-expt
  (implies (and (integerp x)
                (<= n m) ;handle the other case
                (integerp n)
                (<= 0 n)
                (integerp m)
                )
           (equal (LOGHEAD n (BINARY-* (expt 2 m) X))
                  0))
  :hints (("Goal" :in-theory (e/d (unary-/-of-expt loghead expt-gather) (expt-minus EXPONENTS-ADD))
           :do-not '(generalize eliminate-destructors))))

(defthm LOGHEAD-of-*-expt-alt
  (implies (and (integerp x)
                (<= n m) ;handle the other case
                (integerp n)
                (<= 0 n)
                (integerp m)
                )
           (equal (LOGHEAD n (BINARY-* X (expt 2 m)))
                  0))
  :hints (("Goal" :in-theory (e/d (unary-/-of-expt loghead expt-gather) (expt-minus EXPONENTS-ADD))
           :do-not '(generalize eliminate-destructors))))

(defthm LOGHEAD-of-*-expt-const
  (implies (and (syntaxp (quotep k))
                (power2p k)
                (>= (expo k) n)
                (integerp x)
                (integerp n)
                (<= 0 n)
                )
           (equal (LOGHEAD n (BINARY-* k X))
                  0))
  :hints (("Goal" :in-theory (disable LOGHEAD-of-*-expt)
           :use (:instance  LOGHEAD-of-*-expt (m (expo k))))))

(defthm loghead-of-*-expt-2-special
  (implies (integerp x)
           (equal (loghead n (binary-* (expt 2 n) x))
                  (logapp n 0 (loghead 0 x))
                  ))
  :hints (("Goal" :in-theory (e/d (unary-/-of-expt loghead expt-gather) (expt-minus exponents-add))
           :do-not '(generalize eliminate-destructors))))


(defthm loghead-of-*-expt-2-special-const
  (implies (and (syntaxp (quotep k))
                (equal k (expt 2 n))
                (integerp x))
           (equal (loghead n (binary-* k x))
                  (logapp n 0 (loghead 0 x))
                  ))
  :hints (("Goal" :use (:instance loghead-of-*-expt-2-special (n (expo k)))
           :in-theory (disable loghead-of-*-expt-2-special))))

(defthm loghead-of-prod-lemma
  (implies (integerp y)
           (equal (loghead n (* (loghead n x) y))
                  (loghead n (* (ifix x) y))))
  :hints (("Goal" :in-theory (enable loghead imod))))

(defthm loghead-of-prod-lemma-alt
  (implies (integerp y)
           (equal (loghead n (* y (loghead n x)))
                  (loghead n (* (ifix x) y))))
  :hints (("Goal" :use (:instance loghead-of-prod-lemma)
           :in-theory (disable loghead-of-prod-lemma))))

;why is denominator suddenly showing up?

;make a version that matches on constants
(defthm LOGHEAD-of-*-expt-other-case
  (implies (and (integerp x)
                (< m n) ;handle the other case
                (integerp n)
                (<= 0 n)
                (<= 0 m)
                (integerp m)
                )
           (equal (LOGHEAD n (BINARY-* (expt 2 m) X))
                  (BINARY-* (expt 2 m) (LOGHEAD (- n m) X))
                  ))
  :hints (("Goal" ;:in-theory (e/d (unary-/-of-expt loghead expt-gather) (expt-minus EXPONENTS-ADD))
           :use (:instance INTEGERP-EXPT (n (- n m)))
           :in-theory (e/d (loghead ifix
                                    mod-cancel) 
                           (INTEGERP-OF-INVERSE-OF-EXPT
                                          MOD-X-I*J ;yucky force!
                                           ))
           :do-not '(generalize eliminate-destructors))))



(defthm LOGHEAD-of-*-expt-other-case-constant-version
  (implies (and (syntaxp (quotep k))
                (power2p k)
                (integerp x)
                (< (expo k) n) ;handle the other case
                (integerp n)
                (<= 0 n)
                (<= 0 (expo k))
;                (integerp m)
                )
           (equal (LOGHEAD n (BINARY-* k X))
                  (BINARY-* k (LOGHEAD (- n (expo k)) X))
                  ))
  :hints (("Goal" :use (:instance  LOGHEAD-of-*-expt-other-case (m (expo k)))))
  )


(defthm loghead-of-sum-of-prod-of-loghead-lemma
  (implies (and (integerp x)
                (integerp y)
                (integerp a)
                )
           (equal (loghead n (+ a (* y (loghead n x))))
                  (loghead n (+ a (* x y)))))
  :hints (("Goal" :in-theory (disable loghead-of-prod-lemma
                                      loghead-of-prod-lemma-alt

                                      )
           :use (:instance loghead-of-prod-lemma (x x) (y y) (N n)))))


(defthm loghead-of-sum-of-prod-of-loghead-lemma-better2
  (implies (and (integerp x)
                (integerp y)
                (integerp a)
                )
           (equal (loghead n (+ a (- (loghead n x))))
                  (loghead n (+ a (- x)))))
  :hints (("Goal" :in-theory (disable loghead-of-sum-of-prod-of-loghead-lemma
                                      LOGHEAD-+-CANCEL-0 ;was forcing
                                      LOGHEAD-LOGHEAD-BETTER
                                      LOGHEAD-OF-MINUS
                                      )
           :use (:instance loghead-of-sum-of-prod-of-loghead-lemma (y -1)))))


(defthm loghead-hack
  (equal (loghead 16 (+ -65535 off))
         (loghead 16 (+ 1 off)))
  :hints (("Goal" :in-theory (enable loghead 
                                     imod ifix))))

(encapsulate
 ()                  
 (local (defthm loghead-of-sum-with-constant-helper
          (implies (and (syntaxp (quotep c))
                        (unsigned-byte-p n c)
                        (unsigned-byte-p n x)
                        (< x (- (expt 2 n) (loghead n c)))
                        )
                   (equal (loghead n (+ c x))
                          (+ (loghead n c) x)))
          :hints (("Goal" :in-theory (enable unsigned-byte-p integer-range-p)))))

;do we want to disable this?
 (defthm loghead-of-sum-with-constant
   (implies (and (syntaxp (quotep c)) ;could also require n to be a constant?
                 (< x (- (expt 2 n) (loghead n c)))
                 (unsigned-byte-p n x)
                 (integerp c)
                 )
            (equal (loghead n (+ c x))
                   (+ (loghead n c) x)))

   :hints (("Goal" :use (:instance loghead-of-sum-with-constant-helper (n (nfix n)) (c (loghead n c)))
            :in-theory (disable  loghead-of-sum-with-constant-helper
                                 LOGHEAD-LOGHEAD-BETTER
                                 LOGHEAD-IDENTITY
                                 )))))


(include-book "inductions") 

(defthm loghead-induction t
  :rule-classes ((:induction :pattern (loghead n x)
                             :condition t
                             :scheme (loglistr n x))))







;move to loghead.lisp
;trying disabled
(defthmd loghead-almost
  (implies (and (not (unsigned-byte-p n x))
                (unsigned-byte-p (1+ n) x)
                )
           (equal (loghead n x)
                  (if (integerp n)
                      (- x (ash 1 n)) ;use expt here?
                    0
                    )))
  :hints (("goal" ; :induct t
           :do-not '(generalize eliminate-destructors)
           :in-theory (e/d ( ;LRDT ;open-logcons
                            logcdr-of-sum
                            ;ash* ;bzo seems to loop with LOGCONS-OF-0 (problem only arose in the move to acl2 version 3.0)
                            loghead*-better
                            unsigned-byte-p*
                            logcdr--
                          
                            ) ( ;evenp-of-logcons
                            UNSIGNED-BYTE-P-FORWARD
                            ARITH-MOVE-NEGATED-TERM 
                            expt-2-cruncher)))))

;See also the rule loghead-almost.
;Is this rule too expensive to leave enabled?
(defthmd loghead-split-into-2-cases
  (implies (and (< x (* 2 (expt 2 n)))
                (<= 0 x)
                (integerp x)
                (integerp n) ;drop?
                )
           (equal (loghead n x)
                  (if (< x (expt 2 n))
                      x
                    (- x (expt 2 n)))))
  :hints (("Goal" :use (:instance LOGHEAD-ALMOST (n n) (x x))
           :expand (UNSIGNED-BYTE-P (+ 1 N) X)
           :in-theory (e/d (ash EXPONENTS-ADD-UNRESTRICTED) (ARITH-MOVE-NEGATED-TERM
                                                             LOGHEAD-ALMOST)))))

;Is this rule too expensive to leave enabled?
(defthmd loghead-sum-split-into-2-cases
  (implies (and (integerp i)
                (integerp j)
;                (integerp n)
        ;        (<= 0 n)
                )
           (equal (loghead n (+ i j))
                  (if (< (+ (loghead n i) (loghead n j)) (expt 2 n))
                      (+ (loghead n i) (loghead n j))
                    (+ (loghead n i) (loghead n j) (- (expt 2 n))))))
  :hints (("Goal" :in-theory (disable loghead-split-into-2-cases)
           :use (:instance loghead-split-into-2-cases 
                           (n n)
                           (x (+ (loghead n i) (loghead n j)))
                           ))))

(defthm loghead-sum-split-into-2-when-i-is-a-constant
  (implies (and (syntaxp (quotep i))
                (integerp i)
                (integerp j)
;                (integerp n)
 ;               (<= 0 n)
                )
           (equal (loghead n (+ i j))
                  (if (< (+ (loghead n i) (loghead n j)) (expt 2 n))
                      (+ (loghead n i) (loghead n j))
                    (+ (loghead n i) (loghead n j) (- (expt 2 n))))))
  :hints (("Goal" :in-theory (enable  loghead-sum-split-into-2-cases))))



;; (defstub foo (x) t)

;; (thm
;;  (implies (and (not (equal x 65535))
;;                (not (equal x 65534))
;;                (unsigned-byte-p 16 x))
;;           (equal (foo (loghead 16 (+ 2 x)))
;;                  (foo (+ 2 x))))
;;  :hints (("Goal" :in-theory (disable UNSIGNED-BYTE-P-FORWARD-TO-EXPT-BOUND
;;                                      ;extend-<
;;                                      ))))


;; (thm
;;  (implies (and (not (equal x 65535))
;;                (not (equal x 65534))
;;                (not (equal x 65533))
;;                (not (equal x 65532))
;;                (unsigned-byte-p 16 x))
;;           (equal (foo (loghead 16 (+ 4 x)))
;;                  (foo (+ 4 x))))
;;  :hints (("Goal" :in-theory (disable UNSIGNED-BYTE-P-FORWARD-TO-EXPT-BOUND
;;                                      LOGHEAD-UPPER-BOUND
;;                                      EXTEND-<
;;                                      ;UNSIGNED-BYTE-P-FORWARD-TO-NONNEGATIVE-INTEGERP
;;                                      ))))
 

(defthm loghead-sum-chop-first-arg-when-constant
  (implies (and (syntaxp (and (quotep x)
                              (quotep n) ;bzo without this we got a loop; change other rules similarly
                              ))
                (not (unsigned-byte-p n x))
                (<= 0 n)
                (integerp n)
                (integerp x)
                (integerp y))
           (equal (loghead n (+ x y))
                  (loghead n (+ (loghead n x) y)))))



;bzo generalize
(defthm loghead-bound
  (and ;(<= 0 (loghead 32 x))
       (<= (loghead 32 x) (1- (expt 2 32))))
  :hints (("goal" :in-theory (disable unsigned-byte-p-loghead)
           :use ((:instance unsigned-byte-p-loghead (i x) (size1 32) (size 32)))))
  :rule-classes :linear)  ;;why not :rewrite too?

;; ;acl2 does something gross here and loses the (integerp x) fact
;; ;kill this one?
;; (defthm loghead-cancel-hack
;;   (implies (and (integerp k)
;;                 (<= 0 x)
;;                 (integerp x)
;;                 (integerp n)
;;                 (<= 0 n)
;;                 )
;;            (equal (equal x (loghead n (+ k x)))
;;                   (and (unsigned-byte-p n x)
;;                        (equal 0 (loghead n k)))))
;;   :otf-flg t
;;   :hints ( ("Goal" :use (:instance loghead-identity (size n) (i x))
;;             :do-not-induct t
;;             :in-theory (e/d (loghead-sum-split-into-2-cases
;;      ;UNSIGNED-BYTE-P-FORWARD-TO-NONNEGATIVE-INTEGERP
;;                              ) 
;;                             (LOGHEAD-TYPE ;bzo these disables are gross!
;;                              loghead-identity
;;                              LOGHEAD-DOES-NOTHING-REWRITE
;;                              UNSIGNED-BYTE-P-LOGHEAD-FORWARD-CHAINING)))))
       
(defthm loghead-cancel-lemma
  (implies (and (integerp a)
                (integerp size)
                (<= 0 size)
                )
           (equal (equal k (loghead size (+ a k)))
                  (and (unsigned-byte-p size k)
                       (equal 0 (loghead size a)))))
  :hints (("Goal" :use (:instance loghead-plus-constant-equal-constant (size size) (j k) (a a) (k k))
           :in-theory (disable loghead-plus-constant-equal-constant))))

(defthm loghead-cancel-lemma-alt
  (implies (and (integerp a)
                (integerp size)
                (<= 0 size)
                )
           (equal (equal k (loghead size (+ k a)))
                  (and (unsigned-byte-p size k)
                       (equal 0 (loghead size a)))))
  :hints (("Goal" :use (:instance loghead-cancel-lemma)
           :in-theory (disable loghead-cancel-lemma))))

;;Help proofs go faster by essentially doing some substitution before ACL2 would get around to substituting.
;;does this rule match both ways on an (equal x y) term?
;; this rule allows ACL2 to quickly realize that these two facts contradict:
;;       (EQUAL x (LOGHEAD 16 (+ 4 y)))
;;       (EQUAL x (LOGHEAD 16 (+ -1 y))))

(defthm loghead-compare-hack
  (implies (and (equal x (loghead n z)) ;z is a free variable
                (not (equal 0 (loghead n (- z y))))
                (integerp y)
                (integerp z)
                )
           (not (equal x (loghead n y)))))

(defthm loghead-cancel-lemma-3
  (implies (and (integerp a)
                (integerp b)
                (integerp x)
                (integerp n)
                (<= 0 n)
                )
           (equal (EQUAL (LOGHEAD n (+ A b X)) X)
                  (and (unsigned-byte-p n x)
                       (EQUAL (LOGHEAD n (+ a b)) 0))))
  :hints (("Goal" :use (:instance loghead-cancel-lemma (size n) (k x) (a (+ a b)))
           :in-theory (disable loghead-cancel-lemma))))

;; (thm
;;  (implies (and (syntaxp (quotep k))
;;                (integerp b)
;;                (integerp a)
;;                (integerp k)
;;                (<= 0 k)
;;                (< k (* 2 65536))
;;                )
;;           (implies (equal (loghead 16 k) (loghead 16 (+ a b)))
;;                    (equal k (+ (loghead 16 a) (loghead 16 b)))))
;;  :hints (("Goal" :in-theory (enable loghead-sum-split-into-2-cases))))

;expensive!

(defthmd loghead-hack2
  (implies (and (equal (expt 2 n) (+ (loghead n a) (loghead n b)))
                (integerp a) 
                (integerp b)
                )
           (equal (loghead n (+ a b))
                  0))
  :hints (("Goal" :in-theory (enable loghead-sum-split-into-2-cases))))
        
;; Allows ACL2 to quicly see that facts like this contradict:
;; (EQUAL x (LOGHEAD 16 (+ 4 y)))
;; (EQUAL (LOGHEAD 16 (+ 3 x)) y))

(defthm loghead-compare-hack-2
  (implies (and (equal y (loghead n (+ a x)))
                (not (equal 0 (loghead n (+ a b))))
                (integerp a)
                (integerp b)
                )
           (equal (equal x (loghead n (+ b y)))
                  nil))
  :hints (("Goal" :use (:instance loghead-cancel-lemma-3 (n n) (b b))
           :in-theory (disable loghead-cancel-lemma-3))))

(defthm evenp-of-loghead
  (equal (evenp (loghead size i))
         (or (zp size)
             (evenp (ifix i))))
  :hints (("Goal" :in-theory (e/d (loghead imod) 
                                  (mod-cancel)))))




;; ;bzo zz will going against acl2's order be bad?

;; ;Just like term-order, except it calls our-lexorder
;; (defun our-lexorder (x y)
;;   "Documentation available via :doc"
;;   (declare (xargs :guard t))
;;   (cond ((atom x)
;;          (cond ((atom y) (our-alphorder x y)) (t t)))
;;         ((atom y) nil)
;;         ((equal (car x) (car y))
;;          (our-lexorder (cdr x) (cdr y)))
;;         (t (our-lexorder (car x) (car y)))))

;; ;Just like term-order, except it calls our-lexorder
;; (defun our-term-order (term1 term2)
;;   (mv-let (var-count1 fn-count1 p-fn-count1)
;;           (var-fn-count term1)
;;           (mv-let (var-count2 fn-count2 p-fn-count2)
;;                   (var-fn-count term2)
;;                   (cond ((< var-count1 var-count2) t)
;;                         ((> var-count1 var-count2) nil)
;;                         ((< fn-count1 fn-count2) t)
;;                         ((> fn-count1 fn-count2) nil)
;;                         ((< p-fn-count1 p-fn-count2) t)
;;                         ((> p-fn-count1 p-fn-count2) nil)
;;                         (t (our-lexorder term1 term2))))))


(include-book "../util/syntaxp")

;can this loop (if y is a loghead call?)?
(defthm loghead-subst
  (implies (and (equal (loghead m x) y) ;y and m are free variables
                (syntaxp (smaller-term y x))
                (<= n m)
                (integerp m)
                )
           (equal (loghead n x)
                  (loghead n y))))

;The proof of this was a little tricky (due to ACL2 trying to get smart with substitution?). -ews
(defthm loghead-subst2
  (implies (and (equal (loghead m x) (loghead m y)) ;y and m are free variables
                (syntaxp (smaller-term y x))
                (<= n m)
                (integerp m)
                )
           (equal (loghead n x)
                  (loghead n y)))
  :hints (("Goal" :use ((:instance loghead-subst (y (loghead m y)))
                        (:instance LOGHEAD-LOGHEAD-BETTER (size1 n) (size m) (i y)))
           :in-theory (disable loghead-subst LOGHEAD-LOGHEAD-BETTER))))

(defthm loghead-+-cancel-0-better
  (implies (and (integerp j)
                (integerp i)
                )
           (equal (equal (loghead size (+ i j))
                         (loghead size i))
                  (equal (loghead size j) 0)))
  :hints (("Goal" :use (:instance acl2::loghead-+-cancel-0 (acl2::i i) (acl2::j j) (acl2::size size))
           :in-theory (disable acl2::loghead-+-cancel-0))))

(in-theory (disable acl2::loghead-+-cancel-0)) 

(defthm loghead-+-cancel-0-alt
  (implies (and (integerp m)
                (integerp k)
                )
           (equal (equal (loghead n k) (loghead n (+ m k)))
                  (equal 0 (loghead n m)))))

(defthm loghead-sum-equality-move-negated-addend
  (implies (and (integerp j)
                (integerp k)
                (integerp m)
                (integerp a)
                )
           (equal (equal (loghead 16 j) (loghead 16 (+ k (- a) m)))
                  (equal (loghead 16 (+ j a)) (loghead 16 (+ k m))))))

(defthm loghead-cancellation-hack
  (implies (and (not (equal (loghead size j) (loghead size k)))
                (integerp x)
                (integerp j)
                (integerp k))
           (equal (equal (loghead size (+ j x)) (+ k x))
                  nil))
  :hints (("Goal" :in-theory (disable acl2::loghead-+-cancel-better-alt
                                      acl2::loghead-sum-subst
                                      acl2::loghead-compare-hack)
           :use (:instance acl2::loghead-+-cancel-better-alt (acl2::size size) (acl2::j j) (acl2::k k) (acl2::i x)))))

;more like this? this lets' things get done faster, since ACL2 doesn't have to get around to substituting...
(defthmd loghead-compare-hack-2-alt
  (implies (and (equal y (+ a x))
                (not (equal 0 (loghead n (+ a b))))
                (integerp a)
                (integerp b)
                )
           (equal (equal x (loghead n (+ b y)))
                  nil))
  :hints (("Goal" :use (:instance acl2::loghead-cancel-lemma-3 (acl2::n n) (acl2::b b) (acl2::x x) (acl2::a a))
           :in-theory (disable acl2::loghead-cancel-lemma-3))))                 



(defthmd loghead-sum-equality-move-negative
  (implies (and (syntaxp (quotep k))
                (< k 0)
                (integerp k)
                (integerp a)
                )
           (equal (equal (loghead 16 (+ k a)) b)
                  (and (equal (loghead 16 a) (loghead 16 (+ (- k) b)))
                       (unsigned-byte-p 16 b))))
  :hints (("Goal" :use (:instance acl2::loghead-+-cancel (acl2::size 16) (acl2::i (- k)) (acl2::j (+ k a)) (acl2::k b))
           :in-theory (disable acl2::loghead-+-cancel
                               ))))
;bzo gen
(defthm loghead-expt-hack
  (equal (loghead size (expt 2 size))
         0)
  :hints (("Goal" :in-theory (enable loghead))))


(defthm loghead-of-minus-2-to-the-size
  (equal (loghead size (- (expt 2 size)))
         0)
  :hints (("Goal" :in-theory (enable loghead))))


(defthm loghead-cancel-hack
  (implies (and (integerp a)
                (integerp freek)
                (integerp offset2)
                (integerp freeoff))
           (equal (equal (loghead size (+ a offset2)) (loghead size (+ freek freeoff a)))
                  (equal (loghead size offset2) (loghead size (+ freek freeoff))))))
;; ;gen
;; (defthm loghead-sum-loghead-alt
;;   (equal (loghead 16 (+ y (loghead 16 x)))
;;          (if (integerp x)
;;              (if (integerp y)
;;                  (loghead 16 (+ x y))
;;                (if (acl2-numberp y)
;;                    0
;;                  (loghead 16 x)))
;;            (loghead 16 y)))
;;   :otf-flg t
;;   :hints (("Goal" :use (:instance LOGHEAD-+-LOGHEAD (size 16) (i y) (j (fix x)))
;;            :in-theory (disable LOGHEAD-+-LOGHEAD))))

;; ;gen
;; (defthm loghead-sum-loghead
;;   (equal (loghead 16 (+ (loghead 16 x) y))
;;          (if (integerp x)
;;              (if (integerp y)
;;                  (loghead 16 (+ x y))
;;                (if (acl2-numberp y)
;;                    0
;;                  (loghead 16 x)))
;;            (loghead 16 y))))

(defthm loghead-subst-weird
  (implies (and (syntaxp (quotep k))
                (equal (loghead 16 offset2)
                       (loghead 16 (+ freek freeoff)))
                (syntaxp (quotep freek))
                (syntaxp (smaller-term freeoff offset2))
                (integerp k)
                (integerp freek)
                (integerp offset2)
                (integerp freeoff))
           (equal (loghead 16 (+ k offset2))
                  (loghead 16 (+ k (+ freek freeoff)))
                  ))
  :otf-flg t
  :hints (("Goal" :use (:instance LOGHEAD-+-LOGHEAD-BETTER (size 16) (acl2::i offset2) (acl2::j k))
           :in-theory (disable acl2::loghead-+-cancel-better
                               acl2::loghead-subst2
                               acl2::loghead-subst
                               acl2::loghead-+-loghead-better))))


(encapsulate
 ()

 (local (defthm loghead-+-expt-helper
          (implies (integerp x)
                   (equal (loghead n (+ x (expt 2 n)))
                          (if (natp n)
                              (loghead n x)
                            0)))
          :hints (("goal" :in-theory (enable loghead*-better zp)))))

 (defthm loghead-+-expt
   (implies (integerp x)
            (equal (loghead n (+ x (expt 2 n)))
                   (loghead n x)))
   :hints (("goal" :in-theory (enable zp)
            :cases ((natp n))))))


(defthm loghead-+-expt-alt
  (implies (integerp x)
           (equal (loghead n (+ (expt 2 n) x))
                  (loghead n x)))
  :hints (("goal" :cases ((natp n)))))

;could allow k to be the negative of a power of 2...
;more generally, k could be any integer multiple of 2^n
(defthm loghead-+-expt-constant-version
  (implies (and (syntaxp (quotep k))
                (equal (expt 2 n) k)
                (integerp x)
                )
           (equal (loghead n (+ k x))
                  (loghead n x))))


(encapsulate
 ()
 (local (defthm loghead-ignores-subtraction-of-expt-helper
          (implies (integerp x)
                   (equal (loghead n (+ x (- (expt 2 n))))
                          (if (natp n)
                              (loghead n x)
                            0)))
          :hints (("goal" :in-theory (enable loghead*-better)))))

 (defthm loghead-ignores-subtraction-of-expt
   (implies (integerp x)
            (equal (loghead n (+ x (- (expt 2 n))))
                   (loghead n x)))
   :hints (("goal" :in-theory (enable zp) :cases ((natp n))))))

(defthm loghead-ignores-subtraction-of-expt-alt
  (implies (integerp x)
           (equal (loghead n (+ (- (expt 2 n)) x))
                  (loghead n x))))

(defthm loghead-of-sum-with-multiple-of-expt-2-size
  (implies (and (integerp j)
                (<= 0 size)
                (integerp size)
                (integerp x) 
                )
           (equal (loghead size (+ x (* j (expt 2 size))))
                  (loghead size x))))

(defthm loghead-of-sum-with-multiple-of-expt-2-size-alt
  (implies (and (integerp j)
                (<= 0 size)
                (integerp size) 
                (integerp x) 
                )
           (equal (loghead size (+ (* j (expt 2 size)) x))
                  (loghead size x))))

(defthm loghead-of-sum-integer-and-non-integer
  (implies (and (integerp size2)
                (not (integerp size1)))
           (equal (loghead (+ size1 size2) i)
                  (if (acl2-numberp size1)
                      (loghead 0 i)
                    (loghead size2 i)))))

;drop?
(defthmd equal-loghead-+-simple
  (implies (and (equal (loghead n x) 0)
                (integerp n)
                (integerp x)
                (integerp y)
                (< 0 n)
                )
           (equal (equal (loghead n (+ x y)) 0)
                  (equal (loghead n y) 0)))
  :hints (("goal" :in-theory (enable loghead*-better open-logcons))))

