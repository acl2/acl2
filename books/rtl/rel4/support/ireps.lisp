(in-package "ACL2")

; eric smith, david russinoff, with suggestions by matt kaufmann
; amd, june 2001

;this file was previously called irepsproofs.lisp

;note: the proofs in this file are messy.  i haven't taken much time to clean
;them up by eliminating hacks or increasing elegance. -eric

;todo: add t-p for isigf, etc.

(include-book "rtl") ;BOZO remove!
(include-book "bias")
(include-book "float") ;for the defns
(local (include-book "merge"))
(local (include-book "cat"))
(local (include-book "bvecp"))
(local (include-book "bits"))
(local (include-book "bitn"))
(local (include-book "../arithmetic/top"))

(local (in-theory (enable bvecp-forward)))

;;encoding of floating-point numbers with implicit msb
;;bit vectors of length p+q, consisting of 1-bit sign field,
;;q-bit exponent field (bias = 2**(q-1)-1), and (p-1)-bit
;;significand field:
;; p must be > 1



;;;**********************************************************************
;;;                       field extractors
;;;**********************************************************************

(defund isgnf  (x p q) (bitn x (1- (+ p q))))
(defund iexpof (x p q) (bits x (- (+ p q) 2) (1- p)))
(defund isigf  (x p)   (bits x (- p 2) 0))


;;;**********************************************************************
;;;                       representable numbers
;;;**********************************************************************

(defund nrepp (x p q)
  (and (rationalp x)
       (not (= x 0))
       (< 0 (+ (expo x) (bias q)))
       (< (+ (expo x) (bias q)) (- (expt 2 q) 1))
       (exactp x p)))

(defund drepp (x p q)
  (and (rationalp x)
       (not (= x 0))
       (<= (- 2 p) (+ (expo x) (bias q)))
       (<= (+ (expo x) (bias q)) 0)
       (exactp x (+ -2 p (expt 2 (- q 1)) (expo x))))) ;use bias here?
;bits available in the sig field = p-1-(-bias-expo(x))

(defund irepp (x p q)
  (or (nrepp x p q)
      (drepp x p q)))


;;;**********************************************************************
;;;                      valid encodings
;;;**********************************************************************

(defund nencodingp (x p q)
  (and (bvecp x (+ p q))
       (< 0 (iexpof x p q))
       (< (iexpof x p q) (- (expt 2 q) 1))))

(defund dencodingp (x p q)
  (and (bvecp x (+ p q))
       (= (iexpof x p q) 0)
       (not (= (isigf x p) 0))))

(defund iencodingp (x p q)
  (or (nencodingp x p q)
      (dencodingp x p q)))


;;;**********************************************************************
;;;                       encode
;;;**********************************************************************

; sig, expo, and sgn are defined in float.lisp

(defund dencode (x p q)
  (cat (cat (if (= (sgn x) 1) 0 1)
	    1
            0
            q)
       (1+ q)
       (* (sig x) (expt 2 (+ -2 p (expo x) (bias q))))
       (- p 1)))

(defund nencode (x p q)
  (cat (cat (if (= (sgn x) 1) 0 1)
	    1
            (+ (expo x) (bias q))
            q)
       (1+ q)
       (* (- (sig x) 1) (expt 2 (- p 1)))
       (- p 1)))

(defund iencode (x p q)
  (cond ((nrepp x p q)
	 (nencode x p q))
	((drepp x p q)
	 (dencode x p q))))

;;;**********************************************************************
;;;                       decode
;;;**********************************************************************

(defund ndecode (x p q)
  (* (if (= (isgnf x p q) 0) 1 -1)
     (+ (expt 2 (- (iexpof x p q) (bias q)))
        (* (isigf x p)
           (expt 2 (+ 1 (iexpof x p q) (- (bias q)) (- p)))))))


(defund ddecode (x p q)
  (* (if (= (isgnf x p q) 0) 1 -1)
     (isigf x p)
     (expt 2 (+ 2 (- (bias q)) (- p)))))


(defund idecode (x p q)
  (cond ((nencodingp x p q)
	 (ndecode x p q))
	((dencodingp x p q)
	 (ddecode x p q))))

;;;**********************************************************************
;;;                       theorems
;;;**********************************************************************

(defthm nencodingp-means-not-dencodingp
  (implies (nencodingp x p q)
	   (not (dencodingp x p q)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("goal" :in-theory (enable iencodingp nencodingp dencodingp))))

(defthm dencodingp-means-not-nencodingp
  (implies (dencodingp x p q)
	   (not (nencodingp x p q)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("goal" :in-theory (enable iencodingp nencodingp dencodingp))))

(defthm not-both-nencodingp-and-dencodingp
  (implies (iencodingp x p q)
	   (iff (nencodingp x p q) (not (dencodingp x p q))))
  :hints (("Goal" :in-theory (enable iencodingp)))
  :rule-classes ())



; the field extractors return bit-vectors.


;some of the rules below may be bad because they are put into both the
; forward-chaining and type-prescription rule classes, causing them
; not to always work.

;!! rc
(defthm bvecp-isigf-forward-3
  (implies (case-split (integerp p))
           (bvecp (isigf x p) (- p 1)))
  :hints (("goal" :in-theory (enable isigf)))
  :rule-classes (:rewrite
                 (:forward-chaining :trigger-terms ((isigf x p)))
                 ))

(defthm iexpof-bvecp
  (implies (case-split (integerp q))
           (bvecp (iexpof x p q) q))
  :hints (("goal" :in-theory (enable iexpof))))

(defthm isgnf-bvecp
  (bvecp (isgnf x p q) 1)
  :hints (("goal" :in-theory (enable isgnf))))

;forward-chaining-rules for encoding types

(defthm nencodingp-forward-to-iencodingp
  (implies (nencodingp x p q)
           (iencodingp x p q) )
  :hints (("goal" :in-theory (enable iencodingp nencodingp)))
  :rule-classes (:rewrite :forward-chaining)
  )

(defthm dencodingp-forward-to-iencodingp
  (implies (dencodingp x p q)
           (iencodingp x p q) )
  :hints (("goal" :in-theory (enable iencodingp dencodingp)))
  :rule-classes (:rewrite :forward-chaining)
  )

;needed? t-p?
(defthm not-zero-ddecode
  (implies (and (dencodingp x p q)
                (integerp p)
                (< 1 p)
                (integerp q)
                (< 0 q))
           (not (equal (ddecode x p q) 0)))
  :hints (("goal" :in-theory (enable ddecode dencodingp))))

(defthm not-zero-ndecode
  (implies (and ;(nencodingp x p q)
                (rationalp x)
                (>= x 0)
                (integerp p)
                (< 1 p)
                (integerp q)
                (< 0 q))
           (not (equal (ndecode x p q) 0)))
  :hints (("goal" :in-theory (enable ndecode nencodingp))))

;move
;BOZO make a negative-syntaxp version
;or just enable sgn?
(defthm sgn-minus-dist
  (implies (and (acl2-numberp x)
                (acl2-numberp y))
           (equal (sgn (+ (* -1 x) (* -1 y)))
                  (* -1 (sgn (+ x y)))))
  :hints (("Goal" :in-theory (disable sgn-minus)
          :use (:instance sgn-minus (x (* -1 (+ x y)))))))

(defthm expo-ndecode
  (implies (and (nencodingp x p q)
                (integerp p)
                (> p 1)
                (integerp q)
                (> q 0))
           (equal (expo (ndecode x p q))
                  (- (iexpof x p q) (bias q))))
  :hints (("goal" :in-theory (e/d (ndecode nencodingp
                                           expt-split
                                           expt-minus
                                           isigf
                                           )
                                  ()))))

(defthm sgn-ndecode
  (implies (and ; (nencodingp x p q)
            (rationalp x)
            (>= x 0)
            (integerp p)
            (> p 1)
            (integerp q)
            (> q 0))
           (equal (sgn (ndecode x p q))
                  (if (= (isgnf x p q) 0) 1 -1)))
  :hints (("goal" :in-theory (enable ndecode sgn))))

;remove from :rewrite?
(defthm nencodingp-forward-to-positive-integerp
  (implies (nencodingp x p q)
           (and (integerp x)
                (<= 0 x)))
  :hints (("Goal" :in-theory (enable nencodingp)))
  :rule-classes (:forward-chaining))

(defthm dencodingp-forward-to-positive-integerp
  (implies (dencodingp x p q)
           (and (integerp x)
                (<= 0 x)))
  :hints (("Goal" :in-theory (enable dencodingp)))
  :rule-classes (:forward-chaining))

;BOZO do we even need this?
(defthmd ndecode-rewrite
  (implies (and (rationalp x)
                (integerp p)
                (> p 1)
                (integerp q)
                (> q 0))
           (= (ndecode x p q)
              (* (if (= (isgnf x p q) 0) 1 -1)
                 (* (expt 2 (- (iexpof x p q) (bias q)))
                    (+ 1 (* (isigf x p)
                            (expt 2 (+ 1 (- p)))))))))
  :hints (("Goal" :in-theory (enable ndecode))))

(defthm isigf-upper-bound-linear
  (implies (case-split (integerp p))
           (< (isigf x p) (expt 2 (- p 1) )))
  :rule-classes (:rewrite :linear))

(defthm sig-ndecode
  (implies (and (nencodingp x p q) ;gen?
                (integerp p)
                (> p 1)
                (integerp q)
                (> q 0))
           (equal (sig (ndecode x p q))
                  (+ 1 (/ (isigf x p) (expt 2 (- p 1))))
                  ))
  :otf-flg t
  :hints (("goal" :use (:instance expo-unique (x (+ 1
                                                    (* 2 (/ (EXPT 2 P))
                                                       (BITS X (+ -2 P) 0))))
                                  (n 0))
           :in-theory (set-difference-theories
                       (enable ndecode
                               expt-split
                               expt-minus
                               isigf iexpof ; isgnf
                               sig
;                                       nencodingp
                               )
                       '( EXPO-UNIQUE-ERIC-2)))))

;instead, just open up sgn?
(defthm sgn-ddecode
  (implies (and (dencodingp x p q)
                (integerp p)
                (> p 1)
                (integerp q)
                (> q 0))
           (equal (sgn (ddecode x p q))
                  (if (= (isgnf x p q) 0) 1 -1)))
  :hints (("Goal" :in-theory (e/d (ddecode dencodingp sgn) ()))))

(defthm sig-ddecode
  (implies (and (dencodingp x p q)
                (integerp p)
                (> p 1)
                (integerp q)
                (> q 0))
           (equal (sig (ddecode x p q))
                  (sig (isigf x p))))
  :hints (("Goal" :in-theory (e/d ( ddecode sgn ) ()))))

(defthm expo-ddecode
  (implies (and (dencodingp x p q)
                (integerp p)
                (> p 1)
                (integerp q)
                (> q 0))
           (equal (expo (ddecode x p q))
                  (+ 2 (- p) (- (bias q)) (expo (isigf x p)))))
  :hints (("Goal" :in-theory (enable ddecode dencodingp ))))

(defthm sgn-idecode
  (implies (and (iencodingp x p q)
                (integerp p)
                (> p 1)
                (integerp q)
                (> q 0))
           (equal (sgn (idecode x p q))
                  (if (= (isgnf x p q) 0) 1 -1)))
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable idecode iencodingp ISGNF NDECODE)
                              '()))))

(defthm sig-idecode
  (implies (and (iencodingp x p q)
                (integerp p)
                (> p 1)
                (integerp q)
                (> q 0))
           (equal (sig (idecode x p q))
                  (cond ((nencodingp x p q)
                         (+ 1 (/ (isigf x p) (expt 2 (- p 1)))))
                        ((dencodingp x p q)
                         (sig (isigf x p))))))
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable idecode iencodingp)
                              '()))))

(defthm expo-idecode
  (implies (and (iencodingp x p q)
                (integerp p)
                (> p 1)
                (integerp q)
                (> q 0))
           (equal (expo (idecode x p q))
                  (cond ((nencodingp x p q)
                         (- (iexpof x p q) (bias q)))
                        ((dencodingp x p q)
                         (+ 2 (- p) (- (bias q)) (expo (isigf x p)))))))
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable idecode iencodingp)
                              '()))))


;move?
(defthm expo-bvecp-upper-bound
  (implies (and (bvecp x n)
                (integerp n)
                (< 0 n))
           (< (expo x) n))
  :hints (("Goal" :in-theory (enable bvecp)
           :use ((:instance expo<= ( n (- n 1))))))
  :rule-classes (:rewrite (:linear :match-free :all)))

(local (in-theory (disable bvecp-exactp))) ;why? efficiency?

;nice lemma?
(local
 (defthm drepp-decode-1
  (IMPLIES (AND (DENCODINGP X P Q)
                (INTEGERP P)
                (< 1 P)
                (INTEGERP Q)
                (< 0 Q))
           (EXACTP (DDECODE X P Q)
                   (+ (* -1 (BIAS Q))
                      (EXPT 2 (1- Q))
                      (EXPO (ISIGF X P)))))
  :hints (("Goal" :in-theory (enable ddecode dencodingp bias)))))

(defthm drepp-ddecode
  (implies (and (dencodingp x p q)
                (integerp p)
                (> p 1)
                (integerp q)
                (> q 0))
           (drepp (ddecode x p q) p q))
  :hints (("Goal" :use drepp-decode-1
           :in-theory (set-difference-theories
                       (enable drepp)
                       '(drepp-decode-1)))))

;BOZO yuck. better expo-shift rules would help here..
(defthm nrepp-ndecode-hack
  (implies (and (nencodingp x p q)
                (integerp p)
                (> p 1)
                (integerp q)
                (> q 0))
           (exactp (ndecode x p q) p))
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable nrepp nencodingp ndecode exactp
                                      a15
                                      ndecode-rewrite
;expt-split
                                      )
                              '(a9 distributivity
                                   )))
          (and stable-under-simplificationp ;yuck?
               '(:in-theory (enable a9 distributivity a15)))))


#|

(defthm nrepp-ndecode-hack
  (implies (and (nencodingp x p q)
                (integerp p)
                (> p 1)
                (integerp q)
                (> q 0))
           (exactp (ndecode x p q) p))
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable nrepp nencodingp ndecode exactp
                                      a15
                                      ndecode-rewrite
                                      expt-split
                                      expt-minus
                                      sig
                                      isigf
                                      isgnf
                                      iexpof
                                      )
                              '(;a9 distributivity
                                a15
                                   )))
          (and stable-under-simplificationp ;yuck?
               '(:in-theory (enable a9 distributivity a15)))))
|#




(defthm nrepp-ndecode
  (implies (and (nencodingp x p q)
                (integerp p)
                (> p 1)
                (integerp q)
                (> q 0))
           (nrepp (ndecode x p q) p q))
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable nrepp nencodingp)
                              '()))))

(defthm irepp-idecode
  (implies (and (iencodingp x p q)
                (integerp p)
                (> p 1)
                (integerp q)
                (> q 0))
           (irepp (idecode x p q) p q))
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable idecode irepp iencodingp)
                              '()))))


(local
 (defthm nencodingp-nencode-2-1
   (IMPLIES (AND (RATIONALP X)
                 (NOT (EQUAL X 0))
                 (EXACTP X P)
                 (INTEGERP P)
                 (<= 1 P)
                 )
            (integerp (+ (* -1 (EXPT 2 (1- P)))
                         (* (SIG X) (EXPT 2 (1- P))))
                      ))
   :hints (("Goal" :in-theory (enable exactp)
            :use ( sig-lower-bound)))))

(local
 (defthm nencodingp-nencode-2
   (IMPLIES (AND (NREPP X P Q)
                 (INTEGERP P)
                 (< 1 P)
                 (INTEGERP Q)
                 (< 0 Q))
            (<= 0 (NENCODE X P Q)))
 :hints (("Goal"  :in-theory (enable nencode nrepp)))))

(local
 (defthm nencodingp-nencode-3
   (IMPLIES (AND (NREPP X P Q)
                 (INTEGERP P)
                 (< 1 P)
                 (INTEGERP Q)
                 (< 0 Q))
            (< (NENCODE X P Q) (EXPT 2 (+ P Q))))
   :hints (("Goal" :in-theory (enable nencode)))))


(local
 (defthm nencodingp-nencode-4
   (IMPLIES (AND (NREPP X P Q)
                 (INTEGERP P)
                 (< 1 P)
                 (INTEGERP Q)
                 (< 0 Q))
            (< 0 (IEXPOF (NENCODE X P Q) P Q)))
   :hints (("Goal"  :in-theory (e/d ( nencode
                                      iexpof
                                      bvecp
                                      nrepp
                                      bits-tail) (sig-lower-bound sig-upper-bound))
            :use (sig-upper-bound sig-lower-bound)))))


(local
 (defthm nencodingp-nencode-5
   (IMPLIES (AND (NREPP X P Q)
                 (INTEGERP P)
                 (< 1 P)
                 (INTEGERP Q)
                 (< 0 Q))
            (< (IEXPOF (NENCODE X P Q) P Q)
               (1- (EXPT 2 Q))))
   :hints (("Goal"  :in-theory (e/d (nrepp nencode iexpof bvecp
                                       bits-tail) (sig-lower-bound sig-upper-bound))
            :use (sig-upper-bound sig-lower-bound)))))

(defthm nencodingp-nencode
  (implies (and (nrepp x p q)
                (integerp p)
                (> p 1)
                (integerp q)
                (> q 0))
           (nencodingp (nencode x p q) p q) )
  :hints (("Goal" :in-theory (enable nencodingp bvecp)))
  :OTF-FLG T)

(local
 (defthm dencodingp-dencode-hack-3
   (implies (and (drepp x p q)
                 (integerp p)
                 (> p 1)
                 (integerp q)
                 (> q 0))
            (equal (* (SIG X)
                      (EXPT 2 (+ -3 P (EXPO X) (EXPT 2 (1- Q)))))
                   (* (abs x) (EXPT 2 (+ -3 P (EXPT 2 (1- Q)))))))
   :hints (("Goal" :in-theory (set-difference-theories
                               (enable drepp sgn)
                               '(fp-rep-collapse abs))
            :use fp-abs))
   :rule-classes nil))


(local (in-theory (disable expt-compare))) ;yuck

(local
 (defthmd dencodingp-dencode-hack-4
   (implies (and (drepp x p q)
                 (integerp p)
                 (> p 1)
                 (integerp q)
                 (> q 0))
            (bvecp (* (SIG X)
                      (EXPT 2 (+ -3 P (EXPO X) (EXPT 2 (1- Q)))))
                   (- p 1)))

   :hints (("Goal" :in-theory (set-difference-theories (enable dencodingp drepp dencode
                                                               iexpof isigf bias exactp
                                                               expt-split
                                                               bvecp)
                                                       '(abs EXPT-COMPARE sig-upper-bound))
            :use (dencodingp-dencode-hack-3
                  sig-upper-bound
                  (:instance expt-weak-monotone
                             (n (+ -3 P (EXPO X) (EXPT 2 (1- Q))))
                             (m (- p 2))))))))

(defthm dencodingp-dencode
  (implies (and (drepp x p q)
                (integerp p)
;                (> p 1)
                (integerp q)
                (> q 0)
                )
           (dencodingp (dencode x p q) p q) )
  :hints (("Goal" :in-theory (e/d (exactp
                                     dencodingp
                                     drepp
                                     dencode
                                     iexpof
                                     isigf
                                     bias
                                     bits-tail

                                     bvecp
                                     bvecp-bits-0
                                     )
                                  (sig-upper-bound
                                   BITS-SHIFT
                                   BITS-SPLIT-AROUND-ZERO))
           :use (sig-upper-bound
                 sig-lower-bound
                 dencodingp-dencode-hack-4
                 (:instance expt-strong-monotone
                            (n (- p 1))
                            (m (+ p q)))
                 (:instance expt-strong-monotone
                            (n (- p 1))
                            (m (+ p q -1)))))))

(defthm drepp-forward-to-rationalp
  (implies (drepp x p q)
           (rationalp x))
  :hints (("Goal" :in-theory (enable drepp)))
  :rule-classes ((:forward-chaining :trigger-terms ((drepp x p q)))))

(defthm drepp-zero-false
  (not (drepp 0 p q))
  :hints (("Goal" :in-theory (enable drepp))))

(defthm iencodingp-iencode
  (implies (and (irepp x p q)
                (integerp p)
                (> p 1)
                (integerp q)
                (> q 0))
           (iencodingp (iencode x p q) p q) )
  :hints (("Goal" :in-theory (enable iencodingp irepp iencode))))

;prove a thm about bvecp of sig-1?
(defthm isigf-nencode-0
  (implies (and (rationalp x)
                (not (equal x 0))
                (exactp x p)
                (integerp p)
                (< 1 p)
                )
           (bvecp (+ (* -1 (expt 2 (1- p)))
                     (* (sig x) (expt 2 (1- p))))
                  (- p 1)))
  :hints (("goal" :in-theory (set-difference-theories
                              (enable bvecp)
                              '(nencodingp-nencode-2-1
                                sig-upper-bound))
           :use (sig-lower-bound sig-upper-bound nencodingp-nencode-2-1)))
  :rule-classes nil)

(defthm isgnf-nencode
  (implies (and (nrepp x p q)
                (integerp p)
                (> p 1)
                (integerp q)
                (> q 0))
           (equal (isgnf (nencode x p q) p q)
                  (if (equal (sgn x) 1) 0 1)))
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable isgnf nencode nrepp bvecp)
                              '(nencodingp-nencode-2-1
                                bitn-bvecp-0
                                sig-upper-bound
                                                        ))
           :use (nencodingp-nencode-2-1
                 sig-lower-bound
                 sig-upper-bound
                 (:instance bitn-bvecp-0 (m 0)
                            (x (+ (BIAS Q) (EXPO X)))
                            (n q))))))

(defthm isgnf-dencode
  (implies (and (drepp x p q)
                (integerp p)
                (> p 1)
                (integerp q)
                (> q 0))
           (equal (isgnf (dencode x p q) p q)
                  (if (= (sgn x) 1) 0 1)))
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable isgnf dencode drepp bvecp bias)
                              '(nencodingp-nencode-2-1 bitn-bvecp-0))
           :use (dencodingp-dencode-hack-4
                 (:instance expt-strong-monotone
                            (n (- p 1))
                            (m (+ p q -1)))
                 (:instance bitn-bvecp-0
                            (m q)
                            (x (* (SIG X)
                                  (EXPT 2 (+ -3 P (EXPO X) (EXPT 2 (1- Q))))))
                            (n (- p 1)))))))

(defthm isgnf-iencode
  (implies (and (irepp x p q)
                (integerp p)
                (> p 1)
                (integerp q)
                (> q 0))
           (equal (isgnf (iencode x p q) p q)
                  (if (equal (sgn x) 1) 0 1)))

  :hints (("Goal" :in-theory (enable irepp iencode))))

(defthm isigf-nencode-1
  (implies (and (nrepp x p q)
                (integerp p)
                (> p 1)
                (integerp q)
                (> q 0))
           (bvecp (+ (* -2 (EXPT 2 (+ -2 P)))
                     (* 2 (SIG X) (EXPT 2 (+ -2 P)))) (- p 1)   ))
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable isigf nencode nrepp bvecp expt-split)
                              '())
           :use isigf-nencode-0))
  :rule-classes nil)

(defthm isigf-nencode
  (implies (and (nrepp x p q)
                (integerp p)
                (> p 1)
                (integerp q)
                (> q 0))
           (equal (isigf (nencode x p q) p)
                  (* (- (sig x) 1) (expt 2 (- p 1)))))
  :hints (("Goal" :in-theory (e/d (isigf nencode nrepp expt-split bvecp bias bits-tail)
                                  (bits-shift
                                   BITS-SUM-DROP-IRRELEVANT-TERM-1-OF-2
                                   BITS-SHIFT-BY-CONSTANT-POWER-OF-2))
           :use (isigf-nencode-1
                 ))))

(defthm isigf-dencode
  (implies (and (drepp x p q)
                (integerp p)
                (> p 1)
                (integerp q)
                (> q 0))
           (equal (isigf (dencode x p q) p)
                  (* (sig x) (expt 2 (+ -2 p (expo x) (bias q))))))

  :hints (("Goal" :in-theory (set-difference-theories
                              (enable isigf dencode drepp bias bits-tail lead-bit-0)
                              '(BITS-SHIFT))
           :use dencodingp-dencode-hack-4)))

(defthm iexpof-nencode
  (implies (and (nrepp x p q)
                (integerp p)
                (> p 1)
                (integerp q)
                (> q 0))
           (equal (iexpof (nencode x p q) p q)
                  (+ (expo x) (bias q))))
  :hints (("Goal" :in-theory (enable iexpof nencode nrepp bvecp
                                     bits-tail)
           :use (isigf-nencode-1))))

(defthm iexpof-dencode
  (implies (and (drepp x p q)
                (integerp p)
                (> p 1)
                (integerp q)
                (> q 0))
           (equal (iexpof (dencode x p q) p q)
                  0))
  :otf-flg t
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable iexpof dencode drepp bias
                                      bvecp-bits-0
                                      )
                              '())
           :use (dencodingp-dencode-hack-4))))

(defthm ndecode-nencode
  (implies (and (nrepp x p q)
                (integerp p)
                (> p 1)
                (integerp q)
                (> q 0))
           (equal (ndecode (nencode x p q) p q)
                  x))
  :hints (("Goal" :in-theory (enable nrepp ndecode sgn expt-split expt-minus))))

(defthm ddecode-dencode
  (implies (and (drepp x p q)
                (integerp p)
                (> p 1)
                (integerp q)
                (> q 0))
           (equal (ddecode (dencode x p q) p q)
                  x))
  :hints (("Goal" :in-theory (enable drepp ddecode sgn expt-split expt-minus))))

(defthm not-both-nrepp-and-drepp
  (implies (irepp x p q)
	   (iff (nrepp x p q)
		(not (drepp x p q))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable irepp nrepp drepp))))

(defthm idecode-iencode
  (implies (and (irepp x p q)
                (integerp p)
                (> p 1)
                (integerp q)
                (> q 0))
           (equal
            (idecode (iencode x p q) p q)
            x))
  :hints (("Goal" :in-theory (enable irepp idecode iencode idecode)
		  :use (dencodingp-dencode
			not-both-nrepp-and-drepp))))

(defthm nencode-ndecode
  (implies (and (nencodingp x p q)
                (integerp p)
                (> p 1)
                (integerp q)
                (> q 0))
           (equal (nencode (ndecode x p q) p q)
                  x))
  :hints (("Goal" :in-theory (set-difference-theories
			      (enable nencodingp nencode iexpof isigf isgnf sgn
				      cat lead-bit-0
				      expt-split
				      bits-reduce ;why?
				      )
; Modification by Matt K. for v2-9, due to the change to rewrite-clause that
; avoids using forward-chaining facts derived from a literal that has been
; rewritten: use sgn-ndecode explicitly (see :use hint below) and hence disable
; it here.

			      '(sgn-ndecode))
           :use (sgn-ndecode
                 (:instance bits-plus-bits
                            (m 0)
                            (p (- p 1))
                            (n (+ -2 p q)))
                 (:instance bitn-plus-bits
                            (n (+ p q -1))
                            (m 0))
                 (:instance bitn-0-1 (x x) (n (+ -1 p q)))))))

(defthm dencode-ddecode
  (implies (and (dencodingp x p q)
                (integerp p)
                (> p 1)
                (integerp q)
                (> q 0))
           (equal (dencode (ddecode x p q) p q)
                  x))
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable dencodingp dencode iexpof isigf isgnf sgn
                                      cat lead-bit-0 expt-split expt-minus)
                              '())
           :use ((:instance bits-plus-bits
                            (m 0)
                            (p (- p 1))
                            (n (+ -2 p q)))
                 (:instance fp-rep (x (BITS X (+ -2 P) 0)))
                 (:instance bitn-plus-bits
                            (n (+ p q -1))
                            (m 0))
                 (:instance bitn-0-1 (x x) (n (+ -1 p q)))
                 ))))

(defthm iencode-idecode
  (implies (and (iencodingp x p q)
                (integerp p)
                (> p 1)
                (integerp q)
                (> q 0))
           (equal (iencode (idecode x p q) p q)
                  x))
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable irepp idecode iencode idecode IENCODINGP)
                              '())
		  :use (
			(:instance not-both-nrepp-and-drepp (x (ddecode x p q)))))))

(defthm nrepp-bvecp-sig
  (implies (and (natp p)
                (> p 0)
                (nrepp x p q))
           (bvecp (* (1- (sig x)) (expt 2 (1- p)))
                  (1- p)))
  :rule-classes ()
  :hints (("Goal" :in-theory (e/d (nrepp exactp bvecp) ()))))

; Matt K., after v4-2:
; Commenting out the following rule, which rewrites a term to itself!
#||
(defthm nencode-nencode
  (implies (and (nrepp x p q)
                (integerp p)
                (> p 0)
                (integerp q)
                (> q 0))
           (equal (nencode x p q) (nencode x p q)))
  :hints (("Goal" :use (nrepp-bvecp-sig)
		  :in-theory (enable nencode nencode bits-tail nrepp bvecp))))
||#

(defthm drepp-bvecp-sig
    (implies (and (integerp p)
		  (natp q)
		  (> q 0)
		  (drepp x p q))
	     (bvecp (* (sig x) (expt 2 (+ -2 p (expo x) (bias q))))
		    (1- p)))
  :rule-classes ()
  :hints (("Goal" :in-theory (e/d (bias drepp exactp bvecp expt-split) (sig-upper-bound
                                                                        ))
		  :use (;sig-lower-bound
			sig-upper-bound
			(:instance expt-weak-monotone (n (+ -3 P (EXPO X) (EXPT 2 (+ -1 Q)))) (m (- p 2)))))))




