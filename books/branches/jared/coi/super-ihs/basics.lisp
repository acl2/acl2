#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#
(in-package "ACL2")

;why does basics include all this stuff?
;(include-book "ihs/ihs-definitions" :dir :system)
;(include-book "ihs/ihs-lemmas" :dir :system)
(include-book "inductions")
(include-book "evenp")
(include-book "bit-functions")
(include-book "from-rtl")
(include-book "arithmetic")
(include-book "loghead")
(include-book "logext")
(include-book "logcar")
(include-book "ash")


(in-theory (enable natp))

;since UNSIGNED-BYTE-P-FORWARD-TO-NONNEGATIVE-INTEGERP is built into acl2 and we have acl2::unsigned-byte-p-forward-to-expt-bound:
(in-theory (disable ACL2::UNSIGNED-BYTE-P-FORWARD)) 

(local (in-theory (enable FALSIFY-UNSIGNED-BYTE-P))) 

;(include-book "ihs/@logops" :dir :system) ;This had the effect of disabling all the user's stuff when he included @logops book via super-ihs !

;bzo The include-book of @logops above (now commented out) had some majors effects on the theory (it disabled almost everything!); the next two events mimic those effects.  We should clean this up at some point.



(in-theory (disable 
;            (:REWRITE ZP-OPEN)
 ;           (:REWRITE ZIP-OPEN)

   ;         (:DEFINITION NTHCDR)
  ;          (:DEFINITION LAST)

 ;           (:DEFINITION THE-CHECK) ; through ACL2 6.1, the-error
;            (:DEFINITION ZPF)
;;             (:DEFINITION LOGTEST)
;;             (:DEFINITION SUBSEQ-LIST)
;;             (:DEFINITION SUBSEQ)
;;             (:DEFINITION BUTLAST)
;;             (:REWRITE LEN-UPDATE-NTH)
;;             (:DEFINITION PAIRLIS2)
;;             (:DEFINITION DUPLICATES)
;;             (:DEFINITION ADD-TO-SET-EQUAL)
;;             (:DEFINITION INTERSECTION-EQ)
;;             (:REWRITE RIGHT-CANCELLATION-FOR-+)
;;             (:REWRITE INVERSE-OF-+-AS=0)
;;             (:REWRITE RIGHT-CANCELLATION-FOR-*)
;;             (:REWRITE EQUAL-*-X-Y-X)
;;             (:FORWARD-CHAINING NUMERATOR-NONZERO-FORWARD)
;;             (:REWRITE TIMES-ZERO)
;;             (:REWRITE /R-WHEN-ABS-NUMERATOR=1)
;;             (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-RATIONALP)
;;             (:GENERALIZE EXPT-TYPE-PRESCRIPTION-RATIONALP)
;;             (:REWRITE LEFT-NULLITY-OF-1-FOR-EXPT)
;;             (:REWRITE EXPONENTS-ADD-FOR-NONNEG-EXPONENTS)
;;             (:REWRITE DISTRIBUTIVITY-OF-EXPT-OVER-*)
;;             (:REWRITE EXPT-1)
;;             (:REWRITE EQUAL-CONSTANT-+)
;;             (:REWRITE APPEND-PRESERVES-RATIONAL-LISTP)
;;             (:FORWARD-CHAINING RATIONALP-CAR-RATIONAL-LISTP)
;;             (:REWRITE <-*-RIGHT-CANCEL)
;;             (:REWRITE /-INVERTS-ORDER-1)
;;             (:REWRITE <-*-0)
;;             (:REWRITE |0-<-*|)
;;             (:REWRITE /-INVERTS-ORDER-2)
;;             (:REWRITE /-INVERTS-WEAK-ORDER)
;;             (:REWRITE *-PRESERVES->=-FOR-NONNEGATIVES)
;;             (:REWRITE *-PRESERVES->-FOR-NONNEGATIVES-1)
;;             (:REWRITE X*Y>1-POSITIVE-LEMMA)
;;             (:LINEAR X*Y>1-POSITIVE)
;;             (:REWRITE X*Y>1-POSITIVE)
;;             (:REWRITE <-*-X-Y-Y)
;;             (:REWRITE <-Y-*-X-Y)
;            (:REWRITE <-0-+-NEGATIVE-1)
;            (:REWRITE <-0-+-NEGATIVE-2)
;            (:REWRITE <-+-NEGATIVE-0-1)
;           (:REWRITE <-+-NEGATIVE-0-2)
;dsh  Removed for ACL2 2.9.2, where NATP-CR and POSP-CR no longer exist.  
;     This change doesn't appear to affect proofs under ACL2 2.9.
;            (:COMPOUND-RECOGNIZER NATP-CR)
;            (:COMPOUND-RECOGNIZER POSP-CR)
;;             (:FORWARD-CHAINING NATP-FC-1)
;;             (:FORWARD-CHAINING NATP-FC-2)
;;             (:FORWARD-CHAINING POSP-FC-1)
;;             (:FORWARD-CHAINING POSP-FC-2)
;;             (:REWRITE |(natp a)  <=>  (posp a+1)|)
;;             (:REWRITE POSP-NATP)
;;             (:REWRITE NATP-*)
;;             (:REWRITE NATP-POSP)
;;             (:REWRITE NATP-POSP--1)
;;             (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|)
;;             (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|)
;;             (:REWRITE DENOMINATOR-UNARY-MINUS)
;;             (:LINEAR NUMERATOR-GOES-DOWN-BY-INTEGER-DIVISION
;;                      . 1)
;;             (:LINEAR NUMERATOR-GOES-DOWN-BY-INTEGER-DIVISION
;;                      . 2)
;;             (:REWRITE DENOMINATOR-PLUS)
;;             (:REWRITE NUMERATOR-/X)
            ))

(in-theory (enable
 ;           (:DEFINITION ZP) trying..
  ;          (:DEFINITION ZIP)
;            (:DEFINITION NATP)
 ;           (:DEFINITION POSP)
  ;          (:INDUCTION STANDARD-CHAR-LISTP)
   ;         (:INDUCTION STRING<-L)
    ;        (:EXECUTABLE-COUNTERPART ABORT!)
     ;       (:INDUCTION LEXORDER)
            ))

(defthm lognot-zip
  (implies (zip a)
           (equal (lognot a) -1))
  :hints (("goal" :in-theory (enable lognot ifix))))

;consider disabling these for the user? since they might be expensive. probably okay?
(defthm logior-when-i-is-not-an-integerp
  (implies (not (integerp i))
           (equal (logior i j)
                  (ifix j)))
  :hints (("goal" :in-theory (enable logior ifix))))

(defthm logior-when-j-is-not-an-integerp
  (implies (not (integerp j))
           (equal (logior i j)
                  (ifix i)))
  :hints (("goal" :in-theory (enable logior ifix))))

(defthm logior*-better
  (equal (logior i j)
         (logcons (b-ior (logcar i) (logcar j))
                  (logior (logcdr i) (logcdr j))))
  :hints (("Goal" :use (:instance logior*)))
  :rule-classes
  ((:definition :clique (binary-logior)
                :controller-alist
                ((binary-logior t t)))))

;(in-theory (disable LOGIOR*)) ;ours is better

(defthm logand-when-i-is-not-an-integerp
  (implies (not (integerp i))
           (equal (logand i j)
                  0))
  :hints (("goal" :in-theory (enable logand))))

(defthm logand-when-j-is-not-an-integerp
  (implies (not (integerp j))
           (equal (logand i j)
                  0))
  :hints (("goal" :in-theory (enable logand))))

(defthm logand*-better
  (equal (logand i j)
         (logcons (b-and (logcar i) (logcar j))
                  (logand (logcdr i) (logcdr j))))
  :hints (("Goal" :use (:instance logand*)))
  :rule-classes
  ((:definition :clique (binary-logand)
                :controller-alist ((binary-logand t t)))))

(defthm lognot*-better
  (equal (lognot i)
         (logcons (b-not (logcar i))
                  (lognot (logcdr i))))
  :rule-classes ((:definition :clique (lognot)
                              :controller-alist ((lognot t))))
  :hints (("Goal" :use (:instance lognot*))))

(defthm logxor-when-i-is-not-an-integerp
  (implies (not (integerp i))
           (equal (logxor i j)
                  (ifix j)))
  :hints (("goal" :in-theory (enable logxor logeqv logorc1))))

(defthm logxor-when-j-is-not-an-integerp
  (implies (not (integerp j))
           (equal (logxor i j)
                  (ifix i)))
  :hints (("goal" :in-theory (enable logxor logeqv logorc1))))

(defthm logxor*-better
  (equal (logxor i j)
         (logcons (b-xor (logcar i) (logcar j))
                  (logxor (logcdr i) (logcdr j))))
  :rule-classes
  ((:definition :clique (binary-logxor)
                :controller-alist ((binary-logxor t t))))
  :hints (("Goal" :use (:instance logxor*))))


(defthm logbitp*-better
  (implies (and (integerp pos)
                (<= 0 pos)
                )
           (equal (logbitp pos i)
                  (cond ((equal pos 0) (equal (logcar i) 1))
                        (t (logbitp (1- pos) (logcdr i))))))
  :rule-classes
  ((:definition :clique (logbitp)
                :controller-alist ((logbitp t t))))
  :hints (("Goal" :use (:instance logbitp*))))


;;add this stuff into the recursive definitions theory:



(deftheory LRDT
  (set-difference-theories
   (union-theories (theory 'LOGOPS-RECURSIVE-DEFINITIONS-THEORY)
                  '(+-r +-induction
                        lognotr lognot-induction
                        logbinr logand-induction logior-induction logxor-induction
                        loglistr loglist-fwd-r loghead-induction logtail-induction
                        ubp-induction sbp-induction 
                        logbitp-induction logext-induction
                        loglist-+-induction
                        #|logappr|# logapp-induction
                        logmaskpr logmaskp-induction
                        loglist-bwd-r ash-induction
                        loglistr-- loglist-fwd-r-- loglist-bwd-r--
                        loglist-ashr loglist-ash-induction
                        logior*-better
                        logand*-better
                        loghead*-better
                        logext*-better
                        lognot*-better
                        logxor*-better
                        logbitp*-better
                        ))
   '(lognot*
     logxor*
     logior*
     logand*
     logext*
     loghead*
     logbitp*
     )))
                    
(in-theory (disable LRDT))

(in-theory (disable unsigned-byte-p-plus)) ;; an unneeded rule, that slows things down

;redo? trying disabled
(defthmd equal-b-not-logcar
  (and (equal (equal (b-not (logcar x)) 0)
              (equal (logcar x) 1))
       (equal (equal (b-not (logcar x)) 1)
              (equal (logcar x) 0)))
  :hints (("goal" :in-theory (enable b-not logcar))))



