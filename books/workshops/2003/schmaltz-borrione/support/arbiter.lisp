;------------------------------------------------------------------------
;
; File : arbiter.lisp
; Author : Julien Schmaltz
; April 2003
; TIMA-VDS
; Grenoble, France
;
;------------------------------------------------------------------------


(in-package "ACL2")

; my little book on inequalities
(include-book "inequalities")

; the book on decoder and select
(include-book "decoder")

; my book with the needed predicates
(include-book "predicates")

;--------------------------------------------------------------------------

; Bus Arbitration Modeling


;------------------------------------------------------------------------------
;
;                     first step of the algorithm
;
;-----------------------------------------------------------------------------

; function that returns the number of the first line containing at least one
; request or 0

(defun stage_P (L)
  (cond ((endp L) 0)
	((no_requestp_matrix L) 0)
	((not (no_requestp (car L))) 0)
	(t
	 (+ 1 (stage_P (cdr L))))))

; ACL2 finds that the result is a positive integer

;------------------------------------------------------------------------------

;                        Verification of this step

;------------------------------------------------------------------------------


; this step is correct if:


; stage_P returns an integer

;(defthm integerp_stage_P
;  (integerp (stage_P L)))
; proven during definition

; stage_P returns a positive

;(defthm stage_P_>=0
;  (<= 0 (stage_P L)))

; stage number <= master number - 1

(defthm  stage_p_<=_len_L-1
  (implies (and (consp L) (not (no_requestp_matrix L)))
	   (<= (stage_P L) (- (len L) 1))))
; Prove 0.05

; or stage number < master number

(defthm stage_p_<_len_L
  (implies (and (consp L) (not (no_requestp_matrix L)))
	   (< (stage_P L) (len L))))
; Prove 0.03

; any line before the chosen one RLINE contains no pending request

(defthm prior_scheme
  (implies (and (equal (stage_P L) i)
                (< j i) (<= 0 j))
	   (no_requestp (nth j L)))
  :rule-classes ((:rewrite :match-free :all)))
; Prove 0.08

; A chosen stage contains at least one request

(defthm chosen_stage_not_empty
  (implies (and (equal (stage_P L) i) (not (no_requestp_matrix L)))
	   (not (no_requestp (nth i L)))))
; Prove 0.19

(in-theory (disable stage_P))


;------------------------------------------------------------------------------
;
;                    Second step of the algorithm
;
;-----------------------------------------------------------------------------

; computation of the next requesting master to be granted the bus according to
; a round robin scheme

(defun round_robin (RLINE Last_Granted)
  (cond ((no_requestp RLINE) 0)
        ((no_requestp (lastn (1+ Last_Granted) RLINE))
         (find_next_1 (firstn (1+ Last_Granted) RLINE)))
        (t
         (+ (1+ Last_Granted) (find_next_1 (lastn (1+ Last_Granted) RLINE))))))

; Type-presciption: acl2-numberp

;------------------------------------------------------------------------------

;                        Verification of this step

;------------------------------------------------------------------------------

; round_robin returns an integer if its inputs are integers

(defthm integerp_round_robin
  (implies (integerp Last_Granted) ;(<= 0 Last_Granted))
	   (integerp (round_robin RLINE Last_Granted))))
; Prove 0.01

; if inputs are positive then rounb_robin is positive

(defthm round_robin_>=_0
  (implies (<= 0 Last_Granted)
	   (<= 0 (round_robin RLINE Last_Granted))))
; Prove 0.02

; If RLINE has no request then round_robin returns 0

(defthm no_req_=>_round_robin_=_0
  (implies (no_requestp RLINE)
	   (equal (round_robin RLINE Last_Granted) 0)))

; we prove that round_robin returns an integer less than the length of RLINE

; if the last part of the list L containing at least one request
; contains no request, then the first part of the list contains at least one
; request

(defthm lemma_for_round_robin_<_case_2
  (implies (and (not (no_requestp L)) (no_requestp (lastn n L)))
           (not (no_requestp (firstn n L))))
  :hints (("GOAL" :in-theory (enable no_requestp lastn firstn))))
; Prove 0.32

;(defthm round_robin_<_N_case_1
;  (implies (and (no_requestp RLINE) (equal (len RLINE) N) (consp RLINE))
;           (< (round_robin RLINE Last_Granted) N)))

(defthm lemma1_case_2
  (implies (and (not (no_requestp (firstn n L)))
                (list_of_1_and_0 (firstn n L)))
           (<= (find_next_1 (firstn n L)) (len (firstn n L))))
  :hints (("GOAL" :use (:instance find_next_1_<_len_L (L (firstn n L)))
                  :in-theory (disable find_next_1_<_len_L)))
  :rule-classes ((:rewrite :match-free :all)))
; Prove 0.33

(defthm lemma2_case_2
  (implies (and (<= a b) (< b c))
           (< a c))
  :rule-classes ((:rewrite :match-free :all)))

(defthm lemma3_case_2
  (implies (and (<= 0 n) (< n (len L)))
           (< (len (firstn n L)) (len L))))
; Prove 0.02

(defthm lemma4_case_2
  (implies (and (not (no_requestp (firstn n L)))
                (< n (len L)) (<= 0 n)
                (list_of_1_and_0 (firstn n L)))
           (< (find_next_1 (firstn n L)) (len L)))
  :hints (("GOAL" :use (:instance lemma1_case_2)
                  :do-not-induct t
                  :in-theory (disable len-firstn lemma1_case_2))))
; Prove 0.26

(defthm round_robin_<_N_case_2
  (implies (and (no_requestp (lastn (1+ Last_Granted) RLINE))
                (< (1+ Last_Granted) (len RLINE))
                (not (no_requestp RLINE))
                (list_of_1_and_0 (firstn (1+ Last_Granted) RLINE))
                (< 0 (1+ Last_Granted)))
           (< (round_robin RLINE Last_Granted) (len RLINE)))
  :hints (("GOAL" :do-not-induct t
                  :in-theory (disable firstn))))
; Prove 0.05

(defthm lemma1_case_3
  (implies (and (not (no_requestp (lastn n L)))
                (list_of_1_and_0 (lastn n L)))
           (< (find_next_1 (lastn n L)) (len (lastn n L))))
  :hints (("GOAL" :use (:instance find_next_1_<_len_L (L (lastn n L)))
                  :in-theory (disable find_next_1_<_len_L))))
; subsume but useful
; Prove 0.01

;(defthm lemma2_case_3
;  (implies (and (integerp n) (< 0 n) (< n (len L)) (consp L))
;           (<= (len (lastn n L)) (- (len L) n)))) ; USELESS

;(defthm lemma3_case_3
;  (implies (and (< a b) (<= b c))
;           (< a c))
;  :rule-classes ((:rewrite :match-free :all))) ; USELESS

(defthm lemma4_case_3
  (implies (and (integerp n) (< 0 n) (< n (len L))
                (list_of_1_and_0 (lastn n L))
                (not (no_requestp (lastn n L)))
                (consp L))
           (< (find_next_1 (lastn n L)) (- (len L) n)))
  :hints (("GOAL" :use (:instance lemma1_case_3)
                  :do-not-induct t
                  :in-theory (disable lemma1_case_3))))
; Prove 0.19

(defthm lemma5_case_3
  (implies (and (integerp n) (< 0 n) (< n (len L))
                (list_of_1_and_0 (lastn n L))
                (not (no_requestp (lastn n L)))
                (consp L))
           (< (+ n (find_next_1 (lastn n L))) (len L)))
  :hints (("GOAL" :use (:instance lemma4_case_3)
                  :do-not-induct t
                  :in-theory (disable lemma4_case_3))))
; Prove 0.06

(defthm round_robin_<_N_case_3
  (implies (and (not (no_requestp (lastn (1+ Last_Granted) RLINE)))
                (not (no_requestp RLINE))
                (integerp Last_Granted) (<= 0 Last_Granted)
                (list_of_1_and_0 (lastn (1+ Last_Granted) RLINE))
                (consp (lastn (1+ Last_Granted) RLINE))
                (< (1+ Last_Granted) (len RLINE)))
           (< (round_robin RLINE Last_Granted) (len RLINE)))
  :hints (("GOAL" :use (:instance lemma5_case_3 (n (1+ Last_Granted))
                                                (L RLINE))
                  :do-not-induct t
                  :in-theory (disable lemma5_case_3))))
; Prove 0.06

(defthm list_REQ_=>_list_last
  (implies (and (list_of_1_and_0 L) (consp L)
                (integerp n) (< 0 n) (< n (len L)))
           (list_of_1_and_0 (lastn n L)))
  :hints (("GOAL" :in-theory (enable lastn))))
; Prove 0.80

(defthm round_robin_<_N
  (implies (and (integerp Last_Granted) (consp RLINE) (<= 0 Last_Granted)
                (< (1+ Last_Granted) (len RLINE)) (not (no_requestp RLINE))
		(<= 0 Last_Granted) (list_of_1_and_0 RLINE))
    	   (< (round_robin RLINE Last_Granted) (len RLINE)))
  :hints (("GOAL" :use (:instance round_robin_<_N_case_3)
                  :do-not-induct t
                  :in-theory (disable firstn round_robin_<_N_case_3))))
; Prove 0.24

(defthm round_robin_<=N-1
   (implies (and (integerp Last_Granted) (consp RLINE) (<= 0 Last_Granted)
                (< (1+ Last_Granted) (len RLINE)) (not (no_requestp RLINE))
		(<= 0 Last_Granted) (list_of_1_and_0 RLINE))
    	   (<= (round_robin RLINE Last_Granted) (1- (len RLINE))))
   :hints (("GOAL" :use (:instance round_robin_<_N)
                   :in-theory (disable firstn round_robin_<_N))))
; Prove 0.25

; No_Deadlock

(defthm find_not_equal_last_granted
  (implies (and (not (equal last_granted i)) (equal (nth i L) 1)
                (< i last_granted)
                (integerp last_granted) (integerp i) (<= 0 i))
           (not (equal (find_next_1 L) last_granted)))
  :hints (("GOAL" :in-theory (enable find_next_1)))
  :rule-classes ((:rewrite :match-free :all)))
; Prove 0.24

(defthm lemma1_no_deadlock
  (implies (and (integerp last_granted)
                (integerp i)
                (equal (nth last_granted RLINE) 1)
                (equal (nth i RLINE) 1)
                (list_of_1_and_0 RLINE)
                (<= 0 i)
                (< i (1+ last_granted))
                (not (equal last_granted i)))
           (not (equal (round_robin RLINE Last_Granted) Last_Granted)))
  :hints (("GOAL" :use (:instance find_not_equal_last_granted
                                  (L (firstn (1+ Last_Granted) RLINE)))
                   :in-theory (disable find_not_equal_last_granted firstn)))
  :rule-classes ((:rewrite :match-free :all)))
; prove 0.24

(defthm lemma2_no_deadlock
  (implies (and (integerp i) (integerp n) (< 0 n))
           (implies (and (no_requestp (lastn n L)) (equal (nth i L) 1))
                    (< i n)))
  :hints (("GOAL" :in-theory (enable lastn no_requestp)))
  :rule-classes ((:rewrite :match-free :all))
)
; Prove 0.32

(defthm no_deadlock
  (implies (and (integerp i) (<= 0 i)
                (equal (nth Last_Granted RLINE) 1) (list_of_1_and_0 RLINE)
                (not (equal Last_granted i)))
           (implies (equal (nth i RLINE) 1)
                    (not (equal (round_robin RLINE Last_Granted) Last_Granted))))
  :hints (("GOAL" :use lemma1_no_deadlock
                  :in-theory (disable lemma1_no_deadlock firstn)))
  :rule-classes ((:rewrite :match-free :all))
)

; Prove 0.90

(in-theory (disable round_robin))

;------------------------------------------------------------------------------
;
;                     Third step of the algorithm
;
;-----------------------------------------------------------------------------


; computation of the number of the new granted master

(defun master_num (MREQ N Last_Granted)
  (+ (* (stage_P MREQ) N)
     (round_robin (nth (stage_P MREQ) MREQ) Last_Granted)))

; type-prescription: acl2-numberp

;------------------------------------------------------------------------------

;                        Verification of this step

;------------------------------------------------------------------------------

; master_num returns an integer

(defthm int+int=int
  (implies (and (integerp a) (integerp b))
	   (integerp (+ a b)))) ; not subsume,
; Prove 0.00

(defthm integerp_master_num
  (implies (and (integerp N)
		(integerp last_granted))
	   (integerp (master_num MREQ N last_granted))))
; Prove 0.04

; master_num >= 0

(defthm pos+pos=pos
  (implies (and (<= 0 a) (<= 0 b))
	   (<= 0 (+ a b)))); not subsume

(defthm master_num_>=0
  (implies (and (integerp N) (< 0 N)
		(integerp Last_Granted) (<= 0 Last_Granted))
	   (<= 0 (master_num MREQ N Last_Granted))))
; Prove 0.03

;the default_master (number 0) is chosen when necessary

(defthm default_master_master_num
  (implies (no_requestp_matrix MREQ)
	   (equal (master_num MREQ N Last_Granted) 0))
  :hints (("GOAL" :in-theory (enable stage_P round_robin))))
; Prove 0.24

; the computed number is strictly less than the number of masters
; number of masters = N * P


(defthm len_nth_uni_list
  (implies (and (integerp p) (<= 0 p)
                (< p (len l))
                (uniform_listp l)
                (consp (cdr l)))
           (equal (len (nth p l))
                  (len (car l)))))
; Prove 0.35

(defthm master_num_<_P*N
  (implies (and ;(< 0 (stage_p MREQ))
		(integerp N) (< 0 N)
                (integerp Last_Granted) (<= 0 Last_Granted)
		(integerp P) (equal P (len MREQ))
		(equal (len (car MREQ)) N)
		(consp MREQ)
                (not (no_requestp_matrix MREQ))
                (uniform_listp MREQ)
                (consp (cdr MREQ))
                (< (1+ Last_Granted) N)
                (list_of_1_and_0 (nth (stage_P MREQ) MREQ))
		)
	   (< (master_num MREQ N Last_Granted) (* P N)))
  :hints (("GOAL" :use ((:instance stage_P_<_len_L (L MREQ))
                        (:instance round_robin_<=N-1
                                  (RLINE (nth (stage_P MREQ) MREQ))))
	          :in-theory (e/d ()
                                  (COMMUTATIVITY-OF-* COMMUTATIVITY-OF-+
				      uniform_listp no_requestp_matrix
                                      stage_P_<_len_L
                                      firstn nth
                                      round_robin_<=N-1)))))
; the proof require the inequalities book
; Prove 0.60

(in-theory (disable master_num))

;------------------------------------------------------------------------------
;
;                    Last step of the algorithm
;
;-----------------------------------------------------------------------------

; builds the ouptut vector

(defun arbiter (N P MREQ Last_Granted)
      (select (* N P) (master_num MREQ N Last_Granted)))

;------------------------------------------------------------------------------

;                        Verification de cette etape

;------------------------------------------------------------------------------

; arbiter returns a true-list
; found during definition
;(defthm true-listp_AHB_Arbiter
;  (true-listp (AHB_Arbiter N P MREQ Last_Granted)))

; length of arbiter is the number of masters = N*P

(defthm len_arbiter
  (implies (and (integerp N) (< 0 N) (integerp P) (<= 0 P))
	   (equal (len (arbiter N P MREQ Last_Granted)) (* N P))))
; Prove 0.02

; arbiter is a cons-pair

(defthm consp_arbiter
  (implies (and (integerp N) (< 0 N) (integerp P) (< 0 P))
	   (consp (arbiter N P MREQ Last_Granted))))
; Prove 0.00

; The bit at 1 is the desired one

(defthm nth_arbiter_=_1
  (implies (and (integerp N) (< 0 N)
		(integerp Last_Granted) (<= 0 Last_granted)
                (integerp P)
		(equal P (len MREQ))
		(equal (len (car MREQ)) N)
                (not (no_requestp_matrix MREQ))
                (uniform_listp MREQ)
                (< (1+ Last_granted) N)
                (consp MREQ)
                (consp (cdr MREQ))
                (list_of_1_and_0 (nth (stage_P MREQ) MREQ))
		)
	   (equal (nth (master_num MREQ N Last_granted)
                       (arbiter N P MREQ Last_granted)) 1))
  :hints (("GOAL" :use (:instance master_num_<_P*N)
                  :do-not-induct t
                  :in-theory (disable  master_num_<_P*N
                                       DISTRIBUTIVITY
                                       ))))
; Prove 1.43

; we prove the mutual exlusion, i.e. all other bits are 0

(defthm nth_arbiter_=_0
  (implies (and (integerp N)
		(equal P (len MREQ))
                (integerp i) (<= 0 i) (< i (* P N))
                (not (equal i (master_num MREQ N last_Granted)))
		)
	   (equal (nth i
                       (arbiter N P MREQ Last_granted)) 0)))
; Prove 0.03

(in-theory (disable arbiter))
;------------------------------------------------------------------------------
;Summary
;Form:  (CERTIFY-BOOK "arbiter" ...)
;Rules: NIL
;Warnings:  Guards, Subsume, Non-rec and Compiled file
;Time:  13.76 seconds (prove: 5.47, print: 0.55, other: 7.74)
; "/h3/schmaltz/These/ACL2_Workshop/2003/Support/arbiter.lisp"
