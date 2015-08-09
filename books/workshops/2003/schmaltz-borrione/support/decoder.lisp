;------------------------------------------------------------------------
;
; File : decoder.lisp
; Author : Julien Schmaltz
;
; April 2003
; TIMA-VDS
; Grenoble, France
;
;------------------------------------------------------------------------

(in-package "ACL2")

; book on arithmetics
(include-book "../../../../arithmetic/top")

(include-book "../../../../arithmetic-2/floor-mod/floor-mod")

;-------------------------------------------------------------------------
;
;
;                         SELECT
;
;
;------------------------------------------------------------------------

; function that builds a list of bits where
; the first element is the least significant bit
; the bit at position sel is '1' and others are '0'

(defun  select (Card_S SEL)
  (cond ((not (integerp Card_S)) nil)
	((<= Card_S 0) nil)
	((equal SEL 0)
	 (cons 1 (select (1- Card_S) (1- SEL))))
	(t
	 (cons 0 (select (1- Card_S) (1- SEL))))))

;----------------------------------------------------------------------------
;
;
;                     LEMMAS ON SELECT
;
;----------------------------------------------------------------------------


; 1- select returns a true-list
; (ACL2 finds that when accepting the definition)

;(defthm true-listp_select
;  (true-listp (select a b)))

; 2- the length of the list is equal to Card_S

(defthm len_select
  (implies (and (integerp Card_S) (<= 0 Card_S))
	   (equal (len (select Card_S sel)) Card_S)))
; Prove 0.03

; 3- select returns a cons-pair when Card_S> 0

(defthm consp_select
  (implies (and (integerp Card_S) (< 0 Card_S))
	   (consp (select Card_S sel)))
  :hints (("GOAL" :expand (select 1 sel))))
; Prove 0.03

; 4- if (integerp Card_S) and  (< 0 Card_S) then (car (select Card_S0)) is 1
; this lemma is needed to ease the proof of the next theorem

(defthm car_select_=_1
  (implies (and (integerp Card_S) (< 0 Card_S))
	   (equal (car (select Card_S 0)) 1)))
; Prove 0.01

; 5- the i'th bit of (select Card_S i) is 1
; That proofs that the selection of the slave is correct
; SLAVE CHOICE CORRECTNESS
(defthm ith_select_=_1
  (implies (and (integerp i) (integerp Card_S)
		(>= i 0) (> Card_S i))
	   (equal (nth i (select Card_S i )) 1)))
; Prove 0.06

; 6- if p is not equal to i, then (car (select a i)) is 0
; lemma needed for the proof of the UNICITY theorem

(defthm car_select_=_0
 (implies (and (integerp Card_S) (< 0 Card_S) (not (equal i 0)))
	  (equal (car (select Card_S i)) 0))
 :hints (("GOAL"
	  :expand (select 1 I))))
; Prove 0.06

; 7- The p'th is 0

; function suggesting the induction scheme for the proof of the UNICITY theorem

(local
 (defun function_hint_th2_select (p Card_S sel)
  (cond ((zp p) 0)
	((and (not (integerp Card_S))
	      (not (integerp sel)))
	 0)
	(t (+ 1 (function_hint_th2_select  (1- p)
					   (1- Card_S)
					   (1- sel))))))
)

; UNIQUENESS OF THE SELECTION
(defthm pth_select_=_0
  (implies (and (integerp p) (integerp Card_S)
		(<= 0 p) (< p Card_S)
		(not (equal p i)))
	   (equal (nth p (select Card_S i)) 0))
  :hints (("GOAL"
	   :induct (function_hint_th2_select p Card_S i))))
; Prove 0.10

(in-theory (disable select))
;-------------------------------------------------------------------------
;
;
;                         DECODER
;
;
;------------------------------------------------------------------------


;--------------------------------------------------------------------------
;
; function modeling the address decoder
; Card_S = number of slaves
; ADDR = Global address of data
; MEM_SIZE = memory size of each unit

; the local address UNADDR is equal to ADDR mod MEM_SIZE
; the slave number i that possed the datum at ADDR is HADDR/MEM_SIZE

(defun decoder (MEM_SIZE Card_S  HADDR)
  (select Card_S (floor HADDR MEM_SIZE)))

; when accepting the function ACL2 finds that this function returns a true-list

;-------------------------------------------------------------------------
;
;            PREUVE DE AHB_DECODER
;
;------------------------------------------------------------------------


; lemma stating that (floor ADDR MEM_SIZE) < Card_S
; if ADDR = Card_S * MEM_SIZE
; lemma needed for the proof of the next theorem

(defthm floor_<_Card_S
  (implies (and (< HADDR (* Card_S MEM_SIZE))
		(integerp HADDR) (integerp MEM_SIZE)
		(< 0 MEM_SIZE) (< 0 Card_S) (<= 0 ADDR)
		(integerp Card_S))
	   (< (floor HADDR MEM_SIZE) Card_S))
 :hints (("GOAL"   :in-theory (disable floor COMMUTATIVITY-OF-* FLOOR-MOD-ELIM
			        DISTRIBUTIVITY-OF-/-OVER-*
                                FUNCTIONAL-SELF-INVERSION-OF-/))))
; Prove 1.70

; decoder returns 1

(defthm decoder_nth_1
  (implies (and (< HADDR (* Card_S MEM_SIZE))
		(integerp HADDR) (integerp MEM_SIZE)
		(< 0 MEM_SIZE) (< 0 Card_S) (<= 0 HADDR)
		(integerp Card_S))
	   (equal (nth  (floor HADDR MEM_SIZE)
			(decoder MEM_SIZE Card_S HADDR)) 1))
  :hints (("GOAL"
	   :in-theory (disable floor ))))
; Prove 0.11

; decoder returns 0

(defthm decoder_nth_0
  (implies (and (integerp p) (integerp Card_S)
		(<= 0 p) (< p Card_S)
		(not (equal p (floor HADDR MEM_SIZE))))
	   (equal (nth p (decoder MEM_SIZE Card_S HADDR)) 0))
  :hints (("GOAL"  :in-theory (disable floor))))
; Prove 0.02


; DECODER returns a true-list
; (already found by ACL2)
;(defthm true-listp_DECODER
;  (true-listp (DECODER MEM_SIZE Card_S ADDR)))

; the length of DECODER is its second operand

(defthm len_DECODER
  (implies (and (integerp Card_S) (<= 0 Card_S))
	   (equal (len (DECODER MEM_SIZE Card_S HADDR)) Card_S)))

; DECODER is a conspair

(defthm consp_DECODER
  (implies (and (integerp Card_S) (< 0 Card_S))
	   (consp (DECODER MEM_SIZE Card_S HADDR))))


(in-theory (disable DECODER))

;------------------------------------------------------------------------

;Summary
;Form:  (CERTIFY-BOOK "decoder" ...)
;Rules: NIL
;Warnings:  Guards and Non-rec
;Time:  7.41 seconds (prove: 2.48, print: 0.24, other: 4.69)
; "/h3/schmaltz/These/ACL2_Workshop/2003/Support/decoder.lisp"
