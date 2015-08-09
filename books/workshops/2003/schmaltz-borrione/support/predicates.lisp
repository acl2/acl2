;------------------------------------------------------------------------
;
; File : predicates.lisp
; Author : Julien Schmaltz
; April 2003
; TIMA-VDS
; Grenoble, France
;
;------------------------------------------------------------------------


(in-package "ACL2")

; ACL2 books on lists
(include-book "../../../../data-structures/list-defuns")

(include-book "../../../../data-structures/list-defthms")


;------------------------------------------------------------------------------
;
;
; Some predicates used in modeling and proofs
;
;
;------------------------------------------------------------------------------
;
; recognizer of a list of 0
;
;
(defun no_requestp (REQ)
  (cond ((endp REQ) t)
	((equal (car REQ) 1) nil)
	(t (and (equal (car REQ) 0)
		(no_requestp (cdr REQ))))))

; if no_requestp then the car of L is 0

(defthm car_no_requestp
  (implies (and (no_requestp L) (consp L))
	   (equal (car L) 0)))

; if no_requestp then L is a list of 0

(defthm no_requestp_th1
  (implies (and (no_requestp L) (consp L) (< i (len L)))
	   (equal (nth i L) 0)))
; prove 0.07

(defthm no_requestp_th2
  (implies (no_requestp L)
	   (not (equal (nth i L) 1))))
; Prove 0.03

(defthm not_no_requestp_cdr_=>_not_no_requestp_L
  (implies (not (no_requestp (cdr L)))
	   (not (no_requestp L))))

(in-theory (disable no_requestp))

;------------------------------------------------------------------------------
; recognizer of a matrix with no requests

(defun no_requestp_matrix (M)
  (cond ((endp M) t)
	((no_requestp (car M))
	 (no_requestp_matrix (cdr M)))
	(t
	 nil)))

;------------------------------------------------------------------------------

; recognizer of a list of 1 and 0, i.e. a bit vector

(defun list_of_1_and_0 (L)
  (if (endp (cdr L))
      (or (equal (car L) 0) (equal (car L) 1))
      (and (or (equal (car L) 0) (equal (car L) 1))
	   (list_of_1_and_0 (cdr L)))))

(defthm list_of_1_and_0_cdr
  (implies (and (list_of_1_and_0 L) (consp (cdr L)))
	   (list_of_1_and_0 (cdr L))))

(defthm list_REQ_=>_list_first
  (implies (and (list_of_1_and_0 L) (not (zp n)))
           (list_of_1_and_0 (firstn n L))))
; Prove 0.08

;------------------------------------------------------------------------------

; function that returns the last elements af a list form the n + 1

(defun lastn (n L)
  (cond ((endp L) nil)
        ((zp n) L)
	(t
	 (lastn (1- n) (cdr L)))))

(defthm len_lastn
  (implies (and (integerp n) (< 0 n) (consp L) (< n (len L)))
           (equal (len (lastn n L)) (- (len L) n))))
; Prove 0.09

(defthm lastn_no_requestp
  (implies (and (no_requestp L) (consp L))
       (and (no_requestp (firstn n L))
            (no_requestp (lastn n L))))
  :hints (("GOAL" :in-theory (enable no_requestp))))
; Prove 0.22

(defthm len_firstn_2
  (<= (len (firstn n L)) (len L)))
; Prove 0.01

(in-theory (disable lastn))
;------------------------------------------------------------------------------

; function that returns the position of the first '1' in the list L

(defun find_next_1 (L)
  (cond ((endp L) 0)
        ((equal (car L) 1)
         0)
        (t
         (+ 1 (find_next_1 (cdr L))))))

; FIND_NEXT_ONE < (LEN L)

(defthm find_next_1_<_len_L
  (implies (and (not (no_requestp L)) (list_of_1_and_0 L))
           (< (find_next_1 L) (len L)))
  :hints (("GOAL" :in-theory (enable no_requestp))))
; Prove 0.11

(in-theory (disable find_next_1))
;------------------------------------------------------------------------------

; recognizer of a list composed of list with the same length

(defun uniform_listp (L)
  (cond ((endp (cdr L)) t)
	((not (equal (len (car L)) (len (cadr L)))) nil)
	(t
	 (uniform_listp (cdr L)))))

; if uniform_list len (len (car l)) = (len (cadr L))

(defthm l_uni_=>_len_car_=_len_cadr
  (implies (and (consp (cdr L)) (uniform_listp L))
	   (equal (len (car L)) (len (cadr l)))))


;--------------------------------------------------------------------------------
;Summary
;Form:  (CERTIFY-BOOK "predicates" ...)
;Rules: NIL
;Warnings:  Guards
;Time:  2.14 seconds (prove: 0.52, print: 0.23, other: 1.39)
; "/h3/schmaltz/These/ACL2_Workshop/2003/Support/predicates.lisp"
