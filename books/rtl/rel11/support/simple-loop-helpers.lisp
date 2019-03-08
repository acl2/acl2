; RTL - A Formal Theory of Register-Transfer Logic and Computer Arithmetic
; Copyright (C) 1995-2013 Advanced Mirco Devices, Inc.
;
; Contact:
;   David Russinoff
;   1106 W 9th St., Austin, TX 78703
;   http://www.russsinoff.com/
;
; See license file books/rtl/rel11/license.txt.
;
; Author: David M. Russinoff (david@russinoff.com)

(in-package "RTL")

(include-book "rac")
(local (include-book "bits"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Code from former rtlarr.lisp;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; OK, we add here some properties for typing the records and the values which
;; are stored in the records. This "typing" is pretty generic, but we choose the
;; "bvecp" types for record values because it suits AMD's RTL modeling needs.

(local
(defthm as-aux-is-bounded
  (implies (and (arcdp r)
                (as-aux a v r)
                (acl2::<< e a)
                (acl2::<< e (caar r)))
           (acl2::<< e (caar (as-aux a v r))))))

(defun bv-arrp (x k)
  (declare (xargs :guard (integerp k)))
  (or (null x)
      (and (consp x)
           (consp (car x))
           (bv-arrp (cdr x) k)
           (not (equal (cdar x)
                       (default-get-valu)))
           (bvecp (cdar x) k)
           (or (null (cdr x))
               (acl2::<< (caar x) (caadr x))))))

(local
(defrule bvecp-of-default-get-valu-is-true
  (bvecp (default-get-valu) k)
  :enable bvecp))

(local
(defthm bvecp-of-aifrp-tag-is-false
  (not (bvecp (aifrp-tag) k))))

(local
(defthm bv-arrp-implies-arcdp
  (implies (bv-arrp r k)
           (arcdp r))))

(local
(defthm as-aux-maps-bv-arrp-to-bv-arrp
  (implies (and (bv-arrp r k)
                (bvecp v k))
           (bv-arrp (as-aux a v r) k))))

(local
(defthm ag-aux-maps-bv-arrp-to-bvecp
  (implies (bv-arrp r k)
           (bvecp (ag-aux a r) k))))

(local
(defthm bv-arrp-implies-not-aifrp
  (implies (bv-arrp x k)
           (not (aifrp x)))))

(local
(defthm bv-arrp-acl2->arcd-transfers
  (implies (bv-arrp x k)
           (bv-arrp (acl2->arcd x) k))
  :hints (("Goal" :in-theory (enable acl2->arcd)))))

(local
(defthm bv-arrp-arcd->acl2-transfers
  (implies (bv-arrp r k)
           (bv-arrp (arcd->acl2 r) k))
  :hints (("Goal" :in-theory (enable arcd->acl2)))))

(defrule as-maps-bv-arr-to-bv-arr
  (implies (and (bv-arrp r k)
                (bvecp v k))
           (bv-arrp (as a v r) k))
  :enable as)

(defrule ag-maps-bv-arr-to-bvecp
  (implies (bv-arrp r k)
           (bvecp (ag a r) k))
  :enable ag)

(defun mk-bvarr (r k)
  (declare (xargs :guard (integerp k)))
  (if (bv-arrp r k) r ()))

(defthm mk-bvarr-is-bv-arrp
  (bv-arrp (mk-bvarr r k) k))

(defthm mk-bvarr-identity
  (implies (bv-arrp r k)
           (equal (mk-bvarr r k) r)))

(in-theory (disable bv-arrp mk-bvarr))

;; finally we define some "2D" array accessors.

(defmacro ag2 (a b r)
  `(ag (cons ,a ,b) ,r))

(defmacro as2 (a b v r)
  `(as (cons ,a ,b) ,v ,r))


; Begin events added March 2005 when it was discovered that they are in
; ../lib/rtlarr.lisp but not in this file.

(defun positive-integer-listp (l)
  (declare (xargs :guard t))
  (cond ((atom l)
         (equal l nil))
        (t (and (integerp (car l))
                (< 0 (car l))
                (positive-integer-listp (cdr l))))))

(defmacro arr0 (&rest dims)
  (declare (ignore dims)
           (xargs :guard (positive-integer-listp dims)))
  nil)

;;Functions representing bit vectors of determined length but undetermined value:

(encapsulate
 ((reset2 (key size) t))
 (local (defun reset2 (key size) (declare (ignore key size)) nil))
 (defthm bv-arrp-reset2
   (bv-arrp (reset2 key size) size)
   :hints
   (("goal" :in-theory (enable bv-arrp)))
   ))

(encapsulate
 ((unknown2 (key size n) t))
 (local (defun unknown2 (key size n) (declare (ignore key size n)) nil))
 (defthm bv-arrp-unknown2
   (bv-arrp (unknown2 key size n) size)
   :hints
   (("goal" :in-theory (enable bv-arrp)))
   ))

;BOZO where in lib/ should this go?
(defthm bv-arrp-if1
  (equal (bv-arrp (if1 x y z) n)
         (if1 x (bv-arrp y n) (bv-arrp z n))))

; End events added March 2005 when it was discovered that they are in
; ../lib/rtlarr.lisp but not in this file.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Other helpful stuff;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(DEFCONST *EXPT-2-32*
  (EXPT 2 32))

(DEFRULE BITS-31-0
  (IMPLIES (AND (NATP I)
                (< I *EXPT-2-32*))
           (EQUAL (BITS I 31 0)
                  I))
  :ENABLE BVECP
  :USE (:INSTANCE BITS-TAIL
         (X I)
         (I 31)))

(DEFTHM BVECP-BITN
  (BVECP (BITN Y I) 1))

(DEFRULE BITN-SETBITN-NOT-EQUAL

; This holds without needing (CASE-SPLIT (BVECP Y 1)).

  (IMPLIES (AND (NOT (EQUAL N K))
                (CASE-SPLIT (< 0 W))
                (CASE-SPLIT (< N W))
                (CASE-SPLIT (< K W))
                (CASE-SPLIT (<= 0 K))
                (CASE-SPLIT (INTEGERP W))
                (CASE-SPLIT (INTEGERP N))
                (<= 0 N)
                (CASE-SPLIT (INTEGERP K)))
           (EQUAL (BITN (SETBITN X W N Y) K)
                  (BITN X K)))
  :ENABLE (BITN-CAT BITN-BITS))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Generic theory for counting up, non-arrays
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(ENCAPSULATE
 (($$LOOP_0$ADJ (Y+ I) T)
  ($$LOOP_0$HIGH () T))

 (LOCAL
  (DEFUN $$LOOP_0$HIGH () 3))

 (DEFTHM NATP-$$LOOP_0$HIGH
   (AND (INTEGERP ($$LOOP_0$HIGH))
        (<= 0 ($$LOOP_0$HIGH)))
   :RULE-CLASSES :TYPE-PRESCRIPTION)

 (LOCAL
  (DEFUN $$LOOP_0$ADJ (Y+ I)
    (DECLARE (IGNORE I))
    Y+))

 (DEFTHM BITN-$$LOOP_0$ADJ ; $$LOOP_0-ADJ-PASS-THROUGH
   (IMPLIES (AND (NATP I)
                 (NATP J)
                 (NOT (EQUAL I J))
                 (<= I ($$LOOP_0$HIGH))
                 (<= J ($$LOOP_0$HIGH)))
            (EQUAL (BITN ($$LOOP_0$ADJ Y+ I) J)
                   (BITN Y+ J)))
   :HINTS (("Goal" :IN-THEORY (ENABLE $$LOOP_0$ADJ))))

 (DEFTHM BITN-$$LOOP_0$ADJ-$$LOOP_0$ADJ ; $$LOOP_0-ADJ-ABSORB-UNDER
   (IMPLIES (AND (NATP I)
                 (<= I ($$LOOP_0$HIGH))
                 (NATP J)
                 (<= J ($$LOOP_0$HIGH))
                 (<= I J))
            (EQUAL (BITN ($$LOOP_0$ADJ ($$LOOP_0$ADJ Y+ I)
                                       J)
                         J)
                   (BITN ($$LOOP_0$ADJ Y+ J) J)))
   :HINTS (("Goal" :IN-THEORY (ENABLE $$LOOP_0$ADJ)))))

(DEFUN $$LOOP_0 (Y+ I)
  (DECLARE (XARGS :MEASURE (NFIX (- (1+ ($$LOOP_0$HIGH)) I))
                  :HINTS
                  (("Goal" :IN-THEORY
                    (ENABLE LOG< LOG<= LOGAND)))))
  (IF (AND (NATP I) (<= I ($$LOOP_0$HIGH)))
      ($$LOOP_0 ($$LOOP_0$ADJ Y+ I)
                (+ I 1))
      Y+))

(DEFTHM BITN-$$LOOP_0
  (IMPLIES (AND (NATP I)
                (NATP J)
                (<= I ($$LOOP_0$HIGH))
                (<= J ($$LOOP_0$HIGH)))
           (EQUAL (BITN ($$LOOP_0 Y+ I) J)
                  (IF (<= I J)
                      (BITN ($$LOOP_0$ADJ Y+ J) J)
                      (BITN Y+ J)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Generic theory for counting down, non-arrays
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(ENCAPSULATE
 (($$LOOP_1$ADJ (Y+ I) T)
  ($$LOOP_1$LOW () T)
  ($$LOOP_1$HIGH () t))

 (LOCAL
  (DEFUN $$LOOP_1$LOW () 2))

 (LOCAL
  (DEFUN $$LOOP_1$HIGH () 4))

 (DEFTHM NATP-$$LOOP_1$LOW
   (AND (INTEGERP ($$LOOP_1$LOW))
        (<= 0 ($$LOOP_1$LOW)))
   :RULE-CLASSES :TYPE-PRESCRIPTION)

 (LOCAL
  (DEFUN $$LOOP_1$ADJ (Y+ I)
    (DECLARE (IGNORE I))
    Y+))

 (DEFTHM BITN-$$LOOP_1$ADJ ; $$LOOP_1-ADJ-PASS-THROUGH
   (IMPLIES (AND (NATP I)
                 (NATP J)
                 (NOT (EQUAL I J))
                 (>= I ($$LOOP_1$LOW))
                 (>= J ($$LOOP_1$LOW))
                 (< I ($$LOOP_1$HIGH))
                 (< J ($$LOOP_1$HIGH)))
            (EQUAL (BITN ($$LOOP_1$ADJ Y+ I) J)
                   (BITN Y+ J)))
   :HINTS (("Goal" :IN-THEORY (ENABLE $$LOOP_1$ADJ))))

 (DEFTHM BITN-$$LOOP_1$ADJ-$$LOOP_1$ADJ ; $$LOOP_1-ADJ-ABSORB-UNDER
   (IMPLIES (AND (NATP I)
                 (>= I ($$LOOP_1$low))
                 (NATP J)
                 (>= J ($$LOOP_1$LOW))
                 (< I ($$LOOP_1$HIGH))
                 (< J ($$LOOP_1$HIGH))
                 (<= J I))
            (EQUAL (BITN ($$LOOP_1$ADJ ($$LOOP_1$ADJ Y+ I)
                                       J)
                         J)
                   (BITN ($$LOOP_1$ADJ Y+ J) J)))
   :HINTS (("Goal" :IN-THEORY (ENABLE $$LOOP_1$ADJ)))))

(DEFUN $$LOOP_1 (Y+ I)
  (DECLARE (XARGS :MEASURE (NFIX (1+ I))
                  :HINTS
                  (("Goal" :IN-THEORY
                    (ENABLE LOG< LOG<= LOGAND)))))
  (IF (AND (NATP I) (>= I ($$LOOP_1$LOW)))
      ($$LOOP_1 ($$LOOP_1$ADJ Y+ I)
                (- I 1))
      Y+))

(DEFTHM BITN-$$LOOP_1
  (IMPLIES (AND (NATP I)
                (NATP J)
                (>= I ($$LOOP_1$LOW))
                (>= J ($$LOOP_1$LOW))
                (< I ($$LOOP_1$HIGH))
                (< J ($$LOOP_1$HIGH)))
           (EQUAL (BITN ($$LOOP_1 Y+ I) J)
                  (IF (>= I J)
                      (BITN ($$LOOP_1$ADJ Y+ J) J)
                      (BITN Y+ J))))
  :HINTS (("Goal" :EXPAND (($$LOOP_1 Y+ 0)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Generic theory for counting up, arrays
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(ENCAPSULATE
 (($$LOOP_2$ADJ (Y+ I) T)
  ($$LOOP_2$HIGH () T))

 (LOCAL
  (DEFUN $$LOOP_2$HIGH () 3))

 (DEFTHM NATP-$$LOOP_2$HIGH
   (AND (INTEGERP ($$LOOP_2$HIGH))
        (<= 0 ($$LOOP_2$HIGH)))
   :RULE-CLASSES :TYPE-PRESCRIPTION)

 (LOCAL
  (DEFUN $$LOOP_2$ADJ (Y+ I)
    (DECLARE (IGNORE I))
    Y+))

 (DEFTHM AG-$$LOOP_2$ADJ ; $$LOOP_2-ADJ-PASS-THROUGH
   (IMPLIES (AND (NATP I)
                 (NATP J)
                 (NOT (EQUAL I J))
                 (<= I ($$LOOP_2$HIGH))
                 (<= J ($$LOOP_2$HIGH)))
            (EQUAL (AG J ($$LOOP_2$ADJ Y+ I))
                   (AG J Y+)))
   :HINTS (("Goal" :IN-THEORY (ENABLE $$LOOP_2$ADJ))))

 (DEFTHM AG-$$LOOP_2$ADJ-$$LOOP_2$ADJ ; $$LOOP_2-ADJ-ABSORB-UNDER
   (IMPLIES (AND (NATP I)
                 (<= I ($$LOOP_2$HIGH))
                 (NATP J)
                 (<= J ($$LOOP_2$HIGH))
                 (<= I J))
            (EQUAL (AG J ($$LOOP_2$ADJ ($$LOOP_2$ADJ Y+ I)
                                       J))
                   (AG J ($$LOOP_2$ADJ Y+ J))))
   :HINTS (("Goal" :IN-THEORY (ENABLE $$LOOP_2$ADJ)))))

(DEFUN $$LOOP_2 (Y+ I)
  (DECLARE (XARGS :MEASURE (NFIX (- (1+ ($$LOOP_2$HIGH)) I))
                  :HINTS
                  (("Goal" :IN-THEORY
                    (ENABLE LOG< LOG<= LOGAND)))))
  (IF (AND (NATP I) (<= I ($$LOOP_2$HIGH)))
      ($$LOOP_2 ($$LOOP_2$ADJ Y+ I)
                (+ I 1))
      Y+))

(DEFTHM AG-$$LOOP_2
  (IMPLIES (AND (NATP I)
                (NATP J)
                (<= I ($$LOOP_2$HIGH))
                (<= J ($$LOOP_2$HIGH)))
           (EQUAL (AG J ($$LOOP_2 Y+ I))
                  (IF (<= I J)
                      (AG J ($$LOOP_2$ADJ Y+ J))
                      (AG J Y+)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Generic theory for counting down, arrays
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(ENCAPSULATE
 (($$LOOP_3$ADJ (Y+ I) T)
  ($$LOOP_3$LOW () T)
  ($$LOOP_3$HIGH () t))

 (LOCAL
  (DEFUN $$LOOP_3$LOW () 2))

 (LOCAL
  (DEFUN $$LOOP_3$HIGH () 4))

 (DEFTHM NATP-$$LOOP_3$LOW
   (AND (INTEGERP ($$LOOP_3$LOW))
        (<= 0 ($$LOOP_3$LOW)))
   :RULE-CLASSES :TYPE-PRESCRIPTION)

 (LOCAL
  (DEFUN $$LOOP_3$ADJ (Y+ I)
    (DECLARE (IGNORE I))
    Y+))

 (DEFTHM AG-$$LOOP_3$ADJ
   (IMPLIES (AND (NATP I)
                 (NATP J)
                 (NOT (EQUAL I J))
                 (>= I ($$LOOP_3$LOW))
                 (>= J ($$LOOP_3$LOW))
                 (< I ($$LOOP_3$HIGH))
                 (< J ($$LOOP_3$HIGH)))
            (EQUAL (AG J ($$LOOP_3$ADJ Y+ I))
                   (AG J Y+)))
   :HINTS (("Goal" :IN-THEORY (ENABLE $$LOOP_3$ADJ))))

 (DEFTHM AG-$$LOOP_3$ADJ-$$LOOP_3$ADJ
   (IMPLIES (AND (NATP I)
                 (>= I ($$LOOP_3$low))
                 (NATP J)
                 (>= J ($$LOOP_3$low))
                 (< I ($$LOOP_3$HIGH))
                 (< J ($$LOOP_3$HIGH))
                 (<= J I))
            (EQUAL (AG J ($$LOOP_3$ADJ ($$LOOP_3$ADJ Y+ I)
                                       J))
                   (AG J ($$LOOP_3$ADJ Y+ J))))
   :HINTS (("Goal" :IN-THEORY (ENABLE $$LOOP_3$ADJ)))))

(DEFUN $$LOOP_3 (Y+ I)
  (DECLARE (XARGS :MEASURE (NFIX (1+ I))
                  :HINTS
                  (("Goal" :IN-THEORY
                    (ENABLE LOG< LOG<= LOGAND)))))
  (IF (AND (NATP I) (>= I ($$LOOP_3$LOW)))
      ($$LOOP_3 ($$LOOP_3$ADJ Y+ I)
                (- I 1))
      Y+))

(DEFTHM AG-$$LOOP_3
  (IMPLIES (AND (NATP I)
                (NATP J)
                (>= I ($$LOOP_3$LOW))
                (>= J ($$LOOP_3$LOW))
                (< I ($$LOOP_3$HIGH))
                (< J ($$LOOP_3$HIGH)))
           (EQUAL (AG J ($$LOOP_3 Y+ I))
                  (IF (>= I J)
                      (AG J ($$LOOP_3$ADJ Y+ J))
                      (AG J Y+))))
  :HINTS (("Goal" :EXPAND (($$LOOP_3 Y+ 0)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Miscellany
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#| can't be uncommented since is redefined in lib/simple-loop-helpers.lisp
(deftheory simple-loop-thy-1
  (UNION-THEORIES
   '(BITN-SETBITN-NOT-EQUAL
     AG-DIFF-AS
     BITS-31-0
     NATP)
   (THEORY 'MINIMAL-THEORY)))
|#

;(in-theory (enable setbits))
