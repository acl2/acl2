; RTL - A Formal Theory of Register-Transfer Logic and Computer Arithmetic
; Copyright (C) 1995-2013 Advanced Mirco Devices, Inc.
;
; Contact:
;   David Russinoff
;   1106 W 9th St., Austin, TX 78703
;   http://www.russsinoff.com/
;
; See license file books/rtl/rel9/license.txt.
;
; Author: David M. Russinoff (david@russinoff.com)

(in-package "RTL")

(include-book "bits-new")
(local (include-book "bits-new-proofs"))

(local (include-book "../lib2/top"))
(local (include-book "../../arithmetic/top"))
(local (include-book "../support/logand"))
(local (include-book "../support/logior"))
(local (include-book "../support/logxor"))
(local (include-book "../support/log"))


;; (local (include-book "../support/merge"))

;;;**********************************************************************
;;;                       LOGNOT, LOGAND, LOGIOR, and LOGXOR
;;;**********************************************************************

(in-theory (disable lognot logand logior logxor))



;;;
;;; we want prove some result about lognot is lnot(x, (1 + expo(x))) -
;;; 2^(1+(expo(x))
;;;

;;; lognot(x) = if x >= 0
;;;                lnot(x, (1+expo(x))) - 2^(1+(expo(x))))
;;;
;;;             abs(x)-1

;;;
;;; logand(x, y) = land(x,y, 1+min(expo(x),expo(y)))
;;;
;;; what about this?

(defthmd lognot-def
    (implies (integerp x)
	     (equal (lognot x)
		    (1- (- x))))
    :hints (("Goal" :in-theory (e/d (lognot) ()))))


(defthmd logand-def
    (implies (and (case-split (integerp i))
		  (case-split (integerp j)))
	     (equal (logand i j)
		    (+ (* 2 (logand (fl (* 1/2 i)) (fl (* 1/2 j))))
		       (logand (mod i 2) (mod j 2)))))
  :rule-classes ((:definition :controller-alist ((acl2::binary-logand t t)))))


(defthmd logior-def
    (implies (and (case-split (integerp i))
		  (case-split (integerp j)))
	     (equal (logior i j)
		    (+ (* 2 (logior (fl (* 1/2 i)) (fl (* 1/2 j))))
		       (logior (mod i 2) (mod j 2)))))
  :rule-classes ((:definition :controller-alist ((acl2::binary-logior t t)))))


(defthmd logxor-def
    (implies (and (case-split (integerp i))
		  (case-split (integerp j)))
	     (equal (logxor i j)
		    (+ (* 2 (logxor (fl (* 1/2 i)) (fl (* 1/2 j))))
		       (logxor (mod i 2) (mod j 2)))))
  :rule-classes ((:definition :controller-alist ((acl2::binary-logxor t t)))))


;;;;;;
;;;;;;


(defthm logand-natp
    (implies (and (natp i)
		  (integerp j))
	     (natp (logand i j)))
  :rule-classes (:type-prescription :rewrite))

(defthm logand-natp-2
    (implies (and (integerp i)
		  (natp j))
	     (natp (logand i j)))
  :rule-classes (:type-prescription :rewrite))


;; (defthm logand-natp
;;     (implies (and (natp i)
;; 		  (integerp j))
;; 	     (natp (logand i j)))
;;   :rule-classes (:type-prescription :rewrite))

;; (defthm logand-natp-2
;;     (implies (and (integerp i)
;; 		  (natp j))
;; 	     (natp (logand i j)))
;;   :rule-classes (:type-prescription :rewrite))


;;  from ../support/logand.lisp
;;
;; (defthm logand-bnd
;;    (implies (<= 0 x)
;;             (<= (logand x y) x))
;;    :rule-classes :linear
;;    )

(defthm logand-bvecp-g
  (implies (and (natp n)
                (bvecp x n)
                (integerp y))
           (bvecp (logand x y) n))
  :hints (("Goal" :use ((:instance logand-bnd))
           :in-theory (e/d (bvecp) ()))))

(defthm logior-natp
    (implies (and (natp i)
		  (natp j))
	     (natp (logior i j)))
  :rule-classes (:type-prescription :rewrite))

(defthm logior-bvecp
    (implies (and (bvecp x n)
		  (bvecp y n))
	     (bvecp (logior x y) n)))

(defthm logxor-natp
    (implies (and (natp i)
		  (natp j))
	     (natp (logxor i j)))
  :rule-classes (:type-prescription :rewrite))

(defthm logxor-bvecp
    (implies (and (bvecp x n)
		  (bvecp y n)
                  (natp n))
	     (bvecp (logxor x y) n)))



(defun logop-2-induct (x y)
  (if (or (zp x) (zp y))
      ()
    (logop-2-induct (fl (/ x 2)) (fl (/ y 2)))))

(defun logop-2-n-induct (x y n)
  (if (zp n)
      (cons x y)
    (logop-2-n-induct (fl (/ x 2)) (fl (/ y 2)) (1- n))))


(defun logop-3-induct (x y z)
  (declare (xargs :measure (:? x y z)))
  (if (and (natp x) (natp y) (natp z))
      (if (and (zp x) (zp y) (zp z))
	  t
	(logop-3-induct (fl (/ x 2)) (fl (/ y 2)) (fl (/ z 2))))
    t))


(defthm integerp-fl-1
  (implies (and (integerp y)
                (< y 0))
           (<= y (fl (* 1/2 y))))
  :rule-classes :linear)

(defthm integerp-fl-2
  (implies (and (integerp y)
                (< y 0)
                (not (equal y -1)))
           (< y (fl (* 1/2 y))))
  :rule-classes :linear)



;; (defun logop-3-induct (x y z)
;;   (if (and (natp x) (natp y) (natp z))
;;       (if (and (zp x) (zp y) (zp z))
;; 	  t
;; 	(logop-3-induct (fl (/ x 2)) (fl (/ y 2)) (fl (/ z 2))))
;;     t))

(defthmd logand-fl-2-rewrite
    (implies (and (natp x)
		  (natp y))
	     (equal (fl (* 1/2 (logand x y)))
		    (logand (fl (* 1/2 x)) (fl (* 1/2 y))))))

(defthmd logior-fl-2-rewrite
    (implies (and (natp i)
		  (natp j))
	     (equal (fl (* 1/2 (logior i j)))
		    (logior (fl (* 1/2 i)) (fl (* 1/2 j))))))

(defthmd logxor-fl-2-rewrite
    (implies (and (natp i)
		  (natp j))
	     (equal (fl (* 1/2 (logxor i j)))
		    (logxor (fl (* 1/2 i)) (fl (* 1/2 j))))))

;; we appear to have a better rule than logior
;;
;; (DEFTHM LOGIOR-EQUAL-0
;;   (IMPLIES (AND (CASE-SPLIT (INTEGERP I))
;;                 (CASE-SPLIT (INTEGERP J)))
;;            (EQUAL (EQUAL (LOGIOR I J) 0)
;;                   (AND (EQUAL I 0) (EQUAL J 0)))))

(defthm logior-not-0
    (implies (and (integerp x)
		  (integerp y)
		  (= (logior x y) 0))
	     (and (= x 0) (= y 0)))
  :rule-classes ())

;;;
;;; these following two are genuninely new.
;;;

(local
 (encapsulate ()

              (defthmd bvecp-fl-1/2
                (implies (bvecp y (+ 1 n))
                         (bvecp (fl (* 1/2 y)) n))
                :hints (("Goal" :in-theory (e/d (bvecp
                                                 expt-2-reduce-leading-constant) ()))))

              ;; we can prove the following.
              ;;
              ;; (skip-proofs
              ;;  ;; proved in bits-new-proofs.lisp
              ;;  (defthmd logand-ones-g
              ;;    (implies (and (integerp i)
              ;;                  (case-split (integerp i))
              ;;                  )
              ;;             (equal (logand i (1- (expt 2 n)))
              ;;                    (mod i (expt 2 n))))))

              ;; (defthmd logand-ones-g-specific
              ;;    (implies (and (integerp i)
              ;;                  (case-split (integerp i))
              ;;                  )
              ;;             (equal (logand i -1)
              ;;                    i))
              ;;    :hints (("Goal" :use ((:instance logand-ones-g
              ;;                                     (n 0))))))

              (defthmd mod-2-expt-2-is-zero
                (implies (and (integerp n)
                              (> n 0)
                              (integerp x))
                         (equal (mod (* x (expt 2 n)) 2)
                                0))
                :hints (("Goal" :in-theory (e/d (mod) ()))))

              (defthmd integer-decompose
                (implies (integerp y)
                         (equal (FL (* 1/2 Y))
                                (* 1/2 (- y (mod y 2)))))
                :hints (("Goal" :in-theory (e/d (mod evenp) ()))))

              ))

(defthm logior-expt-g
  (implies (and (natp n)
                (integerp x)
                (bvecp y n))
           (= (logior (* (expt 2 n) x) y)
              (+ (* (expt 2 n) x) y)))
  :rule-classes ()
  :hints (("Goal" :in-theory (e/d (mod-2-expt-2-is-zero
                                   expt-2-reduce-leading-constant
                                   bvecp-fl-1/2)
                                  ((logior)))
           :induct (logop-2-n-induct (* (expt 2 n) x)
                                     y
                                     n))
          ("Subgoal *1/2" :use ((:instance logior-def
                                           (i (* (expt 2 n) x))
                                           (j y))
                                (:instance integer-decompose)))))

(defthm logior-expt-2-g
  (implies (and (integerp x)
                (integerp y)
                (natp n))
           (= (logior (* (expt 2 n) x)
                      (* (expt 2 n) y))
              (* (expt 2 n) (logior x y))))
  :rule-classes ()
  :hints (("Goal" :in-theory (e/d (mod-2-expt-2-is-zero
                                   expt-2-reduce-leading-constant)
                                  ((logior)))
           :induct (logop-2-n-induct (* (expt 2 n) x)
                                     (* (expt 2 n) y)
                                     n))
          ("Subgoal *1/2" :use ((:instance logior-def
                                           (i (* (expt 2 n) x))
                                           (j (* (expt 2 n) y)))
                                (:instance integer-decompose)))))




;; (defthm logand-bnd
;;     (implies (and (natp x)
;; 		  (integerp y))
;; 	     (<= (logand x y) x))
;;   :rule-classes :linear)


(defthm logand-bnd
    (implies (<= 0 x)
	     (<= (logand x y) x))
  :rule-classes :linear)

(local
 (defthmd fl-fl-reduce
   (implies (and (integerp n)
                 (> n 0))
            (equal (FL (* 2 (/ (EXPT 2 N)) (FL (* 1/2 Y))))
                  (fl (* y (/ (expt 2 n))))))
   :hints (("Goal" :use ((:instance FL-SHIFT-FL-2-FACTORS-2
                                    (n 1)
                                    (m n)
                                    (x (* 1/2 y))))
            :in-theory (e/d (expt-2-reduce-leading-constant) ())))))


(defthm logand-expt-g
  (implies (and (integerp x)
                (integerp y)
                (natp n))
           (= (logand (* (expt 2 n) x) y)
              (* (expt 2 n) (logand x (fl (/ y (expt 2 n)))))))
   :rule-classes ()
  :hints (("Goal" :in-theory (e/d (mod-2-expt-2-is-zero
                                   fl-fl-reduce
                                   expt-2-reduce-leading-constant)
                                  ((logand)))
           :induct (logop-2-n-induct (* (expt 2 n) x)
                                     y
                                     n))
          ("Subgoal *1/2" :use ((:instance logand-def
                                           (i (* (expt 2 n) x))
                                           (j y))))))


;;;;;; Mon Feb  9 12:53:20 2009

;;;; strategy?
;;;;
;;;; bitn(lnot(x, n), i) vs bitn(lognot(x), i)
;;;;

;; >  D          (DEFTHM BITN-MOD
;;                       (IMPLIES (AND (< K N) (INTEGERP N) (INTEGERP K))
;;                                (EQUAL (BITN (MOD X (EXPT 2 N)) K)
;;                                       (BITN X K))))

;;
;; bitn-mod lemma are pretty powerful. Mon Feb  9 13:17:51 2009
;;

(local
 (defthmd bitn_alt-lognot-lemma
  (implies (and (integerp x)
                (integerp n)
                (> n 0))
           (equal (bitn_alt (lognot x) n)
                  (bitn (lnot x (+ 1 n)) n)))
   :hints (("Goal" :in-theory (e/d (bitn_alt-is-bitn
                                    lnot
                                    bits-mod
                                    lognot-def)
                                   (bits-n-n-rewrite
                                    bitn-0
                                    MOD-MINUS-ALT))
            :use ((:instance bitn-mod
                             (x (+ -1 (* -1 x)))
                             (k n)
                             (n (+ 1 n)))
                  (:instance bitn-mod
                             (x (+ -1 (expt 2 (+ 1 n))
                                   (* -1 (bits x n 0))))
                             (k n)
                             (n (+ 1 n)))))))
)


(defthmd bitn_alt-lognot
  (implies (and (integerp x)
                (integerp n)
                (> n 0))
           (not (equal (bitn_alt (lognot x) n)
                       (bitn_alt x n))))
   :hints (("Goal" :in-theory (e/d (bitn_alt-lognot-lemma
                                    bitn-lnot)
                                   ()))
; Matt K. v7-1 mod for avoiding "Goal'", 2/13/2015: "Goal''" changed to "Goal'".
           ("Goal'" :in-theory (e/d (bitn_alt-is-bitn lnot)
                                    ()))))

;;;;;
;;;;;
;;;;;

;;;
;;; this is generalized to allow n to be negative.
;;;

(defthmd bitn_alt-logand
  (implies (and (integerp x)
                (integerp y)
                (integerp n))
           (equal (bitn_alt (logand x y) n)
                  (logand (bitn_alt x n) (bitn_alt y n))))
  :hints (("Goal" :in-theory (e/d (bitn_alt-is-bitn bitn-neg)
                                  (bitn-logand))
           :use ((:instance bitn-logand)))))




;;;
;;; this following is generalized to allow negative indexs.
;;;
;;; We can prove the following using the above result.
;;;


;; (local
;;  (encapsulate ()
;;               (local (include-book "../support/badguys"))

;;              (defun sumbits-badguy (x y k)
;;                (if (zp k)
;;                    0 ; arbitrary
;;                  (if (not (equal (bitn x (1- k)) (bitn y (1- k))))
;;                      (1- k)
;;                    (sumbits-badguy x y (1- k)))))


;;              (defthmd sumbits-badguy-is-correct
;;                (implies (and (bvecp x k)
;;                              (bvecp y k)
;;                              (equal (bitn x (sumbits-badguy x y k))
;;                                     (bitn y (sumbits-badguy x y k)))
;;                              (integerp k)
;;                              (< 0 k))
;;                         (equal (equal x y) t))
;;                :hints (("Goal"
;;                         :use sumbits-badguy-is-correct-lemma
;;                         :in-theory (enable sumbits-thm))))

;;              (defthmd sumbits-badguy-bounds
;;                (implies (and (integerp k)
;;                              (< 0 k))
;;                         (let ((badguy (sumbits-badguy x y k)))
;;                           (and (integerp badguy)
;;                                (<= 0 badguy)
;;                                (< badguy k)))))
;;              ))



(local
 (defund bvequal (v1 v2 n)
  (equal (sumbits v1 n)
         (sumbits v2 n))))


(local
 (defthm bvequal-then-equal
  (implies (and (bvequal x y n)
                (bvecp x n)
                (bvecp y n)
                (natp n))
           (equal x y))
  :hints (("Goal" :use ((:instance sumbits-thm
                                   (x x))
                        (:instance sumbits-thm
                                   (x y)))
           :in-theory (enable bvequal)))
  :rule-classes nil))


(local
 (defthmd bitn-logand-bvequal
   (implies (and (integerp x)
                 (integerp y)
                (integerp n))
            (equal (bitn (logand x y) n)
                   (logand (bitn x n) (bitn y n))))
  :hints (("Goal" :use ((:instance bitn-logand))
           :in-theory (e/d (bitn-neg) ())))))

(local
 (defthmd  bvequal-bits-logand
   (implies (and (integerp x)
                 (integerp y)
                (integerp i)
                (integerp j)
                (integerp k)
                (<= 0 k)
                (<= k (+ 1 i (* -1 j)))
                (>= i j))
           (bvequal (bits (logand x y) i j)
                    (logand (bits x i j)
                            (bits y i j))
                    k))
  :hints (("Goal" :in-theory (e/d (bvequal sumbits
                                           bitn-logand-bvequal
                                           bitn-bits) (bits-logand))))))


(defthmd bits_alt-logand
  (implies (and (integerp x)
                (integerp y)
                (integerp i)
                (integerp j))
           (equal (bits_alt (logand x y) i j)
                  (logand (bits_alt x i j) (bits_alt y i j))))
  :hints (("Goal" :in-theory (e/d (bits_alt-is-bits
                                   bvequal-bits-logand) (bits-logand))
           :cases ((>= i j)))
          ("Subgoal 1"  :use ((:instance bvequal-then-equal
                                         (n (+ 1 i (* -1 j)))
                                         (x (bits (logand x y) i j))
                                         (y (logand (bits x i j) (bits y i j))))))))




(defthmd bitn_alt-logior
  (implies (and (integerp x)
                (integerp y)
                (integerp n))
           (equal (bitn_alt (logior x y) n)
                  (logior (bitn_alt x n) (bitn_alt y n))))
  :hints (("Goal" :in-theory (e/d (bitn_alt-is-bitn bitn-neg)
                                  ())
           :use ((:instance bitn-logior)))))





(local
 (defthmd bitn-logior-bvequal
   (implies (and (integerp x)
                 (integerp y)
                 (integerp n))
            (equal (bitn (logior x y) n)
                   (logior (bitn x n) (bitn y n))))
   :hints (("Goal" :use ((:instance bitn-logior))
            :in-theory (e/d (bitn-neg) ())))))


(local
 (defthmd  bvequal-bits-logior
   (implies (and (integerp x)
                 (integerp y)
                 (integerp i)
                 (integerp j)
                 (integerp k)
                 (<= 0 k)
                 (<= k (+ 1 i (* -1 j)))
                 (>= i j))
            (bvequal (bits (logior x y) i j)
                     (logior (bits x i j)
                             (bits y i j))
                     k))
   :hints (("Goal" :in-theory (e/d (bvequal sumbits
                                            bitn-logior-bvequal
                                            bitn-bits) (bits-logior))))))

(defthmd bits_alt-logior
   (implies (and (integerp x)
                 (integerp y)
                 (integerp i)
                 (integerp j))
            (equal (bits_alt (logior x y) i j)
                   (logior (bits_alt x i j) (bits_alt y i j))))
   :hints (("Goal" :in-theory (e/d (bits_alt-is-bits
                                    bvequal-bits-logior) (bits-logior))
            :cases ((>= i j)))
           ("Subgoal 1"  :use ((:instance bvequal-then-equal
                                          (n (+ 1 i (* -1 j)))
                                          (x (bits (logior x y) i j))
                                          (y (logior (bits x i j) (bits y i j))))))))


;;;;;;;


(defthmd bitn_alt-logxor
  (implies (and (case-split (integerp x))
                (case-split (integerp y))
                (case-split (integerp n)))
           (equal (bitn_alt (logxor x y) n)
                  (logxor (bitn_alt x n) (bitn_alt y n))))
  :hints (("Goal" :in-theory (e/d (bitn_alt-is-bitn bitn-neg)
                                  ())
           :use ((:instance bitn-logxor)))))



(local
 (defthmd bitn-logxor-bvequal
   (implies (and (integerp x)
                 (integerp y)
                 (integerp n))
            (equal (bitn (logxor x y) n)
                   (logxor (bitn x n) (bitn y n))))
   :hints (("Goal" :use ((:instance bitn-logxor))
            :in-theory (e/d (bitn-neg) ())))))


(local
 (defthmd  bvequal-bits-logxor
   (implies (and (integerp x)
                 (integerp y)
                 (integerp i)
                 (integerp j)
                 (integerp k)
                 (<= 0 k)
                 (<= k (+ 1 i (* -1 j)))
                 (>= i j))
            (bvequal (bits (logxor x y) i j)
                     (logxor (bits x i j)
                             (bits y i j))
                     k))
   :hints (("Goal" :in-theory (e/d (bvequal sumbits
                                            bitn-logxor-bvequal
                                            bitn-bits) (bits-logxor))))))





(defthmd bits_alt-logxor
  (implies (and (case-split (integerp x))
                (case-split (integerp y))
                (case-split (integerp i))
                (case-split (integerp j)))
           (equal (bits_alt (logxor x y) i j)
                  (logxor (bits_alt x i j) (bits_alt y i j))))
  :hints (("Goal" :in-theory (e/d (bits_alt-is-bits
                                   bvequal-bits-logxor) (bits-logxor))
           :cases ((>= i j)))
          ("Subgoal 1"  :use ((:instance bvequal-then-equal
                                         (n (+ 1 i (* -1 j)))
                                         (x (bits (logxor x y) i j))
                                         (y (logxor (bits x i j) (bits y i j))))))))




;;;;;;
;;;;;;

;; we can prove the following.
;;
(local
 (encapsulate ()
;; proved in bits-new-proofs.lisp
(defthmd logand-ones-g
  (implies (and (integerp i)
                (case-split (integerp i))
                )
           (equal (logand i (1- (expt 2 n)))
                  (mod i (expt 2 n)))))

(defthmd logand-ones-g-specific
   (implies (and (integerp i)
                 (case-split (integerp i))
                 )
            (equal (logand 1 i)
                   (bitn i 0)))
   :hints (("Goal" :use ((:instance logand-ones-g
                                    (n 1)))
            :in-theory (e/d (bitn bits-mod)
                            (bits-n-n-rewrite)))))


(defthmd bits-expt-n
  (equal (BITS (EXPT 2 K) (+ -1 K) 0)
         0)
  :hints (("Goal" :in-theory (e/d (bits mod)
                                  ()))))

(defthmd bitn-expt-n
  (implies (natp k)
           (equal (BITN (EXPT 2 K) k)
                  1))
  :hints (("Goal" :in-theory (e/d (bits bitn mod)
                                  ())
           :use ((:instance bits-mod-2
                            (x (expt 2 k))
                            (i (+ 1 k))
                            (j k))))))

(defthmd bvecp-logand-specific
  (implies (and (natp k)
                (integerp x))
           (bvecp (LOGAND X (EXPT 2 K)) (+ 1 k)))
  :hints (("Goal" :use ((:instance logand-bvecp-g
                                   (x (expt 2 k))
                                   (y x)
                                   (n (+ 1 k))))
           :cases ((bvecp (expt 2 k) (+ 1 k))))
          ("Subgoal 2" :in-theory (e/d (bvecp) ()))))

;;;
;;; the proof looks awkward.
;;;
))

(defthmd logand-expt-2-g
    (implies (and (integerp x)
		  (natp k))
	     (equal (logand x (expt 2 k))
		    (* (expt 2 k) (bitn_alt x k))))
    :hints (("Goal" :in-theory (e/d (bitn_alt-is-bitn
                                     cat
                                     bits_alt-is-bits
                                     bits-expt-n
                                     bitn-expt-n
                                     logand-ones-g-specific
                                     bvecp-logand-specific)
                                    (cat-bitn-bits
                                     bits-logand
                                     bitn-logand
                                     bitn-logand-bvequal))
             :use ((:instance cat-bitn-bits
                              (x (logand x (expt 2 k)))
                              (j k)
                              (m 1)
                              (k (+ -1 k))
                              (l 0)
                              (n k))))
            ("Subgoal 1"
             :use ((:instance bits_alt-logand
                              (x x)
                              (y (expt 2 k))
                              (i (+ -1 k))
                              (j 0))
                   (:instance bitn_alt-logand
                              (x x)
                              (y (expt 2 k))
                              (n k))))))
;;;;
;;;; we don't want to include the merge.lisp here. Mon Feb  9 16:48:35 2009
;;;;
;;;;



(local
;;;
;;;
 (defthmd bitn-fl-k
   (implies (and (integerp k)
                 (integerp x)
                 (> k 0))
            (equal (BITN (FL (* 1/2 X)) (+ -1 K))
                   (bitn x k)))
   :hints (("Goal" :in-theory (e/d (bitn-def
                                    fl-fl-reduce
                                    expt-2-reduce-leading-constant
                                    mod)
                                   ())))))



(local
 (defthmd mod-expt-2n
   (implies (and (integerp k)
                 (> k 0))
            (equal (MOD (EXPT 2 K) 2)
                   0))
   :hints (("Goal" :in-theory (e/d (mod) ())))))



;; (defthm logior-0-y
;;      (implies (integerp y)
;;               (equal (logior 0 y) y)))

;;; these are new from merge.lisp

(defthmd logior-expt-3-g
    (implies (and (integerp x)
		  (natp k))
	     (equal (logior x (expt 2 k))
		    (+ x
		       (* (expt 2 k)
			  (- 1 (bitn_alt x k))))))
    :hints (("Goal" :in-theory (e/d (bitn-fl-k
                                     bitn_alt-is-bitn)
                                    ())
             :induct (logop-2-n-induct x (expt 2 k) k))
            ("Subgoal *1/2" :use ((:instance logior-def
                                             (i x)
                                             (j (expt 2 k)))
                                  (:instance integer-decompose
                                             (y x)))
             :in-theory (e/d (bitn-fl-k
                              mod-expt-2n
                              bitn_alt-is-bitn
                              expt-2-reduce-leading-constant)
                             ()))
            ("Subgoal *1/1" :in-theory (e/d (bitn_alt-is-bitn
                                             bitn-def)
                                            ())
             :use ((:instance logior-def
                              (i 1)
                              (j x))
                   (:instance integer-decompose
                              (y x)))
             :cases ((equal (mod x 2) 1)))))


;;;
;;; many ways to prove the following.
;;;
;;; use the bvequal approach
;;;



(local
 (encapsulate ()

 (local
  (encapsulate ()

               (defun all-ones-p (x n)
                 (if (zp n)
                     t
                   (and (equal (bitn x (+ -1 n)) 1)
                        (all-ones-p x (+ -1 n)))))


               (defthmd sumbits-less-than
                 (implies (natp n)
                          (<= (sumbits x n) (+ -1 (expt 2 n))))
                 :hints (("Goal" :do-not '(generalize)
                          :in-theory (enable expt-2-reduce-leading-constant))
                         ("Subgoal *1/4'" :use ((:instance bitn-0-1
                                                           (x x)
                                                           (n (+ -1 n))))))
                 :rule-classes :linear)

               (defthmd all-bits-sumbits-is
                 (implies (equal (sumbits x n) (+ -1 (expt 2 n)))
                          (all-ones-p x n))
                 :hints (("Goal" :do-not '(generalize)
                          :in-theory (enable expt-2-reduce-leading-constant))
                         ("Subgoal *1/4" :use ((:instance sumbits-less-than
                                                          (x x)
                                                          (n (+ -1 n)))))))

               (defthmd bits-tail-specific
                 (implies (and (natp n)
                               (> n 0))
                          (equal (BITS (+ -1 (EXPT 2 N)) (+ -1 N) 0)
                                 (+ -1 (expt 2 n))))
                 :hints (("Goal" :cases ((bvecp (+ -1 (expt 2 n)) n)))
                         ("Subgoal 2" :in-theory (enable bvecp))))

               (defthmd all-bits-sumbits-is-strong
                 (implies (and (natp n)
                               (> n 0))
                          (all-ones-p (+ -1 (expt 2 n)) n))
                 :hints (("Goal" :do-not '(generalize)
                          :in-theory (enable sumbits-bits
                                             bits-tail-specific)
                          :use ((:instance all-bits-sumbits-is
                                           (x (+ -1 (expt 2 n))))))))


               (defthmd all-bits-sumbits-is-2
                 (implies (and (all-ones-p x n)
                               (natp n))
                          (equal (sumbits x n) (+ -1 (expt 2 n))))
                 :hints (("Goal" :do-not '(generalize)
                          :in-theory (enable expt-2-reduce-leading-constant))))



               (defthm all-bits-sumbits-is-2-strong
                 (implies (and (not (equal x (+ -1 (expt 2 n))))
                               (bvecp x n)
                               (natp n)
                               (> n 0))
                          (not (all-ones-p x n)))
                 :hints (("Goal" :do-not '(generalize)
                          :use ((:instance all-bits-sumbits-is-2))
                          :in-theory (enable sumbits-bits
                                             all-bits-sumbits-is-strong
                                             bits-tail-specific))))




               (defthm bitn-all-ones-is-one
                 (implies (and (all-ones-p x n)
                               (natp i)
                               (natp n)
                               (< i n))
                          (equal (bitn x i) 1)))



               (defun all-ones-p-alt (x n)
                 (if (zp n)
                     t
                   (and (equal (bitn x (+ -1 n)) 1)
                        (all-ones-p-alt x (+ -1 n)))))



               (defthmd all-ones-p-bits-all-ones
                 (implies (and (all-ones-p x n)
                               (natp n)
                               (natp i)
                               (natp j)
                               (natp k)
                               (< i n)
                               (<= j i)
                               (<= k (+ 1 i (* -1 j))))
                          (all-ones-p-alt (bits x i j) k))
                 :hints (("Goal" :induct (all-ones-p-alt (bits x i j)
                                                         k)
                          :in-theory (e/d (bitn-bits)
                                          (all-ones-p
                                           bitn-all-ones-is-one)))
                         ("Subgoal *1/3" :use ((:instance bitn-all-ones-is-one
                                                          (i (+ -1 j k)))))))






               (defthm all-ones-p-alt-is-all-one-p
                 (equal (all-ones-p-alt x n)
                        (all-ones-p x n)))

               ))




 (defthmd bits-all-ones-is-all-ones
   (implies (and (natp m)
                 (> m 0)
                 (natp i)
                 (natp j)
                 (> m  i)
                 (>= i j))
            (equal (bits (+ -1 (expt 2 m))
                         i j)
                   (+ -1 (expt 2 (+ 1 i (* -1 j))))))
   :hints (("Goal" :use ((:instance all-bits-sumbits-is-strong
                                    (n m))
                         (:instance all-ones-p-bits-all-ones
                                    (x (+ -1 (expt 2 m)))
                                    (n m)
                                    (i i)
                                    (j j)
                                    (k (+ 1 i (* -1 j))))
                         (:instance all-bits-sumbits-is-2-strong
                                    (x (bits (+ -1 (expt 2 m)) i j))
                                    (n (+ 1 i (* -1 j))))))))




 ))

;; (defthmd bitn-shift
;;   (implies (and (integerp n)
;; 		(integerp k))
;; 	   (equal (bitn (* x (expt 2 k)) (+ n k))
;; 		  (bitn x n))))

(local
(defthmd expt-merge-hack
  (implies (and (integerp n)
                (integerp m))
           (equal (* (expt 2 n) (expt 2 m))
                  (expt 2 (+ n m))))))


(local
(defthmd bitn-expt-expt-i
  (implies (and (natp n)
                (natp k)
                (natp i)
                (<= k n)
                (< i n)) ;; could remove this.
           (equal (BITN (+ (EXPT 2 N) (* -1 (EXPT 2 K)))
                        i)
                  (if (and (<= k i)
                           (< i n))
                      1
                    0)))
  :hints (("Goal" :cases ((equal (bitn (+ (expt 2 n) (* -1 (expt 2 k))) i)
                                 (bitn (+ -1 (expt 2 (+ n (* -1 k))))
                                       (+ i (* -1 k))))))
          ("Subgoal 2" :use ((:instance bitn-shift
                                        (x (+ -1 (expt 2 (+ n (* -1 k)))))
                                        (k k)
                                        (n (+ i (* -1 k)))))
           :in-theory (e/d (expt-merge-hack) ()))
          ("Subgoal 1" :use ((:instance bits-all-ones-is-all-ones
                                        (m (+ n (* -1 k)))
                                        (i (+ i (* -1 k)))
                                        (j (+ i (* -1 k)))))
           :in-theory (e/d (bitn) (bits-n-n-rewrite)))))
)



(local
(defthmd bitn-shift-fact-expt
  (implies (and (integerp n)
                (integerp i)
                (integerp x))
           (equal (bitn (* (expt 2 n) x) i)
                  (bitn x (+ i (* -1 n)))))
  :hints (("Goal"
           :cases ((equal (* (expt 2 n) (expt 2 (* -1 i)))
                          (expt 2 (+ n (* -1 i))))))
          ("Subgoal 1" :in-theory (e/d (bitn-def mod
                                                 expt-inverse
                                                 expt-2-reduce-leading-constant
                                                 ) (EXPO-SHIFT-GENERAL
                                                    EXPT-COMPARE-EQUAL)))))
)

;; (defthm logand-1-x
;;     (implies (bvecp x 1)
;; 	     (equal (logand 1 x) x)))

(local
(defthmd logand-expt-3-bvequal
  (implies (and (integerp x)
                (integerp y)
                (natp n)
                (natp k)
                (natp i)
                (<= k n)
                (< i n))
           (equal (bitn (logand x (+ (expt 2 n)
                                     (* -1 (expt 2 k))))
                        i)
                  (bitn (* (expt 2 k)
                           (bits x (+ -1 n) k)) i)))
  :hints (("Goal" :use ((:instance bitn-logand-bvequal
                                   (x x)
                                   (y (+ (expt 2 n)
                                         (* -1 (expt 2 k))))
                                   (n i)))
           :in-theory (e/d (bitn-expt-expt-i
                            logand-ones-g-specific
                            bitn-shift-fact-expt
                            bitn-bits)
                           ()))))
)

(local
(defthmd  bvequal-logand-expt-3
  (implies (and (integerp x)
                (integerp y)
                (natp n)
                (natp k)
                (<= k n)
                (natp i)
                (<= i n))
           (bvequal (logand x (+ (expt 2 n)
                                 (* -1 (expt 2 k))))
                    (* (expt 2 k)
                       (bits x (+ -1 n) k))
                    i))
  :hints (("Goal" :in-theory (e/d (bvequal sumbits
                                           logand-expt-3-bvequal
                                           bitn-bits) (bits-logand)))))
)

(local
(defthmd bvecp-logand-specific-2
  (implies (and (natp k)
                (natp n)
                (<= k n)
                (integerp x))
           (bvecp (LOGAND X (+ (expt 2 n)
                               (* -1 (EXPT 2 K)))) n))
  :hints (("Goal" :use ((:instance logand-bvecp-g
                                   (x (+ (expt 2 n)
                                         (* -1 (expt 2 k))))
                                   (y x)
                                   (n n)))
           :cases ((bvecp (+ (expt 2 n)
                             (* -1 (expt 2 k))) n)))
          ("Subgoal 2" :in-theory (e/d (bvecp) ()))))
)

(local
(defthmd bvecp-logand-specific-3
  (implies (and (natp k)
                (natp n)
                (<= k n)
                (integerp x))
           (bvecp (* (expt 2 k)
                     (bits X (+ -1 n) k)) n))
  :hints (("Goal" :in-theory (e/d (bvecp) ())
           :cases ((bvecp (bits x (+ -1 n) k)
                          (+ n (* -1 k)))))
          ("Subgoal 1" :cases ((equal (expt 2 (+ n (* -1 k)))
                                      (* (expt 2 n)
                                         (/ (expt 2 k))))))
          ("Subgoal 1.1" :in-theory (e/d (bvecp) (EXPT-COMPARE-EQUAL)))))
       )



(defthmd logand-expt-3-g
    (implies (and (integerp x)
		  (natp n)
		  (natp k)
		  (< k n))
	     (equal (logand x (+ (expt 2 n) (- (expt 2 k))))
		    (* (expt 2 k) (bits_alt x (1- n) k))))
  :hints (("Goal" :in-theory (e/d (bits_alt-is-bits
                                   bvecp-logand-specific-3
                                   bvecp-logand-specific-2
                                   bvequal-logand-expt-3) (bits-logand))
             :use ((:instance bvequal-then-equal
                              (n n)
                              (x (logand x (+ (expt 2 n)
                                              (* -1 (expt 2 k)))))
                              (y (* (expt 2 k)
                                    (bits x (+ -1 n) k))))))))


;;;;

(defthmd lognot-shift
  (implies (and (integerp x)
                (natp k))
           (equal (lognot (* (expt 2 k) x))
		  (+ (* (expt 2 k) (lognot x))
		     (1- (expt 2 k)))))
  :hints (("Goal" :in-theory (e/d (lognot) ()))))




;;               (defthmd mod-2-expt-2-is-zero
;;                 (implies (and (integerp n)
;;                               (> n 0)
;;                               (integerp x))
;;                          (equal (mod (* x (expt 2 n)) 2)
;;                                 0))
;;                 :hints (("Goal" :in-theory (e/d (mod) ()))))

;;               (defthmd integer-decompose
;;                 (implies (integerp y)
;;                          (equal (FL (* 1/2 Y))
;;                                 (* 1/2 (- y (mod y 2)))))
;;                 :hints (("Goal" :in-theory (e/d (mod evenp) ()))))


(defthmd logand-shift
    (implies (and (integerp x)
		  (integerp y)
		  (natp k))
	     (equal (logand (* (expt 2 k) x)
			    (* (expt 2 k) y))
		    (* (expt 2 k) (logand x y))))
    :hints (("Goal" :induct (logop-2-n-induct (* (expt 2 k) x)
                                              (* (expt 2 k) y)
                                              k)
             :in-theory (e/d (mod-2-expt-2-is-zero
                              expt-2-reduce-leading-constant) ()))
            ("Subgoal *1/2" :use ((:instance logand-def
                                             (i (* (expt 2 k) x))
                                             (j (* (expt 2 k) y)))))))



(defthmd logxor-shift
    (implies (and (integerp x)
		  (integerp y)
		  (natp k))
	     (equal (logxor (* (expt 2 k) x)
			    (* (expt 2 k) y))
		    (* (expt 2 k) (logxor x y))))
    :hints (("Goal" :induct (logop-2-n-induct (* (expt 2 k) x)
                                              (* (expt 2 k) y)
                                              k)
             :in-theory (e/d (mod-2-expt-2-is-zero
                              expt-2-reduce-leading-constant) ()))
            ("Subgoal *1/2" :use ((:instance logxor-def
                                             (i (* (expt 2 k) x))
                                             (j (* (expt 2 k) y)))))))



(defthmd logior-shift
    (implies (and (integerp x)
		  (integerp y)
		  (natp k))
	     (equal (logior (* (expt 2 k) x)
			    (* (expt 2 k) y))
		    (* (expt 2 k) (logior x y))))
    :hints (("Goal" :induct (logop-2-n-induct (* (expt 2 k) x)
                                              (* (expt 2 k) y)
                                              k)
             :in-theory (e/d (mod-2-expt-2-is-zero
                              expt-2-reduce-leading-constant) ()))
            ("Subgoal *1/2" :use ((:instance logior-def
                                             (i (* (expt 2 k) x))
                                             (j (* (expt 2 k) y)))))))


;;;;;
;;;;;

;; (defthm fl-lognot
;;   (implies (case-split (integerp i))
;;            (= (fl (* 1/2 (lognot i)))
;;               (lognot (fl (* 1/2 i)))))
;;   :hints (("Goal" :in-theory (enable lognot))))

(encapsulate ()
             (local (include-book "../support/lognot"))


             (defthm fl-lognot
               (implies (case-split (integerp i))
                        (= (fl (* 1/2 (lognot i)))
                           (lognot (fl (* 1/2 i))))))


             )


;; We already have this
;;
;; (defthm fl-logand-by-2
;;   (implies (and (case-split (integerp i))
;;                 (case-split (integerp j))
;;                 )
;;            (equal (fl (* 1/2 (logand i j)))
;;                   (logand (fl (* 1/2 i)) (fl (* 1/2 j))))))
;;
;; easy. Mon Feb  9 17:20:12 2009

(defun fl-induct (x y k)
  (if (zp k)
      (list x y k)
    (fl-induct  (fl (* 1/2 x))
                (fl (* 1/2 y))
                (+ -1 k))))




(defthmd fl-logand
  (implies (and (integerp x)
                (integerp y)
                (natp n)
                (natp k))
           (equal (fl (/ (logand x y) (expt 2 k)))
                  (logand (fl (/ x (expt 2 k))) (fl (/ y (expt 2 k))))))
  :hints (("Goal" :induct (fl-induct x y k))
          ("Subgoal *1/2" :use ((:instance fl-logand-by-2
                                           (i x)
                                           (j y)))
           :in-theory (e/d ()
                           (fl-logand-by-2)))
          ("Subgoal *1/2'''" :in-theory (e/d (expt-2-reduce-leading-constant)
                                             ()))))


(defthmd fl-logior
  (implies (and (integerp x)
                (integerp y)
                (natp n)
                (natp k))
           (equal (fl (/ (logior x y) (expt 2 k)))
                  (logior (fl (/ x (expt 2 k))) (fl (/ y (expt 2 k))))))
  :hints (("Goal" :induct (fl-induct x y k))
          ("Subgoal *1/2" :use ((:instance fl-logior-by-2
                                           (i x)
                                           (j y)))
           :in-theory (e/d ()
                           (fl-logior-by-2)))
          ("Subgoal *1/2'''" :in-theory (e/d (expt-2-reduce-leading-constant)
                                             ()))))

(defthmd fl-logxor
  (implies (and (integerp x)
                (integerp y)
                (natp n)
                (natp k))
           (equal (fl (/ (logxor x y) (expt 2 k)))
                  (logxor (fl (/ x (expt 2 k))) (fl (/ y (expt 2 k))))))
  :hints (("Goal" :induct (fl-induct x y k))
          ("Subgoal *1/2" :use ((:instance fl-logxor-by-2
                                           (i x)
                                           (j y)))
           :in-theory (e/d ()
                           (fl-logxor-by-2)))
          ("Subgoal *1/2'''" :in-theory (e/d (expt-2-reduce-leading-constant)
                                             ()))))

;;;;;
;;;;;

;;;**********************************************************************
;;;                Algebraic Properties
;;;**********************************************************************

(encapsulate ()
             (local (include-book "../support/lognot"))

             (defthm lognot-lognot
               (implies (case-split (integerp i))
                        (equal (lognot (lognot i))
                               i))))

(defthm logand-x-0
    (equal (logand x 0) 0))

(defthm logand-0-y
    (equal (logand 0 y) 0))

(defthm logior-x-0
    (implies (integerp x)
	     (equal (logior x 0) x)))

(defthm logior-0-y
    (implies (integerp y)
	     (equal (logior 0 y) y)))

(defthm logxor-x-0
    (implies (integerp x)
	     (equal (logxor x 0) x)))

(defthm logxor-0-y
    (implies (integerp y)
	     (equal (logxor 0 y) y)))

(defthm logand-self
  (implies (case-split (integerp i))
           (equal (logand i i) i)))

(defthm logior-self
    (implies (case-split (integerp i))
	     (equal (logior i i) i)))


(defthm logxor-self
  (equal (logxor i i) 0))

(defthm logand-x-m1
    (implies (integerp x)
	     (equal (logand x -1) x)))

(defthm logand-m1-y
    (implies (integerp y)
	     (equal (logand -1 y) y)))

(encapsulate ()
  (local (include-book "../support/merge"))
  (defthm logand-1-x
    (implies (bvecp x 1)
	     (equal (logand 1 x) x))))

(defthm logand-x-1
    (implies (bvecp x 1)
	     (equal (logand x 1) x)))


(encapsulate ()
             (local (include-book "../support/logior"))
             (defthm logior-1-x
               (implies (bvecp x 1)
                        (equal (logior 1 x) 1))))

(defthm logior-x-1
  (implies (bvecp x 1)
           (equal (logior x 1) 1)))



(defthm logior-x-m1
    (implies (integerp x)
	     (equal (logior x -1) -1)))

(defthm logior-m1-y
    (implies (integerp y)
	     (equal (logior -1 y) -1)))

(defthm logxor-m1
    (implies (integerp x)
	     (equal (logxor x -1)
		    (lognot x))))

(defthm logand-commutative
    (equal (logand j i) (logand i j)))

(defthm logior-commutative
    (equal (logior j i) (logior i j)))

(defthm logxor-commutative
    (equal (logxor j i) (logxor i j)))

(defthm logand-associative
    (equal (logand (logand i j) k)
           (logand i (logand j k))))

(defthm logior-associative
    (equal (logior (logior i j) k)
	   (logior i (logior j k))))

(defthm logxor-associative
    (equal (logxor (logxor i j) k)
	   (logxor i (logxor j k))))

(DEFTHM LOGAND-COMMUTATIVE-2
  (EQUAL (LOGAND J I K) (LOGAND I J K)))


(DEFTHM LOGIOR-COMMUTATIVE-2
  (EQUAL (LOGIOR J I K) (LOGIOR I J K)))


(DEFTHM LOGXOR-COMMUTATIVE-2
  (EQUAL (LOGXOR J I K) (LOGXOR I J K)))


(DEFTHM LOGNOT-LOGXOR
  (AND (EQUAL (LOGXOR (LOGNOT I) J)
              (LOGNOT (LOGXOR I J)))
       (EQUAL (LOGXOR J (LOGNOT I))
              (LOGNOT (LOGXOR I J)))))


;; (DEFTHM LOGIOR-LOGAND
;;   (IMPLIES (AND (INTEGERP X)
;;                 (<= 0 X)
;;                 (INTEGERP Y)
;;                 (<= 0 Y)
;;                 (INTEGERP Z)
;;                 (<= 0 Z))
;;            (EQUAL (LOGIOR X (LOGAND Y Z))
;;                   (LOGAND (LOGIOR X Y) (LOGIOR X Z))))
;;   :RULE-CLASSES NIL)

;; fl-logand-by-2

(defthm mod-2-0-1
  (implies (integerp x)
           (or (equal (mod x 2) 1)
               (equal (mod x 2) 0)))
  :rule-classes nil)



(defun logop-3-induct-g (x y z)
  (declare (xargs :measure (+ (nfix (abs x)) (nfix (abs y)) (nfix (abs z)))))
  (if (and (integerp x) (integerp y) (integerp z))
      (if (and (or (equal x 0)
                   (equal x -1))
               (or (equal y 0)
                   (equal y -1))
               (or (equal z 0)
                   (equal z -1)))
	  t
	(logop-3-induct-g (fl (/ x 2)) (fl (/ y 2)) (fl (/ z 2))))
    t))



(defthmd logior-logand-specific
  (implies (integerp x)
           (equal (LOGAND (LOGIOR (MOD X 2) (MOD Y 2))
                          (LOGIOR (MOD X 2) (MOD Z 2)))
                  (logior (mod x 2) (logand (mod y 2) (mod z 2)))))
  :hints (("Goal" :use ((:instance mod-2-0-1
                                   (x x))
                        (:instance mod-2-0-1
                                   (x y))
                        (:instance mod-2-0-1
                                   (x z))))))



(defthmd logior-logand-g
  (implies (and (integerp x)
                (integerp y)
                (integerp z))
           (equal (logior x (logand y z))
                  (logand (logior x y) (logior x z))))
  :hints (("Goal" :induct (logop-3-induct-g x y z)
           :in-theory (e/d (logior-logand-specific) ()))
          ("Subgoal *1/2" :use ((:instance logior-def
                                           (i x)
                                           (j (logand y z)))
                                (:instance logand-def
                                           (i (logior x y))
                                           (j (logior x z)))))))




(defthmd logand-logior-specific
  (implies (integerp x)
           (equal (LOGior (LOGand (MOD X 2) (MOD Y 2))
                          (LOGand (MOD X 2) (MOD Z 2)))
                  (logand (mod x 2) (logior (mod y 2) (mod z 2)))))
  :hints (("Goal" :use ((:instance mod-2-0-1
                                   (x x))
                        (:instance mod-2-0-1
                                   (x y))
                        (:instance mod-2-0-1
                                   (x z))))))





(defthmd logand-logior-g
  (implies (and (integerp x)
                (integerp y)
                (integerp z))
    (equal (logand x (logior y z))
	   (logior (logand x y) (logand x z))))
  :hints (("Goal" :induct (logop-3-induct-g x y z)
           :in-theory (e/d (logand-logior-specific) ()))
          ("Subgoal *1/2" :use ((:instance logand-def
                                           (i x)
                                           (j (logior y z)))
                                (:instance logior-def
                                           (i (logand x y))
                                           (j (logand x z)))))))



(defthmd logior-logand-2
  (implies (and (integerp x)
                (integerp y)
                (integerp z))
           (equal (logand  (logior y z) x)
                  (logior (logand y x) (logand z x))))
  :hints (("Goal" :in-theory (e/d (logand-logior-g)))))



(defun logop-2-induct-g (x y)
  (declare (xargs :measure (+ (nfix (abs x)) (nfix (abs y)))))
  (if (and (integerp x) (integerp y))
      (if (and (or (equal x 0)
                   (equal x -1))
               (or (equal y 0)
                   (equal y -1)))
          t
        (logop-2-induct-g (fl (/ x 2)) (fl (/ y 2))))
    t))

(defthmd mod-lognot-is-lognot-mod
  (implies (integerp x)
           (equal (mod (lognot x) 2)
                  (+ 1 (* -1 (mod x 2)))))
  :hints (("Goal" :in-theory (e/d (lognot mod evenp) ()))))


(defthmd logxor-specific
  (implies (and (integerp x)
                (integerp y))
           (equal (LOGIOR (LOGAND (MOD X 2) (MOD (LOGNOT Y) 2))
                          (LOGAND (MOD Y 2) (MOD (LOGNOT X) 2)))
                  (LOGXOR (MOD X 2) (MOD Y 2))))
  :hints (("Goal" :use ((:instance mod-2-0-1
                                   (x x))
                        (:instance mod-2-0-1
                                   (x y))
                        (:instance mod-2-0-1
                                   (x (lognot x)))
                        (:instance mod-2-0-1
                                   (x (lognot y)))
                        (:instance mod-lognot-is-lognot-mod
                                   (x x))
                        (:instance mod-lognot-is-lognot-mod
                                   (x y))))))




(defthmd logxor-rewrite-2-g
  (implies (and (integerp x)
                (integerp y))
           (equal (logxor x y)
                  (logior (logand x (lognot y))
                          (logand y (lognot x)))))
  :hints (("Goal" :induct (logop-2-induct-g x y)
           :in-theory (e/d (logxor-specific) (logxor-commutative)))
          ("Subgoal *1/2" :use ((:instance logxor-def
                                           (i x)
                                           (j y))
                                (:instance logior-def
                                           (i (logand x (lognot y)))
                                           (j (logand y (lognot x))))))))




(defthmd log3-specific
  (equal (LOGIOR (LOGAND (MOD X 2) (MOD Y 2))
                 (LOGAND (MOD X 2) (MOD Z 2))
                 (LOGAND (MOD Y 2) (MOD Z 2)))
         (logior (logand (mod x 2) (mod y 2))
                 (logand (logxor (mod x 2)
                                 (mod y 2))
                         (mod z 2))))
  :hints (("Goal" :use ((:instance mod-2-0-1
                                   (x x))
                        (:instance mod-2-0-1
                                   (x y))
                        (:instance mod-2-0-1
                                   (x z))))))


(defthmd log3
  (implies (and (integerp x)
                (integerp y)
                (integerp z))
           (equal (logior (logand x y) (logior (logand x z) (logand y z)))
                  (logior (logand x y) (logand (logxor x y) z))))
  :hints (("Goal" :induct (logop-3-induct-g x y z)
           :in-theory (e/d (logop-3-induct-g
                            log3-specific)
                           ()))
          ("Subgoal *1/2" :use ((:instance logior-def
                                           (i (logand x y))
                                           (j (logior (logand x z)
                                                      (logand y z))))
                                (:instance logior-def
                                           (i (logand x y))
                                           (j (logand (logxor x y)
                                                      z)))))))



;;;;
