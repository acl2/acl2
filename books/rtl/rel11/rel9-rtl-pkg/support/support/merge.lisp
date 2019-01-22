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

#|
;This book is intended to include lemmas mixing two or types of functions.

History of this file:
David Russinoff created the original version of this file.  In
9/99, Matt Kaufmann modified some of the lemmas with an eye toward
increasing the automation provided by this book.  In the process,
some previous stylistic conventions fell by the wayside, such as
disabling :rewrite rules immediate after their statements.
In 7/2001, Eric Smith moved many of the lemmas into basic.lisp
and other books in the floating point library
In 6/2002-7/2002, Eric Smith made more changes to this book, incorporating some
lemmas from merge4.lisp, add.lisp, etc.

todo:

this book does a lot of including other books locally in encapsulates.  it'd be nice if books like
arithmetic/expt could be included in this book without breakign stuff

See also merge2.lisp.

|#
(local ; ACL2 primitive
 (defun natp (x)
   (declare (xargs :guard t))
   (and (integerp x)
        (<= 0 x))))

(defund bvecp (x k)
  (declare (xargs :guard (integerp k)))
  (and (integerp x)
       (<= 0 x)
       (< x (expt 2 k))))

(defund decode (x n)
  (declare (xargs :guard (rationalp n)))
  (if (and (natp x) (< x n))
      (ash 1 x)
    0))

(defund logior1 (x)
  (declare (xargs :guard t))
  (if (equal x 0) 0 1))

(include-book "ground-zero")
(include-book "log")
(include-book "float")  ;can't drop this, since exactp is used below...

(local (include-book "../../arithmetic/top"))

(local (include-book "bvecp"))
(local (include-book "bitn"))
(local (include-book "lnot")) ;make non-local?
(local (include-book "bits")) ;try making non-local?
(local (include-book "logior"))
(local (include-book "logand"))
(local (include-book "logxor"))
(local (include-book "ocat"))

(local (in-theory (enable expt-minus)))
(local (in-theory (enable expt-split)))

(defthm bits-tail
  (implies (and (bvecp x (1+ i))
                (case-split (acl2-numberp i)))
           (equal (bits x i 0)
                  x)))

(local (in-theory (enable bitn-mod))) ;BOZO why?

;proved in logior
(defthm logior-bvecp
  (implies (and (bvecp x n)
                (bvecp y n))
           (bvecp (logior x y) n)))


(encapsulate
 ()
 (local (defthm mod-n+1-1
          (implies (and (rationalp a);(integerp a)
;                        (>= a 0)
                        (integerp n)
                        (>= n 0))
                   (< (/ (mod a (expt 2 (1+ n))) (expt 2 n))
                      2))
          :rule-classes ()
          :hints (("goal" :in-theory (set-difference-theories
                                      (enable expt-split)
                                      '( *-weakly-monotonic))
                   :use ((:instance mod-bnd-1 (m a) (n (expt 2  (1+ n))))
                         (:instance *-weakly-monotonic
                                    (x (expt 2 n))
                                    (y 2)
                                    (y+ (/ (mod a (expt 2 (1+ n))) (expt 2 n)))))))))

 (local (defthm mod-n+1-2
          (implies (and (rationalp a) ;(integerp a)
                        ;(>= a 0)
                        (integerp n)
                        (>= n 0))
                   (< (fl (/ (mod a (expt 2 (1+ n))) (expt 2 n)))
                      2))
          :rule-classes ()
          :hints (("goal" :use (mod-n+1-1)))))

 (local (defthm mod-n+1-3
          (implies (and (rationalp a); (integerp a)
                        ;(>= a 0)
                        (integerp n)
                        (>= n 0))
                   (<= 0 (fl (/ (mod a (expt 2 (1+ n))) (expt 2 n)))))
          :rule-classes ()
          :hints (("goal" :use ( ;(:instance mod>=0 (m a) (n (expt 2 (1+ n))))
                                )))))

 (local (defthm mod-n+1-4
          (implies (and  (rationalp a) ;(integerp a)
;                        (>= a 0)
                        (integerp n)
                        (>= n 0))
                   (or (= (fl (/ (mod a (expt 2 (1+ n))) (expt 2 n))) 0)
                       (= (fl (/ (mod a (expt 2 (1+ n))) (expt 2 n))) 1)))
          :rule-classes ()
          :hints (("goal" :in-theory (disable EXPT-COMPARE expt-split)
                   :use (mod-n+1-2
                                mod-n+1-3)))))

 (local (defthm mod-n+1-5
          (implies (and (rationalp a) ;(integerp a)
  ;                      (>= a 0)
                        (integerp n)
                        (>= n 0))
                   (= (fl (/ (mod a (expt 2 (1+ n))) (expt 2 n)))
                      (mod (fl (/ (mod a (expt 2 (1+ n))) (expt 2 n))) 2)))
          :rule-classes ()
          :hints (("goal" :use (mod-n+1-4)))))

 (local (defthm mod-n+1-6
          (implies (and (rationalp a) ;(integerp a)
   ;                     (>= a 0)
                        (integerp n)
                        (>= n 0))
                   (= (fl (/ (mod a (expt 2 (1+ n))) (expt 2 n)))
                      (bitn (mod a (expt 2 (1+ n))) n)))
          :rule-classes ()
          :hints (("goal" :use (mod-n+1-5
                     ;			(:instance mod>=0 (m a) (n (expt 2 (1+ n))))
                                (:instance bitn-def (x (mod a (expt 2 (1+ n)))) (n n)))))))

 (local (defthm mod-n+1-7
          (implies (and (rationalp a) ;(integerp a)
    ;                    (>= a 0)
                        (integerp n)
                        (>= n 0))
                   (= (fl (/ (mod a (expt 2 (1+ n))) (expt 2 n)))
                      (bitn a n)))
          :rule-classes ()
          :hints (("goal" :in-theory (disable bitn-mod)
                   :use (mod-n+1-6
                         (:instance bitn-mod (x a) (n (1+ n)) (k n))
                         )))))

;export?  generalize?
 (local (defthm mod-n+1-8
          (implies (and (rationalp a) ;(integerp a)
     ;                   (>= a 0)
                        (integerp n)
                        (> n 0))
                   (= (mod (mod a (expt 2 (1+ n))) (expt 2 n))
                      (mod a (expt 2 n))))
          :rule-classes ()
          :hints (("goal" :use ((:instance mod-of-mod-cor (x a) (a (1+ n)) (b n)))))))

;like bitn-plus-bits
;bad name?
;should this be exported?
 (defthm mod-n+1
   (implies (and (rationalp a) ;(integerp a)
      ;           (>= a 0)
                 (integerp n)
                 (>= n 0)
                 )
            (= (mod a (expt 2 (1+ n)))
               (+ (* (bitn a n) (expt 2 n))
                  (mod a (expt 2 n)))))
   :rule-classes ()
   :hints (("goal" :use (mod-n+1-8
                         mod-n+1-7
                     ;			(:instance mod>=0 (m a) (n (expt 2 (1+ n))))
                         (:instance quot-mod (m (mod a (expt 2 (1+ n)))) (n (expt 2 n)))))))

 )

;prove from bits-mod-0?
(defthm mod-n-n+1
    (implies (and (rationalp a)
		  (integerp n)
		  (>= n 0)
                  )
	     (iff (= (mod a (expt 2 (1+ n))) 0)
		  (and (= (mod a (expt 2 n)) 0)
		       (= (bitn a n) 0))))
  :rule-classes ()
  :hints (("goal" :use ((:instance mod-n+1)
;			(:instance mod>=0 (m a) (n (expt 2 n)))
			(:instance bitn-0-1 (x a))))))

;prove without so many enables?
(defthm bitn-logxor-0
  (implies (and (integerp a)
                (integerp b)
                )
           (equal (bitn (+ a b) 0)
                  (bitn (logxor a b) 0)))
  :rule-classes ()
  :hints (("goal" :in-theory (enable
                              bits bitn
                              mod-by-2
                              integerp-sum-of-odds-over-2
                              ))))

;rename; is about fl...
;export?
;this is basically fl of sig
;move to somewhere in arithmetic/ ?
(defthmd mod-expo-1
  (implies (and (< 0 x)
                (rationalp x)
                )
           (equal (fl (/ x (expt 2 (expo x))))
                  1))
  :hints (("goal" :use ((:instance fl-unique (x (/ x (expt 2 (expo x)))) (n 1))))))

;move to somewhere in arithmetic/ ?
(defthmd mod-expo
  (implies (and (< 0 x)
                (rationalp x)
                )
           (equal (mod x (expt 2 (expo x)))
                  (- x (expt 2 (expo x)))))
  :hints (("goal" :in-theory (enable mod  mod-expo-1))))

(encapsulate
 ()
 (local (defthm mod-logxor-1
               (implies (and (integerp n) (>= n 1)
                             (integerp m) (>= m n)
                             (integerp x) (>= x 0) (< x (expt 2 m))
                             (integerp y) (>= y 0) (< y (expt 2 m)))
                        (= (mod (logxor x y) (expt 2 n))
                           (logior (mod (logand x (lnot y m)) (expt 2 n))
                                   (mod (logand y (lnot x m)) (expt 2 n)))))
               :rule-classes ()
               :hints (("goal" :use ((:instance logxor-rewrite (n m))
                                     (:instance mod-logior
                                                (x (logand x (lnot y m)))
                                                (y (logand y (lnot x m)))))))))


 (local (defthm mod-logxor-2
               (implies (and (integerp n) (>= n 1)
                             (integerp m) (>= m n)
                             (integerp x) (>= x 0) (< x (expt 2 m))
                             (integerp y) (>= y 0) (< y (expt 2 m)))
                        (= (mod (logxor x y) (expt 2 n))
                           (logior (logand (mod x (expt 2 n))
                                           (mod (lnot y m) (expt 2 n)))
                                   (logand (mod y (expt 2 n))
                                           (mod (lnot x m) (expt 2 n))))))
               :rule-classes ()
               :hints (("goal" :use (mod-logxor-1
                                     (:instance mod-logand (y (lnot y m)))
                                     (:instance mod-logand (x y) (y (lnot x m))))))))

 (local (defthm mod-logxor-3
               (implies (and (integerp n) (>= n 1)
                             (integerp m) (>= m n)
                             (integerp x) (>= x 0) (< x (expt 2 m))
                             (integerp y) (>= y 0) (< y (expt 2 m)))
                        (= (mod (logxor x y) (expt 2 n))
                           (logior (logand (mod x (expt 2 n))
                                           (lnot (mod y (expt 2 n)) n))
                                   (logand (mod y (expt 2 n))
                                           (lnot (mod x (expt 2 n)) n)))))
               :rule-classes ()
               :hints (("goal" :in-theory (disable lnot)
                        :use (mod-logxor-2
                              (:instance mod-lnot (x x) (k n) (n m))
                              (:instance mod-lnot (x y) (k n) (n m)))))))

 (local (defthm mod-logxor-4
               (implies (and (integerp n) (>= n 1)
                             (integerp m) (>= m n)
                             (integerp x) (>= x 0) (< x (expt 2 m))
                             (integerp y) (>= y 0) (< y (expt 2 m)))
                        (= (mod (logxor x y) (expt 2 n))
                           (logxor (mod x (expt 2 n))
                                   (mod y (expt 2 n)))))
               :rule-classes ()
               :hints (("goal" :in-theory (disable lnot)
                        :use (mod-logxor-3
                              (:instance logxor-rewrite (x (mod x (expt 2 n))) (y (mod y (expt 2 n))))
;			(:instance mod>=0 (m x) (n (expt 2 n)))
;		(:instance mod>=0 (m y) (n (expt 2 n)))
                              (:instance mod-bnd-1 (m x) (n (expt 2 n)))
                              (:instance mod-bnd-1 (m y) (n (expt 2 n))))))))



 (defthmd mod-logxor
   (implies (and (integerp n) (<= 0 n)
                 (integerp x) (<= 0 x)
                 (integerp y) (<= 0 y))
            (equal (mod (logxor x y) (expt 2 n))
                   (logxor (mod x (expt 2 n))
                           (mod y (expt 2 n)))))
   :hints (("goal" :in-theory (disable  expo-comparison-rewrite-to-bound
                                        expo-comparison-rewrite-to-bound-2)
            :use ((:instance mod-logxor-4 (m (max n (max (1+ (expo x)) (1+ (expo y))))))
                  (:instance expo>= (n (max n (max (1+ (expo x)) (1+ (expo y))))))
                  (:instance expo>= (n (max n (max (1+ (expo x)) (1+ (expo y))))) (x y)))))))

(defthm exact-bits-1
  (implies (and (equal (expo x) (1- n))
                (rationalp x)
                (integerp k)
                )
           (equal (integerp (/ x (expt 2 k)))
                  (exactp x (- n k))))
  :rule-classes ()
  :hints (("goal" :use ((:instance exactp2 (n (- n k)))))))

;strange rule?
(defthm exact-bits-2 ; exact-bits-a-c
  (implies (and (equal (expo x) (1- n))
                (rationalp x)
                (<= 0 x) ;or put abs in conclusion?
                (integerp k)
                )
           (equal (integerp (/ x (expt 2 k)))
                  (equal (bits x (1- n) k)
                         (/ x (expt 2 k)))))
  :rule-classes ()
  :hints (("goal" :in-theory (enable bits)
           :use ((:instance fl-int (x (/ x (expt 2 k))))
                 (:instance mod-does-nothing (m x) (n (expt 2 n)))
                 (:instance expo-upper-bound)))))

#|
;BOZO move?
;proved in mod-expt...
(defthm mod-integerp-when-y-is-power-of-2
  (implies (integerp x)
           (integerp (mod x (expt 2 i))))
  :rule-classes (:rewrite :type-prescription))
|#

(defthm exact-bits-3
  (implies (integerp x)
           (equal (integerp (/ x (expt 2 k)))
                  (equal (bits x (1- k) 0)
                         0)))
  :rule-classes ()
  :hints (("goal" :in-theory (enable bits)
           :use ((:instance quot-mod (m x) (n (expt 2 k)))))))

(defthm exact-bits-b-d
  (implies (and (equal (expo x) (1- n))
                (integerp x)
                (integerp k)
                )
           (equal (exactp x (- n k))
                  (equal (bits x (1- k) 0)
                         0)))
  :rule-classes ()
  :hints (("goal" :use (exact-bits-3 exact-bits-1))))


(encapsulate
 ()
 (local (defthm bvecp-exactp-aux
          (implies (and (case-split (natp n))
                        (bvecp x n))
                   (exactp x n))
          :hints (("Goal" :in-theory (set-difference-theories
                                      (enable expt-split zip bvecp natp)
                                      '())
                   :use ((:instance exact-bits-1 (n (1+ (expo x))) (k 0))
                         (:instance expo<= (n (1- n)))
                         (:instance expo>= (n 0))
                         (:instance exactp-<= (m (1+ (expo x)))))))))
 (defthm bvecp-exactp
   (implies (bvecp x n)
            (exactp x n))

   ))





#| kill this comment if all certifies..

;could combine these next two?

;BOZO move to bitn?
;BOZO enable!
(defthmd bvecp-bitn-0
  (implies (bvecp x n)
           (equal (bitn x n) 0))
  :hints (("Goal" :in-theory (enable bitn bvecp-bits-0))))


;BOZO move to bitn?
;make an alt version?
(defthm bitn-bvecp-0
  (implies (and (bvecp x n)
                (<= 0 m)
                )
           (equal (bitn x (+ m n)) 0))
  :hints (("Goal" :in-theory (disable bvecp-bitn-0)
           :use ((:instance bvecp-bitn-0 (n (+ m n)))))))

;move to bitn?
;k is a free var
;do we need this, if we have bvecp-longer?
(defthm bitn-bvecp-0-eric
  (implies (and (bvecp x k)
                (<= k n))
           (equal (bitn x n) 0))
  :rule-classes ((:rewrite :match-free :all))
  :hints (("Goal" :in-theory (enable bvecp-bitn-0))))

|#


;proved in bvecp.lisp...
(defthm bvecp-product
  (implies (and (bvecp x m)
                (bvecp y n)
                )
           (bvecp (* x y) (+ m n)))
  :rule-classes ())

;proved in bvecp.lisp...
(defthmd bvecp-1-rewrite
  (equal (bvecp x 1)
	 (or (equal x 0) (equal x 1)))
  :hints (("Goal" :in-theory (enable bvecp))))

;proved in bvecp.lisp...
(defthm bvecp-1-0
    (implies (and (bvecp x 1)
		  (not (equal x 1)))
	     (equal x 0))
  :rule-classes :forward-chaining)

#| kill if all certs
;sort of a "bitn-tail" like bits-tail?
(defthm bitn-bvecp-1
    (implies (bvecp x 1)
	     (equal (bitn x 0) x))
    :hints (("Goal" :in-theory (enable bvecp-1-rewrite))))



;rename
(defthmd bvecp-bitn-1
    (implies (and (bvecp x (1+ n))
		  (<= (expt 2 n) x)
                  (natp n))
	     (equal (bitn x n) 1))
  :hints (("Goal" :in-theory (enable bvecp)
           :use (bit-expo-b))))

|#

;add bitn-ash?

(defthm bitn-decode
  (implies (and (case-split (integerp x))
                (case-split (<= 0 x))
                (case-split (< x n))
                )
           (equal (bitn (decode x n) n2)
                  (if (equal x n2)
                      1
                    0)))
  :hints (("Goal" :in-theory (enable floor-fl decode ash)))
  )


;;;**********************************************************************
;;;                       LOGAND, LOGIOR, and LOGXOR
;;;**********************************************************************

;move a bunch of these:

;proved in log.lisp
(defthmd logxor-rewrite-2
    ;; ! Do we really want to get rid of logxor?
    (implies (and (bvecp x n)
		  (bvecp y n)
                  (natp n)
		  (not (= n 0)))
	     (equal (logxor x y)
		    (logior (logand x (lnot y n))
			    (logand y (lnot x n)))))
    :rule-classes ((:rewrite :match-free :all)))

;move!
(defthm logior-expt
    (implies (and (natp n)
		  (natp x)
		  (bvecp y n))
	     (= (logior (* (expt 2 n) x) y)
		(+ (* (expt 2 n) x) y)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable bvecp)
           :use (or-dist-b))))

;move!
(defthm logior-expt-2
    (implies (and (natp x)
		  (natp y)
		  (natp n))
	     (= (logior (* (expt 2 n) x)
			(* (expt 2 n) y))
		(* (expt 2 n) (logior x y))))
  :rule-classes ()
  :hints (("Goal" :use (or-dist-c))))

;move?
(defthm logand-bvecp
    (implies (and (natp n)
		  (bvecp x n)
		  (natp y))
	     (bvecp (logand x y) n))
  :hints (("Goal" :in-theory (enable bvecp)
           :use ( logand-bnd))))

;name doesn't match land0-expt
(defthm logand-expt
    (implies (and (natp x)
		  (natp y)
		  (natp n))
	     (= (logand (* (expt 2 n) x) y)
		(* (expt 2 n) (logand x (fl (/ y (expt 2 n)))))))
  :rule-classes ()
  :hints (("Goal" :use (and-dist-b))))

(defthm mod-logand-expt
    (implies (and (natp x)
		  (natp y)
		  (natp n))
	     (= (mod (logand x y) (expt 2 n))
		(logand (mod x (expt 2 n)) y)))
  :rule-classes ()
  :hints (("Goal" :use (mod-logand-aux))))

(defthm logand-mod-expt
    (implies (and (natp x)
		  (natp y)
		  (natp n)
		  (< x (expt 2 n)))
	     (= (logand x y)
		(logand x (mod y (expt 2 n)))))
  :rule-classes ()
  :hints (("Goal" :use (and-dist-d))))

#|
;proved in logxor...
(defthm logxor-bvecp
  (implies (and (bvecp x n)
                (bvecp y n)
                (natp n) ;gen?
                )
           (bvecp (logxor x y) n)))
|#

(defthm logand-expt-2
    (implies (and (natp x)
		  (natp k))
	     (= (logand x (expt 2 k))
		(* (expt 2 k) (bitn x k))))
  :rule-classes ()
  :hints (("Goal" :use (and-bits-a))))

(defthm logior-expt-3
    (implies (and (natp x)
		  (natp k))
	     (= (logior x (expt 2 k))
		(+ x
		   (* (expt 2 k)
		      (- 1 (bitn x k))))))
  :rule-classes ()
  :hints (("Goal" :use (and-bits-b))))

;;;**********************************************************************
;;;                            LNOT
;;;**********************************************************************

#|
test of having this commented out:

;proved in lnot.lisp
(defthm lnot-x-0
  (equal (lnot x 0) 0)
  :hints (("Goal" :in-theory (enable lnot))))

;proved in lnot.lisp
(defthm lnot-bvecp
  (implies (and (<= n k)
                (case-split (integerp k)))
           (bvecp (lnot x n) k)))

;proved in lnot.litp
(defthm bitn-lnot-not-equal
  (implies (and (< k n)
                (integerp n)
                (<= 0 n)
                (integerp k)
                (<= 0 k)
                )
           (not (= (bitn (lnot x n) k)
                   (bitn x k))))
  :hints (("Goal"; :in-theory (enable bvecp)
           :use (:instance bitn-0-1 (n k))
           ))
  :rule-classes ())
|#



;;**********************************************************************
;;                        NEW STUFF
;;**********************************************************************

(defun ls-induct (k x)
  (if (zp k)
      x
    (ls-induct (1- k) (fl (/ x 2)))))

(local (defthm lshiftamt-low-3-1
    (implies (and (integerp k) (> k 0))
	     (= (fl (/ (1- (expt 2 k)) 2))
		(1- (expt 2 (1- k)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable expt-split)
                              '())
           :use ((:instance fl-unique
                                   (x (/ (1- (expt 2 k)) 2))
                                   (n (1- (expt 2 (1- k))))))))))

(local (defthm lshiftamt-low-3-2
    (implies (and (integerp k) (> k 0))
	     (= (mod (1- (expt 2 k)) 2) 1))
  :rule-classes ()
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable expt-split)
                              '())
           :use ((:instance mod012 (m (1- (expt 2 k))))
			(:instance mod-mod-2-not-equal (m (1- (expt 2 k))))
			(:instance mod-2*i (i (expt 2 (1- k)))))))))



(local (defthm lshiftamt-low-3
    (implies (and (integerp k) (>= k 0)
		  (integerp x) (>= x 0) (< x (expt 2 k)))
	     (= (logior (1- (expt 2 k)) x)
		(1- (expt 2 k))))
  :rule-classes ()
  :hints (("Goal" :in-theory (e/d ( expt-split mod-mult-of-n) ( logior-even))
           :induct (ls-induct k x))
	  ("Subgoal *1/2" :use (lshiftamt-low-3-1
				lshiftamt-low-3-2
				(:instance mod012 (m x))
				(:instance quot-mod (m x) (n 2))
				(:instance quot-mod (m (logior (1- (expt 2 k)) x)) (n 2))
				(:instance fl-def-linear (x (/ x 2)))
                                )))))
;where used?
;this is sort of like logior-ones?
;BOZO kill or move this?
(local (defthm lshiftamt-low-4
              (implies (and (integerp k) (>= k 0)
                            (integerp x) (> x 0)
                            (= (expo x) k))
                       (= (logior x (1- (expt 2 k)))
                          (1- (expt 2 (1+ k)))))
              :rule-classes ()
              :hints (("Goal" :in-theory (e/d( expt-split) (EXPO-COMPARISON-REWRITE-TO-BOUND
                                                            expo-bound-eric
                                                            MOVE-NEGATIVE-CONSTANT-1
                                                            EXPO-COMPARISON-REWRITE-TO-BOUND-2))
                       :use (expo-upper-bound
                             expo-lower-bound
;			(:instance expt-pos (x k))
;			(:instance bit-basic-d (x (- x (expt 2 k))) (y (1- (expt 2 k))))
                             (:instance or-dist-b (n k) (x 1) (y (- x (expt 2 k))))
;			(:instance bit-basic-f (x (expt 2 k)) (y (- x (expt 2 k))) (z (1- (expt 2 k))))
                             (:instance lshiftamt-low-3 (x (- x (expt 2 k))))
                             (:instance or-dist-b (n k) (x 1) (y (1- (expt 2 k)))))))))


;;
;; ocat
;;


#|old definition
(defun OCAT (x y n)
  (+ (* (expt 2 n) x) y))
|#

;now always returns a nat
(defund ocat (x y n)
  (declare (xargs :guard t))
  (+ (* (expt 2 (nfix n)) (nfix x)) (nfix y)))


(defthm ocat-nonnegative-integer-type
  (and (integerp (OCAT X Y N))
       (<= 0 (OCAT X Y N)))
  :rule-classes (:type-prescription)
  )

;this rule is no better than ocat-nonnegative-integer-type and might be worse
(in-theory (disable (:type-prescription ocat)))

;just a rewrite rule
(defthm ocat-natp
  (natp (ocat x y n)))

;proved in ocat.lisp
(defthm ocat-bvecp
  (implies (and (>= k n) ;handle other case?
                (bvecp x (- k n))
                (case-split (natp n))
                (case-split (natp k))
                (case-split (bvecp y n))
                )
           (bvecp (ocat x y n) k)))

;add ocat-bvecp-rewrite!

;this has caused problems in the past (size information is lost)?
;proved in ocat.lisp
(defthm ocat-0-rewrite
    (implies (and (case-split (integerp x))
		  (case-split (<= 0 x)))
	     (equal (ocat 0 x n) x)))

;proved in ocat.lisp
(defthm ocat-associative
  (implies (and (case-split (<= 0 m)) ;new now that ocat fixes its args
                (case-split (<= 0 n)) ;new now that ocat fixes its args
                (case-split (integerp m))
                (case-split (integerp n))
                )
           (equal (ocat (ocat x y m) z n)
                  (ocat x (ocat y z n) (+ m n)))))

;;bits-ocat
;this stuff should be moved to cat? or ocat?
(defthm bits-ocat-1
  (implies (and (< i n)
                (case-split (natp y))
                (case-split (integerp i))
                (case-split (integerp j))
                (case-split (natp n))
                )
           (equal (bits (ocat x y n) i j)
                  (bits y i j)))
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable ocat)
                              '(;expt-2-integerp
                                ))
           :use (;(:instance mod-bits (x (ocat x y n))) ;try
;                 (:instance expt-2-integerp (i (- n (1+ i)))) ;elim?
;                 (:instance mod-mult-eric (y (expt 2 (1+ i))) (x y) (a (* x (expt 2 (- n (1+ i))))))
                 ))))

(defthm bits-ocat-2
  (implies (and (>= j n)
                (case-split (natp x))
                (case-split (bvecp y n))
                (case-split (natp n))
                (case-split (integerp i))
                (case-split (integerp j))
                )
           (equal (bits (ocat x y n) i j)
                  (bits x (- i n) (- j n))))
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable ocat bvecp)
                              '(ACL2::CANCEL_PLUS-EQUAL-CORRECT
                                ACL2::CANCEL_PLUS-LESSP-CORRECT))
           :use ((:instance fl-unique (x (/ (ocat x y n) (expt 2 n))) (n x))
                 (:instance bits-shift-down-1 (i (- i n)) (j (- j n)) (x (ocat x y n)) (k n))
                 ))))



(defthm bits-ocat-3
  (implies (and (>= i n)
                (< j n)
                (case-split (bvecp y n))
                (case-split (natp x))
                (case-split (natp n))
                (case-split (natp i))
                (case-split (natp j))
                )
           (equal (bits (ocat x y n) i j)
                  (ocat (bits x (- i n) 0)
                       (bits y (1- n) j)
                       (- n j))))
  :hints (("Goal" :in-theory (enable ocat bvecp-forward  bits-plus-mult-1)
           :use ((:instance bits-plus-bits (x (ocat x y n)) (p n) (n i) (m j)))
           )))

;includes both bits-ocat-1, bits-ocat-2, and bits-ocat-3
;we expect the indices to be constants, so this won't cause case-splits
(defthm bits-ocat
  (implies (and (case-split (bvecp y n))
                (case-split (natp x))
                (case-split (natp n))
                (case-split (natp i))
                (case-split (natp j))
                )
           (equal (bits (ocat x y n) i j)
                  (if (< i n)
                      (bits y i j)
                    (if (>= j n)
                        (bits x (- i n) (- j n))
                      (ocat (bits x (- i n) 0)
                           (bits y (1- n) j)
                           (- n j))))))
  :hints (("Goal" :in-theory (enable bvecp)))
  )

;bits-ocat should be all we need for simplifying (bits (ocat...))
(in-theory (disable bits-ocat-1 bits-ocat-2 bits-ocat-3))

;; bitn-ocat

(defthm bitn-ocat-1
  (implies (and (< i n)
                (case-split (natp n))
                (case-split (integerp i))
                (case-split (natp x))
                (case-split (natp y))
                )
           (equal (bitn (ocat x y n) i)
                  (bitn y i)))
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable bitn bits-ocat-1)
                              '()))))

(defthm bitn-ocat-2
  (implies (and (>= i n)
                (case-split (bvecp y n))
                (case-split (natp x))
                (case-split (natp n))
                (case-split (integerp i))
                )
           (equal (bitn (ocat x y n) i)
                  (bitn x (- i n))))
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable bitn)
                              '()))))

;includes both bitn-ocat-1 and bitn-ocat-2
(defthm bitn-ocat
  (implies (and (case-split (bvecp y n))
                (case-split (natp x))
                (case-split (natp n))
                (case-split (integerp i))
                )
           (equal (bitn (ocat x y n) i)
                  (if (< i n)
                      (bitn y i)
                    (bitn x (- i n)))))
  :hints (("Goal" :in-theory (enable bvecp))))

;bitn-ocat should be all we need for simplifying (bitn (ocat...))
(in-theory (disable bitn-ocat-1 bitn-ocat-2))


; The following rule allows us to relieve (integerp x) hypotheses when
; a rule applies to show (natp x).
;This rule can be very expensive.  We don't want to backchain to natp if all we need is integerp!
;Our plan is to enable natp in RTL proofs, so we disable this.
;move
(defthmd natp-integerp
  (implies (natp x)
           (integerp x)))

;proved in bitn...
(defthm bitn-bitn-0
  (equal (bitn (bitn x n) 0)
         (bitn x n)))

(include-book "sumbits") ; used in lemmas about cat, below (search for sumbits)

;BOZO proved in logior...
(defthm logior-ones
  (implies (and (natp n)
                (bvecp x n))
           (equal (logior x (1- (expt 2 n)))
                  (1- (expt 2 n))))
  :rule-classes ())

(defthm logxor-ones
  (implies (and (natp n)
                (bvecp x n) ;drop this hyp?
                )
           (equal (logxor x (1- (expt 2 n)))
                  (lnot x n)))
  :rule-classes ()
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable lnot bvecp)
                              '(lnot-bvecp))
           :use (lnot-bvecp
                 (:instance logxor-rewrite-2 (y (1- (expt 2 n))))
                 (:instance logand-ones (i (lnot x n)))))))




;(in-theory (disable bitn-bvecp-0)) ;why?

(defun logop-3-induct (x y z)
  (declare (xargs :measure (+ (nfix x) (nfix y) (nfix z))))
  (if (and (natp x) (natp y) (natp z))
      (if (and (zp x) (zp y) (zp z))
	  t
	(logop-3-induct (fl (/ x 2)) (fl (/ y 2)) (fl (/ z 2))))
    t))

(defun log3a (x y z)
  (logior (logand x y) (logior (logand x z) (logand y z))))

(defun log3b (x y z)
  (logior (logand x y) (logand (logxor x y) z)))

(local (in-theory (disable mod-equal-0 mod-by-2-rewrite-to-even)))

(local (defthm log3-1
    (implies (and (natp x) (natp y) (natp z)
		  (equal (log3a (fl (/ x 2)) (fl (/ y 2)) (fl (/ z 2)))
			 (log3b (fl (/ x 2)) (fl (/ y 2)) (fl (/ z 2)))))
	     (equal (log3a x y z)
		    (log3b x y z)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable)
		  :use ((:instance mod012 (m x))
			(:instance mod012 (m y))
			(:instance mod012 (m z))
			(:instance quot-mod (m (log3a x y z)) (n 2))
			(:instance quot-mod (m (log3b x y z)) (n 2)))))))

(defun logop-induct (x y z)
  (declare (xargs :measure (+ (nfix x) (nfix y) (nfix z))))
  (if (and (natp x) (natp y) (natp z))
      (if (and (zp x) (zp y) (zp z))
	  t
	(logop-induct (fl (/ x 2)) (fl (/ y 2)) (fl (/ z 2))))
    t))

;make a logtop book and put this in it?
;or move this to log.lisp?
(defthm log3
    (implies (and (natp x) (natp y) (natp z))
	     (equal (logior (logand x y) (logior (logand x z) (logand y z)))
		    (logior (logand x y) (logand (logxor x y) z))))
  :rule-classes ()
  :hints (("Goal" :induct (logop-induct x y z))
	  ("Subgoal *1/2" :use (log3-1))))




(defthm exact-k+1
    (implies (and (natp n)
		  (natp x)
		  (= (expo x) (1- n))
		  (natp k)
		  (< k (1- n))
		  (exactp x (- n k)))
	     (iff (exactp x (1- (- n k)))
		  (= (bitn x k) 0)))
  :rule-classes ()
  :hints (("Goal" :use (exact-bits-b-d
			(:instance exact-bits-b-d (k (1+ k)))
			(:instance bits-0-bitn-0 (n k))))))

;from bits.  included so i can disable it
(defthmd bits-reduce
  (implies (and (< x (expt 2 (+ 1 i)))
                (case-split (integerp x))
                (case-split (<= 0 x))
                (case-split (integerp i))
                )
           (equal (bits x i 0)
                  x)))

(in-theory (disable bits-tail)) ;yuck?


;===

;!! drop??
;or move to lnot?
(defthmd lnot-fl-rewrite
  (implies (and (not (zp n))
                (bvecp x n))
           (equal (fl (* 1/2 (lnot x n)))
                  (lnot (fl (* 1/2 x)) (1- n))))
  :hints (("Goal" :use ((:instance lnot-fl-original (k 1))))))

;(in-theory (enable logxor-bvecp)) ;why ever disabled?


(local (defthm lnot-logxor-1
    (implies (and (not (zp n))
		  (bvecp x n)
		  (bvecp y n)
		  (equal (lnot (logxor (fl (/ x 2)) (fl (/ y 2))) (1- n))
			 (logxor (lnot (fl (/ x 2)) (1- n)) (fl (/ y 2)))))
	     (equal (lnot (logxor x y) n)
		    (logxor (lnot x n) y)))
  :rule-classes ()
  :otf-flg t
  :hints (("Goal" :in-theory (e/d ( ;lnot-mod-by-2-alt ;drop?
                                     lnot-bvecp
				     lnot-fl-rewrite
                                     mod-lnot-by-2)
                                  ( LNOT-FL-eric))
		  :use ((:instance mod012 (m x))
			(:instance mod012 (m y))
			(:instance quot-mod (m (lnot (logxor x y) n)) (n 2))
			(:instance quot-mod (m (logxor (lnot x n) y)) (n 2)))))))

(defun logop2-induct (x y n)
  (if (zp n)
      (cons x y)
    (logop2-induct (fl (/ x 2)) (fl (/ y 2)) (1- n))))

;move up?
(defthm bvecp-fl
    (implies (and (not (zp n))
		  (bvecp x n))
	     (bvecp (fl (* 1/2 x)) (1- n)))
  :hints (("Goal" :in-theory (enable bvecp expt-split))))



(defthmd lnot-logxor
  (implies (and (natp n)
                (bvecp x n)
                (bvecp y n))
           (equal (lnot (logxor x y) n)
                  (logxor (lnot x n) y)))
  :hints (("Goal" :induct (logop2-induct x y n))
	  ("Subgoal *1/2" :use (lnot-logxor-1))))

;may be very expensive if we backchain from rationalp to integerp
;move
(defthmd integerp-rationalp
  (implies (integerp x)
           (rationalp x)))

;move
(defun logop-2-induct (x y)
  (if (or (zp x) (zp y))
      ()
    (logop-2-induct (fl (/ x 2)) (fl (/ y 2)))))

;move
(defun logop-2-n-induct (x y n)
  (if (zp n)
      (cons x y)
    (logop-2-n-induct (fl (/ x 2)) (fl (/ y 2)) (1- n))))

;move to log?
;not exported anywhere?
;BOZO put bitn in conclusion and gen hyp..
(defthm logand-1-x
    (implies (bvecp x 1)
	     (equal (logand 1 x) x))
  :hints (("Goal" :in-theory (enable bvecp-1-rewrite))))

(defthm ocat-bits-bits
  (implies (and (equal j (1+ k))
                (equal n (+ 1 (- l) k))
                (case-split (<= j i))
                (case-split (<= l k))
                (case-split (integerp i))
                (case-split (integerp k))
                (case-split (integerp l))
                )
           (equal (ocat (bits x i j) (bits x k l) n)
                  (bits x i l)))
  :hints (("Goal" :in-theory (enable ocat)
           :use ((:instance bits-plus-bits (n i) (p j) (m l))))))

(defthm ocat-bitn-bits
    (implies (and (equal j (+ 1 k))
		  (equal n (+ 1 (- l) k))
		  (case-split (<= l k))
		  (case-split (integerp j))
                  (case-split (integerp k))
                  (case-split (integerp l))
		  )
	     (equal (ocat (bitn x j) (bits x k l) n)
		    (bits x j l)))
    :hints (("Goal" :in-theory (set-difference-theories
                                (enable bitn)
                                '()))))

(defthm ocat-bits-bitn
  (implies (and (equal j (+ 1 k))
                (case-split (<= j i))
                (case-split (integerp i))
                (case-split (integerp j))
                (case-split (integerp k))
                )
           (equal (ocat (bits x i j) (bitn x k) 1)
                  (bits x i k)))
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable bitn)
                              '()))))

;perhaps just use bvecp-expo-rewrite?
(defthm bvecp-expo
  (implies (case-split (natp x))
           (bvecp x (+ 1 (expo x))))
  :hints (("Goal" :in-theory (enable bvecp)
           :use (expo-upper-bound))))

(defthm bvecp-expo-rewrite
  (equal (bvecp x (+ 1 (expo x)))
         (natp x)) ;rephrase to remove natp?
  :hints (("Goal" :in-theory (enable bvecp))))




;if leading bit is zero, can drop it
;move to bits?
;make this better? make more like this?
(defthmd lead-bit-0
  (implies (and (equal (bitn x n) 0)
                (bvecp x (+ 1 n))
                (rationalp n)
                )
           (equal (bits x (- n 1) 0)
                  x))
  :hints (("goal" :in-theory (enable bits-tail)
           :use ((:instance bitn-plus-bits
                                   (x x)
                                   (m 0)
                                   (n n) )))))

;Splits (bits x i j) into three pieces, where (bits x k l) is the middle piece.
;Not a rewrite rule since it does the same thing as ocat-bits-bits firing twice.
(defthm ocat-bits-bits-bits
  (implies (and (<= k i)
                (<= l k)
                (<= j l)
                (integerp i)
                (integerp j)
                (integerp k)
                (integerp l)
                )
           (equal (ocat (bits x i (+ 1 k))
                        (ocat (bits x k l)
                              (bits x (1- l) j)
                              (+ l (- j)))
                        (+ 1 (- j) k))
                  (bits x i j)))
  :rule-classes nil)



;make about cat and add to lib/
(defthm logior1-ocat
  (implies (and (case-split (bvecp y n))
                (case-split (natp x)))
           (equal (logior1 (ocat x y n))
                  (logior (logior1 x)
                          (logior1 y))))
  :hints (("Goal" :in-theory (enable logior1 bvecp))))

;move to bitn?
(defthm bitn-bits-gen
  (implies (and (case-split (<= 0 k))
                (case-split (integerp i))
                (case-split (integerp j))
                (case-split (integerp k))
                )
           (equal (bitn (bits x i j) k)
                  (if (<= k (- i j))
                      (bitn x (+ j k))
                    0)))
  :hints (("Goal" :in-theory (enable bitn-bits BVECP-BITN-0))))

(defthmd bvecp-shift-down
  (implies (and (bvecp x n)
                (natp n)
                (natp k))
           (bvecp (fl (/ x (expt 2 k))) (- n k)))
  :hints (("Goal" :in-theory (enable bvecp expt-split))))

;like bvecp-shift?  prove from that?
(defthmd bvecp-shift-up
    (implies (and (bvecp x (- n k))
                  ;(<= k n)
                  (natp k)
                  (integerp n) ;(natp n)
		  )
	     (bvecp (* x (expt 2 k)) n))
  :hints (("Goal" :in-theory (enable bvecp))))

;export!! enable?
;gen?
(defthmd expt2-of-non-integer-special
  (implies (case-split (not (integerp i)))
           (equal (expt 2 (+ 1 i))
                  (if (acl2-numberp i)
                      1
                    2))))

(local
 (defthm bits-sum-2
    (implies (and (integerp i)
                  (integerp j)
		  (>= i j)
		  (>= j 0)
                  )
	     (equal (+ (bits x i 0)
		       (bits y i 0))
		    (+ (* (expt 2 j)
			  (+ (bits x i j)
			     (bits y i j)
			     (bitn (+ (bits x (1- j) 0)
				      (bits y (1- j) 0))
				   j)))
		       (bits (+ (bits x (1- j) 0)
				(bits y (1- j) 0))
			     (1- j)
			     0))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance bits-plus-bits (n i) (p j) (m 0))
			(:instance bits-plus-bits (x y) (n i) (p j) (m 0))
			(:instance bitn-plus-bits (x (+ (bits x (1- j) 0) (bits y (1- j) 0))) (n j) (m 0)))))))



(defthm bits-sum-helper
  (implies (and (integerp x) ;logically necessary
                (integerp y) ;logically necessary
                (integerp i)
                )
           (equal (bits (+ x y) i j)
                  (bits (+ (bits x i j)
                           (bits y i j)
                           (bitn (+ (bits x (1- j) 0)
                                    (bits y (1- j) 0))
                                 j))
                        (- i j) 0)))
  :rule-classes nil
  :hints (("Goal" :use (bits-sum-2
;			bits-sum-6
			(:instance bits-plus-mult-1
				   (x (bits (+ (bits x (1- j) 0)
					       (bits y (1- j) 0))
					    (1- j)
					    0))
				   (y (+ (bits x i j)
					 (bits y i j)
					 (bitn (+ (bits x (1- j) 0)
						  (bits y (1- j) 0))
					       j)))
				   (k j)
				   (n i)
				   (m j))))))


;The hyps are logically necessary because the conclusion chops off those bits of x and y which are past the
;binary point.  (So the theorem is only true for integers, which have no such bits).
(defthm bits-sum-original
  (implies (and (integerp x)
                (integerp y)
                )
           (equal (bits (+ x y) i j)
                  (bits (+ (bits x i j)
                           (bits y i j)
                           (bitn (+ (bits x (1- j) 0)
                                    (bits y (1- j) 0))
                                 j))
                        (- i j) 0)))
  :rule-classes ()
  :hints (("subgoal 3" :use bits-sum-helper)
          ("Goal" :cases ((and (integerp i) (integerp j))
                          (and (integerp i) (not (integerp j)))
                          (and (not (integerp i)) (integerp j)))
           :in-theory (e/d () (BITN-IN-SUM-SPLIT-CASES)))))


#|
;helpful or not?
(defthm bitn-sum
  (implies (and (integerp x) ;logically necessary
                (integerp y) ;logically necessary
                )
           (equal (bitn (+ x y) n)
                  (bitn (+ (bitn x n)
                           (bitn y n)
                           (bitn (+ (bits x (1- n) 0)
                                    (bits y (1- n) 0))
                                 n))
                        0)))
  :rule-classes ()
  :hints (("Goal" :use (:instance bits-sum-original (i n) (j n))
           :in-theory (e/d (bitn) ()))))

(defthm bitn-of-integer-with-n-negative
  (implies (and (< n 0)
                (integerp x))
           (equal (bitn x n)
                  0))
  :hints (("Goal" :in-theory (e/d (bitn) ()))))

;generalize?
if we know that (bits x i j) = a constant, then we know what any sub-vector of (bits x i j) equals
(defthm bits-0-implies-subrange-0
  (implies (and (equal 0 (bits x i+ j)) ;j+ is a free var
                (< i i+)
                (integerp j+)
                (integerp i)
                )
           (equal (bits x i j)
                  0))
  :hints (("Goal" :use ((:instance bits-plus-bits (x x)
                                   (n i+)
                                   (m j)
                                   (p (+ 1 i)))))))



(defthm bits-sum-special-case-helper
  (implies (and (equal 0 (bits (+ x y) (1- j) 0))
                (natp i) (natp j) (natp x) (natp y))
           (equal (bitn (+ (bits x (1- j) 0)
                           (bits y (1- j) 0))
                        j)
                  (logior (bitn x (1- j)) (bitn y (1- j)))))
  :otf-flg t
  :hints (("Goal" :in-theory (disable BITN-KNOWN-NOT-0-REPLACE-WITH-1 BITS-SUM-1 BITS-SPLIT-AROUND-ZERO)
           :use ((:instance bits-plus-bits (x (+ (BITS X (+ -1 J) 0)
                                                 (BITS Y (+ -1 J) 0)))
                            (n j)
                            (m 0)
                            (p (+ -1 j)))
                 (:instance bits-sum-4 (i (+ -1 j)) (j 0))))))

(:instance bitn-plus-bits (x (+ (BITS X (+ -1 J) 0)
                                                 (BITS Y (+ -1 J) 0)))
                            (n (+ -1 j))
                            (m 0))

(defthm bits-sum-special-case-helper
  (implies (and (equal 0 (bits (+ x y) (1- j) 0))
                (natp i) (natp j) (natp x) (natp y))
           (equal (bitn (+ (bits x (1- j) 0)
                           (bits y (1- j) 0))
                        j)
                  (logior (bitn x (1- j)) (bitn y (1- j)))))
  :otf-flg t
  :hints (("Goal" :in-theory (disable BITN-KNOWN-NOT-0-REPLACE-WITH-1)
           :use ((:instance  bitn-sum (n (+ -1 j)))
))))
                 )))



(defthm bits-sum-special-case-helper
  (implies (and (equal 0 (bits (+ x y) (1- j) 0))
                (natp i) (natp j) (natp x) (natp y))
           (equal (bitn (+ (bits x (1- j) 0)
                           (bits y (1- j) 0))
                        j)
                  (logior (bitn x (1- j)) (bitn y (1- j)))))
  :otf-flg t
  :hints (("Goal" :in-theory (e/d () ()))))
           :use (

                 ))))





(defthm bits-sum-special-case-helper
  (implies (and (equal 0 (bits (+ x y) (1- j) 0))
                (natp i) (natp j) (natp x) (natp y))
           (equal (bitn (+ (bits x (1- j) 0)
                           (bits y (1- j) 0))
                        j)
                  (logior (bitn x (1- j)) (bitn y (1- j)))))
  :otf-flg t
  :hints (("Goal" :in-theory (disable BITN-KNOWN-NOT-0-REPLACE-WITH-1)
           :use ((:instance bitn-0-1 (x x) (n (+ -1 j)))
                 (:instance bitn-0-1 (x y) (n (+ -1 j)))
                 (:instance bitn-sum (n (+ -1 j)))
                 (:instance bitn-plus-bits (x x)
                                   (n (+ -1 j)) (m 0))
                 (:instance bitn-plus-bits (x y)
                                   (n (+ -1 j)) (m 0))
                 ))))



(defthm bits-sum-special-case-helper
  (implies (and (equal 0 (bits (+ x y) (1- j) 0))
                (natp i) (natp j) (natp x) (natp y))
           (equal (bitn (+ (bits x (1- j) 0)
                           (bits y (1- j) 0))
                        j)
                  (logior (bitn x (1- j)) (bitn y (1- j)))))
  :otf-flg t
  :hints (("Goal" :use ((:instance bitn-plus-bits (x (+ (bits x (1- j) 0)
                                                        (bits y (1- j) 0)))
                                   (n j) (m 0))
                        (:instance bitn-plus-bits (x x)
                                   (n (+ -1 j)) (m 0))
                        (:instance bitn-plus-bits (x y)
                                   (n (+ -1 j)) (m 0))
                        (:instance bitn-plus-bits (x (+ x y))
                                   (n (+ -1 j)) (m 0))
                        ))))


                        (:instance bitn-plus-bits (x (+ (bits x (1- j) 0)
                                                        (bits y (1- j) 0)))
                                   (n j) (m 0))

)




 )





(defthm bits-sum-special-case
    (implies (and (= (bits (+ x y) (1- j) 0) 0)
                  (natp x)
		  (natp y)
		  (natp i)
		  (natp j)
		  (>= i j)
		  (> j 0)
		  )
	     (equal (bits (+ x y) i j)
		    (bits (+ (bits x i j) (bits y i j) (logior (bitn x (1- j)) (bitn y (1- j))))
			  (- i j) 0)))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable BITN-IN-SUM-SPLIT-CASES
                                      BITN-KNOWN-NOT-0-REPLACE-WITH-1)
           :use (bits-sum-original
                 bits-sum-special-case-helper))))


(defthm bits-of-negative-integer
  (implies (and (integerp x)
                (< 0 x)) ;gen
           (equal (bits (- x) i j)
                  zz)))


;BOZO.  This looped!
(in-theory (disable BITN-DROP-CRUCIAL-BIT-AND-FLIP-RESULT-ALT-GEN))



;gen to any bits of any constant?
(defthm bits-of-constant-integer-down-to-0
  (implies (and (integerp x)
                (<= 0 x)
                (<= (expo x) i))
           (equal (bits x i 0)
                  (bits x (expo x) 0)))
  :hints (("Goal" :in-theory (enable bits-tail)))
  )

(defthm bits-1
  (implies (case-split (integerp i))
           (equal (bits 1 i 0)
                  (if (<= 0 i)
                      1
                    0))))



rewrite:

(defthm bits-less-than-x-rewrite
  (implies (and (natp i)
                (natp j)
                (natp x)
                (< 0 x)
                (<= j i)
                )
           (equal (< (bits x i j) x)
                  (if (< 0 j)
                      t
                    (if (<= i (expo x))
                        nil
                      t)))))


(defthm bits-x-equal-x
  (implies (and (natp i)
                (natp j)
                (natp x)
                (< 0 x)
                (<= j i)
                )
           (implies (equal (bits x i j) x)
                    (and (equal j 0)
                         (<= (expo x) i))))
  :rule-classes nil
  :hints (("goal" :in-theory (enable bits)))
  )

(defthm bits-1-gen
  (implies (and (case-split (integerp i))
                (case-split (integerp j))
                (case-split (<= 0 j))
                )
           (equal (bits 1 i j)
                  (if (< 1 j)
                      0
                    (if (<= 0 i)
                        1
                      0))))
  :hints (("Goal"; :in-theory (enable bits)
           :cases ((equal 0 j))))
  )



(defthm bits-with-indices-in-the-wrong-order-2
  (implies (case-split (< i j))
           (equal (bits x i j)
                  0)))

;;This should be in lib/ ???:
;prove from bits-sum-original ?
(defthm bits-sum-plus-1-original
    (implies (and (integerp x)
                  (integerp y)
		  (natp i)
		  (natp j)
		  (>= i j)
		  (>= j 0))
	     (equal (bits (+ 1 x y) i j)
		    (bits (+ (bits x i j)
			     (bits y i j)
			     (bitn (+ 1
				      (bits x (1- j) 0)
				      (bits y (1- j) 0))
				   j))
			  (- i j) 0)))
    :otf-flg t
  :rule-classes ()
  :hints (("Goal" :use ((:instance bits-sum-original (x (+ x y)) (y 1))
                        (:instance bits-sum-original))
))
)

  |#







;sort of a special case of another thm?
(local (defthm sticky-21-1
              (implies (and (= (bits (+ x y) (1- k) 0) 0)
                            (integerp x)
                            (integerp y)
                            )
                       (= (bits (+ (bits x (1- k) 0)
                                   (bits y (1- k) 0))
                                (1- k) 0)
                          0))
              :rule-classes ()
              :hints (("Goal" ;:in-theory (enable bits-mod)
                       :use ( ;(:instance mod-mod-sum (a x) (b y) (n (expt 2 k)))
                             )))))

;Either there is a carry or there isn't.
(local (defthm sticky-21-6
    (implies (and (= (bits (+ x y) (1- k) 0) 0)
                  (integerp x)
		  (integerp y)
;		  (natp k)
		  ;(> k 0)
		  )
	     (member (+ (bits x (1- k) 0)
			(bits y (1- k) 0))
		     (list (expt 2 k) 0)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable bits fl-equal-rewrite)
		  :use (;sticky-21-5
			sticky-21-1
			(:instance quot-mod
				   (m (+ (bits x (1- k) 0)
					 (bits y (1- k) 0)))
				   (n (expt 2 k))))))))

(local (defthm sticky-21-7
              (implies (and (integerp x)
                            (integerp y)
      ;                            (integerp k)
      ;                            (natp k)
      ;(>= k 2)
                            (= (bits (+ x y) (1- k) 0) 0)
                            (= (bitn x (1- k)) 0)
                            (= (bitn y (1- k)) 0))
                       (equal (+ (bits x (1- k) 0)
                                 (bits y (1- k) 0))
                              0))
              :rule-classes ()
              :hints (("Goal" :in-theory (enable   bits-of-non-integer-special)
                       :use (sticky-21-6
                             (:instance bitn-plus-bits (n (1- k)) (m 0))
                             (:instance bitn-plus-bits (x y) (n (1- k)) (m 0)))))))



(local (defthm sticky-21-8-2
    (implies (and (integerp x)
		  (integerp y)
		  (>= k 1)
		  (= (bits (+ x y) (1- k) 0) 0)
		  (or (= (bitn x (1- k)) 1)
		      (= (bitn y (1- k)) 1)))
	     (equal (+ (bits x (1- k) 0)
		       (bits y (1- k) 0))
		    (expt 2 k)))
  :rule-classes ()
  :hints (("Goal" :use (sticky-21-6
;			hack-8
;			hack-9
			(:instance bitn-plus-bits (n (1- k)) (m 0))
			(:instance bitn-plus-bits (x y) (n (1- k)) (m 0)))))))


;similar to another lemma
(local (defthm bitn+0
    (implies (and (integerp x)
		  (integerp y)
                  )
	     (= (bitn (+ x y) 0)
		(bitn (+ (bitn x 0) (bitn y 0)) 0)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable bitn-rec-0)
		  :use ((:instance mod-sum (a (bitn x 0)) (b y) (n 2))
			(:instance mod-sum (a y) (b x) (n 2)))))))

(local (defthm sticky-21-8-1
    (implies (and (integerp x)
		  (integerp y)
		  (= (bits (+ x y) 0 0) 0)
		  (or (= (bitn x 0) 1)
		      (= (bitn y 0) 1)))
	     (equal (+ (bits x 0 0)
		       (bits y 0 0))
		    2))
    :rule-classes ()
  :hints (("Goal" :in-theory (enable bits-n-n-rewrite ;yuck?
                                     )
		  :use (bitn+0
			(:instance bitn-0-1 (n 0))
			(:instance bitn-0-1 (x y) (n 0)))))))

;move
(defthmd bitn-of-non-integer-special
  (implies (case-split (not (integerp i)))
           (equal (bitn x i)
                  0)))

;move
;BOZO try enabled
(defthmd bitn-negative-bit-of-integer
  (implies (and (integerp x)
                (case-split (< i 0)))
           (equal (bitn x i)
                  0))
  :hints (("Goal" :in-theory (e/d (bitn) ()))))

(local (defthm sticky-21-8
              (implies (and (integerp x)
                            (integerp y)
                            (= (bits (+ x y) (1- k) 0) 0)
                            (or (= (bitn x (1- k)) 1)
                                (= (bitn y (1- k)) 1)))
                       (equal (+ (bits x (1- k) 0)
                                 (bits y (1- k) 0))
                              (expt 2 k)))
              :rule-classes ()
              :hints (("Goal" :in-theory (enable bitn-of-non-integer-special
                                                 bitn-negative-bit-of-integer)
                       :use (sticky-21-8-2
                             sticky-21-8-1)))))

(local (defthm sticky-21-9
    (implies (and (integerp x)
		  (integerp y)
;		  (natp k)
;		  (>= k 1)
		  (= (bits (+ x y) (1- k) 0) 0))
	     (equal (+ (bits x (1- k) 0)
		       (bits y (1- k) 0))
		    (* (expt 2 k)
		       (logior (bitn y (1- k))
			       (bitn x (1- k))))))
  :rule-classes ()
  :hints (("Goal" :use (sticky-21-7
			sticky-21-8
			(:instance bitn-0-1 (n (1- k)))
			(:instance bitn-0-1 (x y) (n (1- k))))))))

(local (defthm sticky-21-10
    (implies (and (integerp x)
		  (integerp y)
                  (integerp k)
;		  (natp k)
;		  (>= k 1)
;		  (natp n)
		  (>= n k)
		  (= (bits (+ x y) (1- k) 0) 0))
	     (equal (* (expt 2 k) (bits (+ x y) n k))
		    (bits (+ (bits x n 0) (bits y n 0))
			  n 0)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable mod-sum bits)
		  :use ((:instance bits-plus-bits (x (+ x y)) (n n) (p k) (m 0))
			;(:instance mod-mod-sum (a x) (b y) (n (expt 2 k)))
                        )))))

(local (defthm sticky-21-11
              (implies (and (integerp x)
                            (integerp y)
;                            (natp k)
;                            (> k 0)
;                            (natp n)
                            (>= n k)
                            (= (bits (+ x y) (1- k) 0) 0))
                       (equal (* (expt 2 k) (bits (+ x y) n k))
                              (bits (* (expt 2 k)
                                       (+ (bits x n k) (bits y n k) (logior (bitn x (1- k)) (bitn y (1- k)))))
                                    n 0)))
              :rule-classes ()
              :hints (("Goal" ; :in-theory (enable expt)
                       :use (sticky-21-10
                             sticky-21-9
                             (:instance bits-plus-bits (n n) (p k) (m 0))
                             (:instance bits-plus-bits (x y) (n n) (p k) (m 0)))))))

;export??? rename!
(local (defthm sticky-21
    (implies (and (integerp x)
		  (integerp y)
;		  (natp k)
		  (> k 0)
;		  (natp n)
		  (>= n k)
		  (= (bits (+ x y) (1- k) 0) 0))
	     (equal (bits (+ x y) n k)
		    (bits (+ (bits x n k) (bits y n k) (logior (bitn x (1- k)) (bitn y (1- k))))
			  (- n k) 0)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable bitn-of-non-integer-special)
           :use (sticky-21-11
			(:instance bits-shift-up-2
				   (x (+ (bits x n k) (bits y n k) (logior (bitn x (1- k)) (bitn y (1- k)))))
				   (i (- n k))))))))

;Used to be among the sticky lemmas.
;prove from bits-sum-original?
;BOZO gen!
(defthm bits-sum-special-case
  (implies (and (= (bits (+ x y) (1- j) 0) 0)
                (integerp x)
                (integerp y)
                (>= j 0) ;gen?
                )
           (equal (bits (+ x y) i j)
                  (bits (+ (bits x i j)
                           (bits y i j)
                           (logior (bitn x (1- j))
                                   (bitn y (1- j))))
                        (- i j) 0)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable bitn-negative-bit-of-integer)
           :use ((:instance sticky-21 (n i) (k j))))))




(local (defthm bits-sum-1-1
    (implies (and; (natp x)
;		  (natp y)
;		  (natp j)
                  (integerp j)
		  (>= j 0)
                  )
	     (equal (BITS (+ 1
			     (BITS X (+ -1 J) 0)
			     (BITS Y (+ -1 J) 0))
			  J 0)
		    (+ 1
		       (BITS X (+ -1 J) 0)
		       (BITS Y (+ -1 J) 0))))
  :hints (("Goal" :in-theory (union-theories (disable bits-bvecp) '(natp expt-split bvecp))
		  :use ((:instance bits-bvecp (i (1- j)) (j 0) (k j))
			(:instance bits-bvecp (x y) (i (1- j)) (j 0) (k j))
			(:instance bits-tail (x (+ 1 (BITS X (+ -1 J) 0) (BITS Y (+ -1 J) 0))) (i j)))))))

(local (defthm bits-sum-1-2
    (implies (and; (natp x)
;		  (natp y)
		  (natp i)
		  (natp j)
		  (>= i j)
		  (>= j 0))
	     (equal (+ 1
		       (bits x i 0)
		       (bits y i 0))
		    (+ (* (expt 2 j)
			  (+ (bits x i j)
			     (bits y i j)
			     (bitn (+ 1
				      (bits x (1- j) 0)
				      (bits y (1- j) 0))
				   j)))
		       (bits (+ 1
				(bits x (1- j) 0)
				(bits y (1- j) 0))
			     (1- j)
			     0))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance bits-plus-bits (n i) (p j) (m 0))
			(:instance bits-plus-bits (x y) (n i) (p j) (m 0))
			(:instance bitn-plus-bits (x (+ 1 (bits x (1- j) 0) (bits y (1- j) 0))) (n j) (m 0)))))))

(local (defthm bits-sum-1-3
    (implies (and; (natp x)
		 ; (natp y)
              (integerp x)
              (integerp y)
		  (natp i)
		  (natp j)
		  (>= i j)
		  (>= j 0))
	     (equal (mod (+ 1
			    (bits x i 0)
			    (bits y i 0))
			 (expt 2 (1+ i)))
		    (mod (+ 1 x y)
			 (expt 2 (1+ i)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (union-theories (disable expt) '(bits-mod))
		  :use ((:instance mod-sum (a (1+ (bits x i 0))) (b y) (n (expt 2 (1+ i))))
			(:instance mod-sum (a (1+ y)) (b x) (n (expt 2 (1+ i)))))))))

(local (defthm bits-sum-1-4
    (implies (and (integerp x)
                  (integerp y)
		  (natp i)
		  (natp j)
		  (>= i j)
		  (>= j 0))
	     (equal (bits (+ 1 x y) i j)
		    (bits (+ 1
			     (bits x i 0)
			     (bits y i 0))
			  i j)))
  :rule-classes ()
  :hints (("Goal" :use (bits-sum-1-3
			(:instance mod-bits-equal (x (+ 1 x y)) (y (+ 1 (bits x i 0) (bits y i 0)))))))))

(local (defthm bits-sum-1-5
    (implies (and (integerp x)
                  (integerp y)
		  (natp i)
		  (natp j)
		  (>= i j)
		  (>= j 0))
	     (equal (bits (+ 1 x y) i j)
		    (bits (+ (* (expt 2 j)
				(+ (bits x i j)
				   (bits y i j)
				   (bitn (+ 1
					    (bits x (1- j) 0)
					    (bits y (1- j) 0))
					 j)))
			     (bits (+ 1
				      (bits x (1- j) 0)
				      (bits y (1- j) 0))
				   (1- j)
				   0))
			  i j)))
  :rule-classes ()
  :hints (("Goal" :use (bits-sum-1-4 bits-sum-1-2)))))

(local (defthm bits-sum-1-6
    (implies (and (integerp x)
                  (integerp y)
		  (natp i)
		  (natp j)
		  (>= i j)
		  (>= j 0))
	     (< (bits (+ 1
			 (bits x (1- j) 0)
			 (bits y (1- j) 0))
		      (1- j)
		      0)
		(expt 2 j)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable bits-mod)
		  :use ((:instance mod-bnd-1 (m (+ 1 (bits x (1- j) 0) (bits y (1- j) 0))) (n (expt 2 j))))))))

;;This should be in lib/ ???:
;prove from bits-sum-original ?
#|
When we add two bit vectors of length n, we only need to look at 1 bit of carry.

When we add three bitvectors of length n, we need to consider 2 bits of carry.  However, when one of those
three bit vectors is 1, we need only consider 1 bit of carry.

|#
(defthm bits-sum-plus-1-original
    (implies (and (integerp x)
                  (integerp y)
		  (natp i)
		  (natp j)
		  (>= i j)
		  (>= j 0))
	     (equal (bits (+ 1 x y) i j)
		    (bits (+ (bits x i j)
			     (bits y i j)
			     (bitn (+ 1
				      (bits x (1- j) 0)
				      (bits y (1- j) 0))
				   j))
			  (- i j) 0)))
  :rule-classes ()
  :hints (("Goal" :use (bits-sum-1-5
			bits-sum-1-6
			(:instance bits-plus-mult-1
				   (x (bits (+ 1
					       (bits x (1- j) 0)
					       (bits y (1- j) 0))
					    (1- j)
					    0))
				   (y (+ (bits x i j)
					 (bits y i j)
					 (bitn (+ 1
						  (bits x (1- j) 0)
						  (bits y (1- j) 0))
					       j)))
				   (k j)
				   (n i)
				   (m j))))))




;generalize to remove bits from the LHS?
(defthm expo-bits-when-top-bit-is-1
  (implies (and (equal 1 (bitn x i))
                (case-split (<= j i))
                (case-split (integerp j))
		)
	   (equal (expo (bits x i j))
                  (+ i (- j))))
  :otf-flg t
  :hints (("Goal" :in-theory (disable EQUAL-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-RIGHT-HAND-SIDE)
           :use ((:instance expo-unique (x (bits x i j)) (n (+ i (- j))))
                 (:instance bitn-plus-bits (n i) (m j))))))

;generalize to remove bits from the LHS?
(defthm sig-bits-when-top-bit-is-1
  (implies (and (equal 1 (bitn x i))
                (case-split (<= j i))
                (case-split (integerp j))
		)
	   (equal (sig (bits x i j))
                  (/ (bits x i j) (expt 2  (+ i (- j))))))
  :hints (("Goal" :in-theory (enable sig))))


;hack for now:
;I could do this much better (if we know that (bits x i j) equals a constant, we know what any subrange equals.
(defthm bits-0-means-top-bit-0
  (implies (and (equal 0 (bits x i j))
                (<= j i)
                (integerp j)
                )
           (equal (bitn x i)
                  0))
  :hints (("Goal" :use (:instance bitn-plus-bits (n i) (m j)))))

;BOZO This can be kind of expensive. Add back-chain-limit?
(defthm bvecp-tighten
  (implies (and (equal (bitn x (1- n)) 0)
                (natp n))
           (equal (bvecp x n)
                  (bvecp x (1- n))))
  :hints (("Goal" :use (:instance bitn-plus-bits (n (1- n)) (m 0))
           :in-theory (e/d (bvecp)
                           (BITS-SPLIT-AROUND-ZERO
                            ;BITS-REDUCE-EXACTP
                            )))))

;add a bits-0-0-of-sig rule?
(defthm bitn-0-of-sig
  (implies (and (rationalp x)
                (not (equal x 0)))
           (equal (bitn (sig x) 0)
                  1))
  :hints (("Goal" :in-theory (e/d ( bitn bits) ()))))


;BOZO add
;disable?
(defthm bits-reduce-exactp
  (implies (and (equal i (expo x))
                (exactp x (+ 1 i (- j)))
                (integerp j)
                (rationalp x)
                (<= 0 x) ;drop?
                )
           (equal (bits x i j)
                  (/ x (expt 2 j))))
  :otf-flg t
  :hints (("Goal" :in-theory (enable exactp sig)
           :use ((:instance exact-bits-2 (n (+ 1 i)) (k j))
                 ;(:instance exact-bits-2 (x (- x)) (n (+ 1 i)) (k j))
                 ))))


(defthm fp-rep-collapse
  (implies (rationalp x)
           (equal (* (sig x) (expt 2 (expo x)))
                  (abs x)))
  :hints (("goal" :in-theory (enable sig)))
  )


#|

;move to somewhere else in library?
(defthm bitn-1
  (implies (and (equal (bitn x k) 1)
                (integerp x)
                (<= 0 x)
                )
           (>= x (expt 2 k)))
  :hints (("Goal"
           :use ((:instance bvecp-bitn-0 (x x) (n k)))
           :in-theory (enable bvecp)))
  :rule-classes nil
  )



|#

;BOZO, handle this right

(defmacro mod- (x y n)
  `(bits (- ,x ,y) (1- ,n) 0))

;This won't fire, since mod- is a macro?
(defthm mod--bvecp
  (bvecp (mod- x y n) n))

(include-book "cat")

(defthm lnot-cat
  (implies (and (case-split (natp n))
		(case-split (natp m))
		(equal l (+ m n)))
	   (equal (lnot (cat x m y n) l)
		  (cat (lnot x m) m (lnot y n) n)))
  :hints (("Goal" :use (:instance cat-upper-bound)
           :in-theory (e/d (lnot cat expt-split bits-reduce)
                           (cat-upper-bound)))))
