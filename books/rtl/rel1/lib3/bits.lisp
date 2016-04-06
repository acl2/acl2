;;;***************************************************************
;;;An ACL2 Library of Floating Point Arithmetic

;;;David M. Russinoff
;;;Advanced Micro Devices, Inc.
;;;August, 1999
;;; modified by Matt Kaufmann, AMD, September, 1999
;;;***************************************************************

(in-package "ACL2")

(local (include-book "../support/merge"))

(deflabel rtl-lib3-bits-start)

(defun fl (x) (floor x 1))

(defun cg (x) (- (fl (- x))))

; Change for v2-8:  Daron and Pete have deleted some stuff that is no longer
; necessary given their ordinals-related changes, in particular introduction of
; natp.

(in-theory (disable fl cg))


;;;**********************************************************************
;;;                             BITN
;;;**********************************************************************

(defun bvecp (x k)
  (and (integerp x)
       (>= x 0)
       (< x (expt 2 k))))

(in-theory (disable bvecp))

(defthm bvecp-forward
  (implies (bvecp x k)
           (and (integerp x)
                (<= 0 x)
                (< x (expt 2 k))))
  :rule-classes :forward-chaining)

(defthm natp-bvecp
    (implies (bvecp x n)
	     (natp x)))

(defun bitn (x n)
  (if (logbitp n x) 1 0))

(in-theory (disable bitn))

; Matt K. comment: deleted -- see the comment about April 2016 in
; books/rtl/rel1/support/logdefs.lisp, where natp-bitn is introduced as a
; :type-prescription rule.  It doesn't seem important for this to be a rewrite
; rule.
;(defthm natp-bitn
;    (natp (bitn x n))
;    :rule-classes (:type-prescription :rewrite))

(defthm bvecp-bitn
    (bvecp (bitn x n) 1))

; Keep the following rule disabled under normal circumstances!
(defthm bitn-rewrite
    (implies (and (natp x)
		  (natp k))
	     (equal (bitn x k)
		    (rem (fl (/ x (expt 2 k)))
			 2))))

(in-theory (disable bitn-rewrite))

(defthm bitn-0-0
    (implies (natp k)
	     (equal (bitn 0 k) 0)))

(defthm bitn-0-1
    (or (= (bitn x n) 0) (= (bitn x n) 1))
  :rule-classes ())

(defthm bitn-rec-0
    (implies (natp x)
	     (equal (bitn x 0)
		    (rem x 2))))

(in-theory (disable bitn-rec-0))

(defthm bitn-rec-pos-def
    (implies (and (natp x)
		  (natp k)
		  (> k 0))
	     (equal (bitn x k)
		    (bitn (fl (/ x 2)) (1- k))))
  :rule-classes ((:definition :controller-alist ((bitn t t))))
  ;; The following hint is not necessary, but is in keeping with our
  ;; desire to keep proof hacking out of the present file.
  :hints (("Goal" :by bitn-rec-pos)))

(in-theory (disable bitn-rec-pos-def))

(defthm bitn-rem-bitn
    (implies (and (natp x)
		  (natp n)
		  (natp k)
		  (> n k))
	     (equal (bitn (rem x (expt 2 n)) k)
		    (bitn x k))))

(defthm bitn-bvecp
    (implies (and (natp n)
		  (bvecp x n))
	     (equal (bitn x n) 0)))

(defthm bitn-force-1
    (implies (and (natp n)
		  (bvecp x (1+ n))
		  (<= (expt 2 n) x))
	     (equal (bitn x n) 1)))

(in-theory (disable bitn-force-1))

(defthm bitn-force-2
    (implies (and (bvecp x n)
		  (natp n)
		  (natp k)
		  (< k n)
		  (<= (- (expt 2 n) (expt 2 k)) x))
	     (equal (bitn x k) 1)))

(in-theory (disable bitn-force-2))

(defthm bitn-expt
    (implies (natp n)
	     (equal (bitn (expt 2 n) n) 1)))

(in-theory (disable bitn-expt))

(defthm bit+expt
    (implies (and (natp x)
		  (natp n))
	     (not (equal (bitn (+ x (expt 2 n)) n)
			 (bitn x n))))
  :rule-classes ())

(defthm bit+expt-2
    (implies (and (natp x)
		  (natp n)
		  (natp m)
		  (> m n))
	     (equal (bitn (+ x (expt 2 m)) n)
		    (bitn x n))))

(in-theory (disable bit+expt-2))

(defthm bitn+mult
    (implies (and (natp x)
		  (natp k)
		  (natp n)
		  (natp m)
		  (> m n))
	     (equal (bitn (+ x (* k (expt 2 m))) n)
		    (bitn x n))))

(in-theory (disable bitn+mult))

(defthm bitn-shift
    (implies (and (natp x)
		  (natp n)
		  (natp k))
	     (= (bitn (* x (expt 2 k)) (+ n k))
		(bitn x n)))
  :rule-classes ())

(defthm rem+bitn
    (implies (and (natp a)
		  (natp n))
	     (= (rem a (expt 2 (1+ n)))
		(+ (* (bitn a n) (expt 2 n))
		   (rem a (expt 2 n)))))
  :rule-classes ())

(defthm rem-bitn-0
    (implies (and (natp a)
		  (natp n))
	     (iff (= (rem a (expt 2 (1+ n))) 0)
		  (and (= (rem a (expt 2 n)) 0)
		       (= (bitn a n) 0))))
  :rule-classes ())

(defthm bitn-shift-2
    (implies (and (natp x)
		  (natp k)
		  (natp r))
	     (equal (bitn (fl (/ x (expt 2 r))) k)
		    (bitn x (+ k r)))))

(in-theory (disable bitn-shift-2))

(defthm bitn-shift-3
    (implies (and (natp n)
		  (natp m)
		  (natp k)
		  (bvecp x m)
		  (<= m n))
	     (equal (bitn (+ x (* k (expt 2 m))) n)
		    (bitn k (- n m)))))

(in-theory (disable bitn-shift-3))


;;;**********************************************************************
;;;                         BITS
;;;**********************************************************************

(defun bits (x i j)
  (fl (/ (rem x (expt 2 (1+ i))) (expt 2 j))))

(in-theory (disable bits))

(defthm rem-bits-equal
    (implies (and (natp x)
		  (natp y)
		  (natp i)
		  (natp j)
		  (= (rem x (expt 2 (1+ i))) (rem y (expt 2 (1+ i)))))
	     (= (bits x i j) (bits y i j)))
  :rule-classes ())

(defthm bits-0-0
    (implies (and (integerp i)
		  (integerp j)
		  (>= i 0))
	     (equal (bits 0 i j) 0)))

(defthm bits-n-n-rewrite
    (implies (and (natp x)
		  (natp n))
	     (equal (bits x n n)
		    (bitn x n))))

(in-theory (disable bits-n-n-rewrite))

(defthm natp-bits
    (implies (and (natp x)
		  (natp i)
		  (natp j))
	     (natp (bits x i j)))
  :rule-classes (:type-prescription :rewrite))

(defthm bvecp-bits
    (implies (and (natp x)
		  (natp i)
		  (natp j)
		  (= n (- (1+ i) j)))
	     (bvecp (bits x i j) n)))

(in-theory (disable bvecp-bits))

(defthm bits-tail
    (implies (and (natp n)
		  (bvecp x (1+ n)))
	     (equal (bits x n 0)
		    x)))

(defthm bits-rem
    (implies (and (integerp x)
		  (natp n))
	     (equal (bits x n 0)
		    (rem x (expt 2 (1+ n))))))

(in-theory (disable bits-rem))

(defthm bits-shift-1
    (implies (and (natp x)
		  (natp i)
		  (natp j)
		  (natp k))
	     (equal (bits (fl (/ x (expt 2 k)))
			  i
			  j)
		    (bits x (+ i k) (+ j k)))))

(in-theory (disable bits-shift-1))

(defthm bits-shift-2
    (implies (and (natp x)
		  (natp i)
		  (natp j)
		  (natp k)
		  (>= i (+ j k)))
	     (equal (bitn (bits x i j) k)
		    (bitn x (+ j k)))))

(in-theory (disable bits-shift-2))

(defthm bits-shift-3
    (implies (and (natp x)
		  (natp i)
		  (natp j)
		  (natp k)
		  (natp l)
		  (>= i (+ j k)))
	     (equal (bits (bits x i j) k l)
		    (bits x (+ k j) (+ l j)))))

(in-theory (enable bits-shift-3))

(defthm bits-0-rem-0
    (implies (and (natp x)
		  (natp m)
		  (natp n))
	     (iff (= (rem x (expt 2 (+ m n 1))) 0)
		  (and (= (bits x (+ m n) n) 0)
		       (= (rem x (expt 2 n)) 0))))
  :rule-classes ())

(defthm bits-0-bitn-0
    (implies (and (natp x)
		  (natp n)
		  (not (= n 0)))
	     (iff (= (bits x n 0) 0)
		  (and (= (bitn x n) 0)
		       (= (bits x (1- n) 0) 0))))
  :rule-classes ())

(defthm bits-plus-bits
    (implies (and (natp x)
		  (natp r)
		  (natp n)
		  (natp m)
		  (> n r)
		  (> m n))
	     (= (bits x (1- m) r)
		(+ (bits x (1- n) r)
		   (* (expt 2 (- n r)) (bits x (1- m) n)))))
  :rule-classes ())

(defthm bits-plus-bitn
    (implies (and (natp x)
		  (natp m)
		  (natp n)
		  (> n m))
	     (= (bits x n m)
		(+ (* (bitn x n) (expt 2 (- n m)))
		   (bits x (1- n) m))))
  :rule-classes ())

(defthm bitn-plus-bits
    (implies (and (natp x)
		  (natp n)
		  (natp m)
		  (> n m))
	     (= (bits x n m)
		(+ (bitn x m)
		   (* 2 (bits x n (1+ m))))))
  :rule-classes ())

(defthm bits-plus-mult
    (implies (and (natp m)
		  (natp n)
		  (>= n m)
		  (natp k)
		  (<= k m)
		  (natp y)
		  (bvecp x k))
	     (= (bits (+ x (* y (expt 2 k))) n m)
		(bits y (- n k) (- m k))))
  :rule-classes ())


;;;**********************************************************************
;;;                       LOGAND, LOGIOR, and LOGXOR
;;;**********************************************************************

(in-theory (disable logand logior logxor))

(defthm logand-rewrite
    (implies (and (natp x)
		  (natp y))
	     (equal (logand x y)
		    (+ (* 2 (logand (fl (/ x 2)) (fl (/ y 2))))
		       (logand (rem x 2) (rem y 2)))))
  :rule-classes ((:definition :controller-alist ((binary-logand t t)))))

(in-theory (disable logand-rewrite))

(defthm natp-logand
    (implies (and (natp i)
		  (natp j))
	     (natp (logand i j)))
  :rule-classes (:type-prescription :rewrite))

(defthm bvecp-logand
    (implies (and (natp n)
		  (bvecp x n)
		  (natp y))
	     (bvecp (logand x y) n)))

(in-theory (disable bvecp-logand))

(defthm logand-rem-2
    (implies (and (natp x)
		  (natp y))
	     (equal (rem (logand x y) 2)
		    (logand (rem x 2) (rem y 2)))))

(in-theory (disable logand-rem-2))

(defthm logand-fl-2
    (implies (and (natp x)
		  (natp y))
	     (equal (fl (/ (logand x y) 2))
		    (logand (fl (/ x 2)) (fl (/ y 2))))))

(in-theory (disable logand-fl-2))

(defthm logior-rewrite
    (implies (and (natp i)
		  (natp j))
	     (equal (logior i j)
		    (+ (* 2 (logior (fl (/ i 2)) (fl (/ j 2))))
		       (logior (rem i 2) (rem j 2)))))
  :rule-classes ((:definition :controller-alist ((binary-logior t t)))))

(in-theory (disable logior-rewrite))

(defthm natp-logior
    (implies (and (natp i)
		  (natp j))
	     (natp (logior i j)))
  :rule-classes (:type-prescription :rewrite))

(defthm bvecp-logior
    (implies (and (natp n)
		  (bvecp x n)
		  (bvecp y n))
	     (bvecp (logior x y) n)))

(in-theory (disable bvecp-logior))

(defthm logior-rem-2
    (implies (and (natp i)
		  (natp j))
	     (equal (rem (logior i j) 2)
		    (logior (rem i 2) (rem j 2)))))

(in-theory (disable logior-rem-2))

(defthm logior-fl-2
    (implies (and (natp i)
		  (natp j))
	     (equal (fl (/ (logior i j) 2))
		    (logior (fl (/ i 2)) (fl (/ j 2))))))

(in-theory (disable logior-fl-2))

(defthm logxor-def-rewrite
    (implies (and (natp x)
		  (natp y))
	     (equal (logxor x y)
		    (+ (* 2 (logxor (fl (/ x 2)) (fl (/ y 2))))
		       (logxor (rem x 2) (rem y 2)))))
  :rule-classes ((:definition :controller-alist ((binary-logxor t t)))))

(in-theory (disable logxor-def-rewrite))

(defthm natp-logxor
    (implies (and (natp i)
		  (natp j))
	     (natp (logxor i j)))
  :rule-classes (:type-prescription :rewrite))

(defthm bvecp-logxor
    (implies (and (natp n)
		  (bvecp x n)
		  (bvecp y n))
	     (bvecp (logxor x y) n)))

(in-theory (disable bvecp-logxor))

(defthm logxor-rem-2
    (implies (and (natp i)
		  (natp j))
	     (equal (rem (logxor i j) 2)
		    (logxor (rem i 2) (rem j 2)))))

(in-theory (disable logxor-rem-2))

(defthm logxor-fl-2
    (implies (and (natp i)
		  (natp j))
	     (equal (fl (/ (logxor i j) 2))
		    (logxor (fl (/ i 2)) (fl (/ j 2))))))

(in-theory (disable logxor-fl-2))

(defthm logand-0-y
    (equal (logand 0 y) 0))

(defthm logand-x-0
    (equal (logand x 0) 0))

(defthm logior-x-0
    (implies (natp x)
	     (equal (logior x 0) x)))

(defthm logxor-0-y
    (implies (integerp y)
	     (equal (logxor 0 y) y)))

(defthm logxor-x-0
    (implies (integerp x)
	     (equal (logxor x 0) x)))

(defthm logxor-self
    (implies (natp x)
	     (equal (logxor x x) 0)))

(defthm logior-not-0
    (implies (and (natp x)
		  (natp y)
		  (= (logior x y) 0))
	     (and (= x 0) (= y 0)))
  :rule-classes ())

(defthm logand-ones
    (implies (and (natp n)
		  (bvecp x n))
	     (equal (logand x (1- (expt 2 n)))
		    x)))

(in-theory (disable logand-ones))

(defthm logand-commutative
    (implies (and (integerp x)
		  (integerp y))
	     (equal(logand x y) (logand y x))))

(defthm logior-commutative
    (implies (and (integerp x)
		  (integerp y))
	     (equal (logior x y) (logior y x))))

(defthm logxor-commutative-rewrite
    (implies (and (integerp x)
		  (integerp y))
	     (equal (logxor x y) (logxor y x))))

(defthm logand-associative
    (implies (and (natp x)
		  (natp y)
		  (natp z))
	     (equal (logand (logand x y) z)
		    (logand x (logand y z)))))

(in-theory (disable logand-associative))

(defthm logior-associative
    (implies (and (natp x)
		  (natp y)
		  (natp z))
	     (equal (logior (logior x y) z)
		    (logior x (logior y z)))))

(in-theory (disable logior-associative))

(defthm logxor-associative
    (implies (and (natp x)
		  (natp y)
		  (natp z))
	     (equal (logxor (logxor x y) z)
		    (logxor x (logxor y z)))))

(in-theory (disable logxor-associative))

(defthm logior-logand
    (implies (and (natp x)
		  (natp y)
		  (natp z))
	     (equal (logior x (logand y z))
		    (logand (logior x y) (logior x z)))))

(in-theory (disable logior-logand))

(defthm logand-logior
    (implies (and (natp x)
		  (natp y)
		  (natp z))
	     (equal (logand x (logior y z))
		    (logior (logand x y) (logand x z)))))

(in-theory (disable logand-logior))

(defthm logior-logand-2
    (implies (and (natp x)
		  (natp y)
		  (natp z))
	     (equal (logand  (logior y z) x)
		    (logior (logand y x) (logand z x)))))

(in-theory (disable logior-logand-2))

(defthm logand-self
    (implies (natp x)
	     (equal (logand x x) x)))

(defthm logior-expt
    (implies (and (natp n)
		  (natp x)
		  (bvecp y n))
	     (= (logior (* (expt 2 n) x) y)
		(+ (* (expt 2 n) x) y)))
  :rule-classes ())

(defthm logior-expt-2
    (implies (and (natp x)
		  (natp y)
		  (natp n))
	     (= (logior (* (expt 2 n) x)
			(* (expt 2 n) y))
		(* (expt 2 n) (logior x y))))
  :rule-classes ())

(defthm rem-logior
    (implies (and (natp x)
		  (natp y)
		  (natp n))
	     (equal (rem (logior x y) (expt 2 n))
		    (logior (rem x (expt 2 n)) (rem y (expt 2 n))))))

(in-theory (disable rem-logior))

(defthm logand-bnd
    (implies (and (natp x)
		  (natp y))
	     (<= (logand x y) x))
  :rule-classes :linear)

(defthm logand-expt
    (implies (and (natp x)
		  (natp y)
		  (natp n))
	     (= (logand (* (expt 2 n) x) y)
		(* (expt 2 n) (logand x (fl (/ y (expt 2 n)))))))
  :rule-classes ())

(defthm rem-logand-expt
    (implies (and (natp x)
		  (natp y)
		  (natp n))
	     (= (rem (logand x y) (expt 2 n))
		(logand (rem x (expt 2 n)) y)))
  :rule-classes ())

(defthm rem-logand-rewrite
    (implies (and (natp x)
		  (natp y)
		  (natp n))
	     (equal (rem (logand x y) (expt 2 n))
		    (logand (rem x (expt 2 n)) (rem y (expt 2 n))))))

(in-theory (disable rem-logand-rewrite))

(defthm rem-logxor-rewrite
    (implies (and (natp x)
		  (natp y)
		  (natp n))
	     (equal (rem (logxor x y) (expt 2 n))
		    (logxor (rem x (expt 2 n))
			    (rem y (expt 2 n))))))

(in-theory (disable rem-logxor-rewrite))

(defthm logand-rem-expt
    (implies (and (natp x)
		  (natp y)
		  (natp n)
		  (< x (expt 2 n)))
	     (= (logand x y)
		(logand x (rem y (expt 2 n)))))
  :rule-classes ())

(defthm bitn-logand
    (implies (and (natp x)
		  (natp y)
		  (natp n))
	     (equal (bitn (logand x y) n)
		    (logand (bitn x n) (bitn y n)))))

(in-theory (disable bitn-logand))

(defthm bits-logand
    (implies (and (natp x)
		  (natp y)
		  (natp i)
		  (natp j)
		  (>= i j))
	     (equal (bits (logand x y) i j)
		    (logand (bits x i j) (bits y i j)))))

(in-theory (disable bits-logand))

(defthm bitn-logior
    (implies (and (natp x)
		  (natp y)
		  (natp n))
	     (equal (bitn (logior x y) n)
		    (logior (bitn x n) (bitn y n)))))

(in-theory (disable bitn-logior))

(defthm bits-logior
    (implies (and (natp x)
		  (natp y)
		  (natp i)
		  (natp j)
		  (>= i j))
	     (equal (bits (logior x y) i j)
		    (logior (bits x i j) (bits y i j)))))

(in-theory (disable bits-logior))

(defthm logxor-bitn
    (implies (and (natp x)
		  (natp y)
		  (natp n))
	     (equal (bitn (logxor x y) n)
		    (logxor (bitn x n) (bitn y n)))))

(in-theory (disable logxor-bitn))

(defthm bits-logxor
    (implies (and (bvecp x n)
		  (bvecp y n)
		  (natp n)
		  (natp i)
		  (natp j)
		  (> n i)
		  (>= i j))
	     (equal (bits (logxor x y) i j)
		    (logxor (bits x i j) (bits y i j)))))

(in-theory (disable bits-logxor))

(defthm bits-logxor-upper-slice
    (implies (and (equal n (+ 1 i))
                  (bvecp x n)
		  (bvecp y n)
		  (natp n)
		  (natp i)
		  (natp j)
		  (> n i)
		  (>= i j))
	     (equal (bits (logxor x y) i j)
		    (logxor (bits x i j) (bits y i j)))))

(defthm logand-expt-2
    (implies (and (natp x)
		  (natp k))
	     (= (logand x (expt 2 k))
		(* (expt 2 k) (bitn x k))))
  :rule-classes ())

(defthm logior-expt-3
    (implies (and (natp x)
		  (natp k))
	     (= (logior x (expt 2 k))
		(+ x
		   (* (expt 2 k)
		      (- 1 (bitn x k))))))
  :rule-classes ())

(defthm logand-expt-3
    (implies (and (natp x)
		  (natp n)
		  (natp k)
		  (< k n))
	     (= (logand x (- (expt 2 n) (expt 2 k)))
		(* (expt 2 k) (bits x (1- n) k))))
  :rule-classes ())

(defthm logand-expt-4
    (implies (and (natp n)
		  (natp k)
		  (natp l)
		  (< l k)
		  (<= k n))
	     (= (logand (- (1- (expt 2 n)) (expt 2 l)) (- (expt 2 n) (expt 2 k)))
		(- (expt 2 n) (expt 2 k))))
  :rule-classes ())

(defthm bitn-logxor-0
    (implies (and (natp a)
		  (natp b))
	     (= (bitn (+ a b) 0)
		(bitn (logxor a b) 0)))
  :rule-classes ())


;;;**********************************************************************
;;;                          COMP1, CAT, and SHFT
;;;**********************************************************************

(defun comp1 (x n)
  (1- (- (expt 2 n) x)))

(in-theory (disable comp1))

(defthm integerp-comp1-nat
    (implies (and (integerp x)
		  (natp n))
	     (integerp (comp1 x n)))
  :rule-classes (:type-prescription :rewrite))

(defthm natp-comp1
    (implies (and (natp n)
		  (bvecp x n))
	     (natp (comp1 x n)))
    :rule-classes
    ;; It seems a good idea to make this a :rewrite rule, not just a
    ;; :type-prescription rule, because of the bvecp hypothesis.
    (:type-prescription :rewrite)
    :hints (("Goal" :in-theory (enable bvecp natp comp1))))

(defthm comp1-comp1-rewrite
    (implies (and (integerp n)
		  (integerp x))
	     (equal (comp1 (comp1 x n) n)
                    x)))

(defthm comp1-fl
    (implies (and (natp n)
		  (natp k)
		  (<= k n)
		  (bvecp x n))
	     (= (fl (/ (comp1 x n) (expt 2 k)))
		(comp1 (fl (/ x (expt 2 k))) (- n k))))
  :rule-classes ())

(defthm rem-comp1-2
    (implies (and (natp n)
		  (not (= n 0))
		  (bvecp x n))
	     (not (= (rem (comp1 x n) 2)
		     (rem x 2))))
  :rule-classes ())

(defthm bvecp-comp1
    (implies (and (natp n)
		  (bvecp x n))
	     (bvecp (comp1 x n) n)))

(in-theory (disable bvecp-comp1))

(defthm bitn-comp1-not-equal
    (implies (and (natp n)
		  (bvecp x n)
		  (natp k)
		  (< k n))
	     (not (= (bitn (comp1 x n) k)
		     (bitn x k))))
  :rule-classes ())

(defthm bits-comp1
    (implies (and (natp m)
		  (natp i)
		  (natp j)
		  (> m i)
		  (>= i j)
		  (bvecp x m))
	     (equal (bits (comp1 x m) i j)
		    (comp1 (bits x i j) (1+ (- i j))))))

(in-theory (disable bits-comp1))

(defthm rem-comp1-rewrite
    (implies (and (natp n)
		  (natp m)
		  (bvecp x m)
		  (not (= n 0))
		  (>= m n))
	     (equal (rem (comp1 x m) (expt 2 n))
		    (comp1 (rem x (expt 2 n)) n))))

(in-theory (disable rem-comp1-rewrite))

(defthm logxor-rewrite-2
    (implies (and (bvecp x n)
		  (bvecp y n)
                  (natp n)
		  (not (= n 0)))
	     (equal (logxor x y)
		    (logior (logand x (comp1 y n))
			    (logand y (comp1 x n))))))

(in-theory (disable logxor-rewrite-2))

(defun cat (x y n)
  (+ (* (expt 2 n) x) y))

(in-theory (disable cat))

(defthm cat-nat
    (implies (and (natp x)
		  (natp y)
		  (natp n))
	     (natp (cat x y n)))
  :rule-classes (:type-prescription :rewrite))

(defthm bvecp-cat
    (implies (and (natp n)
		  (natp p)
		  (>= p n)
		  (bvecp x (- p n))
		  (bvecp y n))
	     (bvecp (cat x y n) p)))

(in-theory (disable bvecp-cat))

(defthm cat-0-rewrite
    (implies (natp x)
	     (equal (cat 0 x n) x)))

(defthm bitn-cat-1
    (implies (and (natp x)
		  (natp y)
		  (natp i)
		  (natp n)
		  (>= n (1+ i)))
	     (equal (bitn (cat x y n) i)
		    (bitn y i))))

(defthm bitn-cat-2
    (implies (and (natp n)
		  (natp i)
		  (>= i n)
		  (natp x)
		  (bvecp y n))
	     (equal (bitn (cat x y n) i)
		    (bitn x (- i n)))))

(defthm bits-cat-1
    (implies (and (natp x)
		  (natp y)
		  (natp j)
		  (natp i)
		  (natp n)
		  (>= n (1+ i)))
	     (equal (bits (cat x y n) i j)
		    (bits y i j))))

(defthm bits-cat-2
    (implies (and (natp n)
		  (natp j)
		  (>= j n)
		  (natp i)
		  (>= i j)
		  (natp x)
		  (bvecp y n))
	     (equal (bits (cat x y n) i j)
		    (bits x (- i n) (- j n)))))

(defun shft (x s l)
  (rem (fl (* (expt 2 s) x)) (expt 2 l)))

(in-theory (disable shft))

(defthm natp-shft
    (implies (and (natp x)
		  (natp n)
		  (integerp s))
	     (natp (shft x s n)))
  :rule-classes (:type-prescription :rewrite))

(defthm bvecp-shft
    (implies (and (natp x)
		  (natp n)
		  (integerp s))
	     (bvecp (shft x s n) n)))

(in-theory (disable bvecp-shft))

(include-book "../support/rewrite-theory")

(deftheory rtl-lib3-bits-theory
  (rewrite-theory 'rtl-lib3-bits-start))

