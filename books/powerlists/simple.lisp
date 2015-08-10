#|
This book verifies some simple properties about powerlists.  The examples all
come from Misra's wonderful "Powerlists: a structure for parallel recursion"
paper, published in ACM TOPLAS, Nov 1994.  The results are described in my own
paper "Defthms about zip and tie", UTCS tech report TR97-02.

To certify this book, I do the following:

    (ld ;; Newline to fool dependency scanner
      "defpkg.lisp")
    (certify-book "simple" 4)
|#

(in-package "POWERLISTS")
(include-book "algebra")
(include-book "arithmetic/top" :dir :system :load-compiled-file nil)

(set-verify-guards-eagerness 2)

;;; We begin with the reverse function.  We define this using the tie
;;; constructor, and we show that it is its own inverse.

(defun p-reverse (p)
  (if (powerlist-p p)
      (p-tie (p-reverse (p-untie-r p))
	     (p-reverse (p-untie-l p)))
    p))

(defthm reverse-reverse
  (equal (p-reverse (p-reverse x)) x))

;;; Next, we define reverse using the zip constructor.  We show that this is
;;; the same function as the one defined using tie.  Hence, it is its own
;;; inverse.

(defun p-reverse-zip (p)
  (if (powerlist-p p)
      (p-zip (p-reverse-zip (p-unzip-r p)) (p-reverse-zip (p-unzip-l p)))
    p))

(defthm reverse-zip
  (equal (p-zip (p-reverse x) (p-reverse y))
	 (p-reverse (p-zip y x))))

(defthm reverse-reverse-zip
  (equal (p-reverse-zip x) (p-reverse x))
  :rule-classes nil)

;;; Now, we define functions that rotate a powerlist to the left and right.
;;; Naturally, these functions are inverses of each other.

(defun p-rotate-right (x)
  "Rotate once to the right"
  (if (powerlist-p x)
      (p-zip (p-rotate-right (p-unzip-r x))
	     (p-unzip-l x))
    x))

(defun p-rotate-left (x)
  "Rotate once to the left"
  (if (powerlist-p x)
      (p-zip (p-unzip-r x)
	     (p-rotate-left (p-unzip-l x)))
    x))

(defthm rotate-left-right
  (equal (p-rotate-left (p-rotate-right x)) x))

(defthm rotate-right-left
  (equal (p-rotate-right (p-rotate-left x)) x))

;;; Here are some amusing identities.  From Misra:

;;; On the amusing identity: rev, rr and rl are the kind of functions that
;;; semi-commute:
;;;
;;;  rev * rr = rl * rev, where * denotes function composition
;;;
;;; or, more interestingly, the function rev * rr is its own inverse. You
;;; may look into some of the identities along this line. The amusing
;;; identity follows trivially:
;;;  rev * rr * rev *rr = rev * rr * rl * rev
;;; = { rr, rl are inverses of each other}
;;;   rev * rev
;;; = identity

(defthm reverse-rotate
  (equal (p-reverse-zip (p-rotate-right x))
	 (p-rotate-left (p-reverse-zip x))))

(defthm reverse-rotate-reverse-rotate
  (equal (p-reverse-zip
	  (p-rotate-right
	   (p-reverse-zip
	    (p-rotate-right x))))
	 x))

;;; Now, we consider shifting a powerlist by more than a single position.
;;; A simple definition follows.

(defun p-rotate-right-k (x k)
  (declare (xargs :guard (and (integerp k) (>= k 0))))
  (if (zp k)
      x
    (p-rotate-right (p-rotate-right-k x (1- k)))))

;;; Before considering a faster definition, we must learn some basic facts
;;; about the naturals.  Perhaps we should include the kaufmann's arithmetic
;;; books instead?

(defun natural-induction (x)
  (declare (xargs :guard (and (integerp x) (>= x 0))))
  "Induct on naturals"
  (if (or (zp x) (equal x 1))
      x
    (natural-induction (1- x))))

(defthm even-odd
  (implies (and (integerp k)
		(>= k 0)
		(not (integerp (* 1/2 k))))
	   (integerp  (+ -1/2 (* 1/2 k))))
  :hints (("Goal" :induct (natural-induction k))))

(defthm even-odd-2
  (implies (and (integerp k)
		(>= k 0)
		(not (integerp (* 1/2 k))))
	   (and (integerp (* (+ -1 K) 1/2))
		(<= 0 (* (+ -1 K) 1/2))))
  :hints (("Goal" :induct (natural-induction k))))


(defthm int-int+1
  (implies (integerp x)
	   (integerp (1+ x))))

(defthm simplify-1-1/2
  (equal (+ 1 -1/2 x) (+ 1/2 x)))

(defthm even-odd-3
  (implies (and (integerp k)
		(>= k 0)
		(not (integerp (* 1/2 k))))
	   (integerp (+ 1/2 (* 1/2 k))))
  :hints (("Goal"
	   :use ((:instance even-odd)
		 (:instance int-int+1 (x (+ -1/2 (* 1/2 k)))))
	   :in-theory (disable even-odd int-int+1))))

(defthm even-odd-4
  (implies (and (integerp k)
		(>= k 0)
		(not (integerp (* 1/2 k))))
	   (and (integerp (+ 1 (* (+ -1 K) 1/2)))
		(<= 0 (+ 1 (* (+ -1 K) 1/2)))))
  :hints (("Goal"
	   :use (:instance even-odd-2)
	   :in-theory (disable even-odd-2))))

;;; Now, we can define a faster rotation function.  Intuitively, this function
;;; shifts a powerlist k times by considering the odd- and even-indexed
;;; elements of the powerlist separately and shifting these by k/2.

(defun p-rotate-right-k-fast (x k)
  (declare (xargs :guard (and (integerp k) (>= k 0))))
  (if (powerlist-p x)
      (if (integerp (/ k 2))
	  (p-zip (p-rotate-right-k-fast (p-unzip-l x)
					(/ k 2))
		 (p-rotate-right-k-fast (p-unzip-r x)
					(/ k 2)))
	(p-zip (p-rotate-right-k-fast (p-unzip-r x)
				      (1+ (/ (1- k) 2)))
	       (p-rotate-right-k-fast (p-unzip-l x)
				      (/ (1- k) 2))))
    x))

;;; We now show that our "fast" rotation returns the same result as our earlier
;;; "slow" rotation.

(defthm rotate-right-k-base
  (implies (and (not (powerlist-p x))
		(integerp k)
		(<= 0 k))
	   (equal (p-rotate-right-k x k) x)))

(defthm rotate-right-k-lemma
  (implies (and (integerp k)
		(>= k 0))
	   (equal (p-rotate-right-k x k)
		  (if (not (powerlist-p x))
		      x
		    (if (integerp (/ k 2))
			  (p-zip (p-rotate-right-k (p-unzip-l x) (/ k 2))
				 (p-rotate-right-k (p-unzip-r x) (/ k 2)))
			(p-rotate-right (p-zip (p-rotate-right-k (p-unzip-l x)
								 (/ (1- k) 2))
					       (p-rotate-right-k (p-unzip-r x)
								 (/ (1- k)
								    2))))))))
  :hints (("Goal" :induct (natural-induction k)))
  :rule-classes nil)

(defthm rotate-right-k
  (implies (and (integerp k)
		(>= k 0))
	   (equal (p-rotate-right-k-fast x k)
		  (p-rotate-right-k x k)))
  :hints (("Goal" :induct (p-rotate-right-k-fast x k))
	  ("Subgoal *1/2" :use (:instance rotate-right-k-lemma))
	  ("Subgoal *1/1" :use (:instance rotate-right-k-lemma))))

;;; We now define the shuffle routines which shift not the elements of a
;;; powerlist, but the index of each element (in binary).

(defun p-right-shuffle (x)
  (if (powerlist-p x)
      (p-tie (p-unzip-l x) (p-unzip-r x))
    x))

(defun p-left-shuffle (x)
  (if (powerlist-p x)
      (p-zip (p-untie-l x) (p-untie-r x))
    x))

(defthm left-right-shuffle
  (equal (p-left-shuffle (p-right-shuffle x)) x))

(defthm right-left-shuffle
  (equal (p-right-shuffle (p-left-shuffle x)) x))

;;; We now define the invert routine which permutes a powerlist by taking
;;; the index of each element, reversing the index (011 -> 110), and placing
;;; the element at that new position index.  This is useful, for example, in
;;; the FFT computation.

(defun p-invert (x)
  (if (powerlist-p x)
      (p-zip (p-invert (p-untie-l x))
	     (p-invert (p-untie-r x)))
    x))

(defthm invert-zip
  (equal (p-invert (p-zip x y))
	 (p-tie (p-invert x) (p-invert y))))

(defthm invert-invert
      (equal (p-invert (p-invert x)) x))

(defthm invert-reverse
      (equal (p-invert (p-reverse x))
             (p-reverse (p-invert x))))

(defthm invert-zip-fn2
      (implies (p-similar-p x y)
               (equal (p-invert (a-zip-fn2 x y))
                      (a-zip-fn2 (p-invert x)
                                 (p-invert y)))))
