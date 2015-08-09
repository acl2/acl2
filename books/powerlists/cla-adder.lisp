#|

This book proves the correctness of a carry-lookahead adder, by showing that it
performs the same function as a simple ripple-carry adder.  It was suggested by
Jay Misra, after he reviewed the paper "Defthms About Zip and Tie", UTCS tech
report TR97-02, in which we proved (among other things) the correctness of two
prefix-sum algorithms.

To compile it, I do the following:

    (ld ;; newline to fool dependency scanner
     "defpkg.lisp")
    (certify-book "cla-adder" 4)
    (in-package "POWERLISTS")

|#

(in-package "POWERLISTS")
(include-book "prefix-sum" :load-compiled-file nil)
(include-book "algebra" :load-compiled-file nil)
(include-book "arithmetic/top" :dir :system :load-compiled-file nil)

;;; First, we define our basic adder circuits.  We represent bit vectors as
;;; powerlists of zeros or ones.  In the carry-lookahed adder to come, we will
;;; also allow the element nil, to stand for the "propagate" carry marker

(defmacro bit-p (x)
  `(or (equal ,x 0) (equal ,x 1)))

(defmacro bit-nil-p (x)
  `(or (equal ,x 0) (equal ,x 1) (equal ,x nil)))

(defun bit-list-p (x)
  (if (powerlist-p x)
      (and (bit-list-p (p-untie-l x)) (bit-list-p (p-untie-r x)))
    (bit-p x)))
(in-theory (disable (bit-list-p)))

(defun bit-nil-list-p (x)
  (if (powerlist-p x)
      (and (bit-nil-list-p (p-untie-l x)) (bit-nil-list-p (p-untie-r x)))
    (bit-nil-p x)))
(in-theory (disable (bit-nil-list-p)))

(defun adder-fa (x y cin)
  (if (zp cin)
      (cons (if (equal (zp x) (zp y)) 0 1)
	    (if (or    (zp x) (zp y)) 0 1))
    (cons (if (equal (zp x) (zp y)) 1 0)
	  (if (and   (zp x) (zp y)) 0 1))))

(defthm car-adder-fa-type-prescription
  (bit-p (car (adder-fa x y cin)))
  :rule-classes :type-prescription)

(defthm cdr-adder-fa-type-prescription
  (bit-p (cdr (adder-fa x y cin)))
  :rule-classes :type-prescription)

;;; We now present our basy ripple-carry adder.  It returns two values, encoded
;;; as the car and cdr of a cons structure.  The first value is the actual sum,
;;; and the second value is the carry-out bit.

(defun adder-rc (x y cin)
  (if (powerlist-p x)
      (let ((left (adder-rc (p-untie-l x)
			    (p-untie-l y)
			    cin)))
	(let ((right (adder-rc (p-untie-r x)
			       (p-untie-r y)
			       (cdr left))))
	  (cons (p-tie (car left)
		       (car right))
		(cdr right))))
    (adder-fa x y cin)))
(in-theory (disable (adder-rc)))

(defthm car-adder-rc-type-prescription
  (bit-list-p (car (adder-rc x y cin)))
  :rule-classes :type-prescription)

(defthm cdr-adder-rc-type-prescription
  (bit-p (cdr (adder-rc x y cin)))
  :rule-classes :type-prescription)

;;; Now, we define a basic carry-lookahead adder.  The function local-carry can
;;; be executed in parallel and it determines what the carry bit position will
;;; be at a given location.  This can be one of 1, 0, or nil.  If the carryout
;;; is nil, it means that we'll propagate the carryout of the immediate
;;; low-order bit position.

(defun local-carry (x y)
  (if (equal (zp x) (zp y))
      (if (zp x) 0 1)
    nil))

;;; This function encodes how we combine the local-carry bit with the carry
;;; from the carryin.  Basically, it just returns the local-carry, unless it's
;;; nil, when it returns the carryin.  However, we have to be careful, since we
;;; intend to take the prefix-sum with this function as the "sum".  So, we must
;;; ensure that it satisfies the constraints imposed in the prefix-sum book.
;;; Of course, it's still just a hardware switch.

(defun prop-carry (cin local-carry)
  (if (null cin)
      (if (null local-carry)
	  local-carry
	(if (zp local-carry) 0 1))
    (if local-carry
	(if (zp local-carry) 0 1)
      (if (zp cin) 0 1))))

;;; The following function computes the local-carry bit for all the bits

(defun local-carry-vector (x y)
  (if (powerlist-p x)
      (p-tie (local-carry-vector (p-untie-l x)
				 (p-untie-l y))
	     (local-carry-vector (p-untie-r x)
				 (p-untie-r y)))
    (local-carry x y)))
(in-theory (disable (local-carry-vector)))

;;; This function propagates the carryin through all the local-carries.  It's a
;;; straight-forward prefix-sum computation.

(defun prop-carry-vector (cin lcv)
  (if (powerlist-p lcv)
      (p-tie (prop-carry-vector cin (p-untie-l lcv))
	     (prop-carry-vector
	      (p-last (prop-carry-vector
		       cin
		       (p-untie-l lcv)))
	      (p-untie-r lcv)))
    (prop-carry cin lcv)))
(in-theory (disable (prop-carry-vector)))

;;; This function simply performs a parallel full-adder on the bits

(defun pairwise-adder (x y c)
  (if (powerlist-p x)
      (p-tie (pairwise-adder (p-untie-l x)
			     (p-untie-l y)
			     (p-untie-l c))
	     (pairwise-adder (p-untie-r x)
			     (p-untie-r y)
			     (p-untie-r c)))
    (car (adder-fa x y c))))
(in-theory (disable (pairwise-adder)))

;;; Our carry-lookahead adder must shift the resulting carryout bits (since the
;;; ith carryout in the (i+1)st carryin), and so we instantiate the needed
;;; lemmas about prefix-sum, shift, and last

(defthm prop-carry-vector-shift
  (implies (and (bit-nil-p c1)
		(bit-nil-p c2)
		(bit-nil-list-p x))
	   (equal (prop-carry-vector c1 (p-shift c2 x))
		  (p-shift (prop-carry c1 c2)
			   (prop-carry-vector (prop-carry c1 c2) x))))
  :hints (("Goal"
	   :by (:functional-instance p-prefix-sum-p-shift
				     (p-domain-list-p bit-nil-list-p)
				     (p-prefix-sum-aux prop-carry-vector)
				     (domain-p (lambda (x) (bit-nil-p x)))
				     (bin-op prop-carry)
				     (left-zero (lambda () nil))))))

(defthm prop-carry-last-shift-prop-carry-vector
  (implies (bit-nil-p c)
	   (equal (prop-carry (p-last (p-shift c (prop-carry-vector c x)))
			      (p-last x))
		  (p-last (prop-carry-vector c x))))
  :hints (("Goal"
	   :by (:functional-instance binop-last-shift-prefix-sum
				     (p-prefix-sum-aux prop-carry-vector)
				     (domain-p (lambda (x) (bit-nil-p x)))
				     (bin-op prop-carry)
				     (left-zero (lambda () nil))))))


;;; We can now define the "slow" version of the carry-lookahead adder.  It's
;;; slow, because instead of a ripple-carry to do the addition, we're using a
;;; linear prefix-sum to "lookahead" the carries.  But, it's convenient,
;;; because it's simple to relate back to the ripple-carry adder.

(defun adder-cla-slow (x y cin)
  (let ((carry-vector
	 (prop-carry-vector nil
			    (p-shift cin
				     (local-carry-vector x y)))))
    (cons (pairwise-adder x y carry-vector)
	  (prop-carry cin
		      (prop-carry (p-last carry-vector)
				  (p-last
				   (local-carry-vector
				    x y)))))))
(in-theory (disable (adder-cla-slow)))

;;; As it turns out, this equivalent definition is easier to check against the
;;; ripple-carry adder.  Luckily, we can verify it's identical to the one above

(defun adder-cla-slow-good (x y cin)
  (let ((carry-vector
	 (prop-carry-vector cin
			    (local-carry-vector x y))))
    (cons (pairwise-adder x y
			  (p-shift cin carry-vector))
	  (p-last carry-vector))))
(in-theory (disable (adder-cla-slow-good)))

(defthm adder-cla-slow-good-works
  (implies (and (bit-p cin)
		(bit-nil-p x)
		(bit-nil-p y))
	   (equal (adder-cla-slow-good x y cin)
		  (adder-cla-slow x y cin)))
  :rule-classes nil)

;;; We can now prove that our carry-lookahead adder accurately computes the sum
;;; of two bit-vectors.

(defthm adder-cla-slow-good-adder-rc
  (implies (and (p-similar-p x y)
		(bit-p cin))
	   (equal (adder-cla-slow-good x y cin)
		  (adder-rc x y cin)))
  :hints (("Subgoal *1/1"
	   :use (:instance cdr-adder-rc-type-prescription
			   (x (powerlist-car x))
			   (y (powerlist-car y)))))
  :rule-classes nil)

(defthm adder-cla-slow-adder-rc
  (implies (and (p-similar-p x y)
		(bit-p cin)
		(bit-nil-p x)
		(bit-nil-p y))
	   (equal (adder-cla-slow x y cin)
		  (adder-rc x y cin)))
  :hints (("Goal"
	   :use ((:instance adder-cla-slow-good-works)
		 (:instance adder-cla-slow-good-adder-rc)))))

;;; The next step is to replace our serial prefix-sum computation with a faster
;;; one.  We will use the ladner-fischer scheme.  The following definitions and
;;; theorems are simple instances of the ladner-fischer scheme as defined in
;;; prefix-sum.lisp

(defun cla-star (x)
  (if (powerlist-p x)
      (p-zip (cla-star (p-unzip-r x)) (p-unzip-l x))
    nil))
(in-theory (disable (cla-star)))

(defun cla-add (x y)
  (if (powerlist-p x)
      (p-zip (cla-add (p-unzip-l x) (p-unzip-l y))
	     (cla-add (p-unzip-r x) (p-unzip-r y)))
    (prop-carry x y)))
(in-theory (disable (cla-add)))

(defthm measure-cla-star
  (equal (p-measure (cla-star x)) (p-measure x))
  :hints (("Goal"
	   :by (:functional-instance measure-star
				     (p-star cla-star)
				     (bin-op prop-carry))))
  :rule-classes (:linear :rewrite))

(defthm measure-cla-add
  (<= (p-measure (cla-add x y)) (p-measure x))
  :hints (("Goal"
	   :by (:functional-instance measure-add
				     (p-add cla-add)
				     (bin-op prop-carry))))
  :rule-classes (:linear :rewrite))

(defun carry-look-ahead (x)
  (declare (xargs :measure (p-measure x)))
  (if (powerlist-p x)
      (let ((y (carry-look-ahead
		(cla-add (p-unzip-l x) (p-unzip-r x)))))
	(p-zip (cla-add (cla-star y) (p-unzip-l x)) y))
    x))
(in-theory (disable (carry-look-ahead)))

(defun adder-cla (x y cin)
  (let ((carry-vector (carry-look-ahead
		       (p-shift cin
				(local-carry-vector
				 x y)))))
    (cons (pairwise-adder x y carry-vector)
	  (prop-carry cin (prop-carry
			   (p-last carry-vector)
			   (p-last
			    (local-carry-vector
			     x y)))))))
(in-theory (disable (adder-cla)))

;;; We can now instantiate the important lemma which relates the ladner-fischer
;;; version of prefix sum with the slow one we defined previously

(defthm carry-look-ahead-prop-carry-vector
  (implies (and (p-regular-p x)
		(bit-nil-list-p x))
	   (equal (carry-look-ahead x)
		  (prop-carry-vector nil x)))
  :hints (("Goal"
	   :by (:functional-instance lf-prefix-sum-prefix-sum
				     (p-domain-list-p bit-nil-list-p)
				     (p-lf-prefix-sum
				      carry-look-ahead)
				     (p-prefix-sum-aux prop-carry-vector)
				     (domain-p (lambda (x) (or (bit-p x)
							       (equal x nil))))
				     (bin-op prop-carry)
				     (left-zero (lambda () nil))
				     (p-star cla-star)
				     (p-add cla-add)))))

;;; Now, we wish to invoke our first theorem about the correctness of the
;;; carry-lookahead when we use ladner-fischer prefix sum.  First, we have to
;;; prove certain structure lemmas, since we've added an extra condition,
;;; namely that we're dealing with regular powerlists (needed in the proof of
;;; correctness for ladner-fischer)

(defthm p-similar-p-local-carry-vector
  (p-similar-p (local-carry-vector x y) x))

(defthm p-regular-p-local-carry-vector
  (equal (p-regular-p (local-carry-vector x y))
	 (p-regular-p x))
  :hints (("Goal"
	   :use ((:instance similar-regular
			    (x (local-carry-vector x y))
			    (y x))
		 (:instance similar-regular
			    (y (local-carry-vector x y))))
	   :in-theory (disable similar-regular))))

(defthm local-carry-vector-type-prescription
  (bit-nil-list-p (local-carry-vector x y))
  :rule-classes (:rewrite :type-prescription))

(defthm p-similar-p-shift
  (implies (not (powerlist-p c))
	   (p-similar-p (p-shift c y) y)))

(defthm p-regular-p-shift
  (implies (and (not (powerlist-p c))
		(p-regular-p x))
	   (p-regular-p (p-shift c x))))

(defthm bit-nil-list-p-shift
  (implies (and (bit-nil-p cin)
		(bit-nil-list-p x))
	   (bit-nil-list-p (p-shift cin x)))
  :hints (("Goal"
	   :by (:functional-instance p-domain-list-p-p-shift
				     (domain-p (lambda (x) (bit-nil-p x)))
				     (p-domain-list-p bit-nil-list-p)
				     (bin-op prop-carry)
				     (left-zero (lambda () nil))))))

;;; Finally, we can equate our fast carry-lookahead adder with the serial
;;; carry-lookahead.  And then, of course, we can equate it with the original
;;; ripple-carry adder.

(defthm adder-cla-adder-cla-slow
  (implies (and (p-regular-p x)
		(p-similar-p x y)
		(bit-nil-p cin))
	   (equal (adder-cla x y cin)
		  (adder-cla-slow x y cin))))

(defthm adder-cla-adder-rc
      (implies (and (p-regular-p x)
                    (p-similar-p x y)
                    (bit-p cin)
                    (bit-nil-p x)
                    (bit-nil-p y))
               (equal (adder-cla x y cin)
                      (adder-rc x y cin))))


