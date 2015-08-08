(in-package "ACL2")

; Eric Smith, David Russinoff, with contributions and suggestions by Matt Kaufmann
; AMD, June 2001

(local (include-book "../support/ereps"))
(local (include-book "../support/guards"))

(set-inhibit-warnings "theory") ; avoid warning in the next event
(local (in-theory nil))


;;Necessary defuns: BOZO is all this necessary?

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

(defund fl (x)
  (declare (xargs :guard (real/rationalp x)))
  (floor x 1))

(defund bits (x i j)
  (declare (xargs :guard (and (natp x)
                              (natp i)
                              (natp j))))
  (mbe :logic (if (or (not (integerp i))
                      (not (integerp j)))
                  0
                (fl (/ (mod x (expt 2 (1+ i))) (expt 2 j))))
       :exec  (if (< i j)
                  0
                (logand (ash x (- j)) (1- (ash 1 (1+ (- i j))))))))

(defund bitn (x n)
  (declare (xargs :guard (and (natp x)
                              (natp n))))
  (mbe :logic (bits x n n)
       :exec  (if (evenp (ash x (- n))) 0 1)))

(defund lnot (x n)
  (declare (xargs :guard (and (natp x)
                              (integerp n)
                              (< 0 n))))
  (if (natp n)
      (+ -1 (expt 2 n) (- (bits x (1- n) 0)))
    0))

(defun expo-measure (x)
;  (declare (xargs :guard (and (real/rationalp x) (not (equal x 0)))))
  (cond ((not (rationalp x)) 0)
	((< x 0) '(2 . 0))
	((< x 1) (cons 1 (fl (/ x))))
	(t (fl x))))

(defund expo (x)
  (declare (xargs :guard t
                  :measure (expo-measure x)))
  (cond ((or (not (rationalp x)) (equal x 0)) 0)
	((< x 0) (expo (- x)))
	((< x 1) (1- (expo (* 2 x))))
	((< x 2) 0)
	(t (1+ (expo (/ x 2))))))

;could redefine to divide by the power of 2 (instead of making it a negative power of 2)...
(defund sig (x)
  (declare (xargs :guard t))
  (if (rationalp x)
      (if (< x 0)
          (- (* x (expt 2 (- (expo x)))))
        (* x (expt 2 (- (expo x)))))
    0))

;make defund?
(defun sgn (x)
  (declare (xargs :guard t))
  (if (or (not (rationalp x)) (equal x 0))
      0
    (if (< x 0)
        -1
      1)))

(defund exactp (x n)
;  (declare (xargs :guard (and (real/rationalp x) (integerp n))))
  (integerp (* (sig x) (expt 2 (1- n)))))


(defund binary-cat (x m y n)
  (declare (xargs :guard (and (natp x)
                              (natp y)
                              (integerp m) (< 0 m)
                              (integerp n) (< 0 n))))
  (if (and (natp m) (natp n))
      (+ (* (expt 2 n) (bits x (1- m) 0))
         (bits y (1- n) 0))
    0))

(defun formal-+ (x y)
  ;;an auxiliary function that does not appear in translate-rtl output.
  (declare (xargs :guard t))
  (if (and (acl2-numberp x) (acl2-numberp y))
      (+ x y)
    (list '+ x y)))

;;X is a list of alternating data values and sizes.  CAT-SIZE returns the
;;formal sum of the sizes.  X must contain at least 1 data/size pair, but we do
;;not need to specify this in the guard, and leaving it out of that guard
;;simplifies the guard proof.

(defun cat-size (x)
  ;;an auxiliary function that does not appear in translate-rtl output.
  (declare (xargs :guard (and (true-listp x) (evenp (length x)))))
  (if (endp (cddr x))
      (cadr x)
    (formal-+ (cadr x)
	      (cat-size (cddr x)))))

(defmacro cat (&rest x)
  (declare (xargs :guard (and x (true-listp x) (evenp (length x)))))
  (cond ((endp (cddr x))
         `(bits ,(car x) ,(formal-+ -1 (cadr x)) 0))
        ((endp (cddddr x))
         `(binary-cat ,@x))
        (t
         `(binary-cat ,(car x)
                      ,(cadr x)
                      (cat ,@(cddr x))
                      ,(cat-size (cddr x))))))

;Allows things like (in-theory (disable cat)) to refer to binary-cat.
(add-macro-alias cat binary-cat)

(defund mulcat (l n x)

; We introduce mbe not because we want particularly fast execution, but because
; the existing logic definition does not satisfy the guard of cat, which can't
; be changed because of the guard of bits.

  (declare (xargs :guard (and (integerp l)
                              (< 0 l)
                              (acl2-numberp n)
                              (natp x))))
  (mbe :logic (if (and (integerp n) (> n 0))
                  (cat (mulcat l (1- n) x)
                       (* l (1- n))
                       x
                       l)
                0)
       :exec  (cond ((eql n 1)
                     (bits x (1- l) 0))
                    ((and (integerp n) (> n 0))
                     (cat (mulcat l (1- n) x)
                          (* l (1- n))
                          x
                          l))
                    (t 0))))


;;
;; New stuff:
;;


; bias of a q bit exponent field is 2^(q-1)-1
(defund bias (q) (- (expt 2 (- q 1)) 1) )

;;Encoding of floating-point numbers with explicit leading one:
;;bit vectors of length p+q+1, consisting of 1-bit sign field,
;;q-bit exponent field (bias = 2**(q-1)-1), and p-bit significand field.

(defund esgnf  (x p q) (bitn x (+ p q)))
(defund eexpof (x p q) (bits x (1- (+ p q)) p))
(defund esigf  (x p)   (bits x (1- p) 0))

;;;**********************************************************************
;;;                       REPRESENTABLE NUMBERS
;;;**********************************************************************

(defun erepp (x p q)
  (and (rationalp x)
       (not (= x 0))
       (bvecp (+ (expo x) (bias q)) q)
       (exactp x p)))


;;;**********************************************************************
;;;                      VALID ENCODINGS
;;;**********************************************************************

(defun eencodingp (x p q)
  (and (bvecp x (+ p q 1))
       (= (bitn x (- p 1)) 1)))


;;;**********************************************************************
;;;                       EENCODE
;;;**********************************************************************



; sig, expo, and sgn are defined in float.lisp


;bozo disable!
(defun eencode (x p q)
  (cat (cat (if (= (sgn x) 1) 0 1)
	    1
	    (+ (expo x) (bias q))
	    q)
       (1+ q)
       (* (sig x) (expt 2 (- p 1)))
       p) )




;;;**********************************************************************
;;;                       EDECODE
;;;**********************************************************************


(defun edecode (x p q)
  (* (if (= (esgnf x p q) 0) 1 -1)
     (esigf x p)
     (expt 2 (+ 1 (- p) (eexpof x p q) (- (bias q))))))



;;;**********************************************************************
;;;                      Encoding and Decoding are Inverses
;;;**********************************************************************

(defthm erepp-edecode
  (implies (and (eencodingp x p q)
                (integerp p)
                (> p 0)
                (integerp q)
                (> q 0))
           (erepp (edecode x p q) p q)))


(defthm eencodingp-eencode
  (implies (and (erepp x p q)
                (integerp p)
                (> p 0)
                (integerp q)
                (> q 0))
           (eencodingp (eencode x p q) p q) ))

(defthm edecode-eencode
  (implies (and (erepp x p q)
                (integerp p)
;                (> p 0)
                (integerp q)
 ;               (> q 0)
                )
           (equal (edecode (eencode x p q) p q)
                  x )))

(defthm eencode-edecode
  (implies (and (eencodingp x p q)
                (integerp p)
                (>= p 0)
                (integerp q)
                (> q 0))
           (equal (eencode (edecode x p q) p q)
                  x )))

(defthm expo-edecode
  (implies (and (eencodingp x p q)
                (integerp p)
                (> p 0)
                (integerp q)
                (> q 0))
           (equal (expo (edecode x p q))
                  (- (eexpof x p q) (bias q))
                  )))

(defthm sgn-edecode
  (implies (and (eencodingp x p q)
                (integerp p)
                (> p 0)
                (integerp q)
                (> q 0))
           (equal (sgn (edecode  x p q))
                  (if (= (esgnf x p q) 0) 1 -1))))

(defthm sig-edecode
  (implies (and (eencodingp  x p q)
                (integerp p)
                (> p 0)
                (integerp q)
                (> q 0))
           (equal (sig (edecode  x p q))
                  (/ (esigf x p) (expt 2 (- p 1))))))

(defthm eencodingp-not-zero
  (implies (and (eencodingp x p q)
                (integerp p)
                (> p 0)
                (integerp q)
                (> q 0))
           (not (equal (edecode x p q) 0))))

(defun rebias-expo (expo old new)
  (+ expo (- (bias new) (bias old))))

;;I actually needed all four of the following lemmas, although I would have thought
;;that the two bvecp lemmas would be enough.

(defthm natp-rebias-up
    (implies (and (natp n)
		  (natp m)
		  (< 0 m)
		  (<= m n)
		  (bvecp x m))
	     (natp (rebias-expo x m n)))
    :hints (("goal" :in-theory (e/d ( expt-split rebias-expo bvecp natp bias
                                                  ) (expt-compare))
		  :use (:instance expt-weak-monotone (n m) (m n)))))

(defthm natp-rebias-down
    (implies (and (natp n)
		  (natp m)
		  (< 0 m)
		  (<= m n)
		  (bvecp x n)
		  (< x (+ (expt 2 (1- n)) (expt 2 (1- m))))
		  (>= x (- (expt 2 (1- n)) (expt 2 (1- m)))))
	     (natp (rebias-expo x n m)))
    :hints (("goal" :in-theory (enable rebias-expo bvecp natp bias))))

(defthm bvecp-rebias-up
    (implies (and (natp n)
		  (natp m)
		  (< 0 m)
		  (<= m n)
		  (bvecp x m))
	     (bvecp (rebias-expo x m n) n)))

(defthm bvecp-rebias-down
    (implies (and (natp n)
		  (natp m)
		  (< 0 m)
		  (<= m n)
		  (bvecp x n)
		  (< x (+ (expt 2 (1- n)) (expt 2 (1- m))))
		  (>= x (- (expt 2 (1- n)) (expt 2 (1- m)))))
	     (bvecp (rebias-expo x n m) m)))

(defthm rebias-up
    (implies (and (natp n)
		  (natp m)
		  (> n m)
		  (> m 1)
		  (bvecp x m))
	     (equal (rebias-expo x m n)
		    (cat (cat (bitn x (1- m))
			      1
			      (mulcat 1 (- n m) (lnot (bitn x (1- m)) 1))
			      (- n m))
			 (1+ (- n m))
			 (bits x (- m 2) 0)
			 (1- m))))
  :rule-classes ())

(defthm rebias-down
    (implies (and (natp n)
		  (natp m)
		  (> n m)
		  (> m 1)
		  (bvecp x n)
		  (< x (+ (expt 2 (1- n)) (expt 2 (1- m))))
		  (>= x (- (expt 2 (1- n)) (expt 2 (1- m)))))
	     (equal (rebias-expo x n m)
		    (cat (bitn x (1- n))
			 1
			 (bits x (- m 2) 0)
			 (1- m))))
  :rule-classes ())

