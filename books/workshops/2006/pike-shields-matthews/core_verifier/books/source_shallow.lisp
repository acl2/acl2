#|
  Book:    source-shallow
  Copyright: (c) 2005 Galois Connections, Inc.
  Author:    Lee Pike, Galois Connections, Inc. <leepike@galois.com>
  Author:    Mark Shields, Galois Connections, Inc. <mbs@galois.com>
  Author:    John Matthews, Galois Connections, Inc. <matthews@galois.com>
|#

(in-package "ACL2")

(include-book "arithmetic/mod-gcd" :dir :system)
(include-book "ordinals/ordinals" :dir :system)
(include-book "ihs/ihs-definitions" :dir :system)

(encapsulate ()

(local (include-book "ihs/ihs-lemmas" :dir :system))

;; --------------------- Helper Function

(defun nbits-hlp (x i)
  (declare (xargs :measure (acl2-count (- x (expt2 i)))))
  (cond ((or (not (natp i))
             (zp x)
             (< x (expt2 i))) 0)
        ((and (>= x (expt2 i))
              (< x (expt2 (+ i 1))))
         (+ i 1))
        (T (nbits-hlp x (+ i 1)))))

;; Number of unsigned bits needed to represent x
;; (nbits 5) --> 3
;; (nbits -8) --> 4
(defun nbits (x)
  (nbits-hlp (abs x) 0))

;; ---------------------- Arithmetic in Z_{2^n}

;; Addition 2^w
(defund
 c-word-+ (w x y)
  (loghead w (+ x y)))

;; Subtraction modulo 2^w
(defund c-word-- (w x y)
  (loghead w (- x y)))

;; Multiplication modulo 2^w
(defund c-word-* (w x y)
  (loghead w (* x y)))

;; Division (modulo 2^w implicit)
(defund c-word-/ (x y)
  (floor x y))

;; Remainder after division (modulo 2^w implicit)
(defund c-word-% (x y)
  (mod x y))

;; Greatest common divisor (modulo 2^w implicit)
(defund c-word-gcd (x y)
  (nonneg-int-gcd x y))

(defun c-word-**-hlp (w x y)
  (declare (xargs :measure (acl2-count y)))
  (if (zp y) 1
    (if (not (logbitp 0 y))
	(let ((r (loghead w (c-word-**-hlp w x (logtail 1 y)))))
	  (expt r 2))
      (* x (loghead w (c-word-**-hlp w x (- y 1)))))))

;; Exponentation (x^y) modulo 2^w
(defund c-word-** (w x y)
  (loghead w (c-word-**-hlp w x y)))

(defun c-lg2-hlp (x i)
  (declare (xargs :measure (acl2-count (- x (expt2 i)))))
  (cond ((or (not (natp i))
             (zp x)
             (<= x (expt2 i))) 0)
        ((and (> x (expt2 i))
              (<= x (expt2 (+ i 1))))
         (+ i 1))
        (T (c-lg2-hlp x (+ i 1)))))

;; Base-2 logarithm of natural number,
;; rounding up to the nearest natural (returns 0 if x is 0)
(defund c-lg2 (x)
  (c-lg2-hlp x 0))

(defund c-word-min (x y)
  (min x y))

(defund c-word-max (x y)
  (max x y))

;; Negation of x mod 2^w
;; Note: (c-word-neg w x) = (loghead w -x)
(defund c-word-neg (w x)
  (loghead w (1+ (lognot x))))


;; ---------------------- Bitvector Operators

;; In the following, words (unsigned bitvectors) are denoted by integers
;; (possibly modulo some fixed width).

;; Shift word word modulo 2^w toward the most
;; significant bits by shfit bits.
;; (c-word-<< 4 6 1) --> 12
(defund c-word-<< (w word shift)
  (loghead w (ash word shift)))

;; Shift word word modulo 2^w toward the least
;; significant bits by shfit bits.
;; (c-word->> 4 6 1) --> 3
(defund c-word->> (w word shift)
  (declare (ignore w))
  (logtail shift word))

;; Rotate x modulo 2^w toward the most
;; significant bits by shfit bits.
;; (c-word-<<< 4 12 2) --> 3
(defund c-word-<<< (w x shift)
  (logrev w (let ((x1 (logrev w x)))
              (logapp (- w shift) (logtail shift x1)
                      (loghead shift x1)))))

;; Rotate x modulo 2^w toward the least
;; significant bits by shfit bits.
;; (c-word->>> 4 3 2) --> 12
(defund c-word->>> (w x shift)
  (logapp (- w shift) (logtail shift x)
          (loghead shift x)))

(defun c-word-append-hlp (words acc)
  (if (endp words) acc
    (c-word-append-hlp (cddr words)
                       (logapp (car words) (cadr words) acc))))

;; Append the list of words (w_0 n_0 w_1 n_1 w_2 n_2), where
;; 2^w_0 is the modulo for n_0, 2^w_1 is the modulo for n_1, and so on.
;; The words are appended on to the least signficant bits
;; (c-word-append '(2 1 2 3)) --> 7
(defund c-word-append (words)
  (c-word-append-hlp words 0))

(defun c-word-extract-hlp (x widths)
  (if (endp widths) (list x)
    (let ((w (car widths)))
      (cons (loghead w x)
            (c-word-extract-hlp (logtail w x) (cdr widths))))))

;; Extract n words of modulo (2^w_0 2^w_1 ... 2^w_i) given by the list of modulos
;; (w_0 w_1 .. w_i-1).
;; If w is modulo of the smallest bitvector representing x,
;; then w_0 + w_1 + ... + w_i = w.
;; Returns a list of naturals giving the extractions from the most
;; significant bits to the least.
;; (c-word-extract 25 `(2 2)) --> (3 0 1)
;; NOTE: appending the extractions yields the original:
;; (c-word-append '(2 3 2 0 1 1)) --> 25
(defund c-word-extract (x widths)
  (c-word-extract-hlp (logrev (nbits x) x) widths))

(defun c-word-join-hlp (w wrd-vec)
  (if (endp wrd-vec) 0
    (logapp w (car wrd-vec) (c-word-join-hlp w (cdr wrd-vec)))))

;; Append the list of words, from most to least significant bits, all of
;; which are modulo 2^w.
;; (c-word-join 2 '(1 0 3)) --> 19
(defund c-word-join (w wrd-vec)
  (c-word-join-hlp w (reverse wrd-vec)))

(defun c-word-split-hlp (wi x i)
  (declare (xargs :measure (acl2-count i)))
  (if (zp i) nil
    (cons (loghead wi x)
	  (c-word-split-hlp wi (logtail wi x) (- i 1)))))

;; Split word x into wo words, each of which is modulo 2^wi.
;; A list of words, spliting x from least to most significant bits, is returned.
;; (c-word-split 2 3 23) --> (1 1 3)
;; NOTE joining the splits yields the original value:
;; (c-word-join 2 '(1 1 3)) --> 23
(defund c-word-split (wi wo x)
  (reverse (c-word-split-hlp wi x wo)))

;; Extract a subword fom x modulo 2^(ws + wr) beginning at bit offset
;; (from index 0) modulo 2^ws.  Index 0 begins at the least signficant
;; bit of x.
;; (c-word-segment 2 3 14 1) --> 3
(defund c-word-segment (ws wr x offset)
  (logrev ws (loghead ws (logtail offset (logrev (+ ws wr) x)))))

(defund make-trans-wd (wi words)
  (if (endp words) 0
    (logapp 1 (if (logbitp wi (car words)) 1 0)
            (make-trans-wd wi (cdr words)))))

(defun c-word-transpose-hlp (wi wo words)
  (if (zp wi) nil
    (let ((w (- wi 1)))
      (cons (logrev wo (make-trans-wd w words))
            (c-word-transpose-hlp (- wi 1) wo words)))))

;; Given a list of words words of length wo and each word is modulo 2^wi, return a
;; list of words of length wi, each of which is of length wo, by making word i in the
;; returned list from bits i of each word in words.  Indexing is from the least
;; significant bits.
;; (c-word-transpose 2 3 '(2 3 1)) --> (6 3)
(defund c-word-transpose (wi wo words)
  (c-word-transpose-hlp wi wo words))

;; Reverse word x modulo 2^w.
(defund c-word-reverse (w x)
  (logrev w x))

;; Number of true-bits in x mod 2^w.
(defund c-word-parity (w x)
  (declare (ignore w))
  (oddp (logcount x)))


;; ---------------------- Arithmetic in GF_{2^n}
;; Polynomials are denoted by unsigned bitvector representations
;; of integers modulo some constant of the polynomial's coefficients.
;; Ex. Polynomial "5 width 4" has the bitvector representation 1010
;;     (most significant bit on the right), and denotes the
;;     polynomal x^2 + 1

;; Polynomial addition of polynomials x width wl and y width wr.
(defund c-word-padd (wl wr x y)
  (declare (ignore wl wr))
  (logxor x y))

(defun c-word-pmult-hlp (wl wr x y i acc)
  (declare (xargs :measure (acl2-count x)
                  :hints (("Goal" :in-theory (enable c-word->>)))))
  (if (zp x) acc
    (let ((acc1 (c-word-padd wl wr acc (* (loghead 1 x)
                                     (ash y i)))))
      (c-word-pmult-hlp wl wr (c-word->> wl x 1) y (1+ i) acc1))))

;; Polynomial multiplication of polynomials x width wl and y width wr.
(defund c-word-pmult (wl wr x y)
  (c-word-pmult-hlp wl wr x y 0 0))

(defund c-word-pdiv-pmod (wl wr x y d i)
 (declare (xargs :measure (acl2-count i)))
 (if (not (and (natp x) (natp y) (natp i))) 0
   (if (zp i) 0
     (let* ((div-bits (nbits y))
            (scale (- (nbits x) div-bits)))
       (if (< scale 0) (cons d x)
         (let ((v (c-word-padd wl wr x (ash y scale))))
           (c-word-pdiv-pmod wl wr v y (+ d (ash 1 scale)) (- i 1))))))))

;; Polynomial division of polynomials x width wl divided by y width wr.
(defund c-word-pdiv (wl wr x y)
  (car (c-word-pdiv-pmod wl wr x y 0 (expt2 (+ wl wr)))))

;; Polynomial remainder after division of
;; polynomials x width wl divided by y width wr
;; (error on division by zero).
(defund c-word-pmod (wl wr x y)
  (cdr (c-word-pdiv-pmod wl wr x y 0 (expt2 (+ wl 1)))))

(defun c-word-pgcd-hlp (wl wr x y i)
  (declare (xargs :measure (acl2-count i)))
  (if (not (and (natp x) (natp y) (natp i))) 0
    (if (zp i) 0
      (if (zp y) x
    (if (< (nbits x) (nbits y))
        (c-word-pgcd-hlp wr wl y x (- i 1))
      (c-word-pgcd-hlp wr wl y (c-word-pmod wl wr x y) (- i 1)))))))

;; Poynomial greatest common divisor of
;; polynomials x width wl and y width wr.
(defund c-word-pgcd  (wl wr x y)
  (c-word-pgcd-hlp wl wr x y (expt2 (+ wl 1))))

(defun c-word-pirred-hlp (w x i n)
  (declare (xargs :measure (acl2-count i)))
  (if (not (and (natp x) (natp i) (natp n))) 0
  (if (< i 1) T
    (let* ((n1 (c-word-pmod (- (+ w w) 1) w (c-word-pmult w w n n) x))
           (d (c-word-pgcd w w x (c-word-padd w w n1 2))))
      (if (not (equal d 1)) NIL
        (c-word-pirred-hlp w x (- i 1) n1))))))

;; True if poynomial x width w is irreducible.
(defund c-word-pirred (w x)
  (let ((degree (- (nbits x) 1)))
    (and (>= degree 0) (c-word-pirred-hlp w x (floor degree 2) 2))))

(defun c-word-pinv-hlp (wl wr g v h w i)
  (declare (xargs :measure (acl2-count i)))
  (if (zp i) 3
      (if (zp h) v
	(let ((hbits (nbits h))
	      (gbits (nbits g))
	      (vbits (nbits v))
	      (wbits (nbits w)))
	  (let ((dr (c-word-pdiv-pmod gbits hbits g h 0 (expt2 (+ wl wr)))))
	    (c-word-pinv-hlp hbits wbits h w (cdr dr)
			     (let ((wl1 (nbits (car dr))))
			       (c-word-padd vbits (- (+ wl1 wbits) 1) v
					    (c-word-pmult wl1 wbits
							  (car dr) w)))
			   (- i 1)))))))

;; Multiplicative inverse of polynomial n width wr with respect to
;; irreducible polynomial irred width wl (an unspecified value is
;; returned if irred is not irreducible).
(defund c-word-pinv (wl wr irred n)
  (let ((q (c-word-pinv-hlp wl wr irred 0 n 1 (expt2 (+ wl wr)))))
    (c-word-pmod (nbits q) wl q irred)))

;; ---------------------- Equality (over Simple Types)

(defund c-== (x y)
  (equal x y))

(defund c-!= (x y)
  (not (equal x y)))


;; ---------------------- Logical Operators

;; exclusive or of bits
(defund c-^ (x y)
  (and (not (equal x y)) (or x y)))

;; In the following, unsigned bitvectors are denoted by integers
;; modulo some width.

;; Bitwise conjunction
(defund c-word-&& (x y)
  (logand x y))

;; Bitwise disjunction
(defund c-word-or (x y)
  (logior x y))

;; Bitwise exclusive-or
(defund c-word-^^ (x y)
  (logxor x y))

;; Bitwise complementation of x width w.
;; (c-~ 3 5) --> 2
;; (c-~ 3 1) --> 6
(defund c-~ (w x)
  (loghead w (lognot x)))


;; ---------------------- Vector Operators
;; In the following, vectors are represented as lists.  We assume the
;; vector is indexed from 0 at the car of the list representing it.

;; Shift the vector vec shift places toward the head.
;; Fill in the remaining indexes with zero.
;; (c-vec-<< '(1 2 3 4) 2 5) --> (3 4 5 5)
(defund c-vec-<< (vec shift zero)
  (if (zp shift) vec
    (append (nthcdr shift vec)
	    (make-list shift :initial-element zero))))

;; Shift the vector vec shift places toward the tail.
;; Fill in the remaining indexes with zero.
;; (c-vec->> '(1 2 3 4) 2 5) --> (5 5 1 2)
(defund c-vec->> (vec shift zero)
  (if (zp shift) vec
    (append (make-list shift :initial-element zero)
	    (take shift vec))))

;; Rotate the vector vec shift places toward the head.
;; (c-vec-<<< '(1 2 3 4) 1) --> (2 3 4 1)
(defund c-vec-<<< (vec shift)
  (append (nthcdr shift vec)
          (take shift vec)))

;; Rotate the vector vec shift places toward the tail.
;; (c-vec->>> '(1 2 3 4) 2) --> (4 1 2 3)
(defund c-vec->>> (vec shift)
  (append (reverse (take shift (reverse vec)))
          (take (- (len vec) shift) vec)))

;; Append the list of vectors vecs.
;; (c-vec-append `((1 2) (3 4 5) (6)))) --> (1 2 3 4 5 6)
(defund c-vec-append (vecs)
  (if (endp vecs) nil
    (append (car vecs) (c-vec-append (cdr vecs)))))

;; Extract the from the vector vec i vectors of width (w_0 w_1 ... w_i-1).
;; (c-vec-extract '(1 2 3 4 5 6) '(1 2)) --> ((1) (2 3) (4 5 6))
(defund c-vec-extract (vec widths)
  (if (endp widths) (list vec)
    (let ((w (car widths)))
      (cons (take w vec)
            (c-vec-extract (nthcdr w vec) (cdr widths))))))

;; Flatten the vector of vectors vec.
;; (c-vec-join `((1 2 3) (4 5) (6))) --> (1 2 3 4 5 6)
(defund c-vec-join (vec)
  (declare (xargs :measure (o+ (o* (omega) (len vec)) (len (car vec)))))
  (if (not (and (true-list-listp vec) (consp (car vec)))) nil
    (if (endp vec) nil
      (cons (caar vec)
            (if (cdar vec) (c-vec-join (cons (cdar vec) (cdr vec)))
              (c-vec-join (cdr vec)))))))

;; Split the vector vec into vectors, each of which is of width wi.
;; (c-vec-split 2 '(1 2 3 4 5 6 7)) --> ((1 2) (3 4) (5 6) (7))
(defund c-vec-split (wi vec)
  (if (not (and (natp wi) (< 0 wi) (<= wi (len vec)))) (list vec)
    (if (equal wi (len vec))
        (list vec)
      (cons (take wi vec)
            (c-vec-split wi (nthcdr wi vec))))))

;; Take the subvector of vec of length ws beginning at index offset.
;; (c-vec-segment 3 '(1 2 3 4 5) 2) --> (3 4 5)
(defund c-vec-segment (ws vec offset)
  (take ws (nthcdr offset vec)))

(defun make-rows (ind wo vecs i)
  (declare (xargs :measure (acl2-count (|+| 1 wo (- i)))))
  (if (not (and (natp i) (natp wo))) nil
    (if (>= i wo) nil
      (cons (nth ind (nth i vecs))
	    (make-rows ind wo vecs (+ i 1))))))

(defun c-vec-transpose-hlp (wi wo vecs i)
  (declare (xargs :measure (acl2-count (|+| 1 wi (- i)))))
  (if (not (and (natp i) (natp wi))) nil
    (if (>= i wi) nil
      (cons (make-rows i wo vecs 0)
	    (c-vec-transpose-hlp wi wo vecs (+ i 1))))))

;; Transpose the matrix (i.e., vector of vectors) into a vector of length
;; wi containing vectors of length wo.
;; (c-vec-transpose 3 2 `((1 2 3) (4 5 6))) --> ((1 4) (2 5) (3 6))
(defund c-vec-transpose (wi wo vecs)
  (c-vec-transpose-hlp wi wo vecs 0))

(defun c-vec-reverse-hlp (w vec i)
  (declare (xargs :measure (acl2-count (+ 1 w (- i)))))
  (if (not (and (natp i) (natp w))) nil
    (if (>= i w) nil
      (cons (nth (- (1- w) i) vec)
	    (c-vec-reverse-hlp w vec (+ i 1))))))

;; Reverse the (sub-)vector of width w of vector vec.
;; (c-vec-reverse 3 '(1 2 3 4 5)) --> (3 2 1)
(defund c-vec-reverse (w vec)
  (c-vec-reverse-hlp w vec 0))


)
