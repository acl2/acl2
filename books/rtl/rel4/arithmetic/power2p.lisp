(in-package "ACL2")

;The rule power2p-rewrite has proven quite helpful.

(defund fl (x)
  (declare (xargs :guard (real/rationalp x)))
  (floor x 1))

(local (include-book "fl")) ;or could use floor?
(local (include-book "fp2"))
(local (include-book "predicate"))
(local (include-book "unary-divide"))

;old version
;(defun power2p (x)
 ; (equal x (expt 2 (expo x))))

(include-book "ordinals/e0-ordinal" :dir :system)
(set-well-founded-relation e0-ord-<)

(defund power2p-measure (x)
  (declare (xargs :guard (and (rationalp x) (not (equal x 0)))))
  (cond ((or (not (rationalp x))
             (<= x 0)) 0)
	((< x 1) (cons 1 (fl (/ x))))
	(t (fl x))))

(defund power2p (x)
  (declare (xargs :guard t
                  :measure (power2p-measure x)
                  :hints (("goal" :in-theory (enable power2p-measure)))))
  (cond ((or (not (rationalp x))
             (<= x 0))
         nil)
        ((< x 1) (power2p (* 2 x)))
        ((<= 2 x) (power2p (* 1/2 x)))
        ((equal x 1) t)
        (t nil) ;got a number in the doubly-open interval (1,2)
        ))

#| A term fits the "power of 2" pattern iff it is a tree built using * and /  (actually, binary-* and unary-/)
in which each leaf is either a rational constant which is a power of 2 or a term of the form (EXPT 2 I).
|#

(defund power2-syntaxp (term)
  (if (not (consp term))
      nil
    (case (car term)
      (quote (and (rationalp (cadr term))
                  (power2p (cadr term))))
      (expt (equal (cadr term) '(quote 2))) ;allow the base to be any power of 2?  (constants only? or (expt 2 n)??
      (binary-* (and (power2-syntaxp (cadr term))
                     (power2-syntaxp (caddr term))))
      (unary-/ (power2-syntaxp (cadr term)))
      (otherwise nil))))

#|

Notes:

(power2-syntaxp ''2)
(power2-syntaxp '(expt 2 i))
(power2-syntaxp '(unary-/ (expt 2 i)))
(power2-syntaxp '(binary-/ (expt 2 i) (expt 2 j)))
(power2-syntaxp '(binary-* (expt 2 i) (expt 2 j)))
(power2-syntaxp '(binary-* '2 (binary-* (expt '2 j) (expt '2 k))))
(power2-syntaxp '(binary-* '2 (binary-* (expt '2 j) (expt '2 (binary-+ k (binary-* '-1 j))))))

|#


;induction?
(defthmd power2p-with-arg-between-one-and-two
  (implies (and (< 1/2 x)
                (< x 1)
                )
           (not (power2p x)))
  :hints (("goal" :in-theory  (enable power2p)))
  )

(defthm power2p-of-non-rational
  (implies (not (rationalp x))
           (equal (power2p x)
                  nil))
  :hints (("goal" :in-theory (enable power2p))))

(defthm power2p-of-non-positive
  (implies (not (< 0 x))
           (equal (power2p x)
                  nil))
  :hints (("goal" :in-theory (enable power2p))))

;induction
(defthm power2p-inverse
  (and (equal (power2p (/ x))
              (power2p x))
       (equal (power2p (/ 1 x)) ;do we need this?
              (power2p x)))
  :otf-flg t
  :hints (("goal" :in-theory (enable power2p
                                     power2p-with-arg-between-one-and-two))))

;what about (/ -1 x) ? (/ 1 (- x)) ?
;in general, what if x is negative, and we have something like (power2p (- x)) ?

;power2p-double and power2p-half helped clean up the proof of power2p-prod
(defthmd power2p-double
  (equal (power2p (* 2 x))
         (power2p x))
  :hints (("goal" :in-theory (enable power2p
                                     power2p-with-arg-between-one-and-two))))

(defthmd power2p-half
  (equal (power2p (* 1/2 x))
         (power2p x))
  :hints (("goal" :in-theory (enable power2p
                                     power2p-with-arg-between-one-and-two))))
;consider enabling?
(defthmd power2p-prod
  (implies (and (power2p x)
                (power2p y))
           (power2p (* x y)))
  :hints (("goal" :in-theory (enable power2p power2p-double power2p-half
                                     power2p-with-arg-between-one-and-two))))

;robustify with power2p-quotient?

;reorder hyps?  make conclusion into an equality?
(defthmd power2p-prod-not
  (implies (and (not (power2p x))
                (power2p y)
                )
           (not (power2p (* x y))))
   :hints (("goal" :in-theory (disable power2p-prod)
            :use (:instance power2p-prod (x (* x y)) (y (/ y))))))

(defthm power2p-shift
  (implies (and (syntaxp (power2-syntaxp x))
                (force (power2p x)) ;this should be true if the syntaxp hyp is satisfied
                )
           (equal (power2p (* x y))
                  (power2p y)))
  :hints (("goal"
           :use ((:instance power2p-prod-not (y x) (x y))
                 (:instance power2p-prod (y x) (x y))))))

(defthm power2p-shift-2
  (implies (and (syntaxp (power2-syntaxp y))
                (force (power2p y)) ;this should be true if the syntaxp hyp is satisfied
                )
           (equal (power2p (* x y))
                  (power2p x)))
  :hints (("goal" :in-theory (disable power2p)
           :use ( power2p-prod-not power2p-prod))))


;make rules for quotient of powers of 2


(defthm power2p-means-positive-rationalp
  (implies (power2p x)
           (and (< 0 x)
                (rationalp x)))
  :rule-classes ((:forward-chaining :trigger-terms ((POWER2P X)))))


