; See the top-level arithmetic-3 LICENSE file for authorship,
; copyright, and license information.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; arithmetic-theory.lisp
;;;
;;; This book contains the rules which will be assembled into the
;;; arithmetic-theory used for rewriting during linear and non-
;;; linear arithmetic.  There are two reasons for using this
;;; alternate theory: 1. Efficiency --- we will be rewriting
;;; many of the terms repeatedly, and 2. This will allow us to
;;; use a (possibly) different ``normal'' form during linear and
;;; non-linear arithmetic from that used while rewriting.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#|
(defthm crock-2
  (implies (integerp i)
           (equal (expt 2 (* 2 i))
                  (* (expt 2 i) (expt 2 i)))))

(in-theory (disable crock-2))

(defthm crock-3
  (implies (integerp i)
           (equal (expt 2 (* 3 i))
                  (* (expt 2 i) (expt 2 i) (expt 2 i)))))

(in-theory (disable crock-3))
|#

(in-package "ACL2")

(local
 (include-book "basic"))

(include-book "common")

(include-book "building-blocks")

(local
 (include-book "collect"))

(local
 (in-theory (enable collect-*)))

(local
 (in-theory (enable collect-+)))

(defun arith-bubble-down (x match)
  (declare (xargs :guard t)
           (ignore match))
  x)

(local
 (defthm temp510
     (implies (and (rationalp x)
                   (rationalp y))
              (equal (equal (+ x y) 0)
                     (equal x (- y))))))


(table acl2-defaults-table :state-ok t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun arith-find-matching-factor-gather-exponents (to-match x)
  (declare (xargs :guard (and (true-listp to-match)
                              (pseudo-termp x))))
  (cond ((eq (fn-symb x) 'BINARY-*)
         (cond ((arith-matching-factor-gather-exponents-p to-match (arg1 x))
                (list (cons 'match (arg1 x))))
               ((eq (fn-symb (arg2 x)) 'BINARY-*)
                (arith-find-matching-factor-gather-exponents to-match (arg2 x)))
               ((arith-matching-factor-gather-exponents-p to-match (arg2 x))
                (list (cons 'match (arg2 x))))
               (t
                nil)))
        ((arith-matching-factor-gather-exponents-p to-match x)
         (list (cons 'match x)))
        (t
         nil)))

(defthm arith-normalize-factors-gather-exponents
    (implies (and (bind-free
                   (arith-find-matching-factor-gather-exponents
                    (arith-factor-pattern-gather-exponents x) y)
                   (match))
                  (syntaxp (proveably-non-zero x mfc state)))
             (equal (* x y)
                    (* (arith-bubble-down x match) y))))

(local
 (in-theory (disable arith-normalize-factors-gather-exponents)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun arith-find-matching-factor-scatter-exponents (to-match x)
  (declare (xargs :guard (and (true-listp to-match)
                              (pseudo-termp x))))
  (cond ((eq (fn-symb x) 'BINARY-*)
         (cond ((arith-matching-factor-scatter-exponents-p to-match (arg1 x))
                (list (cons 'match (arg1 x))))
               ((eq (fn-symb (arg2 x)) 'BINARY-*)
                (arith-find-matching-factor-scatter-exponents to-match (arg2 x)))
               ((arith-matching-factor-scatter-exponents-p to-match (arg2 x))
                (list (cons 'match (arg2 x))))
               (t
                nil)))
        ((arith-matching-factor-scatter-exponents-p to-match x)
         (list (cons 'match x)))
        (t
         nil)))

(defthm arith-normalize-factors-scatter-exponents
    (implies (and (bind-free
                   (arith-find-matching-factor-scatter-exponents
                    (arith-factor-pattern-scatter-exponents x) y)
                   (match))
                  (syntaxp (proveably-non-zero x mfc state)))
             (equal (* x y)
                    (* (arith-bubble-down x match) y))))

(local
 (in-theory (disable arith-normalize-factors-scatter-exponents)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun arith-find-matching-addend (to-match x)
  (declare (xargs :guard (pseudo-termp x)))
  (cond ((eq (fn-symb x) 'BINARY-+)
         (cond ((matching-addend-p to-match (arg1 x))
                (list (cons 'match (arg1 x))))
               ((eq (fn-symb (arg2 x)) 'BINARY-+)
                (arith-find-matching-addend to-match (arg2 x)))
               ((matching-addend-p to-match (arg2 x))
                (list (cons 'match (arg2 x))))
               (t
                nil)))
        ((matching-addend-p to-match x)
         (list (cons 'match x)))
        (t
         nil)))

(defthm arith-normalize-addends
    (implies (bind-free
              (arith-find-matching-addend (addend-pattern x) y)
              (match))
             (equal (+ x y)
                    (+ (arith-bubble-down x match) y))))

(local
 (in-theory (disable arith-normalize-addends)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm |arith (- (- x))|
  (implies (acl2-numberp x)
           (equal (- (- x))
                  x)))

(defthm |arith (- (+ x y))|
  (equal (- (+ x y))
         (+ (- x) (- y))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm |arith (* y x)|
  (equal (* y x) (* x y)))

(defthm |arith (* y (* x z))|
   (equal (* y (* x z))
          (* x (* y z))))

(defthm |arith (* (* x y) z)|
  (equal (* (* x y) z) (* x (* y z))))

(defthm |arith (* 1 x)|
  (implies (acl2-numberp x)
           (equal (* 1 x)
                  x)))

(defthm |arith (* x 1)|
    (implies (acl2-numberp x)
           (equal (* x 1)
                  x)))

(defthm |arith (* 0 x)|
  (equal (* 0 x)
         0))

(defthm |arith (* x 0)|
    (equal (* x 0)
           0))

(defthm |arith (* -1 x)|
  (equal (* -1 x)
         (- x)))

(defthm |arith (/ (/ x))|
  (implies (acl2-numberp x)
           (equal (/ (/ x))
                  x)))

(defthm |arith (/ (* x y))|
  (equal (/ (* x y))
	 (* (/ x) (/ y))))

(defthm |arith (* x (+ y z))|
  (equal (* x (+ y z))
         (+ (* x y) (* x z))))

(local
 (in-theory (disable Distributivity)))

(defthm |arith (* (+ x y) z)|
  (equal (* (+ x y) z)
	 (+ (* x z) (* y z))))

(defthm |arith (* x (- y))|
  (implies (syntaxp (not (quotep y)))
	   (equal (* x (- y))
		  (- (* x y)))))

(defthm |arith (* (- x) y)|
  (implies (syntaxp (not (quotep x)))
	   (equal (* (- x) y)
		  (- (* x y)))))

(defthm |arith (- (* c x))|
  (implies (syntaxp (quotep c))
	   (equal (- (* c x))
		  (* (- c) x))))

(defthm |arith (/ (- x))|
  (implies (syntaxp (not (quotep x)))
  (equal (/ (- x))
         (- (/ x)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Should we expand (expt (+ c x) d), whenever c and d are const?

(defthm |arith (expt (+ x y) 2)|
    (implies (syntaxp (rewriting-goal-literal x mfc state))
             (equal (expt (+ x y) 2)
                    (+ (expt x 2) (* 2 x y) (expt y 2))))
  :hints (("Goal" :expand (expt (+ x y) 2))))

(defthm |arith (expt (+ x y) 3)|
    (implies (syntaxp (rewriting-goal-literal x mfc state))
             (equal (expt (+ x y) 3)
                    (+ (expt x 3) (* 3 (expt x 2) y) (* 3 x (expt y 2)) (expt y 3))))
  :hints (("Goal" :expand ((expt (+ x y) 3)
			   (expt (+ x y) 2)))))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm |arith (* c (* d x))|
  (implies (and (syntaxp (quotep c))
		(syntaxp (quotep d)))
	   (equal (* c (* d x))
		  (* (* c d) x))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm |arith (expt x 0)|
 (equal (expt x 0)
        1))

(defthm |arith (expt 0 n)|
    (equal (expt 0 n)
           (if (zip n)
               1
             0)))

(defthm |arith (expt x 1)|
  (implies (acl2-numberp x)
           (equal (expt x 1)
                  x)))

(defthm |arith (expt 1 n)|
    (equal (expt 1 n)
           1))

(defthm |arith (expt x -1)|
  (equal (expt x -1)
	 (/ x)))

(defthm |arith (expt (/ x) n)|
  (equal (expt (/ x) n)
         (/ (expt x n))))

(defthm |arith (expt x (- n))|
    (implies (syntaxp (negative-addends-p n))
             (equal (expt x n)
                    (/ (expt x (- n))))))

;;; The syntaxp hyps recognize terms of the form 1/c,
;;; where c is a constant.  Note that since x is a
;;; constant, we are NOT introducing a / inside the
;;; expt since ACL2 will ``execute'' (/ x).  For
;;; example, (expt 1/4 n) will get rewritten to
;;; (/ (expt (/ 1/4) n)) and thence to (/ (expt 4 n)).

(defthm |arith (expt 1/c n)|
    (implies (and (syntaxp (quotep x))
                  (syntaxp (rationalp (unquote x)))
                  (syntaxp (not (integerp (unquote x))))
                  (syntaxp (equal (numerator x) 1)))
             (equal (expt x n)
                    (/ (expt (/ x) n)))))

;;; Note: The next three rules really should be generalized.

(defthm |arith (expt 4 n)|
    (implies (integerp n)
             (equal (expt 4 n)
                    (expt 2 (* 2 n)))))

(defthm |arith (expt 8 n)|
    (implies (integerp n)
             (equal (expt 8 n)
                    (expt 2 (* 3 n)))))

(defthm |arith (expt 16 n)|
    (implies (integerp n)
             (equal (expt 16 n)
                    (expt 2 (* 4 n)))))
#|
(defthm |arith (expt (/ x) (- c))|
    (implies (syntaxp (and (quotep c)
                           (< (unquote c) 0)))
             (equal (expt (/ x) c)
                    (expt x (- c)))))
|#
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm |arith (expt (* x y) n)|
  (equal (expt (* x y) n)
         (* (expt x n)
            (expt y n))))

(defthm |arith (expt (expt x m) n)|
  (implies (and (integerp m)
                (integerp n))
           (equal (expt (expt x m) n)
                  (expt x (* m n)))))


(defthm |arith (expt x (+ m n))|
  (implies (and (integerp m)
		(integerp n))
	   (equal (expt x (+ m n))
		  (if (equal (+ m n) 0)
		      1
		      (* (expt x m)
			 (expt x n))))))
#|
;;; I don't think we want these next two.  I leave them here for
;;; referance purposes only.

(defthm |arith (expt x (+ m n)) non-pos m and n|
  (implies (and (<= m 0)
		(<= n 0)
		(integerp m)
		(integerp n))
	   (equal (expt x (+ m n))
		  (* (expt x m)
		     (expt x n)))))

(defthm |arith (expt x (+ m n))) non-neg m and n|
  (implies (and (<= 0 m)
		(<= 0 n)
		(integerp m)
		(integerp n))
	   (equal (expt x (+ m n))
		  (* (expt x m)
		     (expt x n)))))
|#

(defthm |arith (expt x (+ m n)) non-zero x|
  (implies (and (not (equal 0 x))
		(acl2-numberp x)
		(integerp m)
		(integerp n))
	   (equal (expt x (+ m n))
		  (* (expt x m)
		     (expt x n))))
  :hints (("Goal" :use (|(expt x (+ m n))|))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm |arith (fix x)|
  (implies (acl2-numberp x)
	   (equal (fix x)
                  x)))

(defthm |arith (* (numerator x) (/ (denominator x)))|
  (implies (rationalp x)
           (equal (* (numerator x) (/ (denominator x)))
                  x)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm |arith (* c (* d x))|
  (implies (and (syntaxp (quotep c))
		(syntaxp (quotep d)))
	   (equal (* c (* d x))
		  (* (* c d) x))))

(defun arith-collect-* (x y)
  (declare (xargs :guard (and (acl2-numberp x)
                              (acl2-numberp y))))
  (* x y))

(defthm arith-collect-*-problem-finder
    (implies (equal x x)
             (equal (arith-collect-* x y)
                    (* x y))))

(in-theory (disable arith-collect-*-problem-finder))

(defthm |arith (* (expt x n) (expt y n))|
    (implies (integerp n)
             (equal (arith-collect-* (expt x n) (expt y n))
                    (expt (* x y) n))))

(defthm |arith (* x x)|
    (equal (arith-collect-* x x)
           (expt x 2)))

(defthm |arith (* x (/ x))|
    (equal (arith-collect-* x (/ x))
           (if (equal (fix x) 0)
               0
             1)))

(defthm |arith (* x (expt x n))|
    (implies (integerp n)
             (equal (arith-collect-* x (expt x n))
                    (if (equal (fix x) 0)
                        0
                      (expt x (+ n 1))))))

(defthm |arith (* x (expt (- x) n))|
    (implies (integerp n)
             (equal (arith-collect-* x (expt (- x) n))
                    (cond ((equal (fix x) 0)
                           0)
                          ((evenp n)
                           (expt x (+ n 1)))
                          (t
                           (- (expt x (+ n 1))))))))

(defthm |arith (* x (/ (expt x n)))|
    (implies (integerp n)
             (equal (arith-collect-* x (/ (expt x n)))
                    (if (equal (fix x) 0)
                        0
                      (/ (expt x (- n 1)))))))

(defthm |arith (* x (/ (expt (- x) n)))|
    (implies (integerp n)
             (equal (arith-collect-* x (/ (expt (- x) n)))
                    (cond ((equal (fix x) 0)
                           0)
                          ((evenp n)
                           (/ (expt x (- n 1))))
                          (t
                           (- (/ (expt x (- n 1)))))))))

(defthm |arith (* (/ x) (expt x n))|
    (implies (integerp n)
             (equal (arith-collect-* (/ x) (expt x n))
                    (if (equal (fix x) 0)
                        0
                      (expt x (- n 1))))))

(defthm |arith (* (/ x) (expt (- x) n))|
    (implies (integerp n)
             (equal (arith-collect-* (/ x) (expt (- x) n))
                    (cond ((equal (fix x) 0)
                           0)
                          ((evenp n)
                           (expt x (- n 1)))
                          (t
                           (- (expt x (- n 1))))))))

(defthm |arith (* (expt x m) (expt x n))|
    (implies (and (integerp m)
                  (integerp n))
             (equal (arith-collect-* (expt x m) (expt x n))
                    (if (and (equal (fix x) 0)
                             (not (equal m 0))
                             (not (equal n 0)))
                        0
                      (expt x (+ m n))))))

(defthm |arith (* (expt (- x) m) (expt x n))|
    (implies (and (integerp m)
                  (integerp n))
             (equal (arith-collect-* (expt (- x) m) (expt x n))
                    (cond ((and (equal (fix x) 0)
                                (not (equal m 0))
                                (not (equal n 0)))
                           0)
                          ((evenp m)
                           (expt x (+ m n)))
                          (t
                           (- (expt x (+ m n))))))))

(defthm |arith (* (expt x m) (expt (- x) n))|
    (implies (and (integerp m)
                  (integerp n))
             (equal (arith-collect-* (expt x m) (expt (- x) n))
                    (cond ((and (equal (fix x) 0)
                                (not (equal m 0))
                                (not (equal n 0)))
                           0)
                          ((evenp n)
                           (expt x (+ m n)))
                          (t
                           (- (expt x (+ m n))))))))

(defthm |arith (* (/ (expt x m)) (expt x n))|
    (implies (and (integerp m)
                  (integerp n))
             (equal (arith-collect-* (/ (expt x m)) (expt x n))
                    (if (and (equal (fix x) 0)
                             (not (equal m 0))
                             (not (equal n 0)))
                        0
                      (expt x (- n m))))))

(defthm |arith (* (/ (expt (- x) m)) (expt x n))|
    (implies (and (integerp m)
                  (integerp n))
             (equal (arith-collect-* (/ (expt (- x) m)) (expt x n))
                    (cond ((and (equal (fix x) 0)
                                (not (equal m 0))
                                (not (equal n 0)))
                           0)
                          ((evenp m)
                           (expt x (- n m)))
                          (t
                           (- (expt x (- n m))))))))

(defthm |arith (* (/ (expt x m)) (expt (- x) n))|
    (implies (and (integerp m)
                  (integerp n))
             (equal (arith-collect-* (/ (expt x m)) (expt (- x) n))
                    (cond ((and (equal (fix x) 0)
                                (not (equal m 0))
                                (not (equal n 0)))
                           0)
                          ((evenp n)
                           (expt x (- n m)))
                          (t
                           (- (expt x (- n m))))))))

(defthm |arith (* (expt x m) (/ (expt x n)))|
    (implies (and (integerp m)
                  (integerp n))
             (equal (arith-collect-* (expt x m) (/ (expt x n)))
                    (if (and (equal (fix x) 0)
                             (not (equal m 0))
                             (not (equal n 0)))
                        0
                      (expt x (- m n))))))

(defthm |arith (* (expt (- x) m) (/ (expt x n)))|
    (implies (and (integerp m)
                  (integerp n))
             (equal (arith-collect-* (expt (- x) m) (/ (expt x n)))
                    (cond ((and (equal (fix x) 0)
                                (not (equal m 0))
                                (not (equal n 0)))
                           0)
                          ((evenp m)
                           (expt x (- m n)))
                          (t
                           (- (expt x (- m n))))))))

(defthm |arith (* (expt x m) (/ (expt (- x) n)))|
    (implies (and (integerp m)
                  (integerp n))
             (equal (arith-collect-* (expt x m) (/ (expt (- x) n)))
                    (cond ((and (equal (fix x) 0)
                                (not (equal m 0))
                                (not (equal n 0)))
                           0)
                          ((evenp n)
                           (expt x (- m n)))
                          (t
                           (- (expt x (- m n))))))))

(defthm |arith (* (expt c n) (expt d n))|
    (implies (and (integerp n)
                  (syntaxp (quotep c))
                  (syntaxp (quotep d)))
             (equal (arith-collect-* (expt c n) (expt d n))
                    (expt (* c d) n))))

(defthm |arith (expt x c)|
  (implies (and (syntaxp (quotep c))
                (integerp c)
                (not (equal c 0)))
           (equal (expt x c)
                  (cond ((< c 0)
                         (* (/ x) (expt x (+ c 1))))
                        (t  ; (< 0 c)
                         (* x (expt x (- c 1)))))))
  :hints (("Goal" :in-theory (disable |arith (expt x (+ m n)) non-zero x|
                                      |arith (expt x (+ m n))|
                                      |(expt x (+ m n)) non-zero x|
                                      |(expt x (+ m n))|))))

(defthm |(arith-collect-* y x)|
    (equal (arith-collect-* y x)
           (arith-collect-* x y)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm |arith (+ c (+ d x))|
  (implies (and (syntaxp (quotep c))
		(syntaxp (quotep d)))
	   (equal (+ c (+ d x))
		  (+ (+ c d) x))))

(defun arith-collect-+ (x y)
  (declare (xargs :guard (and (acl2-numberp x)
                              (acl2-numberp y))))
  (+ x y))

(defthm arith-collect-+-problem-finder
    (implies (equal x x)
             (equal (arith-collect-+ x y)
                    (+ x y))))

(in-theory (disable arith-collect-+-problem-finder))

(defthm |arith (+ x x)|
    (equal (arith-collect-+ x x)
           (* 2 x)))

(defthm |arith (+ x (- x))|
    (equal (arith-collect-+ x (- x))
           0))

(defthm |arith (+ x (* c x))|
    (implies (syntaxp (quotep c))
             (equal (arith-collect-+ x (* c x))
                    (* (+ c 1) x))))


(defthm |arith (+ (- x) (* c x))|
    (implies (syntaxp (quotep c))
             (equal (arith-collect-+ (- x) (* c x))
                    (* (- c 1) x))))

(defthm |arith (+ (* c x) (* d x))|
    (implies (and (syntaxp (quotep c))
                  (syntaxp (quotep d)))
             (equal (arith-collect-+ (* c x) (* d x))
                    (* (+ c d) x))))

(defthm |(arith-collect-+ y x)|
    (equal (arith-collect-+ y x)
           (arith-collect-+ x y)))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm arith-bubble-down-*-problem-finder
    (implies (equal x x)
             (equal (* (arith-bubble-down x match) y)
                    (* x y))))

(in-theory (disable arith-bubble-down-*-problem-finder))

(defthm arith-bubble-down-*-bubble-down
    (equal (* (arith-bubble-down x match) y z)
           (* y (arith-bubble-down x match) z)))

(defthm arith-bubble-down-*-match-1
    (implies (syntaxp (equal match y))
             (equal (* (arith-bubble-down x match) y)
                    (arith-collect-* x y))))

(defthm arith-bubble-down-*-match-2
    (implies (syntaxp (equal match y))
             (equal (* y (arith-bubble-down x match))
                    (arith-collect-* x y))))

(defthm arith-bubble-down-*-match-3
    (implies (syntaxp (equal match y))
             (equal (* (arith-bubble-down x match) y z)
                    (* (arith-collect-* x y) z))))

(defthm arith-bubble-down-+-problem-finder
    (implies (equal x x)
             (equal (+ (arith-bubble-down x match) y)
                    (+ x y))))

(in-theory (disable arith-bubble-down-+-problem-finder))

(defthm arith-bubble-down-+-bubble-down
    (equal (+ (arith-bubble-down x match) y z)
           (+ y (arith-bubble-down x match) z)))

(defthm arith-bubble-down-+-match-1
    (implies (syntaxp (equal match y))
             (equal (+ (arith-bubble-down x match) y)
                    (arith-collect-+ x y))))

(defthm arith-bubble-down-+-match-2
    (implies (syntaxp (equal match y))
             (equal (+ y (arith-bubble-down x match))
                    (arith-collect-+ x y))))

(defthm arith-bubble-down-+-match-3
    (implies (syntaxp (equal match y))
             (equal (+ (arith-bubble-down x match) y z)
                    (+ (arith-collect-+ x y) z))))

(in-theory (disable arith-bubble-down))

(in-theory (disable arith-collect-*))

(in-theory (disable arith-collect-+))
