(in-package "RTL")

(include-book "util")
(include-book "std/util/defrule" :dir :system)
(include-book "ordinals/e0-ordinal" :dir :system)

(local (include-book "arithmetic-5/top" :dir :system))

;; From basic.lisp:

(defund fl (x)
  (declare (xargs :guard (real/rationalp x)))
  (floor x 1))

(defund cg (x)
  (declare (xargs :guard (real/rationalp x)))
  (- (fl (- x))))

(defund chop-r (x k radix)
  (declare (xargs :guard (and (real/rationalp x)
                              (integerp k)
                              (integerp radix)
                              (>= radix 2))))
  (/ (fl (* (expt radix k) x)) (expt radix k)))

(defund chop (x k)
  (/ (fl (* (expt 2 k) x)) (expt 2 k)))

;; From bits.lisp:

(defund bvecp (x k)
  (declare (xargs :guard (integerp k)))
  (and (integerp x)
       (<= 0 x)
       (< x (expt 2 k))))

(local (defrule natp-bvecp
  (implies (bvecp x k) (natp x))
  :enable bvecp
  :rule-classes :forward-chaining))

(defun nats (n) (if (zp n) () (cons (1- n) (nats (1- n)))))

(defund bits-exec (x i j)
  ;; The executable version of BITS
  (if (< i j)
      0
      (logand (ash x (- j))
              (1- (ash 1 (1+ (- i j)))))))

(defrule bits-mbe-lemma
  (implies (and (integerp x)
                (integerp i)
                (integerp j))
           (equal (fl (* (/ (expt 2 j)) (mod x (expt 2 (+ 1 i)))))
                  (bits-exec x i j)))
  :prep-lemmas (
    (defrule logand-as-mod
      (implies (and (integerp x) (natp n))
               (equal (logand x (1- (ash 1 n)))
                      (mod x (expt 2 n)))))
    (defrule bits-exec-rewrite
      (implies (and (integerp i) (integerp j))
               (= (bits-exec x i j)
                  (if (< i j)
                      0
                      (mod (ash x (- j)) (expt 2 (1+ (- i j)))))))
      :enable (bits-exec)
      :disable (ash mod))
    (defruled |mod-fl-expt|
      (equal (mod (fl x) (expt 2 i))
             (fl (mod x (expt 2 i))))
      :enable (fl)
      :cases ((real/rationalp x))
      :hints (("subgoal 1" :cases ((natp i)))))
    (defrule logic-rewrite
      (implies
        (and (integerp x) (integerp i) (integerp j))
        (equal
          (fl (* (expt 2 (- j)) (mod x (expt 2 (+ 1 i)))))
          (mod (fl (* x (expt 2 (- j)))) (expt 2 (+ 1 i (- j))))))
      :enable (|mod-fl-expt|))
    (defrule fl-as-floor
      (equal (fl (* x (expt 2 n)))
             (floor x (expt 2 (- n))))
      :enable fl))
  :rule-classes ())

(defund bits (x i j)
  (declare (xargs :guard (and (integerp x)
                              (integerp i)
                              (integerp j))
                  :guard-hints (("goal" :use (bits-mbe-lemma bits-exec)))))
  (mbe :logic (if (or (not (integerp i))
                      (not (integerp j)))
                  0
                (fl (/ (mod x (expt 2 (1+ i))) (expt 2 j))))
       :exec  (if (< i j)
                  0
                (logand (ash x (- j)) (1- (ash 1 (1+ (- i j))))))))

(local (defrule natp-bits
  (natp (bits x i j))
  :enable (bits fl)
  :rule-classes :type-prescription))

(defund bitn-exec (x n)
  (if (evenp (ash x (- n))) 0 1))

(defrule bitn-mbe-lemma
  (implies (and (integerp x)
                (integerp n))
           (equal (bits x n n)
                  (bitn-exec x n)))
  :prep-lemmas (
    (defrule lemma
      (implies
        (integerp x)
        (equal (logand x 1)
               (if (evenp x) 0 1)))))
  :enable (bits bits-exec bitn-exec)
  :disable (evenp ash mod)
  :use (:instance bits-mbe-lemma (i n) (j n))
  :rule-classes ())

(defund bitn (x n)
  (declare (xargs :guard (and (integerp x)
                              (integerp n))
                  :guard-hints (("goal" :use (bitn-mbe-lemma bitn-exec)))))
  (mbe :logic (bits x n n)
       :exec  (if (evenp (ash x (- n))) 0 1)))

(defun sumbits (x n)
  (if (zp n)
      0
    (+ (* (expt 2 (1- n)) (bitn x (1- n)))
       (sumbits x (1- n)))))

(defun all-bits-p (b k)
  (if (zp k)
      t
    (and (or (= (nth (1- k) b) 0)
	     (= (nth (1- k) b) 1))
	 (all-bits-p b (1- k)))))

(defun sum-b (b k)
  (if (zp k)
      0
    (+ (* (expt 2 (1- k)) (nth (1- k) b))
       (sum-b b (1- k)))))

(defrule bit-diff-measure-lemma
  (implies
    (and
      (= (bitn x 0) (bitn y 0))
      (integerp x)
      (integerp y)
      (not (= x y)))
    (< (+ (abs (fl (/ x 2)))
          (abs (fl (/ y 2))))
       (+ (abs x)
          (abs y))))
  :prep-lemmas (
    (defrule lemma
      (implies (and (integerp n)
                    (not (= n 0))
                    (not (= n -1)))
               (< (abs (fl (/ n 2))) (abs n)))
      :enable (fl)
      :rule-classes ()))
  :use ((:instance lemma (n x))
        (:instance lemma (n y)))
  :disable (abs)
  :rule-classes ())

(defun bit-diff (x y)
  (declare (xargs :measure (+ (abs (ifix x)) (abs (ifix y)))
                  :hints (("goal" :use bit-diff-measure-lemma))))
  (if (or (not (integerp x)) (not (integerp y)) (= x y))
      ()
    (if (= (bitn x 0) (bitn y 0))
        (1+ (bit-diff (fl (/ x 2)) (fl (/ y 2))))
      0)))

(defund binary-cat (x m y n)
  (declare (xargs :guard (and (integerp x)
                              (integerp y)
                              (natp m)
                              (natp n))))
  (if (and (natp m) (natp n))
      (+ (* (expt 2 n) (bits x (1- m) 0))
         (bits y (1- n) 0))
    0))

(local (defrule natp-binary-cat
  (natp (binary-cat x m y n))
  :enable (binary-cat)
  :rule-classes :type-prescription))

(defun formal-+ (x y)
  (declare (xargs :guard t))
  (if (and (acl2-numberp x) (acl2-numberp y))
      (+ x y)
    (list '+ x y)))

(defun cat-size (x)
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

(defund mulcat (l n x)
  (declare (xargs :guard (and (integerp l) (< 0 l) (acl2-numberp n) (natp x))
                  :verify-guards nil))
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

(local (defrule natp-mulcat
  (natp (mulcat l n x))
  :enable (mulcat)
  :rule-classes (:type-prescription)))

(verify-guards mulcat
  :hints (("goal" :in-theory (enable mulcat binary-cat))))

(defund si (r n)
  (if (= (bitn r (1- n)) 1)
      (- r (expt 2 n))
    r))

(defund sextend (m n r)
  (bits (si r n) (1- m) 0))

;; From float.lisp:

(defund sgn (x)
  (declare (xargs :guard t))
  (if (or (not (rationalp x)) (equal x 0))
      0
    (if (< x 0) -1 +1)))

(defun expo-measure (x)
  (cond ((not (real/rationalp x)) 0)
	((< x 0) '(2 . 0))
	((< x 1) (cons 1 (fl (/ x))))
	(t (fl x))))

(defund expo (x)
  (declare (xargs :guard t
                  :hints (("goal" :in-theory (enable fl)))
                  :well-founded-relation e0-ord-<
                  :measure (expo-measure x)))
  (cond ((or (not (rationalp x)) (equal x 0)) 0)
	((< x 0) (expo (- x)))
	((< x 1) (1- (expo (* 2 x))))
	((< x 2) 0)
	(t (1+ (expo (/ x 2))))))

(defund sig (x)
  (declare (xargs :guard t))
  (if (rationalp x)
      (if (< x 0)
          (- (* x (expt 2 (- (expo x)))))
        (* x (expt 2 (- (expo x)))))
    0))

(defund exactp (x n)
  (integerp (* (sig x) (expt 2 (1- n)))))

(defun fp+ (x n)
  (+ x (expt 2 (- (1+ (expo x)) n))))

(defun fp- (x n)
  (if (= x (expt 2 (expo x)))
      (- x (expt 2 (- (expo x) n)))
    (- x (expt 2 (- (1+ (expo x)) n)))))

;; From reps.lisp:

(encapsulate ()

(defund formatp (f)
  (declare (xargs :guard t))
  (and (consp f)
       (consp (cdr f))
       (consp (cddr f))
       (natp (cadr f))
       (> (cadr f) 1)
       (natp (caddr f))
       (> (caddr f) 1)))
(local (in-theory (enable formatp)))

(defund explicitp (f) (declare (xargs :guard (formatp f))) (car f))
(local (in-theory (enable explicitp)))

(defund prec (f) (declare (xargs :guard (formatp f))) (cadr f))
(local (in-theory (enable prec)))

(defund expw (f) (declare (xargs :guard (formatp f))) (caddr f))
(local (in-theory (enable expw)))

(defund sigw (f)
  (declare (xargs :guard (formatp f)))
  (if (explicitp f)
      (prec f)
    (1- (prec f))))
(local (in-theory (enable sigw)))

(defund encodingp (x f)
  (declare (xargs :guard (formatp f)))
  (bvecp x (+ 1 (expw f) (sigw f))))
(local (in-theory (enable encodingp)))

(defund sp () (declare (xargs :guard t)) '(nil 24 8))

(defund dp () (declare (xargs :guard t)) '(nil 53 11))

(defund ep () (declare (xargs :guard t)) '(t 64 15))

(in-theory (disable (sp) (dp) (ep)))

(defund sgnf (x f)
  (declare (xargs :guard (and (integerp x) (formatp f))))
  (bitn x (+ (expw f) (sigw f))))

(defund expf (x f)
  (declare (xargs :guard (and (integerp x) (formatp f))))
  (bits x (1- (+ (expw f) (sigw f))) (sigw f)))
(local (in-theory (enable expf)))

(defund sigf (x f)
  (declare (xargs :guard (and (integerp x) (formatp f))))
  (bits x (1- (sigw f)) 0))

(defund manf (x f)
  (declare (xargs :guard (and (integerp x) (formatp f))))
  (bits x (- (prec f) 2) 0))

(defund bias (f) (declare (xargs :guard (formatp f))) (- (expt 2 (- (expw f) 1)) 1))
(local (in-theory (enable bias)))

(defund normp (x f)
  (declare (xargs :guard (formatp f)))
  (and (encodingp x f)
       (< 0 (expf x f))
       (< (expf x f) (1- (expt 2 (expw f))))
       (implies (explicitp f) (= (bitn x (1- (prec f))) 1))))

(defund unsupp (x f)
  (declare (xargs :guard (formatp f)))
  (and (explicitp f)
       (encodingp x f)
       (< 0 (expf x f))
       (= (bitn x (1- (prec f))) 0)))

(defund ndecode (x f)
  (declare (xargs :guard (and (integerp x) (formatp f))))
  (* (if (= (sgnf x f) 0) 1 -1)
     (expt 2 (- (expf x f) (bias f)))
     (1+ (* (manf x f) (expt 2 (- 1 (prec f)))))))

(defund nrepp (x f)
  (and (rationalp x)
       (not (= x 0))
       (< 0 (+ (expo x) (bias f)))
       (< (+ (expo x) (bias f)) (1- (expt 2 (expw f))))
       (exactp x (prec f))))

(defund nencode (x f)
  (cat (if (= (sgn x) 1) 0 1)
       1
       (+ (expo x) (bias f))
       (expw f)
       (* (sig x) (expt 2 (1- (prec f))))
       (sigw f)))

(defund spn (f)
  (declare (xargs :guard (formatp f)))
  (expt 2 (- 1 (bias f))))

(defund lpn (f)
  (declare (xargs :guard (formatp f)))
  (* (expt 2 (- (expt 2 (expw f)) (+ 2 (bias f))))
     (- 2 (expt 2 (- 1 (prec f))))))

(defund zerp (x f)
  (declare (xargs :guard (formatp f)))
  (and (encodingp x f)
       (= (expf x f) 0)
       (= (sigf x f) 0)))

(defund zencode (sgn f) (cat sgn 1 0 (+ (sigw f) (expw f))))

(defund denormp (x f)
  (declare (xargs :guard (formatp f)))
  (and (encodingp x f)
       (= (expf x f) 0)
       (not (= (sigf x f) 0))
       (implies (explicitp f) (= (bitn x (1- (prec f))) 0))))

(defund pseudop (x f)
  (declare (xargs :guard (formatp f)))
  (and (explicitp f)
       (encodingp x f)
       (= (expf x f) 0)
       (= (bitn x (1- (prec f))) 1)))

(defund ddecode (x f)
  (declare (xargs :guard (and (integerp x) (formatp f))))
  (* (if (= (sgnf x f) 0) 1 -1)
     (sigf x f)
     (expt 2 (+ 2 (- (bias f)) (- (prec f))))))

(defund decode (x f)
  (declare (xargs :guard (and (integerp x) (formatp f))))
  (if (= (expf x f) 0)
      (ddecode x f)
    (ndecode x f)))

(defund drepp (x f)
  (and (rationalp x)
       (not (= x 0))
       (<= (- 2 (prec f)) (+ (expo x) (bias f)))
       (<= (+ (expo x) (bias f)) 0)
       (exactp x (+ (1- (prec f)) (bias f) (expo x)))))

(defund dencode (x f)
  (cat (if (= (sgn x) 1) 0 1)
       1
       0
       (expw f)
       (* (sig x) (expt 2 (+ -2 (prec f) (expo x) (bias f))))
       (sigw f)))

(defund spd (f)
     (declare (xargs :guard (formatp f)))
     (expt 2 (+ 2 (- (bias f)) (- (prec f)))))

(defund infp (x f)
  (declare (xargs :guard (formatp f)))
  (and (encodingp x f)
       (= (expf x f) (1- (expt 2 (expw f))))
       (not (unsupp x f))
       (= (manf x f) 0)))

(defun iencode (sgn f)
  (if (explicitp f)
      (cat sgn 1 (1- (expt 2 (expw f))) (expw f) 1 1 0 (1- (sigw f)))
    (cat sgn 1 (1- (expt 2 (expw f))) (expw f) 0 (sigw f))))

(defund nanp (x f)
  (declare (xargs :guard (formatp f)))
  (and (encodingp x f)
       (= (expf x f) (1- (expt 2 (expw f))))
       (not (unsupp x f))
       (not (= (manf x f) 0))))
(local (in-theory (enable nanp)))

(defund qnanp (x f)
  (declare (xargs :guard (formatp f)))
  (and (nanp x f) (= (bitn x (- (prec f) 2)) 1)))

(defund snanp (x f)
  (declare (xargs :guard (formatp f)))
  (and (nanp x f) (= (bitn x (- (prec f) 2)) 0)))

(defund qnanize (x f)
  (declare (xargs :guard (and (integerp x) (formatp f))))
  (logior x (expt 2 (- (prec f) 2))))

(defund indef (f)
  (if (explicitp f)
      (cat (1- (expt 2 (+ (expw f) 3)))
           (+ (expw f) 3)
           0
           (- (sigw f) 2))
    (cat (1- (expt 2 (+ (expw f) 2)))
         (+ (expw f) 2)
         0
         (1- (sigw f)))))

(defund rebias (expo old new)
  (+ expo (- (expt 2 (1- new)) (expt 2 (1- old)))))

(defund rtz (x n)
  (declare (xargs :guard (integerp n)))
  (* (sgn x)
     (fl (* (expt 2 (1- n)) (sig x)))
     (expt 2 (- (1+ (expo x)) n))))

(defund raz (x n)
  (* (sgn x)
     (cg (* (expt 2 (1- n)) (sig x)))
     (expt 2 (- (1+ (expo x)) n))))

(defun re (x)
  (- x (fl x)))

(defund rne (x n)
  (let ((z (fl (* (expt 2 (1- n)) (sig x))))
	(f (re (* (expt 2 (1- n)) (sig x)))))
    (if (< f 1/2)
	(rtz x n)
      (if (> f 1/2)
	  (raz x n)
	(if (evenp z)
	    (rtz x n)
	  (raz x n))))))

(defund rne-witness (x y n)
  (if (= (expo x) (expo y))
      (/ (+ (rne x n) (rne y n)) 2)
    (expt 2 (expo y))))

(defund rna (x n)
  (if (< (re (* (expt 2 (1- n)) (sig x)))
	 1/2)
      (rtz x n)
    (raz x n)))

(defund rna-witness (x y n)
  (if (= (expo x) (expo y))
      (/ (+ (rna x n) (rna y n)) 2)
    (expt 2 (expo y))))

(defund rto (x n)
  (if (exactp x (1- n))
      x
    (+ (rtz x (1- n))
       (* (sgn x) (expt 2 (1+ (- (expo x) n)))))))

(defun rup (x n)
  (if (>= x 0)
      (raz x n)
    (rtz x n)))

(defun rdn (x n)
  (if (>= x 0)
      (rtz x n)
    (raz x n)))

(defund IEEE-rounding-mode-p (mode)
  (member mode '(rtz rup rdn rne)))

(defund common-mode-p (mode)
  (or (IEEE-rounding-mode-p mode) (equal mode 'raz) (equal mode 'rna)))

(defund rnd (x mode n)
  (case mode
    (raz (raz x n))
    (rna (rna x n))
    (rtz (rtz x n))
    (rup (rup x n))
    (rdn (rdn x n))
    (rne (rne x n))
    (otherwise 0)))

(defund flip-mode (m)
  (case m
    (rup 'rdn)
    (rdn 'rup)
    (t m)))

(defun rnd-const (e mode n)
  (case mode
    ((rne rna) (expt 2 (- e n)))
    ((rup raz) (1- (expt 2 (1+ (- e n)))))
    (otherwise 0)))

(defund roundup-pos (x e sticky mode n)
  (case mode
    ((rup raz) (or (not (= (bits x (- e n) 0) 0))
                   (= sticky 1)))
    (rna (= (bitn x (- e n)) 1))
    (rne (and (= (bitn x (- e n)) 1)
               (or (not (= (bits x (- e (1+ n)) 0) 0))
                   (= sticky 1)
                   (= (bitn x (- (1+ e) n)) 1))))
    (otherwise ())))

(defund roundup-neg (x e sticky mode n)
  (case mode
    ((rdn raz) t)
    ((rup rtz) (and (= (bits x (- e n) 0) 0)
                    (= sticky 0)))
    (rna (or (= (bitn x (- e n)) 0)
             (and (= (bits x (- e (1+ n)) 0) 0)
                  (= sticky 0))))
    (rne (or (= (bitn x (- e n)) 0)
             (and (= (bitn x (- (1+ e) n)) 0)
                  (= (bits x (- e (1+ n)) 0) 0)
                  (= sticky 0))))
    (otherwise ())))

(defund drnd (x mode f)
  (rnd x mode (+ (prec f) (expo x) (- (expo (spn f))))))

)

;; from sqrt.lisp:

(defund rtz-sqrt (x n)
  (if (zp n)
      0
    (let* ((lower (rtz-sqrt x (1- n)))
           (upper (+ lower (expt 2 (- n)))))
      (if (<= (* upper upper) x)
          upper
        lower))))
; ACL2 derives this type-prescription rule from the above definition, but it
; doesn't export it properly.
(defrule nonnegative-rtz-sqrt
  (>= (rtz-sqrt x n) 0)
  :rule-classes :type-prescription)

(defund rto-sqrt (x n)
  (let ((trunc (rtz-sqrt x (1- n))))
    (if (< (* trunc trunc) x)
        (+ trunc (expt 2 (- n)))
      trunc)))

(defund qsqrt (x n)
  (let ((e (1+ (fl (/ (expo x) 2)))))
    (* (expt 2 e)
       (rto-sqrt (/ x (expt 2 (* 2 e))) n))))
