(in-package "RTL")

(include-book "tools/with-arith5-help" :dir :system)
(local (acl2::allow-arith5-help))
(local (in-theory (acl2::enable-arith5)))

(include-book "util")
(include-book "std/util/defrule" :dir :system)
(include-book "ordinals/e0-ordinal" :dir :system)

;; From basic.lisp:

(defund fl (x)
  (declare (xargs :guard (real/rationalp x)))
  (floor x 1))

(defund cg (x)
  (declare (xargs :guard (real/rationalp x)))
  (- (fl (- x))))

(defund congruent (a b n)
  (declare (xargs :guard (and (real/rationalp a)
                              (real/rationalp b)
                              (real/rationalp n)
                              (not (= n 0)))))
  (equal (mod a n) (mod b n)))

(defnd radixp (b)
  (and (integerp b) (>= b 2)))

(defrule radixp-forward
  (implies (radixp b)
           (and (integerp b) (>= b 2)))
  :rule-classes :forward-chaining)

(defmacro digitp (x b)
  `(and (natp ,x) (< ,x ,b)))

(defund chop-r (x k r)
  (declare (xargs :guard (and (real/rationalp x)
                              (integerp k)
                              (radixp r))))
  (/ (fl (* (expt r k) x)) (expt r k)))

(defund chop (x k)
  (declare (xargs :guard (and (real/rationalp x)
                              (integerp k))))
  (/ (fl (* (expt 2 k) x)) (expt 2 k)))

;; From bits.lisp:

(defnd dvecp (x k b)
;  (declare (xargs :guard (and (natp k)
;                              (radixp b))))
  (and (natp x)
       (natp k)
       (radixp b)
       (< x (expt b k))))

(defund bvecp (x k)
  (declare (xargs :guard (integerp k)))
  (and (integerp x)
       (<= 0 x)
       (< x (expt 2 k))))

(local (defrule natp-bvecp
  (implies (bvecp x k) (natp x))
  :enable bvecp
  :rule-classes :forward-chaining))

(defun nats (n)
  (declare (xargs :guard (natp n)))
  (if (zp n) () (cons (1- n) (nats (1- n)))))

(defund digits (x i j b)
  (declare (xargs :guard (and (real/rationalp x)
                              (integerp i)
                              (integerp j)
                              (radixp b))))
  (if (or (not (integerp i))
          (not (integerp j)))
      0
      (fl (* (mod x (expt b (1+ i))) (expt b (- j))))))

(defrule digits-nonnegative-integerp-type
  (implies (radixp b)
           (natp (digits x i j b)))
  :enable (digits fl)
  :rule-classes :type-prescription)

(in-theory (disable (:type-prescription digits)))

(defund bits-exec (x i j)
  ;; The executable version of BITS
  (declare (xargs :guard (and (integerp x)
                              (integerp i)
                              (integerp j))))
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

(defrule bits-nonnegative-integerp-type
  (and (<= 0 (bits x i j))
       (integerp (bits x i j)))
  :enable (bits fl)
  :rule-classes :type-prescription)

(in-theory (disable (:type-prescription bits)))

(defund digitn (x n b)
  (declare (xargs :guard (and (real/rationalp x)
                              (integerp n)
                              (radixp b))))
  (digits x n n b))

(defrule digitn-nonnegative-integer
  (implies (radixp b)
           (natp (digitn x n b)))
  :enable digitn
  :rule-classes (:type-prescription))

(in-theory (disable (:type-prescription digitn)))

(defund bitn-exec (x n)
  (declare (xargs :guard (and (integerp x)
                              (integerp n))))
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

(defrule bitn-nonnegative-integer
  (and (integerp (bitn x n))
       (<= 0 (bitn x n)))
  :rule-classes (:type-prescription))

(in-theory (disable (:type-prescription bitn)))

(defun sumdigits (x n b)
  (declare (xargs :guard (and (integerp x)
                              (natp n)
                              (radixp b))))
  (if (zp n)
      0
    (+ (* (expt b (1- n)) (digitn x (1- n) b))
       (sumdigits x (1- n) b))))

(defun sumbits (x n)
  (declare (xargs :guard (and (integerp x)
                              (natp n))))
  (if (zp n)
      0
    (+ (* (expt 2 (1- n)) (bitn x (1- n)))
       (sumbits x (1- n)))))

(defnd all-digits-p (list k b)
  (declare (xargs :guard-hints (("goal" :induct (all-digits-p list k b)))))
  (if (posp k)
      (and (consp list)
           (all-digits-p (cdr list) (1- k) b)
           (digitp (car list) b))
    (and (true-listp list)
         (equal k 0)
         (radixp b))))

(defrule all-digits-p-forward
  (implies (all-digits-p list k b)
           (and (true-listp list)
                (natp k)
                (<= k (len list))
                (radixp b)))
  :enable all-digits-p
  :induct (all-digits-p list k b)
  :rule-classes :forward-chaining)

(defrule nth-all-digits-p
  (implies (and (all-digits-p list k b)
                (natp i)
                (integerp k)
                (< i k))
           (digitp (nth i list) b))
  :prep-lemmas (
    (defrule lemma
      (implies (and (all-digits-p list (+ k i) b)
                    (natp i)
                    (posp k))
               (digitp (nth i list) b))
      :enable (all-digits-p)
      :induct (nth i list)))
  :use (:instance lemma (k (- k i)))
  :rule-classes ())

(defnd all-bits-p (b k)
  (declare (xargs :guard-hints (("goal" :induct (all-bits-p b k)))))
  (if (posp k)
      (and (consp b)
           (all-bits-p (cdr b) (1- k))
           (or (equal (car b) 0)
               (equal (car b) 1)))
    (and (true-listp b)
         (equal k 0))))

(defun sum-d (list k b)
  (declare (xargs :guard (all-digits-p list k b)
                  :guard-hints (("goal" :in-theory (enable all-digits-p)))))
  (if (zp k)
      0
    (+ (* (expt b (1- k)) (nth (1- k) list))
       (sum-d list (1- k) b))))

(defun sum-b (b k)
  (declare (xargs :guard (all-bits-p b k)
                  :guard-hints (("goal" :in-theory (enable all-bits-p)))))
  (if (zp k)
      0
    (+ (* (expt 2 (1- k)) (nth (1- k) b))
       (sum-b b (1- k)))))

(local
 (defrule digit-diff-measure-lemma
   (implies
    (and (= (digitn x 0 b) (digitn y 0 b))
         (integerp x)
         (integerp y)
         (not (= x y))
         (radixp b))
    (< (+ (abs (fl (/ x b)))
          (abs (fl (/ y b))))
       (+ (abs x)
          (abs y))))
   :prep-lemmas (
     (defrule digitn-0
       (implies (radixp b)
                (equal (digitn 0 0 b) 0))
       :enable (digitn digits))
     (defrule digitn--1
       (implies (radixp b)
                (equal (digitn -1 0 b) (1- b)))
       :enable (digitn digits fl))
     (defrule abs-type
       (implies (integerp x)
                (integerp (abs x)))
       :rule-classes :type-prescription)
     (defrule abs-fl--1
       (implies (radixp b)
                (equal (abs (fl (- (/ b)))) 1))
       :enable fl)
     (defrule lemma
       (implies (and (integerp n)
                     (not (= n 0))
                     (not (= n -1))
                     (radixp b))
                (< (abs (fl (/ n b))) (abs n)))
       :enable (fl)
       :rule-classes ()))
   :use ((:instance lemma (n x))
         (:instance lemma (n y)))
   :disable (abs)
   :rule-classes ()))

(defn digit-diff (x y b)
  (declare (xargs :verify-guards nil
                  :measure (+ (abs (ifix x)) (abs (ifix y)))
                  :hints (("goal" :use digit-diff-measure-lemma))))
  (if (or (not (integerp x))
          (not (integerp y))
          (not (radixp b))
          (= x y))
      ()
    (if (= (digitn x 0 b) (digitn y 0 b))
        (1+ (digit-diff (fl (/ x b)) (fl (/ y b)) b))
      0)))

(defrule digit-diff-nonnegative-integer
  (implies (and (integerp x)
                (integerp y)
                (radixp b)
                (not (= x y)))
           (natp (digit-diff x y b)))
  :induct (digit-diff x y b)
  :rule-classes :type-prescription)

(local
 (defrule bit-diff-measure-lemma
   (implies
    (and (= (bitn x 0) (bitn y 0))
         (integerp x)
         (integerp y)
         (not (= x y)))
    (< (+ (abs (fl (/ x 2)))
          (abs (fl (/ y 2))))
       (+ (abs x)
          (abs y))))
   :prep-lemmas (
     (defrule bitn-as-digitn
       (equal (bitn x n) (digitn x n 2))
       :enable (bitn digitn bits digits)))
   :use (:instance digit-diff-measure-lemma (b 2))))

(defn bit-diff (x y)
  (declare (xargs :verify-guards nil
                  :measure (+ (abs (ifix x)) (abs (ifix y)))
                  :hints (("goal" :use bit-diff-measure-lemma))))
  (if (or (not (integerp x)) (not (integerp y)) (= x y))
      ()
    (if (= (bitn x 0) (bitn y 0))
        (1+ (bit-diff (fl (/ x 2)) (fl (/ y 2))))
      0)))

(defrule bit-diff-nonnegative-integer
  (implies (and (integerp x)
                (integerp y)
                (not (= x y)))
           (natp (bit-diff x y)))
  :rule-classes :type-prescription)

(defund radix-cat (b x m y n)
  (declare (xargs :guard (and (dvecp x m b)
                              (dvecp y n b))
                  :guard-hints (("goal" :in-theory (enable dvecp)))))
  (if (and (natp m) (natp n))
      (+ (* (digits x (1- m) 0 b) (expt b n))
         (digits y (1- n) 0 b))
    0))

(defund binary-cat (x m y n)
  (declare (xargs :guard (and (integerp x)
                              (integerp y)
                              (natp m)
                              (natp n))
                  :verify-guards nil))
  (if (and (natp m) (natp n))
      (+ (* (expt 2 n) (bits x (1- m) 0))
         (bits y (1- n) 0))
    0))

(defn formal-+ (x y)
  (if (and (acl2-numberp x) (acl2-numberp y))
      (+ x y)
    (list '+ x y)))

(defun cat-size (x)
  (declare (xargs :guard (and (true-listp x)
                              (evenp (length x)))))
  (if (endp (cddr x))
      (cadr x)
    (formal-+ (cadr x)
	      (cat-size (cddr x)))))

;; We define macros, CAT-R and CAT, that take a list of alternating data values and
;; sizes.  CAT-SIZE returns the formal sum of the sizes.  The list must contain
;; at least 1 data/size pair, but we do not need to specify this in the guard,
;; and leaving it out of the guard simplifies the guard proof.

(defmacro cat-r (b &rest x)
  (declare (xargs :guard (and x (true-listp x) (evenp (length x)))))
  (cond ((endp (cddr x))
         `(digits ,(car x) ,(formal-+ -1 (cadr x)) 0 ,b))
        ((endp (cddddr x))
         `(radix-cat ,b ,@x))
        (t
         `(radix-cat ,b
                     ,(car x)
                     ,(cadr x)
                     (cat-r ,b ,@(cddr x))
                     ,(cat-size (cddr x))))))

(defrule cat-r-nonnegative-integer-type
  (implies (radixp b)
           (natp (cat-r b x m y n)))
  :enable radix-cat
  :rule-classes (:type-prescription))

(in-theory (disable (:type-prescription radix-cat)))

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

(defrule cat-nonnegative-integer-type
  (and (integerp (cat x m y n))
       (<= 0 (cat x m y n)))
  :rule-classes (:type-prescription))

(in-theory (disable (:type-prescription binary-cat)))

(defund mulcat-r (l n x b)
  (declare (xargs :guard (and (natp n)
                              (dvecp x l b))
                  :verify-guards nil))
  (if (and (integerp n) (> n 0))
      (cat-r b (mulcat-r l (1- n) x b)
             (* l (1- n))
             x
             l)
    0))

(defrule mulcat-r-nonnegative-integer-type
  (implies (radixp b)
           (natp (mulcat-r l n x b)))
  :enable mulcat-r
  :induct (sub1-induction n)
  :rule-classes (:type-prescription))

(in-theory (disable (:type-prescription mulcat-r)))

(defund mulcat (l n x)
  (declare (xargs :guard (and (natp l)
                              (natp n)
                              (natp x))
                  :verify-guards nil))
  (if (and (integerp n) (> n 0))
      (cat (mulcat l (1- n) x)
           (* l (1- n))
           x
           l)
    0))

(defrule mulcat-nonnegative-integer-type
  (and (integerp (mulcat l n x))
       (<= 0 (mulcat l n x)))
  :rule-classes (:type-prescription))

(in-theory (disable (:type-prescription mulcat)))

(defund ui-r (r n b)
  (declare (xargs :guard (and (real/rationalp r)
                              (integerp n)
                              (radixp b))))
  (mod (realfix r) (expt b n)))

(defrule ui-r-real/rational>=0
  (implies (radixp b)
           (and (real/rationalp (ui-r r n b))
                (>= (ui-r r n b) 0)))
  :enable ui-r
  :rule-classes :type-prescription)

(defrule ui-r-nat
  (implies (and (integerp r)
                (radixp b))
           (natp (ui-r r n b)))
  :enable ui-r
  :cases ((posp n))
  :rule-classes :type-prescription)

(defnd ui (r) r)

(defrule ui-nat
  (implies (natp r)
           (natp (ui r)))
  :rule-classes :type-prescription)

(defund si-r (r n b)
  (declare (xargs :guard (and (real/rationalp r)
                              (integerp n)
                              (radixp b))))
  (let ((r (mod (realfix r) (expt b n))))
    (if (>= r (/ (expt b n) 2))
        (- r (expt b n))
      r)))

(defrule si-r-real/rational
  (implies (radixp b)
           (real/rationalp (si-r r n b)))
  :enable si-r
  :rule-classes :type-prescription)

(defrule si-r-integer
  (implies (and (integerp r)
                (radixp b))
           (integerp (si-r r n b)))
  :enable si-r
  :cases ((posp n))
  :rule-classes :type-prescription)

(defund si (r n)
  (declare (xargs :guard (and (integerp r)
                              (natp n))))
  (if (= (bitn r (1- n)) 1)
      (- r (expt 2 n))
    r))

(defrule si-integer
  (implies (integerp r)
           (integerp (si r n)))
  :enable si
  :cases ((posp n))
  :hints (("subgoal 2" :in-theory (enable bitn bits)))
  :rule-classes :type-prescription)

(defund sextend-r (m n r b)
  (declare (xargs :guard (and (real/rationalp r)
                              (integerp m)
                              (integerp n)
                              (radixp b))
                  :guard-hints (("goal" :in-theory (enable si-r)))))
  (mod (si-r r n b) (expt b m)))

(defund sextend (m n r)
  (declare (xargs :guard (and (natp m)
                              (natp n)
                              (integerp r))))
  (bits (si r n) (1- m) 0))

(defund uf-r (r n m b)
  (declare (xargs :guard (and (real/rationalp r)
                              (integerp n)
                              (integerp m)
                              (radixp b))))
  (* (expt b (- m n)) (ui-r r n b)))

(defrule uf-r-real/rational>=0
  (implies (radixp b)
           (and (real/rationalp (uf-r r n m b))
                (>= (uf-r r n m b) 0)))
  :rule-classes :type-prescription
  :enable uf-r)

(defrule uf-r-nat
  (implies (and (>= m n)
                (integerp r)
                (radixp b))
           (natp (uf-r r n m b)))
  :rule-classes :type-prescription
  :enable uf-r)

(defund uf (r n m)
  (declare (xargs :guard (and (natp r)
                              (natp n)
                              (natp m))))
  (* (expt 2 (- m n)) (ui r)))

(defund sf-r (r n m b)
  (declare (xargs :guard (and (real/rationalp r)
                              (integerp n)
                              (integerp m)
                              (radixp b))))
  (* (expt b (- m n)) (si-r r n b)))

(defrule sf-r-real/rational
  (implies (radixp b)
           (real/rationalp (sf-r r n m b)))
  :rule-classes :type-prescription
  :enable sf-r)

(defrule sf-r-integer
  (implies (and (>= m n)
                (integerp r)
                (radixp b))
           (integerp (sf-r r n m b)))
  :rule-classes :type-prescription
  :enable sf-r)

(defund sf (r n m)
  (declare (xargs :guard (and (integerp r)
                              (natp n)
                              (natp m))))
  (* (expt 2 (- m n)) (si r n)))

;; From float.lisp:

(defnd sgn (x)
  (if (or (not (rationalp x)) (equal x 0))
      0
    (if (< x 0) -1 +1)))

(defun expo-measure (x)
  (cond ((not (real/rationalp x)) 0)
	((< x 0) '(2 . 0))
	((< x 1) (cons 1 (fl (/ x))))
	(t (fl x))))

(local
 (defrule e0-oridnalp-expo-measure
   (e0-ordinalp (expo-measure x))
   :enable fl))

(local
 (defrule e0-ord-<-expo-measure
   (implies (and (real/rationalp x)
                 (radixp b))
            (and (implies (< x 0)
                          (e0-ord-< (expo-measure (- x))
                                    (expo-measure x)))
                 (implies (and (< 0 x) (< x 1))
                          (e0-ord-< (expo-measure (* b x))
                                    (expo-measure x)))
                 (implies (<= b x)
                          (e0-ord-< (expo-measure (* (/ b) x))
                                    (expo-measure x)))))
   :prep-lemmas (
     (acl2::with-arith5-nonlinear-help
      (defrule lemma
        (implies (and (real/rationalp x) (>= x 1) (radixp b))
                 (< (fl (* (/ b) x)) (fl x)))
        :enable fl)))))

; e from IEEE 754-2008
(defund expe (x b)
  (declare (xargs :guard (and (real/rationalp x)
                              (radixp b))
                  :hints (("goal" :in-theory (disable expo-measure)))
                  :well-founded-relation e0-ord-<
                  :measure (expo-measure (realfix x))))
  (cond ((not (mbt (real/rationalp x))) 0)
        ((not (mbt (radixp b))) 0)
        ((equal x 0) 0)
        ((< x 0) (expe (- x) b))
        ((< x 1) (1- (expe (* b x) b)))
        ((< x b) 0)
        (t (1+ (expe (/ x b) b)))))

; q from IEEE 754-2008
(defund expq (x p b)
  (declare (xargs :guard (and (real/rationalp x)
                              (integerp p)
                              (radixp b))))
  (- (expe x b) (1- p)))

(defrule expq-integer-type
  (implies (integerp p)
           (integerp (expq x p b)))
  :enable expq
  :rule-classes :type-prescription)

(in-theory (disable (:type-prescription expq)))

(defnd expo (x)
  (declare (xargs :hints (("goal" :in-theory (enable fl)))
                  :well-founded-relation e0-ord-<
                  :measure (expo-measure x)
                  :verify-guards nil))
  (mbe :logic (cond ((or (not (rationalp x)) (equal x 0)) 0)
                    ((< x 0) (expo (- x)))
                    ((< x 1) (1- (expo (* 2 x))))
                    ((< x 2) 0)
                    (t (1+ (expo (/ x 2)))))
       :exec (if (rationalp x)
                 (let* ((n (abs (numerator x)))
                        (d (denominator x))
                        (ln (integer-length n))
                        (ld (integer-length d))
                        (l (- ln ld)))
                   (if (>= ln ld)
                       (if (>= (ash n (- l)) d) l (1- l))
                     (if (> ln 1)
                         (if (> n (ash d l)) l (1- l))
                       (- (integer-length (1- d))))))
               0)))

; m from IEEE 754-2008
(defund sigm (x b)
  (declare (xargs :guard (and (real/rationalp x)
                              (radixp b))))
  (cond ((not (mbt (real/rationalp x))) 0)
        ((not (mbt (radixp b))) 0)
        (t (* (abs x) (expt b (- (expe x b)))))))

; c from IEEE 754-2008
(defund sigc (x p b)
  (declare (xargs :guard (and (real/rationalp x)
                              (integerp p)
                              (radixp b))))
  (* (sigm x b) (expt b (1- p))))

(defnd sig (x)
  (declare (xargs :verify-guards nil))
  (if (rationalp x)
      (if (< x 0)
          (- (* x (expt 2 (- (expo x)))))
        (* x (expt 2 (- (expo x)))))
    0))

(defnd exactrp (x p b)
  (and (real/rationalp x)
       (integerp p)
       (radixp b)
       (integerp (sigc x p b))))

(defund exactp (x n)
  (declare (xargs :guard (and (real/rationalp x)
                              (integerp n))
                  :verify-guards nil))
  (integerp (* (sig x) (expt 2 (1- n)))))

(defun fpr+ (x p b)
  (declare (xargs :guard (and (exactrp x p b) (> x 0))
                  :guard-hints (("goal" :in-theory (enable exactrp)))))
  (+ x (expt b (expq x p b))))

(defun fp+ (x n)
  (declare (xargs :guard (and (real/rationalp x)
                              (integerp n))
                  :verify-guards nil))
  (+ x (expt 2 (- (1+ (expo x)) n))))

(defun fpr- (x p b)
  (declare (xargs :guard (and (exactrp x p b) (> x 0))
                  :guard-hints (("goal" :in-theory (enable exactrp)))))
  (if (= x (expt b (expe x b)))
      (- x (expt b (expq x (1+ p) b)))
    (- x (expt b (expq x p b)))))

(defun fp- (x n)
  (declare (xargs :guard (and (real/rationalp x)
                              (integerp n))
                  :verify-guards nil))
  (if (= x (expt 2 (expo x)))
      (- x (expt 2 (- (expo x) n)))
    (- x (expt 2 (- (1+ (expo x)) n)))))

;; From reps.lisp:

(defnd formatp (f)
  (and (consp f)
       (consp (cdr f))
       (consp (cddr f))
       (natp (cadr f))
       (> (cadr f) 1)
       (natp (caddr f))
       (> (caddr f) 1)))

(defund explicitp (f)
  (declare (xargs :guard (formatp f)
                  :guard-hints (("goal" :in-theory (enable formatp)))))
  (car f))

(defund prec (f)
  (declare (xargs :guard (formatp f)
                  :guard-hints (("goal" :in-theory (enable formatp)))))
  (cadr f))

(defrule prec-positive-integer-type
  (implies (formatp f)
           (posp (prec f)))
  :enable (formatp prec)
  :rule-classes :type-prescription)

(defund expw (f)
  (declare (xargs :guard (formatp f)
                  :guard-hints (("goal" :in-theory (enable formatp)))))
  (caddr f))

(defrule expw-positive-integer-type
  (implies (formatp f)
           (posp (expw f)))
  :enable (formatp expw)
  :rule-classes :type-prescription)

(defund sigw (f)
  (declare (xargs :guard (formatp f)))
  (if (explicitp f)
      (prec f)
    (1- (prec f))))

(defrule sigw-positive-integer-type
  (implies (formatp f)
           (posp (sigw f)))
  :enable (formatp sigw prec)
  :rule-classes :type-prescription)

(defnd encodingp (x f)
  (and (formatp f) (bvecp x (+ 1 (expw f) (sigw f)))))

(defnd hp () '(nil  11 5))

(defnd sp () '(nil 24 8))

(defnd dp () '(nil 53 11))

(defnd ep () '(t 64 15))

(defnd bf () '(nil 8 8))

(in-theory (disable (hp) (sp) (dp) (ep) (bf)))

(defund sgnf (x f)
  (declare (xargs :guard (encodingp x f)
                  :guard-hints (("goal" :in-theory (enable encodingp)))))
  (bitn x (+ (expw f) (sigw f))))

;(defrule sgnf-nonnegative-integer-type
;  (natp (sgnf x f))
;  :rule-classes :type-prescription)

(defund expf (x f)
  (declare (xargs :guard (encodingp x f)
                  :guard-hints (("goal" :in-theory (enable encodingp)))))
  (bits x (1- (+ (expw f) (sigw f))) (sigw f)))

;(defrule expf-nonnegative-integer-type
;  (natp (expf x f))
;  :rule-classes :type-prescription)

(defund sigf (x f)
  (declare (xargs :guard (encodingp x f)
                  :guard-hints (("goal" :in-theory (enable encodingp)))))
  (bits x (1- (sigw f)) 0))

;(defrule sigf-nonnegative-integer-type
;  (natp (sigf x f))
;  :rule-classes :type-prescription)

(defund manf (x f)
  (declare (xargs :guard (encodingp x f)
                  :guard-hints (("goal" :in-theory (enable encodingp)))))
  (bits x (- (prec f) 2) 0))

;(defrule manf-nonnegative-integer-type
;  (natp (sigf x f))
;  :rule-classes :type-prescription)

(defund bias (f)
  (declare (xargs :guard (formatp f)))
  (- (expt 2 (- (expw f) 1)) 1))

(defrule bias-positive-integer-type
  (implies (formatp f)
           (posp (bias f)))
  :enable (formatp bias expw)
  :rule-classes :type-prescription)

(defund normp (x f)
  (declare (xargs :guard (encodingp x f)
                  :guard-hints (("goal" :in-theory (enable encodingp)))))
  (and (mbt (encodingp x f))
       (< 0 (expf x f))
       (< (expf x f) (1- (expt 2 (expw f))))
       (implies (explicitp f) (= (bitn x (1- (prec f))) 1))))

(defund unsupp (x f)
  (declare (xargs :guard (encodingp x f)
                  :guard-hints (("goal" :in-theory (enable encodingp)))))
  (and (mbt (encodingp x f))
       (explicitp f)
       (< 0 (expf x f))
       (= (bitn x (1- (prec f))) 0)))

(defund ndecode (x f)
  (declare (xargs :guard (encodingp x f)
                  :guard-hints (("goal" :in-theory (enable encodingp)))))
  (* (if (= (sgnf x f) 0) 1 -1)
     (expt 2 (- (expf x f) (bias f)))
     (1+ (* (manf x f) (expt 2 (- 1 (prec f)))))))

(defnd nrepp (x f)
  (declare (xargs :verify-guards nil))
  (and (rationalp x)
       (formatp f)
       (not (= x 0))
       (< 0 (+ (expo x) (bias f)))
       (< (+ (expo x) (bias f)) (1- (expt 2 (expw f))))
       (exactp x (prec f))))

(defund nencode (x f)
  (declare (xargs :guard (nrepp x f)
                  :verify-guards nil))
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
  (declare (xargs :guard (encodingp x f)))
  (and (mbt (encodingp x f))
       (= (expf x f) 0)
       (= (sigf x f) 0)))

(defund zencode (sgn f)
  (declare (xargs :guard (and (bvecp sgn 1)
                              (formatp f))
                  :verify-guards nil))
  (cat sgn 1 0 (+ (sigw f) (expw f))))

(defund denormp (x f)
  (declare (xargs :guard (encodingp x f)
                  :guard-hints (("goal" :in-theory (enable encodingp)))))
  (and (mbt (encodingp x f))
       (= (expf x f) 0)
       (not (= (sigf x f) 0))
       (implies (explicitp f) (= (bitn x (1- (prec f))) 0))))

(defund pseudop (x f)
  (declare (xargs :guard (encodingp x f)
                  :guard-hints (("goal" :in-theory (enable encodingp)))))
  (and (mbt (encodingp x f))
       (explicitp f)
       (= (expf x f) 0)
       (= (bitn x (1- (prec f))) 1)))

(defund ddecode (x f)
  (declare (xargs :guard (encodingp x f)
                  :guard-hints (("goal" :in-theory (enable encodingp)))))
  (* (if (= (sgnf x f) 0) 1 -1)
     (sigf x f)
     (expt 2 (+ 2 (- (bias f)) (- (prec f))))))

(defund decode (x f)
  (declare (xargs :guard (encodingp x f)))
  (if (= (expf x f) 0)
      (ddecode x f)
    (ndecode x f)))

(defnd drepp (x f)
  (declare (xargs :verify-guards nil))
  (and (rationalp x)
       (formatp f)
       (not (= x 0))
       (<= (- 2 (prec f)) (+ (expo x) (bias f)))
       (<= (+ (expo x) (bias f)) 0)
       (exactp x (+ (1- (prec f)) (bias f) (expo x)))))

(defund dencode (x f)
  (declare (xargs :guard (drepp x f)
                  :verify-guards nil))
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
  (declare (xargs :guard (encodingp x f)
                  :guard-hints (("goal" :in-theory (enable encodingp)))))
  (and (mbt (encodingp x f))
       (= (expf x f) (1- (expt 2 (expw f))))
       (not (unsupp x f))
       (= (manf x f) 0)))

(defun iencode (sgn f)
  (declare (xargs :guard (and (bvecp sgn 1)
                              (formatp f))
                  :verify-guards nil))
  (if (explicitp f)
      (cat sgn 1 (1- (expt 2 (expw f))) (expw f) 1 1 0 (1- (sigw f)))
    (cat sgn 1 (1- (expt 2 (expw f))) (expw f) 0 (sigw f))))

(defund nanp (x f)
  (declare (xargs :guard (encodingp x f)
                  :guard-hints (("goal" :in-theory (enable encodingp)))))
  (and (mbt (encodingp x f))
       (= (expf x f) (1- (expt 2 (expw f))))
       (not (unsupp x f))
       (not (= (manf x f) 0))))
(local (in-theory (enable nanp)))

(defund qnanp (x f)
  (declare (xargs :guard (encodingp x f)
                  :guard-hints (("goal" :in-theory (enable encodingp)))))
  (and (nanp x f) (= (bitn x (- (prec f) 2)) 1)))

(defund snanp (x f)
  (declare (xargs :guard (encodingp x f)
                  :guard-hints (("goal" :in-theory (enable encodingp)))))
  (and (nanp x f) (= (bitn x (- (prec f) 2)) 0)))

(defund qnanize (x f)
  (declare (xargs :guard (encodingp x f)
                  :guard-hints (("goal" :in-theory (enable encodingp formatp prec)))))
  (logior x (expt 2 (- (prec f) 2))))

(defund indef (f)
  (declare (xargs :guard (formatp f)
                  :verify-guards nil))
  (if (explicitp f)
      (cat (1- (expt 2 (+ (expw f) 2)))
           (+ (expw f) 2)
           0
           (- (sigw f) 2))
    (cat (1- (expt 2 (+ (expw f) 1)))
         (+ (expw f) 1)
         0
         (1- (sigw f)))))

(defund rebias (expo old new)
  (declare (xargs :guard (and (integerp expo)
                              (posp old)
                              (posp new))))
  (+ expo (- (expt 2 (1- new)) (expt 2 (1- old)))))

(defund rtz (x n)
  (declare (xargs :guard (and (real/rationalp x)
                              (integerp n))
                  :verify-guards nil))
  (* (sgn x)
     (fl (* (expt 2 (1- n)) (sig x)))
     (expt 2 (- (1+ (expo x)) n))))

(defund raz (x n)
  (declare (xargs :guard (and (real/rationalp x)
                              (integerp n))
                  :verify-guards nil))
  (* (sgn x)
     (cg (* (expt 2 (1- n)) (sig x)))
     (expt 2 (- (1+ (expo x)) n))))

(defun re (x)
  (declare (xargs :guard (real/rationalp x)))
  (- x (fl x)))

(defund rne (x n)
  (declare (xargs :guard (and (real/rationalp x)
                              (integerp n))
                  :verify-guards nil))
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
  (declare (xargs :guard (and (real/rationalp x)
                              (integerp n))
                  :verify-guards nil))
  (if (< (re (* (expt 2 (1- n)) (sig x)))
	 1/2)
      (rtz x n)
    (raz x n)))

(defund rna-witness (x y n)
  (if (= (expo x) (expo y))
      (/ (+ (rna x n) (rna y n)) 2)
    (expt 2 (expo y))))

(defund rto (x n)
  (declare (xargs :guard (and (real/rationalp x)
                              (integerp n))
                  :verify-guards nil))
  (if (exactp x (1- n))
      x
    (+ (rtz x (1- n))
       (* (sgn x) (expt 2 (1+ (- (expo x) n)))))))

(defun rup (x n)
  (declare (xargs :guard (and (real/rationalp x)
                              (integerp n))
                  :verify-guards nil))
  (if (>= x 0)
      (raz x n)
    (rtz x n)))

(defun rdn (x n)
  (declare (xargs :guard (and (real/rationalp x)
                              (integerp n))
                  :verify-guards nil))
  (if (>= x 0)
      (rtz x n)
    (raz x n)))

(defnd IEEE-rounding-mode-p (mode)
  (member mode '(rtz rup rdn rne)))

(defnd common-mode-p (mode)
  (or (IEEE-rounding-mode-p mode) (equal mode 'raz) (equal mode 'rna)))

(defund rnd (x mode n)
  (declare (xargs :guard (and (real/rationalp x)
                              (common-mode-p mode)
                              (integerp n))
                  :verify-guards nil))
  (case mode
    (raz (raz x n))
    (rna (rna x n))
    (rtz (rtz x n))
    (rup (rup x n))
    (rdn (rdn x n))
    (rne (rne x n))
    (otherwise 0)))

(defund flip-mode (m)
  (declare (xargs :guard (common-mode-p m)))
  (case m
    (rup 'rdn)
    (rdn 'rup)
    (t m)))

(defun rnd-const (e mode n)
  (declare (xargs :guard (and (integerp e)
                              (common-mode-p mode)
                              (integerp n))))
  (case mode
    ((rne rna) (expt 2 (- e n)))
    ((rup raz) (1- (expt 2 (1+ (- e n)))))
    (otherwise 0)))

(defund roundup-pos (x e sticky mode n)
  (declare (xargs :guard (and (integerp x)
                              (integerp e)
                              (integerp sticky)
                              (common-mode-p mode)
                              (integerp n))))
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
  (declare (xargs :guard (and (integerp x)
                              (integerp e)
                              (integerp sticky)
                              (common-mode-p mode)
                              (integerp n))))
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
  (declare (xargs :guard (and (real/rationalp x)
                              (common-mode-p mode)
                              (formatp f))
                  :verify-guards nil))
  (rnd x mode (+ (prec f) (expo x) (- (expo (spn f))))))

;; from sqrt.lisp:

(defund rtz-sqrt (x n)
  (declare (xargs :guard (and (real/rationalp x)
                              (natp n))
                  :verify-guards nil))
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
  (declare (xargs :guard (and (real/rationalp x)
                              (posp n))
                  :verify-guards nil))
  (let ((trunc (rtz-sqrt x (1- n))))
    (if (< (* trunc trunc) x)
        (+ trunc (expt 2 (- n)))
      trunc)))

(defund qsqrt (x n)
  (declare (xargs :guard (and (real/rationalp x)
                              (posp n))
                  :verify-guards nil))
  (let ((e (1+ (fl (/ (expo x) 2)))))
    (* (expt 2 e)
       (rto-sqrt (/ x (expt 2 (* 2 e))) n))))
