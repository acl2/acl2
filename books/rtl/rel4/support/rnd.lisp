;;;***************************************************************
;;;An ACL2 Library of Floating Point Arithmetic

;;;David M. Russinoff
;;;Advanced Micro Devices, Inc.
;;;February, 1998
;;;***************************************************************

;put all the new defuns in this book together at the t

(in-package "ACL2")

(local (include-book "float"))
(local (include-book "trunc"))
(local (include-book "away"))
(local (include-book "near"))
(local (include-book "near+"))
(local (include-book "sticky"))
(local (include-book "bitn")) ; for roundup
(local (include-book "land")) ; for roundup
(local (include-book "lior")) ; for roundup

;; Necessary functions:

(local ; ACL2 primitive
 (defun natp (x)
   (declare (xargs :guard t))
   (and (integerp x)
        (<= 0 x))))

(defund fl (x)
  (declare (xargs :guard (real/rationalp x)))
  (floor x 1))

(defund cg (x)
  (declare (xargs :guard (real/rationalp x)))
  (- (fl (- x))))

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

(defun fp+ (x n)
  (+ x (expt 2 (- (1+ (expo x)) n))))

(defund trunc (x n)
  (declare (xargs :guard (integerp n)))
  (* (sgn x) (fl (* (expt 2 (1- n)) (sig x))) (expt 2 (- (1+ (expo x)) n))))

(defund away (x n)
  (* (sgn x) (cg (* (expt 2 (1- n)) (sig x))) (expt 2 (- (1+ (expo x)) n))))


(defund re (x)
  (- x (fl x)))

(defund near (x n)
  (let ((z (fl (* (expt 2 (1- n)) (sig x))))
	(f (re (* (expt 2 (1- n)) (sig x)))))
    (if (< f 1/2)
	(trunc x n)
      (if (> f 1/2)
	  (away x n)
	(if (evenp z)
	    (trunc x n)
	  (away x n))))))

(defund near+ (x n)
  (if (< (re (* (expt 2 (1- n)) (sig x)))
	 1/2)
      (trunc x n)
    (away x n)))

(defund sticky (x n)
  (cond ((exactp x (1- n)) x)
	(t (+ (trunc x (1- n))
              (* (sgn x) (expt 2 (1+ (- (expo x) n))))))))

(defund bits (x i j)
  (declare (xargs :guard (and (natp x)
                              (natp i)
                              (natp j))
                  :verify-guards nil))
  (mbe :logic (if (or (not (integerp i))
                      (not (integerp j)))
                  0
                (fl (/ (mod x (expt 2 (1+ i))) (expt 2 j))))
       :exec  (if (< i j)
                  0
                (logand (ash x (- j)) (1- (ash 1 (1+ (- i j))))))))

(defund bitn (x n)
  (declare (xargs :guard (and (natp x)
                              (natp n))
                  :verify-guards nil))
  (mbe :logic (bits x n n)
       :exec  (if (evenp (ash x (- n))) 0 1)))

;;
;; New stuff:
;;

;Typically, we may plan to have inf and minf enabled, but we have a few lemmas about them anyway..

(defund inf (x n)
  (if (>= x 0)
      (away x n)
    (trunc x n)))

(defund minf (x n)
  (if (>= x 0)
      (trunc x n)
    (away x n)))

(defund IEEE-MODE-P (mode)
  (member mode '(trunc inf minf near)))

(defund rounding-mode-p (mode)
  (or (IEEE-mode-p mode) (equal mode 'away) (equal mode 'near+)))

(defund rnd (x mode n)
  (case mode
    (away (away x n))
    (near+ (near+ x n))
    (trunc (trunc x n))
    (inf (inf x n))
    (minf (minf x n))
    (near (near x n))
    (otherwise 0)))

(defund flip (m)
  (case m
    (inf 'minf)
    (minf 'inf)
    (t m)))

;rounding constant..
(defun rnd-const (e mode n)
  (case mode
    ((near near+) (expt 2 (- e n)))
    ((inf away) (1- (expt 2 (1+ (- e n)))))
    (otherwise 0)))

(defthmd inf-minus
  (equal (inf (* -1 x) n)
         (* -1 (minf x n)))
  :hints (("Goal" :in-theory (enable inf minf))))

(defthmd minf-minus
  (equal (minf (* -1 x) n)
         (* -1 (inf x n)))
  :hints (("Goal" :in-theory (enable inf minf))))

(defthm inf-shift
  (implies (and (rationalp x)
                (integerp n)
                (integerp k))
           (= (inf (* x (expt 2 k)) n)
              (* (inf x n) (expt 2 k))))
  :hints (("Goal" :in-theory (enable inf)
           )))

(defthm minf-shift
  (implies (and (rationalp x)
                (integerp n)
                (integerp k))
           (= (minf (* x (expt 2 k)) n)
              (* (minf x n) (expt 2 k))))
  :hints (("Goal"  :in-theory (enable minf))))

(defthm ieee-mode-p-implies-rounding-mode-p
  (implies (IEEE-mode-p mode)
           (rounding-mode-p mode))
  :hints (("Goal" :in-theory (enable rounding-mode-p)))
  :rule-classes (:rewrite; :forward-chaining
                 ))

(defthm rationalp-rnd
  (rationalp (rnd x mode n))
  :hints (("Goal" :in-theory (enable rnd)))
  :rule-classes (:type-prescription))

(defthmd rnd-minus
  (equal (rnd (* -1 x) mode n)
         (* -1 (rnd x (flip mode) n)))
  :hints (("Goal" :in-theory (enable rnd flip  minf-minus inf-minus near+-minus))))

(local (defthm rnd-const-thm-1
         (implies (and (integerp n)
                       (> n 1)
                       (integerp x)
                       (> x 0)
                       (>= (expo x) n))
                  (= (near x n)
                     (if (and (exactp x (1+ n))
                              (not (exactp x n)))
                         (trunc (+ x (rnd-const (expo x) 'near n)) (1- n))
                       (trunc (+ x (rnd-const (expo x) 'near n)) n))))
         :rule-classes ()
         :hints (("Goal"
                  :use ((:instance near-trunc))))))

(local (defthm rnd-const-thm-2
    (implies (and (integerp n)
		  (> n 1)
		  (integerp x)
		  (> x 0)
		  (>= (expo x) n))
	     (= (away x n)
		(trunc (+ x (rnd-const (expo x) 'inf n)) n)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable exactp2)
		  :use ((:instance away-imp (m (1+ (expo x)))))))))

(local (defthm rnd-const-thm-3
    (implies (and (integerp n)
		  (> n 1)
		  (integerp x)
		  (> x 0)
		  (>= (expo x) n))
	     (= (near+ x n)
		(trunc (+ x (rnd-const (expo x) 'near+ n)) n)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable exactp2)
		  :use ((:instance near+trunc))))))

(defthm RND-CONST-THM
    (implies (and (rounding-mode-p mode)
		  (integerp n)
		  (> n 1)
		  (integerp x)
		  (> x 0)
		  (>= (expo x) n))
	     (= (rnd x mode n)
		(if (and (eql mode 'near)
			 (exactp x (1+ n))
			 (not (exactp x n)))
		    (trunc (+ x (rnd-const (expo x) mode n)) (1- n))
		  (trunc (+ x (rnd-const (expo x) mode n)) n))))
  :rule-classes ()
  :hints (("Goal"  :in-theory (enable inf minf rnd rounding-mode-p ieee-mode-p)
           :use (rnd-const-thm-1 rnd-const-thm-2 rnd-const-thm-3))))

(defun roundup (x mode n)
; Returns T when we should add an ulp after truncating x to n digits.
  (case mode
    (near+ (= (bitn x (- (expo x) n)) 1))
    (near (and (= (bitn x (- (expo x) n)) 1)
               (or (not (exactp x (1+ n)))
                   (= (bitn x (- (1+ (expo x)) n)) 1))))
    ((inf away) (not (exactp x n)))
    (otherwise nil)))

(local
 (defthm exactp-preserved-up ; could perhaps manage with exactp-<= instead
   (implies (and (integerp n)
                 (< 0 n)
                 (exactp x n))
            (exactp x (1+ n)))
   :hints (("Goal" :in-theory (enable exactp)
            :expand ((expt 2 n))))))

(local (include-book "merge"))

(local
 (defthm roundup-thm-1
   (implies (and (rounding-mode-p mode)
                 (not (eq mode 'near))
                 (not (eq mode 'near+))
                 (integerp n)
                 (> n 1)
                 (integerp x)
                 (> x 0)
                 (>= (expo x) n))
            (= (rnd x mode n)
               (if (roundup x mode n)
                   (fp+ (trunc x n) n)
                 (trunc x n))))
   :hints (("Goal"  :in-theory (enable inf minf rnd rounding-mode-p
                                       ieee-mode-p)
            :use (trunc-away trunc-exactp-a away-exactp-a)))))

(local (include-book "bits-trunc"))

(local
 (defthm roundup-thm-2-1-1-1
   (implies (and (integerp n)
                 (< 1 n)
                 (integerp x)
                 (< 0 x)
                 (<= n (expo x))
                 (equal (bitn x (+ 1 (expo x) (* -1 n)))
                        0))
            (equal (trunc x n)
                   (trunc x (1- n))))
   :hints (("Goal" :use ((:instance bits-trunc-2 (k n)
                                    (n (1+ (expo x))))
                         (:instance bits-trunc-2 (k (1- n))
                                    (n (1+ (expo x))))
                         (:instance bits-plus-bitn (n (expo x))
                                    (m (+ 1 (expo x) (* -1 n)))))
            :expand ((expt 2 (+ 2 (expo x) (* -1 n))))))
   :rule-classes nil))

(local
 (defthm roundup-thm-2-1-1
   (implies (and (integerp n)
                 (< 1 n)
                 (integerp x)
                 (< 0 x)
                 (<= n (expo x))
                 (equal (bitn x (+ 1 (expo x) (* -1 n)))
                        0))
            (exactp (trunc x n) (1- n)))
   :hints (("Goal" :use roundup-thm-2-1-1-1))))

(local
 (defthm roundup-thm-2-1-2
   (implies (and (not (exactp x n))
                 (integerp n)
                 (< 1 n)
                 (integerp x)
                 (< 0 x)
                 (<= n (expo x))
                 (exactp x (+ 1 n)))
            (equal (+ x (expt 2 (+ (expo x) (* -1 n))))
                   (+ (trunc x n)
                      (expt 2 (1+ (+ (expo x) (* -1 n)))))))
   :hints (("Goal" :use trunc-away-a
            :expand ((expt 2 (+ 1 (expo x) (* -1 n))))))
   :rule-classes nil))

(local
 (defthm roundup-thm-2-1
   (implies (and (not (exactp x n))
                 (integerp n)
                 (< 1 n)
                 (integerp x)
                 (< 0 x)
                 (<= n (expo x))
                 (exactp x (+ 1 n))
                 (not (equal (bitn x (+ 1 (expo x) (* -1 n)))
                             1)))
            (equal (trunc (+ x (expt 2 (+ (expo x) (* -1 n))))
                          (1- n))
                   (trunc x n)))
   :hints (("Goal" :in-theory (enable plus-trunc-corollary
                                      expt-strong-monotone)
            :use roundup-thm-2-1-2))))

(local
 (defthm roundup-thm-2-2
   (implies (and (not (exactp x n))
                 (exactp x (+ 1 n))
                 (integerp n)
                 (< 1 n)
                 (integerp x)
                 (< 0 x)
                 (<= n (expo x)))
            (equal (bitn x (+ (expo x) (* -1 n)))
                   1))
   :hints (("Goal" :use ((:instance exact-k+1
                                    (n (1+ (expo x)))
                                    (k (+ (expo x) (* -1 n)))))))))

(local
 (encapsulate
  ()

  (local
   (defthm roundup-thm-2-3-1-1-1
     (implies (and (not (exactp x n))
                   (exactp x (+ 1 n))
                   (integerp n)
                   (< 1 n)
                   (integerp x)
                   (< 0 x)
                   (<= n (expo x))
                   (equal (bitn x (+ 1 (expo x) (* -1 n)))
                          1))
              (equal (bits x (expo x)
                           (+ 1 (expo x) (* -1 n)))
                     (+ 1
                        (* 2
                           (bits x (expo x)
                                 (+ 2 (expo x) (* -1 n)))))))
     :hints (("Goal" :use ((:instance bits-plus-bitn (n (expo x))
                                      (m (+ 1 (expo x) (* -1 n)))))))))

  (defthm roundup-thm-2-3-1-1
    (implies (and (not (exactp x n))
                  (exactp x (+ 1 n))
                  (integerp n)
                  (< 1 n)
                  (integerp x)
                  (< 0 x)
                  (<= n (expo x))
                  (equal (bitn x (+ 1 (expo x) (* -1 n)))
                         1))
             (equal x
                    (+ (trunc x (1- n))
                       (expt 2 (+ (expo x) (* -1 n)))
                       (expt 2 (+ 1 (expo x) (* -1 n))))))
    :hints (("Goal"
             :use ((:instance bits-trunc-2 (n (1+ (expo x)))
                              (k (1+ n)))
                   (:instance bits-plus-bitn (n (expo x))
                              (m (+ (expo x) (* -1 n))))
                   (:instance bits-plus-bitn (n (expo x))
                              (m (+ 1 (expo x) (* -1 n))))
                   (:instance bits-trunc-2 (n (1+ (expo x)))
                              (k (1- n))))
             :expand
             ((expt 2 (+ 2 (expo x) (* -1 n)))))
            ;; BOZO!! We can't put the following as part of Goal's :expand hint.
            ("Subgoal 4" :expand ((expt 2 (+ 1 (expo x) (* -1 n)))))
            ("Subgoal 1" :expand ((expt 2 (+ 1 (expo x) (* -1 n))))))
    :rule-classes nil)))

(local
 (defthm roundup-thm-2-3-1-2
   (implies (and (not (exactp x n))
                 (exactp x (+ 1 n))
                 (integerp n)
                 (< 1 n)
                 (integerp x)
                 (< 0 x)
                 (<= n (expo x))
                 (equal (bitn x (+ 1 (expo x) (* -1 n)))
                        1))
            (equal (+ x (expt 2 (+ (expo x) (* -1 n))))
                   (+ (trunc x (1- n))
                      (expt 2 (+ 2 (expo x) (* -1 n))))))
   :hints (("Goal" :use roundup-thm-2-3-1-1
            :expand ((expt 2 (+ 2 (expo x) (* -1 n)))))
           ("Subgoal 1" ; !! BOZO: avoid infinite by using separate subgoal hint
            :expand ((expt 2 (+ 1 (expo x) (* -1 n))))))
   :rule-classes nil))

(local
 (defthm roundup-thm-2-3-1
   (implies (and (not (exactp x n))
                 (exactp x (+ 1 n))
                 (integerp n)
                 (< 1 n)
                 (integerp x)
                 (< 0 x)
                 (<= n (expo x))
                 (equal (bitn x (+ 1 (expo x) (* -1 n)))
                        1))
            (exactp (+ x (expt 2 (+ (expo x) (* -1 n))))
                    (1- n)))
   :hints (("Goal" :use (roundup-thm-2-3-1-1
                         roundup-thm-2-3-1-2
                         (:instance fp+2
                                    (x (trunc x (1- n)))
                                    (n (1- n))))))
   :rule-classes nil))

(local
 (defthm roundup-thm-2-3-2
   (implies (and (not (exactp x n))
                 (exactp x (+ 1 n))
                 (integerp n)
                 (< 1 n)
                 (integerp x)
                 (< 0 x)
                 (<= n (expo x))
                 (equal (bitn x (+ 1 (expo x) (* -1 n)))
                        1))
            (equal (+ (trunc x n)
                      (expt 2 (+ 1 (expo x) (* -1 n))))
                   (+ x (expt 2 (+ (expo x) (* -1 n))))))
   :hints (("Goal" :use trunc-away-a
            :expand ((expt 2 (+ 1 (expo x) (* -1 n))))))
   :rule-classes nil))

(local
 (defthm roundup-thm-2-3
   (implies (and (not (exactp x n))
                 (exactp x (+ 1 n))
                 (integerp n)
                 (< 1 n)
                 (integerp x)
                 (< 0 x)
                 (<= n (expo x))
                 (equal (bitn x (+ 1 (expo x) (* -1 n)))
                        1))
            (equal (trunc (+ x (expt 2 (+ (expo x) (* -1 n))))
                          (1- n))
                   (+ (trunc x n)
                      (expt 2 (+ 1 (expo x) (* -1 n))))))
   :hints (("Goal" :use (roundup-thm-2-3-1
                         roundup-thm-2-3-2
                         (:instance trunc-exactp-a
                                    (x (+ x (expt 2 (+ (expo x) (* -1 n)))))
                                    (n (1- n))))))))

; We need a special case of the following lemma for roundup-thm-2-4, so let's
; prove a nice version to include in the library.

(defthmd trunc-split
  (implies (and (= n (1+ (expo x)))
                (>= x 0)
                (integerp m)
                (> m k)
                (integerp k)
                (> k 0))
           (equal (trunc x m)
                  (+ (trunc x k)
                     (* (expt 2 (- n m))
                        (bits x (1- (- n k)) (- n m))))))
  :hints (("Goal" :use ((:instance expt-split (r 2)
                                   (i (+ m (* -1 k)))
                                   (j (+ 1 (expo x) (* -1 m))))
                        bits-trunc-2
                        (:instance bits-trunc-2 (k m)
                                   (n (1+ (expo x))))
                        (:instance bits-plus-bits (n (expo x))
                                   (m (- (1+ (expo x)) m))
                                   (p (- (1+ (expo x)) k)))))))

(defund trunc-rem (x n)
  (- x (trunc x n)))

(defthm trunc-rem-small
  (implies (and (integerp n)
                (<= 0 n)
                (rationalp x)
                (<= 0 x))
           (< (trunc-rem x n)
              (expt 2 (+ 1 (expo x) (* -1 n)))))
  :hints (("Goal" :use (trunc-diff-pos trunc-rem)))
  :rule-classes :linear)

(defthm trunc-rem-nonnegative
  (implies (and (integerp n)
                (<= 0 n)
                (rationalp x)
                (<= 0 x))
           (and (rationalp (trunc-rem x n))
                (<= 0 (trunc-rem x n))))
  :hints (("Goal" :use (trunc-lower-pos trunc-rem)))
  :rule-classes :type-prescription)

; First, break x into the high n bits, the next bit, and the rest.

(local
 (defthm roundup-thm-2-4-1
   (implies (and (integerp n)
                 (< 1 n)
                 (integerp x)
                 (< 0 x)
                 (<= n (expo x))
                 (equal (bitn x (+ (expo x) (* -1 n)))
                        1))
            (equal x
                   (+ (trunc x n)
                      (expt 2 (- (expo x) n))
                      (trunc-rem x (1+ n)))))
   :hints (("Goal" :use ((:instance trunc-split
                                    (n (1+ (expo x)))
                                    (m (1+ n))
                                    (k n)))
            :in-theory (enable trunc-rem bitn)))
   :rule-classes nil))

; Next, trivially introduce fp+.  A key fact is that (exactp (fp+ (trunc x n)
; n) n), by fp+2 and trunc-exact-b.  We need that fact in order to apply
; plus-trunc-corollary.

(local
 (defthm roundup-thm-2-4-2
   (implies (and (integerp n)
                 (< 1 n)
                 (integerp x)
                 (< 0 x)
                 (<= n (expo x))
                 (equal (bitn x (+ (expo x) (* -1 n)))
                        1))
            (equal (+ x (expt 2 (+ (expo x) (* -1 n))))
                   (+ (fp+ (trunc x n) n)
                      (trunc-rem x (1+ n)))))
   :hints (("Goal" :use (roundup-thm-2-4-1)
            :expand ((expt 2 (+ 1 (expo x) (* -1 n))))))
   :rule-classes nil))

(local
 (defthm expt-2-+-constant
   (implies (and (syntaxp (quotep k))
                 (integerp n)
                 (<= 0 n)
                 (integerp k)
                 (<= 0 k))
            (equal (expt 2 (+ k n))
                   (* 2 (expt 2 (+ (1- k) n)))))
   :hints (("Goal" :expand ((expt 2 (+ k n)))))))

; Note: fp+-positive was first discovered at about this point.

(local
 (defthm roundup-thm-2-4-3
   (implies (and (integerp n)
                 (< 1 n)
                 (integerp x)
                 (< 0 x)
                 (<= n (expo x))
                 (equal (bitn x (+ (expo x) (* -1 n)))
                        1))
            (equal (trunc (+ (fp+ (trunc x n) n)
                             (trunc-rem x (1+ n)))
                          n)
                   (fp+ (trunc x n) n)))
   :hints (("Goal" :use ((:instance fp+2 (x (trunc x n)))
                         (:instance plus-trunc-corollary
                                    (x (fp+ (trunc x n) n))
                                    (y (trunc-rem x (1+ n))))
                         (:instance trunc-rem-small (n (1+ n)))
                         (:instance fp+2-2 (x (trunc x n))))
            :in-theory (disable fp+ plus-trunc-corollary)))
   :rule-classes nil))

(local
 (defthm roundup-thm-2-4
   (implies (and (integerp n)
                 (< 1 n)
                 (integerp x)
                 (< 0 x)
                 (<= n (expo x))
                 (equal (bitn x (+ (expo x) (* -1 n)))
                        1))
            (equal (trunc (+ x (expt 2 (+ (expo x) (* -1 n))))
                          n)
                   (+ (trunc x n)
                      (expt 2 (+ 1 (expo x) (* -1 n))))))
   :hints (("Goal" :use (roundup-thm-2-4-2 roundup-thm-2-4-3)))))

(local
 (defthm roundup-thm-2-5-1
   (implies (and (integerp n)
                 (< 1 n)
                 (integerp x)
                 (< 0 x)
                 (<= n (expo x))
                 (equal (bitn x (+ (expo x) (* -1 n)))
                        0))
            (equal x
                   (+ (trunc x n)
                      (trunc-rem x (1+ n)))))
   :hints (("Goal" :use ((:instance trunc-split
                                    (n (1+ (expo x)))
                                    (m (1+ n))
                                    (k n)))
            :in-theory (enable trunc-rem bitn)))
   :rule-classes nil))

(local
 (defthm roundup-thm-2-5-2
   (implies (and (integerp n)
                 (< 1 n)
                 (integerp x)
                 (< 0 x)
                 (<= n (expo x))
                 (equal (bitn x (+ (expo x) (* -1 n)))
                        0))
            (equal (+ x (expt 2 (+ (expo x) (* -1 n))))
                   (+ (trunc x n)
                      (expt 2 (+ (expo x) (* -1 n)))
                      (trunc-rem x (1+ n)))))
   :hints (("Goal" :use (roundup-thm-2-5-1)
            :expand ((expt 2 (+ 1 (expo x) (* -1 n))))))
   :rule-classes nil))

(local
 (defthm roundup-thm-2-5-3
   (implies (and (integerp n)
                 (< 1 n)
                 (integerp x)
                 (< 0 x)
                 (<= n (expo x)))
            (< (+ (expt 2 (+ (expo x) (* -1 n)))
                  (trunc-rem x (1+ n)))
               (expt 2 (+ 1 (expo x) (* -1 n)))))
   :hints (("Goal" :expand ((expt 2 (+ 1 (expo x) (* -1 n))))
            :use ((:instance trunc-rem-small (n (1+ n))))))
   :rule-classes nil))

(local
 (defthm roundup-thm-2-5
   (implies (and (integerp n)
                 (< 1 n)
                 (integerp x)
                 (< 0 x)
                 (<= n (expo x))
                 (not (equal (bitn x (+ (expo x) (* -1 n)))
                             1)))
            (equal (trunc (+ x (expt 2 (+ (expo x) (* -1 n))))
                          n)
                   (trunc x n)))
   :hints (("Goal" :use ((:instance plus-trunc-corollary
                                    (x (trunc x n))
                                    (y (+ (trunc-rem x (+ 1 n))
                                          (expt 2 (+ (expo x) (* -1 n))))))
                         roundup-thm-2-5-2
                         roundup-thm-2-5-3)
            :in-theory (disable fp+ plus-trunc-corollary)))))

(local
 (defthm roundup-thm-2-6
   (implies (and (exactp x n)
                 (integerp n)
                 (< 1 n)
                 (integerp x)
                 (< 0 x)
                 (<= n (expo x)))
            (equal (bitn x (+ (expo x) (* -1 n)))
                   0))
   :hints (("Goal" :use ((:instance exact-bits-1
                                    (n (1+ (expo x)))
                                    (k (- (1+ (expo x)) n)))
                         (:instance exact-bits-3
                                    (k (- (1+ (expo x)) n))))))))

(local
 (defthm roundup-thm-2
   (implies (and (eq mode 'near)
                 (integerp n)
                 (> n 1)
                 (integerp x)
                 (> x 0)
                 (>= (expo x) n))
            (= (rnd x mode n)
               (if (roundup x mode n)
                   (fp+ (trunc x n) n)
                 (trunc x n))))
   :hints (("Goal"  :in-theory (enable rnd)
            :use (near-exactp-a rnd-const-thm-1)))
   :rule-classes ()))

(local
 (defthm roundup-thm-3
   (implies (and (eq mode 'near+)
                 (integerp n)
                 (> n 1)
                 (integerp x)
                 (> x 0)
                 (>= (expo x) n))
            (= (rnd x mode n)
               (if (roundup x mode n)
                   (fp+ (trunc x n) n)
                 (trunc x n))))
   :hints (("Goal"  :in-theory (enable rnd)
            :use near+trunc))
   :rule-classes ()))

(defthm roundup-thm
    (implies (and (rounding-mode-p mode)
		  (integerp n)
		  (> n 1)
		  (integerp x)
		  (> x 0)
		  (>= (expo x) n))
	     (= (rnd x mode n)
                (if (roundup x mode n)
                    (fp+ (trunc x n) n)
                  (trunc x n))))
  :hints (("Goal"  :in-theory (enable rounding-mode-p)
           :use (roundup-thm-1
                 roundup-thm-2
                 roundup-thm-3)))
  :rule-classes ())

;rephrase?
(defthmd rnd-sticky
  (implies (and (> n (1+ k))
                (rounding-mode-p mode)
                (rationalp x) (> x 0)
                (integerp k) (> k 0)
                (integerp n) )
           (equal (rnd (sticky x n) mode k)
                  (rnd x mode k)))
  :hints (("Goal" :in-theory (enable rnd minf inf)
           :use (sticky-pos
                 (:instance trunc-sticky (m k))
                 (:instance away-sticky (m k))
                 (:instance near-sticky (m k))
                 (:instance near+-sticky (m k))))))

(defthm rnd-shift
  (implies (and (rationalp x)
                (integerp n)
                (rounding-mode-p mode)
                (integerp k))
           (= (rnd (* x (expt 2 k)) mode n)
              (* (rnd x mode n) (expt 2 k))))
  :rule-classes ()
  :hints (("goal" :in-theory (enable rnd IEEE-MODE-P
                                     rounding-mode-p)
           :use (trunc-shift
                 away-shift
                 near-shift
                 near+-shift
                 inf-shift
                 minf-shift
                 ))))
;elim <-- why?
(defthm expo-rnd
    (implies (and (rationalp x)
		  (not (= x 0))
		  (integerp n)
		  (> n 0)
		  (rounding-mode-p mode)
		  (not (= (abs (rnd x mode n))
			  (expt 2 (1+ (expo x))))))
	     (= (expo (rnd x mode n))
		(expo x)))
  :rule-classes ()
  :hints (("goal" :in-theory (enable rounding-mode-p
                                     ieee-mode-p near near+ rnd minf inf)
		  :use (expo-trunc expo-away))))

;better rule-classes?
(defthm rnd-pos
  (implies (and (< 0 x)
                (rationalp x)
                (integerp n)
                (> n 0)
                (rounding-mode-p mode))
           (> (rnd x mode n) 0))
  :rule-classes (:type-prescription)
  :hints (("goal" :in-theory (enable rounding-mode-p ieee-mode-p near rnd inf minf)
           :use ())))

(defthm rnd-0
  (equal (rnd 0 mode n)
         0)
  :hints (("Goal" :in-theory (enable rnd rounding-mode-p ieee-mode-p inf minf)
           :use (trunc-0 away-0))))

;better rule-classes?
(defthm rnd-neg
  (implies (and (< x 0)
                (rationalp x)
                (integerp n)
                (> n 0)
                (rounding-mode-p mode))
           (< (rnd x mode n) 0))
  :rule-classes (:type-prescription)
  :hints (("Goal" :in-theory (enable rnd rounding-mode-p ieee-mode-p inf minf)
           :use (
                 near-neg))))

;would like to not open minf, inf here?
(defthm rnd-non-pos
  (implies (<= x 0)
           (<= (rnd x mode n) 0))
  :hints (("goal" :in-theory (enable rnd near+ inf minf)))
  :rule-classes (:rewrite :type-prescription :linear))

;would like to not open minf, inf here?
;add to lib?
(defthm rnd-non-neg
  (implies (<= 0 x)
           (<= 0 (rnd x mode n)))
  :hints (("goal" :in-theory (enable rnd near+ inf minf)))
  :rule-classes (:rewrite :type-prescription :linear))

(defthm sgn-rnd
  (implies (and; (rationalp x)
                (rounding-mode-p mode)
                (integerp n)
                (> n 0)
                )
           (equal (sgn (rnd x mode n))
                  (sgn x)))
  :hints (("Goal" :in-theory (enable ieee-mode-p rounding-mode-p rnd near+ inf minf)
           :use (sgn-trunc
                 sgn-away
                 sgn-near-2))))

;enable?
(defthmd rnd-exactp-a
  (implies (and (rationalp x)
                (rounding-mode-p mode)
                (integerp n)
                (> n 0))
           (equal (equal x (rnd x mode n))
                  (exactp x n)))
  :hints (("Goal" :in-theory (enable ieee-mode-p rounding-mode-p rnd near+ minf inf)
           :use (near-exactp-a
                 trunc-exactp-a
                 away-exactp-a))))

(defthm rnd-exactp-b
    (implies (< 0 n)
	     (exactp (rnd x mode n) n))
  :hints (("Goal" :in-theory (enable rnd near+ minf inf))))

(defthm rnd-exactp-c
    (implies (and (rationalp x)
		  (> x 0)
		  (rounding-mode-p mode)
		  (integerp n)
		  (> n 0)
		  (rationalp a)
		  (exactp a n)
		  (>= a x))
	     (>= a (rnd x mode n)))
  :hints (("Goal" :in-theory (enable ieee-mode-p rnd minf inf)
		  :use (near-exactp-c
			away-exactp-c
			trunc-upper-pos))))

(defthm rnd-exactp-d
    (implies (and (rationalp x)
		  (> x 0)
		  (rounding-mode-p mode)
		  (integerp n)
		  (> n 0)
		  (rationalp a)
		  (exactp a n)
		  (<= a x))
	     (<= a (rnd x mode n)))
  :hints (("Goal" :in-theory (enable ieee-mode-p rounding-mode-p rnd minf inf)
		  :use (near-exactp-c
			trunc-exactp-c
			away-lower-pos))))


(defthm rnd<=away
    (implies (and (rationalp x)
		  (> x 0)
		  (rounding-mode-p mode)
		  (integerp n)
		  (> n 0))
	     (<= (rnd x mode n) (away x n)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable ieee-mode-p rnd minf inf)
		  :use (trunc-upper-pos
			away-lower-pos
			near-choice))))

(defthm rnd>=trunc
    (implies (and (rationalp x)
		  (> x 0)
		  (rounding-mode-p mode)
		  (integerp n)
		  (> n 0))
	     (>= (rnd x mode n) (trunc x n)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable ieee-mode-p rounding-mode-p rnd minf inf)
		  :use (trunc-upper-pos
			away-lower-pos
			near-choice))))

(defthm rnd-monotone
    (implies (and (<= x y)
                  (rationalp x)
		  (rationalp y)
		  (< 0 x)
		  (rounding-mode-p mode)
		  (integerp n)
		  (> n 0))
	     (<= (rnd x mode n) (rnd y mode n)))
  :hints (("Goal" :in-theory (enable ieee-mode-p rnd minf inf)
		  :use (trunc-monotone
			away-monotone
			near-monotone))))

(defthm exactp-rnd
  (implies (and (rationalp x)
                (rounding-mode-p mode)
                (integerp n)
                (> n 0))
           (exactp (rnd x mode n) n))
  :hints (("Goal" :in-theory (enable ieee-mode-p rounding-mode-p rnd inf minf))))

(defthm rnd-choice
  (implies (rounding-mode-p mode)
           (or (equal (rnd x mode n) (rnd x 'away n))
               (equal (rnd x mode n) (rnd x 'trunc n))))
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable rnd near+ inf minf near rounding-mode-p ieee-mode-p)
                              '(re evenp))))
  :rule-classes nil)

(defthm ieee-mode-p-flip
    (implies (ieee-mode-p m)
	     (ieee-mode-p (flip m)))
    :hints (("Goal" :in-theory (enable ieee-mode-p flip))))

(defthm rounding-mode-p-flip
    (implies (rounding-mode-p m)
	     (rounding-mode-p (flip m)))
    :hints (("Goal" :in-theory (enable ieee-mode-p flip))))


(defthm expo-rnd-bnd
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0)
		  (rounding-mode-p mode))
	     (>= (expo (rnd x mode n))
		 (expo x)))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable expo-minus)
           :use (expo-rnd
			(:instance expo-minus (x (rnd x mode n)))))))

(defthm plus-inf
    (implies (and (rationalp x)
		  (>= x 0)
		  (rationalp y)
		  (>= y 0)
		  (integerp k)
		  (exactp x (+ k (- (expo x) (expo y)))))
	     (= (+ x (inf y k))
		(inf (+ x y) (+ k (- (expo (+ x y)) (expo y))))))
  :rule-classes ()
  :hints (("goal" :in-theory (enable inf)
           :use plus-away)))

(defthm plus-minf
    (implies (and (rationalp x)
		  (>= x 0)
		  (rationalp y)
		  (>= y 0)
		  (integerp k)
		  (exactp x (+ k (- (expo x) (expo y)))))
	     (= (+ x (minf y k))
		(minf (+ x y) (+ k (- (expo (+ x y)) (expo y))))))
  :rule-classes ()
  :hints (("goal" :in-theory (enable minf)
           :use plus-trunc)))

;make alt form too?
; add to lib?
(defthm plus-rnd
  (implies (and (rationalp x)
                (>= x 0)
                (rationalp y)
                (>= y 0)
                (integerp k)
                (exactp x (+ -1 k (- (expo x) (expo y))))
                (rounding-mode-p mode))
           (= (+ x (rnd y mode k))
              (rnd (+ x y)
                   mode
                   (+ k (- (expo (+ x y)) (expo y))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable rnd ieee-mode-p ROUNDING-MODE-P)
           :use (plus-near
                 plus-near+
                 plus-away
                 plus-trunc
                 plus-minf
                 plus-inf
                 (:instance exactp-<= (m (+ -1 k (- (expo x) (expo y))))
                            (n (+  k (- (expo x) (expo y)))))))))

(defthm rnd-rarely-zero
  (implies (and (rationalp x)
                (integerp k)
                (case-split (< 0 k))
                (case-split (rounding-mode-p mode)))
           (equal (equal (rnd x mode k) 0)
                  (equal x 0)
           ))
  :hints (("Goal" :in-theory (enable rnd near+ minf inf near ROUNDING-MODE-P ieee-mode-p))))

;add to lib?
(defthm flip-flip
  (equal (flip (flip mode))
         mode)
  :hints (("Goal" :in-theory (enable flip))))

;add to lib?
(defthm inf-lower-bound
  (implies (and (rationalp x)
                (integerp n))
           (>= (inf x n) x))
  :hints (("Goal" :in-theory (enable inf)
           :use trunc-upper-bound))
  :rule-classes (:rewrite :linear))

;add to lib?
(defthm minf-upper-bound
  (implies (and (rationalp x)
                (integerp n))
           (<= (minf x n) x))
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable minf)
                              '(abs-away))
           :use away-lower-bound))
  :rule-classes (:rewrite :linear))


;add to lib?
(defthm rnd-diff
  (implies (and (rationalp x)
                (integerp n)
                (> n 0)
                (rounding-mode-p mode))
           (< (abs (- x (rnd x mode n))) (expt 2 (- (1+ (expo x)) n))))
  :hints (("Goal" :in-theory (enable rnd near near+ inf minf ieee-mode-p rounding-mode-p)
           :use (trunc-diff away-diff))))
