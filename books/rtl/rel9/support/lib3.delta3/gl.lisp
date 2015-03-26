(in-package "ACL2")

(include-book "centaur/gl/gl" :dir :system)

(include-book "../lib2/basic") ;; no change from rel8

(local (include-book "../lib2.delta1/bits-new"))


;;;**********************************************************************
;;;				BVECP
;;;**********************************************************************

(local (encapsulate ()

(defund bvecp (x k)
  (declare (xargs :guard (integerp k)))
  (and (integerp x)
       (<= 0 x)
       (< x (expt 2 k))))

(defthm bvecp-forward
  (implies (bvecp x k)
	   (and (integerp x)
		(<= 0 x)
		(< x (expt 2 k))))
  :rule-classes :forward-chaining)

(defthmd bvecp-monotone
    (implies (and (bvecp x n)
		  (<= n m)
		  (case-split (integerp m)))
	     (bvecp x m)))

(defthmd bvecp-shift-down
    (implies (and (bvecp x n)
		  (natp n)
		  (natp k))
	     (bvecp (fl (/ x (expt 2 k))) (- n k))))

(defthmd bvecp-shift-up
    (implies (and (bvecp x (- n k))
		  (natp k)
		  (integerp n))
	     (bvecp (* x (expt 2 k)) n)))

(defthm bvecp-product
    (implies (and (bvecp x m)
		  (bvecp y n))
	     (bvecp (* x y) (+ m n)))
  :rule-classes ())

(defthmd bvecp-1-rewrite
  (equal (bvecp x 1)
	 (or (equal x 0) (equal x 1))))

(defthm bvecp-1-0
  (implies (and (bvecp x 1)
		(not (equal x 1)))
	   (equal x 0))
  :rule-classes :forward-chaining)

(defthm bvecp-0-1
  (implies (and (bvecp x 1)
		(not (equal x 0)))
	   (equal x 1))
  :rule-classes :forward-chaining)

))

;;;**********************************************************************
;;;			    BITS
;;;**********************************************************************

(local (include-book "../../arithmetic/top"))

(local (encapsulate ()



                      (defthmd bits-mbe-lemma-subgoal-2
                        (IMPLIES (AND (INTEGERP J)
                                      (INTEGERP I)
                                      (INTEGERP X)
                                      (< I J))
                                 (EQUAL (FL (* (/ (EXPT 2 J))
                                               (MOD X (EXPT 2 (+ 1 I)))))
                                        0)))

                      (encapsulate ()

                                   (local (encapsulate ()

                                                       (encapsulate ()
                                                                    (local (include-book "../lib2.delta1/log-new"))
                                                                    (defthm bitn_alt-logand
                                                                      (implies (and (integerp x) ; (>= x 0)
                                                                                    (integerp y) ; (>= y 0)
                                                                                    (integerp n) ;
                                                                                    )
                                                                               (equal (bitn_alt (logand x y) n)
                                                                                      (logand (bitn_alt x n) (bitn_alt y n)))))


                                                                    )


                                                       (encapsulate ()
                                                                    (local (include-book "../lib2.delta1/log-new"))

                                                                    (defthmd logand-1-x_alt
                                                                      (implies (bvecp x 1)
                                                                               (equal (logand 1 x) x)))

                                                                    )




                                                       (encapsulate ()
                                                                    (local (include-book "../lib2.delta1/../support/logand"))

                                                                    (defthm logand-bnd
                                                                      (implies (<= 0 x)
                                                                               (<= (logand x y) x))
                                                                      :rule-classes :linear
                                                                      )


                                                                    (defthm logand-commutative
                                                                      (equal (logand j i)
                                                                             (logand i j)))

                                                                    ;;


                                                                    (defthm logand-non-negative
                                                                      (implies (or (<= 0 x)
                                                                                   (<= 0 y)
                                                                                   )
                                                                               (<= 0 (logand x y))))


                                                                    (DEFTHM LOGAND-NON-NEGATIVE-INTEGER-TYPE-PRESCRIPTION
                                                                      (IMPLIES (OR (<= 0 I) (<= 0 J))
                                                                               (AND (<= 0 (LOGAND I J))
                                                                                    (INTEGERP (LOGAND I J))))
                                                                      :RULE-CLASSES (:TYPE-PRESCRIPTION))

                                                                    )







                                                       (defund bvequal (v1 v2 n)
                                                         (equal (sumbits_alt v1 n)
                                                                (sumbits_alt v2 n)))


                                                       (defthm bvequal-then-equal
                                                         (implies (and (bvequal x y n)
                                                                       (bvecp x n)
                                                                       (bvecp y n)
                                                                       (natp n))
                                                                  (equal x y))
                                                         :hints (("Goal" :use ((:instance sumbits_alt-thm
                                                                                          (x x))
                                                                               (:instance sumbits_alt-thm
                                                                                          (x y)))
                                                                  :in-theory (enable bvequal)))
                                                         :rule-classes nil)



                                                       (encapsulate ()
                                                                    (local (include-book "../lib2.delta1/bits-new"))
                                                                    (defthmd bitn_alt-mod
                                                                      (implies (and (< k n)
                                                                                    (integerp n)
                                                                                    (integerp k))
                                                                               (equal (bitn_alt (mod x (expt 2 n)) k)
                                                                                      (bitn_alt x k)))))



                                                       (defthmd logand-ones-g-lemma-lemma
                                                         (implies (and (<= 0 k)
                                                                       (<= k (+ -1 n))
                                                                       (integerp n)
                                                                       (> n 0)
                                                                       (integerp k))
                                                                  (equal (bitn_alt (+ -1 (expt 2 n)) k) 1))
                                                         :hints (("Goal" :in-theory (e/d (bitn_alt bits_alt
                                                                                                   expt-2-reduce-leading-constant)
                                                                                         (bits_alt-n-n-rewrite)))))


                                                       (defthmd logand-ones-g-lemma-1
                                                         (implies (and (<= 0 k)
                                                                       (<= k (+ -1 n))
                                                                       (< 0 n)
                                                                       (integerp n)
                                                                       (integerp x)
                                                                       (integerp k))
                                                                  (equal (bitn_alt (logand x (+ -1 (expt 2 n))) k)
                                                                         (bitn_alt (mod x (expt 2 n)) k)))
                                                         :hints (("Goal" :in-theory (e/d (bitn_alt-logand
                                                                                          bitn_alt-mod
                                                                                          logand-1-x_alt
                                                                                          logand-ones-g-lemma-lemma)
                                                                                         ()))))


                                                       (defthm logand-ones-bvequal
                                                         (implies (and (<= 0 k)
                                                                       (<= k n)
                                                                       (< 0 n)
                                                                       (integerp n)
                                                                       (integerp x)
                                                                       (integerp k))
                                                                  (bvequal (logand x (+ -1 (expt 2 n)))
                                                                           (mod x (expt 2 n))
                                                                           k))
                                                         :hints (("Goal" :in-theory (e/d
                                                                                     (logand-ones-g-lemma-1
                                                                                      bvequal) ()))))



                                                       (defthm logand-ones-g-lemma-2
                                                         (implies (and (integerp x)
                                                                       (natp n))
                                                                  (bvecp (logand x (+ -1 (expt 2 n))) n))
                                                         :hints (("Goal"
                                                                  :cases ((equal (logand x (+ -1 (expt 2 n)))
                                                                                 (logand (+ -1 (expt 2 n)) x))))
                                                                 ("Subgoal 1"
                                                                  :in-theory (e/d (bvecp)
                                                                                  (logand-bnd
                                                                                   logand-commutative
                                                                                   logand-non-negative))
                                                                  :use ((:instance logand-bnd
                                                                                   (x (+ -1 (expt 2 n)))
                                                                                   (y x))
                                                                        (:instance logand-non-negative
                                                                                   (x x)
                                                                                   (y (+ -1 (expt 2 n))))))))



                                                       (defthm logand-ones-g-lemma-3
                                                         (implies (integerp x)
                                                                  (bvecp (mod x (expt 2 n)) n))
                                                         :hints (("Goal" :in-theory (enable bvecp))))
                                                       ))

                                   (defthmd logand-ones-g
                                     (implies (and (integerp i)
                                                   (case-split (integerp i))
                                                   )
                                              (equal (logand i (1- (expt 2 n)))
                                                     (mod i (expt 2 n))))
                                     :hints (("Goal" :in-theory (e/d (logand-ones-bvequal) ())
                                              :cases ((not (and (integerp n)
                                                                (> n 0)))))
                                             ("Subgoal 2"  :use ((:instance bvequal-then-equal
                                                                            (x (logand i (+ -1 (expt 2 n))))
                                                                            (y (mod i (expt 2 n)))
                                                                            (n n))))
                                             ("Subgoal 1.1" :in-theory (enable acl2::binary-logand))))


                                   )


                      (local
                       (defthmd bits-mbe-lemma-subgoal-1-lemma-1
                         (IMPLIES (AND (INTEGERP J)
                                       (INTEGERP I)
                                       (INTEGERP X)
                                       (<= J I))
                                  (EQUAL (FL (* (/ (EXPT 2 J))
                                                (MOD X (EXPT 2 (+ 1 I)))))
                                         (mod (FL (* X (EXPT 2 (* -1 J))))
                                              (EXPT 2 (+ 1 I (* -1 J))))))
                         :hints (("Goal" :in-theory (e/d (mod
                                                          expt-minus)
                                                         ())))))




                      (local
                       (defthmd bits-mbe-lemma-subgoal-1-lemma-2
                         (IMPLIES (AND (INTEGERP J)
                                       (INTEGERP I)
                                       (INTEGERP X)
                                       (<= J I))
                                  (EQUAL (LOGAND (FL (* X (EXPT 2 (* -1 J))))
                                                 (+ -1 (EXPT 2 (+ 1 I (* -1 J)))))
                                         (mod (FL (* X (EXPT 2 (* -1 J))))
                                              (EXPT 2 (+ 1 I (* -1 J))))))
                         :hints (("Goal" :in-theory (e/d (mod expt-minus
                                                              logand-ones-g)
                                                         ())))))



                      (defthmd bits-mbe-lemma-subgoal-1
                        (IMPLIES (AND (INTEGERP J)
                                      (INTEGERP I)
                                      (INTEGERP X)
                                       (<= J I))
                                 (EQUAL (FL (* (/ (EXPT 2 J))
                                               (MOD X (EXPT 2 (+ 1 I)))))
                                        (LOGAND (FL (* X (EXPT 2 (* -1 J))))
                                                (+ -1 (EXPT 2 (+ 1 I (* -1 J)))))))
                        :hints (("Goal" :in-theory (e/d (bits-mbe-lemma-subgoal-1-lemma-2
                                                         bits-mbe-lemma-subgoal-1-lemma-1
                                                         ) ()))))



                      ))

  (defund bits (x i j)
    (declare (xargs :guard (and (integerp x)
                                (integerp i)
                                (integerp j))
                    :guard-hints (("Goal" :in-theory (e/d
                                                      (bits-mbe-lemma-subgoal-1
                                                       ash
                                                       bits-mbe-lemma-subgoal-2) ())))))
    (mbe :logic (if (or (not (integerp i))
                        (not (integerp j)))
                    0
                  (fl (/ (mod x (expt 2 (1+ i))) (expt 2 j))))
         :exec  (if (< i j)
                    0
                  (logand (ash x (- j)) (1- (ash 1 (1+ (- i j))))))))

(local
 (defthm bits_alt-is-bits
   (equal (bits_alt x i j)
          (bits x i j))
   :hints (("Goal" :in-theory (e/d (bits_alt bits) ())))))

  (local (defun my-bits (x i j)
           ;; The executable version of BITS
           (IF (< I J)
               0
               (LOGAND (ASH X (- J))
                       (1- (ASH 1 (1+ (- I J))))))))

  (local
     ;; I'm skipping this, but you have presumably already proved it somewhere in
    ;; the RTL libraries, since it's the MBE version of BITS!
    (defthm your-bits-is-my-bits
      (implies (and (integerp i)
                    (integerp j)
                    (integerp x))
               (equal (bits x i j)
                      (my-bits x i j)))
      :hints (("Goal" :in-theory (enable bits ash bits-mbe-lemma-subgoal-2 bits-mbe-lemma-subgoal-1)))))

  (defthm bits-for-gl
    (equal (bits x i j)
           (if (and (integerp x)
                    (integerp i)
                    (integerp j))
               (if (< i j)
                   0
                 (logand (ash x (- j))
                         (1- (ash 1 (1+ (- i j))))))
             (let ((msg (cw "WARNING: guard violation for the function BITS during a GL proof.~%")))
               (declare (ignore msg))
               (if (or (not (integerp i))
                       (not (integerp j)))
                   0
                 (fl (/ (mod x (expt 2 (1+ i))) (expt 2 j)))))))
    :hints (("Goal" :in-theory (enable bits)
                    :use (your-bits-is-my-bits)))
    :rule-classes ())

;; Tell GL to actually use our definition
  (gl::set-preferred-def bits bits-for-gl)





 (local (encapsulate ()
                     (local
                      (defthmd evenp-sum
                        (implies (and (evenp x)
                                      (evenp y))
                                 (evenp (- x y)))
                        :hints (("Goal" :in-theory (e/d (evenp) ())))))

                     (local
                      (defthmd evenp-2-factor
                        (implies (integerp x)
                                 (evenp (* 2 x)))
                        :hints (("Goal" :in-theory (e/d (evenp) ())))))

                     (local
                      (defthmd bitn-mbe-subgoal-2-lemma
                        (IMPLIES (AND (INTEGERP N)
                                      (INTEGERP X)
                                      (evenp (FL (* X (EXPT 2 (* -1 N))))))
                                 (evenp (BITN_alt X N)))
                        :hints (("Goal" :in-theory (e/d (bitn_alt expt-minus
                                                                  evenp-2-factor)
                                                        (bits_alt-n-n-rewrite
                                                         bits_alt-is-bits))
                                 :use ((:instance bits_alt-mod-2
                                                  (x x)
                                                  (i (+ 1 n))
                                                  (j n))
                                       (:instance evenp-sum
                                                  (x (fl (* x (/ (expt 2 n)))))
                                                  (y (* 2 (fl (* x (/ (expt 2 (+ 1 n)))))))))))))


                     (defthmd bitn-mbe-subgoal-2
                       (IMPLIES (AND (INTEGERP N)
                                     (INTEGERP X)
                                     (evenp (FL (* X (EXPT 2 (* -1 N))))))
                                (EQUAL (BITN_alt X N) 0))
                       :hints (("Goal" :use ((:instance bitn_alt-0-1
                                                        (x x)
                                                        (n n))
                                             (:instance bitn-mbe-subgoal-2-lemma))
                                :in-theory (e/d (evenp) ()))))

                     ))

 (local (encapsulate ()
                     (local
                      (defthmd not-evenp-sum
                        (implies (and (not (evenp x))
                                      (evenp y))
                                 (not (evenp (- x y))))
                        :hints (("Goal" :in-theory (e/d (evenp) ())))))

                     (local
                      (defthmd evenp-2-factor
                        (implies (integerp x)
                                 (evenp (* 2 x)))
                        :hints (("Goal" :in-theory (e/d (evenp) ())))))


                     (local
                      (defthmd bitn-mbe-subgoal-1-lemma
                        (IMPLIES (AND (INTEGERP N)
                                      (INTEGERP X)
                                      (not (evenp (FL (* X (EXPT 2 (* -1 N)))))))
                                 (not (evenp (BITN_alt X N))))
                        :hints (("Goal" :in-theory (e/d (bitn_alt expt-minus
                                                                  evenp-2-factor)
                                                        (bits_alt-n-n-rewrite
                                                         bits_alt-is-bits))
                                 :use ((:instance bits_alt-mod-2
                                                  (x x)
                                                  (i (+ 1 n))
                                                  (j n))
                                       (:instance not-evenp-sum
                                                  (x (fl (* x (/ (expt 2 n)))))
                                                  (y (* 2 (fl (* x (/ (expt 2 (+ 1 n)))))))))))))




                     (defthmd bitn-mbe-subgoal-1
                       (IMPLIES (AND (INTEGERP N)
                                     (INTEGERP X)
                                     (NOT (evenp (FL (* X (EXPT 2 (* -1 N)))))))
                                (EQUAL (BITN_alt X N) 1))
                       :hints (("Goal" :use ((:instance bitn_alt-0-1
                                                        (x x)
                                                        (n n))
                                             (:instance bitn-mbe-subgoal-1-lemma))
                                :in-theory (e/d (evenp) ()))))
                     ))



 (defund bitn (x n)
   (declare (xargs :guard (and (integerp x)
                               (integerp n))
                   :guard-hints (("Goal" :in-theory (e/d (bitn-mbe-subgoal-1
                                                          bitn-mbe-subgoal-2
                                                          ash
                                                          ) (bits_alt-is-bits))
                                  :use ((:instance bits_alt-is-bits
                                                   (x x) (i n) (j n)))))))
   (mbe :logic (bits x n n)
        :exec  (if (evenp (ash x (- n))) 0 1)))


  (local (defun my-bitn (x n)
           (IF (EVENP (ASH X (- N))) 0 1)))

  (local
    (defthm your-bitn-is-my-bitn
      ;; Again you've presumably proven this somewhere in the RTL library
      (implies (and (integerp x)
                    (integerp n))
               (equal (bitn x n)
                      (my-bitn x n)))
      :hints (("Goal" :in-theory (e/d (bitn bitn-mbe-subgoal-1 bitn-mbe-subgoal-2 ash) (bits_alt-is-bits))
                      :use ((:instance bits_alt-is-bits (x x) (i n) (j n)))))))

(local (encapsulate ()

  (local (include-book "centaur/bitops/ihsext-basics" :dir :system))
;;  (local (include-book "arithmetic/top" :dir :system))

  (local (include-book "centaur/bitops/defaults" :dir :system))
  (local (include-book "centaur/bitops/equal-by-logbitp" :dir :system))

  (defthm nicer-version-of-my-bitn
           ;; This is maybe nicer because it avoids ASH, which could perhaps
           ;; shift the wrong way and create a huge number, in degenerate cases
           (implies (integerp n)
                    (equal (my-bitn x n)
                           (if (< n 0)
                               ;; The ASH goes the wrong way so we're sure
                               ;; it's even.
                               0
                             (if (logbitp n x) 1 0))))
           :hints(("Goal"
                   :in-theory (e/d (acl2::evenp-is-logbitp
                                    bitops::logbitp-of-ash-split )
                                   (logbitp
                                    ash)))))))

  (defthm bitn-for-gl
    ;; This is the definition we'll tell GL to use.  It's not as nice as, say,
    ;; LOGBITP, but it should do okay.
    (equal (bitn x n)
           (if (and (integerp x)
                    (integerp n))
               (if (< n 0)
                   0
                 (if (logbitp n x) 1 0))
             ;; Again use the stupid alias as a fallback, in case of non-integer
             ;; inputs.  Gross and would be good to get rid of this if possible.
             (let ((msg (cw "WARNING: guard violation for the function BITN during a GL proof.~%")))
               (declare (ignore msg))
               (if (not (integerp n))
                   0
                 (fl (/ (mod x (expt 2 (1+ n))) (expt 2 n)))))))
    :hints (("Goal" :in-theory (e/d (bits) (nicer-version-of-my-bitn your-bitn-is-my-bitn))
                    :use (bitn your-bits-is-my-bits nicer-version-of-my-bitn your-bitn-is-my-bitn)))
    :rule-classes ())


  ;; Tell GL to use our new definition.
  (gl::set-preferred-def bitn bitn-for-gl)





(defund binary-cat (x m y n)
  (declare (xargs :guard (and (integerp x)
                              (integerp y)
                              (natp m)
                              (natp n))))
  (if (and (natp m) (natp n))
      (+ (* (expt 2 n) (bits x (1- m) 0))
         (bits y (1- n) 0))
    0))

(local (include-book "../lib3/log"))

 (defthm binary-cat-for-gl
   (equal (binary-cat x m y n)
          (if (and (natp m)
                   (natp n))
              (logior (ash (BITS X (1- M) 0) n)
                      (BITS Y (1- N) 0))
            0))
   :hints (("Goal" :use ((:instance logior-expt (x (bits x (1- m) 0)) (y (bits y (1- n) 0))))
                   :in-theory (enable binary-cat ash)))
   :rule-classes ())

(gl::set-preferred-def binary-cat binary-cat-for-gl)
