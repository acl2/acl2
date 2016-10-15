(in-package "ACL2")

; The lemmas below were initially provd after including ../lib/top (or at least
; they could have been; actually we used ../lib/ books bits, arith, and util).
; But we want to prove them in this support/ directory, so we include a
; book, top1, whose events are a superset of those that were in the
; aforementioned lib/ books, and then we put ourselves in the same theory as
; though we had included ../lib/top.

(include-book "rtl")
(include-book "fadd")
(local (include-book "top1"))
(local (in-theory (theory 'lib-top1)))

; Proof of bits-sum-swallow:

; Proof:  Since y < 2^(k+1), y[i:k+1] = 0.
;
; Since x[k] = 0, x[k:0] = x[k-1:0] < 2^k.
;
; Hence,
;
;   x[k:0] + y[k:0] < 2^k + 2^k = 2^(k+1)
;
; and
;
;   (x[k:0] + y[k:0])[k+1] = 0.
;
; By BITS-SUM,
;
;   (x+y)[i:k+1] = (x[i:k+1] + y[i:k+1] + (x[k:0] + y[k:0])[k+1])[i-k-1:0]
;                = (x[i:k+1])[i-k-1:0]
;                = x[i:k+1] {by BITS-BITS}.
;
; By BITS-BITS,
;
;   (x+y)[i:j] = (x+y)[i:k+1][i-k-1:j-k-1]
;              = x[i:k+1][i-k-1:j-k-1]
;              = x[i:j].

(local-defthm bits<expt
  (implies (and (natp x)
                (integerp i)
                (natp j)
                (<= j i)
                (equal n (1+ (- i j))))
           (< (bits x i j)
              (expt 2 n)))
  :hints (("Goal" :use ((:instance bits-bvecp
                                   (k n)))
           :in-theory (e/d (bvecp) (bits-bvecp bits-bvecp-simple))))
  :rule-classes :linear)

(local-defthm bits-sum-swallow-1-1-1-1
  (implies (and (natp x)
                (natp k)
                (= (bitn x k) 0))
           (< (bits x k 0)
              (expt 2 k)))
  :hints (("Goal" :use ((:instance bitn-plus-bits (n k) (m 0))
                        (:theorem (or (zp k) (< 0 k))))))
  :rule-classes :linear)

(local-defthm bits-sum-swallow-1-1-1-2
  (implies (and (natp y)
                (natp k)
                (<= y (expt 2 k)))
           (equal (bits y k 0) y))
  :hints (("Goal" :in-theory (enable bvecp)
           :expand ((expt 2 (1+ k))))))

(local-defthm bits-sum-swallow-1-1-1
  (implies (and (natp x)
                (natp y)
                (natp k)
                (= (bitn x k) 0)
                (<= y (expt 2 k)))
           (< (+ (bits x k 0) (bits y k 0))
              (expt 2 (1+ k))))
  :hints (("Goal" :expand ((expt 2 (1+ k)))))
  :rule-classes nil)

(local-defthm bits-sum-swallow-1-1
  (implies (and (natp x)
                (natp y)
                (natp k)
                (= (bitn x k) 0)
                (<= y (expt 2 k)))
           (equal (bitn (+ (bits x k 0) (bits y k 0))
                        (1+ k))
                  0))
  :hints (("Goal" :in-theory (enable bvecp) ; for bvecp-bitn-0
           :use bits-sum-swallow-1-1-1))
  :rule-classes nil)

(local-defthm bits-sum-swallow-1-2
  (implies (and (natp y)
                (natp k)
                (>= i k)
                (<= y (expt 2 k)))
           (equal (bits y i (1+ k))
                  0))
  :hints (("Goal" :in-theory (enable bvecp-bits-0 bvecp)
           :expand ((expt 2 (1+ k))))))

(local-defthm bits-sum-swallow-1
  (implies (and (natp x)
                (natp y)
                (natp k)
                (>= i k)
                (= (bitn x k) 0)
                (<= y (expt 2 k)))
            (equal (bits (+ x y) i (1+ k))
                   (bits x i (1+ k))))
  :hints (("Goal" :use ((:instance bits-sum (j (1+ k)))
                        bits-sum-swallow-1-1))))

(defthmd bits-sum-swallow
  (implies (and (equal (bitn x k) 0)
                (natp x)
                (natp y)
                (integerp i)
                (integerp j)
                (integerp k)
                (>= i j)
                (> j k)
                (>= k 0)
                (<= y (expt 2 k)))
           (equal (bits (+ x y) i j)
                  (bits x i j)))
  :hints (("Goal"
           ;; We deliberately leave bits-bits enabled because we need another
           ;; instance of it too.
           :use ((:instance bits-bits
                            (x (+ x y))
                            (i i)
                            (j (1+ k))
                            (k (1- (- i k)))
                            (l (1- (- j k))))))))

(defthmd bits-sum-of-bits
  (implies (and (integerp x)
                (integerp y)
                (natp i))
           (equal (bits (+ x (bits y i 0)) i 0)
                  (bits (+ x y) i 0)))
  :hints (("Goal" :use ((:instance bits-sum
                                   (x x)
                                   (y (bits y i 0))
                                   (i i)
                                   (j 0))
                        (:instance bits-sum
                                   (x x)
                                   (y y)
                                   (i i)
                                   (j 0))))))

(defthm bits-sum-3
  (implies (and (integerp x)
                (integerp y)
                (integerp z)
                (integerp i)
                (integerp j))
           (equal (bits (+ x y z) i j)
                  (bits (+ (bits x i j)
                           (bits y i j)
                           (bits z i j)
                           (bitn (+ (bits x (1- j) 0) (bits y (1- j) 0))
                                 j)
                           (bitn (+ (bits (+ x y) (1- j) 0) (bits z (1- j) 0))
                                 j))
                        (- i j) 0)))
  :hints (("Goal" :use ((:instance bits-sum
                                   (x x)
                                   (y y)
                                   (i (1- j))
                                   (j 0))
                        (:instance bits-sum
                                   (x x)
                                   (y y)
                                   (i i)
                                   (j j))
                        (:instance bits-sum
                                   (x (+ x y))
                                   (y z)
                                   (i i)
                                   (j j))
                        (:instance bits-sum-of-bits
                                   (x (+ (bits z i j)
                                         (bitn (+ (bits z (1- j) 0)
                                                  (bits (+ x y) (1- j) 0))
                                               j)))
                                   (y (+ (bits x i j)
                                         (bits y i j)
                                         (bitn (+ (bits x (1- j) 0)
                                                  (bits y (1- j) 0))
                                               j)))
                                   (i (+ i (* -1 j)))))))
  :rule-classes ())

(local-defthm bits-sum-3-with-gen-normal-case
  (implies (and (integerp x)
                (integerp y)
                (integerp z)
                (integerp i)
                (integerp j)
                (< 0 j))
           (equal (bits (+ x y z) i j)
                  (bits (+ (bits x i j)
                           (bits y i j)
                           (bits z i j)
                           (gen x y (1- j) 0)
                           (gen (+ x y) z (1- j) 0))
                        (- i j) 0)))
  :hints (("Goal" :use bits-sum-3
           :in-theory (enable gen-as-bitn)))
  :rule-classes ())

(defthm bits-sum-3-with-gen
  (implies (and (integerp x)
                (integerp y)
                (integerp z)
                (integerp i)
                (integerp j))
           (equal (bits (+ x y z) i j)
                  (bits (+ (bits x i j)
                           (bits y i j)
                           (bits z i j)
                           (gen x y (1- j) 0)
                           (gen (+ x y) z (1- j) 0))
                        (- i j) 0)))
  :hints (("Goal" :use (bits-sum-3 bits-sum-3-with-gen-normal-case)))
  :rule-classes ())

(defthmd lior-bits-1
  (equal (lior (bits x (1- n) 0)
               y
               n)
         (lior x y n))
  :hints (("Goal" :in-theory (e/d (lior)
                                  (logior
                                   lior-commutative

; Matt K. mod for assume-true-false improvement for calls of the form (integerp
; (+ k term)).

                                   (force))))))

(defthmd lior-bits-2
  (equal (lior x
               (bits y (1- n) 0)
               n)
         (lior x y n))
  :hints (("Goal" :in-theory (e/d (lior)
                                  (logior
                                   lior-commutative

; Matt K. mod for assume-true-false improvement for calls of the form (integerp
; (+ k term)).

                                   (force))))))

(defthmd land-bits-1
  (equal (land (bits x (1- n) 0)
               y
               n)
         (land x y n))
  :hints (("Goal" :in-theory (e/d (land)
                                  (logior
                                   land-commutative

; Matt K. mod for assume-true-false improvement for calls of the form (integerp
; (+ k term)).

                                   (force))))))

(defthmd land-bits-2
  (equal (land x
               (bits y (1- n) 0)
               n)
         (land x y n))
  :hints (("Goal" :in-theory (e/d (land)
                                  (logior
                                   land-commutative

; Matt K. mod for assume-true-false improvement for calls of the form (integerp
; (+ k term)).

                                   (force))))))

(defthmd lxor-bits-1
  (equal (lxor (bits x (1- n) 0)
               y
               n)
         (lxor x y n))
  :hints (("Goal" :in-theory (e/d (lxor)
                                  (logior
                                   lxor-commutative

; Matt K. mod for assume-true-false improvement for calls of the form (integerp
; (+ k term)).

                                   (force))))))

(defthmd lxor-bits-2
  (equal (lxor x
               (bits y (1- n) 0)
               n)
         (lxor x y n))
  :hints (("Goal" :in-theory (e/d (lxor)
                                  (logior
                                   lxor-commutative

; Matt K. mod for assume-true-false improvement for calls of the form (integerp
; (+ k term)).

                                   (force))))))

; Proof of lior-slice:

; Note that (2^i - 2^j) = 2^j(2^(i-j)-1) = {2^(i-j)-1,j'b0}

; x[n-1:0] | (2^i - 2^j) =
; {x[n-1:i], x[i-1:j], x[j-1:0]} | {(n-i)'b0, 2^(i-j), j'b0} =
; [by LIOR-CAT, LIOR-0, and LIOR-ONES]
; {{x[n-1:i], 2^(i-j)-1, x[j-1:0]}.

(local-defthm lior-slice-1
  (implies (and (<= j i)
                (<= i n)
                (integerp n)
                (integerp i)
                (integerp j)
                (<= 0 j))
           (equal (cat (bits x (1- n) i) (- n i)
                       (bits x (1- i) j) (- i j)
                       (bits x (1- j) 0) j)
                  (bits x (1- n) 0)))
  :hints (("Goal" :use ((:instance cat-bits-bits
                                   (x (bits x (1- i) 0))
                                   (i (1- i))
                                   (j j)
                                   (k (1- j))
                                   (l 0)
                                   (m (- i j))
                                   (n j))
                        (:instance cat-bits-bits
                                   (x x)
                                   (i (1- n))
                                   (j i)
                                   (k (1- i))
                                   (l 0)
                                   (m (- n i))
                                   (n i)))))
  :rule-classes nil)

(local-defthm bvecp-power-of-2-minus-1
  (implies (and (integerp k)
                (equal k k2)
                (< 0 k))
           (bvecp (1- (expt 2 k))
                  k2))
  :hints (("Goal" :in-theory (enable bvecp))))

(local-defthm bvecp-power-of-2-minus-1-alt
  (implies (and (natp k)
                (equal k2 (1+ k)))
           (bvecp (1- (* 2 (expt 2 k)))
                  k2))
  :hints (("Goal" :in-theory (enable bvecp expt))))

(local-defthm lior-slice-2
  (implies (and (<= j i)
                (<= i n)
                (integerp n)
                (integerp i)
                (integerp j)
                (<= 0 j))
           (equal (cat 0                     (- n i)
                       (1- (expt 2 (- i j))) (- i j)
                       0                     j)
                  (- (expt 2 i) (expt 2 j))))
  ;; The following hint is very weird!!  It can't be on Goal or Goal'.  The
  ;; idea came from a proof-builder proof.  I should investigate....
  :hints (("Goal''" :in-theory (enable cat expt)))
  :rule-classes nil)

(local
 (defthmd lior-slice-3-1
   (implies (and (<= j i)
                 (integerp i)
                 (integerp j)
                 (<= 0 j)
                 (equal k (1- (expt 2 (- i j))))
                 (equal diff (- i j)))
            (equal (lior k
                         (bits x (1- i) j)
                         diff)
                   (1- (expt 2 (- i j)))))
   :hints (("Goal" :use ((:instance lior-ones
                                    (x (bits x (1- i) j))
                                    (n (- i j))))))))

(local-defthm lior-slice-3
  (implies (and (<= j i)
		(<= i n)
		(integerp n)
		(integerp i)
		(integerp j)
		(<= 0 j))
	   (equal (lior (cat (bits x (1- n) i) (- n i)
                             (bits x (1- i) j) (- i j)
                             (bits x (1- j) 0) j)
                        (cat 0                     (- n i)
                             (1- (expt 2 (- i j))) (- i j)
                             0                     j)
                        n)
                  (cat (bits x (1- n) i)     (- n i)
                       (1- (expt 2 (- i j))) (- i j)
                       (bits x (1- j) 0)     j)))
  :hints (("Goal" :in-theory (e/d (lior-cat lior-slice-3-1)
                                  (cat-bits-bits cat-0))
           :cases ((and (equal j i) (equal j 0) (equal i n))
                   (and (equal j i) (not (equal j 0)) (equal i n))
                   (and (not (equal j i)) (equal j 0) (equal i n))
                   (and (equal j i) (equal j 0) (not (equal i n)))
                   (and (equal j i) (not (equal j 0)) (not (equal i n)))
                   (and (not (equal j i)) (equal j 0) (not (equal i n)))
                   (and (not (equal j i)) (not (equal j 0)) (not (equal i n))))))
  :rule-classes nil)

(local-defthm lior-slice-almost
  (implies (and (<= j i)
		(<= i n)
		(integerp n)
		(integerp i)
		(integerp j)
		(<= 0 j))
	   (equal (lior (bits x (1- n) 0)
                        (- (expt 2 i) (expt 2 j))
                        n)
		  (cat (bits x (1- n) i)     (- n i)
                       (1- (expt 2 (- i j))) (- i j)
                       (bits x (1- j) 0)     j)))
  :hints (("Goal" :use (lior-slice-1 lior-slice-2 lior-slice-3)
           :in-theory (theory 'ground-zero)))
  :rule-classes nil)

(defthmd lior-slice
  (implies (and (<= j i)
		(<= i n)
		(integerp n)
		(integerp i)
		(integerp j)
		(<= 0 j))
	   (equal (lior x
                        (- (expt 2 i) (expt 2 j))
                        n)
		  (cat (bits x (1- n) i)     (- n i)
                       (1- (expt 2 (- i j))) (- i j)
                       (bits x (1- j) 0)     j)))
  :hints (("Goal" :use (lior-slice-almost)
           :in-theory (enable lior-bits-1))))

(local-defthm land-base-lemma
  (implies (and (bvecp x 1) (bvecp y 1))
           (equal (land x y 1)
                  (if (and (equal (bitn x 0) 1)
                           (equal (bitn y 0) 1))
                      1
                    0)))
  :rule-classes nil)

(defthm land-base
  (equal (land x y 1)
         (if (and (equal (bitn x 0) 1)
                  (equal (bitn y 0) 1))
             1
           0))
  :hints (("Goal" :use ((:instance land-base-lemma
                                   (x (bits x 0 0))
                                   (y (bits y 0 0)))
                        (:instance land-bits-1
                                   (x x)
                                   (y (bits y 0 0))
                                   (n 1))
                        (:instance land-bits-2 (n 1)))))
  :rule-classes nil)

(local-defthm lior-base-lemma
  (implies (and (bvecp x 1) (bvecp y 1))
           (equal (lior x y 1)
                  (if (or (equal (bitn x 0) 1)
                          (equal (bitn y 0) 1))
                      1
                    0)))
  :rule-classes nil)

(defthm lior-base
  (equal (lior x y 1)
         (if (or (equal (bitn x 0) 1)
                 (equal (bitn y 0) 1))
             1
           0))
  :hints (("Goal" :use ((:instance lior-base-lemma
                                   (x (bits x 0 0))
                                   (y (bits y 0 0)))
                        (:instance lior-bits-1
                                   (x x)
                                   (y (bits y 0 0))
                                   (n 1))
                        (:instance lior-bits-2 (n 1)))))
  :rule-classes nil)

(local-defthm lxor-base-lemma
  (implies (and (bvecp x 1) (bvecp y 1))
           (equal (lxor x y 1)
                  (if (iff (equal (bitn x 0) 1)
                           (equal (bitn y 0) 1))
                      0
                    1)))
  :rule-classes nil)

(defthm lxor-base
  (equal (lxor x y 1)
         (if (iff (equal (bitn x 0) 1)
                  (equal (bitn y 0) 1))
             0
           1))
  :hints (("Goal" :use ((:instance lxor-base-lemma
                                   (x (bits x 0 0))
                                   (y (bits y 0 0)))
                        (:instance lxor-bits-1
                                   (x x)
                                   (y (bits y 0 0))
                                   (n 1))
                        (:instance lxor-bits-2 (n 1)))))
  :rule-classes nil)

(local (in-theory (theory 'lib-top1)))

(local-defthm lxor-1-not-2
  (equal (equal 2 (lxor i j 1))
         nil)
  :hints (("Goal" :expand ((lxor i j 1))
           :use ((:instance acl2::bvecp-1-rewrite
                            (acl2::x (bitn i 0)))
                 (:instance acl2::bvecp-1-rewrite
                            (acl2::x (bitn j 0)))))))

(local
 (encapsulate
  ()

  (local-defthm bitn-of-1-less-than-power-of-2-lemma-1
    (implies (natp j)
             (equal (bitn (1- (expt 2 (1+ j))) j)
                    1))
    :hints (("Goal" :in-theory (enable acl2::bvecp-bitn-1 bvecp)
             :expand ((expt 2 (+ 1 j))))))

  (defthm bitn-of-1-less-than-power-of-2
    (implies (and (integerp i)
                  (natp j)
                  (< j i))
             (equal (bitn (1- (expt 2 i)) j)
                    1))
    :hints (("Goal" :use ((:instance acl2::bitn-plus-mult
                                     (acl2::x (1- (expt 2 (1+ j))))
                                     (acl2::k (1- (expt 2 (- i (1+ j)))))
                                     (acl2::m (1+ j))
                                     (acl2::n j))))))))

(local-defun prop-as-lxor-thm (i j x y)
  (implies (and (natp i)
                (natp j)
                (<= j i)
                (natp x)
                (natp y))
           (equal (prop x y i j)
                  (log= (lxor (bits x i j) (bits y i j) (1+ (- i j)))
                        (1- (expt 2 (1+ (- i j))))))))

(local-defthm prop-as-lxor-thm-proved-1
  (implies (not (and (natp i) (natp j) (<= j i)))
           (prop-as-lxor-thm i j x y)))

(local-defthm prop-as-lxor-thm-proved-3-1
  (implies (and (integerp i)
                (<= 0 i)
                (integerp j)
                (<= 0 j)
                (<= j i)
                (equal (bitn x i) (bitn y i))
                (integerp x)
                (<= 0 x)
                (integerp y)
                (<= 0 y))
           (not (equal (bitn (+ -1 (expt 2 (+ 1 i (* -1 j)))) (- i j))
                       (bitn (lxor (bits x i j)
                                   (bits y i j)
                                   (+ 1 i (* -1 j)))
                             (- i j)))))
  :rule-classes nil)

(local-defthm prop-as-lxor-thm-proved-3
  (implies (and (and (natp i) (natp j) (<= j i))
                (= (bitn x i) (bitn y i)))
           (prop-as-lxor-thm i j x y))
  :hints (("Goal" :use prop-as-lxor-thm-proved-3-1
           :in-theory (e/d (log=)
                           (bitn-of-1-less-than-power-of-2)))))

(local (in-theory (enable bvecp-0)))

(local-defthm prop-as-lxor-thm-proved-2
  (implies (and (and (natp i) (natp j) (<= j i))
                (not (= (bitn x i) (bitn y i)))
                (prop-as-lxor-thm (+ -1 i) j x y))
           (prop-as-lxor-thm i j x y))
  :hints (("Goal" :in-theory (enable log=)
           :expand ((expt 2 (+ 1 i (* -1 j))))
           :use ((:instance acl2::bitn-plus-bits (acl2::m 0)
                            (n (- i j))
                            (acl2::x (lxor (bits x i j)
                                           (bits y i j)
                                           (+ 1 i (* -1 j)))))
                 (:instance acl2::bvecp-1-rewrite
                            (acl2::x (bitn x i)))
                 (:instance acl2::bvecp-1-rewrite
                            (acl2::x (bitn y i)))
                 (:instance acl2::bvecp-1-rewrite
                            (acl2::x (bitn x 0)))
                 (:instance acl2::bvecp-1-rewrite
                            (acl2::x (bitn y 0)))))))

(local-defthm prop-as-lxor-thm-proved
  (prop-as-lxor-thm i j x y)
  :hints (("Goal" :induct (prop x y i j)
           :in-theory (disable prop-as-lxor-thm)))
  :rule-classes nil)

(defthmd prop-as-lxor
  (implies (and (natp i)
                (natp j)
                (<= j i)
                (natp x)
                (natp y))
           (equal (prop x y i j)
                  (log= (lxor (bits x i j) (bits y i j) (1+ (- i j)))
                        (1- (expt 2 (1+ (- i j)))))))
  :hints (("Goal" :use prop-as-lxor-thm-proved)))
