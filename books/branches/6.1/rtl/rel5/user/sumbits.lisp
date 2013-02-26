; This book can provide help for reducing equality of bit vectors to equality
; of respective bits.  It provides the "badguy" trick.  For an example, see the
; proof of lior0-cat in ../support/merge2.lisp.

(in-package "ACL2")

(local (include-book "../support/sumbits"))
(local (include-book "../support/guards"))

; We need some definitions to be present.  We define them using defun rather
; than defund because we don't want inclusion of this book to affect whether or
; not these functions are disabled, if they were already defined.

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

(defund bvecp (x k)
  (declare (xargs :guard (integerp k)))
  (and (integerp x)
       (<= 0 x)
       (< x (expt 2 k))))

(local (in-theory (disable fl bits bitn bvecp)))

;; New stuff

(defun sumbits (x n)
  (if (zp n)
      0
    (+ (* (expt 2 (1- n)) (bitn x (1- n)))
       (sumbits x (1- n)))))

(defthmd sumbits-bits
  (implies (and (natp x)
                (natp n)
                (> n 0))
           (equal (sumbits x n)
                  (bits x (1- n) 0)))
  :hints (("Goal" :in-theory (enable bits-n-n-rewrite) ;yuck?
           :induct (sumbits x n))
          ("Subgoal *1/2" :use ((:instance bitn-plus-bits (n (1- n)) (m 0))))))

(defthmd sumbits-thm
     (implies (and (bvecp x n)
                   (natp n)
                   (> n 0))
              (equal (sumbits x n)
                     x))
   :hints (("Goal" :in-theory (enable sumbits-bits bvecp))))

(defun sumbits-badguy (x y k)
  (if (zp k)
      0 ; arbitrary
    (if (not (equal (bitn x (1- k)) (bitn y (1- k))))
        (1- k)
      (sumbits-badguy x y (1- k)))))

(defthmd sumbits-badguy-is-correct
  (implies (and (bvecp x k)
                (bvecp y k)
                (equal (bitn x (sumbits-badguy x y k))
                       (bitn y (sumbits-badguy x y k)))
                (integerp k)
                (< 0 k))
           (equal (equal x y) t))
  :hints (("Goal"
           :use sumbits-badguy-is-correct-lemma
           :in-theory (enable sumbits-thm))))

(defthmd sumbits-badguy-bounds
  (implies (and (integerp k)
                (< 0 k))
           (let ((badguy (sumbits-badguy x y k)))
             (and (integerp badguy)
                  (<= 0 badguy)
                  (< badguy k)))))
