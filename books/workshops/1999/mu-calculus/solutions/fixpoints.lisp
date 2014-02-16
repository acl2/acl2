(in-package "SETS")

(include-book "sets")

(encapsulate
 ((f (X) t)
  (S () t))

 (local (defun f (X)
          (declare (ignore X))
          nil))

 (local (defun S ()
          nil))

 (defthm f-is-monotonic
   (implies (=< X Y)
            (=< (f X) (f Y))))

 (defthm S-is-top
   (=< (f X) (set-union X (S)))))

; applyf is constrained, so we don't care about its guards.
(defun applyf (X n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      X
    (if (== X (f X))
        X
      (applyf (f X) (1- n)))))

(local
 (defcong == == (f X) 1
   :hints (("Goal"
            :in-theory (enable ==)))))

(local
 (defcong == == (applyf X m) 1))

(local
 (defthm normal-applyf-form
   (== (applyf (f X) m)
       (f (applyf X m)))))

(local
 (defthm mono-helper
   (implies (and (=< X Y)
                 (=< (f Y) Y))
            (=< (f X) Y))
   :hints (("Goal"
            :in-theory (disable f-is-monotonic)
            :use ((:instance f-is-monotonic))))))

(defabbrev lfpf ()
  (applyf nil (cardinality (S))))

(local
 (defthm lfix-is-below-all-post-fixpoints-aux
   (implies (=< (f X) X)
            (=< (applyf nil n) X))
   :hints (("Goal" :in-theory (disable =<-LEN-REM-DUPS)))))  ;; RBK: t-s and lin

; Exercise 12, part 2
(defthm lfix-is-below-all-post-fixpoints
  (implies (=< (f X) X)
           (=< (lfpf) X)))

(local
 (defthm applyf-goes-up-on-nil
   (=< (applyf nil n)
       (applyf nil (1+ n)))
   :hints (("Goal" :in-theory (disable =<-LEN-REM-DUPS)))))  ;; RBK: t-s and lin

(local
 (defthm len-of-non-empty-set
   (implies (not (== nil X))
            (<= 1 (len (rem-dups X))))
   :hints (("Goal" :in-theory (disable =<-LEN-REM-DUPS)))))  ;; RBK: t-s and lin

(local
 (defthm lfix-count-argument
   (implies (and (integerp n)
                 (< 0 n)
                 (not (== (applyf nil n)
                          (applyf nil (1- n)))))
            (>= (len (rem-dups (applyf nil n)))
                n))
   :hints (("Goal" :induct (applyf nil n))
           ;; "1/3.4" replaced twice by "1/3.3" for v2-6 by Matt K.
           ("Subgoal *1/3.2"
            :in-theory (enable ==)
            :use ((:instance applyf-goes-up-on-nil
                             (n (+ -1 n)))))
           ("Subgoal *1/3.2'5'"
            :in-theory (disable s<-implies-<-len)
            :use ((:instance s<-implies-<-len
                             (x (applyf nil (+ -1 n)))
                             (y (f (applyf nil (+ -1 n)))))))
           ("Subgoal *1/2" :in-theory (disable =<-LEN-REM-DUPS
                                               |X == Y  =>  X =< Y / Y =< X|))  ;; RBK: f-c and lin
           ("Subgoal *1.2/2" :in-theory (disable =<-LEN-REM-DUPS
                                               |X == Y  =>  X =< Y / Y =< X|))  ;; RBK: f-c and lin
           ("Subgoal *1.1/2" :in-theory (disable =<-LEN-REM-DUPS
                                               |X == Y  =>  X =< Y / Y =< X|)))))  ;; RBK: f-c and lin


(local
 (defthm S-is-top-really
   (=< (f (S)) (S))
   :hints (("Goal"
            :in-theory (disable S-is-top)
            :use ((:instance S-is-top (X (S))))))))

(local
 (defthm applyf-on-nil-below-top
   (=< (f (applyf nil n))
       (S))))

; Exercise 12, part 1
(defthm lfix-is-a-fixpoint
  (== (f (lfpf))
      (lfpf))
  :hints (("Goal"
           :in-theory (enable ==)
           :use ((:instance lfix-count-argument
                            (n (1+ (len (rem-dups (S))))))))
          ("Goal'''"
           :in-theory (disable applyf-on-nil-below-top)
           :use ((:instance applyf-on-nil-below-top
                            (n (len (rem-dups (S)))))))))

(defabbrev gfpf ()
  (applyf (S) (cardinality (S))))

(local
 (defthm gfix-is-above-all-pre-fixpoints-aux
   (implies (and (=< X (S))
                 (=< X (f X)))
            (=< X (applyf (S) n)))
   :hints (("Goal" :induct (applyf (S) n)))))

; Exercise 13, part 2
(defthm gfix-is-above-all-pre-fixpoints
  (implies (and (=< X (S))
                (=< X (f X)))
           (=< X (gfpf))))

(local
 (defthm applyf-goes-down-on-pre-fixes
   (implies (=< (f X) X)
            (=< (applyf X n) X))))

(local
 (defthm applyf-goes-down
   (implies (and (integerp m)
                 (< n m)
                 (=< (f X) X))
            (=< (applyf X m)
                (applyf X n)))))

(local
 (defthm applyf-f-S
   (=< (f (applyf (S) n)) (applyf (S) n))))

(local
 (defthm S-len
   (implies (equal (len (rem-dups (f (S))))
                   (len (rem-dups (S))))
            (=< (S) (f (S))))
   :hints (("goal"
            :use ((:instance subset-lens
                             (x (f (S)))
                             (y (S))))))
   :rule-classes :forward-chaining))

(local
 (defthm gfix-count-argument
   (implies (and (integerp n)
                 (< 0 n)
                 (not (== (applyf (S) n)
                          (applyf (S) (1- n)))))
            (<= (len (rem-dups (applyf (S) n)))
                (- (len (rem-dups (S))) n)))
   :hints (("Goal"
            :induct (applyf (S) n)
            :in-theory (enable ==))
           ("Subgoal *1/3.2"
            :use ((:instance s<-implies-<-len
                             (x (f (applyf (S) (+ -1 n))))
                             (y (applyf (S) (+ -1 n)))))))))

; Exercise 13, part 1
(defthm gfix-is-a-fixpoint
  (== (f (gfpf))
      (gfpf))
 :hints (("Goal"
           :in-theory (enable ==)
           :use ((:instance gfix-count-argument
                            (n (+ 1 (len (rem-dups (S))))))))))

