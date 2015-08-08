(in-package "ACL2")

#|

  stepwise-invariants-partial.lisp
  ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

In this book, we show a proof of soundness of the stepwise invariant
proof strategy for total correctness.  That is, we prove that if the
proof obligations for stepwise invariants is met then total
correctness follows.  The proof is rather trivial, and hopefully
self-explanatory.

|#

(encapsulate
 (((step-fn *) => *)
  ((pre *) => *)
  ((post *) => *)
  ((exitpoint *) => *)
  ((inv *) => *)
  ((m *) => *))

 (local (defun step-fn (s) s))
 (local (defun pre (s) (declare (ignore s)) nil))
 (local (defun exitpoint (s) (declare (ignore s)) nil))
 (local (defun post (s) (declare (ignore s)) t))
 (local (defun inv (s) (declare (ignore s)) nil))
 (local (defun m (s) (declare (ignore s)) 0))

 (defthm |pre satisfies inv|
   (implies (pre s) (inv s)))

 (defthm |inv persists|
   (implies (and (inv s)
                 (not (exitpoint s)))
            (inv (step-fn s))))

 (defthm |inv at exit implies post|
   (implies (and (inv s)
                 (exitpoint s))
            (post s)))

 (defthm |m is ordinal|
   (implies (inv s)
            (o-p (m s))))

 (defthm |m decreases|
   (implies (and (inv s)
                 (not (exitpoint s)))
            (o< (m (step-fn s))
                (m s)))))


(defun run-fn (s n)
  (if (zp n)
      s
    (run-fn (step-fn s) (1- n))))

(defun-sk n-is-first (s n)
  (forall m (implies (and (natp m)
                          (< m n))
                     (not (exitpoint (run-fn s m))))))

(local (in-theory (disable n-is-first n-is-first-necc)))

;; I could have followed the partial correctness proof here.  But I
;; think it's just easier to define a clock function and generate the
;; proof that way.

(local
 (defun clock-fn (s)
   (declare (xargs :measure (if (inv s) (m s) 0)))
   (if (or (exitpoint s) (not (inv s)))
       0
     (1+ (clock-fn (step-fn s))))))

(local
 (defthm clock-fn-is-minimal
   (implies (and (inv s)
                 (natp n)
                 (exitpoint (run-fn s n)))
            (<= (clock-fn s) n))
   :rule-classes :linear))

(local
 (include-book "ordinals/ordinals" :dir :system))

(local
 (defthm clock-fn-is-exit
   (implies (inv s)
            (exitpoint (run-fn s (clock-fn s))))))

(local
 (defthm clock-fn-is-inv
   (implies (inv s)
            (inv (run-fn s (clock-fn s))))))

(local
 (defthm total-correctness-of-clock
   (implies (pre s)
            (post (run-fn s (clock-fn s))))))

(local
 (defthm n-is-first-reduces-to-clock
   (implies (and (n-is-first s n)
                 (exitpoint (run-fn s n))
                 (natp n)
                 (pre s))
            (equal (clock-fn s) n))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance n-is-first-necc
                             (m (clock-fn s))))))))


(defthm |stepwise produces partial correctness|
  (implies (and (pre s)
                (natp n)
                (exitpoint (run-fn s n))
                (n-is-first s n))
           (post (run-fn s n)))
  :hints (("Goal"
           :use n-is-first-reduces-to-clock)))


(defun-sk exists-exitpoint (s)
  (exists n (and (natp n)
                 (exitpoint (run-fn s n)))))

(local (in-theory (disable exists-exitpoint-suff
                           exists-exitpoint)))

(defthm |stepwise invariants termination|
  (implies (pre s)
           (exists-exitpoint s))
  :hints (("Goal"
           :use ((:instance exists-exitpoint-suff
                            (n (clock-fn s)))))))
