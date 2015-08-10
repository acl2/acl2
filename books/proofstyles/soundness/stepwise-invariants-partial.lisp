(in-package "ACL2")

#|

  stepwise-invariants-partial.lisp
  ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

In this book, we show a proof of soundness of the stepwise invariant
proof strategy for partial correctness.  That is, we prove that if the
proof obligations for stepwise invariants is met then partial
correctness follows.  The proof is rather trivial, and hopefully
self-explanatory.

|#

(encapsulate
 (((step-fn *) => *)
  ((pre *) => *)
  ((post *) => *)
  ((exitpoint *) => *)
  ((inv *) => *))

 (local (defun step-fn (s) s))
 (local (defun pre (s) (declare (ignore s)) nil))
 (local (defun exitpoint (s) (declare (ignore s)) nil))
 (local (defun post (s) (declare (ignore s)) t))
 (local (defun inv (s) (declare (ignore s)) t))

 (defthm |pre satisfies inv|
   (implies (pre s) (inv s)))

 (defthm |inv persists|
   (implies (and (inv s)
                 (not (exitpoint s)))
            (inv (step-fn s))))

 (defthm |inv at exit implies post|
   (implies (and (inv s)
                 (exitpoint s))
            (post s))))


(defun run-fn (s n)
  (if (zp n)
      s
    (run-fn (step-fn s) (1- n))))

(defun-sk n-is-first (s n)
  (forall m (implies (and (natp m)
                          (< m n))
                     (not (exitpoint (run-fn s m))))))

(local (in-theory (disable n-is-first n-is-first-necc)))

(local
 (defun no-exit (s n)
   (declare (xargs :measure (nfix n)))
   (if (zp n) t
     (if (exitpoint s) nil
       (no-exit (step-fn s) (1- n))))))

(local
 (defthm no-exit-to-exitpoint
   (implies (and (no-exit s n)
                 (natp m)
                 (natp n)
                 (< m n))
            (not (exitpoint (run-fn s m))))))

(local
 (defthm no-exit-to-no-exit
   (implies (and (no-exit s n)
                 (natp m)
                 (natp n)
                 (< m n))
            (no-exit s m))))

(local
 (defthm inv-and-no-exit
   (implies (and (inv s)
                 (no-exit s n))
            (inv (run-fn s n)))))

(local (include-book "arithmetic/top-with-meta" :dir :system))


(local
 (defthm n-is-first-to-n-is-first
   (implies (and (n-is-first s n)
                 (natp n)
                 (not (exitpoint s)))
            (n-is-first (step-fn s) (1- n)))
   :hints (("Goal"
            :use ((:instance (:definition n-is-first)
                             (s (step-fn s))
                             (n (1- n)))
                  (:instance n-is-first-necc
                             (m (1+ (n-is-first-witness
                                     (step-fn s)
                                     (1- n)))))
                  (:instance (:definition run-fn)
                             (n (1+ (n-is-first-witness (step-fn s) (1- n))))))))))

(local
 (defun induction-hint (s m n)
   (declare (xargs :measure (acl2-count m)))
   (if (or (zp m) (exitpoint s))
       (list s m n)
     (induction-hint (step-fn s) (1- m) (1- n)))))

(local
 (defthm n-is-first-to-no-exit
   (implies (and (n-is-first s n)
                 (natp n)
                 (natp m)
                 (<= m n))
            (no-exit s m))
   :hints (("Goal"
            :induct (induction-hint s m n))
           ("Subgoal *1/1"
            :use ((:instance n-is-first-necc
                             (m 0)))))))


;; Here is the proof of partial correctness.

(defthm |partial correctness of stepwise invariants|
  (implies (and (pre s)
                (natp n)
                (exitpoint (run-fn s n))
                (n-is-first s n))
           (post (run-fn s n))))




