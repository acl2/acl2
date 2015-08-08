(in-package "ACL2")

(encapsulate
 (((step-fn *) => *)
  ((pre *) => *)
  ((exitpoint *) => *)
  ((post *) => *))

 (local (defun step-fn (s) s))
 (local (defun pre (s) (declare (ignore s)) nil))
 (local (defun exitpoint (s) (declare (ignore s)) nil))
 (local (defun post (s) (declare (ignore s)) nil))

 (defun run-fn (s n)
   (if (zp n) s
     (run-fn (step-fn s) (1- n))))

 (defun-sk n-is-first (s n)
   (forall m (implies (and (natp m)
                           (< m n))
                      (not (exitpoint (run-fn s m))))))


 (defthm |partial correctness|
   (implies (and (pre s)
                 (natp n)
                 (exitpoint (run-fn s n))
                 (n-is-first s n))
           (post (run-fn s n))))

 (defun-sk exists-exitpoint (s)
  (exists n (and (natp n)
                 (exitpoint (run-fn s n)))))


 (defthm |termination|
   (implies (pre s)
            (exists-exitpoint s))))









