(in-package "ACL2")

#|

  clock-partial.lisp
  ~~~~~~~~~~~~~~~~~~

Author: Sandip Ray
Date: Fri Aug 10 15:37:42 2007

In this book, we show that the soundness of clock functions as a proof strategy
for deductive verification of total correctness of deterministic sequential
programs.  The proof is rather straightforward, since clock functions tend to
do *more* than soundness.

|#


(defstub step-fn (*) => *)

(defun run-fn (s n)
  (if (zp n) s
    (run-fn (step-fn s) (1- n))))


(encapsulate
 (((clock-fn *) => *)
  ((pre *) => *)
  ((post *) => *)
  ((exitpoint *) => *))

 (local (defun pre (s) (declare (ignore s)) nil))
 (local (defun exitpoint (s) (declare (ignore s)) nil))
 (local (defun post (s) (declare (ignore s)) nil))
 (local (defun clock-fn (s) (declare (ignore s)) 0))

 (defthm |clock function is natural|
   (implies (pre s)
            (natp (clock-fn s)))
   :rule-classes :type-prescription)

 (defthm |clock function is minimal|
   (implies (and (pre s)
                 (natp n)
                 (exitpoint (run-fn s n)))
            (<= (clock-fn s) n))
   :rule-classes :linear)

 (defthm |clock function produces exitpoint|
   (implies (pre s)
            (exitpoint (run-fn s (clock-fn s)))))

 (defthm |clock function produces postcondition|
   (implies (pre s)
            (post (run-fn s (clock-fn s))))))


(defun-sk n-is-first (s n)
  (forall m (implies (and (natp m)
                          (< m n))
                     (not (exitpoint (run-fn s m))))))

(local (in-theory (disable n-is-first n-is-first-necc)))

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


(defthm |clock function produces partial correctness|
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

(defthm |clock function terminates|
  (implies (pre s)
           (exists-exitpoint s))
  :hints (("Goal"
           :use ((:instance exists-exitpoint-suff
                            (n (clock-fn s)))))))


