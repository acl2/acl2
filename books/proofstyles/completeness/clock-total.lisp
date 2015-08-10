(in-package "ACL2")

(include-book "generic-total")
(include-book "misc/defpun" :dir :system)

(local (include-book "arithmetic/top-with-meta" :dir :system))

;; I do the obvious thing, namely define the function clock with the
;; tail-recursive equation so that it drives us to the first moment at
;; which we reach an exitpoint.


(defpun clock-fn-tail (s i)
  (if (exitpoint s) i
    (clock-fn-tail (step-fn s) (1+ i))))

(defun clock-fn (s)
  (clock-fn-tail s 0))

;; Now I know how to prove theorems about these tail-recursive
;; equations.  So I just go through them.

(local
 (defun cutpoint-induction (k steps s)
   (if (zp k) (list k steps s)
     (cutpoint-induction (1- k) (1+ steps) (step-fn s)))))


(local
 (encapsulate
  ()

 (local
  (defthmd clock-fn-tail-inv
    (implies (and (exitpoint (run-fn s k))
                  (natp steps))
             (let* ((result  (clock-fn-tail s steps))
                    (exitpoint-steps (- result steps)))
               (and (natp result)
                    (natp exitpoint-steps)
                    (implies (natp k)
                             (<= exitpoint-steps k))
                    (exitpoint (run-fn s exitpoint-steps)))))
    :hints (("Goal"
             :in-theory (enable natp)
             :induct (cutpoint-induction k steps s)))))


 (defthm clock-fn-is-natp
  (implies (exitpoint (run-fn s k))
           (natp (clock-fn s)))
  :rule-classes (:rewrite :forward-chaining :type-prescription)
  :hints (("Goal"
           :use ((:instance clock-fn-tail-inv
                            (steps 0))))))

 (defthm clock-fn-provide-exitpoint
   (implies (exitpoint (run-fn s k))
            (exitpoint (run-fn s (clock-fn s))))
   :hints (("Goal"
            :use ((:instance clock-fn-tail-inv
                             (steps 0))))))

 (defthm clock-fn-is-minimal
  (implies (and (exitpoint (run-fn s k))
                (natp k))
           (<= (clock-fn s)
               k))
  :rule-classes :linear
  :hints (("Goal"
           :use ((:instance clock-fn-tail-inv
                            (steps 0))))))))

(local (in-theory (disable clock-fn)))

;; Now I prove that the first thing to reach an exitpoint is the clock
;; function.

(local
 (defthm n-is-first-reduces-to-clock
   (implies (and (n-is-first s n)
                 (exitpoint (run-fn s n))
                 (natp n)
                 (pre s))
            (equal (clock-fn s) n))
   :hints (("Goal"
            :use ((:instance n-is-first-necc
                             (m (clock-fn s))))))))

;; And finally I just prove the desired clock function theorems.

(defthm |clock fn is natp|
   (implies (pre s)
            (natp (clock-fn s)))
   :hints (("Goal"
            :in-theory (disable |termination|)
            :use ((:instance |termination|))))
   :rule-classes :type-prescription)

(defthm |clock fn is minimal|
  (implies (and (pre s)
                (natp n)
                (exitpoint (run-fn s n)))
           (<= (clock-fn s) n))
  :rule-classes :linear)

(defthm |clock fn produces exitpoint|
  (implies (pre s)
           (exitpoint (run-fn s (clock-fn s))))
   :hints (("Goal"
            :in-theory (disable |termination|)
            :use ((:instance |termination|)))))

(defthm |clock fn produces postcondition|
  (implies (pre s)
           (post (run-fn s (clock-fn s))))
   :hints (("Goal"
            :in-theory (disable |termination|)
            :use ((:instance |termination|)))))


