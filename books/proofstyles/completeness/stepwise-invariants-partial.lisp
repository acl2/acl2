(in-package "ACL2")

(include-book "clock-partial")

(local (include-book "arithmetic/top-with-meta" :dir :system))

(defun-sk exists-some-exitpoint (s)
  (exists alpha (exitpoint (run-fn s alpha))))


(local (in-theory (disable exists-some-exitpoint
                           exists-some-exitpoint-suff)))

(defun-sk inv (s)
  (exists (p m)
          (and (pre p)
               (natp m)
               (equal s (run-fn p m))
               (implies (exists-some-exitpoint p)
                        (<= m (clock-fn p))))))


(in-theory (disable inv inv-suff))

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

(defthm |pre implies inv|
  (implies (pre s)
           (inv s))
  :hints (("Goal"
           :in-theory (enable exists-some-exitpoint)
           :use ((:instance inv-suff
                            (p s)
                            (m 0))))))

(local
 (defun induction-hint (s n)
   (if (zp n) (list s n)
     (induction-hint (step-fn s) (1- n)))))

(local
 (defthmd step-fn-run-fn-is-run-fn-step-fn
   (equal (step-fn (run-fn s n))
          (run-fn (step-fn s) n))
   :hints (("Goal"
            :induct (induction-hint s n)))))


(defthm |inv implies step-fn inv|
  (implies (and (inv s)
                (not (exitpoint s)))
           (inv (step-fn s)))
  :hints (("Goal"
           :in-theory (disable clock-fn-provide-exitpoint
                               clock-fn-is-natp)
           :do-not '(eliminate-destructors generalize fertilize)
           :use ((:instance (:definition inv))
                 (:instance inv-suff
                            (s (step-fn s))
                            (p (car (inv-witness s)))
                            (m (1+ (mv-nth 1 (inv-witness s)))))))
          ("Subgoal 3"
           :cases ((equal (mv-nth 1 (inv-witness s))
                          (clock-fn (car (inv-witness s))))))
          ("Subgoal 3.1"
           :use ((:instance (:definition exists-some-exitpoint)
                            (s (car (inv-witness s))))
                 (:instance clock-fn-provide-exitpoint
                            (s (car (inv-witness s)))
                            (k (exists-some-exitpoint-witness
                                (car (inv-witness s)))))))
          ("Subgoal 3.2"
           :use ((:instance (:definition exists-some-exitpoint)
                            (s (car (inv-witness s))))
                 (:instance clock-fn-is-natp
                            (s (car (inv-witness s)))
                            (k (exists-some-exitpoint-witness
                                (car (inv-witness s)))))))
          ("Subgoal 4"
           :use ((:instance step-fn-run-fn-is-run-fn-step-fn
                            (s (car (inv-witness s)))
                            (n (mv-nth 1 (inv-witness s))))))))


(defthm |inv and exitpoint implies post|
  (implies (and (inv s)
                (exitpoint s))
           (post s))
  :hints (("Goal"
           :in-theory (disable |clock fn produces postcondition|)
           :use ((:instance (:definition inv))))
          ("Subgoal 2.1"
           :use ((:instance exists-some-exitpoint-suff
                            (s (car (inv-witness s)))
                            (alpha (mv-nth 1 (inv-witness s))))))
          ("Subgoal 2.2"
           :use ((:instance |clock fn produces postcondition|
                            (s (car (inv-witness s)))
                            (n (mv-nth 1 (inv-witness s))))))))