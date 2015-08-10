(in-package "ACL2")

(include-book "clock-total")
(local (include-book "arithmetic/top-with-meta" :dir :system))

(local (in-theory (disable |partial correctness| |termination|)))

(local (include-book "arithmetic/top-with-meta" :dir :system))

(defun-sk exists-some-exitpoint (s)
  (exists alpha  (exitpoint (run-fn s alpha))))

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
                            (s (car (inv-witness s))))))))


(defun m (s)
  (clock-fn s))

(local
 (defthmd run-fn-+-reduction
   (implies (and (natp m)
                 (natp n))
            (equal (run-fn s (+ m n))
                   (run-fn (run-fn s m) n)))
   :hints (("Goal"
            :induct (induction-hint s m)))))

(defthm inv-implies-exitpoint
  (implies (inv s)
           (exitpoint (run-fn s (- (clock-fn (car (inv-witness s)))
                                (mv-nth 1 (inv-witness s))))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance run-fn-+-reduction
                            (s (car (inv-witness s)))
                            (m (mv-nth 1 (inv-witness s)))
                            (n (- (clock-fn (car (inv-witness s)))
                                  (mv-nth 1 (inv-witness s)))))
                 (:instance (:definition inv))
                 (:instance exists-some-exitpoint-suff
                            (s (car (inv-witness s)))
                            (alpha (clock-fn (car (inv-witness s)))))))))

(local
 (defthm m-is-natural
   (implies (inv s)
            (natp (m s)))
   :rule-classes (:rewrite :forward-chaining :type-prescription)
   :hints (("Goal"
            :in-theory (disable clock-fn-is-natp)
            :use ((:instance inv-implies-exitpoint)
                  (:instance clock-fn-is-natp
                             (k (- (clock-fn (car (inv-witness s)))
                                   (mv-nth 1 (inv-witness s))))))))))

(defthm |m is ordinal|
  (implies (inv s)
           (o-p (m s)))
  :hints (("Goal"
           :in-theory (disable m-is-natural)
           :use ((:instance m-is-natural)))))


(local
 (defthm steps-decrease-1
   (implies  (and (not (exitpoint s))
                  (exitpoint (run-fn s n)))
             (<= (clock-fn s)
                 (1+ (clock-fn (step-fn s)))))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance clock-fn-provide-exitpoint
                             (s (step-fn s))
                             (k (1- n)))
                  (:instance clock-fn-is-minimal
                             (k (1+ (clock-fn (step-fn s))))))))))

(local
 (defthm steps-decrease-2
   (implies  (and (not (exitpoint s))
                  (exitpoint (run-fn s n)))
             (<= (1+ (clock-fn (step-fn s)))
                 (clock-fn s)))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance clock-fn-provide-exitpoint
                             (k n))
                  (:instance clock-fn-is-minimal
                             (k (1- (clock-fn s)))
                             (s (step-fn s))))))))

(local
 (defthm steps-decrease
   (implies (and (not (exitpoint s))
                 (exitpoint (run-fn s n)))
            (equal (clock-fn s)
                   (1+ (clock-fn (step-fn s)))))
   :rule-classes nil
   :otf-flg t
   :hints (("Goal"
            :cases ((<= (clock-fn s)
                        (1+ (clock-fn (step-fn s))))))
           ("Subgoal 2"
            :use ((:instance steps-decrease-1)))
           ("Subgoal 1"
            :use ((:instance steps-decrease-2))))))


(local
 (defthm m-decreases
   (implies (and (inv s)
                 (not (exitpoint s)))
            (< (m (step-fn s))
               (m s)))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance (:definition inv))
                  (:instance steps-decrease
                             (n (- (clock-fn (car (inv-witness s)))
                                   (mv-nth 1 (inv-witness s)))))
                  (:instance inv-implies-exitpoint))))))

(defthm |m decreases|
  (implies (and (inv s)
                (not (exitpoint s)))
           (o< (m (step-fn s))
               (m s)))
  :hints (("Goal"
           :in-theory (disable m-is-natural)
           :use ((:instance m-decreases)
                 (:instance m-is-natural
                            (s (step-fn s)))))))


