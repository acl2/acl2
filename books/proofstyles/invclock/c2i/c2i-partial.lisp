(in-package "ACL2")

#|

 c2i-partial.lisp
 ~~~~~~~~~~~~~~

In this book, we show how to do the transformation from clocks to invariants
for partial correctness proofs. Given a clock function proof I define here an
inductive invariant and a measure function that satisfies the requirements for
an inductive invariant proof.

The proof is the same as the original total correctness proofs without the
measure. So this book is essentially not commented. Please look at the
corresponding comments in the total correctness proofs.


|#

(set-match-free-default :once)

(in-theory (disable mv-nth))

;; (defun natp (n)
;;   (and (integerp n)
;;        (<= 0 n)))

;; (defthm natp-compound-recognizer
;;   (iff (natp n)
;;        (and (integerp n)
;;             (<= 0 n)))
;;   :rule-classes :compound-recognizer)

(in-theory (disable natp))

(encapsulate
 (((partial-next *) => *)
  ((partial-pre *) => *)
  ((partial-external *) => *)
  ((partial-post *) => *)
  ((partial-clock-fn *) => *))


 (local (defun partial-next (s) s))

 (defun partial-run (s n) (if (zp n) s (partial-run (partial-next s) (1- n))))

 (local (defun partial-pre (s) (declare (ignore s)) nil))
 (local (defun partial-external (s) (declare (ignore s)) nil))
 (local (defun partial-post (s) (declare (ignore s)) nil))

 (local (defun partial-clock-fn (s) (declare (ignore s)) 0))

 ;; The constrains as usual.

 (defthm partial-clock-fn-is-natp
   (natp (partial-clock-fn s)))

 (defthm partial-pre-is-not-partial-external
   (implies (partial-pre s) (not (partial-external s))))

 (defthm standard-theorem-for-partial-clocks-1
   (implies (and (partial-pre s)
                 (partial-external (partial-run s i)))
            (partial-external (partial-run s (partial-clock-fn s)))))

 (defthm standard-theorem-for-partial-clocks-2
   (implies (and (partial-pre s)
                 (partial-external (partial-run s i)))
            (partial-post (partial-run s (partial-clock-fn s)))))

 (defthm standard-theorem-for-partial-clocks-3
   (implies (and (partial-pre s)
                 (partial-external (partial-run s i)))
            (<= (partial-clock-fn s) i)))

)


;; The same invariant as total correctness incidentally.

(defun-sk exists-partial-pre-state (s)
  (exists (init i)
          (and (partial-pre init)
               (natp i)
               (< i (partial-clock-fn init))
               (equal s (partial-run init i)))))

(local (in-theory (disable exists-partial-pre-state exists-partial-pre-state-suff)))

(defun-sk no-partial-external-partial-run (s)
  (forall i
          (not (partial-external (partial-run s i)))))

(defun partial-inv (s)
  (if (no-partial-external-partial-run s) T
    (and (exists-partial-pre-state s)
         (not (partial-external s)))))


 (local
  (defun partial-run-fn (s n)
    (if (zp n) s (partial-run-fn (partial-next s) (1- n)))))

 (local
  (defthm partial-run-fn-is-partial-run
    (equal (partial-run s n) (partial-run-fn s n))))

 (local
  (in-theory (disable partial-run-fn-is-partial-run)))

 (local
  (defthm partial-clock-fn-is-equal-if-<
    (implies (<= (partial-clock-fn s) 0)
             (equal (partial-clock-fn s) 0))
    :hints (("Goal"
             :in-theory (disable partial-clock-fn-is-natp)
             :use partial-clock-fn-is-natp))))

 (local
  (defthm partial-pre-has-partial-clock->0
    (implies (and (partial-pre s)
                  (partial-external (partial-run s i)))
             (< 0 (partial-clock-fn s)))
    :hints (("Goal"
             :cases ((> (partial-clock-fn s) 0)
                     (= (partial-clock-fn s) 0)))
            ("Subgoal 1"
             :in-theory (disable standard-theorem-for-partial-clocks-1)
             :use standard-theorem-for-partial-clocks-1))))

 (DEFTHM partial-pre-has-partial-inv
   (implies (partial-pre s)
            (partial-inv s))
   :hints (("Goal"
            :cases ((no-partial-external-partial-run s)))
           ("Subgoal 2"
            :use ((:instance exists-partial-pre-state-suff
                             (init s)
                             (i 0))))))

 (local
  (in-theory (disable no-partial-external-partial-run no-partial-external-partial-run-necc)))

 (local
  ;; [Jared] changed this to use arithmetic-3 instead of 2
  (include-book "arithmetic-3/bind-free/top" :dir :system))

 (local
  (defthm partial-run-is-same-for-nfix
    (equal (partial-run s (nfix i))
           (partial-run s i))
    :hints (("Goal"
             :cases ((natp i))
             :in-theory (enable partial-run-fn-is-partial-run)))))

 (local
  (defthm partial-external-to-partial-external-partial-next
    (implies (partial-external (partial-run (partial-next s) i))
             (partial-external (partial-run s (1+ (nfix i)))))))


 (local
  (defthm no-partial-external-to-partial-external-partial-next
    (implies (no-partial-external-partial-run s)
             (not (partial-external (partial-run (partial-next s) i))))
    :hints (("Goal"
             :use ((:instance no-partial-external-partial-run-necc
                              (i (1+ (nfix i)))))))))

 (local
  (defthm no-partial-external-persists
    (implies (no-partial-external-partial-run s)
             (no-partial-external-partial-run (partial-next s)))
    :hints (("Goal"
             :use ((:instance (:definition no-partial-external-partial-run)
                              (s (partial-next s))))))))

 (local
  (defthm partial-run-natp-partial-next
    (implies (and (equal s (partial-run init i))
                  (natp i))
             (equal (partial-next s)
                    (partial-run init (1+ i))))
    :rule-classes nil
    :hints (("Goal"
             :in-theory (enable partial-run-fn-is-partial-run)))))

 (local
  (defthm partial-clock-<-partial-next
    (implies (and (partial-pre p)
                  (natp i)
                  (< i (partial-clock-fn p))
                  (partial-external (partial-run p j))
                  (not (partial-external (partial-run p i)))
                  (not (partial-external (partial-run p (1+ i)))))
             (< (1+ i) (partial-clock-fn p)))
    :rule-classes nil
    :hints (("Goal"
             :cases ((equal (1+ i) (partial-clock-fn p))))
            ("Subgoal 2"
             :in-theory (disable partial-clock-fn-is-natp)
             :use ((:instance partial-clock-fn-is-natp
                              (s p)))))))

 (local
  (defthm partial-clock-fn-<-partial-next-concretized
    (implies (and (partial-pre p)
                  (natp i)
                  (< i (partial-clock-fn p))
                  (not (no-partial-external-partial-run p))
                  (not (partial-external (partial-run p i)))
                  (not (partial-external (partial-run p (1+ i)))))
             (< (1+ i)
                (partial-clock-fn p)))
    :rule-classes nil
    :hints (("Goal"
             :use ((:instance partial-clock-<-partial-next
                              (j (no-partial-external-partial-run-witness p)))
                   (:instance (:definition no-partial-external-partial-run)
                              (s p)))))))

 (local
  (defthm partial-run-+-reduction
    (implies (and (natp i)
                  (natp j))
             (equal (partial-run s (+ i j))
                    (partial-run (partial-run s i) j)))
    :hints (("Goal"
             :in-theory (enable partial-run-fn-is-partial-run)))))

 (local
  (defthm weird-partial-run-+-reduction
    (equal (partial-run (partial-run s i) j)
           (partial-run s (+ (nfix i) (nfix j))))
    :hints (("Goal"
             :cases ((and (natp i) (natp j))
                     (natp i)
                     (natp j))))))

 (local
  (in-theory (disable partial-run-+-reduction)))

 (local
  (defthm no-partial-external-to-no-partial-external
    (implies (not (no-partial-external-partial-run (partial-run p i)))
             (not (no-partial-external-partial-run p)))
    :hints (("Goal"
             :in-theory (disable partial-run-+-reduction)
             :use ((:instance no-partial-external-partial-run-necc
                              (s p)
                              (i (+ (nfix i) (nfix (no-partial-external-partial-run-witness
                                                    (partial-run
                                                     p i))))))
                   (:instance (:definition no-partial-external-partial-run)
                              (s (partial-run p i))))))))

 (DEFTHM partial-inv-implies-partial-next-partial-inv
   (implies (and (partial-inv s)
                 (not (partial-external (partial-next s))))
            (partial-inv (partial-next s)))
   :hints (("Goal"
            :cases ((no-partial-external-partial-run s)))
           ("Subgoal 2"
            :in-theory (disable fix nfix)
            :use ((:instance exists-partial-pre-state-suff
                             (init (mv-nth 0 (exists-partial-pre-state-witness s)))
                             (s (partial-next s))
                             (i (1+ (mv-nth 1 (exists-partial-pre-state-witness s)))))
                  (:instance (:definition exists-partial-pre-state))
                  (:instance partial-run-natp-partial-next
                             (init (mv-nth 0 (exists-partial-pre-state-witness s)))
                             (i (mv-nth 1 (exists-partial-pre-state-witness s))))
                  (:instance partial-clock-fn-<-partial-next-concretized
                             (i (mv-nth 1 (exists-partial-pre-state-witness s)))
                             (p (mv-nth 0 (exists-partial-pre-state-witness s))))
                  (:instance no-partial-external-to-no-partial-external
                             (p (mv-nth 0 (exists-partial-pre-state-witness s)))
                             (i (mv-nth 1 (exists-partial-pre-state-witness s))))))))


 (local
  (in-theory (enable partial-run-+-reduction)))

 (local
  (in-theory (disable weird-partial-run-+-reduction)))

 (local
  (defthm partial-clock-fn-is-the-smallest
    (implies (and (natp i)
                  (< i (partial-clock-fn p))
                  (partial-external (partial-run p (1+ i)))
                  (partial-pre p))
             (equal (partial-clock-fn p) (1+ i)))
    :hints (("Goal"
             :cases ((equal (partial-clock-fn p) (1+ i))
                     (> (partial-clock-fn p) (1+ i))))
            ("Subgoal 2"
             :in-theory (disable partial-clock-fn-is-natp)
             :use ((:instance partial-clock-fn-is-natp
                              (s p)))))))

 (local
  (defthm partial-run-1-is-partial-next
    (equal (partial-run s 1)
           (partial-next s))
    :hints (("Goal"
             :use ((:instance (:definition partial-run)
                              (n 1)))))))

 (local
  (defthm partial-external-to-not-no-partial-external
    (implies (partial-external (partial-next s))
             (not (no-partial-external-partial-run s)))
    :hints (("Goal"
             :use ((:instance no-partial-external-partial-run-necc
                              (i 1)))))))

 (DEFTHM partial-inv-and-partial-external-implies-partial-post
   (implies (and (partial-inv s)
                 (partial-external (partial-next s)))
            (partial-post (partial-next s)))
   :hints (("Goal"
            :do-not '(eliminate-destructors generalize fertilize)
            :in-theory (e/d (exists-partial-pre-state)
                            (partial-run-+-reduction standard-theorem-for-partial-clocks-2
                                             fix nfix))
            :use ((:instance partial-run-natp-partial-next
                             (init (mv-nth 0 (exists-partial-pre-state-witness s)))
                             (i (mv-nth 1 (exists-partial-pre-state-witness s))))
                  (:instance standard-theorem-for-partial-clocks-2
                             (s (mv-nth 0 (exists-partial-pre-state-witness s)))
                             (i (1+ (mv-nth 1 (exists-partial-pre-state-witness s)))))))))
