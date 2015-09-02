(in-package "ACL2")

#|

 c2i-total.lisp
 ~~~~~~~~~~~~~~

In this book, we show how to do the transformation from clocks to invariants
for total correctness proofs. Given a clock function proof I define here an
inductive invariant and a measure function that satisfies the requirements for
an inductive invariant proof.

|#

(set-match-free-default :once)

;; For compatibility with e0-ordinal and e0-ord-<. This book predates the
;; introduction of new ordinals in ACL2....:->
(include-book "ordinals/e0-ordinal" :dir :system)
(set-well-founded-relation e0-ord-<)


(local
 (in-theory (disable mv-nth)))

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
 (((total-next *) => *)
  ((total-pre *) => *)
  ((total-external *) => *)
  ((total-post *) => *)
  ((total-clock-fn *) => *))


 (local (defun total-next (s) s))

 (defun total-run (s n) (if (zp n) s (total-run (total-next s) (1- n))))

 (local (defun total-pre (s) (declare (ignore s)) nil))
 (local (defun total-external (s) (declare (ignore s)) nil))
 (local (defun total-post (s) (declare (ignore s)) nil))

 (local (defun total-clock-fn (s) (declare (ignore s)) 0))

 ;; Here are the constraints associated with a clock function proof.

 (defthm total-clock-fn-is-natp
   (natp (total-clock-fn s)))

 (defthm total-pre-is-not-total-external
   (implies (total-pre s) (not (total-external s))))

 (defthm standard-theorem-for-total-clocks-1
   (implies (total-pre s)
            (total-external (total-run s (total-clock-fn s)))))

 (defthm standard-theorem-for-total-clocks-2
   (implies (total-pre s)
            (total-post (total-run s (total-clock-fn s)))))

 (defthm standard-theorem-for-total-clocks-3
   (implies (and (total-pre s)
                 (total-external (total-run s i)))
            (<= (total-clock-fn s) i)))

)

;; Now we show how to produce the invariant.

;; The inductive invariant is simple. It is simply a predicate that recognizes
;; all states reachable from some state satisfying the precondition. Again here
;; is the beauty of defun-sk at work.

(defun-sk exists-total-pre-state (s)
  (exists (init i)
          (and (total-pre init)
               (natp i)
               (< i (total-clock-fn init))
               (equal s (total-run init i)))))

(local (in-theory (disable exists-total-pre-state exists-total-pre-state-suff)))

(defun total-inv (s)
  (and (exists-total-pre-state s)
       (not (total-external s))))

;; I need to introduce a new run function since induction schemes (based on
;; run) are not exported out of encapsulation. And I quickly prove that it is
;; the same as the original run.

(local
 (defun total-run-fn (s n)
   (if (zp n) s (total-run-fn (total-next s) (1- n)))))

(local
 (defthm total-run-fn-is-total-run
   (equal (total-run s n) (total-run-fn s n))))

(local
 (in-theory (disable total-run-fn-is-total-run)))

;; I stupid hack showing that if the clock is <= 0 then it must be 0.

(local
 (defthm total-clock-fn-is-equal-if-<
   (implies (<= (total-clock-fn s) 0)
            (equal (total-clock-fn s) 0))
   :hints (("Goal"
            :in-theory (disable total-clock-fn-is-natp)
            :use total-clock-fn-is-natp))))

;; Then I show that pre must have total clock > 0.

(local
 (defthm total-pre-has-total-clock->0
   (implies (total-pre s)
            (< 0 (total-clock-fn s)))
   :hints (("Goal"
            :cases ((> (total-clock-fn s) 0)
                    (= (total-clock-fn s) 0)))
           ("Subgoal 1"
            :in-theory (disable standard-theorem-for-total-clocks-1)
            :use standard-theorem-for-total-clocks-1))))

;; Of course now it is trivial to show that pre has indeed got the inductive
;; invariant we wanted.

(DEFTHM total-pre-has-total-inv
  (implies (total-pre s)
           (total-inv s))
  :hints (("Goal"
           :use ((:instance exists-total-pre-state-suff
                            (init s)
                            (i 0))))))

(local
 ;; [Jared] changed this to use arithmetic-3 instead of 2
 (include-book "arithmetic-3/bind-free/top" :dir :system))

;; Since I use nfix, I have to know something about removing nfix.

(local
 (defthm total-run-is-same-for-nfix
   (equal (total-run s (nfix i))
          (total-run s i))
   :hints (("Goal"
            :cases ((natp i))
            :in-theory (enable total-run-fn-is-total-run)))))


;; I also show that next of (run s n) is simply (run s (1+ n)). I cannot of
;; course leave this theorem enabled because it will cause looping with the
;; definition of run. But I have it just in case.

(local
 (defthm total-run-natp-total-next
   (implies (and (equal s (total-run init i))
                 (natp i))
            (equal (total-next s)
                   (total-run init (1+ i))))
   :rule-classes nil
   :hints (("Goal"
            :in-theory (enable total-run-fn-is-total-run)))))


;; Now show that if I have not reached the external state the clock function
;; still has some time in it.

(local
 (defthm total-clock-<-total-next
   (implies (and (total-pre p)
                 (natp i)
                 (< i (total-clock-fn p))
                 (not (total-external (total-run p i)))
                 (not (total-external (total-run p (1+ i)))))
            (< (1+ i) (total-clock-fn p)))
   :rule-classes nil
   :hints (("Goal"
            :cases ((equal (1+ i) (total-clock-fn p))))
           ("Subgoal 2"
            :in-theory (disable total-clock-fn-is-natp)
            :use ((:instance total-clock-fn-is-natp
                             (s p)))))))

(local
 (defthm total-clock-fn-<-total-next-concretized
   (implies (and (total-pre p)
                 (natp i)
                 (< i (total-clock-fn p))
                 (not (total-external (total-run p i)))
                 (not (total-external (total-run p (1+ i)))))
            (< (1+ i)
               (total-clock-fn p)))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance total-clock-<-total-next))))))

;; This is a stupid theorem about composition of runs. It is surprising that I
;; did not need it earlier.

(local
 (defthm total-run-+-reduction
   (implies (and (natp i)
                 (natp j))
            (equal (total-run s (+ i j))
                   (total-run (total-run s i) j)))
   :hints (("Goal"
            :in-theory (enable total-run-fn-is-total-run)))))

;; And now throw in the idea that it is the same as running with parameters
;; wrapped with nfix.

(local
 (defthm weird-total-run-+-reduction
   (equal (total-run (total-run s i) j)
          (total-run s (+ (nfix i) (nfix j))))
   :hints (("Goal"
            :cases ((and (natp i) (natp j))
                    (and (not (natp i)) (natp j))
                    (and (natp i) (not (natp j)))
                    (and (not (natp i)) (not (natp j))))))))

(local
 (in-theory (disable total-run-+-reduction)))

;; It is now easy to get to the theorem that shows that the invariants
;; persist.

(DEFTHM total-inv-implies-total-next-total-inv
  (implies (and (total-inv s)
                (not (total-external (total-next s))))
           (total-inv (total-next s)))
  :hints (("Goal"
           :in-theory (disable fix nfix)
           :use ((:instance exists-total-pre-state-suff
                            (init (mv-nth 0 (exists-total-pre-state-witness s)))
                            (s (total-next s))
                            (i (1+ (mv-nth 1 (exists-total-pre-state-witness s)))))
                 (:instance (:definition exists-total-pre-state))
                 (:instance total-run-natp-total-next
                            (init (mv-nth 0 (exists-total-pre-state-witness s)))
                            (i (mv-nth 1 (exists-total-pre-state-witness s))))
                 (:instance total-clock-fn-<-total-next-concretized
                            (i (mv-nth 1 (exists-total-pre-state-witness s)))
                            (p (mv-nth 0 (exists-total-pre-state-witness s))))))))

(local
 (in-theory (enable total-run-+-reduction)))

(local
 (in-theory (disable weird-total-run-+-reduction)))

;; Now let us focus on proving that the clock function is the smallest one
;; taking me to external. This will let me relate the invariant with the
;; postcondition.

(local
 (defthm total-clock-fn-is-the-smallest
   (implies (and (natp i)
                 (< i (total-clock-fn p))
                 (total-external (total-run p (1+ i)))
                 (total-pre p))
            (equal (total-clock-fn p) (1+ i)))
   :hints (("Goal"
            :cases ((equal (total-clock-fn p) (1+ i))
                    (> (total-clock-fn p) (1+ i))))
           ("Subgoal 2"
            :in-theory (disable total-clock-fn-is-natp)
            :use ((:instance total-clock-fn-is-natp
                             (s p)))))))

(local
 (defthm total-run-1-is-total-next
   (equal (total-run s 1)
          (total-next s))
   :hints (("Goal"
            :use ((:instance (:definition total-run)
                             (n 1)))))))

;; And that does it.

(DEFTHM total-inv-and-total-external-implies-total-post
  (implies (and (total-inv s)
                (total-external (total-next s)))
           (total-post (total-next s)))
  :hints (("Goal"
           :in-theory (e/d (exists-total-pre-state)
                           (total-run-+-reduction standard-theorem-for-total-clocks-2
                                                  fix nfix))
           :use ((:instance total-run-natp-total-next
                            (init (mv-nth 0 (exists-total-pre-state-witness s)))
                            (i (mv-nth 1 (exists-total-pre-state-witness s))))
                 (:instance standard-theorem-for-total-clocks-2
                            (s (mv-nth 0 (exists-total-pre-state-witness s))))))))


;; Now comes the difficult part, the measure function and showing that it
;; decreases. The idea is to consider the distance of a state from the first
;; external state.

(defun find-total-external (s n)
  (declare (xargs :measure (nfix n)))
  (if (or (zp n) (total-external s)) 0
    (1+ (find-total-external (total-next s) (1- n)))))

(defun m (s)
  (mv-let (p i)
          (exists-total-pre-state-witness s)
          (find-total-external s (- (total-clock-fn p) i))))

;; Of course the measure is trivially an ordinal.

(local
 (defthm find-total-external-is-natp
   (natp (find-total-external s n))))

(DEFTHM m-is-an-ordinal
  (e0-ordinalp (m s)))

(local
 (in-theory (disable m-is-an-ordinal)))

;; Now why should it decrease? Well consider the situation. We notice that
;; find-external must find the closesnt external state. Thus the one for s and
;; the one for the (next s ) must be exactly the same if in fact s is not
;; external.

(local
 (defthm total-external-implies-find-total-external-total-external
   (implies (and (total-external (total-run s i))
                 (natp i)
                 (natp n)
                 (<= i n))
            (total-external (total-run s (find-total-external s n))))
   :hints (("Goal"
            :in-theory (enable total-run-fn-is-total-run)))))

;; A little hack. This just ensures that I can apply the (- m n) for run.

(local
 (defthm total-run-minus-reduction
   (implies (and (natp i)
                  (natp j)
                  (<= j i))
             (equal (total-run (total-run p j)
                         (- i j))
                    (total-run p i)))
    :rule-classes nil
    :hints (("Goal"
             :in-theory (e/d (natp) (total-run-+-reduction))
             :use ((:instance total-run-+-reduction
                              (s p)
                              (i j)
                              (j (- i j))))))))



;; Now show that if a state is reachable from pre then we can find an external
;; state based on the clock function of the pre-witness.

(local
 (defthm total-inv-states-have-total-external
   (implies (exists-total-pre-state s)
            (total-external (total-run s
                                       (- (total-clock-fn
                                           (mv-nth 0 (exists-total-pre-state-witness s)))
                                          (mv-nth 1 (exists-total-pre-state-witness s))))))
   :hints (("Goal"
            :in-theory (enable exists-total-pre-state)
            :use ((:instance total-run-minus-reduction
                             (i (total-clock-fn
                                 (mv-nth 0 (exists-total-pre-state-witness s))))
                             (j (mv-nth 1 (exists-total-pre-state-witness s)))
                             (p (mv-nth 0 (exists-total-pre-state-witness s)))))))))

;; Now go one extending this to some more arithmetic lemmas.

(local
 (defthm exists-total-pre-state-to-total-clock
   (implies (exists-total-pre-state s)
            (<= 1 (- (total-clock-fn
                      (mv-nth 0 (exists-total-pre-state-witness s)))
                     (mv-nth 1 (exists-total-pre-state-witness s)))))
   :hints (("Goal"
            :in-theory (e/d (exists-total-pre-state) (total-clock-fn-is-natp))
            :use ((:instance total-clock-fn-is-natp
                             (s (mv-nth 0 (exists-total-pre-state-witness s)))))))))

(local
 (defthm exists-total-pre-state-to-total-clock-2
   (implies (exists-total-pre-state s)
            (natp (- (total-clock-fn
                      (mv-nth 0 (exists-total-pre-state-witness s)))
                     (mv-nth 1 (exists-total-pre-state-witness s)))))
   :rule-classes nil
   :hints (("Goal"
            :in-theory (e/d (natp exists-total-pre-state) (total-clock-fn-is-natp))
            :use ((:instance total-clock-fn-is-natp
                             (s (mv-nth 0 (exists-total-pre-state-witness s)))))))))

(local
 (defthm exists-total-pre-state-to-total-clock-3
   (implies (exists-total-pre-state s)
            (natp (1- (- (total-clock-fn
                          (mv-nth 0 (exists-total-pre-state-witness s)))
                         (mv-nth 1 (exists-total-pre-state-witness s))))))
   :rule-classes nil
   :hints (("Goal"
            :in-theory (e/d (natp)
                            (total-clock-fn-is-natp
                             exists-total-pre-state-to-total-clock))
            :use ((:instance exists-total-pre-state-to-total-clock)
                  (:instance total-clock-fn-is-natp
                             (s (mv-nth 0 (exists-total-pre-state-witness s))))
                  (:instance exists-total-pre-state-to-total-clock-2))))))

;; So finally we learnt that (1- (- (clock wit) j)) is a natp. Now we want to
;; specify that before this, there is no external state. So we define
;; no-external state below.

(local
 (defun no-total-external-state (s n)
   (declare (xargs :measure (nfix n)))
   (cond ((zp n) (not (total-external s)))
         ((total-external s) nil)
         (t (no-total-external-state (total-next s) (1- n))))))

(local
  (defthm no-total-external-state-to<=
    (implies (and (no-total-external-state s n)
                  (natp i)
                  (natp n)
                  (<= i n))
             (no-total-external-state s i))))

(local
 (defthm no-total-external-state-to-no-total-external
   (implies (and (no-total-external-state s n)
                 (not (total-external s)))
            (not (total-external (total-run s n))))
   :hints (("Goal"
            :in-theory (enable total-run-fn-is-total-run)))))

(local
 (defthm no-total-external-to-<=-concretized
   (implies (and (no-total-external-state s n)
                 (natp i)
                 (natp n)
                 (<= i n))
            (not (total-external (total-run s i))))
   :rule-classes nil))


;; Indeed my no-externalstate must be correct by the above theorems. Now then
;; if nothing exists for n steps and something exists for n+1 steps then
;; find-external must return 1+ n.
(local
 (defthm no-total-external-extate-to-find-total-external
   (implies (and (no-total-external-state s n)
                 (total-external (total-run s (1+ n)))
                 (natp j)
                 (<= (1+ n) j)
                 (natp n))
            (equal (find-total-external s j)
                   (1+ n)))
   :hints (("Goal"
            :do-not '(generalize))
           ("Subgoal *1/6.1"
            :in-theory (enable natp)))))

;; I still have a little more work to go. I want to say that if I have proved
;; that for any i <= n (external s i) does not hold then I want to infer
;; no-external. To get there, I will simply define the external witness.

(local
 (defun no-total-external-witness (s n)
   (declare (xargs :measure (nfix n)))
   (if (zp n) 0
     (if (total-external s) 0
       (1+ (no-total-external-witness (total-next s) (1- n)))))))

(local
 (defthm no-total-external-witness-<=n
   (implies (natp n)
            (<= (no-total-external-witness s n) n))
   :rule-classes nil))

(local
 (defthm no-total-external-witness-is-natp
   (natp (no-total-external-witness s n))
   :rule-classes nil))

(local
 (defthm no-total-external-witness-implies-no-total-external
   (implies (not (total-external (total-run s (no-total-external-witness s n))))
            (no-total-external-state s n))))

;; And I have achieved that goal. So I now show that starting from pre until
;; clock function there is no external state.

(local
 (defthm total-pre-implies-no-total-external
   (implies (and (total-pre p)
                 (natp i)
                 (< i (total-clock-fn p)))
            (no-total-external-state p i))
   :hints (("Goal"
            :cases ((total-external (total-run p (no-total-external-witness p i)))))
           ("Subgoal 1"
            :in-theory (disable standard-theorem-for-total-clocks-3)
            :use ((:instance standard-theorem-for-total-clocks-3
                             (i (no-total-external-witness p i))
                             (s p))
                  (:instance no-total-external-witness-is-natp
                             (s p)
                             (n i))
                  (:instance no-total-external-witness-<=n
                             (s p)
                             (n i)))))))

;; Thus it must be that no-external holds for all the states upto the requisite
;; value.

(local
 (defthm no-total-external-to-no-total-external-total-run
   (implies (and (natp i)
                 (natp j)
                 (<= j i)
                 (no-total-external-state p i))
            (no-total-external-state (total-run p j) (- i j)))
   :hints (("Goal"
            :in-theory (e/d (natp) (total-run-+-reduction
                                    no-total-external-witness-implies-no-total-external))
            :use ((:instance no-total-external-witness-implies-no-total-external
                             (s (total-run p j))
                             (n (- i j)))
                  (:instance total-run-minus-reduction
                             (i (no-total-external-witness (total-run p j) (- i j)))
                             (j (no-total-external-witness
                                 (total-run p j)
                                 (- i j))))
                  (:instance no-total-external-witness-<=n
                             (s (total-run p j))
                             (n (- i j)))
                  (:instance no-total-external-witness-is-natp
                             (s (total-run p j))
                             (n (- i j)))
                  (:instance no-total-external-to-<=-concretized
                             (n i)
                             (s p)
                             (i (+ j (no-total-external-witness (total-run p j) (- i j)))))
                  (:instance total-run-+-reduction
                             (s p)
                             (i j)
                             (j (no-total-external-witness (total-run p j) (- i j)))))))))

(local
 (defthm total-pre-to-no-total-external-total-run
   (implies (and (total-pre p)
                 (natp i)
                 (< i (total-clock-fn p))
                 (natp j)
                 (<= j i))
            (no-total-external-state (total-run p j) (- i j)))
   :rule-classes nil))

;; And therefore for any state satisfying inv no-external holds until we have
;; run for the requisite steps.

(local
 (defthm total-inv-to-no-total-external
   (implies (exists-total-pre-state s)
            (no-total-external-state s
                                     (1-
                                      (- (total-clock-fn (mv-nth 0 (exists-total-pre-state-witness
                                                                    s)))
                                         (mv-nth 1 (exists-total-pre-state-witness s))))))
   :hints (("Goal"
            :in-theory (e/d (exists-total-pre-state) (total-clock-fn-is-natp
                                                      total-pre-has-total-clock->0))
            :use ((:instance total-pre-to-no-total-external-total-run
                             (p (mv-nth 0 (exists-total-pre-state-witness s)))
                             (i (1-
                                 (total-clock-fn
                                  (mv-nth 0
                                          (exists-total-pre-state-witness
                                           s)))))
                             (j (mv-nth 1 (exists-total-pre-state-witness s))))
                  (:instance total-clock-fn-is-natp
                             (s (mv-nth 0 (exists-total-pre-state-witness s))))
                  (:instance total-pre-has-total-clock->0
                             (s (mv-nth 0 (exists-total-pre-state-witness s)))))))))


;; And more hacks. I need to get to i+2. Notice that most of these hacks are
;; because there is no good book to support defun-sk and/or good rewrite rules
;; in the context in which I am working.

(local
 (defthm no-total-external-implies-+-2
   (implies (and (no-total-external-state p i)
                 (natp i)
                 (total-external (total-run p j))
                 (not (total-external (total-run p (1+ i)))))
            (>= j (+ i 2)))
   :hints (("Goal"
            :in-theory (enable total-run-fn-is-total-run)))))

(local
 (defthm no-total-external-implies-+-2-concretized
   (implies (and (total-pre p)
                 (natp i)
                 (< i (total-clock-fn p))
                 (not (total-external (total-run p (1+ i)))))
            (>= (total-clock-fn p) (+ i 2)))
   :hints (("Goal"
            :in-theory (disable no-total-external-implies-+-2)
            :use ((:instance no-total-external-implies-+-2
                             (j (total-clock-fn p))))))))

;; So 1- clock must ne natp. That is clock >= 1 for pre states.

(local
 (defthm total-pre-implies-total-clock-natp
   (implies (total-pre s)
            (natp (1- (total-clock-fn s))))
   :rule-classes nil
   :hints (("Goal"
            :in-theory (e/d (natp) (total-pre-has-total-clock->0
                                    total-clock-fn-is-natp))
            :use ((:instance total-clock-fn-is-natp)
                  (:instance  total-pre-has-total-clock->0))))))

;; Finally everything starts gelling together. I now know that m is the same as
;; subtracting the clock of the witness from whatever we have already run to.

(local
 ;; Jared added this when switching to arithmetic-3 to avoid loops in
 ;; the next theorem.
 (in-theory (disable prefer-positive-addends-<)))

(local
 (defthm find-total-external-for-state
   (implies (total-inv s)
            (equal (m s)
                   (- (total-clock-fn (mv-nth 0 (exists-total-pre-state-witness s)))
                      (mv-nth 1 (exists-total-pre-state-witness s)))))
   :hints (("Goal"
            :in-theory (e/d (exists-total-pre-state)
                            (no-total-external-extate-to-find-total-external
                             no-total-external-state
                             total-clock-fn-is-natp))
            :use ((:instance total-clock-fn-is-natp
                             (s (mv-nth 0 (exists-total-pre-state-witness s))))
                  (:instance exists-total-pre-state-to-total-clock-3)
                  (:instance exists-total-pre-state-to-total-clock-2)
                  (:instance total-pre-implies-total-clock-natp
                             (s (mv-nth 0 (exists-total-pre-state-witness s))))
                  (:instance total-pre-to-no-total-external-total-run
                             (p (mv-nth 0 (exists-total-pre-state-witness s)))
                             (i (1- (total-clock-fn
                                     (mv-nth 0
                                             (exists-total-pre-state-witness
                                              s)))))
                             (j (mv-nth 1 (exists-total-pre-state-witness s))))
                  (:instance total-run-minus-reduction
                             (p (mv-nth 0 (exists-total-pre-state-witness s)))
                             (i (total-clock-fn
                                 (mv-nth 0 (exists-total-pre-state-witness
                                            s))))
                             (j (mv-nth 1 (exists-total-pre-state-witness s))))
                  (:instance no-total-external-extate-to-find-total-external
                             (j (- (total-clock-fn
                                    (mv-nth 0
                                            (exists-total-pre-state-witness
                                             s)))
                                   (mv-nth 1 (exists-total-pre-state-witness s))))
                             (n (1-
                                 (- (total-clock-fn
                                     (mv-nth 0
                                             (exists-total-pre-state-witness
                                              s)))
                                    (mv-nth 1
                                            (exists-total-pre-state-witness s)))))))))))


;; Now is it the same for next? Let us prove that. For next, I will run 1 less
;; time so I have this forced rewrite rule.

(local
 (defthm natp-to-total-run-s-n
   (implies (force (natp (1- n)))
            (equal (total-run (total-next s) (1- n))
                   (total-run s n)))
   :hints (("Goal"
            :in-theory (enable total-run-fn-is-total-run)))))

;; For the next guy the external is 1 less.

(local
 (defthm total-inv-states-have-total-external-total-next
   (implies (and (exists-total-pre-state s)
                 (not (total-external s)))
            (total-external
             (total-run (total-next s)
                        (1-
                         (- (total-clock-fn
                             (mv-nth 0 (exists-total-pre-state-witness s)))
                            (mv-nth 1 (exists-total-pre-state-witness s)))))))
   :rule-classes nil
   :hints (("Goal"
            :in-theory (disable total-inv-states-have-total-external)
            :use total-inv-states-have-total-external)
           ("[1]Goal"
            :use exists-total-pre-state-to-total-clock-3))))

(local
 (in-theory (disable natp-to-total-run-s-n)))

;; But the steps from witness is 1 more. TO justify that we add more arithmetic
;; about the arguments returned by exists-pre-state.

(local
 (defthm exists-total-pre-state-to-witness
   (implies (and (exists-total-pre-state s)
                 (natp i))
            (equal (total-run s i)
                   (total-run (mv-nth 0 (exists-total-pre-state-witness s))
                              (+ (mv-nth 1 (exists-total-pre-state-witness s)) i))))
   :rule-classes nil
   :hints (("Goal"
            :in-theory (e/d (exists-total-pre-state) (total-run-+-reduction))
            :use ((:instance total-run-+-reduction
                             (i (mv-nth 1 (exists-total-pre-state-witness s)))
                             (j i)
                             (s (mv-nth 0
                                        (exists-total-pre-state-witness s)))))))))

(local
 (defthm exists-total-pre-state-to-witness-2
   (implies (and (exists-total-pre-state s)
                 (not (total-external s))
                 (exists-total-pre-state (total-next s)))
            (total-external
             (total-run
              (mv-nth 0 (exists-total-pre-state-witness (total-next s)))
              (+ (1- (- (total-clock-fn
                         (mv-nth 0
                                 (exists-total-pre-state-witness
                                  s)))
                        (mv-nth 1 (exists-total-pre-state-witness s))))
                 (mv-nth 1 (exists-total-pre-state-witness (total-next s)))))))
   :rule-classes nil
   :hints (("Goal"
            :in-theory (disable total-run)
            :use ((:instance total-inv-states-have-total-external-total-next)
                  (:instance exists-total-pre-state-to-total-clock-3)
                  (:instance
                   exists-total-pre-state-to-witness
                   (s (total-next s))
                   (i (1- (- (total-clock-fn
                              (mv-nth 0
                                      (exists-total-pre-state-witness
                                       s)))
                             (mv-nth 1 (exists-total-pre-state-witness s)))))))))))

(local
 (defthm total-clock-fn-is-less-1
   (implies (and (exists-total-pre-state s)
                 (not (total-external s))
                 (exists-total-pre-state (total-next s)))
            (<=  (total-clock-fn
                  (mv-nth 0 (exists-total-pre-state-witness (total-next s))))
                 (+ (1- (- (total-clock-fn
                            (mv-nth 0 (exists-total-pre-state-witness s)))
                           (mv-nth 1 (exists-total-pre-state-witness s))))
                    (mv-nth 1 (exists-total-pre-state-witness (total-next s))))))
   :rule-classes nil
   :hints (("Goal"
            :in-theory (e/d (natp) (standard-theorem-for-total-clocks-3
                                    total-run))
            :use ((:instance standard-theorem-for-total-clocks-3
                             (s (mv-nth 0 (exists-total-pre-state-witness s)))
                             (i (+ (1- (- (total-clock-fn
                                           (mv-nth 0 (exists-total-pre-state-witness
                                                      s)))
                                          (mv-nth 1 (exists-total-pre-state-witness
                                                     s))))
                                   (mv-nth 1 (exists-total-pre-state-witness
                                              (total-next s))))))
                  (:instance (:definition exists-total-pre-state)
                             (s (total-next s)))
                  (:instance exists-total-pre-state-to-witness-2)
                  (:instance exists-total-pre-state-to-total-clock-3))))))

;; And yes running from (next s) is simply 1 more than running from s.

(local
 (defthm natp-to-total-run-s-n-2
   (implies (force (natp n))
            (equal (total-run s (1+ n))
                   (total-run (total-next s) n)))))

;; The theorem below is just a reincarnation for (next s) of an analogous
;; theorem for s. See above.

(local
 (defthm total-inv-states-have-total-external-total-previous
   (implies (exists-total-pre-state (total-next s))
            (total-external
             (total-run
              s
              (1+
               (- (total-clock-fn
                   (mv-nth 0
                           (exists-total-pre-state-witness
                            (total-next s))))
                  (mv-nth 1 (exists-total-pre-state-witness (total-next s))))))))
   :hints (("Goal"
            :in-theory (e/d (natp exists-total-pre-state) (total-clock-fn-is-natp))
            :use ((:instance total-run-minus-reduction
                             (p (mv-nth 0
                                        (exists-total-pre-state-witness
                                         (total-next s))))
                             (i (total-clock-fn
                                 (mv-nth 0 (exists-total-pre-state-witness
                                            (total-next s)))))
                             (j (mv-nth 1 (exists-total-pre-state-witness
                                           (total-next s)))))
                  (:instance total-clock-fn-is-natp
                             (s (mv-nth 0
                                        (exists-total-pre-state-witness
                                         (total-next s))))))))))

(local
 (in-theory (disable natp-to-total-run-s-n-2)))

;; Now of course I have just proven that if pre-state holds for s, then it also
;; holds for (next s).

(local
 (defthm exists-total-pre-state-to-witness-3
   (implies (and (exists-total-pre-state s)
                 (not (total-external s))
                 (exists-total-pre-state (total-next s)))
            (total-external
             (total-run
              (mv-nth 0 (exists-total-pre-state-witness s))
              (+ (1+ (- (total-clock-fn
                         (mv-nth 0
                                 (exists-total-pre-state-witness
                                  (total-next s))))
                        (mv-nth 1 (exists-total-pre-state-witness (total-next s)))))
                 (mv-nth 1 (exists-total-pre-state-witness s))))))
   :rule-classes nil
   :hints (("Goal"
            :in-theory (disable total-run)
            :use ((:instance total-inv-states-have-total-external-total-previous)
                  (:instance exists-total-pre-state-to-total-clock-3)
                  (:instance exists-total-pre-state-to-witness
                             (s s)
                             (i (1+
                                 (- (total-clock-fn
                                     (mv-nth 0
                                             (exists-total-pre-state-witness
                                              (total-next s))))
                                    (mv-nth 1 (exists-total-pre-state-witness
                                               (total-next s))))))))))))

;; Now can we start justifying that the witness of (exists-pre-state s) and
;; that of (exists-pre-state (next s)) will provide the same value. Of course
;; we can! To do this I will try the model of showing x=y by showing x<=y and
;; x>=y.

(local
 (defthm total-clock-fn-is-less-2
   (implies (and (exists-total-pre-state s)
                 (not (total-external s))
                 (exists-total-pre-state (total-next s)))
            (<=  (total-clock-fn (mv-nth 0 (exists-total-pre-state-witness s)))
                 (+ (1+ (- (total-clock-fn
                             (mv-nth 0 (exists-total-pre-state-witness (total-next s))))
                            (mv-nth 1 (exists-total-pre-state-witness (total-next s)))))
                     (mv-nth 1 (exists-total-pre-state-witness s)))))
    :rule-classes nil
    :hints (("Goal"
             :in-theory (e/d (natp) (standard-theorem-for-total-clocks-3
                                     total-run))
             :use ((:instance standard-theorem-for-total-clocks-3
                              (s (mv-nth 0 (exists-total-pre-state-witness s)))
                              (i (+ (1+ (- (total-clock-fn
                                            (mv-nth 0 (exists-total-pre-state-witness
                                                       (total-next s))))
                                           (mv-nth 1 (exists-total-pre-state-witness
                                                      (total-next s)))))
                                    (mv-nth 1 (exists-total-pre-state-witness s)))))
                   (:instance (:definition exists-total-pre-state))
                   (:instance exists-total-pre-state-to-witness-3)
                   (:instance exists-total-pre-state-to-total-clock-3))))))

;; Yes. And then it is done.

(local
 (defthm total-clock-fn-is-same
   (implies (and (exists-total-pre-state s)
                 (not (total-external s))
                 (exists-total-pre-state (total-next s)))
            (equal (- (total-clock-fn (mv-nth 0 (exists-total-pre-state-witness (total-next s))))
                      (mv-nth 1 (exists-total-pre-state-witness (total-next s))))
                   (1- (- (total-clock-fn (mv-nth 0 (exists-total-pre-state-witness s)))
                          (mv-nth 1 (exists-total-pre-state-witness s))))))
   :hints (("Goal"
            :use ((:instance total-clock-fn-is-less-1)
                  (:instance total-clock-fn-is-less-2))))))


;; I now also consider the theorem that m is a natural. It is not important to
;; get it out, but I want to disable m soon.

(local
 (defthm m-is-a-natp
   (natp (m s))
   :rule-classes nil))

(local
 (in-theory (disable total-inv m)))

;; Now this actually shows that the m of (next s) is the same as (m s).

(local
 (defthm total-inv-implies-m-total-next
   (implies (and (total-inv s)
                 (not (total-external (total-next s))))
            (equal (m (total-next s))
                   (1- (- (total-clock-fn
                           (mv-nth 0 (exists-total-pre-state-witness s)))
                          (mv-nth 1 (exists-total-pre-state-witness s))))))
   :hints (("Goal"
            :in-theory (disable total-clock-fn-is-same
                                total-inv-implies-total-next-total-inv)
            :use ((:instance total-inv-implies-total-next-total-inv)
                  (:instance (:definition total-inv)
                             (s (total-next s)))
                  (:instance (:definition total-inv)
                             (s s))
                  (:instance total-clock-fn-is-same)
                  (:instance find-total-external-for-state
                             (s (total-next s))))))))

;; And therefore we are done.

(DEFTHM internal-steps-decrease-m
  (implies (and (total-inv s)
                (not (total-external (total-next s))))
           (e0-ord-< (m (total-next s))
                     (m s)))
  :hints (("Goal"
           :use ((:instance m-is-a-natp
                            (s s))
                 (:instance m-is-a-natp
                            (s (total-next s)))))))


