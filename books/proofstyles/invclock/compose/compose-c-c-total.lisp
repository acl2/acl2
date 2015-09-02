(in-package "ACL2")

#|

 compose-cc-partial.lisp
 ~~~~~~~~~~~~~~~~~~~~~~~

In this book we show the composition result for total correctness. The proof is
obvious, basically showing that runs compose ober their second argument. I am
doing only for clocks without loss of generality, since invariants can be shown
to be equivalent to clocks by our previous result. Given a total correctness
proof in terms of clock, you can functionally instantiate the capital DEFTHMS
in this book to get the composition of proofs.

|#

(set-match-free-default :once)

;; (defun natp (n)
;;   (and (integerp n)
;;        (<= 0 n)))

;; (defthm natp-compound-recognizer
;;   (iff (natp n)
;;        (and (integerp n)
;;             (<= 0 n)))
;;   :rule-classes :compound-recognizer)

(in-theory (disable natp))


(include-book "ordinals/e0-ordinal" :dir :system)
(set-well-founded-relation e0-ord-<)

(encapsulate
 (((next *) => *)
  ((pre-1 *) => *)
  ((pre-2 *) => *)
  ((post-1 *) => *)
  ((post-2 *) => *)
  ((clock-1 *) => *)
  ((clock-2 *) => *)
  ((c-witness * *) => *)
  ((external-1 *) => *)
  ((external-2 *) => *))

 (local (defun next (s) s))

 (defun run (s n) (if (zp n) s (run (next s) (1- n))))

 (local (defun pre-1 (s) (declare (ignore s)) nil))
 (local (defun pre-2 (s) (declare (ignore s)) nil))
 (local (defun post-1 (s) (declare (ignore s)) nil))
 (local (defun post-2 (s) (declare (ignore s)) nil))
 (local (defun external-1 (s) (declare (ignore s)) nil))
 (local (defun external-2 (s) (declare (ignore s)) nil))

 (local (defun c-witness (s i) (declare (ignore s i)) 0))

 (local (defun clock-1 (s) (declare (ignore s)) 0))
 (local (defun clock-2 (s) (declare (ignore s)) 0))


 (defthm clock-1-is-natp
   (natp (clock-1 s)))

 (defthm clock-2-is-natp
   (natp (clock-2 s)))

 (defthm standard-theorem-about-clocks-11
   (implies (pre-1 s)
            (external-1 (run s (clock-1 s)))))

 (defthm standard-theorem-about-clocks-12
   (implies (pre-1 s)
            (post-1 (run s (clock-1 s)))))

 (defthm standard-theorem-about-clocks-13
   (implies (and (pre-1 s)
                 (external-1 (run s i)))
            (<= (clock-1 s) i)))

 (defthm standard-theorem-about-clocks-21
   (implies (pre-2 s)
            (external-2 (run s (clock-2 s)))))

 (defthm standard-theorem-about-clocks-22
   (implies (pre-2 s)
            (post-2 (run s (clock-2 s)))))


 (defthm standard-theorem-about-clocks-23
   (implies (and (pre-2 s)
                 (external-2 (run s i)))
            (<= (clock-2 s) i)))

 (defthm composition-1
   (implies (and (post-1 s)
                 (external-1 s))
            (pre-2 s)))

 (defthm composition-2
   (implies (and (pre-1 s)
                 (external-2 (run s j)))
            (external-1 (run s (c-witness s j)))))

 (defthm composition-3
   (implies (and (pre-1 s)
                 (external-2 (run s j)))
            (> (nfix j) (c-witness s j))))

 (defthm c-witness-is-natp
   (natp (c-witness s j)))

)

;; We now produce the clock function for the composition.

(encapsulate
 (((clock-fn *) => *))

 (local
  ;; [Jared] changed this to use arithmetic-3 instead of 2
  (include-book "arithmetic-3/bind-free/top" :dir :system))

 (local
  (defun clock-fn (s)
    (+ (clock-1 s) (clock-2 (run s (clock-1 s))))))

 (local
  (defun run-fn (s n)
    (if (zp n) s (run-fn (next s) (1- n)))))

 (local
  (defthm run-fn-is-run
    (equal (run s n)
           (run-fn s n))))

 (local
  (in-theory (disable run-fn-is-run)))

 (local
  (defthm run-fn-+-reduction
    (implies (and (natp i)
                  (natp j))
             (equal (run-fn s (+ i j))
                    (run-fn (run-fn s i) j)))))

 (local
  (defthm run-+-reduction
    (implies (and (natp i)
                  (natp j))
             (equal (run s (+ i j))
                    (run (run s i) j)))
    :hints (("Goal"
             :in-theory (enable run-fn-is-run)))))

 (local
  (defthm run-minus-reduction
    (implies (and (natp i)
                  (natp j)
                  (<= i j))
             (equal (run (run s i) (- j i))
                    (run s j)))
    :hints (("Goal"
             :in-theory (e/d (natp) (run-+-reduction))
             :use ((:instance run-+-reduction
                              (i i)
                              (j (- j i))))))))


 (DEFTHM clock-fn-is-natp
   (natp (clock-fn s))
   :hints (("Goal"
            :in-theory (disable clock-1-is-natp clock-2-is-natp)
            :use ((:instance clock-1-is-natp)
                  (:instance clock-2-is-natp
                             (s (run s (clock-1 s))))))))

 (local
  (defthm clock-smaller-than-witnes
    (implies (and (pre-1 s)
                  (external-2 (run s j)))
             (<= (clock-1 s) (c-witness s j)))))

 (local
  (defthm run-same-for-nfix
    (equal (run s (nfix i))
           (run s i))
    :rule-classes nil))

 (local
  (defthm run-from-clock-gives-j
    (implies (and (pre-1 s)
                  (external-2 (run s j)))
             (equal (run (run s (clock-1 s))
                         (- (nfix j) (clock-1 s)))
                    (run s j)))
    :rule-classes nil
    :hints (("Goal"
             :in-theory (disable nfix fix composition-3
                                 standard-theorem-about-clocks-13
                                 clock-smaller-than-witnes
                                 run-minus-reduction)
             :use ((:instance run-minus-reduction
                              (i (clock-1 s))
                              (j (nfix j)))
                   (:instance run-same-for-nfix
                              (i j))
                   (:instance clock-smaller-than-witnes)
                   (:instance composition-3))))))

 (DEFTHM standard-theorem-for-clocks-1
   (implies (pre-1 s)
            (external-2 (run s (clock-fn s))))
   :hints (("Goal"
            :do-not '(generalize fertilize)
            :in-theory (disable standard-theorem-about-clocks-11
                                standard-theorem-about-clocks-12
                                fix nfix
                                standard-theorem-about-clocks-21
                                composition-1
                                composition-2)
            :use ((:instance composition-2)
                  (:instance standard-theorem-about-clocks-11)
                  (:instance standard-theorem-about-clocks-12)
                  (:instance composition-1
                             (s (run s (clock-1 s))))
                  (:instance run-from-clock-gives-j)
                  (:instance standard-theorem-about-clocks-21
                             (s (run s (clock-1 s))))))))


 (DEFTHM standard-theorem-for-clocks-2
   (implies (pre-1 s)
            (post-2 (run s (clock-fn s))))
   :hints (("Goal"
            :do-not '(generalize fertilize)
            :in-theory (disable standard-theorem-about-clocks-11
                                standard-theorem-about-clocks-12
                                fix nfix
                                standard-theorem-about-clocks-22
                                composition-1
                                composition-2)
            :use ((:instance composition-2)
                  (:instance standard-theorem-about-clocks-11)
                  (:instance standard-theorem-about-clocks-12)
                  (:instance composition-1
                             (s (run s (clock-1 s))))
                  (:instance run-from-clock-gives-j)
                  (:instance standard-theorem-about-clocks-22
                             (s (run s (clock-1 s))))))))


 (local
  (defthm clock-smaller-than-j
    (implies (and (pre-1 s)
                  (external-2 (run s j)))
             (< (clock-1 s) (nfix j)))
    :hints (("Goal"
             :in-theory (disable composition-3
                                 fix nfix
                                 standard-theorem-about-clocks-13
                                 clock-smaller-than-witnes)
             :use ((:instance clock-smaller-than-witnes)
                   (:instance composition-3))))))

 (local
  (defthm nfix-is-identity
    (implies (natp x)
             (equal (nfix x) x))
    :hints (("Goal"
             :in-theory (enable natp)))))

 (local
  (defthm fix-is-identity
    (implies (natp x)
             (equal (fix x) x))
    :hints (("Goal"
             :in-theory (enable natp)))))

 (local
  (defthm clock-fn-is-least
    (implies (and (natp j)
                  (external-2 (run s j))
                  (pre-1 s))
             (<= (clock-fn s) j))
    :hints (("Goal"
             :do-not '(generalize fertilize)
             :in-theory (disable standard-theorem-about-clocks-11
                                 standard-theorem-about-clocks-12
                                 fix nfix
                                 standard-theorem-about-clocks-21
                                 standard-theorem-about-clocks-23
                                 composition-1
                                 composition-2)
             :use ((:instance composition-2)
                   (:instance standard-theorem-about-clocks-11)
                   (:instance standard-theorem-about-clocks-12)
                   (:instance composition-1
                              (s (run s (clock-1 s))))
                   (:instance run-from-clock-gives-j)
                   (:instance standard-theorem-about-clocks-21
                              (s (run s (clock-1 s))))
                   (:instance standard-theorem-about-clocks-23
                              (s (run s (clock-1 s)))
                              (i (- (nfix j) (clock-1 s)))))))))

 (local
  (defthm nfix-0
    (implies (not (natp j))
             (equal (nfix j) 0))))

 (local
  (defthm natp-or-not-external
    (implies (and (equal j 0)
                  (natp x))
             (<= j x))
    :hints (("Goal"
             :in-theory (enable natp)))))

 (local
  (defthm natp-implies-no-c-witness
    (implies (and (not (natp j))
                  (pre-1 s))
             (not (external-2 (run s j))))
    :hints (("Goal"
             :in-theory (disable composition-3)
             :use composition-3))))

 (local
  (in-theory (disable clock-fn)))

 (DEFTHM standard-theorem-for-clocks-3
   (implies (and (pre-1 s)
                 (external-2 (run s j)))
            (<= (clock-fn s) j))
   :hints (("Goal"
            :in-theory (disable run)
            :cases ((natp j)))))

)
