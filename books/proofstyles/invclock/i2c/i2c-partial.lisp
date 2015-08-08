(in-package "ACL2")

#|

  i2c-partial.lisp
  ~~~~~~~~~~~~~~~~

In this book, I want to prove a partial correctness result using clocks. I
assume that I have been provided a traditional invariant proof showing partial
correctness. In particular, I assume that somebody has provided a function inv,
so that it is an invariant, is implied by the precondition and implies the
postcondition we are interested in. I want to show a result saying something
like this: "If there is a run that takes you from the precondition state to a
return state then the run is invatiably going to be taking you to a "good
state".

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

(encapsulate
 (((pre-partial *) => *)
  ((inv-partial *) => *)
  ((external-partial *) => *)
  ((post-partial *) => *)
  ((next-partial *) => *))

 ;; The constraints here are the same as those for total correctness but
 ;; without the measure.

 (local (defun next-partial (s) s))

 (local (defun pre-partial (s) (declare (ignore s)) nil))
 (local (defun inv-partial (s) (declare (ignore s)) nil))
 (local (defun post-partial (s) (declare (ignore s)) nil))
 (local (defun external-partial (s) (declare (ignore s)) nil))

 (defthm pre-partial-implies-inv-partial
   (implies (pre-partial s) (inv-partial s)))

 (defthm inv-partial-is-not-external-partial
   (implies (inv-partial s)
            (not (external-partial s))))

 (defthm inv-partial-and-external-partial-is-post-partial
   (implies (and (inv-partial s)
                 (external-partial (next-partial s)))
            (post-partial (next-partial s))))

 (defthm inv-partial-is-an-inv-partialariant
   (implies (and (inv-partial s)
                 (not (external-partial (next-partial s))))
            (inv-partial (next-partial s))))

)


(defun run-partial (s n)
  (if (zp n) s (run-partial (next-partial s) (1- n))))

;; Here now I cannot use the constructive definition of clock which I did for
;; total correctness. But notice the beauty of defun-sk. All I need to do is
;; have a defun-sk that works. To be fair I could have used this same defun-sk
;; to do the total correctness. That would have been great for the sake of
;; uniformity, and it is easy to do this proof with them. But I like to get
;; constructive definitions sometimes especially when the recursion is
;; intuitive, and so I did not clutter that other book with this definition. By
;; the way, non-uniformity of our approach was a comment made by John Matthews
;; and Daron Vroon in their ACL2 workshop 2004 paper "Partial Clock Functions
;; in ACL2". My reaction to the comment it that it is possible to do it
;; uniformly, but I prefer things to be more intuitive and I think the other
;; way is more intuitive in this case.

(defun-sk for-all-inv-partial (s i)
  (forall j
          (implies (<= j i)
                   (inv-partial (run-partial s j)))))

(defun-sk exists-run-partial-to-external-partial (s)
  (exists i (and (natp i)
                 (for-all-inv-partial s i)
                 (inv-partial (run-partial s i))
                 (external-partial (next-partial (run-partial s i))))))

(local
 (in-theory (disable exists-run-partial-to-external-partial exists-run-partial-to-external-partial-suff)))


;; Here is the (admittedly stupid) clock function.

(defun clock-partial--fn (s)
  (if (exists-run-partial-to-external-partial s)
      (1+ (exists-run-partial-to-external-partial-witness s))
    0))


;; OK, so we have been able to define the clock function. We need now to prove
;; the partial correctness theorem. We need some helper functions and lemmas.

(local
 (defun find-external-partial (s n)
   (declare (xargs :measure (nfix n)))
   (cond ((or (zp n) (external-partial (next-partial s))) 0)
         (t (1+ (find-external-partial (next-partial s) (1- n)))))))


(local
 ;; [Jared] changed this to use arithmetic-3 instead of 2
 (include-book "arithmetic-3/bind-free/top" :dir :system))

;; Now prove some theorems. These theorems are admittedly more complicated than
;; the total correctness ones.

;; Just saying that we can bring next up before run.

(local
 (defthm run-partial-next-partial-to-next-partial-run-partial
   (equal (run-partial (next-partial s) n)
          (next-partial (run-partial s n)))))

;; Also prove that inv holds for every run upto find-external.

(local
 (defthm inv-partial-to-external-partial
   (implies (inv-partial s)
            (inv-partial (run-partial s (find-external-partial s n))))))


(local
 (defthm inv-partial-upto-find-external-partial
   (implies (and (inv-partial s)
                 (<= j (find-external-partial s n)))
            (inv-partial (run-partial s j)))))

;; Now quantify this and say that forall-inv holds for all states upto an
;; external state.

(local
 (defthm for-all-inv-partial-for-find-external-partial
   (implies (inv-partial s)
            (for-all-inv-partial s (find-external-partial s n)))))

;; Now I need to show that find-external is actually an external state if such
;; an external state exists.

(local
 (defthm external-partial-to-find-external-partial
   (implies (and (external-partial (run-partial s i))
                 (inv-partial s))
            (external-partial (next-partial
                               (run-partial s (find-external-partial s i)))))))

;; And thus exists-to-external must be true in this case.

(local
 (defthm exists-from-find-external-partial
   (implies (and (inv-partial s)
                 (external-partial (run-partial s i)))
            (exists-run-partial-to-external-partial s))
   :hints (("Goal"
            :in-theory (disable for-all-inv-partial for-all-inv-partial-necc)
            :use ((:instance exists-run-partial-to-external-partial-suff
                             (i (find-external-partial s i))))))))


(local
 (defthm exists-to-external-partial
   (implies (exists-run-partial-to-external-partial s)
            (external-partial (run-partial s (clock-partial--fn s))))
   :hints (("Goal"
            :in-theory (enable exists-run-partial-to-external-partial)))))


;; Hence the invariant theorems must give me that running for that many states
;; gives me a good state.

(local
 (defthm exists-to-good
   (implies (exists-run-partial-to-external-partial s)
            (post-partial (run-partial s (clock-partial--fn s))))
   :hints (("Goal"
            :in-theory (enable exists-run-partial-to-external-partial)))))

(local
 (defthm for-all-inv-partial-to-inv-partial
   (implies (and (for-all-inv-partial s i)
                 (<= j i))
            (inv-partial (run-partial s j)))
   :hints (("Goal"
            :in-theory (disable for-all-inv-partial for-all-inv-partial-necc)
            :use ((:instance for-all-inv-partial-necc))))))

;; Now I prove that anything less than external-witness must not be
;; external.

;; Comments: I dont like to have to always reason about this
;; thing. Here is what I mean. If there is a defun-sk then the witness gives me
;; one something that has the property that is desired in defun-sk. But it does
;; not give a minimal (or maximal) witness. Thus every time we do anything with
;; it, I end up having to prove that if there is some witness then there must
;; be a minimal witness for some minimality criterion.

;; TODO (Maybe): Write a macro that creates such a defun-sk with the witness
;; that is minimal according to some user-supplied minimality criterion.

(local
 (defthm inv-partial-persists-till-external-partial
   (implies (and (exists-run-partial-to-external-partial s)
                 (<= i (exists-run-partial-to-external-partial-witness s)))
            (not (external-partial (run-partial s i))))
   :hints (("Goal"
            :in-theory (e/d (exists-run-partial-to-external-partial)
                            (for-all-inv-partial))))))



;; The main theorems exported from this book are marked with CAPITAL
;; DEFTHM.

;; clock function is of course nato. This is obvious.

(DEFTHM clock-partial--is-a-natp
  (natp (clock-partial--fn s))
  :hints (("Goal"
           :in-theory (enable exists-run-partial-to-external-partial
                              exists-run-partial-to-external-partial-suff))))

;; And ti is also the minimal. That is based on all the previous lemma.

(local
 (defthm clock-partial--fn-is-minimum
   (implies (and (inv-partial s)
                 (external-partial (run-partial s i)))
            (<= (clock-partial--fn s) i))
   :hints (("Goal"
            :cases ((not (natp i))))
           ("Subgoal 2"
            :in-theory (e/d (exists-run-partial-to-external-partial)
                            (exists-from-find-external-partial
                             for-all-inv-partial
                             inv-partial-persists-till-external-partial))
            :use ((:instance inv-partial-persists-till-external-partial)
                  (:instance exists-from-find-external-partial))))))


(local
 (in-theory (disable clock-partial--fn)))

;; And the rest of the crap.

(DEFTHM standard-theorem-for-clock-partial-s-1
  (implies (and (pre-partial s)
                (external-partial (run-partial s i)))
           (external-partial (run-partial s (clock-partial--fn s)))))


(DEFTHM standard-theorem-for-clock-partial-s-2
  (implies (and (pre-partial s)
                (external-partial (run-partial s i)))
           (post-partial (run-partial s (clock-partial--fn s)))))


(DEFTHM standard-theorem-for-clock-partial-s-3
  (implies (and (pre-partial s)
                (external-partial (run-partial s i)))
           (<= (clock-partial--fn s) i))
  :hints (("Goal"
           :in-theory (disable clock-partial--fn-is-minimum)
           :use ((:instance clock-partial--fn-is-minimum)))))

