(in-package "ACL2")

#|

  i2c-total.lisp
  ~~~~~~~~~~~~~~

In this book, we discuss how to transform invariant proofs guaranteeing total
correctness into clock function proofs. We assume that that invariants are
strong enough to guarantee total correctness.

We assume that a program is specified by a function called step, and three
predicates pre, external, and post. The goal correctness criterion of the
program can be informally stated as: If the program starts from a state
satisfies pre, then it will eventually reach an external state (think about
the external state as the "ending state" of the program) and in that state
post holds.

How do we normally prove this using invariants? The key idea is to define a
function inv with the following properties:

1. inv holds for every pre state.
2. if inv holds in a state, then inv holds in the next state.
3. if invholds in an external state, then post holds in the same state.
4. if inv holds in a state, then there is an external state reachable from that
state.

We note that the notion of such a reachability in ACL2 is normally specified by
an ordinal measure that decreases along the path that takes an inv state to an
external state.


It is clear, then, that if we can prove these 4 points, then we have proved
total correctness of the program.

A clock function proof goes like this: We define a function called "clock" that
returns a natural number. The function tells us, given a state s satisfying p,
how many times we need to step the machine in order to get to a state that
satisfies external and post.

In this book, we will show that given an invariant proof of total correctness
of an arbitrary sequential program, we can mechanically produce a clock
function proof. The same technique can be extended (I think) to multithreaded
programs,. but I have not done that as yet.

|#

(set-match-free-default :once)

;; For compatibility with e0-ordinal and e0-ord-<. This book predates the
;; introduction of new ordinals in ACL2....:->
(include-book "ordinals/e0-ordinal" :dir :system)
(set-well-founded-relation e0-ord-<)

;; Early auxilliary stuff.

;; Comment out natp since this is defined in versions from v2-8

;; (defun natp (n)
;;   (and (integerp n)
;;        (<= 0 n)))

;; Comment out natp-compound-recognizer since this is defined since v2-9-2.

;; (defthm natp-compound-recognizer
;;   (iff (natp n)
;;        (and (integerp n)
;;             (<= 0 n)))
;;   :rule-classes :compound-recognizer)

(in-theory (disable natp))

(encapsulate

 ;; This encapsulation formalizes the notion of an invariant proof.

 (((next-total *) => *)                ;; The step function
  ((pre-total *) => *)                 ;; pre-total condition
  ((post-total *) => *)                ;; post-total condition
  ((external-total *) => *)            ;; the state of interest.

  ((inv-total *) => *)                 ;; The invariant

  ((m *) => *))                  ;; measure function guaranteeing termination

 (local (defun next-total (s) s))
 (local (defun pre-total (s) (declare (ignore s)) nil))
 (local (defun external-total (s) (declare (ignore s)) nil))
 (local (defun post-total (s) (declare (ignore s)) nil))
 (local (defun inv-total (s) (declare (ignore s)) nil))
 (local (defun m (s) (declare (ignore s)) 0))

 ;; Here are the constraints that I export from the purported inductive
 ;; invariant proof. Thse should be self-explanatory.

 (defthm pre-total-implies-inv-total
   (implies (pre-total s)
            (inv-total s)))

 (defthm inv-total-is-invariant
   (implies (and (inv-total s)
                 (not (external-total (next-total s))))
            (inv-total (next-total s))))

 (defthm inv-total-and-external-total-implies-post-total
   (implies (and (inv-total s)
                 (external-total (next-total s)))
            (post-total (next-total s))))

 (defthm inv-total-implies-not-external-total
   (implies (inv-total s)
            (not (external-total s))))

 (defthm m-is-an-ordinal
   (e0-ordinalp (m s)))

 (defthm internal-steps-decrease-m
   (implies (and (inv-total s)
                 (not (external-total (next-total s))))
            (e0-ord-< (m (next-total s))
                      (m s))))

)

;; In order to define a clock function proof it is necessary to work with
;; run. So I define run here.

(defun run-total (s n)
  (if (zp n) s
    (run-total (next-total s) (1- n))))

;; We now define the clock function

(local
 ;; [Jared] changed this to use arithmetic-3 instead of 2
 (include-book "arithmetic-3/bind-free/top" :dir :system))

;; The clock function is trivial. Simply goes on with stepping the machine
;; until it halts. The cute aspect of this is that I can do this simply because
;; the inductive invariant theorems provide me with a measure.

(defun clock-total--fn-aux (s)
  (declare (xargs :measure (m s)))
  (cond ((not (inv-total s)) 0)
        ((external-total (next-total s)) 0)
        (t (1+ (clock-total--fn-aux (next-total s))))))

(defun clock-total--fn (s)
  (1+ (clock-total--fn-aux s)))

;; Ok so the proof. First prove that running for clock steps satisfies the
;; invariant.

(local
 (defthm inv-total-run-total-1
   (implies (inv-total s)
            (inv-total (run-total s (clock-total--fn-aux s))))))

;; Also clock drives you to an external state.

(local
 (defthm inv-total-run-total-2
   (implies (inv-total s)
            (external-total (next-total (run-total s (clock-total--fn-aux s)))))))

;; The next theorem is stupid, but added so as to get ACL2 to expand (run s (1+
;; n)).


(local
 (defthm next-total-run-total-is-run-total-1
   (implies (natp n)
            (equal (run-total s (1+ n))
                   (next-total (run-total s n))))))

;; And now the standard clock function theorems. Trivial, isn't it?

(DEFTHM clock-total--fn-is-natp
  (natp (clock-total--fn s))
  :hints (("Goal"
           :in-theory (enable natp))))

(DEFTHM standard-theorem-about-clock-total-s-1
  (implies (pre-total s)
           (external-total (run-total s (clock-total--fn s)))))

(DEFTHM standard-theorem-about-clock-total-s-2
  (implies (pre-total s)
           (post-total (run-total s (clock-total--fn s)))))

;; This theorem should be properly moved up. But I said what the heck, let me
;; have it here.

(local
 (defthm clock-total--fn-is-minimum
   (implies (and (natp i)
                 (inv-total s)
                 (<= i (clock-total--fn-aux s)))
            (inv-total (run-total s i)))))

(DEFTHM standard-theorem-about-clock-total-s-3
  (implies (and (pre-total s)
                (external-total (run-total s i)))
           (<= (clock-total--fn s) i)))



