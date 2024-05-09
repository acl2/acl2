; Copyright (C) 2022, ForrestHunt, Inc.
; Written by J Strother Moore
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.
; Release approved by DARPA with "DISTRIBUTION STATEMENT A. Approved
; for public release. Distribution is unlimited."

; (certify-book "lp12")

(in-package "ACL2")

(include-book "projects/apply/top" :dir :system)

; First tell the reader to return to his or her solutions to lp8.lisp and prove
; each of the equivalences.  Our answers to the lp8.lisp problems are in that
; file.

; -----------------------------------------------------------------
; LP12-1: Define (assoc-equal-loop$ x alist) to be equal to (assoc-equal x
; alist) when (alistp alist).  Verify the guards of assoc-equal-loop$ and prove
; that your function satisfies the specification above.  Is your function
; unconditionally equal to assoc-equal?  If so, prove it; if not, show a
; counterexample.

; Answer:

(defun assoc-equal-loop$ (x alist)
  (declare (xargs :guard (alistp alist)))
  (loop$ for pair in alist
         thereis
         :guard (consp pair)
         (if (equal (car pair) x)
             pair
             nil)))

(defthm LP12-1
  (implies (alistp alist)
           (equal (assoc-equal-loop$ x alist)
                  (assoc-equal x alist))))

(defthm counterexample-to-stronger-LP12-1
  (let ((x nil)
        (alist '(nil (nil . 33))))
    (and (equal (assoc-equal x alist) nil)
         (equal (assoc-equal-loop$ x alist) '(nil . 33))))
  :rule-classes nil)

; -----------------------------------------------------------------
; LP12-2: Under what conditions is this a theorem?  Prove it.

; (defthm LP12-2
;   (implies ...
;            (equal (loop$ for x in keys as y in vals collect (cons x y))
;                   (pairlis$ keys vals)))
;   :rule-classes nil)

; Answer:

(defthm LP12-2
  (implies (<= (len keys) (len vals))
           (equal (loop$ for x in keys as y in vals collect (cons x y))
                  (pairlis$ keys vals))))

; Note that it is not actually necessary that keys or vals be true-lists, even
; though the guards of both the loop$ and of pairlis$ require true-lists.
; Logically, the loop$ is equivalent to the pairlis$ as long as the hypothesis
; above holds.  We just proved it.  If the hypothesis does not hold the two are
; not equal.  In fact, we can prove a stronger version of LP12-2:

(defthm LP12-2-equivalence
  (equal (equal (loop$ for x in keys as y in vals collect (cons x y))
                (pairlis$ keys vals))
         (<= (len keys) (len vals)))
  :rule-classes nil)

; The key to this equivalence is the observation that pairlis$ stops when keys
; is empty, but the loop$ stops when the shorter of the two is empty.

(defthm LP12-2-observation
  (let ((keys '(A B C))
        (vals '(1 2)))
    (and (equal (loop$ for x in keys as y in vals collect (cons x y))
                '((A . 1) (B . 2)))
         (equal (pairlis$ keys vals)
                '((A . 1) (B . 2) (C . NIL)))))
  :rule-classes nil)

; -----------------------------------------------------------------
; LP12-3: Prove

; (defthm LP12-3
;   (equal (* 2 (len (loop$ for tl on lst append tl)))
;          (* (len lst) (+ (len lst) 1))))

; Hint: By phrasing the challenge with the multiplication by 2 on the left-hand
; side, we produce a conjecture that can be proved (perhaps with a few lemmas)
; without the need for ``heavy duty'' arithmetic books.  Had we divided by 2 on
; the right-hand side, we'd have brought division into the problem which we
; intentionally avoided.  You will still need a lemma or two, discoverable by
; The Method.

; Answer:

(defthm LP12-3-lemma
  (equal (len (append a b)) (+ (len a) (len b))))

(defthm LP12-3
  (equal (* 2 (len (loop$ for tl on lst append tl)))
         (* (len lst) (+ (len lst) 1))))

; -----------------------------------------------------------------
; LP12-4:  Define

(defun nats (n)
  (cond ((zp n) (list 0))
        (t (append (nats (- n 1)) (list n)))))

; and prove that the obvious loop$ statement is equivalent to (nats n) when n
; is a natural.  Make your defthm of :rule-classes nil so as not to interfere
; with your work on the next problem.

; Answer:

; One's first reaction might be to generalize the 0 below so we can induct up
; to n.  But that sort of conflicts with (nats n) which inducts down.  Perhaps
; surprisingly, the projects/apply/top book has rules that allow (from-to-by 0
; n 1) to suggest induction down.  So the direct proof just works.

(defthm LP12-4
  (implies (natp n)
           (equal (loop$ for i from 0 to n collect i)
                  (nats n)))
  :rule-classes nil)

; -----------------------------------------------------------------
; LP12-5:  Define

(defun nats-up (i n)
  (declare (xargs :measure (nfix (- (+ (nfix n) 1) (nfix i)))))
  (let ((i (nfix i))
        (n (nfix n)))
    (cond ((> i n) nil)
          (t (cons i (nats-up (+ i 1) n))))))

; Prove
; (defthm LP12-5
;   (implies (natp n)
;            (equal (loop$ for i from 0 to n collect i)
;                  (nats-up 0 n)))
;   :rule-classes nil)

; Answer:

(defthm LP12-5-lemma
  (implies (and (natp n)
                (natp i0))
           (equal (loop$ for i from i0 to n collect i)
                  (nats-up i0 n))))

(defthm LP12-5
  (implies (natp n)
           (equal (loop$ for i from 0 to n collect i)
                  (nats-up 0 n)))
  :rule-classes nil)

; -----------------------------------------------------------------
; LP12-6: Fill in the blanks below and prove the theorem.  You may need hints.
; If not, just delete the :hints setting.

; (defthm LP12-6
;   (implies (true-listp lst)
;            (equal (loop$ ...)
;                   (strip-cars lst)))
;   :hints ...
;   :rule-classes nil)

; Answer:

(defthm LP12-6
  (implies (true-listp lst)
           (equal (loop$ for e in lst collect (car e))
                  (strip-cars lst))))

; -----------------------------------------------------------------
; LP12-7:  Prove the following, adding :hints if necessary.  Otherwise, just
; delete the :hints setting.

; (defthm LP12-7
;   (loop$ for pair in (loop$ for key in keys
;                             as  val from 0 to (+ (len keys) -1)
;                             collect (cons key val))
;          always (integerp (cdr pair)))
;   :hints ...)

; Answer: We clearly need to generalize the ``val from 0 to (+ (len keys) -1)''
; so we can induct up from some arbitrary starting point j0.  But this is a
; case where we do not have to be careful about how many steps we take.  So we
; can just start at some integer j0 and go up to some integer max.  No matter
; what, we'll always build a list of pairs containing integers in the cdrs.

(defthm LP12-7-lemma
  (implies (and (integerp j0)
                (integerp max))
           (loop$ for pair in (loop$ for key in keys
                                     as  val from j0 to max
                                     collect (cons key val))
                  always (integerp (cdr pair)))))

(defthm LP12-7
  (loop$ for pair in (loop$ for key in keys
                            as  val from 0 to (+ (len keys) -1)
                            collect (cons key val))
         always (integerp (cdr pair))))

; -----------------------------------------------------------------
; LP12-8:  Fill in the blanks below and then prove the theorem.  You may
; need hints.  If not, just delete the :hints setting.

; (defthm LP12-8
;   (implies (natp n)
;            (equal (loop$ ...)
;                   (nth n lst)))
;   :hints ...
;   :rule-classes nil)

; Answer: We fill in blank (loop$ ...) with

; (loop$ for e in lst as i from 0 to (+ (len lst) -1)
;        thereis (if (equal n i) e nil))
; which formally is
;  (THEREIS$+ (LAMBDA$ (LOOP$-GVARS LOOP$-IVARS)
;                      (AND (EQUAL (CAR LOOP$-GVARS)
;                                  (CADR LOOP$-IVARS))
;                           (CAR LOOP$-IVARS)))
;             (LIST N)
;             (LOOP$-AS (LIST LST (FROM-TO-BY 0 (+ (LEN LST) -1) 1))))

; You'll see such THEREIS$+ terms in checkpoints, so it is good to be able to
; bo back and forth between the loop$ form and the scion form.  But we'll state
; our lemmas with the loop$ form even though the checkpoints are displayed as
; thereis$+ forms.

; It is clear we have to generalize this so that instead of going from 0 to the
; given upper limit it goes from some initial i0 to that same upper limit plus
; i0.  Our final statement of that generalized lemma is LP12-8-lemma below.

; But the first failed proof of that lemma raised a checkpoint, namely Subgoal
; *1/5.1.2', that included the term:

; (THEREIS$+ (LAMBDA$ (LOOP$-GVARS LOOP$-IVARS)
;                     (AND (EQUAL (CAR LOOP$-GVARS)
;                                 (CADR LOOP$-IVARS))
;                          (CAR LOOP$-IVARS)))
;            (LIST I0)
;            (LOOP$-AS (LIST (CDR LST)
;                            (FROM-TO-BY (+ 1 I0)
;                                        (+ I0 (LEN (CDR LST)))
;                                        1))))

; which can be written as this loop$:

; (loop$ for e in (cdr lst) as i from (+ 1 I0) to (+ I0 (LEN (CDR LST)))
;        thereis (if (equal i0 i) e nil))

; By the way, the observation that the loop$ translates (and cleans up) to
; the thereis$+ can be confirmed by using :tcp on the loop$.

; We recognized that this loop$ is equal to NIL.  The reason is that i runs
; from (+ 1 I0) upwards but the loop$ body is looking for i0.  It clearly isn't
; going to find it!

; To prove that we generalize the loop$ to what is shown below, so we can induct
; on j upwards to max.  The original limits on the i were entwined with I0 which
; is being held constant by the thereis loop$ and so prevents the induction we
; need.  But this:

(defthm LP12-8-lemma-lemma
  (implies (and (natp i0)
                (natp j)
                (natp max)
                (< i0 j))
           (not (loop$ for e in lst as i from j to max
                       thereis (if (equal i0 i) e nil)))))

; is proved easily.

; Using the above we can prove the lemma we need, which is named LP12-8-lemma.
; Note how in LP12-8-lemma we generalized

; ``... as i from 0  to (+    (len lst) -1) ...'' to
; ``... as i from i0 to (+ i0 (len lst) -1) ...''

; so that we can induct ``upwards'' on i and still take as many iterations as
; required.

; Logically speaking, this lemma is the key result.  Everything we do after
; this is just figuring out how to get the prover to use this result!

(defthm LP12-8-lemma
  (implies (and (natp n)
                (natp i0)
                (<= i0 n))
           (equal (loop$ for e in lst as i from i0 to (+ i0 (len lst) -1)
                         thereis (if (equal n i) e nil))
                  (nth (- n i0) lst)))
  :rule-classes nil)

; Note that we stored this lemma with :rule-classes nil.  The reason is that
; finding a way to make the prover take advantage of the lemma is difficult.
; We will explore three slightly ``different'' proofs.  Logically, they're all
; the same, but operationally we have to take different actions depending on
; how we phrase and store the rule.

; If LP12-8-lemma is stored as a :rewrite rule as written it fails to hit the
; target.

; lhs  above:  (loop$ for e in lst
;                     as  i from i0 to (+ I0 (LEN LST) -1)
;                     thereis (if (equal n i) e nil))
; target:      (loop$ for e in lst
;                     as  i from  0 to (+ (LEN LST) -1)
;                     thereis (if (equal n i) e nil))

; Even if you instantiate i0 in the rule with 0, the UPPERCASE portion of the
; lhs of the instantiated rule does not SYNTACTICALLY match the UPPERCASE
; portion of the target because (+ 0 (LEN LST) -1) and (+ (LEN LST) -1) are
; different.  Of course, they're equal.  So one way to prove the main theorem
; is just to :use an instance of the lemma:

(defthm LP12-8-proof-1 ; aka LP12-8
  (implies (natp n)
           (equal (loop$ for e in lst as i from 0 to (+ (len lst) -1)
                         thereis (if (equal n i) e nil))
                  (nth n lst)))
  :hints (("Goal"
           :use ((:instance LP12-8-lemma (i0 0)))))
  :rule-classes nil)

; But we would like lemmas to fire automatically when appropriate.  So what
; can we do?

; An alternative approach is to try to make the lemma more general so it will
; fire.  We ``generalize'' the upper limit.  This is not actually a
; generalization, because we replace the upper limit with the new variable max
; and then add the hypothesis that max is (+ i0 (len lst) -1).  Boyer and Moore
; called such lemmas ``bridge'' lemmas because they allowed pattern matching to
; work and then bridged over the syntactic differences with theorem proving.

(defthm LP12-8-lemma-bridge
  (implies (and (natp n)
                (natp i0)
                (<= i0 n)
                (equal max (+ i0 (len lst) -1)))
           (equal (loop$ for e in lst as i from i0 to max
                         thereis (if (equal n i) e nil))
                  (nth (- n i0) lst)))
  :hints (("Goal" :use lp12-8-lemma)))

; Note that we prove the bridge trivially from lp12-8-lemma.  But we could have
; stated lp12-8-lemma this ``more general'' way in the first place, proved it
; inductively as before, and stored it as a :rewrite rule.

; Often that such bridge lemmas are an effective strategy.  However, the
; attempt to prove the main result, LP12-8, via the automatic use of this
; bridge lemma still doesn't work!  The translated lhs of the :rewrite rule
; created by the bridge is

; ACL2 >:tcp (loop$ for e in lst as i from i0 to max
;                       thereis (if (equal n i) e nil))
;  (THEREIS$+ (LAMBDA$ (LOOP$-GVARS LOOP$-IVARS)
;                      (AND (EQUAL (CAR LOOP$-GVARS)
;                                  (CADR LOOP$-IVARS))
;                           (CAR LOOP$-IVARS)))
;             (LIST N)
;             (LOOP$-AS (LIST LST (FROM-TO-BY I0 MAX 1))))

; and that indeed syntactically matches the translated target we want to
; rewrite in the main theorem;

; ACL2 >:tcp (loop$ for e in lst as i from 0 to (+ (len lst) -1)
;                       thereis (if (equal n i) e nil))
;  (THEREIS$+ (LAMBDA$ (LOOP$-GVARS LOOP$-IVARS)
;                      (AND (EQUAL (CAR LOOP$-GVARS)
;                                  (CADR LOOP$-IVARS))
;                           (CAR LOOP$-IVARS)))
;             (LIST N)
;             (LOOP$-AS (LIST LST (FROM-TO-BY 0 (+ (LEN LST) -1) 1))))

; But unfortunately, before the theorem prover tries to apply the lemma it
; opens up the (FROM-TO-BY 0 (+ (LEN LST) -1) 1) in the target by applying the
; definition of from-to-by and puts (CONS 0 (FROM-TO-BY 1 (+ (LEN LST) -1) 1))
; in its place.  This causes our rule no longer to match.

; So to ``automatically'' apply lp12-5-lemma-bridge we have to stop from-to-by
; from opening, by disabling it.  This is our ``second'' proof of LP12-8:

(defthm LP12-8-proof-2 ; aka LP12-8
  (implies (natp n)
           (equal (loop$ for e in lst as i from 0 to (+ (len lst) -1)
                         thereis (if (equal n i) e nil))
                  (nth n lst)))
  :hints (("Goal"
           :in-theory (disable from-to-by)))
  :rule-classes nil)

; The problem of finding a rule that will automatically fire on LP12-8 can be
; addressed by a different bridge.  The idea is to replace the (FROM-TO-BY ...)
; in the lhs of our rule by a variable, say xxx, and require that variable to
; be equal to the from-to-by expression.  But you can't state that rule in
; terms of loop$ because no subterm of the loop$ syntax is a from-to-by
; expression!  You have to write the lhs of this bridge lemma in the form of
; the translated loop$:

(defthm LP12-8-lemma-different-bridge
  (implies (and (<= i0 n) ; <-- elevated to chose the free i0!
                (natp n)
                (natp i0)
                (equal xxx (FROM-TO-BY I0 (+ I0 (LEN LST) -1) 1)))
           (equal (THEREIS$+ (LAMBDA$ (LOOP$-GVARS LOOP$-IVARS)
                                      (AND (EQUAL (CAR LOOP$-GVARS)
                                                  (CADR LOOP$-IVARS))
                                           (CAR LOOP$-IVARS)))
                             (LIST N)
                             (LOOP$-AS (LIST LST xxx)))
                  (nth (- n i0) lst)))
  :hints (("Goal" :use lp12-5-lemma)))

; Furthermore, the equality between xxx and the from-to-by expression involves
; a variable, I0, occurring nowhere else in the target.  So I0 is free in this
; rule and the theorem prover needs some guidance as to how to choose I0 when
; applying the rule.  To give it guidance, we move the (<= i0 n) hypothesis up
; to the top so I0 is chosen to be some term known to be less than N.

; Now LP12-8-lemma-different-bridge is used ``automatically.''  But it is
; extremely fragile because of the free I0 and the rather generic term selected
; to guide its choice.  So here's a ``third'' proof.

(defthm LP12-8-proof-3 ; aka LP12-8
  (implies (natp n)
           (equal (loop$ for e in lst as i from 0 to (+ (len lst) -1)
                         thereis (if (equal n i) e nil))
                  (nth n lst)))
  :rule-classes nil)

; Personally, in this particular case, we would probably go with proof 1, where
; the LP12-8-lemma is of :rule-classes nil and we just :use it where we want
; it.  But we show the other two tricks because they are sometimes handy.
