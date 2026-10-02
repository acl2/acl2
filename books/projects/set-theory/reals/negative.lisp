; Copyright (C) 2026, Matt Kaufmann
; Written by Matt Kaufmann
;   with substantial assistance from Claude Code Opus 4.8, max effort,
;   using the acl2-mcp interface, as noted below
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This book introduces the dedekind cut that is the negative of a given
; dedekind cut.

; Using the acl2-mcp interface I got major help from Claude Code Opus 4.8, max
; effort.  I have noted Claude's contributions below with annotations in angle
; brackets: <<....>>.

(in-package "ZF")

(include-book "dedekind")
(include-book "projects/set-theory/set-algebra" :dir :system)
(include-book "projects/set-theory/zify" :dir :system)
(include-book "projects/set-theory/restrict" :dir :system)

(local (in-theory (disable diff-distributes-over-diff)))

; The negative of a dedekind cut is obtained by taking the complement of what
; is not in the cut (i.e., above the cut), and removing the maximum if that
; exists.  We first define a set-theoretic function, z-rational-unary--, which
; applies to a rational r to yield (- r).

(zify z-rational-unary-- unary-- :dom s :ran (rationals)
      :args (s)
      :xhyps ((rational-setp s))
      :props (rationals$prop v$prop))

; <<Begin comment added by Claude>>
; Note that (z-rational-unary-- dr) is the set-theoretic function (a set of
; ordered pairs) that negates rationals in dr; its *image*, (image
; (z-rational-unary-- dr)), is the set {-r : r in dr}.  So the set s below,
; (diff (rationals) (image (z-rational-unary-- dr))), is the set of rationals q
; with (- q) not in dr, i.e., the rationals at or below the negative of the
; cut.  We then remove the maximum of s if it exists.
; <<End comment added by Claude>>

(defund dr-unary-- (dr)
  (let ((s (diff (rationals)
; <<Originally I forgot to call image just below.  Claude figured that out and
; added that call.>>
                 (image (z-rational-unary-- dr)))))
    (if (dr-max-p s)
        (diff s (singleton (dr-max s)))
      s)))

(local (in-theory (enable drp)))

; <<Begin comments and lemmas added by Claude>>
; A basic arithmetic rewrite: cancel a double negation.  (This is needed
; because the set-theory books do not load an arithmetic library.)
(local
 (defthm neg-neg
   (equal (- (- x))
          (fix x))))

; Membership in the image of z-rational-unary--: a rational q is in the image
; exactly when (- q) is in dr.  We prove the two directions and then combine
; them into the rewrite rule in-image-z-neg.

(defthmz in-image-z-neg-back
  (implies (and (rational-setp dr) (rationalp q) (in (- q) dr))
           (in q (image (z-rational-unary-- dr))))
  :hints (("Goal"
           :use ((:instance in-apply-image
                            (r (z-rational-unary-- dr))
                            (x (- q))))))
  :props (dr-prop0 z-rational-unary--$prop))

(defthmz in-image-z-neg-fwd
  (implies (and (rational-setp dr) (rationalp q)
                (in q (image (z-rational-unary-- dr))))
           (in (- q) dr))
  :hints (("Goal"
           :in-theory (enable in-image-rewrite)
           :use ((:instance rational-setp-necc
                            (s dr)
                            (x (apply (inverse (z-rational-unary-- dr)) q))))))
  :props (dr-prop0 z-rational-unary--$prop))

(defthmz in-image-z-neg
  (implies (and (rational-setp dr) (rationalp q))
           (equal (in q (image (z-rational-unary-- dr)))
                  (in (- q) dr)))
  :hints (("Goal" :use (in-image-z-neg-back in-image-z-neg-fwd)
           :in-theory (disable in-image-z-neg-back in-image-z-neg-fwd)))
  :props (dr-prop0 z-rational-unary--$prop))

; <<End comments and lemmas added by Claude>>

(defthm rationalp-dr-bound
  (implies (dr-bounded-above dr)
           (rationalp (dr-bound dr)))
  :hints (("Goal" :in-theory (enable dr-bounded-above)))
  :rule-classes :type-prescription)

; <<Begin comments and lemma added by Claude>>

; Membership in the negative region s = (diff (rationals) (image ...)): a
; rational q is in s exactly when (- q) is not in dr.

(defthmz in-neg-region
  (implies (and (rational-setp dr) (rationalp q))
           (equal (in q (diff (rationals) (image (z-rational-unary-- dr))))
                  (not (in (- q) dr))))
  :props (dr-prop0 diff$prop z-rational-unary--$prop))

; A downward-closed set is closed under passing to a smaller (rational) value.

; <<End comments and lemma added by Claude>>

; <<I supplied the following lemma, except that I neglected to add the
; (rationalp r2) hypothesis, I wrapped the lemma with skip-proofs, and I had
; extra :props.  Claude added the missing hypothesis and removed unnecessary
; :props, and Claude added the :hints and removed the skip-proofs.>>

(defthmz closed-downward-consequence
  (implies (and (rational-setp dr)
                (dr-closed-downward dr)
                (in r1 dr)
                (<= r2 r1)
                (rationalp r2))
           (in r2 dr))
  :hints (("Goal"
           :use ((:instance dr-closed-downward-necc (x r2) (y r1) (s dr)))
           :in-theory (disable dr-closed-downward-necc)))
  :props (dr-prop0))

(defthmz rational-setp-diff
  (implies (rational-setp s1)
           (rational-setp (diff s1 s2)))
  :hints (("Goal" :expand ((rational-setp (diff s1 s2)))))
  :props (diff$prop))

(defthmz rational-setp-rationals
  (rational-setp (rationals))
  :hints (("Goal" :in-theory (enable rational-setp)))
; <<Claude removed unnecessary :props:>>
  :props (dr-prop0))

; <<Claude added the following comment:>>
; (dr-unary-- dr) is a set of rationals.

(defthmz drp-dr-unary---3
  (implies (drp dr)
           (rational-setp (dr-unary-- dr)))
  :hints (("Goal" :in-theory (enable dr-unary--)))
  :props (dr-prop0 diff$prop z-rational-unary--$prop))

; <<Begin comments and lemmas added by Claude>>

; The negative region s is closed downward (as a set of rationals): this is the
; contrapositive of dr being closed downward.

(defthmz neg-region-closed
  (implies (and (drp dr) (rationalp a) (rationalp b) (< a b)
                (in b (diff (rationals) (image (z-rational-unary-- dr)))))
           (in a (diff (rationals) (image (z-rational-unary-- dr)))))
  :hints (("Goal"
           :use ((:instance closed-downward-consequence (r1 (- a)) (r2 (- b))))
           :in-theory (disable closed-downward-consequence)))
  :props (dr-prop0 diff$prop z-rational-unary--$prop))

; (dr-unary-- dr) is closed downward.  If y is in it then y is in s, and if x <
; y then x is in s (neg-region-closed); moreover, if the maximum M of s was
; removed, then x < y <= M so x is not M, hence x remains in (dr-unary-- dr).

(defthmz du-closed
  (implies (and (drp dr) (rationalp x) (< x y) (in y (dr-unary-- dr)))
           (in x (dr-unary-- dr)))
  :hints (("Goal"
           :in-theory (enable dr-unary-- dr-max-p)
           :use ((:instance neg-region-closed (a x) (b y))
                 (:instance rational-setp-necc (s (dr-unary-- dr)) (x y)))))
  :props (dr-prop0 diff$prop z-rational-unary--$prop))

; <<End comments and lemmas added by Claude>>

; <<Claude removed skip-proofs that was wrapped around the following.  It also
; added an extra layer of parentheses around the :expand hint -- not necessary,
; but arguably better style.>>
(defthmz drp-dr-unary---5
  (implies (drp dr)
           (dr-closed-downward (dr-unary-- dr)))
  :hints (("Goal" :expand ((dr-closed-downward (dr-unary-- dr)))))
  :props (dr-prop0 diff$prop z-rational-unary--$prop))

; <<Begin comment and lemma added by Claude>>

; (dr-unary-- dr) has no maximum: no member r of it is an upper bound.  If the
; maximum M of s remains (i.e., s has no maximum), this is immediate since s =
; (dr-unary-- dr) has no maximum (dr-max-p-suff).  Otherwise M was removed, and
; the midpoint (r+M)/2 lies strictly between r and M, hence is in s, is not M,
; and so is a member of (dr-unary-- dr) exceeding r.

(defthmz du-not-max
  (implies (and (drp dr) (in r (dr-unary-- dr)))
           (not (dr-boundp r (dr-unary-- dr))))
  :hints (("Goal"
           :in-theory (enable dr-unary--)
           :expand ((dr-max-p (diff (rationals) (image (z-rational-unary-- dr)))))
           :use ((:instance neg-region-closed
                            (a (* 1/2 (+ r (dr-max (diff (rationals) (image (z-rational-unary-- dr)))))))
                            (b (dr-max (diff (rationals) (image (z-rational-unary-- dr))))))
                 (:instance dr-boundp-necc
                            (b r) (s (dr-unary-- dr))
                            (y (* 1/2 (+ r (dr-max (diff (rationals) (image (z-rational-unary-- dr))))))))
                 (:instance dr-boundp-necc
                            (b (dr-max (diff (rationals) (image (z-rational-unary-- dr)))))
                            (s (diff (rationals) (image (z-rational-unary-- dr))))
                            (y r))
                 (:instance dr-max-p-suff
                            (b r)
                            (s (diff (rationals) (image (z-rational-unary-- dr))))))))
  :props (dr-prop0 diff$prop z-rational-unary--$prop))

; <<End comment and lemma added by Claude>>

; <<Claude removed the skip-proofs wrapper from the following lemma.  Claude
; also replaced the :hints with suitable :hints.>>
(defthmz drp-dr-unary---2
  (implies (drp dr)
           (not (dr-max-p (dr-unary-- dr))))
  :hints (("Goal"
           :expand ((dr-max-p (dr-unary-- dr)))
           :use ((:instance du-not-max (r (dr-max (dr-unary-- dr)))))))
  :props (dr-prop0 diff$prop z-rational-unary--$prop))

; <<Begin comment and lemmas added by Claude>>

; (dr-unary-- dr) is bounded above by (abs (min-in dr)).  For q in it, (- q) is
; not in dr; but if q exceeded (abs (min-in dr)) then (- q) would be below
; (- (abs (min-in dr))), which is at most (min-in dr) and hence in dr -- a
; contradiction.

(defthmz du-bounded-matrix
  (implies (and (drp dr) (in q (dr-unary-- dr)))
           (<= q (abs (min-in dr))))
  :hints (("Goal"
           :in-theory (enable dr-unary--)
           :use ((:instance closed-downward-consequence
                            (r1 (min-in dr)) (r2 (- (abs (min-in dr)))))
                 (:instance closed-downward-consequence
                            (r1 (- (abs (min-in dr)))) (r2 (- q)))
                 (:instance rational-setp-necc (s (dr-unary-- dr)) (x q)))))
  :props (dr-prop0 diff$prop z-rational-unary--$prop))

(defthmz du-dr-boundp
  (implies (drp dr)
           (dr-boundp (abs (min-in dr)) (dr-unary-- dr)))
  :hints (("Goal"
           :expand ((dr-boundp (abs (min-in dr)) (dr-unary-- dr)))
           :in-theory (disable abs)))
  :props (dr-prop0 diff$prop z-rational-unary--$prop))

; <<End comment and lemmas added by Claude>>

; <<Claude removed the skip-proofs wrapper from the following lemma.>>
(defthmz drp-dr-unary---4

; <<I provided Claude with the following comment, which it removed.>>

; Proof sketch.  Choose r \in dr (e.g., r = (min-in dr)).  There are two cases.
; If r >= 0, then by (dr-closed-downward dr), (dr-unary-- dr) consists only of
; negative rationals, so r is an upper bound for (dr-unary-- dr).  Otherwise r
; < 0, in which case -r is an upper bound for (dr-unary-- dr).

  (implies (drp dr)
           (dr-bounded-above (dr-unary-- dr)))
  :hints (("Goal"
           :use ((:instance dr-bounded-above-suff
                            (b (abs (min-in dr))) (s (dr-unary-- dr)))
; <<Claude added the following two lemma instances to this :use hint.>>
                 (:instance rational-setp-necc (s dr) (x (min-in dr)))
                 du-dr-boundp)
           :in-theory (disable dr-bounded-above-suff)))
  :props (dr-prop0 diff$prop z-rational-unary--$prop))

; <<Begin comment and lemmas added by Claude>>

; (dr-unary-- dr) is non-empty.  For any k>0, -(k + (dr-bound dr)) is in s,
; since its negation exceeds the bound of dr and so is not in dr.  The witness
; -(2 + (dr-bound dr)) lies strictly below -(1 + (dr-bound dr)), which is at
; most the maximum M of s; hence the witness is not M and remains in
; (dr-unary-- dr).

(defthmz in-neg-big
  (implies (and (drp dr) (rationalp k) (< 0 k))
           (in (- (+ k (dr-bound dr)))
               (diff (rationals) (image (z-rational-unary-- dr)))))
  :hints (("Goal"
           :expand ((dr-bounded-above dr))
           :use ((:instance dr-boundp-necc (b (dr-bound dr)) (s dr)
                            (y (+ k (dr-bound dr)))))))
  :props (dr-prop0 diff$prop z-rational-unary--$prop))

(defthmz du-has-elt
  (implies (drp dr)
           (in (- (+ 2 (dr-bound dr))) (dr-unary-- dr)))
  :hints (("Goal"
           :in-theory (enable dr-unary--)
           :expand ((dr-max-p (diff (rationals) (image (z-rational-unary-- dr)))))
           :use ((:instance in-neg-big (k 2))
                 (:instance in-neg-big (k 1))
                 (:instance dr-boundp-necc
                            (b (- (+ 2 (dr-bound dr))))
                            (s (diff (rationals) (image (z-rational-unary-- dr))))
                            (y (- (+ 1 (dr-bound dr))))))))
  :props (dr-prop0 diff$prop z-rational-unary--$prop))

; <<end comment and lemmas added by Claude>>

; <<Claude removed the skip-proofs that was wrapped around the following
; lemma.>>
(defthmz drp-dr-unary---1
  (implies (drp dr)
           (not (equal (dr-unary-- dr) 0)))
; <<Claude added the following :hints.>>
  :hints (("Goal" :use du-has-elt))
  :props (dr-prop0 diff$prop z-rational-unary--$prop))

; <<Claude added the following comment:>>
; Finally: the negative of a dedekind cut is a dedekind cut.

(defthmz drp-dr-unary--
  (implies (drp dr)
           (drp (dr-unary-- dr)))
; <<I included the following needless :hints, which Claude didn't delete.
; I'm commenting out the :hints after the fact.>>
; :hints (("Goal" :in-theory (enable drp)))
  :props (dr-prop0 diff$prop z-rational-unary--$prop))
