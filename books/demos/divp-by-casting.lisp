; Copyright (C) 2025, J Strother Moore
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Divisibility by Casting
; J Moore
; May, 2025

; (certify-book "divp-by-casting")

; Abstract

; In this book we prove the general theorem that the divisibility of n by d can
; be determined by recursively summing the base-b digits of n and then checking
; that the final sum is divisible by d, provided n, d and b are naturals, d and
; b are greater than 1, and b is equivalent to 1 mod d.  We then prove
; corollaries that show ``casting out 9s'' and ``casting out 3s'' work
; correctly when decimal (base b = 10) digits are extracted and summed.  We
; also show that ``casting out 7s'' works when octal (base b = 8) digits are
; extracted and summed.  Furthermore, we prove that casting out 7s can be
; computed using the logical operations [logand] and [ash] instead of [mod] and
; [floor].

; The proof of the general theorem requires non-linear arithmetic since d and b
; are variables, whereas in the corollaries b and d are constants, e.g., 10 and
; 3 or 8 and 7.  So use is made of the powerful arithmetic book
; arithmetic-5/top.  This book provides rules for manipulating many arithmetic
; primitives, including mod and floor and is able to handle many non-linear
; arithmetic problems heuristically.  However, (a) arithmetic-5/top does not
; rewrite mod and floor expressions as we wanted them rewritten for this proof,
; and (b) arithmetic-5/top sometimes goes into an infinite loop in its attempt
; to reason about multiplication.  So perhaps the most important lesson to be
; gained from this book is an illustration of one way to manage such problems
; while still using arithmetic-5/top on the problems it can solve.  For that
; reason, we've taken special care to describe how the proof script here was
; created.  For further details, read the extensive comments in the
; divp-by-casting book.

; Related ACL2 Work

; The problem of ``casting out 3s'' was listed in Freek Wiedijk's ``Formalizing
; 100 Theorems.'' In response, in 2019, several ACL2 users, including Dave
; Greve, David Hardin, Pete Manolios, and David Russinoff produced ACL2 proofs.
; For Russinoff's proof script, which I believe was the first of these ACL2
; proofs, see books/projects/numbers/div3.lisp.  I ``invented'' the present
; generalization while wondering whether there was a similar trick for
; determining divibility by 7.  I put ``invented'' in quotes because I haven't
; seen this algorithm discussed before -- but then I haven't looked for it --
; but feel certain it must have been because it's the obvious generalization.

; General Introduction

; We all know that a number is divisible by 9 if, when you sum the digits
; recursively (until the sum is less than 10) the result is 9.  It actually is
; an iff, provided you also recognize that 0 is divisible by 9.  The key
; insight in ``casting out 9s'' is that the recursive sum of the digits of n
; and n itself are equivalent, mod 9.

; But the same algorithm works to determine divisibility by 3, if in the base
; case you check that the final sum is divisible by 3, which means the final
; sum is 0, 3, 6, or 9.

; Observe that if n is represented in binary then the mods and floors that are
; involved in extracting the base-b digits can be replaced by logand and ash
; provided one can choose a b as above that is also a power of 2.  For example,
; one can determine divisibility by 7, without involving mod or floor, by
; summing the base-8 digits.

; So after proving the correctness of the general algorithm I derive, as
; straightforward corollaries, that casting out 9s ``works'' when reading
; digits in base 10, that casting out 3s also ``works'' for base 10, and that
; casting out 7s ``works'' for octal (base 8) digits.  Furthermore, the last
; result is rephrased so that mod and floor are never involved in the
; determination of divisibility by 7.

; This book is unusual in that in the comments I make a great effort to explain
; how I developed the proof script.  The reason is that several lemmas look
; like ugly rabbits pulled out of the hat when in fact they are almost
; formulated for me by failed proofs.

; The Crux of the Proof

; Because the general theorem uses variables for the divisor, d, and the base,
; b, where the special cases use constants, e.g., d=9 and b=10, or d=7 and b=8,
; the proof involves ``non-linear'' arithmetic.  Unfortunately, the non-linear
; book, arithmetic-5/top, occasionally falls into rewrite loops.  So that aspect
; of the mechanized proof has to be managed.

; I'll define three functions:

; (SUMDIGS N B)           - sum the base-b digits of n
; (SUMDIGS* N B)          - recursively sum the digits by calling sumdigs
;                           repeatedly
; (DIVP-BY-CASTING N B D) - use sumdigs* to recursively sum the digits and
;                           check whether the final sum is divisible by d.

; And here is my claim.  Let n, b, and d be naturals, 1 < b, and 0 < d.
; Furthermore, let b be one greater than some multiple of d.  E.g., if d is 3,
; the permissible bs are 4, 7, 10, 13, etc.  Then (divp-by-casting n b d) is t
; iff d|n, i.e., (mod n d) = 0.

; (defthm divp-by-casting-correct
;   (implies (and (natp n)
;                 (natp b)
;                 (< 1 b)
;                 (natp d)
;                 (< 1 d)
;                 (equal (mod (- b 1) d) 0))
;            (equal (divp-by-casting n b d)
;                   (equal (mod n d) 0))))

; Observe that if sumdigs preserves n mod d then it is trivial to show that
; sumdigs* does also, and thus it is trivial to prove divp-by-casting correct.

; So the key lemma is:

; (defthm mod-sumdigs        ; the ``crux'' lemma
;   (implies (and (natp n)
;                 (natp b)
;                 (< 1 b)
;                 (natp d)
;                 (< 1 d)
;                 (equal (mod (- b 1) d) 0))
;            (equal (mod (sumdigs n b) d)
;                   (mod n d)))
;   :hints (("Goal" :in-theory (disable mod floor))))

; The Informal Proof of mod-sumdigs

; Mod ``distributes'' over + and *, provided one keeps a mod at the top,
; e.g.,

; (mod (+ x y) z) = (mod (+ (mod x z) (mod y z)) z)
; and
; (mod (* x y) z) = (mod (* (mod x z) (mod y z)) z)

; We call this ``scattering'' the mods.

; Furthermore, if the base b is one more than a multiple of d then (mod b d) =
; 1, and because of that and of scattering, (mod b^j d)=1.  That is, the powers
; b are all equal to 1 mod d.

; Finally, the base-b digits of n are just the mods, base b, of successive
; floors of n, base b.

; Let d0, d1, ..., dk be the base-b digits of n, i.e.,

; n = b^k*dk + ... + b^1*d1 + b^0*d0

; Thus, by the foregoing and arithmetic

; (mod n d) = (mod b^k*dk + ... + b^1*d1 + b^0*d0 d)
;           = (mod (dk+...+d1+d0) d)
;           = (mod (sumdigs n b) d)

; Of course, the formal proof uses induction instead of ellipses!

; Proof Sketch of mod-sumdigs:

; Induct according to (sumdigs n b).  The base case is trivial.  In the
; induction step, the lhs of the conclusion of the induction conclusion
; expands, by opening up sumdigs, to

; (mod (+ (mod n b)
;         (sumdigs (floor n b) b))
;      d)

; Now scatter (mods ... d) down to the arguments of the +, getting

; (mod (+ (mod (mod n b) d)
;         (mod (sumdigs (floor n b) b) d))
;      d).

; Note that, by the induction hypothesis, the second addend is (mod (floor n b)
; d).  So the conclusion of the induction conclusion is now:

; (equal (mod (+ (mod (mod n b) d)
;                (mod (floor n b) d))
;             d)
;        (mod n d))

; Next, use floor-mod-elim to replace n by (+ i (* b j)).  This is actually the
; beginning of a chain of 3 uses of floor-mod-elim (since it introduces new
; variables into the maws of other mod and floor terms).  Continue to scatter
; the mods down, including down through the calls of *.

; Eventually the following ugly subgoal is produced:

; Subgoal *1/2.1.1''    ; the so-called ``ugly subgoal''
;   (IMPLIES
;    (AND (INTEGERP J)
;         (<= 0 J)
;         (INTEGERP N)
;         (<= 0 N)
;         (< J D)
;         (INTEGERP (+ J (* D N)))
;         (<= 0 (+ J (* D N)))
;         (INTEGERP I)
;         (<= 0 I)
;         (INTEGERP M)
;         (<= 0 M)
;         (< I D)
;         (INTEGERP (+ I (* D M)))
;         (<= 0 (+ I (* D M)))
;         (INTEGERP K)
;         (<= 0 K)
;         (INTEGERP L)
;         (<= 0 L)
;         (< K D)
;         (INTEGERP (+ K (* D L)))
;         (<= 0 (+ K (* D L)))
;         (< (+ K (* D L)) (+ J (* D N)))
;         (<= 0
;             (+ K (* D L)
;                (* I J)
;                (* I D N)
;                (* J D M)
;                (* D M D N)))
;         (< 1 (+ J (* D N)))
;         (< 0
;            (+ K (* D L)
;               (* I J)
;               (* I D N)
;               (* J D M)
;               (* D M D N)))
;         (EQUAL (MOD (SUMDIGS (+ I (* D M)) (+ J (* D N)))
;                     D)
;                I)
;         (INTEGERP D)
;         (<= 0 D)
;         (< 1 D)
;         (EQUAL (MOD (+ -1 J (* D N)) D) 0))
;    (EQUAL (MOD (+ (MOD I D) (MOD K D)) D)
;           (MOD (+ (MOD K D)
;                   (MOD (+ (MOD (* (MOD I D) (MOD J D)) D)
;                           (MOD (+ (MOD (* (MOD D D) (MOD L D)) D)
;                                   (MOD (* (MOD J D)
;                                           (MOD (* (MOD D D) (MOD M D)) D))
;                                        D))
;                                D))
;                        D))
;                D))))

; Now clean that up, e.g., by replacing (MOD D D) by 0, (MOD J D) by J (since
; J<D), etc.  The result is

;    (EQUAL (MOD (+ (MOD I D) (MOD K D)) D)
;           (MOD (+ (MOD I D) (MOD K D)) D))

; Q.E.D.

; -----------------------------------------------------------------
; Tactical Considerations and Actual Proof Process

; Admitting the first two of the three functions, sumdigs and sumdigs*,
; requires facts about mod and floor, including ``non-linear'' facts.  So I do
; a lot of the work in the theory created by arithmetic-5/top, which provides
; both non-linear reasoning and a lot of facts about mod and floor.  But
; arithmetic-5/top does not manipulate mod and floor quite the way I want in
; the proof.  So the basic idea here is to get into an encapsulate, locally
; include arithmetic-5/top, admit the definitions and prove some lemmas mainly
; about mod and floor.  While in that encapsulate I will have to grapple with
; the unfortunate fact that arithmetic-5/top sometimes get into loops.  (This
; behavior apparently has nothing to do with what rules I've proved but the
; rules built into arithmetic-5/top itself.)  When the encapsulate is complete
; and I exit back to ACL2's ``boot-strap'' (or ``ground-zero'') theory, that
; simple theory is extended with the definitions of sumdigs, sumdigs*, and
; divp-by-casting, and just the rewrite rules proved in the encapsulate.

; The encapsulate evolved as I discovered the rules that would need to be
; proved within it.  In particular, below I discuss two versions of the
; encapsulate: the first was used to discover the ``ugly subgoal'' above and
; then from that version I produced the second (final) version of the
; encapsulate.  In actual fact, several minor versions were created as I
; discovered other necessary lemmas but I focus on just these two versions.

; Once out of the encapsulate, I immediately disable MOD and FLOOR.

; In that slightly extended theory, I prove the ``crux'' lemma, mod-sumdigs,
; which says (sumdigs n b d) and n are equal mod d (under our hypotheses about
; n, b, and d).  From there it's straightforward to prove the analogous fact
; about sumdigs*, and that divp-by-casting is correct.  Then I derive the
; correctness of casting out 9s, casting out 3s, and casting out 7s, as
; straightforward corollaries.

; Henceforth in this comment I focus on the proof of mod-sumdigs and, in
; particular, the lemmas proved within the encapsulate to enable the proof
; sketched above.

; Recall mod-sumdigs.  It states that under certain hypotheses

; (mod (sumdigs n b) d) = (mod n d).

; After induction as suggested by (sumdigs n b) and expansion of the sumdigs
; term in (mod (sumdigs n b) d), I scatter all the mods through the + and *
; terms.  By that I mean I use rewrites like:

; scatter-mods:
; (mod (+ x y) d) = (mod (+ (mod x d) y) d)
; (mod (+ x y) d) = (mod (+ x (mod y d)) d)
; (mod (* x y) d) = (mod (* (mod x d) y) d)
; and
; (mod (* x y) d) = (mod (* x (mod y d)) d)

; So I will prove those four rewrite rules within the encapsulate.  But to
; prevent looping I have to impose a syntactic restriction to avoid a chain of
; rewrites like:

; (mod (+ x y) d)
;  = (mod (+ (mod x d) y) d)
;  = (mod (+ (mod (mod x d) d) y) d)
;  = ...

; So our rules won't put (mod ... d) on an argument if that argument already
; has one, i.e., the (mod ... d) on an argument to + or * inside a (mod ... d)
; term is a marker preventing the rules from firing again.

; But simplification in a more interesting theory can remove such a ``marker.''
; E.g., (mod x d) might rewrite to x when x<d.  Thus, moving mods through + and
; * can loop in the presence of rules that eliminate calls of mod.  The lesson
; is that during the first phase of simplifying (mod (sumdigs n b) d) the
; scatter-mods rules should be available and rules doing other simplifications
; of mod terms should not be available; then, once I've got the mods maximally
; distributed, the scatter-mods rules should be unavailable and the other
; simplification rules should be available.  The point at which I make this
; switch is when the ``ugly subgoal,'' discussed in the proof sketch, is
; produced.  So my next task was to identify that ugly subgoal.

; By the way, there are various ways to control the switching of theories
; within the prover itself.  See :DOC computed-hints and :DOC
; using-computed-hints-7.  But I chose this method -- of proving some lemmas
; within an encapsulate providing a powerful local theory and then proving my
; main theorems using what's exported from that encapsulate -- because it just
; felt simplest, didn't require me to re-learn how to use computed hints (!),
; and allowed easy experimentation by having two shell buffers, one with
; arithmetic-5/top included and one testing the current encapsulate and
; subsequent theorems, The last point is the most important.  The shell in
; which all of arithmetic-5/top was available could be used to experiment with
; the proofs of lemmas I'd wished I put into the current version of the
; encapsulate.

; Thus, the first version of the encapsulate did not contain rules for cleaning
; up mods.  That early version of the encapsulate just proved the scatter-mods
; rules and the other mod rules I realized I needed for my main theorems.  Then
; I disabled mod and floor and tried to prove mod-sumdigs.  That first attempt
; at mod-sumdigs failed, but produced the ugly subgoal, which was Subgoal
; *1/2.1.1''.  Then, from the ugly subgoal, I formulated a rewrite rule,
; UGLY-LEMMA, that proves the ugly subgoal.

; In creating ugly-lemma, I modified the ugly subgoal in two ways.  I deleted
; the 5th-to-last hypothesis

; (EQUAL (MOD (SUMDIGS ...) D) I).

; which equates a (mod (sumdigs ...) d) term to the variable I introduced by
; floor-mod-elim.  That hypothesis is a remnant of the induction hypothesis and
; has already be used.  Note that (sumdigs ... d) does not appear in the
; conclusion of the ugly subgoal.

; But if the prove attacks that ugly subgoal with the equality intact, the
; prover (stupidly) substitutes the (MOD (SUMDIGS ...) D) for I!  This is
; clearly a bad idea and wrecks the chance for a proof.  So I deleted that
; EQUAL hypothesis (since I also felt it was almost certainly irrelevant now).

; The second way I modified the ugly subgoal to make it an effective rewrite
; rule was to swap the left- and right-hand sides of the conclusion, so that
; the syntactically larger term is rewritten to the syntactically smaller one.

; The result is UGLY-LEMMA, shown below in this script.

; Crucially, I inserted UGLY-LEMMA in the encapsulate BEFORE proving the
; scatter-mods rules.  Had I inserted UGLY-LEMMA after the scatter-mods rules
; its proof would fallen into an infinite marking and unmarking loop caused by
; mod simplification rules in arithmetic-5/top.

; That modified encapsulate is the second version mentioned above.  Right after
; it I disable mod and floor so our rules fire, and then prove mod-sumdigs.

; The rest of the script is easy.

(in-package "ACL2")
(include-book "xdoc/top" :dir :system)

(defxdoc divp-by-casting
  :parents (miscellaneous)
  :short "Generalized version of casting out nines"

  :long "<p>In this book we prove the general theorem that the divisibility of
  @('n') by @('d') can be determined by recursively summing the base-@('b')
  digits of @('n') and then checking that the final sum is divisible by @('d'),
  provided @('n'), @('d') and @('b') are naturals, @('d') and @('b') are
  greater than 1, and @('b') is equivalent to 1 mod @('d').  We then prove
  corollaries that show ``casting out 9s'' and ``casting out 3s'' work
  correctly when decimal (base @('b') = 10) digits are extracted and summed.
  We also show that ``casting out 7s'' works when octal (base @('b') = 8)
  digits are extracted and summed.  Furthermore, we prove that casting out 7s
  can be computed using the logical operations @(tsee logand) and @(tsee ash)
  instead of @(tsee mod) and @(tsee floor).</p>

  <p>The proof of the general theorem requires non-linear arithmetic since
  @('d') and @('b') are variables, whereas in the corollaries @('b') and @('d')
  are constants, e.g., 10 and 3 or 8 and 7.  So use is made of the powerful
  arithmetic book @('arithmetic-5/top').  This book provides rules for
  manipulating many arithmetic primitives, including @('mod') and @('floor')
  and is able to handle many non-linear arithmetic problems heuristically.
  However, (a) @('arithmetic-5/top') does not rewrite @('mod') and @('floor')
  expressions as we wanted them rewritten for this proof, and (b)
  @('arithmetic-5/top') sometimes goes into an infinite loop in its attempt to
  reason about multiplication.  So perhaps the most important lesson to be
  gained from this book is an illustration of one way to manage such problems
  while still using @('arithmetic-5/top') on the problems it can solve.  For
  that reason, we've taken special care to describe how the proof script here
  was created.  For further details, read the extensive comments in the
  @('divp-by-casting') book.</p>")

(encapsulate nil

  (local (include-book "arithmetic-5/top" :dir :system))

  (local (set-default-hints '((nonlinearp-default-hint stable-under-simplificationp
                                                       hist pspv))))
  (defun sumdigs (n b)

; Sum the base b digits of n.  E.g., if b is 10 and n is 987451, then (sumdigs
; n b) = 34.

    (cond ((and (natp b) (< 1 b))
           (cond
            ((zp n) 0)
            (t (+ (mod n b) (sumdigs (floor n b) b)))))
          (t 0)))

; Next I admit sumdigs*.  But the attempt to admit sumdigs* within this
; encapsulate initially looped forever -- because of an inherent flaw in
; arithmetic-5/top -- on a subgoal that suggested the following lemma.  The
; lemma lemma is just the subgoal except two hypotheses have been deleted, as
; noted in comments below.  Arithmetic-5/top loops forever on the lemma if the
; first of these two hypotheses is left in the lemma.  The second deleted
; hypothesis is simply redundant with other hypotheses.  This lemma requires
; non-linear reasoning.

  (defthm LEMMA-FOR-ADMISSION-OF-SUMDIGS*
    (IMPLIES (AND (INTEGERP B)
                  (<= 0 B)
                  (< 1 B)
;                 (< (* N (EXPT B -2)) 1) ; DELETING THIS ALLOWS THE PROOF TO WORK!
                  (INTEGERP N)
;                 (<= 0 N) ; this follows from 1 < B <= N
                  (<= B N))
             (< (+ (MOD N B) (* (/ B) N)) N))
    :rule-classes :linear)

  (defun sumdigs* (n b)

; Recursively sum the base-b digits of n until the sum is less than b.

    (declare (xargs :measure (acl2-count n)))
    (let ((n (nfix n)))
      (cond
       ((and (natp b) (< 1 b))
        (if (< n b)
            n
            (sumdigs* (sumdigs n b) b)))
       (t 0))))

  (defun divp-by-casting (n b d)
; Determine whether n is divisible by d, by recursively summing the base-b
; digits of n.
    (let* ((n (nfix n))
           (b (nfix b))
           (d (nfix d))
           (temp (sumdigs* n b)))
      (equal (mod temp d) 0)))

; At this point I have defined the three functions necessary to state our main
; theorem that divp-by-casting is correct.  But first I test it.

(defthm some-tests
  (and

; -----------------------------------------------------------------
; I can ``cast out 3's'' to determine if a number is divisible by 3, provided
; I extract the digits base 10, because 10 is just one more than a multiple of
; 3.

; Consider casting out 3's to determine whether 334215 is divisible by 3.  I extract
; digits base 10.  I determine that 3|334215 as follows.

; > (divp-by-casting 334215 10 3)
;   > (sumdigs* 334215 10)
;     > (sumdigs 334215 10) = 3+3+4+2+1+5 = 18
;     < 18
;     > (sumdigs 18) = 1+8 = 9
;     < 9
;   < 9
;   then divp-by-casting checks whether (mod 9 3) = 0 and it is, so
; < T

; Similarly, I can check that 3 does not divide 334216, because the
; sumdigs* produces 1 and (mod 1 3) is not 0.

   (let ((d 3)
         (b 10))
     (and (divp-by-casting 334215 b d) ; 3 divides 334215 ==> 3+3+4+2+1+5 = 18 => 1+8 = 9
          (not (divp-by-casting 334216 b d)) ; 3 does not divide 3343
          ))

; -----------------------------------------------------------------
; I can ``cast out 7's'' to determine if a number is divisible by 7, provided
; I extract the digits base 8, because 8 is just one more than a multiple of
; 7.

   (let ((d 7)
         (b 8))                                        ; Note that b = 1*d+1
     (and (divp-by-casting (* 7 31415) b d)            ; 7 divides (* 7 31415)
          (not (divp-by-casting (+ 1 (* 7 31415)) b d)))) ; but not 31416.

; -----------------------------------------------------------------
; But I could also extract the digits base 512, because 73*7+1 = 512.

   (let ((d 7)
         (b 512)) ; Note that b = 73*d+1
     (and (divp-by-casting (* 7 31415) b d)
          (not (divp-by-casting (+ 1 (* 7 31415)) b d)))))
  :rule-classes nil)

; Next I prove the ugly-lemma required to prove the crux lemma, mod-sumdigs.
; This lemma was not in the first version of this encapsulate.  That version
; was used to discover the ugly subgoal that formed the suggestion of this
; lemma.

  (defthm  UGLY-LEMMA
    (IMPLIES
     (AND (INTEGERP J)
          (<= 0 J)
          (INTEGERP N)
          (<= 0 N)
          (< J D)
          (INTEGERP (+ J (* D N)))
          (<= 0 (+ J (* D N)))
          (INTEGERP I)
          (<= 0 I)
          (INTEGERP M)
          (<= 0 M)
          (< I D)
          (INTEGERP (+ I (* D M)))
          (<= 0 (+ I (* D M)))
          (INTEGERP K)
          (<= 0 K)
          (INTEGERP L)
          (<= 0 L)
          (< K D)
          (INTEGERP (+ K (* D L)))
          (<= 0 (+ K (* D L)))
          (< (+ K (* D L)) (+ J (* D N)))
          (<= 0
              (+ K (* D L)
                 (* I J)
                 (* I D N)
                 (* J D M)
                 (* D M D N)))
          (< 1 (+ J (* D N)))
          (< 0
             (+ K (* D L)
                (* I J)
                (* I D N)
                (* J D M)
                (* D M D N)))
;         (EQUAL (MOD (SUMDIGS (+ I (* D M)) (+ J (* D N))) ; deleted hyp from
;                     D)                                    ; ugly subgoal
;                I)
          (INTEGERP D)
          (<= 0 D)
          (< 1 D)
          (EQUAL (MOD (+ -1 J (* D N)) D) 0))
     (EQUAL (MOD (+ (MOD K D)                               ; swapped equality
                    (MOD (+ (MOD (* (MOD I D) (MOD J D)) D) ; from ugly subgoal
                            (MOD (+ (MOD (* (MOD D D) (MOD L D)) D)
                                    (MOD (* (MOD J D)
                                            (MOD (* (MOD D D) (MOD M D)) D))
                                         D))
                                 D))
                         D))
                 D)
            (MOD (+ (MOD I D) (MOD K D)) D))))

; Now I prove the other lemmas I'll need.

  (defthm scatter-mods

; This is really four rules.  Note the syntaxp hypothesis that uses (mod ... d)
; as a marker that prevents the firing of the rule.

    (and (implies (and (syntaxp (or (variablep x)
                                    (fquotep x)
                                    (not (eq (ffn-symb x) 'mod))
                                    (not (equal (fargn x 2) d))))
                       (force (natp x))
                       (force (natp y))
                       (not (zp d)))
                  (equal (mod (+ x y) d)
                         (mod (+ (mod x d) y) d)))

         (implies (and (syntaxp (or (variablep y)
                                    (fquotep y)
                                    (not (eq (ffn-symb y) 'mod))
                                    (not (equal (fargn y 2) d))))
                       (force (natp x))
                       (force (natp y))
                       (not (zp d)))
                  (equal (mod (+ x y) d)
                         (mod (+ x (mod y d)) d)))

         (implies (and (syntaxp (or (variablep x)
                                    (fquotep x)
                                    (not (eq (ffn-symb x) 'mod))
                                    (not (equal (fargn x 2) d))))
                       (force (natp x))
                       (force (natp y))
                       (not (zp d)))
                  (equal (mod (* x y) d)
                         (mod (* (mod x d) y) d)))

         (implies (and (syntaxp (or (variablep y)
                                    (fquotep y)
                                    (not (eq (ffn-symb y) 'mod))
                                    (not (equal (fargn y 2) d))))
                       (force (natp x))
                       (force (natp y))
                       (not (zp d)))
                  (equal (mod (* x y) d)
                         (mod (* x (mod y d)) d)))))

; These are the other facts about mod that I'll need.  All the facts are
; trivial consequences of often more general rules in arithmetic-5/top.  (Note
; that I'm concerned here only with operations on natural numbers, but the more
; general rules often deal with a rationals.  By proving these rules here and
; exporting them I make them available outside the encapsulate (where the more
; general rules are unavailable).

  (defthm mod-mod
    (equal (mod (mod x y) y) (mod x y)))

  (defthm integerp-mod
    (implies (and (integerp x)
                  (integerp y))
             (integerp (mod x y)))
    :rule-classes :type-prescription)

  (defthm nonnegative-mod
    (implies (and (<= 0 x)
                  (<= 0 y))
             (<= 0 (mod x y)))
    :rule-classes :type-prescription)

  (defthm mod-<-d
    (implies (and (natp x)
                  (not (zp d)))
             (< (mod x d) d))
    :rule-classes (:generalize))

  (defthm nonnegative-floor
    (implies (and (<= 0 x)
                  (<= 0 y))
             (<= 0 (floor x y)))
    :rule-classes :type-prescription)

  (defthm natp-floor-mod-elim
    (implies (natp x)
             (equal (+ (mod x y) (* y (floor x y)))
                    x))
    :rule-classes ((:rewrite) (:elim)))

  )

; That concludes the encapsulate and the proofs of the lemmas necessary for our
; general theorem.

; Now that we're outside the encapsulate but have the foregoing rules (but not
; the more general rules of arithmetic-5/top), disable mod and floor so our
; rules will find their targets.

(in-theory (disable mod floor))

; The crux of the whole proof:
(defthm mod-sumdigs
  (implies (and (natp n)
                (natp b)
                (< 1 b)
                (natp d)
                (< 1 d)
                (equal (mod (- b 1) d) 0))
           (equal (mod (sumdigs n b) d)
                  (mod n d))))

; It follows easily that sumdigs* preserves the mod.

(defthm mod-sumdigs*
  (implies (and (natp n)
                (natp b)
                (< 1 b)
                (natp d)
                (< 1 d)
                (equal (mod (- b 1) d) 0))
           (equal (mod (sumdigs* n b) d)
                  (mod n d))))

; and returns an answer below b.

(defthm sumdigs*-below-b
  (implies (and (natp n)
                (natp b)
                (< 1 b))
           (and (<= 0 (sumdigs* n b))
                (< (sumdigs* n b) b)))
  :rule-classes :linear)

; And here is the main theorem.

(defthm divp-by-casting-correct
  (implies (and (natp n)
                (natp b)
                (< 1 b)
                (natp d)
                (< 1 d)
                (equal (mod (- b 1) d) 0))
           (equal (divp-by-casting n b d)
                  (equal (mod n d) 0))))

; -----------------------------------------------------------------
; Here is the correctness of ``casting out 9s''

(defthm divp9-correct
  (implies (natp n)
           (equal (divp-by-casting n 10 9)
                  (equal (mod n 9) 0))))

; -----------------------------------------------------------------
; Here is the instance of the algorithm for deciding divibility by 3
; ``without mod'' -- if one imagines a human just reading off the base-10
; digits of n and of the subsequent sums of digits.

(defun divp3 (n)  ; casting out 3s
  (let* ((n (nfix n))
         (temp (sumdigs* n 10)))
    (if (member temp '(0 3 6 9)) t nil)))

(defthm enumerate-the-interval-below-10
  (implies (natp temp)
           (iff (< temp 10)
                (member temp '(0 1 2 3 4 5 6 7 8 9))))
  :rule-classes nil)

(defthm divp3-correct
  (implies (natp n)
           (equal (divp3 n)
                  (equal (mod n 3) 0)))
  :hints (("Goal"
           :use ((:instance enumerate-the-interval-below-10
                            (temp (sumdigs* n 10)))
                 (:instance mod-sumdigs*
                            (n n)
                            (b 10)
                            (d 3)))
           :in-theory (disable mod-sumdigs*))))

; -----------------------------------------------------------------
; And here is the algorithm for deciding divibility by 7 by extracting octal
; digits with logand and ash.  I need facts from arithmetic-5 which I didn't
; prove and export earlier (because I waw focused on the general theorem, not
; the specific case of d=7).

(encapsulate nil
  (local (include-book "arithmetic-5/top" :dir :system))
  (defun sumdigs7 (n)
    (if (zp n)
        0
        (+ (logand n 7)
           (sumdigs7 (ash n -3)))))

  (defthm sumdigs7-is-sumdigs
    (implies (natp n)
             (equal (sumdigs7 n)
                    (sumdigs n 8))))

  (defun sumdigs7* (n)
    (let ((n (nfix n)))
      (if (< n 8)
          n
          (sumdigs7* (sumdigs7 n)))))

  (defthm sumdigs7*-is-sumdigs*
    (implies (natp n)
             (equal (sumdigs7* n)
                    (sumdigs* n 8)))))

(defun divp7 (n)
  (let* ((n (nfix n))
         (temp (sumdigs7* n)))
    (or (= temp 0)
        (= temp 7))))

(defthm enumerate-the-interval-below-8
  (implies (natp temp)
           (iff (< temp 8)
                (member temp '(0 1 2 3 4 5 6 7))))
  :rule-classes nil)

(defthm divp7-correct
  (implies (natp n)
           (equal (divp7 n)
                  (equal (mod n 7) 0)))
  :hints (("Goal"
           :use ((:instance enumerate-the-interval-below-8
                            (temp (sumdigs* n 8)))
                 (:instance mod-sumdigs*
                            (n n)
                            (b 8)
                            (d 7)))
           :in-theory (disable mod-sumdigs*))))
