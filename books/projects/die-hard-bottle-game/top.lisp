; Copyright (C) 2005, Regents of the University of Texas
; Written by J Strother Moore
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; (certify-book "die-hard-bottle-game-summary")

; The Die Hard Bottle Game
; J Strother Moore
; December, 2005
; Edinburgh, Scotland

; About this Book

; This exercise was inspired by the 1995 movie, Die Hard with a Vengeance, in
; which the characters John McClane and Zeus Carver (played by Bruce Willis and
; Samuel L. Jackson) have to solve a puzzle: Given a 5 gallon water bottle and
; a 3 gallon water bottle and an unlimited supply of water, measure out exactly
; 4 gallons.  I happened to see the movie (again) on TV in 2005 and started
; thinking about the obvious generalization of the game: given any two
; integer-sized bottles, what amounts can you exactly measure out?  The answer:
; any integer multiple of the gcd of the capacities of the two bottles, up to
; the capacity of the larger bottle.

; In this file I show my analysis of the general case, using ACL2 to prove the
; theorems I conjecture.  I formalize the acts of filling a bottle, emptying a
; bottle, and pouring water from one bottle to the other.  I think of these as
; ``moves'' in a game or ``operations'' in a simple operational semantics.  I
; define the semantics as the function ``play'', which takes a list of moves (here
; called a ``program'') and an initial state and returns the final state.  I
; then write a function that generates a sequence of these moves to achieve a
; given goal, e.g., produce 4 gallons in the larger bottle, and I prove it
; correct.  Along the way I prove that every possible sequence produces an
; integral multiple of the gcd, thus implicitly establishing that it is
; impossible to measure, say, 3 gallons given bottles of capacities 6 and 4.

; This work relies heavily on ACL2 work by John Cowles to formalize
; within ACL2 the fundamental properties of mod and gcd, in his book
; which comes with the ACL2 distribition: books/arithmetic/mod-gcd.

; This file is just a wrapper.  The real work, including many rather ugly
; lemmas, may be found in the books "work" and "my-mod-gcd".

; Cowles' book deals with nonneg-int-mod, a natural number version of mod which
; can't be given the name ``mod'' because that is defined in CLTL and operates
; on all real/rationals (in ACL2(r)/ACL2).  Key properties of nonneg-int-mod
; proved by Cowles include:

; (implies (and (natp x)
;               (natp y)
;               (natp z)
;               (equal (nonneg-int-mod x n)      ;     x = y (mod n)
;                      (nonneg-int-mod y n)))    ; ->
;          (equal (nonneg-int-mod (+ x z) n)     ;   x+z = y+z (mod n)
;                 (nonneg-int-mod (+ y z) n)))

; and

; (implies (and (natp x)
;               (natp y)
;               (natp z)
;               (natp n)
;               (< 0 n)
;               (equal (nonneg-int-mod x n)      ;     x = y (mod n)
;                      (nonneg-int-mod y n)))    ; ->
;          (equal (nonneg-int-mod (* x z) n)     ; x*z = y*z (mod n)
;                 (nonneg-int-mod (* y z) n)))

; Note: These are not ACL2 :CONGRUENCE rules because of (a) the presence of n
; in the ``equivalence relation'' x = y (mod n), and (b) the hypotheses.
; Problem (a) can be overcome by constraining a non-zero constant (n) and
; appealing later to functional instantiation.  Problem (b) would require
; eliminating + and * and using natural number versions of these functions.

; Cowles' book also deals with nonneg-int-gcd, the natural number version of
; the CLTL gcd function.  Cowles proves three important facts about
; (nonneg-int-gcd p q):

; (1) It divides both p and q.

; (2) It is the largest natural number that divides them both.

; (3) There exists integers a and b such that
;     (nonneg-int-gcd p q) = a*p + b*q.

; Acknowlegements and Historical Notes:

; I am very grateful for John Cowles' work on mod and gcd and his help,
; recounted in my-mod-gcd.lisp, on the particular lemma I use.

; I actually did this work in December, 2005.  I subsequently used it in a
; challenge problem for my graduate class on Recursion and Induction in the
; Spring of 2006.  I did not enter it into the ACL2 Community Book Repository
; until 2021!  I simply forgot about the book until 2021 when I had occasion to
; think about the problem again and realized I'd never posted my solution.  One
; final confession: I actually don't know if there is a more elegant solution
; or proof of correctness.  This work was done just as an intellectual hobby
; over one Christmas break, without reference to any material found on the web
; or otherwise published (besides John's work on mod and gcd).

; J Moore, March, 2021

; ---------------------------------------------------------------------

(in-package "ACL2")
(include-book "work")

; We define an operational semantics to formalize the game.

; A state has two fields, each of which is a list of length 2.

; ((v0 v1) (c0 c1))

; The vi give the volume of water in each of the two bottles.  The ci give the
; maximum capacity of each of each bottle.  Without loss of generality we adopt
; the convention that c0 is the capacity of the larger bottle, i.e., c0 >= c1.
; But that convention is not part of the model, just how we use the model in
; examples and theorems.  The functions below let me set the volume of bottle
; i, fetch the volume, and fetch the capacity.

(defun set-vol (i v s)
  (update-nth 0 (update-nth i v (nth 0 s)) s))

(defun vol (i s)
  (nth i (nth 0 s)))

(defun cap (i s)
  (nth i (nth 1 s)))

; This game will have three moves:

; (FILL i) - set the volume of bottle i to its max.

; (EMPTY i) - set the volume of bottle i to 0.

; (POUR i j) - pour the contents of bottle i into bottle j, filling
;              j just to its capacity or emptying bottle i, whichever
;              occurs first.

(defun arg1 (inst) (nth 1 inst))

(defun arg2 (inst) (nth 2 inst))

(defun execute-FILL (inst s)
  (let ((i (arg1 inst)))
    (set-vol i (cap i s) s)))

(defun execute-EMPTY (inst s)
  (let ((i (arg1 inst)))
    (set-vol i 0 s)))

(defun execute-POUR (inst s)
  (let ((i (arg1 inst))
        (j (arg2 inst)))
    (set-vol i (max 0
                    (- (vol i s) (- (cap j s) (vol j s))))
             (set-vol j (min (cap j s)
                             (+ (vol i s) (vol j s)))
                      s))))

(defun do-inst (inst s)
  (if (equal (car inst) 'FILL)
      (execute-FILL inst s)
    (if (equal (car inst) 'EMPTY)
        (execute-EMPTY inst s)
      (if (equal (car inst) 'POUR)
          (execute-POUR inst s)
        s))))

(defun play (insts s)
  (if (endp insts)
      s
    (play (cdr insts)
          (do-inst (car insts) s))))

; Starting with state ((0 0) (5 3)), meaning two empty bottles with capacities
; 5 and 3 gallons, respectively, run the program below to produce 4 gallons in
; the larger bottle.  The column to the right of the moves shows the volumes of
; the two bottles after the move.

(defthm example-1
  (equal (play '((FILL 0)   ; (5 0)
                 (POUR 0 1) ; (2 3)
                 (EMPTY 1)  ; (2 0)
                 (POUR 0 1) ; (0 2)
                 (FILL 0)   ; (5 2)
                 (POUR 0 1) ; (4 3)
                 )
               '((0 0) (5 3)))
         '((4 3) (5 3)))
  :rule-classes nil)

(defun inv (s)
  (and (natp (cap 0 s))
       (natp (cap 1 s))
       (< 0 (cap 0 s))
       (< 0 (cap 1 s))
       (natp (vol 0 s))
       (natp (vol 1 s))
       (<= (vol 0 s) (cap 0 s))
       (<= (vol 1 s) (cap 1 s))
       (equal (nonneg-int-mod (vol 0 s)
                              (nonneg-int-gcd (cap 0 s) (cap 1 s)))
              0)
       (equal (nonneg-int-mod (vol 1 s)
                              (nonneg-int-gcd (cap 0 s) (cap 1 s)))
              0)))

(defthm inv-do-inst
  (implies (and (inv s)
                (well-formed-instruction inst))
           (inv (do-inst inst s))))

(defthm inv-play
  (implies (and (inv s)
                (well-formed-program lst))
           (inv (play lst s))))

(defthm all-programs-produce-gcd-multiples
  (implies (and (natp c0)
                (natp c1)
                (< 0 c0)
                (< 0 c1)
                (well-formed-program lst))
           (let ((final-state (play lst (initial-state c0 c1)))
                 (gcd (nonneg-int-gcd c0 c1)))
             (and
              (equal (nonneg-int-mod (vol 0 final-state) gcd) 0)
              (equal (nonneg-int-mod (vol 1 final-state) gcd) 0)))))

; Below is a program that repeatedly pours bottle 0 into bottle 1,
; preserving the "residuals" in bottle 0 on each cycle.  Start with c0
; = 5 and c1 = 3, with both bottles empty.

; step inst      (v0 v1)     v0

;  1 (EMPTY 1)   (0 0)       <- 0
;  2 (FILL 0)    (5 0)
;  3 (POUR 0 1)  (2 3)
;  4 (EMPTY 1)   (2 0)       <- 2
;  5 (POUR 0 1)  (0 2)
;  6 (FILL 0)    (5 2)
;  7 (POUR 0 1)  (4 3)
;  8 (EMPTY 1)   (4 0)       <- 4
;  9 (POUR 0 1)  (1 3)
; 10 (EMPTY 1)   (1 0)       <- 1
; 11 (POUR 0 1)  (0 1)
; 12 (FILL 0)    (5 1)
; 13 (POUR 0 1)  (3 3)
; 14 (EMPTY 1)   (3 0)       <- 3
; 15 END         (3 0)

; This program produces every integer between 0 and c0.

; What is the pattern?

;  1 (EMPTY 1)   (0 0)        <- 0 = 5*3 mod 5
;  2 (FILL 0)    (5 0)
;  3 (POUR 0 1)  (2 3)
;  4 (EMPTY 1)   (2 0)        <- 2 = 4*3 mod 5
;  5 (POUR 0 1)  (0 2)
;  6 (FILL 0)    (5 2)
;  7 (POUR 0 1)  (4 3)
;  8 (EMPTY 1)   (4 0)        <- 4 = 3*3 mod 5
;  9 (POUR 0 1)  (1 3)
; 10 (EMPTY 1)   (1 0)        <- 1 = 2*3 mod 5
; 11 (POUR 0 1)  (0 1)
; 12 (FILL 0)    (5 1)
; 13 (POUR 0 1)  (3 3)
; 14 (EMPTY 1)   (3 0)        <- 3 = 1*3 mod 5
; 15 END         (3 0)


; Basic Blocks

;  1 (EMPTY 1)   (0 0)        <- 0 = 5*3 mod 5

;  2 (FILL 0)    (5 0)
;  3 (POUR 0 1)  (2 3)
;  4 (EMPTY 1)   (2 0)        <- 2 = 4*3 mod 5

;  5 (POUR 0 1)  (0 2)
;  6 (FILL 0)    (5 2)
;  7 (POUR 0 1)  (4 3)
;  8 (EMPTY 1)   (4 0)        <- 4 = 3*3 mod 5

;  9 (POUR 0 1)  (1 3)
; 10 (EMPTY 1)   (1 0)        <- 1 = 2*3 mod 5

; 11 (POUR 0 1)  (0 1)
; 12 (FILL 0)    (5 1)
; 13 (POUR 0 1)  (3 3)
; 14 (EMPTY 1)   (3 0)        <- 3 = 1*3 mod 5

; 15 END         (3 0)

(defun play2 (instructions s)
  (mv instructions
      (play instructions s)))

; This function generates a "basic block" which is the code between
; successive "<-" landmarks in the displays above.  A basic block just
; does POURS 0 into 1, appropriately FILLing 0, if it is initially
; empty.  However, if the POUR empties 0 without filling 1, we refill
; 0 and do another POUR.  The block always concludes with EMPTYing 1.

(defun basic-block (s)
  (mv-let
   (instructions1 s1)
   (if (zp (vol 0 s))
       (play2 '((FILL 0)) s)
     (play2 nil s))
   (mv-let
    (instructions2 s2)
    (play2 '((POUR 0 1)) s1)
    (mv-let
     (instructions3 s3)
     (if (equal (vol 1 s2) (cap 1 s2))
         (play2 '((EMPTY 1)) s2)
       (play2 '((FILL 0)
                (POUR 0 1)
                (EMPTY 1))
              s2))
     (mv (append instructions1
                 instructions2
                 instructions3)
         s3)))))

(defthm basic-block-example-1
  (equal (basic-block (initial-state 5 3))
         (mv '((FILL 0)
               (POUR 0 1)
               (EMPTY 1))
             '((2 0) (5 3))))
  :rule-classes nil)

(defthm basic-block-example-2
  (equal (basic-block '((2 0) (5 3)))
         (mv '((POUR 0 1)
               (FILL 0)
               (POUR 0 1)
               (EMPTY 1))
             '((4 0) (5 3))))
  :rule-classes nil)

(defthm basic-block-correct
  (implies (and (natp c0)
                (natp c1)
                (< 0 c0)
                (< 0 c1)
                (<= c1 c0)
                (natp k)
                (<= c1 k))
           (equal (play
                   (mv-nth 0
                           (basic-block ; (mv-nth 0 ...) = (car ...)
                            (list
                             (list (nonneg-int-mod k c0) 0)
                             (list c0 c1))))
                   (list (list (nonneg-int-mod k c0) 0)
                         (list c0 c1)))
                  (list (list (nonneg-int-mod (- k c1) c0) 0)
                        (list c0 c1))))
  :rule-classes nil)


(defun make-prog1 (i s)

; Let v0, v1, c0 and c1 be the obvious components of s.  Assume c0 >= c1
; that v1 is 0, and that v0 is (nonneg-int-mod (* n c1) c0), for some
; n.  We create a program that will leave

; (nonneg-int-mod (* (- n i) c1) c0)

; in the bottle 0.  It will leave bottle 1 empty.

  (if (zp i)
      nil
    (mv-let (instructions s1)
            (basic-block s)
            (append instructions (make-prog1 (- i 1) s1)))))

(defthm make-prog1-is-correct
  (implies (and (natp n)
                (< 0 n)
                (natp i)
                (<= i n)
                (natp c0)
                (natp c1)
                (< 0 c0)
                (< 0 c1)
                (<= c1 c0))
           (equal (play
                   (make-prog1 i
                               (list (list (nonneg-int-mod (* n c1) c0) 0)
                                     (list c0 c1)))
                   (list (list (nonneg-int-mod (* n c1) c0) 0)
                         (list c0 c1)))
                  (list (list (nonneg-int-mod (* (- n i) c1) c0) 0)
                         (list c0 c1))))
  :hints (("Goal" :use make-prog1-correct)))


(defun make-prog (j c0 c1)

; Let gcd be the gcd of the two capacities, c0 and c1, in s.  Assume without
; loss of generality that c0 >= c1 and that both bottles are initially empty.
; Then we generate a program that leaves (nonneg-int-mod (* j c1) c0) in bottle
; 0.  It leaves bottle 1 empty.

  (cons '(EMPTY 1)
        (make-prog1 (- (floor c0 (nonneg-int-gcd c0 c1))
                       (nonneg-int-mod j (floor c0 (nonneg-int-gcd c0 c1))))
                    (initial-state c0 c1))))

(defthm make-prog-is-correct
  (implies (and (natp c0)
                (natp c1)
                (< 0 c0)
                (< 0 c1)
                (<= c1 c0)
                (natp j))
           (equal (vol 0 (play (make-prog j c0 c1)
                               (initial-state c0 c1)))
                  (nonneg-int-mod (* j c1) c0)))
  :hints (("Goal" :use make-prog-correct))
  :rule-classes nil)

; I will soon define (gcd-prog p q) to generate a Bottle Game program
; to measure out the gcd of p and q.

; (Gcd-prog p q) will be defined as a call of (make-prog j p q),
; with a creative choice of j.  To understand the choice of j, I
; give the proof that gcd-prog is correct.

; (defthm exists-gcd-prog
;   (implies (and (natp p)
;                 (natp q)
;                 (< 0 p)
;                 (< 0 q)
;                 (< q p))
;            (equal (vol 0 (play (gcd-prog p q)
;                                (initial-state p q)))
;                   (nonneg-int-gcd p q))))

; Proof:

; Let
; g = (nonneg-int-gcd p q)
; c = (nonnegative-integer-quotient p g)
; d = (nonnegative-integer-quotient q g)
; Thus,
; p = (* c g)
; q = (* d g)

; We know that (make-prog j p q) computes
; (nonneg-int-mod (* j q) p)
; =
; (nonneg-int-mod (* j d g) (* c g))
; =
; (* g (nonneg-int-mod (* j d) c))

; We would be done if we could show that for the value of j used
; in gcd-prog, (nonneg-int-mod (* j d) c) = 1.

; Now two important observations.  The first is proved in
; John Cowles' book "books/arithmetic/mod-gcd.

; Theorem: The gcd of two naturals can be expressed as a linear
; combination of the two naturals.

(defthm
  Linear-combination-for-nonneg-int-gcd
  (equal (nonneg-int-gcd x y)
         (+ (* (nfix x)
               (nonneg-int-gcd-multiplier1 x y))
            (* (nfix y)
               (nonneg-int-gcd-multiplier2 x y)))))

; Thus, let

; a = (nonneg-int-gcd-multiplier1 c d)
; b = (nonneg-int-gcd-multiplier2 c d)

; Hence:

; (nonneg-int-gcd c d) = a*c + b*d

; The second important observation is that c and d are relatively
; prime.  This follows from the fact that gcd is the LARGEST common
; divisor (which is also proved in Cowles' book).

; Thus, since
; g = (nonneg-int-gcd p q)
; c = (nonnegative-integer-quotient p g)
; d = (nonnegative-integer-quotient q g)

; We can conclude that:

; (nonneg-int-gcd c d) = 1

; Cowles' definition of nonneg-int-gcd deals only with natural
; numbers.  But the linear combination theorem produces integral
; values of a and b (and they are always of opposite sign).

; However, additive inverses may be found in the ring mod n.
; Below, (fixnonneg a c) takes an integer a and returns the
; equivalent natural in the ring mod c.   For example, in the
; ring mod 5, -2 is equivalent to 3.  (fixnonneg -2 5) = 3.

; Thus

; 1
; =
; (nonneg-int-mod (+ (* (fixnonneg a c) c)
;                    (* (fixnonneg b c) d))
;                 c)
; =
; (nonneg-int-mod (* (fixnonneg b c) d)
;                 c)
; Thus, in gcd-prog we select j = (* (fixnonneg b c) d)

(defun gcd-prog (c0 c1)
  (make-prog
   (fixnonneg (nonneg-int-gcd-multiplier1
               (nonnegative-integer-quotient c1 (nonneg-int-gcd c0 c1))
               (nonnegative-integer-quotient c0 (nonneg-int-gcd c0 c1)))
              (nonnegative-integer-quotient c0 (nonneg-int-gcd c0 c1)))
   c0 c1))

; Q.E.D.

(defun gcd-prog! (p q)
  (if (equal p q)
      '((FILL 0)
        (EMPTY 1))
    (gcd-prog p q)))

(defthm exists-gcd-prog
  (implies (and (natp p)
                (natp q)
                (< 0 p)
                (< 0 q)
                (<= q p))
           (equal (vol 0 (play (gcd-prog! p q)
                               (initial-state p q)))
                  (nonneg-int-gcd p q))))

; Statistics:

; defuns                        33
; defthms                       88
; Hints (actually, clause ids)  49!
