; Copyright (C) 2013, Regents of the University of Texas
; Written by Matt Kaufmann and J Strother Moore, April 2, 2003
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; A Proof of the Correctness of a Towers of Hanoi Program

; Abstract

; In this book we prove the correctness of a function that
; purportedly generates moves to play the Towers of Hanoi game
; for an arbitrary number of disks.

; This is Moore's translation into ACL2 of Matt Kaufmann's
; Pc-Nqthm solution of this problem.  Matt devised his solution
; as an illustration of PC-Nqthm.  This proof is entirely
; rule-based.  But the elegance of Matt's solution was in his
; statement of the problem and of the main lemma, h-lemma.

; To certify this book, execute:

#|
(defpkg "HANOI"
    (set-difference-equal
     (union-eq *acl2-exports*
               *common-lisp-symbols-from-main-lisp-package*)
     '(PUSH POP GET)))

(certify-book "hanoi" 1)

JSM
August, 2004
|#

(in-package "HANOI")

(defun mem (e x)
  (if (consp x)
      (if (equal e (car x))
          x
        (mem e (cdr x)))
    nil))

(defun app (x y)
  (if (consp x)
      (cons (car x)
          (app (cdr x) y))
    y))

(defun del (e x)
  (if (consp x)
      (if (equal e (car x))
          (cdr x)
        (cons (car x) (del e (cdr x))))
    nil))

(defun perm (x y)
  (if (consp x)
      (and (mem (car x) y)
           (perm (cdr x)
                 (del (car x) y)))
    (not (consp y))))

; Note: I will use the perm expression (perm (list a b c) '(0 1 2)) to
; characterize the peg numbers, a, b, and c.  But I will then use the
; lemma to rewrite the perm into a conjunction of facts that give us
; all we need without "revealing" the identities of a, b, and c.  If
; we allow the perm to expand, the proof of h-lemma takes 40 times
; longer.

(defthm perm-opener
  (equal (perm (list a b c) '(0 1 2))
         (and (integerp a) (<= 0 a) (<= a 2)
              (integerp b) (<= 0 b) (<= b 2)
              (integerp c) (<= 0 c) (<= c 2)
              (not (equal a b))
              (not (equal a c))
              (not (equal b c)))))

(defthm app-assoc
  (equal (app (app a b) c) (app a (app b c))))

(defthm app-right-id
  (implies (true-listp x)
           (equal (app x nil) x)))

(defun get (n x)
  (if (zp n) (car x) (get (- n 1) (cdr x))))

(defun put (v n x)
  (if (zp n) (cons v (cdr x)) (cons (car x) (put v (- n 1) (cdr x)))))

(defthm get-put
  (implies (and (natp i)
                (natp j))
           (equal (get i (put v j x))
                  (if (equal i j) v (get i x)))))

(defthm put-get
  (implies (and (equal x (get n s))
                (natp n)
                (< n (len s)))
           (equal (put x n s) s)))

(defthm put-put-1
  (implies (and (natp i)
                (natp j)
                (not (equal i j)))
           (equal (put v i (put u j s))
                  (put u j (put v i s))))
  :rule-classes ((:rewrite :loop-stopper ((i j)))))

(defthm put-put-2
  (equal (put v i (put w i s))
         (put v i s)))

(defthm true-listp-put
  (implies (and (natp n)
                (< n (len x)))
           (equal (true-listp (put v n x))
                  (true-listp x))))

(defthm len-put
  (implies (and (natp n)
                (< n (len x)))
           (equal (len (put v n x))
                  (len x))))


(defun push (e x) (cons e x))
(defun pop (x) (cdr x))
(defun top (x) (car x))

(defun h (i j k n)
 (if (zp n)
     nil
     (app (h i k j (- n 1))
          (cons (list 'MOVE i k)
                (h j i k (- n 1))))))

(defun Hanoi (n) (h 0 1 2 n))




(defun a (m) (get 1 m))
(defun b (m) (get 2 m))




; Is m a syntactically well-formed move?

(defun legal-syntaxp (m)
  (and (true-listp m)
       (equal (car m) 'MOVE)
       (equal (len m) 3)
       (mem (a m) '(0 1 2))
       (mem (b m) '(0 1 2))
       (not (equal (a m) (b m)))))

; Is m a legal move in state s?

(defun legal-movep (m s)
  (and (legal-syntaxp m)
       (consp (get (a m) s))
       (if (consp (get (b m) s))
           (< (car (get (a m) s))
              (car (get (b m) s)))
         t)))

; Let's assume that s is a good state, that a and b are distinct
; pegs, and that it is legal to move the top element of tower a
; to tower b.  This function returns the state produced by making
; that move.

(defun do-move (m s)
  (let ((stacka (get (a m) s))
        (stackb (get (b m) s)))
    (put (pop stacka) (a m)
     (put (push (top stacka) stackb) (b m)
                 s))))

; The Hanoi game generates a list of moves, where each move is of
; the form (MOVE a b), where a and b are distinct pegs.

(defun play (moves s)

; Moves is a list of moves.  Each move is of the form (MOVE a b),
; where a and b are distinct pegs.  Play returns the state
; produced by doing each of the moves, in turn, to s.  If an
; illegal move occurs, NIL is returned.  Otherwise, the final
; state (which is never nil) is returned.

  (if (consp moves)
      (if (legal-movep (car moves) s)
          (play (cdr moves)
                (do-move (car moves)
                         s))
          nil)
      s))

(defun tower (n)
  (if (zp n)
      nil
    (app (tower (- n 1)) (list n))))

(defthm examples
  (and (equal (play (Hanoi 7) (list (tower 7) nil nil))
              (list nil nil (tower 7)))
       (equal (play (Hanoi 2) (list (tower 3) nil '(4)))
              '((3) nil (1 2 4)))
       (equal (play (Hanoi 3) '((1 2 3) (0) nil))
              nil)))

; ---------------------------------------------------------------
; Lemmas

(defthm true-listp-tower
  (true-listp (tower n)))

(defthm play-app
  (equal (play (app moves1 moves2) s)
         (play moves2 (play moves1 s))))

; ----------------------------------------------------------------
; The General Lemma

; Here is the generalized form of the correctness theorem.

(defun big-tops (a b c n s)
  (and (or (endp (get a s))
           (< n (car (get a s))))
       (or (endp (get b s))
           (< n (car (get b s))))
       (or (endp (get c s))
           (< n (car (get c s))))))

; Note: I could have used 0, 1, and 2 for a, b, and c.  But instead I
; passed them in.  The reason is that in my proof of h-lemma below I
; explicitly avoid revealing that a, b, and c are those particular
; numbers.

; The key lemma is called h-lemma, below, and the next function
; definition describes the induction hint needed to prove it.

; Look at h-lemma first.

; The conclusion is

; (equal (play (h a b c n)                           ;[lhs]
;              (put (app (tower n) (get a s)) a s))
;        (put (app (tower n) (get c s)) c s)) ;[rhs]

; Consider the lhs

; (play (h a b c n)
;       (put (app (tower n) (get a s)) a s))

; (h a b c n) will open to

; (app (h a c b (- n 1))
;      (cons (list 'MOVE a c)
;            (h b a c (- n 1))))

; and because of play-app and the definition of play,

; lhs
; =
; (play (h b a c (- n 1))
;       (do-move (list 'MOVE a c)
;                (play (h a c b (- n 1))
;                      (put a
;                           (app (tower n) (get a s))
;                           s))))

; Expand (tower n) to (app (tower (- n 1)) (list n)) and associate
; and you get

; lhs
; =
; (play (h b a c (- n 1))                      ; [outer play]
;       (do-move (list 'MOVE a c)
;                (play (h a c b (- n 1))       ; [inner play]
;                      (put (app (tower (- n 1))
;                                (cons n (get a s)))
;                           a
;                           s))))

; Consider the [inner play] term.  We can provide an induction
; hyp that tells us about this term!  Here is the lhs of our
; theorem again.

; (play (h a b c n)
;       (put (app (tower n)
;                 (get a s))
;            a
;            s))

; Instantiate it by a := a, b := c, c := b, n := (- n 1), and
; s := (put (cons n (get a s)) a s)
; and you get:

; (play (h a c b (- n 1))
;       (put (app (tower (- n 1))
;                 (get a
;                      (put (cons n (get a s))
;                           a
;                           s)))
;            a
;            (put (cons n (get a s))
;                 a
;                 s)))
;
; Now that is not quite what we want.  But simplify it, first by
; simplifying the (get a (put ... a ...)):

; (play (h a c b (- n 1))
;       (put (app (tower (- n 1))
;                 (cons n (get a s)))
;            a
;            (put (cons n (get a s))
;                 a
;                 s)))

; And then by simplifying (put ... a ... (put ... a ...))

; (play (h a c b (- n 1))
;       (put (app (tower (- n 1))
;                 (cons n (get a s)))
;            a
;            s))

; And voila, it's [inner play].

; The induction hypothesis tells us [inner play] is equal to

; (put (app (tower (- n 1))
;           (get b
;                (put (cons n (get a s)) a s)))
;      b
;      (put (cons n (get a s)) a s))

; which we can simplify, using get and put facts, to

; (put (app (tower (- n 1))
;           (get b s))
;      b
;      (put (cons n (get a s)) a s))

; So, using this hypothesis, we get

; lhs
; =
; (play (h b a c (- n 1))                      ; [outer play]
;       (do-move (list 'MOVE a c)
;                (put (app (tower (- n 1)) (get b s))
;                     b
;                     (put (cons n (get a s))
;                          a
;                          s))))

; Now do the MOVE and we get
;
; lhs
; =
; (play (h b a c (- n 1))
;       (put (cons n (get c s))
;            c
;            (put (app (tower (- n 1)) (get b s))
;                 b
;                 s)))

; (Again, using get and put simplifications.)

; Commute the put on c and b (another lemma about these
; important functions)

; lhs
; =
; (play (h b a c (- n 1))
;       (put (app (tower (- n 1)) (get b s))
;            b
;            (put (cons n (get c s))
;                 c
;                 s)))

; Does this look familiar?  We can supply an induction hypothesis
; to tell us what this term is, too!
;
; Here is the [lhs] of our theorem, again:

; (play (h a b c n)
;       (put (app (tower n)
;                 (get a s))
;            a
;            s))

; Instantiate it with a := b, b := a, c := c, n := (- n 1) and
; s := (put (cons n (get c s)) c s)
; and simplify.

; So now replace this with the rhs of the second induction
; hypothesis:

; lhs
; =
; (put (app (tower (- n 1))
;           (get c (put (cons n (get c s)) c s)))
;      c
;      (put (cons n (get c s)) c s))

; and simplify as usual

; lhs
; =
; (put (app (tower (- n 1))
;           (cons n (get c s)))
;      c
;      s)
; =
; (put (app (tower n)
;           (get c s))
;      c
;      s)
; = rhs!

; So you can see we need two induction hypotheses, as described by
; the two substitutions:

; a := a, b := c, c := b, n := (- n 1),
; s := (put (cons n (get a s)) a s)

; a := b, b := a, c := c, n := (- n 1),
; s := (put (cons n (get c s)) c s)

; That is what is coded below.

(defun induction-hint (a b c n s)
  (if (zp n)
      (list a b c n s)
    (list (induction-hint a c b (- n 1)
                          (put (push n (get a s)) a s))
          (induction-hint b a c (- n 1)
                          (put (push n (get c s)) c s)))))

; So here is h-lemma, the crux of the proof.  The proof is
; tedious because we have to deal with the preservation of
; the big-tops hypothesis under the instantiations and
; the constant pathological possibilities that a = b or some
; other a = 4 or some other nonsense that prevents the
; nth and update-nth rules from applying.  These are dealt with
; by brute force:  just consider the possible values of
; a, b, and c and do the inductive argument for each one.

; Time:  14.10 seconds (prove: 12.85, print: 1.24, other: 0.01)

(defthm h-lemma
  (implies (and (natp n)
                (true-listp s)
                (equal (len s) 3)
                (perm (list a b c) '(0 1 2))
                (big-tops a b c n s))
           (equal (play (h a b c n)
                        (put (app (tower n) (get a s))
                             a
                             s))
                  (put (app (tower n) (get c s)) c s)))

  :rule-classes nil
  :hints (("Goal" :induct (induction-hint a b c n s))))



; ----------------------------------------------------------------
; The Main Theorem

(defthm hanoi-correct
  (equal (play (hanoi n) (list (tower n) nil nil))
         (list nil nil (tower n)))
  :hints (("Goal" :use (:instance h-lemma
                                  (a 0)
                                  (b 1)
                                  (c 2)
                                  (s (list nil nil nil))))))
