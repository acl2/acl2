; Copyright (C) 2005, Regents of the University of Texas
; Written by J Strother Moore
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; (certify-book "work")

(in-package "ACL2")

; A state has two fields, each of which is a list of length 2.

; ((v0 v1) (m0 m1))

; The vi give the volume of water in each of the two bottles.  The mi
; give the maximum capacity of each of each bottle.  The functions
; below let me set the volume of bottle i, fetch the volume, and fetch
; the capacity.

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

(defthm example-1
  (equal (play '((fill 0)   ; (5 0)
                 (pour 0 1) ; (2 3)
                 (empty 1)  ; (2 0)
                 (pour 0 1) ; (0 2)
                 (fill 0)   ; (5 2)
                 (pour 0 1) ; (4 3)
                 )
               '((0 0) (5 3)))
         '((4 3) (5 3)))
  :rule-classes nil)

(defthm example-2
  (equal (play '((empty 0)
                 (fill 1)
                 (pour 1 0)
                 (fill 1)
                 (pour 1 0)
                 )
               '((0 0) (5 3)))
         '((5 1) (5 3)))
  :rule-classes nil)

; I wish to prove that it is possible to measure out the gcd of the
; two capacities.  Here, gcd is named nonneg-int-gcd.

(include-book "my-mod-gcd")

; I first prove an invariant that establishes that the bottle game can
; only compute multiples of the gcd.

(defthm nth-1
  (equal (nth 1 x) (cadr x)))

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

(defun well-formed-instruction (inst)
  (and (consp inst)
       (case (car inst)
         (FILL (or (equal (nth 1 inst) 0)
                   (equal (nth 1 inst) 1)))
         (EMPTY (or (equal (nth 1 inst) 0)
                    (equal (nth 1 inst) 1)))
         (POUR (if (equal (nth 1 inst) 0)
                   (equal (nth 2 inst) 1)
                 (and (equal (nth 1 inst) 1)
                      (equal (nth 2 inst) 0))))
         (t nil))))

(defthm divides-sum
  (implies (and (natp q)
                (< 0 q)
                (natp i)
                (natp j)
                (equal (nonneg-int-mod i q) 0)
                (equal (nonneg-int-mod j q) 0))
           (equal (nonneg-int-mod (+ i j) q) 0)))

(defthm divides-difference
  (implies (and (natp q)
                (< 0 q)
                (natp i)
                (natp j)
                (natp (- i j))
                (equal (nonneg-int-mod i q) 0)
                (equal (nonneg-int-mod j q) 0))
           (equal (nonneg-int-mod (- i j) q) 0)))

(defthm divides-difference-1
  (implies (and (natp q)
                (< 0 q)
                (natp i)
                (natp j)
                (natp (- i j))
                (equal (nonneg-int-mod i q) 0)
                (equal (nonneg-int-mod j q) 0))
           (equal (nonneg-int-mod (+ (- j) i) q) 0)))

(in-theory (disable COMMUTATIVITY-OF-NONNEG-INT-GCD))

(defthm nonneg-int-gcd-<=
  (implies (and (natp p)
                (natp q)
                (< 0 p)
                (< 0 q))
           (and (<= (nonneg-int-gcd p q) p)
                (<= (nonneg-int-gcd p q) q)))
  :rule-classes :linear)

(defthm divides-difference-2
  (implies (and (natp q)
                (< 0 q)
                (natp i)
                (natp k)
                (natp j)
                (natp (+ i k (- j)))
                (equal (nonneg-int-mod i q) 0)
                (equal (nonneg-int-mod k q) 0)
                (equal (nonneg-int-mod j q) 0))
           (equal (nonneg-int-mod (+ i k (- j)) q) 0)))

(defthm divides-difference-3
  (implies (and (natp q)
                (< 0 q)
                (natp i)
                (natp k)
                (natp j)
                (natp (+ i (- j) k))
                (equal (nonneg-int-mod i q) 0)
                (equal (nonneg-int-mod k q) 0)
                (equal (nonneg-int-mod j q) 0))
           (equal (nonneg-int-mod (+ i (- j) k) q) 0)))



(defthm inv-do-inst
  (implies (and (inv s)
                (well-formed-instruction inst))
           (inv (do-inst inst s))))

(defun well-formed-program (lst)
  (if (endp lst)
      t
    (and (well-formed-instruction (car lst))
         (well-formed-program (cdr lst)))))

(defthm inv-play
  (implies (and (inv s)
                (well-formed-program lst))
           (inv (play lst s)))
  :hints (("Goal" :in-theory (disable inv
                                      do-inst
                                      well-formed-instruction))))

(defun initial-state (c0 c1)
  (list (list 0 0) (list c0 c1)))

(defthm inv-initial-state
  (implies (and (natp c0)
                (natp c1)
                (< 0 c0)
                (< 0 c1))
           (inv (initial-state c0 c1))))

; I have to prove that c0 and c1 don't change.  I'll prove them both
; together by proving that the cadr of the state doesn't change.

(defthm c0-c1-constant
  (implies (well-formed-program lst)
           (equal (cadr (play lst s))
                  (cadr s))))

(defthm c0-initial-state
  (equal (car (cadr (initial-state c0 c1))) c0))

(defthm c1-initial-state
  (equal (cadr (cadr (initial-state c0 c1))) c1))

; The following theorem establishes that well-formed bottle programs
; starting in the initial state can only produce multiples of the GCD.

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
              (equal (nonneg-int-mod (vol 1 final-state) gcd) 0))))
  :hints
  (("Goal"
    :in-theory (disable initial-state inv-play)
    :use (:instance inv-play
                    (s (initial-state c0 c1))
                    (lst lst)))))

; This concludes the first part of our project!  Now we prove the much
; harder result that there is a program that measures the GCD of the
; two capacities.

; Without loss of generality, we assume that c0 >= c1.  Let a
; ``basic block'' for c0 and c1 be the program fragment:

; (FILL 0)
; (POUR 0 1)
; (EMPTY 1)
; ...
; (POUR 0 1)
; (EMPTY 1)

; of length such that both bottles are left empty.  For example, if c0
; is 5 and c1 is 3, then two pours are done.  If c0 is 7 and c1 is 3,
; then three pours are done.

(defun next (i p q)
  (nonneg-int-mod (* i q) p))

(defthm next-unique
  (implies (and (natp i)
                (natp j)
                (natp p)
                (natp q)
                (< 0 p)
                (< 0 q))
           (equal (equal (next i p q)
                         (next j p q))
                  (equal (nonneg-int-mod (* i (nonneg-int-gcd p q)) p)
                         (nonneg-int-mod (* j (nonneg-int-gcd p q)) p))))
  :hints (("Goal" :in-theory (enable COMMUTATIVITY-OF-NONNEG-INT-GCD)
                  :use (:instance main-lemma
                                  (p q)
                                  (q p)))))

(defun cycle (p q n)
  (if (zp n)
      nil
    (cons (next n p q)
          (cycle p q (- n 1)))))

(defun play-trace (insts s ans)
  (if (endp insts)
      (reverse (cons (list 'END s) ans))
    (let ((new-s (do-inst (car insts) s)))
      (play-trace (cdr insts)
                  new-s
                  (cons (list (car insts) new-s)
                        ans)))))

(set-state-ok t)

(defun fmt-trace (i n lst state)
  (declare (xargs :mode :program))
  (cond ((endp lst) state)
        ((and (equal (car (car lst)) '(EMPTY 1))
              (not (equal (car (car (cadr (car lst))))
                          (next n
                                (cap 0 (cadr (car lst)))
                                (cap 1 (cadr (car lst)))))))
         (prog2$ (er hard 'fmt-trace "Something is wrong!")
                 state))
        (t (pprogn
            (fms "~c0 ~x1~t2~x3~#4~[~/ ~tt<- ~x5 = ~x6*~x7 mod ~x8~]"
                 (list (cons #\0 (cons i 4))
                       (cons #\1 (car (car lst)))
                       (cons #\2 17)
                       (cons #\3 (car (cadr (car lst))))
                       (cons #\4 (if (equal (car (car lst)) '(EMPTY 1))
                                     1
                                   0))
                       (cons #\5 (car (car (cadr (car lst)))))
                       (cons #\6 n)
                       (cons #\7 (cadr (cadr (cadr (car lst)))))
                       (cons #\8 (car (cadr (cadr (car lst)))))
; tab column
                       (cons #\t 30))
                 *standard-co* state nil)
            (fmt-trace (+ 1 i)
                       (if (equal (car (car lst)) '(EMPTY 1))
                           (- n 1)
                         n)
                       (cdr lst)
                       state)))))

; Now I define a function that generates the "universal program" for a
; given initial state.  The universal program cycles through all the
; reachable milestones.  This program is just part of my coming to
; understand the problem.  It is not part of my final answer, though I
; rely on its notion of ``basic block.''

(defun play2 (instructions s)
  (mv instructions
      (play instructions s)))

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

(defun uprog1 (i s)
  (cond ((or (zp i)
             (equal i 1))
         nil)
        (t (mv-let (instructions s1)
                   (basic-block s)
                   (append instructions (uprog1 (- i 1) s1))))))

(defun uprog (s)

; This initial (EMPTY 1) is unnecessary since both bottles are
; initially empty anyway.  But I put it in to maintain the invariant
; that the milestones happen after each (EMPTY 1) instruction.

  (cons '(EMPTY 1)
        (uprog1 (floor (cap 0 s) (nonneg-int-gcd (cap 0 s) (cap 1 s)))
                s)))

(defun test (c0 c1 state)
  (declare (xargs :mode :program))
  (fmt-trace 1 (floor c0 (nonneg-int-gcd c0 c1))
             (play-trace (uprog (initial-state c0 c1))
                         (initial-state c0 c1) nil)
             state))

; (test 5 3 state)

; (test 390 154 state)

(defun make-prog1 (i s)

; Let v0, v1, c0 and c1 be the obvious components of s.  Assume c0 >= c1
; that v1 is 0, and that v0 is (nonneg-int-mod (* n c1) c0), for some
; n.  We create a program taht will leave

; (nonneg-int-mod (* (- n i) c1) c0)

; in the bottle 0.  It will leave bottle 1 empty.

  (if (zp i)
      nil
    (mv-let (instructions s1)
            (basic-block s)
            (append instructions (make-prog1 (- i 1) s1)))))

(defthm play-append
  (equal (play (append a b) s)
         (play b (play a s)))
  :hints (("Goal" :in-theory (disable do-inst))))

(encapsulate
 nil
 (local
  (defthm |BASIC-BLOCK-CORRECT Subgoal 2.5.1''|
    (IMPLIES (AND (INTEGERP I)
                  (< 0 I)
                  (INTEGERP J)
                  (<= 0 J)
                  (< I C0)
                  (<= 0 (+ I (* C0 J)))
                  (<= 0 C0)
                  (NATP C0)
                  (NATP C1)
                  (< 0 C0)
                  (< 0 C1)
                  (<= C1 C0)
                  (<= C1 (+ I (* C0 J)))
                  (< C1 I)
                  (<= C1 I))
             (EQUAL (NONNEG-INT-MOD (+ (- C1) I (* C0 J))
                                    C0)
                    (+ (- C1) I)))
    :hints (("Goal"
             :in-theory (disable Nonneg-int-mod-+-*-1)
             :use (:instance  Nonneg-int-mod-+-*-1
                              (x (+ (- c1) i))
                              (j j)
                              (n c0)))
            ("Goal'''"
             :expand (NONNEG-INT-MOD (+ (- C1) I) C0)))))

 (local
  (defthm |BASIC-BLOCK-CORRECT Subgoal 2.3.1''|
    (IMPLIES (AND (INTEGERP I)
                  (< 0 I)
                  (INTEGERP J)
                  (<= 0 J)
                  (< I C0)
                  (<= 0 (+ I (* C0 J)))
                  (<= 0 C0)
                  (NATP C0)
                  (NATP C1)
                  (< 0 C0)
                  (< 0 C1)
                  (<= C1 C0)
                  (<= C1 (+ I (* C0 J)))
                  (<= I C1)
                  (NOT (EQUAL I C1))
                  (<= 0 (+ C0 (- C1) I)))
             (EQUAL (NONNEG-INT-MOD (+ (- C1) I (* C0 J))
                                    C0)
                    (+ C0 (- C1) I)))
    :hints
    (("Goal" :in-theory (disable Nonneg-int-mod-+-*-1)
      :use (:instance  Nonneg-int-mod-+-*-1
                       (x (+ c0 (- c1) i))
                       (j (- j 1))
                       (n c0))))))

 (local
  (defthm |BASIC-BLOCK-CORRECT Subgoal 1.4.1''|
    (IMPLIES (AND (INTEGERP J)
                  (<= 0 J)
                  (<= 0 C0)
                  (NATP C0)
                  (NATP C1)
                  (< 0 C0)
                  (< 0 C1)
                  (<= C1 C0)
                  (<= C1 (* C0 J))
                  (< C1 C0))
             (EQUAL (NONNEG-INT-MOD (+ (- C1) (* C0 J))
                                    C0)
                    (+ C0 (- C1))))
    :hints
    (("Goal" :in-theory (disable Nonneg-int-mod-+-*-1)
      :use (:instance  Nonneg-int-mod-+-*-1
                       (x (+ c0 (- c1)))
                       (j (- j 1))
                       (n c0))))))

 (defthm mv-nth-0-basic-block-correct
   (implies (and (natp c0)
                 (natp c1)
                 (< 0 c0)
                 (< 0 c1)
                 (<= c1 c0)
                 (force (natp k))
                 (force (<= c1 k)))
            (equal (play
                    (car (basic-block ; (mv-nth 0 ...) = (car ...)
                          (list
                           (list (nonneg-int-mod k c0) 0)
                           (list c0 c1))))
                    (list (list (nonneg-int-mod k c0) 0)
                          (list c0 c1)))
                   (list (list (nonneg-int-mod (- k c1) c0) 0)
                         (list c0 c1)))))

 (defthm mv-nth-1-basic-block-correct
   (implies (and (natp c0)
                 (natp c1)
                 (< 0 c0)
                 (< 0 c1)
                 (<= c1 c0)
                 (force (natp k))
                 (force (<= c1 k)))
            (equal (mv-nth 1
                           (basic-block
                            (list
                             (list (nonneg-int-mod k c0) 0)
                             (list c0 c1))))
                   (list (list (nonneg-int-mod (- k c1) c0) 0)
                         (list c0 c1)))))

 )

(in-theory (disable basic-block))

(defun make-prog1-induction (i n)
  (if (zp i)
      (list n)
    (make-prog1-induction (- i 1) (- n 1))))

(defthm make-prog1-correct
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
  :rule-classes nil
  :hints (("Goal" :induct (make-prog1-induction i n))))

(defun make-prog (j c0 c1)

; Let gcd be the gcd of the two capacities, c0 and c1, in s.  Assume
; wlog c1 >= c0 and that both bottles are initially empty.  Then we
; generate a program that leaves (nonneg-int-mod (* j c1) c0) in
; bottle 0.  It leaves bottle 1 empty.

  (cons '(EMPTY 1)
        (make-prog1 (- (floor c0 (nonneg-int-gcd c0 c1))
                       (nonneg-int-mod j (floor c0 (nonneg-int-gcd c0 c1))))
                    (initial-state c0 c1))))

(encapsulate
 nil
 (local
  (defthm little-lemma
    (IMPLIES (AND (natp gcd)
                  (EQUAL (NONNEG-INT-MOD C0 gcd)
                         0)
                  (EQUAL (NONNEG-INT-MOD C1 gcd)
                         0)
                  (NATP C0)
                  (NATP C1)
                  (< 0 C0)
                  (< 0 C1))
             (EQUAL (NONNEG-INT-MOD (* C1 (FLOOR C0 gcd))
                                    C0)
                    0))))
 (defthm nonneg-int-mod-*-floor-gcd
   (implies (and (natp c0)
                 (natp c1)
                 (< 0 c0)
                 (< 0 c1))
            (equal (NONNEG-INT-MOD (* C1 (FLOOR C0 (NONNEG-INT-GCD C0 C1))) C0)
                   0))
   :hints (("Goal"
            :do-not-induct t
            :in-theory (disable floor Nonneg-int-gcd-is-COMMON-divisor)
            :use (:instance Nonneg-int-gcd-is-COMMON-divisor
                            (x c0)
                            (y c1))))))

(defthm natp-floor
  (implies (and (natp i)
                (natp j))
           (natp (floor i j))))

(encapsulate
 nil
 (local
  (defthm positive-floor-little-lemma
    (implies (and (natp gcd)
                  (equal (nonneg-int-mod i gcd) 0)
                  (equal (nonneg-int-mod j gcd) 0)
                  (natp i)
                  (natp j)
                  (< 0 i)
                  (< 0 j))
             (< 0 (floor i gcd)))
    :rule-classes :linear))

 (defthm positive-floor
   (implies (and (natp c0)
                 (natp c1)
                 (< 0 c0)
                 (< 0 c1))
            (< 0 (floor c0 (nonneg-int-gcd c0 c1))))
   :rule-classes :linear
   :hints (("Goal"
            :in-theory (disable floor Nonneg-int-gcd-is-COMMON-divisor)
            :use (:instance Nonneg-int-gcd-is-COMMON-divisor
                            (x c0)
                            (y c1))))))

(encapsulate
 nil
 (local
  (defthm natp-/-gcd-little-lemma
    (implies (and (natp gcd)
                  (equal (nonneg-int-mod i gcd) 0)
                  (equal (nonneg-int-mod j gcd) 0)
                  (natp i)
                  (natp j)
                  (< 0 i)
                  (< 0 j))
             (natp (* i (/ gcd))))))

 (defthm natp-/-gcd
   (implies (and (natp i)
                 (natp j)
                 (< 0 i)
                 (< 0 j))
            (natp (* i (/ (nonneg-int-gcd i j)))))
   :hints (("Goal"
            :in-theory (disable Nonneg-int-gcd-is-COMMON-divisor)
            :use (:instance Nonneg-int-gcd-is-COMMON-divisor
                            (x i)
                            (y j))))))

(encapsulate
 nil
 (local
  (defthm variable-renaming-hack
    (IMPLIES (AND (EQUAL (NONNEG-INT-MOD C0 (NONNEG-INT-GCD C0 X1))
                         0)
                  (EQUAL (NONNEG-INT-MOD X1 (NONNEG-INT-GCD C0 X1))
                         0)
                  (NATP (* C0 (/ (NONNEG-INT-GCD C0 X1))))
                  (NATP (* X1 (/ (NONNEG-INT-GCD C0 X1))))
                  (NOT (NATP (* X1 K (/ (NONNEG-INT-GCD C0 X1)))))
                  (NATP I)
                  (NATP K)
                  (< (* I (NONNEG-INT-GCD C0 X1)) C0)
                  (<= 0
                      (+ I (* C0 K (/ (NONNEG-INT-GCD C0 X1)))))
                  (NATP C0)
                  (NATP X1)
                  (< 0 C0)
                  (< 0 X1)
                  (<= X1 C0))
             (EQUAL (NONNEG-INT-MOD (+ (* X1 I)
                                       (* C0 X1 K (/ (NONNEG-INT-GCD C0 X1))))
                                    C0)
                    (NONNEG-INT-MOD (* X1 I) C0)))))

 (defthm mod-+-*-floor-gcd
   (IMPLIES
    (AND (natp i)
         (natp k)
         (< I (FLOOR C0 (NONNEG-INT-GCD C0 C1)))
         (<= 0
             (+ I
                (* K (FLOOR C0 (NONNEG-INT-GCD C0 C1)))))
         (<= 0 (FLOOR C0 (NONNEG-INT-GCD C0 C1)))
         (NATP C0)
         (NATP C1)
         (< 0 C0)
         (< 0 C1)
         (<= C1 C0))
    (EQUAL (NONNEG-INT-MOD (+ (* C1 I)
                              (* C1 K (FLOOR C0 (NONNEG-INT-GCD C0 C1))))
                           C0)
           (NONNEG-INT-MOD (* C1 I) C0)))
   :otf-flg t
   :hints
   (("Goal"
     :do-not-induct t
     :in-theory (e/d (commutativity-of-nonneg-int-gcd)
                     (Nonneg-int-gcd-is-COMMON-divisor
                      natp-/-gcd
                      Nonneg-int-mod-+-*-1))
     :use ((:instance Nonneg-int-gcd-is-COMMON-divisor
                      (x c0)
                      (y c1))
           (:instance natp-/-gcd
                      (i c0)
                      (j c1))
           (:instance natp-/-gcd
                      (i c1)
                      (j c0))
           (:instance Nonneg-int-mod-+-*-1
                      (x (* C1 I))
                      (n c0)
                      (j (* C1 K (/ (NONNEG-INT-GCD C0 C1))))))))))



(defthm make-prog-correct
  (implies (and (natp c0)
                (natp c1)
                (< 0 c0)
                (< 0 c1)
                (<= c1 c0)
                (natp j))
           (equal (vol 0 (play (make-prog j c0 c1)
                               (initial-state c0 c1)))
                  (nonneg-int-mod (* j c1) c0)))
  :otf-flg t
  :hints (("Goal"
           :in-theory (disable floor)
           :use ((:instance
                  make-prog1-correct
                  (i (- (floor c0 (nonneg-int-gcd c0 c1))
                        (nonneg-int-mod j (floor c0 (nonneg-int-gcd c0 c1)))))
                  (n (floor c0 (nonneg-int-gcd c0 c1))))))))

(in-theory (disable make-prog initial-state vol))

(encapsulate
 nil
 (local
  (defthm little-lemma0
    (implies (and (natp i)
                  (natp k)
                  (< 0 i)
                  (< 0 k)
                  (not (equal k 1)))
             (equal (nonneg-int-mod i (* i k)) i))))

 (local
  (encapsulate
   nil
   (local
    (defthm nonnegative-integer-quotient-gcd-non-0-1-little-lemma
      (implies (and (natp gcd)
                    (equal (nonneg-int-mod p gcd) 0)
                    (equal (nonneg-int-mod q gcd) 0)
                    (natp p)
                    (natp q)
                    (< 0 p)
                    (< 0 q))
               (< 0 (nonnegative-integer-quotient p gcd)))
      :rule-classes :linear))

   (defthm nonnegative-integer-quotient-gcd-non-0-1
     (implies (and (natp p)
                   (natp q)
                   (< 0 p)
                   (< 0 q))
              (< 0 (nonnegative-integer-quotient p
                                                 (nonneg-int-gcd p q))))
     :rule-classes :linear
     :hints (("Goal"
              :in-theory (disable Nonneg-int-gcd-is-COMMON-divisor)
              :use (:instance Nonneg-int-gcd-is-COMMON-divisor
                              (x p)
                              (y q)))))))

 (local
  (in-theory (enable commutativity-of-nonneg-int-gcd)))

 (local
  (defthm nonnegative-integer-quotient-gcd-non-0-2
    (implies (and (natp p)
                  (natp q)
                  (< 0 p)
                  (< 0 q))
             (< 0 (nonnegative-integer-quotient q (nonneg-int-gcd p q))))
    :hints (("Goal" :in-theory (disable nonnegative-integer-quotient-gcd-non-0-1)
             :use (:instance nonnegative-integer-quotient-gcd-non-0-1
                             (p q)
                             (q p))))
    :rule-classes :linear))

 (local
  (defthm little-lemma1
    (IMPLIES
     (AND
      (EQUAL Px
             (* (NONNEG-INT-GCD P Q)
                ax))
      (EQUAL
       ax
       (* (NONNEG-INT-GCD (NONNEGATIVE-INTEGER-QUOTIENT P (NONNEG-INT-GCD P Q))
                          (NONNEGATIVE-INTEGER-QUOTIENT Q (NONNEG-INT-GCD P Q)))
          (NONNEGATIVE-INTEGER-QUOTIENT
           (NONNEGATIVE-INTEGER-QUOTIENT P (NONNEG-INT-GCD P Q))
           (NONNEG-INT-GCD
            (NONNEGATIVE-INTEGER-QUOTIENT P (NONNEG-INT-GCD P Q))
            (NONNEGATIVE-INTEGER-QUOTIENT Q (NONNEG-INT-GCD P Q)))))))
     (EQUAL
      (NONNEG-INT-MOD
       Px
       (* (NONNEG-INT-GCD P Q)
          (NONNEG-INT-GCD
           (NONNEGATIVE-INTEGER-QUOTIENT P (NONNEG-INT-GCD P Q))
           (NONNEGATIVE-INTEGER-QUOTIENT Q (NONNEG-INT-GCD P Q)))))
      0))
    :hints
    (("Goal"
      :in-theory (disable NONNEGATIVE-INTEGER-QUOTIENT-GCD
                          Left-nonneg-int-mod-*)
      :use (:instance
            Left-nonneg-int-mod-*
            (j (NONNEGATIVE-INTEGER-QUOTIENT
                (NONNEGATIVE-INTEGER-QUOTIENT P (NONNEG-INT-GCD P Q))
                (NONNEG-INT-GCD
                 (NONNEGATIVE-INTEGER-QUOTIENT P (NONNEG-INT-GCD P Q))
                 (NONNEGATIVE-INTEGER-QUOTIENT Q (NONNEG-INT-GCD P Q)))))
            (n (* (NONNEG-INT-GCD P Q)
                  (NONNEG-INT-GCD
                   (NONNEGATIVE-INTEGER-QUOTIENT P (NONNEG-INT-GCD P Q))
                   (NONNEGATIVE-INTEGER-QUOTIENT Q (NONNEG-INT-GCD P Q))))))))))

 (local
  (defthm little-lemma2
    (IMPLIES
     (AND
      (EQUAL Qx
             (* (NONNEG-INT-GCD P Q)
                ax))
      (EQUAL
       ax
       (* (NONNEG-INT-GCD (NONNEGATIVE-INTEGER-QUOTIENT P (NONNEG-INT-GCD P Q))
                          (NONNEGATIVE-INTEGER-QUOTIENT Q (NONNEG-INT-GCD P Q)))
          (NONNEGATIVE-INTEGER-QUOTIENT
           (NONNEGATIVE-INTEGER-QUOTIENT Q (NONNEG-INT-GCD P Q))
           (NONNEG-INT-GCD
            (NONNEGATIVE-INTEGER-QUOTIENT P (NONNEG-INT-GCD P Q))
            (NONNEGATIVE-INTEGER-QUOTIENT Q (NONNEG-INT-GCD P Q)))))))
     (EQUAL
      (NONNEG-INT-MOD
       Qx
       (* (NONNEG-INT-GCD P Q)
          (NONNEG-INT-GCD
           (NONNEGATIVE-INTEGER-QUOTIENT P (NONNEG-INT-GCD P Q))
           (NONNEGATIVE-INTEGER-QUOTIENT Q (NONNEG-INT-GCD P Q)))))
      0))
    :hints
    (("Goal"
      :in-theory (disable NONNEGATIVE-INTEGER-QUOTIENT-GCD
                          Left-nonneg-int-mod-*)
      :use (:instance
            Left-nonneg-int-mod-*
            (j (NONNEGATIVE-INTEGER-QUOTIENT
                (NONNEGATIVE-INTEGER-QUOTIENT Q (NONNEG-INT-GCD P Q))
                (NONNEG-INT-GCD
                 (NONNEGATIVE-INTEGER-QUOTIENT P (NONNEG-INT-GCD P Q))
                 (NONNEGATIVE-INTEGER-QUOTIENT Q (NONNEG-INT-GCD P Q)))))
            (n (* (NONNEG-INT-GCD P Q)
                  (NONNEG-INT-GCD
                   (NONNEGATIVE-INTEGER-QUOTIENT P (NONNEG-INT-GCD P Q))
                   (NONNEGATIVE-INTEGER-QUOTIENT Q (NONNEG-INT-GCD P Q))))))))))

 (defthm nonnegative-integer-quotient-gcd-relatively-prime
   (implies (and (natp p)
                 (natp q)
                 (< 0 p)
                 (< 0 q))
            (equal (nonneg-int-gcd
                    (nonnegative-integer-quotient p (nonneg-int-gcd p q))
                    (nonnegative-integer-quotient q (nonneg-int-gcd p q)))
                   1))
   :hints
   (("Goal"
     :do-not-induct t
     :in-theory (e/d (commutativity-of-nonneg-int-gcd
                      Nonneg-int-gcd-is-LARGEST-common-divisor-mod)
                     (NONNEGATIVE-INTEGER-QUOTIENT-GCD))
     :use
     ((:instance note-3 (p p) (q q))
      (:instance note-3 (p q) (q p))
      (:instance note-3
                 (p (nonnegative-integer-quotient p (nonneg-int-gcd p q)))
                 (q (nonnegative-integer-quotient q (nonneg-int-gcd p q))))
      (:instance note-3
                 (p (nonnegative-integer-quotient q (nonneg-int-gcd p q)))
                 (q (nonnegative-integer-quotient p (nonneg-int-gcd p q))))
      (:instance Nonneg-int-gcd-is-LARGEST-common-divisor-mod
                 (x p)
                 (y q)
                 (d (* (nonneg-int-gcd
                        (nonnegative-integer-quotient p (nonneg-int-gcd p q))
                        (nonnegative-integer-quotient q (nonneg-int-gcd p q)))
                       (nonneg-int-gcd p q)))))))))



(defun gcd-prog (c0 c1)
  (make-prog
   (fixnonneg (nonneg-int-gcd-multiplier1
               (nonnegative-integer-quotient c1 (nonneg-int-gcd c0 c1))
               (nonnegative-integer-quotient c0 (nonneg-int-gcd c0 c1)))
              (nonnegative-integer-quotient c0 (nonneg-int-gcd c0 c1)))
   c0 c1))

; (defthm exists-gcd-prog
;   (implies (and (natp p)
;                 (natp q)
;                 (< 0 p)
;                 (< 0 q)
;                 (<= q p))
;            (equal (vol 0 (play (gcd-prog p q)
;                                (initial-state p q)))
;                   (nonneg-int-gcd p q))))

; Proof (of the subcase of this where q<p).  If q=p, gcd-prog fails!
; But gcd-prog!, defined below, will handle that case.

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

; We would be done if we could show that for the value of j used above
; in gcd-prog, (nonneg-int-mod (* j d) c) = 1.

; Note that (nonneg-int-gcd c d) = 1.  But because it is a gcd, we can
; represent it as a linear combination of ac+bd as follows.

; a = (nonneg-int-gcd-multiplier1 c d)
; b = (nonneg-int-gcd-multiplier2 c d)

; Thus,

; 1
; =
; (nonneg-int-mod (+ (* (fixnonneg a c) c)
;                    (* (fixnonneg b c) d))
;                 c)
; =
; (nonneg-int-mod (* (fixnonneg b c) d)
;                 c)
; Note that the value of j used in gcd-prog is (fixnonneg b c),
; i.e.,
; (fixnonneg (nonneg-int-gcd-multiplier2
;             (nonnegative-integer-quotient p (nonneg-int-gcd p q))
;             (nonnegative-integer-quotient q (nonneg-int-gcd p q)))
;            (nonnegative-integer-quotient p (nonneg-int-gcd p q)))
; Q.E.D.

(encapsulate
 nil
 (local
  (defthm positive-nonnegative-integer-quotient-gcd-little-lemma
    (implies (and (natp gcd)
                  (equal (nonneg-int-mod c0 gcd) 0)
                  (equal (nonneg-int-mod c1 gcd) 0)
                  (natp c0)
                  (natp c1)
                  (< 0 c0)
                  (< 0 c1))
             (< 0 (nonnegative-integer-quotient c0 gcd)))
    :rule-classes :linear))

 (defthm positive-nonnegative-integer-quotient-gcd
   (implies (and (natp c0)
                 (natp c1)
                 (< 0 c0)
                 (< 0 c1))
            (< 0 (nonnegative-integer-quotient c0 (nonneg-int-gcd c0 c1))))
   :rule-classes :linear
   :hints (("Goal"
            :in-theory (disable floor Nonneg-int-gcd-is-COMMON-divisor)
            :use (:instance Nonneg-int-gcd-is-COMMON-divisor
                            (x c0)
                            (y c1))))))

(in-theory (enable commutativity-of-nonneg-int-gcd))

(defthm positive-nonnegative-integer-quotient-gcd-2
   (implies (and (natp c0)
                 (natp c1)
                 (< 0 c0)
                 (< 0 c1))
            (< 0 (nonnegative-integer-quotient c1 (nonneg-int-gcd c0 c1))))
   :rule-classes :linear
   :hints (("Goal"
            :in-theory (disable positive-nonnegative-integer-quotient-gcd)
            :use (:instance positive-nonnegative-integer-quotient-gcd
                            (c0 c1)
                            (c1 c0)))))
(in-theory (disable make-prog initial-state vol))

(encapsulate
 nil
 (local
  (defthm nonnegative-integer-quotient-gcd-exceeds-1-little-lemma
    (implies (and (natp gcd)
                  (equal (nonneg-int-mod p gcd) 0)
                  (equal (nonneg-int-mod q gcd) 0)
                  (natp p)
                  (natp q)
                  (< 0 p)
                  (< 0 q)
                  (< q p))
             (< 1 (nonnegative-integer-quotient p gcd)))
    :rule-classes :linear))

 (defthm nonnegative-integer-quotient-gcd-exceeds-1
   (implies (and (natp p)
                 (natp q)
                 (< 0 p)
                 (< 0 q)
                 (< q p))
            (< 1 (nonnegative-integer-quotient p (nonneg-int-gcd p q))))
   :rule-classes :linear
   :hints (("Goal"
            :in-theory (disable floor Nonneg-int-gcd-is-COMMON-divisor)
            :use (:instance Nonneg-int-gcd-is-COMMON-divisor
                            (x p)
                            (y q))))))
(defthm nonneg-int-gcd-0
  (equal (nonneg-int-gcd 0 q)
         (nfix q))
  :hints (("Goal" :in-theory (disable COMMUTATIVITY-OF-NONNEG-INT-GCD)
                  :expand (nonneg-int-gcd 0 q))))


(defthm renaming-hack-lemma
  (IMPLIES
   (AND
    (EQUAL
     (NONNEG-INT-MOD 1
                     (NONNEGATIVE-INTEGER-QUOTIENT P (NONNEG-INT-GCD P Q)))
     (NONNEG-INT-MOD
      (+
       (*
        (NONNEGATIVE-INTEGER-QUOTIENT P (NONNEG-INT-GCD P Q))
        (FIXNONNEG (NONNEG-INT-GCD-MULTIPLIER2
                    (NONNEGATIVE-INTEGER-QUOTIENT Q (NONNEG-INT-GCD P Q))
                    (NONNEGATIVE-INTEGER-QUOTIENT P (NONNEG-INT-GCD P Q)))
                   (NONNEGATIVE-INTEGER-QUOTIENT P (NONNEG-INT-GCD P Q))))
       (*
        (NONNEGATIVE-INTEGER-QUOTIENT Q (NONNEG-INT-GCD P Q))
        (FIXNONNEG (NONNEG-INT-GCD-MULTIPLIER1
                    (NONNEGATIVE-INTEGER-QUOTIENT Q (NONNEG-INT-GCD P Q))
                    (NONNEGATIVE-INTEGER-QUOTIENT P (NONNEG-INT-GCD P Q)))
                   (NONNEGATIVE-INTEGER-QUOTIENT P (NONNEG-INT-GCD P Q)))))
      (NONNEGATIVE-INTEGER-QUOTIENT P (NONNEG-INT-GCD P Q))))
    (EQUAL
     (NONNEG-INT-MOD
      (* (NONNEG-INT-GCD P Q)
         (NONNEGATIVE-INTEGER-QUOTIENT Q (NONNEG-INT-GCD P Q))
         (FIXNONNEG (NONNEG-INT-GCD-MULTIPLIER1
                     (NONNEGATIVE-INTEGER-QUOTIENT Q (NONNEG-INT-GCD P Q))
                     (NONNEGATIVE-INTEGER-QUOTIENT P (NONNEG-INT-GCD P Q)))
                    (NONNEGATIVE-INTEGER-QUOTIENT P (NONNEG-INT-GCD P Q))))
      (* (NONNEG-INT-GCD P Q)
         (NONNEGATIVE-INTEGER-QUOTIENT P (NONNEG-INT-GCD P Q))))
     (*
      (NONNEG-INT-GCD P Q)
      (NONNEG-INT-MOD
       (*
        (NONNEGATIVE-INTEGER-QUOTIENT Q (NONNEG-INT-GCD P Q))
        (FIXNONNEG (NONNEG-INT-GCD-MULTIPLIER1
                    (NONNEGATIVE-INTEGER-QUOTIENT Q (NONNEG-INT-GCD P Q))
                    (NONNEGATIVE-INTEGER-QUOTIENT P (NONNEG-INT-GCD P Q)))
                   (NONNEGATIVE-INTEGER-QUOTIENT P (NONNEG-INT-GCD P Q))))
       (NONNEGATIVE-INTEGER-QUOTIENT P (NONNEG-INT-GCD P Q)))))
    (NATP P)
    (NATP Q)
    (< 0 P)
    (< 0 Q)
    (< Q P))
   (EQUAL
    (NONNEG-INT-MOD
     (* (NONNEGATIVE-INTEGER-QUOTIENT Q (NONNEG-INT-GCD P Q))
        (FIXNONNEG (NONNEG-INT-GCD-MULTIPLIER1
                    (NONNEGATIVE-INTEGER-QUOTIENT Q (NONNEG-INT-GCD P Q))
                    (NONNEGATIVE-INTEGER-QUOTIENT P (NONNEG-INT-GCD P Q)))
                   (NONNEGATIVE-INTEGER-QUOTIENT P (NONNEG-INT-GCD P Q))))
     (NONNEGATIVE-INTEGER-QUOTIENT P (NONNEG-INT-GCD P Q)))
    1))
  :otf-flg t
  :hints
  (("Goal"
    :in-theory (disable Nonneg-int-mod-+-*-1)
    :do-not-induct t
    :use
    (:instance
     Nonneg-int-mod-+-*-1
     (x (*
         (NONNEGATIVE-INTEGER-QUOTIENT Q (NONNEG-INT-GCD P Q))
         (FIXNONNEG (NONNEG-INT-GCD-MULTIPLIER1
                     (NONNEGATIVE-INTEGER-QUOTIENT Q (NONNEG-INT-GCD P Q))
                     (NONNEGATIVE-INTEGER-QUOTIENT P (NONNEG-INT-GCD P Q)))
                    (NONNEGATIVE-INTEGER-QUOTIENT P (NONNEG-INT-GCD P Q)))))
     (j (FIXNONNEG (NONNEG-INT-GCD-MULTIPLIER2
                    (NONNEGATIVE-INTEGER-QUOTIENT Q (NONNEG-INT-GCD P Q))
                    (NONNEGATIVE-INTEGER-QUOTIENT P (NONNEG-INT-GCD P Q)))
                   (NONNEGATIVE-INTEGER-QUOTIENT P (NONNEG-INT-GCD P Q))))
     (n (NONNEGATIVE-INTEGER-QUOTIENT P (NONNEG-INT-GCD P Q)))))
   ("Goal'''"
    :in-theory (disable nonnegative-integer-quotient-gcd-exceeds-1)
    :use nonnegative-integer-quotient-gcd-exceeds-1
    :expand (NONNEG-INT-MOD 1
                      (NONNEGATIVE-INTEGER-QUOTIENT P (NONNEG-INT-GCD P Q))))))

(defthm renaming-hack
  (IMPLIES
   (AND
    (EQUAL Px
           (* (NONNEG-INT-GCD P Q)
              (NONNEGATIVE-INTEGER-QUOTIENT P (NONNEG-INT-GCD P Q))))
    (EQUAL Qx
           (* (NONNEG-INT-GCD P Q)
              (NONNEGATIVE-INTEGER-QUOTIENT Q (NONNEG-INT-GCD P Q))))
    (EQUAL
     (NONNEG-INT-GCD (NONNEGATIVE-INTEGER-QUOTIENT P (NONNEG-INT-GCD P Q))
                     (NONNEGATIVE-INTEGER-QUOTIENT Q (NONNEG-INT-GCD P Q)))
     1)
    (EQUAL
     (NONNEG-INT-MOD 1
                     (NONNEGATIVE-INTEGER-QUOTIENT P (NONNEG-INT-GCD P Q)))
     (NONNEG-INT-MOD
      (+
       (*
        (NONNEGATIVE-INTEGER-QUOTIENT P (NONNEG-INT-GCD P Q))
        (FIXNONNEG (NONNEG-INT-GCD-MULTIPLIER2
                    (NONNEGATIVE-INTEGER-QUOTIENT Q (NONNEG-INT-GCD P Q))
                    (NONNEGATIVE-INTEGER-QUOTIENT P (NONNEG-INT-GCD P Q)))
                   (NONNEGATIVE-INTEGER-QUOTIENT P (NONNEG-INT-GCD P Q))))
       (*
        (NONNEGATIVE-INTEGER-QUOTIENT Q (NONNEG-INT-GCD P Q))
        (FIXNONNEG (NONNEG-INT-GCD-MULTIPLIER1
                    (NONNEGATIVE-INTEGER-QUOTIENT Q (NONNEG-INT-GCD P Q))
                    (NONNEGATIVE-INTEGER-QUOTIENT P (NONNEG-INT-GCD P Q)))
                   (NONNEGATIVE-INTEGER-QUOTIENT P (NONNEG-INT-GCD P Q)))))
      (NONNEGATIVE-INTEGER-QUOTIENT P (NONNEG-INT-GCD P Q))))
    (EQUAL
     (NONNEG-INT-MOD
      (* (NONNEG-INT-GCD P Q)
         (NONNEGATIVE-INTEGER-QUOTIENT Q (NONNEG-INT-GCD P Q))
         (FIXNONNEG (NONNEG-INT-GCD-MULTIPLIER1
                     (NONNEGATIVE-INTEGER-QUOTIENT Q (NONNEG-INT-GCD P Q))
                     (NONNEGATIVE-INTEGER-QUOTIENT P (NONNEG-INT-GCD P Q)))
                    (NONNEGATIVE-INTEGER-QUOTIENT P (NONNEG-INT-GCD P Q))))
      Px)
     (*
      (NONNEG-INT-GCD P Q)
      (NONNEG-INT-MOD
       (*
        (NONNEGATIVE-INTEGER-QUOTIENT Q (NONNEG-INT-GCD P Q))
        (FIXNONNEG (NONNEG-INT-GCD-MULTIPLIER1
                    (NONNEGATIVE-INTEGER-QUOTIENT Q (NONNEG-INT-GCD P Q))
                    (NONNEGATIVE-INTEGER-QUOTIENT P (NONNEG-INT-GCD P Q)))
                   (NONNEGATIVE-INTEGER-QUOTIENT P (NONNEG-INT-GCD P Q))))
       (NONNEGATIVE-INTEGER-QUOTIENT P (NONNEG-INT-GCD P Q)))))
    (natp p)
    (natp q)
    (< 0 P)
    (< 0 Q)
    (< Q P))
   (EQUAL
    (NONNEG-INT-MOD
     (* Qx
        (FIXNONNEG (NONNEG-INT-GCD-MULTIPLIER1
                    (NONNEGATIVE-INTEGER-QUOTIENT Q (NONNEG-INT-GCD P Q))
                    (NONNEGATIVE-INTEGER-QUOTIENT P (NONNEG-INT-GCD P Q)))
                   (NONNEGATIVE-INTEGER-QUOTIENT P (NONNEG-INT-GCD P Q))))
     Px)
    (NONNEG-INT-GCD P Q)))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable NONNEGATIVE-INTEGER-QUOTIENT-GCD))))


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
                  (nonneg-int-gcd p q)))
  :otf-flg t
  :hints
  (("Goal"
    :do-not-induct t
    :in-theory (disable nonnegative-integer-quotient-gcd-relatively-prime
                        Linear-combination-for-nonneg-int-gcd
                        NONNEGATIVE-INTEGER-QUOTIENT-GCD
                        nonneg-int-mod-*-*)
    :use
    ((:instance note-3 (p p) (q q))  ;  p = c*g
     (:instance note-3 (p q) (q p))  ;  q = d*g
     (:instance nonnegative-integer-quotient-gcd-relatively-prime
                (p p)
                (q q))
     (:instance note-2
                (q (nonnegative-integer-quotient p (nonneg-int-gcd p q)))
                (p (nonnegative-integer-quotient q (nonneg-int-gcd p q))))
     (:instance nonneg-int-mod-*-*
                (i (NONNEG-INT-GCD P Q))
                (j (* (NONNEGATIVE-INTEGER-QUOTIENT Q (NONNEG-INT-GCD P Q))
                      (FIXNONNEG (NONNEG-INT-GCD-MULTIPLIER1
                                  (NONNEGATIVE-INTEGER-QUOTIENT Q (NONNEG-INT-GCD P Q))
                                  (NONNEGATIVE-INTEGER-QUOTIENT P (NONNEG-INT-GCD P Q)))
                                 (NONNEGATIVE-INTEGER-QUOTIENT P (NONNEG-INT-GCD P Q)))))
                (k (NONNEGATIVE-INTEGER-QUOTIENT P (NONNEG-INT-GCD P Q))))))
   ("Subgoal 2" :in-theory (enable vol initial-state))))
