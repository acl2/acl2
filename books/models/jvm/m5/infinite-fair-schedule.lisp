; (certify-book "infinite-fair-schedule")

; An Infinite Fair Scheduler

; In this file we constrain a nat-valued function fair-sched, of one
; argument.  We think of fair-sched as an infinite sequence.  That is,
; we index it with naturals.  (We don't care what it does off the
; naturals but for convenience we insist that it return a natural.)
; We say that a nat i ``occurs'' in fair-sched if there is a nat x
; such that (fair-sched x) = i.

; We constrain fair-sched so that every nat occurs infinitely often.

; This is stated by saying that for every nat i there is an x such
; that (fair-sched x) is i and there is a nat y > x such that
; (fair-sched y) is also i.

; We construct such a function using a diagonalization scheme.

; This whole development is due to Rob Sumners, who did it first and
; told me about it over a beer.  I've reconstructed it on my own, but
; I strongly suspect what follows is essentially what Rob did.

; J Moore
; Marktoberdorf Summer School, 2002.

(in-package "ACL2")

; Here is the diagonalization scheme I use.  Key to my thinking is the
; enumeration of successive "blocks".

; index:0  1  2  3  4  5  6  7  8  9 10 11 12 13 14 15 16 17 18 19 20 ...
;
; block
; 0     0
; 1        0  1
; 2              0  1  2
; 3                       0  1  2  3
; 4                                   0  1  2  3  4
; 5                                                  0  1  2  3  4  5

; The first item in every block is 0.  The last item in block b is b.

; To do this work I have to define all my functions relative to a
; given block.  In the final encapsulation, I use block 0, but for the
; inductive arguments to work I must think more generally.

(include-book "arithmetic/top-with-meta" :dir :system)

(defun movei (n b)

; Suppose you're standing on the first item in block b.  We move
; forward n steps from that point and return the resulting item.

  (cond ((or (not (natp n))
             (not (natp b))
             (< n (+ b 1)))
         (nfix n))
        (t (movei (- n (+ b 1)) (+ b 1)))))

(defun moveb (n b)

; Suppose you're standing on the first item in block b.  We move
; forward n steps from that point and return the resulting block.

  (cond ((or (not (natp n))
             (not (natp b))
             (< n (+ b 1)))
         (nfix b))
        (t (moveb (- n (+ b 1)) (+ b 1)))))

(defun distex (a b)

; We assume that a and b are block numbers and a<=b.  We compute the
; "index distance" between the beginning of block a and that of block
; b.

  (declare (xargs :measure (nfix (- b a))))
  (cond ((or (not (natp a))
             (not (natp b))
             (<= b a))
         0)
        (t (+ (+ 1 a) (distex (+ 1 a) b)))))

; Here are three simple warmup exercises.  None of the next three
; theorems are used by the encapsulation.  But I found my initial
; attempts to do this so erroneous that I thought it wise to check my
; definitions with a few simple properties.

; Let d be the index distance between blocks a and b.  Then the item d
; away from block a is 0 -- the first item of block b.

(defthm movei-distex
  (implies (and (natp a)
                (natp b)
                (<= a b))
           (equal (movei (distex a b) a) 0))
  :rule-classes nil)

; And here is the theorem that shows the move leaves you in block b.

(defthm moveb-distex
  (implies (and (natp a)
                (natp b)
                (<= a b))
           (equal (moveb (distex a b) a) b))
  :rule-classes nil)

; Also, an item from a block is always no greater than the block number.

(defthm movei_<=_moveb
  (implies (and (natp x)
                (natp a))
           (<= (movei x a) (moveb x a)))
  :rule-classes nil)

; Suppose index x maps (relative to some base block) to item i in
; block a.  Where is the next occurrence of item i (relative to that
; base block)?  It will be at 1+x+a, i.e., it will be 1+a distant from
; x.

(defthm next-occurrence-of-item
  (implies (and (natp x)
                (natp base))
           (equal (movei (+ 1 x (moveb x base)) base)
                  (movei x base))))

; While it is not important, I prove there is no intervening
; occurrence.  In the encapsulation, I use the name "next-time" to
; witness a later time at which (fair-sched x) reoccurs.  The
; following theorem justifies the use of the phrase "next time".  Of
; course, if there is a later time, then we can define the function
; that returns the next time.  So providing this as an "additional"
; constraint on the witness does not actually change the abstraction
; and some users might benefit from the constraint that there is no
; intervening occurrence.

(defthm no-intervening-occurrence-lemma
  (implies (and (< d (+ 1 (moveb x base)))
                (< 0 d)
                (natp d)
                (natp x)
                (natp base))
           (equal (movei (+ x d) base)
                  (if (> (+ (movei x base) d) (moveb x base))
                      (+ (movei x base) d (- (moveb x base)) -1)
                    (+ (movei x base) d))))
  :rule-classes nil
  :hints
  (("Goal" :do-not '(generalize fertilize))
   ("Subgoal *1/1.2.1" :expand (MOVEI (+ -1 (- BASE) D X) (+ 1 BASE)))
   ("Subgoal *1/1.1" :expand (MOVEI (+ D X) BASE))))

(defthm no-intervening-occurrence
  (implies (and (< y (+ 1 x (moveb x base)))
                (< x y)
                (natp y)
                (natp x)
                (natp base))
           (equal (movei y base)
                  (if (> (+ (movei x base) (- y x)) (moveb x base))
                      (+ (movei x base) (- y x) (- (moveb x base)) -1)
                    (+ (movei x base) (- y x)))))
  :hints (("Goal" :use (:instance no-intervening-occurrence-lemma
                                  (d (- y x))))))

; Every every nat, i, occurs as an item (relative to any base).  I.e.,
; for every nat i and base, there is an x such that (movei x base) =
; i.

(defthm every-nat-occurs
  (implies (and (natp i)
                (natp base))
           (equal (movei (+ i (distex base i)) base) i)))

; Finally, there are no earlier occurrences than the one constructed
; above.  In the encapsulation I have to give a name to the function
; that constructs a time at which i occurs in the schedule.  I call
; the function "first-time".  This theorem is used to prove that it
; really is the first time.  Of course, if there is an occurrence
; there will always be a first one.  So adding this extra bit of
; information about the witness adds nothing important.

(defthm no-earlier-occurrences
  (implies (and (< x (+ i (distex base i)))
                (natp x)
                (natp i)
                (natp base))
           (< (movei x base) i))
  :rule-classes :linear)

(encapsulate ((fair-sched (x) t)
              (next-time (x) t)
              (first-time (i) t))

 (local (defun fair-sched (x) (movei x 0)))
 (local (defun next-time  (x) (+ 1 x (moveb x 0))))
 (local (defun first-time (i) (+ i (distex 0 i))))

; The scheduler is a total function to nats.

 (defthm natp-fair-sched
   (natp (fair-sched x)))

; For every nat i, there is a time at which the sheduler returns i and
; that time is a nat, and there is no earlier time than the one
; witnessed.

 (defthm always-a-first-time
   (implies (natp i)
            (and (equal (fair-sched (first-time i)) i)
                 (natp (first-time i))
                 (implies (and (natp x)
                               (< x (first-time i)))
                          (not (equal (fair-sched x) i))))))

; There is always a next time at which the item at x will occur, that
; time is a nat, it is greater than x.


 (defthm always-a-next-time
   (implies (natp x)
            (and (equal (fair-sched (next-time x)) (fair-sched x))
                 (natp (next-time x))
                 (< x (next-time x))
                 (implies (and (natp y)
                               (< x y)
                               (< y (next-time x)))
                          (not (equal (fair-sched y) (fair-sched x)))))))
 )

