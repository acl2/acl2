; An ACL2 version of a HOL4 example from Magnus Myreen
; Matt Kaufmann
; August, 2009 (comments revised December, 2009)

; The following proof is a translation to ACL2 of a proof by Magnus Myreen
; (Univ. of Cambridge), inspired by separation logic, about reversing linked
; lists.  That work is reported in a paper by Magnus Myreen, in preparation,
; entitled "Separation logic adapted for proofs by rewriting".  I changed
; Magnus's definition of NEXT a bit in order to take advantage of what I think
; is a standard sort of trick for controlling how the next-state function opens
; up, and changed some function names changed slightly to avoid conflicts with
; built-in Lisp names.

; The coi bags library was extremely helpful!

; Those who have more experience with interpreter proofs than I do may easily
; be able to simplify my proof, in particular eliminating the ugly hack
; involving equality (as explained in the comment above RD-PC-HACK).

(in-package "ACL2")

; The following must go in the certification world (and hence is redundant
; here).  Actually, only "coi/bags/top" is needed in the certification world;
; but the proof of spec-body seemed to be failing with the order of these
; include-book forms reversed!
(include-book "arithmetic/top-with-meta" :dir :system)
(include-book "coi/bags/top" :dir :system)

; Then: (certify-book "reverse-by-separation" 2)

(defun rd (x lst)
  (cond ((atom lst) 0)
        ((equal x (caar lst))
         (cdar lst))
        (t (rd x (cdr lst)))))

(defun wr (y z lst)
  (cons (cons y z) lst))

(defun rd-pc (s)
  (rd 0 s))

(defund next (p s)
  (let* ((i (rd p s)) ; read instruction, part 1
         (x (rd (+ 1 p) s)) ; read instruction, part 2
         (y (rd (+ 2 p) s))) ; read instruction, part 3
    (case i
      (0 #|| imm     ||# (wr x y s))
      (1 #|| move    ||# (wr x (rd y s) s))
      (2 #|| load    ||# (wr x (rd (rd y s) s) s))
      (3 #|| store   ||# (wr (rd x s) (rd y s) s))
      (4 #|| back    ||# (wr 0 (if (equal (rd x s) 0) p (- p y)) s))
      (5 #|| forward ||# (wr 0 (if (equal (rd x s) 0) p (+ p y)) s))
      (6 #|| add     ||# (wr x (+ (rd x s) (rd y s)) s))
      (7 #|| addi    ||# (wr x (+ (rd x s) y) s))
      (otherwise s))))

(defun bump-pc (s)
  (wr 0 (+ (rd-pc s) 3) s))

(defun exec (n s)
  (cond ((zp n) s)
        (t (exec (1- n)
                 (bump-pc (next (rd-pc s) s))))))

(defun seq (p xs)
  (cond ((atom xs) nil)
        (t (cons (cons p (car xs))
                 (seq (1+ p) (cdr xs))))))

; The code:
(defun rev-code (p)
  (seq p '(
           0 2 0   ;   0 : imm 2 0
           5 0 12  ;   3 : forward 0 12
           2 3 1   ;   6 : load 3 1
           3 1 2   ;   9 : store 1 2
           1 2 1   ;  12 : move 2 1
           1 1 3   ;  15 : move 1 3
           4 1 15  ;  18 : back 1 15
           )))

(defun list-addr (xs)
  (cond ((atom xs) 0)
        (t (caar xs))))

(defun list-in-store (xs)
  (cond ((atom xs) nil)
        (t
         (let ((l (caar xs))
               (y (cdar xs)))
           (list* (cons l (list-addr (cdr xs)))
                  (cons (1+ l) y)
                  (list-in-store (cdr xs)))))))

(defun list-for (v xs)
  (cons (cons v (list-addr xs))
        (list-in-store xs)))

(defun separate (lst s rest)
  (cond ((atom lst) (bag::unique rest))
        (t (let ((x (caar lst))
                 (y (cdar lst))
                 (xs (cdr lst)))
             (if (member-equal x rest)
                 nil
               (and (equal (rd x s) y)
                    (separate xs s (cons x rest))))))))

(defun spec (s n pre1 pre2 code post1 post2)
  (implies (separate (append code pre1) s pre2)
           (separate (append code post1) (exec n s) post2)))

(defthm exec-add
  (implies (and (natp m)
                (natp n))
           (equal (exec (+ m n) s)
                  (exec m (exec n s)))))

(defthm spec-compose
  (implies (and (spec s n pre1 pre2 code m1 m2)
                (spec (exec n s) k m1 m2 code post1 post2)
                (natp n)
                (natp k))
           (spec s (+ k n) pre1 pre2 code post1 post2)))

(defun rd-listp (lst s)
  (cond ((atom lst) t)
        (t (and (equal (rd (caar lst) s)
                       (cdar lst))
                (rd-listp (cdr lst) s)))))

(defthm rd-listp-append
  (equal (rd-listp (append x y) s)
         (and (rd-listp x s)
              (rd-listp y s))))

(defthm separate-thm
  (equal (separate xs s rest)
         (and (rd-listp xs s)
              (bag::unique (append (strip-cars xs) rest)))))

; ACL2's heuristics are timid about opening up calls of the form (exec n s),
; even for n a natural number constant, so we prove the following lemma.

(defthm exec-open
  (and (implies (not (zp n))
                (equal (exec n s)
                       (exec (1- n)
                             (bump-pc (next (rd-pc s) s)))))
       (implies (zp n)
                (equal (exec n s)
                       s))))

(defthm strip-cars-append
  (equal (strip-cars (append x y))
         (append (strip-cars x)
                 (strip-cars y))))

(defthm rd-listp-open
  (and (equal (rd-listp nil s) t)
       (equal (rd-listp (cons (cons a v) rest) s)
              (and (equal (rd a s) v)
                   (rd-listp rest s)))))

(local (in-theory (disable rd-listp)))

; The proof of spec-body (below) seems to have at least one case that assumes
; (EQUAL (RD 0 S) (+ 18 P)) and seems to require substitution of (+ 18 P) for
; (RD 0 S) in order to prove efficiently, e.g., without destructor elimination
; and an explicit case split in the output.  ACL2 substitutes the "smaller"
; term for the "larger" in such cases, and unfortunately, (RD 0 S) is deemed to
; be "smaller" than (+ 18 P) -- specifically,
; (term-order '(RD '0 S) '(binary-+ '18 P)) holds, because the two terms have
; the same number of function symbols and variables, so the order is determined
; by the so-called pseudo-fn count, which is based on the sizes of constants.
; We get around this problem by introducing a term equivalent to (rd 0 s) that
; is larger in the term-order than terms such as (binary-+ '18 P), by adding an
; unused variable.  Then we prove a rewrite rule, rd-pc-hack-intro below, that
; introduces the new, more complex form of (rd-pc s).  We call this the "rd-pc
; hack".

(defun rd-pc-hack (s ign)
  (declare (ignore ign))
  (rd-pc s))

(defthm rd-pc-hack-cons
  (and (equal (rd-pc-hack (cons (cons 0 x) s) ign)
              x)
       (implies (not (equal i 0))
                (equal (rd-pc-hack (cons (cons i x) s) ign)
                       (rd-pc-hack s ign)))))

(defthm rd-pc-hack-intro
  (equal (rd 0 s)
         (rd-pc-hack s s)))

(in-theory (disable rd-pc-hack))

; End of support for the rd-pc hack.

(defthm next-opener
  (implies
   (syntaxp (or (eq p 'p)
                (case-match p
                  (('BINARY-+ n 'p)
                   (quotep n)))))
   (equal (next p s)
          (let* ((i (rd p s))        ; read instruction, part 1
                 (x (rd (+ 1 p) s))  ; read instruction, part 2
                 (y (rd (+ 2 p) s))) ; read instruction, part 3
            (case i
              (0 #|| imm     ||# (wr x y s))
              (1 #|| move    ||# (wr x (rd y s) s))
              (2 #|| load    ||# (wr x (rd (rd y s) s) s))
              (3 #|| store   ||# (wr (rd x s) (rd y s) s))
              (4 #|| back    ||# (wr 0 (if (equal (rd x s) 0) p (- p y)) s))
              (5 #|| forward ||# (wr 0 (if (equal (rd x s) 0) p (+ p y)) s))
              (6 #|| add     ||# (wr x (+ (rd x s) (rd y s)) s))
              (7 #|| addi    ||# (wr x (+ (rd x s) y) s))
              (otherwise s)))))
  :hints (("Goal" :in-theory (enable next))))

(defthm rd-listp-cons
  (implies (not (list::memberp addr (strip-cars lst)))
           (equal (rd-listp lst (cons (cons addr val) s))
                  (rd-listp lst s)))
  :hints (("Goal" :in-theory (enable rd-listp))))

(defthm spec-body ; Can take over 5 minutes on fast machine circa Jan. 2010
  (spec s
        5
        (append (list (cons 0 (+ p 18)))
                (list-for 1 (cons x xs))
                (list-for 2 ys)
                frame)
        (cons 3 rest)
        (rev-code p)
        (append (list (cons 0 (+ p 18)))
                (list-for 1 xs)
                (list-for 2 (cons x ys))
                frame)
        (cons 3 rest)))

(defthm strip-cars-list-in-store-append
  (equal (strip-cars (list-in-store (append x y)))
         (append (strip-cars (list-in-store x))
                 (strip-cars (list-in-store y)))))

(defthm revappend-append
  (bag::perm (revappend x y)
             (append x y)))

(defthm strip-cars-list-in-store-revappend
  (bag::perm (strip-cars (list-in-store (revappend x y)))
             (strip-cars (append (list-in-store x)
                                 (list-in-store y)))))

; Base step for spec-loop:
(defthm spec-loop-base
  (implies (not (consp xs))
           (spec s
                 (1+ (* 5 (len xs)))
                 (append (list (cons 0 (+ p 18)))
                         (list-for 1 xs)
                         (list-for 2 ys)
                         frame)
                 (cons 3 rest)
                 (rev-code p)
                 (append (list (cons 0 (+ p 21)))
                         (list-for 2 (append (reverse xs) ys))
                         frame)
                 (cons 1 (cons 3 rest)))))

(defthm append-revappend
  (equal (append (revappend x y) z)
         (revappend x (append y z))))

; Inductive step for spec-loop:
(defthm spec-loop-step
  (implies (and (consp xs)
                (spec (exec 5 s)
                      (1+ (* 5 (len (cdr xs))))
                      (append (list (cons 0 (+ p 18)))
                              (list-for 1 (cdr xs))
                              (list-for 2 (cons (car xs) ys))
                              frame)
                      (cons 3 rest)
                      (rev-code p)
                      (append (list (cons 0 (+ p 21)))
                              (list-for 2 (append (reverse (cdr xs))
                                                  (cons (car xs) ys)))
                              frame)
                      (cons 1 (cons 3 rest))))
           (spec s
                 (1+ (* 5 (len xs)))
                 (append (list (cons 0 (+ p 18)))
                         (list-for 1 xs)
                         (list-for 2 ys)
                         frame)
                 (cons 3 rest)
                 (rev-code p)
                 (append (list (cons 0 (+ p 21)))
                         (list-for 2 (append (reverse xs) ys))
                         frame)
                 (cons 1 (cons 3 rest))))
  :hints (("Goal"
           :in-theory
           (disable spec-compose spec exec-open list-for rev-code)
           :use ((:instance spec-body
                            (xs (cdr xs))
                            (x (car xs)))
                 (:instance spec-compose
                            (s s)
                            (k (+ 1 (* 5 (LEN (CDR XS)))))
                            (n 5)
                            (pre1 (append (list (cons 0 (+ p 18)))
                                          (list-for 1 xs)
                                          (list-for 2 ys)
                                          frame))
                            (pre2 (cons 3 rest))
                            (post1
                             (cons (cons 0 (+ 21 p))
                                   (append (list-for
                                            2
                                            (revappend (cdr xs)
                                                       (cons (car xs) ys)))
                                           frame)))
                            (post2 (list* 1 3 rest))
                            (code (rev-code p))
                            (m1 (cons (cons 0 (+ 18 p))
                                      (append (list-for 1 (cdr xs))
                                              (list-for 2 (cons (car xs) ys))
                                              frame)))
                            (m2 (cons 3 rest)))))))

; Induction scheme for spec-loop:
(defun spec-loop-induct (xs ys s)
  (if (atom xs)
      (list ys s) ; avoid irrelevant-formals error
    (spec-loop-induct (cdr xs)
                      (cons (car xs) ys)
                      (exec 5 s))))

(defthm spec-loop
  (spec s
        (1+ (* 5 (len xs)))
        (append (list (cons 0 (+ p 18)))
                (list-for 1 xs)
                (list-for 2 ys)
                frame)
        (cons 3 rest)
        (rev-code p)
        (append (list (cons 0 (+ p 21)))
                (list-for 2 (append (reverse xs) ys))
                frame)
        (cons 1 (cons 3 rest)))
  :hints (("Goal" :induct (spec-loop-induct xs ys s)
           :in-theory (union-theories '(spec-loop-base
                                        spec-loop-step
                                        spec-loop-induct)
                                      (theory 'minimal-theory)))))

(defthm spec-init
  (spec s
        2
        (append (list (cons 0 p))
                (list-for 1 xs)
                frame)
        (cons 2 (cons 3 rest))
        (rev-code p)
        (append (list (cons 0 (+ p 18)))
                (list-for 1 xs)
                (list-for 2 nil)
                frame)
        (cons 3 rest))
  :hints (("Goal" :in-theory (e/d (next rd-pc-hack)
                                  (rd-pc-hack-intro)))))

(defthm spec-rev-lemma
  (spec s
        (+ (+ 1 (* 5 (len xs))) 2)
        (append (list (cons 0 p))
                (list-for 1 xs)
                frame)
        (cons 2 (cons 3 rest))
        (rev-code p)
        (append (list (cons 0 (+ p 21)))
                (list-for 2 (append (reverse xs) nil))
                frame)
        (cons 1 (cons 3 rest)))
  :hints (("Goal"
           :in-theory (union-theories '(spec-loop
                                        spec-init
                                        spec-compose
                                        natp-compound-recognizer
                                        (:type-prescription len))
                                      (theory 'minimal-theory))
           :restrict ((spec-compose ((m1 (append (list (cons 0 (+ p 18)))
                                                 (list-for 1 xs)
                                                 (list-for 2 nil)
                                                 frame))
                                     (m2 (cons 3 rest)))))))
  :rule-classes nil)

(defthm true-listp-revappend
  (equal (true-listp (revappend x y))
         (true-listp y)))

(defthm spec-rev
  (implies (true-listp xs) ; reverse could be applied to a string!
           (spec s
                 (+ 3 (* 5 (len xs)))
                 (append (list (cons 0 p))
                         (list-for 1 xs)
                         frame)
                 (cons 2 (cons 3 rest))
                 (rev-code p)
                 (append (list (cons 0 (+ p 21)))
                         (list-for 2 (reverse xs))
                         frame)
                 (cons 1 (cons 3 rest))))
  :hints (("Goal" :use spec-rev-lemma
           :in-theory (union-theories '(true-listp-revappend)
                                      (current-theory 'rd)))))
