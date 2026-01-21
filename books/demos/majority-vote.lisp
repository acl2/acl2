; Copyright (C) 2008, Regents of the University of Texas
; Written by J Strother Moore
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Correctness of the Linear Time Majority Vote Algorithm
; Robert S. Boyer and J Strother Moore
; July 11, 2008

; (certify-book "majority-vote")

; This algorithm was invented by Boyer and Moore in 1980 and its proof of
; correctness was originally carried out using the FORTRAN VCG and Nqthm
; prover, as reported in the 1991 paper ``MJRTY - A Fast Majority Vote
; Algorithm,'' R.S. Boyer and J Moore. In R.S. Boyer (ed.), Automated
; Reasoning: Essays in Honor of Woody Bledsoe, Automated Reasoning Series,
; Kluwer Academic Publishers, Dordrecht, The Netherlands, 1991, pp. 105-117.

; The long gap between its invention and publication of our 1991 paper is
; explained in Section 5.8 of that paper and bears repeating here:

;   The algorithm described here was invented in 1980 while we worked at SRI
;   International.  A colleague at SRI, working on fault tolerance, was trying
;   to specify some algorithms using the logic supported by the ``Boyer-Moore
;   Theorem Prover.''  He asked us for an elegant definition within that logic
;   of the notion of the majority element of a list.  Our answer to this
;   challenge was the recursive expression of the algorithm described below.

;   In late 1980, we wrote a Fortran version of the algorithm and proved it
;   correct mechanically.  In February, 1981, we wrote this paper, describing
;   that work.  In our minds the paper was noteworthy because it simultaneously
;   announced an interesting new algorithm and offered a mechanically checked
;   correctness proof.  We submitted the papoer for publication.

;   In 1981 we moved to the University of Texas.  Jay Misra, a colleague at UT,
;   heard our presentation of the algorithm to an NSF site-visit team.
;   According to Misra (private communication, 1990): ``I wondered how to
;   generalize [the algorithm] to detect elements that occur more than n/k
;   times, for all k, k>=2.  I developed algorithm 2 [given in Section 3 of
;   [9]] which is directly inspired by your algorithm.  Also, I showed that
;   this algorithm is optimal [Section 5, op. cit.].  On a visit to Cornell, I
;   showed all this to David Gries; he was inspired enough to contribute
;   algorithm 1 [Section 2, op. cit.].'' In 1982, Misra and Gries published
;   their work ``[9]'', citing our technical report appropriately as
;   ``submitted for publication.''

;   However, our paper was repeatedly rejected for publication, largely because
;   of its emphasis on Fortran and mechanical verification.  A rewritten
;   version emphasizing the algorithm itself was rejected on the grounds that
;   the work was superceded by the paper of Misra and Gries!

; The Misra-Gries paper, referred to as [9] in the extract above, is

; [9] J. Misra and D. Gries (1982): Finding Repeated Elements. Science of
;     Computer Programming 2, 143-152.

; The problem of proving the majority vote algorithm correct has been used,
; since 1981, as an exercise in Boyer and Moore's ``Recursion and Induction''
; class at the University of Texas at Austin's Computer Science Department.
; Eventually, in 2008, this ACL2 version of the proof was prepared but never
; posted (to encourage students to figure it out for themselves).  But finally,
; in 2025, we decided to include this file in the ACL2 regression suite.

(in-package "ACL2")
(include-book "xdoc/top" :dir :system)

(defxdoc majority-vote
  :parents (miscellaneous)
  :short "A Linear Time Majority Vote Algorithm"
  :long "<p>In this book we prove the correctness of a linear time majority
  vote algorithm: given a list of elements determine which element occurs a
  majority of times in the list, assuming some such element occurs.  The
  algorithm was invented by Bob Boyer and J Moore in 1980 and verified with
  their Nqthm theorem prover.  However, the proof was not published until 1991.
  This proof is done in ACL2.  For a detailed history of the algorithm, its
  proof, and its publication, see the long comment at the top of the
  majority-vote.lisp book.</p>")

(defun majority (c i lst)
  (if (endp lst)
      c
    (if (equal i 0)
        (majority (car lst) 1 (cdr lst))
      (majority c (+ i (if (equal c (car lst)) +1 -1)) (cdr lst)))))

(defun how-many (e x)
  (cond
   ((endp x)
    0)
   ((equal e (car x))
    (1+ (how-many e (cdr x))))
   (t
    (how-many e (cdr x)))))

; This is the generalized theorem that explains how majority works on any c and
; i instead of just on the initial c=nil and i=0.

; The way to imagine (majority c i x) is that we started with
; a bigger x' that contains i occurrences of c follwed by x:
; x' = (c c ... c . x).  We "know" that (majority nil 0 x') finds
; the majority in x' IF THERE IS ONE.

; So the generalized theorem supposes that e occurs a majority of times in x'.
; We can say that in terms of c, i, and x: the number of times e occurs in x
; plus i (if e is c) is greater than half of the length of x plus i.

; The conclusion states that (majority c i x) is e.  We write it as (equal
; (equal lhs rhs) t) because rhs contains (is) a free var, namely e.

(defthm majority-general
  (implies (and (natp i)
                (< (* 1/2 (+ i (len x)))
                   (+ (if (equal e c) i 0) (how-many e x))))
           (equal (equal (majority c i x) e) t)))

; Main Theorem: If c is in a majority element of lst, then the majority
; function returns c.

(defthm majority-is-correct
  (implies (< (* 1/2 (len lst)) (how-many c lst))
           (equal (majority nil 0 lst) c)))

; Corollary: If there exists a majority element then majority returns a
; majority element.

(defthm exists-majority-implies-majority
  (implies (< (* 1/2 (len lst)) (how-many c lst))
           (< (* 1/2 (len lst)) (how-many (majority nil 0 lst) lst))))

; This is equivalent to its contrapositive, which says that if the majority
; function returns something not in the majority, then there exists no
; majority.












