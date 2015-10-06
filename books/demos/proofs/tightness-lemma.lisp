; Copyright (C) 2015, Regents of the University of Texas
; Written by Matt Kaufmann, July - September, 2015
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Formalization of proof of Tightness Lemma
; Matt Kaufmann

; First, here is the story behind this lemma.  This summer I largely took a
; break from ACL2 and returned to my roots as a mathematical logician.  To my
; surprise, a lemma arose in a model theory paper I'm co-authoring that could
; be abstracted to something amenable to a straightforward formalization in
; ACL2.  To my dismay, it took me approximately 2 full days (16 hours, actually
; spread over many days) to complete that exercise.

; We begin by presenting an informal description of the lemma and its
; proof.  We then give ACL2 events that implement that description.

; Notation.

; (1) Given a finite sequence s = (s_0,...,s_k), and a set A of natural
; numbers N, let s|+A be the subsequence of s consisting of those s_i
; for which i is in A, and let s|-A be the rest, i.e., s|+(N\A).

; (2) For an ordered set (I,<), an "(I,<)-sequence" is a sequence of
; members of I that is strictly increasing in the sense of <.  We may
; write "I-sequence" when the ordering is understood.

; Abstract Tightness Lemma. We assume all of the following.

; (a) (I,<) forms an infinite totally ordered set containing an infinite
;     strictly increasing sequence i_0 < i_1 < ... .

; (b) n_f is a positive natural number and n_g is a natural number.

; (c) f and g are functions whose domains are the set of I-sequences of
;     length n_f and n_g, respectively.

; (d) P is a unary predicate such that for all I-sequences s1 and
;     s2 of length n_f such that maximum(s1) < minimum(s2), if f(s1) =
;     f(s2) then P(f(s1)).

; (e) Let r = n_f + n_g and let R = {0,...,r-1}.  Then for all strictly
;     <-increasing I-tuples s1 and s2 of length r and every subset A of
;     R of size n_f, f(s1|+A) = g(s1|-A) if and only if f(s2|+A) =
;     g(s2|-A).

; (f) If s1 and s2 are strictly <-increasing I-tuples of length n_f such
;     that P(f(s1)), then P(f(s2)).

; (g) s_f and s_g are disjoint strictly <-increasing I-tuples of length
;     n_f and n_g, respectively, such that f(s_f) = g(s_g).

; Then P(f(s_f)).

; Proof. Our first step is to "move" s_f and s_g from (g) to lie within
; {i_0,...,i_{r-1}}.  More precisely: by (g) and (e) we may choose a
; subset B of {0,...,r-1} such that, letting s* be the I-sequence
; <i_0,...,i_{r-1}>, and letting s_f = s*|+B and s_g = s*|-B, we have:

; (*) f(s*|+B) = g(s*|-B).

; Our plan is to shift the last element of s* way to the right, then
; shift the next-to-last element of s* way to the right (but immediately
; to the left of the already-shifted element), and so on, so that
; ultimately the entirety of s* has been shifted completely to the right
; of s*.  So for each natural number j <= r, define the sequence s_j by:

; s_j(i) = <i_0,...,i_{r-j-1},i_{2r-j},...,i_{2r-1}>

; So s_0 = s* and s_r is the I-sequence <i_r,...,i_{2r-1}>.  A
; straightforward induction shows that for all j <= r, f(s*|+B) =
; f(s_j|+B) = g(s_j|-B).  (Hint: for the base step j=0 use (*) above,
; and for the induction step, use (e) together with the observation that
; either the application of f or the application of g remains
; unchanged.)  In particular, substituting r for j, we obtain f(s*|+A) =
; f(s_r|+A), which by (d) yields P(f(s*|+A)).  By (f), we have
; P(f(s_f)). -|

(in-package "ACL2")

(local (include-book "tightness-lemma-proof"))

(set-enforce-redundancy t)

(encapsulate

; We introduce here the order (I,<) described in (2) of the informal
; description, where I is recognized by the predicate ip and < is represented
; by the binary function i<.  We also introduce a function (i-n n) to represent
; the strictly increasing i_0 i< i_1 i< ... from (a) of the informal
; description.

 ((ip (x) t)
  (i< (x y) t)
  (i-n (n) t))

 (local (defun ip (x) (integerp x)))
 (local (defun i< (x y)
          (and (ip x) (ip y) (< x y))))
 (local (defun i-n (n) n))

 (defthm booleanp-ip
   (booleanp (ip x))
   :rule-classes :type-prescription)
 (defthm booleanp-i<
   (booleanp (i< x y))
   :rule-classes :type-prescription)
 (defthm i<-transitive
   (implies (and (i< x y)
                 (i< y z)
                 (ip x)
                 (ip y)
                 (ip z)
                 )
            (i< x z)))
 (defthm i<-asymmetric
   (implies (and (ip x)
                 (ip y)
                 (i< x y))
            (not (i< y x))))
 (defthm i<-trichotomy
   (implies (and (ip x)
                 (ip y))
            (or (i< x y) (equal x y) (i< y x)))
   :rule-classes nil)
 (defthm i-p-i-n
   (implies (natp n)
            (ip (i-n n))))
 (defthm i-n-increasing
   (implies (natp n)
            (i< (i-n n)
                (i-n (1+ n))))))

(defun i-listp (lst)
  (declare (xargs :guard t))
  (cond ((atom lst) (null lst))
        (t (and (ip (car lst))
                (if (atom (cdr lst))
                    (null (cdr lst))
                  (and (i< (car lst) (cadr lst))
                       (i-listp (cdr lst))))))))

(defun ordered-nat-listp-1 (lst)
  (declare (xargs :guard (nat-listp lst)))
  (cond ((or (endp lst)
             (endp (cdr lst)))
         t)
        (t (and (< (car lst) (cadr lst))
                (ordered-nat-listp-1 (cdr lst))))))

(defun ordered-nat-listp (lst)
  (declare (xargs :guard t))
  (and (nat-listp lst)
       (ordered-nat-listp-1 lst)))

(defun restrict (lst indices posn)

; The notation "s|+A" from (1) in the informal description corresponds to the
; term (restrict s A 0).

  (declare (xargs :guard (and (true-listp lst)
                              (ordered-nat-listp indices)
                              (natp posn)
                              (or (null indices)
                                  (<= posn (car indices))))))
  (cond ((endp lst) nil)
        ((endp indices) nil)
        ((eql posn (car indices))
         (cons (car lst)
               (restrict (cdr lst) (cdr indices) (1+ posn))))
        (t (restrict (cdr lst) indices (1+ posn)))))

(defun co-restrict (lst indices posn)

; The notation "s|-A" from (1) in the informal description corresponds to the
; term (co-restrict s A 0).

  (declare (xargs :guard (and (true-listp lst)
                              (ordered-nat-listp indices)
                              (natp posn)
                              (or (null indices)
                                  (<= posn (car indices))))))
  (cond ((endp lst) nil)
        ((endp indices) lst)
        ((eql posn (car indices))
         (co-restrict (cdr lst) (cdr indices) (1+ posn)))
        (t (cons (car lst)
                 (co-restrict (cdr lst) indices (1+ posn))))))

(encapsulate

; Here, we introduce axioms (b) through (f) from the informal description.
; Below, we use labels from (b) through (f) to indicate how this formalization
; corresponds to that informal description.

 ((p (x) t)
  (i-f (lst) t)    ; (c)
  (i-f-arity () t) ; (b)
  (i-g (lst) t)    ; (c)
  (i-g-arity () t) ; (c)
  )

; The following three ACL2 events can be ignored by those reading this file for
; logical content.  The first two avoid some unnecessary syntactic checks,
; while the third causes ACL2 to do some minimal "type-checking".

 (set-ignore-ok t)
 (set-irrelevant-formals-ok t)
 (set-verify-guards-eagerness 2)

 (local (defun p (x) t))
 (local (defun i-f (lst) t))
 (local (defun i-f-arity () 1))
 (local (defun i-g (lst) t))
 (local (defun i-g-arity () 0))
 (defthm posp-i-f-arity ; (b)
   (posp (i-f-arity))
   :rule-classes :type-prescription)
 (defthm natp-i-g-arity ; (b)
   (natp (i-g-arity))
   :rule-classes :type-prescription)
 (defthmd tightness ; (d)
   (implies (and (i-listp lst1)
                 (i-listp lst2)
                 (equal (len lst1) (i-f-arity))
                 (equal (len lst2) (i-f-arity))
                 (i< (car (last lst1)) (car lst2))
                 (equal (i-f lst1) (i-f lst2)))
            (p (i-f lst1))))
 (defthmd indisc-1 ; (e)
   ;; Some hypotheses are probably redundant.
   (implies (and (i-listp lst1)
                 (i-listp lst2)
                 (equal (len lst1) (len lst2))
                 )
            (let ((f1 (restrict lst1 indices 0))
                  (f2 (restrict lst2 indices 0))
                  (g1 (co-restrict lst1 indices 0))
                  (g2 (co-restrict lst2 indices 0)))
              (implies (and (equal (len f1) (i-f-arity))
                            (equal (len f2) (i-f-arity))
                            (equal (len g1) (i-g-arity))
                            (equal (len g2) (i-g-arity)))
                       (equal (equal (i-f f1) (i-g g1))
                              (equal (i-f f2) (i-g g2)))))))
 (defthmd indisc-2 ; (f)
   (implies (and (p (i-f lst1))
                 (i-listp lst1)
                 (i-listp lst2)
                 (equal (len lst1) (i-f-arity))
                 (equal (len lst2) (i-f-arity)))
            (p (i-f lst2)))))

(defthm tightness-lemma
  (implies (and (i-listp x)
                (i-listp y)
                (equal (len x) (i-f-arity))
                (equal (len y) (i-g-arity))
                (not (intersectp x y))
                (equal (i-f x) (i-g y)))
           (p (i-f x))))
