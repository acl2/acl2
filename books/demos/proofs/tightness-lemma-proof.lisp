; Copyright (C) 2015, Regents of the University of Texas
; Written by Matt Kaufmann, July - September, 2015
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Events supporting tightness-lemma.lisp.  See that file for an informal
; treatment, which is referenced in comments below.

(in-package "ACL2")

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

(defthm i-n-increasing-alt
   (implies (posp n)
            (i< (i-n (1- n))
                (i-n n)))
   :hints (("Goal"
            :in-theory (disable i-n-increasing)
            :use ((:instance i-n-increasing (n (1- n)))))))

; For testing, it is very handy to attach executable functions to our
; constrained functions.

(defun int< (x y)
  (declare (xargs :guard t))
  (and (integerp x)
       (integerp y)
       (< x y)))

(defattach
  (ip natp)
  (i< int<)
  (i-n identity))

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

(defun r () ; (e) from informal description
  (declare (xargs :guard t))
  (+ (i-f-arity) (i-g-arity)))

; Start proof of tightness lemma.  The plan is this: given disjoint x and y
; each satisfying i-listp and having lengths equal to the arities of i-f and
; i-g respectively, we merge those lists and show that their restriction and
; co-restriction to a suitable list J of indices are the original x and y,
; respectively.  Then we move the merged list as in the hand proof, showing by
; induction using indisc-1 (property (e)) that each resulting list still
; satisfies the equality of f on its J-restriction with g on its
; J-co-restriction.

(defun i-merge (x y)

; This function merges disjoint i-listps x and y into an i-listp containing
; each as a subsequence.

  (declare (xargs :guard (and (i-listp x)
                              (i-listp y))
                  :measure (+ (len x) (len y))))
  (cond ((endp x) y)
        ((endp y) x)
        ((i< (car x) (car y))
         (cons (car x)
               (i-merge (cdr x) y)))
        (t
         (cons (car y)
               (i-merge x (cdr y))))))

(defun integers-from (n len)
  (declare (xargs :guard (and (integerp n)
                              (natp len))))
  (cond ((zp len) nil)
        (t (cons n
                 (integers-from (1+ n) (1- len))))))

(defun restrict-indices-from-merge (x y posn)

; Given disjoint i-listps x and y, (restrict-indices-from-merge x y 0) is the
; list of indices from (i-merge x y) that give elements of x.  See
; restrict-to-restrict-indices-from-merge and
; co-restrict-to-restrict-indices-from-merge.

  (declare (xargs :guard (and (i-listp x)
                              (i-listp y)
                              (natp posn))
                  :measure (+ (len x) (len y))))
  (cond ((endp x) nil)
        ((endp y) (integers-from posn (len x)))
        ((i< (car x) (car y))
         (cons posn
               (restrict-indices-from-merge (cdr x) y (1+ posn))))
        (t (restrict-indices-from-merge x (cdr y) (1+ posn)))))

; Start proof of restrict-to-restrict-indices-from-merge.

(local (include-book "arithmetic/top" :dir :system))

(defthm car-integers-from
  (implies (and (natp n)
                (posp len))
           (equal (car (integers-from n len))
                  n)))

(defthm len-of-consp
  (implies (consp x)
           (< 0 (len x)))
  :rule-classes :linear)

(defthm car-restrict-indices-from-merge-inequality
  (implies (and (natp p)
                (consp (restrict-indices-from-merge x y p)))
           (<= p
               (car (restrict-indices-from-merge x y p))))
  :rule-classes :linear)

(defthm restrict-to-restrict-indices-from-merge
  (implies (and (i-listp x)
                (i-listp y)
                (natp posn))
           (let ((indices (restrict-indices-from-merge x y posn)))
             (equal (restrict (i-merge x y) indices posn)
                    x))))

(defthm co-restrict-to-restrict-indices-from-merge
  (implies (and (i-listp x)
                (i-listp y)
                (natp posn))
           (let ((indices (restrict-indices-from-merge x y posn)))
             (equal (co-restrict (i-merge x y) indices posn)
                    y))))

; Next, we introduce a few useful notions and some lemmas about them.  We are
; working towards len-restrict-restrict-indices-from-merge and
; len-co-restrict-restrict-indices-from-merge.

(defun i-from (n len)

; (I-from n len) is the sequence of length len consisting of (i-n k) for k = n,
; n+1, ....

  (declare (xargs :guard (and (integerp n)
                              (natp len))))
  (cond ((zp len) nil)
        (t (cons (i-n n)
                 (i-from (1+ n) (1- len))))))

(defthm i-listp-i-from
  (implies (natp n)
           (i-listp (i-from n len)))
  :hints (("Goal"
           :in-theory (enable i-from)
           :expand ((i-from (+ 1 n) (+ -1 len))))))

(defthm i<-irreflexive
  (implies (ip x)
           (not (i< x x)))
  :hints (("Goal"
           :in-theory (disable i<-asymmetric)
           :use ((:instance i<-asymmetric
                            (x x)
                            (y x))))))

(defthm i<-trichotomy-rewrite
   (implies (and (not (i< x y))
                 (ip x)
                 (ip y))
            (equal (i< y x)
                   (not (equal x y))))
   :hints (("Goal" :use i<-trichotomy)))

(defthm intersectp-cdr
  (implies (intersectp x (cdr y))
           (intersectp x y)))

(defthm i-listp-i-merge
  (implies (and (i-listp x)
                (i-listp y)
                (not (intersectp x y)))
           (i-listp (i-merge x y)))
  :hints (("Goal" :induct (i-merge x y))))

(defthm len-i-from
  (equal (len (i-from n len))
         (nfix len)))

(defthm len-i-merge
  (equal (len (i-merge x y))
         (+ (len x) (len y))))

(defthm len-restrict
  (implies (and (natp n)
                (ordered-nat-listp indices)
                (or (null indices)
                    (and (<= n (car indices))
                         (< (car (last indices))
                            (+ n (len lst))))))
           (equal (len (restrict lst indices n))
                  (len indices))))

(defthm len-restrict-indices-from-merge
  (equal (len (restrict-indices-from-merge x y posn))
         (len x)))

(encapsulate
 ()

 (local (defthm consp-integers-from
          (equal (consp (integers-from n len))
                 (posp len))))

 (defthm ordered-nat-listp-1-integers-from
   (implies (and (natp n)
                 (natp len))
            (ordered-nat-listp-1 (integers-from n len)))))

(defthm ordered-nat-listp-1-restrict-indices-from-merge
  (implies (natp posn)
           (ordered-nat-listp-1 (restrict-indices-from-merge x y posn))))

(defthm nat-listp-restrict-indices-from-merge
  (implies (natp posn)
           (nat-listp (restrict-indices-from-merge x y posn))))

(defthm len-restrict-restrict-indices-from-merge-1-1
  (implies (and (posp k)
                (natp n))
           (< (car (last (integers-from n k)))
              (+ n k))))

(defthm len-restrict-restrict-indices-from-merge-1
  (implies (and (natp n)
                (restrict-indices-from-merge x y n))
           (< (car (last (restrict-indices-from-merge x y n)))
              (+ (len x) (len y) n)))
  :rule-classes :linear)

(defthm len-restrict-restrict-indices-from-merge
  (implies (equal (len lst)
                  (+ (len x) (len y)))
           (equal (len (restrict lst
                                 (restrict-indices-from-merge x y 0)
                                 0))
                  (len x))))

(defthm len-co-restrict
  (implies (and (natp n)
                (ordered-nat-listp indices)
                (or (null indices)
                    (and (<= n (car indices))
                         (< (car (last indices))
                            (+ n (len lst))))))
           (equal (len (co-restrict lst indices n))
                  (- (len lst) (len indices)))))

(defthm len-co-restrict-restrict-indices-from-merge
  (implies (equal (len lst)
                  (+ (len x) (len y)))
           (equal (len (co-restrict lst
                                    (restrict-indices-from-merge x y 0)
                                    0))
                  (len y))))

(in-theory (disable restrict co-restrict i-merge restrict-indices-from-merge
                    integers-from i-from i-listp len))

; We can now prove the lemma corresponding to property (*) from the informal
; proof sketch.

(defthm main-lemma-base
  (implies (and (i-listp x)
                (i-listp y)
                (not (intersectp x y))
                (equal (len x) (i-f-arity))
                (equal (len y) (i-g-arity))
                (equal (i-f x) (i-g y)))
           (let* ((s0 (i-from 0 (r)))
                  (indices (restrict-indices-from-merge x y 0))
                  (f1 (restrict s0 indices 0))
                  (g1 (co-restrict s0 indices 0)))
             (equal (equal (i-f f1) (i-g g1))
                    t)))
  :otf-flg t
  :hints (("Goal"
           :do-not-induct t
           :use
           ((:instance indisc-1
                       (lst1 (i-from 0 (r)))
                       (lst2 (i-merge x y))
                       (indices (restrict-indices-from-merge x y 0)))))))

(defun sn (j r)

; The following example illustrates this function.  The length of the
; increasing sequence is r, and j specifies the position at which we switch
; from i_n to i_{r+n}.

; ACL2 !>(list (sn 0 4) (sn 1 4) (sn 2 4) (sn 3 4) (sn 4 4))
; ((0 1 2 3)
;  (0 1 2 7)
;  (0 1 6 7)
;  (0 5 6 7)
;  (4 5 6 7))
; ACL2 !>

  (declare (xargs :guard (and (natp j)
                              (natp r)
                              (<= j r))))
  (append (i-from 0 (- r j))
          (i-from (+ r r (- j))
                  j)))

(defthm sn-0-is-s0
  (equal (sn 0 r)
         (i-from 0 r))
  :hints (("Goal" :in-theory (enable i-from))))

(defthm sn-r-is-i-from-r
  (equal (sn r r)
         (i-from r r))
  :hints (("Goal" :in-theory (enable i-from))))

(defun main (j indices)
  (declare (xargs :guard (and (natp j)
                              (<= j (r))
                              (ordered-nat-listp indices))))
  (let* ((s* (i-from 0 (r)))
         (s (sn j (r)))
         (f* (restrict s* indices 0))
         (f1 (restrict s indices 0))
         (g1 (co-restrict s indices 0)))
    (and (equal (i-f f1) (i-f f*))
         (equal (i-f f1) (i-g g1)))))

; In an earlier version, main-lemma and then tightness-lemma-main were here,
; each with skip-proofs.  I've moved them back so that other lemmas are
; available when developing their proofs.

(defthm i-listp-restrict-lemma
  (implies (and (i-listp s)
                (ip i)
                (i< i (car s))
                (consp (restrict s indices posn)))
           (i< i (car (restrict s indices posn))))
  :hints (("Goal" :in-theory (enable i-listp restrict))))

(defthm i-listp-restrict
  (implies (i-listp s)
           (i-listp (restrict s indices posn)))
  :hints (("Goal" :in-theory (enable i-listp restrict))))

; Some lemmas that are probably helpful for tightness-lemma-1:

(defthm car-append
  (equal (car (append x y))
         (if (consp x)
             (car x)
           (car y))))

(defthm car-last-append
  (equal (car (last (append x y)))
         (if (consp y)
             (car (last y))
           (car (last x)))))

(defthm last-i-from
  (implies (and (force (natp n))
                (force (posp len)))
           (equal (last (i-from n len))
                  (list (i-n (+ n (1- len))))))
  :hints (("Goal"
           :in-theory (enable i-from)
           :induct (i-from n len))))

(defthm car-i-from
  (implies (force (posp len))
           (equal (car (i-from n len))
                  (i-n n)))
  :hints (("Goal" :expand ((i-from n len)))))

(defthm ip-car-last-restrict
  (implies (and (i-listp s)
                (consp (restrict s indices posn)))
           (ip (car (last (restrict s indices posn)))))
  :hints (("Goal" :in-theory (enable i-listp restrict))))

(encapsulate
 ()

 (local (defthm equal-len-0
          (equal (equal (len x) 0)
                 (not (consp x)))
          :hints (("Goal" :in-theory (enable len)))))

 (defthm consp-restrict-restrict-indices-from-merge
   (implies (equal (len lst)
                   (+ (len x) (len y)))
            (iff (consp (restrict lst
                                  (restrict-indices-from-merge x y 0)
                                  0))
                 (consp x)))
   :hints (("Goal"
            :use len-restrict-restrict-indices-from-merge
            :in-theory (union-theories '(equal-len-0)
                                       (theory 'ground-zero))))))

(defthm i-f-arity-gives-consp
  (implies (equal (len x) (i-f-arity))
           (consp x))
  :hints (("Goal" :expand (len x))))

; start proof of i<-car-last-restrict-1

(defthm i-listp-implies-ip-car-last
  (implies (and (i-listp s)
                (consp s))
           (ip (car (last s))))
  :hints (("Goal" :in-theory (enable i-listp))))

(defthm consp-i-from
  (equal (consp (i-from i len))
         (not (zp len)))
  :hints (("Goal" :in-theory (enable i-from))))

(defthm i<-car-last-restrict-2
   (implies (and (natp i)
                 (posp len))
            (equal (car (last (i-from i len)))
                   (i-n (1- (+ i len)))))
   :hints (("Goal"
            :in-theory (enable restrict i-from len posp)
            :induct (i-from i len))))

(defun add1-induction (n)
  (if (zp n)
      n
    (add1-induction (1- n))))

(defthm not-equal-i-n-successors
  (implies (natp i)
           (not (equal (i-n (+ 1 i)) (i-n i))))
  :hints (("Goal"
           :in-theory (disable i-n-increasing)
           :use ((:instance i-n-increasing (n i))))))

(defthm i-n-increasing-strong-lemma
  (implies (and (i< (i-n i) (i-n (+ -1 j)))
                (natp i)
                (natp j)
                (< i j))
           (i< (i-n i) (i-n j)))
  :hints (("Goal"
           :in-theory (disable i<-transitive)
           :use ((:instance i<-transitive
                            (x (i-n i))
                            (y (i-n (1- j)))
                            (z (i-n j)))))))

(defthm i-n-increasing-strong
  (implies (and (natp i)
                (natp j)
                (< i j))
           (i< (i-n i)
               (i-n j)))
  :hints (("Goal" :induct (add1-induction j))))

(defthm consp-restrict-implies-posp-len
  (implies (consp (restrict (i-from i len) indices posn))
           (posp len))
  :hints (("Goal" :in-theory (enable i-from restrict)))
  :rule-classes :forward-chaining)

(defthm i<-car-last-restrict-1
  (implies (and (ip i0)
                (i-listp s)
                (consp (restrict s indices posn))
                (i< (car (last s)) i0))
           (i< (car (last (restrict s indices posn)))
               i0))
  :hints (("Goal"
           :in-theory (enable restrict i-from i-listp)
           :expand (restrict s indices posn)))
  :rule-classes nil)

(defthm i<-car-last-restrict

; I think I might have first proved this in order to prove a lemma (which I
; called tightness-lemma-1-1) that is no longer needed -- but this lemma is
; indeed needed.

  (implies (and (natp i)
                (natp len)
                (consp (restrict (i-from i len) indices posn))
                (natp k)
                (<= (+ i len) k))
           (i< (car (last (restrict (i-from i len) indices posn)))
               (i-n k)))
  :hints (("Goal" :use ((:instance i<-car-last-restrict-1
                                   (s (i-from i len))
                                   (i0 (i-n k)))))))

; start proof of main-lemma-induction-step

(defun lists-agree-mod-position (lst1 lst2 posn)
  (cond ((endp lst1) (endp lst2))
        ((endp lst2) nil)
        ((eql posn 0)
         (equal (cdr lst1) (cdr lst2)))
        (t (and (equal (car lst1) (car lst2))
                (lists-agree-mod-position (cdr lst1) (cdr lst2) (1- posn))))))

(defthmd restrict-agrees-when-lists-agree-mod-position
  (implies (and (not (member (+ posn1 posn2) indices))
                (ordered-nat-listp indices)
                (natp posn1)
                (natp posn2)
                (lists-agree-mod-position lst1 lst2 posn1))
           (equal (equal (restrict lst1 indices posn2)
                         (restrict lst2 indices posn2))
                  t))
  :hints (("Goal" :in-theory (enable restrict ordered-nat-listp))))

(defthmd co-restrict-agrees-when-lists-agree-mod-position
  (implies (and (member (+ posn1 posn2) indices)
                (ordered-nat-listp indices)
                (natp posn1)
                (natp posn2)
                (<= posn2 (car indices))
                (lists-agree-mod-position lst1 lst2 posn1))
           (equal (equal (co-restrict lst1 indices posn2)
                         (co-restrict lst2 indices posn2))
                  t))
  :hints (("Goal" :in-theory (enable co-restrict ordered-nat-listp))))

; start proof of main-lemma-induction-step-lemma-1

(defthm lists-agree-mod-position-append-i-from-i-from
  (implies (and (natp k1)
                (posp k3))
           (lists-agree-mod-position
            (append (i-from k0 (+ 1 k1))
                    (i-from (1+ k2) (1- k3)))
            (append (i-from k0 k1)
                    (i-from k2 k3))
            k1))
  :hints (("Goal"
           :in-theory (e/d (i-from) ((i-from)))
           :expand ((append (i-from k0 1)
                            (i-from (+ 1 k2) (1- k3)))
                    (i-from k0 1))
           :induct (list (i-from k0 k1)))))

(defthm consp-append
  (equal (consp (append x y))
         (or (consp x) (consp y))))

(defthm main-lemma-induction-step-lemma-1-1
  (implies (and (not (zp j))
                (<= j (r))
                (ordered-nat-listp indices)
                (equal (len indices) (i-f-arity))
                (< (car (last indices)) (r))
                (not (member (- (r) j) indices)))
           (equal (restrict (sn (+ -1 j) (r)) indices 0)
                  (restrict (sn j (r))        indices 0)))
  :hints (("Goal"
           :use
           ((:instance
             restrict-agrees-when-lists-agree-mod-position
             (posn1 (- (r) j))
             (posn2 0)
             (lst1 (append (i-from 0
                                   (1+ (- (r) j)))
                           (i-from (1+ (- (+ (r) (r)) j))
                                   (1- j))))
             (lst2 (append (i-from 0 (- (r) j))
                           (i-from (+ (r) (r) (- j))
                                   j)))))))
  :rule-classes nil)

(defthm main-lemma-induction-step-lemma-1-2
  (implies (and (not (zp j))
                (<= j (r))
                (ordered-nat-listp indices)
                (equal (len indices) (i-f-arity))
                (< (car (last indices)) (r))
                (member (- (r) j) indices))
           (equal (co-restrict (sn (+ -1 j) (r)) indices 0)
                  (co-restrict (sn j (r))        indices 0)))
  :hints (("Goal"
           :use
           ((:instance
             co-restrict-agrees-when-lists-agree-mod-position
             (posn1 (- (r) j))
             (posn2 0)
             (lst1 (append (i-from 0
                                   (1+ (- (r) j)))
                           (i-from (1+ (- (+ (r) (r)) j))
                                   (1- j))))
             (lst2 (append (i-from 0 (- (r) j))
                           (i-from (+ (r) (r) (- j))
                                   j)))))))
  :rule-classes nil)

(defthm main-lemma-induction-step-lemma-1
  (implies (and (not (zp j))
                (<= j (r))
                (ordered-nat-listp indices)
                (equal (len indices) (i-f-arity))
                (< (car (last indices)) (r)))
           (or (equal (restrict (sn (+ -1 j) (r)) indices 0)
                      (restrict (sn j (r))        indices 0))
               (equal (co-restrict (sn (+ -1 j) (r)) indices 0)
                      (co-restrict (sn j (r))        indices 0))))
  :hints (("Goal" :use (main-lemma-induction-step-lemma-1-1
                        main-lemma-induction-step-lemma-1-2)))
  :rule-classes nil)

; start proof of main-lemma-induction-step-lemma-2

(defthm len-append
  (equal (len (append x y))
         (+ (len x) (len y)))
  :hints (("Goal" :in-theory (enable len))))

(defthm i-listp-append
  (implies (true-listp x)
           (equal (i-listp (append x y))
                  (and (i-listp x)
                       (i-listp y)
                       (or (null x)
                           (null y)
                           (i< (car (last x)) (car y))))))
  :hints (("Goal" :in-theory (enable i-listp))))

(defthm i-from-iff
  (iff (i-from i j)
       (not (zp j)))
  :hints (("Goal" :in-theory (enable i-from))))

#||
(defthm main-lemma-induction-step-lemma-2
  (implies (and (natp j)
                (<= j (r))
                (ordered-nat-listp indices)
                (equal (len indices) (i-f-arity))
                (< (car (last indices)) (r))
                (equal (i-f (restrict (i-from 0 (r)) indices 0))
                       (i-g (co-restrict (i-from 0 (r))
                                         indices 0))))
           (equal (i-f (restrict (sn j (r)) indices 0))
                  (i-g (co-restrict (sn j (r)) indices 0))))

; I rarely leave :instructions in a book.  But the proof without :instructions
; is ugly, too!  However, it may be less brittle, so I'll leave this
; :instructions-based proof in a comment, and put the proof I found without
; :instructions below.

  :instructions (:bash (:use (:instance indisc-1 (lst1 (i-from 0 (r)))
                                        (lst2 (sn j (r)))))
                       :bash (:contrapose 1)
                       (:dv 1)
                       (:rewrite len-restrict)
                       :top
                       :prove :prove
                       :prove :prove
                       :prove :prove))
||#

(defthm main-lemma-induction-step-lemma-2
  (implies (and (natp j)
                (<= j (r))
                (ordered-nat-listp indices)
                (equal (len indices) (i-f-arity))
                (< (car (last indices)) (r))
                (equal (i-f (restrict (i-from 0 (r)) indices 0))
                       (i-g (co-restrict (i-from 0 (r))
                                         indices 0))))
           (equal (i-f (restrict (sn j (r)) indices 0))
                  (i-g (co-restrict (sn j (r)) indices 0))))
  :hints (("Goal"
           :in-theory (disable len-restrict len-co-restrict)
           :use
           ((:instance len-restrict
                       (lst (i-from 0 (+ (i-f-arity) (i-g-arity))))
                       (indices indices)
                       (n 0))
            (:instance len-co-restrict
                       (lst (i-from 0 (+ (i-f-arity) (i-g-arity))))
                       (indices indices)
                       (n 0))
            (:instance len-co-restrict
                       (lst (i-from (+ (i-f-arity) (i-g-arity))
                                    (+ (i-f-arity) (i-g-arity))) )
                       (indices indices)
                       (n 0))
            (:instance len-co-restrict
                       (lst
                        (append (i-from 0 (+ (i-f-arity) (i-g-arity) (- j)))
                                (i-from (+ (i-f-arity)
                                           (i-f-arity)
                                           (i-g-arity)
                                           (i-g-arity)
                                           (- j))
                                        j)) )
                       (indices indices)
                       (n 0))
            (:instance len-restrict
                       (lst (append
                             (i-from 0 (+ (i-f-arity) (i-g-arity) (- j)))
                             (i-from (+ (i-f-arity)
                                        (i-f-arity)
                                        (i-g-arity)
                                        (i-g-arity)
                                        (- j))
                                     j)))
                       (indices indices)
                       (n 0))
            (:instance indisc-1
                       (lst1 (i-from 0 (r)))
                       (lst2 (sn j (r))))))))

(defthm main-lemma-induction-step

; This is perhaps the key lemma in the entire proof.  From this, we obtain
; main-lemma, which is key for tightness-lemma-main.

  (implies (and (not (zp j))
                (main (+ -1 j) indices)
                (main 0 indices)
                (natp j)
                (<= j (r))
                (ordered-nat-listp indices)
                (equal (len indices) (i-f-arity))
                (< (car (last indices)) (r)))
           (main j indices))
  :hints (("Goal" :use (main-lemma-induction-step-lemma-1
                        main-lemma-induction-step-lemma-2))))

(defthm main-lemma

; This is the main lemma, proved by induction on j.  The base step is trivial,
; and the induction step is proved just above.

  (implies (and (main 0 indices)
                (natp j)
                (<= j (r))
                (ordered-nat-listp indices)
                (equal (len indices) (i-f-arity))
                (< (car (last indices)) (r)))
           (main j indices))
  :hints (("Goal"
           :in-theory (disable main)
           :induct (add1-induction j)))
  :rule-classes nil)

(defthm car-last-restrict-indices-from-merge-bound
  (implies (and (natp posn)
                (consp x))
           (< (car (last (restrict-indices-from-merge x y posn)))
              (+ (len x) (len y) posn)))
  :hints (("Goal" :in-theory (enable restrict-indices-from-merge len)))
  :rule-classes :linear)

(defthm tightness-lemma-main

; In order to show (using notation from the informal proof) that P(f(s*|+A)) --
; i.e., to prove tightness-lemma-1 below -- we prove here that f(s*|+A) =
; f(s_r|+A).

  (implies (and (i-listp x)
                (i-listp y)
                (equal (len x) (i-f-arity))
                (equal (len y) (i-g-arity))
                (not (intersectp x y))
                (equal (i-f x) (i-g y)))
           (let ((indices (restrict-indices-from-merge x y 0)))
             (equal (i-f (restrict (i-from  0  (r)) indices 0))
                    (i-f (restrict (i-from (r) (r)) indices 0)))))
  :hints (("Goal" :in-theory (disable main-lemma-base)
           :use (main-lemma-base
                 (:instance main-lemma
                            (j (r))
                            (indices (restrict-indices-from-merge x y 0))))))
  :rule-classes nil)

(defthm tightness-lemma-1

; This is the main goal, to prove, using notation from the informal proof,
; P(f(s*|+A)).  Once we have proved this, it is a short step to show P(f(s_f)).

  (implies (and (i-listp x)
                (i-listp y)
                (equal (len x) (i-f-arity))
                (equal (len y) (i-g-arity))
                (not (intersectp x y))
                (equal (i-f x) (i-g y)))
           (p (i-f (restrict (i-from 0 (r))
                             (restrict-indices-from-merge x y 0)
                             0))))
  :hints (("Goal"
           :use
           (tightness-lemma-main
            (:instance tightness
                       (lst1 (restrict (i-from 0 (r))
                                       (restrict-indices-from-merge x y 0)
                                       0))
                       (lst2 (restrict (i-from (r) (r))
                                       (restrict-indices-from-merge x y 0)
                                       0)))))))

(defthm tightness-lemma
  (implies (and (i-listp x)
                (i-listp y)
                (equal (len x) (i-f-arity))
                (equal (len y) (i-g-arity))
                (not (intersectp x y))
                (equal (i-f x) (i-g y)))
           (p (i-f x)))
  :hints (("Goal"
           :use (tightness-lemma-1
                 (:instance indisc-2 ; (f)
                            (lst1 (restrict (i-from 0 (r))
                                            (restrict-indices-from-merge x y 0)
                                            0))
                            (lst2 x))))))
