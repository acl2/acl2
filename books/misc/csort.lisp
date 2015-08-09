; Copyright (C) 1997  Computational Logic, Inc.
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.
; Authors: Bishop Brock and J Strother Moore

; This book is the ACL2 script accompanying the paper

; A Mechanically Checked Proof of a Comparator Sort Algorithm
;         Bishop Brock and J Strother Moore

; Abstract

; We describe a mechanically checked correctness proof for the
; comparator sort algorithm underlying a microcode program in a
; commercially designed digital signal processing chip.  The abstract
; algorithm uses an unlimited number of systolic comparator modules to
; sort a stream of data.  In addition to proving that the algorithm
; produces an ordered permutation of its input, we prove two theorems
; that are important to verifying the microcode implementation.  These
; theorems describe how positive and negative ``infinities'' can be
; streamed into the array of comparators to achieve certain effects.
; Interesting generalizations are necessary in order to prove these
; theorems inductively.  The mechanical proofs were carried out with
; the ACL2 theorem prover.  We find these proofs both mathematically
; interesting and illustrative of the kind of mathematics that must be
; done to verify software.

; This file is divided into six ``chapters'' by comments to that effect.
; See the above paper for a tour through this file.

; The basis for this work was done at Computational Logic, Inc. under
; a contract to model the Motorola CAP Digitial Signal Processor.  The
; original version of this script was distributed as the ACL2 book
; v2-3/books/cli-misc/comparator-sort.lisp, which was copyrighted by
; Computational Logic, Inc., 1997.  The present script was developed
; as a simplified version of that one.

(in-package "ACL2")

; We start with basic facts unrelated to comparator sorting.

; Chapter 1:  Elementary Stuff

; List Processing

(defun firstn (n l)
  "The sublist of L consisting of its first N elements."
  (declare (xargs :guard (and (true-listp l)
                              (integerp n)
                              (<= 0 n))))
  (cond ((endp l) nil)
        ((zp n) nil)
        (t (cons (car l)
                 (firstn (1- n) (cdr l))))))

(defthm member-equal-car-firstn
  (implies (and (integerp n)
		(<= 1 n)
		(consp lst))
	   (member-equal (car (firstn n lst)) lst)))

(defthm firstn-too-long
  (implies (and (true-listp lst)
                (integerp n)
                (<= (len lst) n))
           (equal (firstn n lst) lst)))

(defun repeat (n x)
  (cond ((zp n) nil)
        (t (cons x (repeat (1- n) x)))))

(defun evnp (n)
  (cond ((zp n) t)
        ((zp (1- n)) nil)
        (t (evnp (1- (1- n))))))

(defun rev (x)
  (cond ((endp x) nil)
        (t (append (rev (cdr x)) (list (car x))))))

(defthm car-append
  (equal (car (append a b))
         (if (consp a) (car a) (car b))))

(defthm assoc-of-append
  (equal (append (append a b) c)
         (append a (append b c))))

(defthm true-listp-append-rewrite
  (equal (true-listp (append a b))
         (true-listp b)))

(defthm len-append
  (equal (len (append x y))
         (+ (len x) (len y))))


; Arithmetic.

(defthm +-constant-folding
  (implies (syntaxp (and (quotep x) (quotep y)))
	   (equal (+ x (+ y z)) (+ (+ x y) z))))

; Facts about Perm

(defun delete-equal (x lst)
  (cond ((endp lst) nil)
        ((equal x (car lst)) (cdr lst))
        (t (cons (car lst) (delete-equal x (cdr lst))))))

(defun perm (lst1 lst2)
  (cond ((endp lst1) (endp lst2))
        ((member-equal (car lst1) lst2)
         (perm (cdr lst1) (delete-equal (car lst1) lst2)))
        (t nil)))

(defthm perm-reflexive
  (perm x x))

(defthm perm-cons
  (implies (member-equal a x)
           (equal (perm x (cons a y))
                  (perm (delete-equal a x) y)))
  :hints (("Goal" :induct (perm x y))))

(defthm perm-symmetric
  (implies (perm x y) (perm y x)))

(defthm member-equal-delete-equal
  (implies (member-equal a (delete-equal b x))
           (member-equal a x)))

(defthm perm-member-equal
  (implies (and (perm x y)
                (member-equal a x))
           (member-equal a y)))

(defthm member-equal-delete-equal2
  (implies (and (member-equal a x)
                (not (equal a b)))
           (member-equal a (delete-equal b x))))

(defthm comm-delete-equal
  (equal (delete-equal a (delete-equal b x))
         (delete-equal b (delete-equal a x))))

(defthm perm-delete-equal
  (implies (perm x y)
           (perm (delete-equal a x) (delete-equal a y))))

(defthm perm-transitive
  (implies (and (perm x y) (perm y z)) (perm x z)))

(defequiv perm)

(defcong perm perm (cons x y) 2)

(defcong perm iff (member-equal x y) 2)

(defthm atom-perm
  (implies (not (consp x)) (perm x nil))
  :rule-classes :forward-chaining)

; Apologia: The following lemma wasn't necessary until we fixed the
; controller-alist bug.  Of course, this is a pretty reasonable lemma
; to have.

(defthm member-equal-append
  (iff (member-equal e (append x y))
       (or (member-equal e x)
           (member-equal e y))))

(defcong perm perm (append x y) 1)

(defcong perm perm (append x y) 2)

(defthm perm-append-cons
  (perm (append x (cons i y))
        (cons i (append x y))))

(defcong perm equal (len x) 1)

(defthm perm-rev
  (perm (rev x) x))

(defthm perm-append-nil
  (perm (append x nil) x))

(defthm append-repeat
  (equal (append (repeat n x) (list x))
         (cons x (repeat n x))))

(defthm rev-repeat
  (equal (rev (repeat n x)) (repeat n x)))

(defthm len-repeat
  (equal (len (repeat n x)) (nfix n)))

(defthm consp-repeat
  (equal (consp (repeat n x))
         (not (zp n)))
  :hints (("Goal" :expand (REPEAT 1 X))))

(defthm car-repeat
  (equal (car (repeat n x))
         (if (zp n) nil x))
  :hints (("Goal" :expand (REPEAT 1 X))))

; Chapter 2: All-gte, Orderings, etc

(defun data (pair)
  (cdr pair))

(in-theory (disable data))

(defun ordered (lst)
  (cond ((endp lst) t)
        ((endp (cdr lst)) t)
        ((>= (data (car lst)) (data (cadr lst)))
         (ordered (cdr lst)))
        (t nil)))

(defun all-gte (pair lst)
  (cond ((endp lst) t)
        ((and (>= (data pair) (data (car lst)))
              (all-gte pair (cdr lst))))
        (t nil)))

(defthm all-gte-delete-equal-1
  (implies (all-gte pair lst)
           (all-gte pair (delete-equal x lst))))

(defthm all-gte-delete-equal-2
  (implies (and (all-gte pair (delete-equal x lst))
                (>= (data pair) (data x)))
           (all-gte pair lst)))

(encapsulate nil
             (local (defthm lemma
                      (implies (and (perm lst lst-equiv)
                                    ;; Added for mod to ACL2 v2-8 that does
                                    ;; better matching for calls of equivalence
                                    ;; relations against the current context:
                                    (syntaxp (not (term-order lst lst-equiv)))
                                    (all-gte pair lst))
                               (all-gte pair lst-equiv))))
             (defcong perm equal (all-gte pair lst) 2))

(defthm all-gte-implies-gte-member-equal
  (implies (and (all-gte pair1 a)
                (member-equal pair2 a))
           (<= (data pair2) (data pair1)))
  :rule-classes :linear)

(defthm gte-car-firstn
  (implies (and (all-gte pair a)
		(perm a b)
		(integerp n)
		(<= 1 n)
		(consp b))
	   (<= (data (car (firstn n b))) (data pair)))
  :rule-classes nil)

(defthm all-gte-helper
  (implies (and (all-gte pair1 lst)
                (<= (data pair1) (data pair2)))
           (all-gte pair2 lst)))

(defun all-all-gte (lst1 lst2)
  (cond ((endp lst1) t)
        (t (and (all-gte (car lst1) lst2)
                (all-all-gte (cdr lst1) lst2)))))

(defcong perm equal (all-all-gte lst1 lst2) 1)

(defcong perm equal (all-all-gte lst1 lst2) 2)

(defthm all-all-gte-cdr
  (implies (all-all-gte lst acc)
           (all-all-gte lst (cdr acc))))

(defthm ordered-cons
  (implies (all-gte pair1 s)
           (equal (ordered (cons pair1 s))
                  (ordered s))))

(defthm all-gte-append-cons
  (equal (all-gte pair1 (append s (list pair2)))
         (and (all-gte pair1 s)
              (>= (data pair1) (data pair2)))))

(defthm ordered-append
  (equal (ordered (append lst1 lst2))
         (and (ordered lst1)
              (ordered lst2)
              (all-all-gte lst1 lst2))))

(defthm ordered-cons-append-cons
  (implies (and (all-gte pair1 s)
                (>= (data pair1) (data pair2))
                (all-all-gte s (list pair2))
                (ordered s))
           (ordered (CONS pair1 (APPEND S (list pair2)))))
  :rule-classes nil)

(defthm all-all-gte-cons
  (implies (syntaxp (not (equal acc ''nil)))
           (equal (all-all-gte s (cons pair acc))
                  (and (all-all-gte s (list pair))
                       (all-all-gte s acc)))))

(defthm all-all-gte-append1
  (equal (all-all-gte s (append lst1 lst2))
         (and (all-all-gte s lst1)
              (all-all-gte s lst2)))
  :hints (("Goal" :induct (append lst1 lst2))))

(defthm all-all-gte-append2
  (equal (all-all-gte (append lst1 lst2) lst3)
         (and (all-all-gte lst1 lst3)
              (all-all-gte lst2 lst3))))

(defthm all-all-gte-nil
  (all-all-gte lst nil))

(defthm ordered-repeat
  (ordered (repeat n x)))

(defthm all-all-gte-repeat
  (equal (all-all-gte (repeat n maxpair) acc)
         (or (zp n)
             (all-gte maxpair acc)))
  :hints (("Goal" :induct (repeat n maxpair))))

(defthm all-all-gte-repeat-2
  (implies (all-all-gte lst (list minpair))
           (all-all-gte lst (repeat n minpair))))

; Chapter 3: comparator sort.

(defun max-pair (pair1 pair2)
  (cond ((<= (data pair1) (data pair2)) pair2)
        (t pair1)))

(defun min-pair (pair1 pair2)
  (cond ((<= (data pair1) (data pair2)) pair1)
        (t pair2)))

(defun cstep (acc)
  (cond ((endp acc) nil)
        ((endp (cdr acc)) acc)
        (t (cons (max-pair (cadr acc) (car acc))
                 (cons (min-pair (cadr acc) (car acc))
                       (cstep (cddr acc)))))))

(defun cfeed (lst acc)
  (cond ((endp lst) acc)
        (t (cfeed (cdr lst)
                  (cstep (cons (car lst) acc))))))

(defun cdrain (n acc)
  (cond ((zp n) acc)
        (t (cons (car acc)
                 (cdrain (1- n) (cstep (cdr acc)))))))

(defun csort (lst)
  (cdrain (len lst)
          (cfeed lst nil)))

; Chapter 4:  Basic Properties of the Subroutines

(defthm perm-cstep
  (perm (cstep acc) acc))

(defthm perm-cfeed
  (perm (cfeed lst acc) (append lst acc))
  :hints (("Goal" :induct (cfeed lst acc))))

(defthm perm-cdrain
  (implies (<= n (len acc))
           (perm (cdrain n acc) acc)))

; One might wonder why we need the next lemma (and several others like
; it).  The proof of this lemma is obvious given that perm is a congruence
; relation for len.  So one is tempted to conclude that we'll prove it
; whenever we need it.  Wrong.

; The lemma is used to relieve a hyp of the form (<= ... (len a)).  In
; the application, a is bound to (cstep acc), which was rewritten
; under equiv EQUAL.  If we were to retrieve the binding of a and
; rewrite it under equiv PERM, we would simplify (len a) to (len acc).
; But we don't rewrite the binding.  So we have to prove a rewrite
; rule.

(defthm len-cstep
  (equal (len (cstep acc)) (len acc)))

(defthm len-cfeed
  (equal (len (cfeed lst acc))
         (+ (len lst) (len acc))))

(defthm true-listp-cstep
  (implies (true-listp acc)
           (true-listp (cstep acc)))
  :hints (("Goal" :induct (cstep acc))))

(defthm true-listp-cfeed
  (implies (true-listp acc)
           (true-listp (cfeed lst acc))))

(defthm true-listp-cdrain
  (implies (true-listp acc)
           (true-listp (cdrain n acc))))

(defthm len-cdrain
  (implies (and (integerp n)
                (<= n (len acc)))
           (equal (len (cdrain n acc))
                  (len acc))))

(defthm cfeed-opener
  (equal (cfeed (cons pair lst) acc)
         (cfeed lst (cstep (cons pair acc)))))

(defthm cstep-append1
  (implies (evnp (len a))
           (equal (cstep (append a b))
                  (append (cstep a)
                          (cstep b))))
  :rule-classes nil
  :hints (("Goal" :induct (cstep a))))

(defthm cstep-noop
  (implies (and (true-listp acc)
                (ordered acc))
           (equal (cstep acc) acc))
  :hints (("Goal" :induct (cstep acc))))

(defthm cstep-append2
  (implies (and (true-listp b)
                (ordered b)
                (all-all-gte a b))
           (equal (cstep (append a b))
                  (append (cstep a) b)))
  :hints (("Goal" :induct (cstep a))))




; Chapter 5:  Invariant work

(defun phi (acc)
  (cond ((endp acc) t)
        ((endp (cdr acc)) t)
        (t (and (all-gte (car acc) (cdr acc))
                (phi (cddr acc))))))

(defthm all-gte-cstep
  (implies (all-gte x acc)
           (all-gte x (cstep acc)))
  :hints (("Goal" :induct (cstep acc))))

(defthm phi-cstep
  (implies (phi (cdr acc))
           (phi (cstep acc))))

(defthm phi-cons
  (equal (phi (cons pair acc))
         (or (endp acc)
             (and (all-gte pair acc)(phi (cdr acc))))))

(defthm phi-cfeed
  (implies (phi acc)
           (phi (cfeed lst acc)))
  :hints (("Goal" :induct (cfeed lst acc)
           :in-theory (disable cstep))))

; Chapter 6:  The Main Theorems

(defthm perm-csort
  (perm (csort acc) acc))


; Here is the proof that csort orders.

(defthm ordered-firstn-cdrain
  (implies (and (integerp n)
		(<= n (len acc))
		(phi acc))
	   (ordered (firstn (+ 2 n) (cdrain n acc))))
  :hints
  (("Subgoal *1/5"
    :use (:instance gte-car-firstn
		    (a (cdr acc))
		    (b (cDRAIN (+ -1 N)
                               (cSTEP (CDR ACC))))
		    (pair (car acc))
		    (n (+ 1 n))))
   ("Subgoal *1/1"
    :expand ((FIRSTN (+ 2 N) ACC)
	     (FIRSTN (+ 1 N) (cdr ACC))))))

(defthm ordered-csort
  (ordered (csort lst))
  :hints
  (("Goal" :use (:instance ordered-firstn-cdrain
                           (n (len lst))
                           (acc (cfeed lst nil))))))

; Here is the proof of the positive infinity property.  The whole
; key is the following rewrite rule and the induction hint.

(defthm bridge
  (implies
   (and (all-gte pair1 s)
        (>= (data pair1) (data pair2))
        (all-all-gte s (list pair2))
        (evnp (len s))
        (ordered s))
   (equal
    (cstep (cons pair1 (append s (cons pair2 acc))))
    (cons pair1 (append s (cons pair2 (cstep acc))))))
  :hints
  (("Goal"
    :use ((:instance cstep-append1
                     (a (cons pair1 (append s (list pair2))))
                     (b acc))
          (:instance ordered-cons-append-cons
                     (pair1 pair1)
                     (s s)
                     (pair2 pair2))))))

(defun positive-infinity-hint (lst s acc)
  (cond
   ((endp lst) (list s acc))
   (t (positive-infinity-hint (cdr lst)
                              (cons (car lst)
                                    (append s (list (car acc))))
                              (cstep (cdr acc))))))

(defthm positive-infinity-gen
  (implies (and (<= (len lst) (len acc))
                (evnp (len s))
                (ordered s)
                (ordered (rev lst))
                (phi acc)
                (all-all-gte lst s)
                (all-all-gte lst acc)
                (all-all-gte s acc))
           (equal (cfeed lst (append s acc))
                  (append (rev lst)
                          s
                          (cdrain (len lst) acc))))
  :hints
  (("Goal" :induct (positive-infinity-hint lst s acc)))
  :rule-classes nil)

(defthm positive-infinity
  (implies (and (integerp n)
                (<= n (len acc))
                (all-gte maxpair acc)
                (phi acc))
           (equal (cfeed (repeat n maxpair) acc)
                  (append (repeat n maxpair)
                          (cdrain n acc))))
  :hints (("Goal"
           :use (:instance positive-infinity-gen
                                  (lst (repeat n maxpair))
                                  (s nil)
                                  (acc acc)))))
; The negative infinity property is easier.

(defthm negative-infinity-gen
  (implies (and (true-listp acc)
                (all-all-gte lst acc)
                (all-all-gte s acc)
                (ordered acc))
           (equal (cfeed lst (append s acc))
                  (append (cfeed lst s) acc)))
  :hints
  (("Goal" :induct (cfeed lst s)))
  :rule-classes nil)

(defthm negative-infinity
  (implies (all-all-gte lst (list minpair))
           (equal (cfeed lst (repeat n minpair))
                  (append (cfeed lst nil) (repeat n minpair))))
  :hints (("Goal" :use (:instance negative-infinity-gen
                                  (lst lst)
                                  (s nil)
                                  (acc (repeat n minpair))))))
