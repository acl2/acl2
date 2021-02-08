;; Copyright (C) 2016, Regents of the University of Texas
;; Written by Cuong Chau (derived from earlier work of Brock and Hunt)
;; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

;; See the README for historical information.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; August 2016

(in-package "FM9001")

(include-book "utils")

(include-book "std/lists/repeat" :dir :system)

;; ======================================================================

(defun assoc-eq-value (x alist)
  (declare (xargs :guard (and (symbolp x)
                              (alistp alist))))
  (cdr (assoc-eq x alist)))

(defthm assoc-eq-value-cons-1
  (implies (equal x (car pair))
           (equal (assoc-eq-value x (cons pair alist))
                  (cdr pair))))

(defthm assoc-eq-value-cons-2
  (implies (not (equal x (car pair)))
           (equal (assoc-eq-value x (cons pair alist))
                  (assoc-eq-value x alist))))

;; Necessary for some proofs with lots of signals, otherwise stack overflow
;; occurs from deeply nested rewriting!  This lemma also speeds up proofs
;; significantly if the modules have lots of single output gates.

(defthm rewrite-assoc-eq-value-4x
  (equal (assoc-eq-value a
                         (cons (cons b c)
                               (cons (cons d e)
                                     (cons (cons g h)
                                           (cons (cons i j)
                                                 k)))))
         (if (equal a b)
             c
           (if (equal a d)
               e
             (if (equal a g)
                 h
               (if (equal a i)
                   j
                 (assoc-eq-value a k)))))))

(defthm assoc-eq-value-append-pairlis$
  (equal (assoc-eq-value a (append (pairlis$ b c) alist))
         (if (member a b)
             (assoc-eq-value a (pairlis$ b c))
           (assoc-eq-value a alist))))

;; Not sure we always want this one firing
(defthmd assoc-eq-value-pairlis$-member
  (implies (member name names)
           (equal (assoc-eq-value name (pairlis$ names values))
                  (car (nthcdr (position1 name names) values))))
  :hints (("Goal" :in-theory (enable position1))))

(defthm assoc-eq-value-pairlis$-not-member
  (implies (not (member name names))
           (not (assoc-eq-value name (pairlis$ names values)))))

(defthm assoc-eq-value-update-alist-1
  (implies (and (equal occ-name1 occ-name2)
                (consp (assoc-eq occ-name2 sts-alist)))
           (equal (assoc-eq-value occ-name1
                                  (update-alist occ-name2 sts sts-alist))
                  sts))
  :hints (("Goal" :in-theory (enable update-alist))))

(defthm assoc-eq-value-update-alist-2
  (implies (not (equal occ-name1 occ-name2))
           (equal (assoc-eq-value occ-name1
                                  (update-alist occ-name2 sts sts-alist))
                  (assoc-eq-value occ-name1
                                  sts-alist)))
  :hints (("Goal" :in-theory (enable update-alist))))

(defthmd assoc-eq-value-nth-pairlis$
  (implies (and (<= 0 n)
                (< n (len keys))
                (no-duplicatesp keys)
                (<= (len keys) (len vals)))
           (equal (assoc-eq-value (nth n keys)
                                  (pairlis$ keys vals))
                  (nth n vals))))

(defthm assoc-eq-value-of-si-pairlis$-sis
  (implies (and (natp m)
                (posp n)
                (natp i)
                (<= m i)
                (< i (+ m n))
                (<= n (len vals)))
           (equal (assoc-eq-value (si s i)
                                  (pairlis$ (sis s m n) vals))
                  (nth (- i m) vals)))
  :hints (("Goal"
           :use (si-is-nth-of-sis
                 (:instance assoc-eq-value-nth-pairlis$
                            (n (- i m))
                            (keys (sis s m n)))))))

(in-theory (disable assoc-eq-value))

(defun assoc-eq-values (syms alist)
  (declare (xargs :guard (and (symbol-listp syms)
                              (alistp alist))))
  (if (atom syms)
      nil
    (cons (assoc-eq-value (car syms) alist)
          (assoc-eq-values (cdr syms) alist))))

(defthm len-assoc-eq-values
  (equal (len (assoc-eq-values syms alist))
         (len syms)))

(defthm pairlis$-assoc-eq-values
  (implies (and (no-duplicatesp syms)
                (alistp alist)
                (equal syms (strip-cars alist)))
           (equal (pairlis$ syms (assoc-eq-values syms alist))
                  alist)))

(defthm assoc-eq-values-cons-not-member
  (implies (not (member (car pair) syms))
           (equal (assoc-eq-values syms (cons pair alist))
                  (assoc-eq-values syms alist))))

(defthm assoc-eq-values-append-pairlis$
  (implies (and (no-duplicatesp x)
                (true-listp a)
                (equal (len x) (len a)))
           (equal (assoc-eq-values x (append (pairlis$ x a) alist))
                  a)))

(defthm assoc-eq-values-append-when-disjoint-1
  (implies (disjoint syms (strip-cars x))
           (equal (assoc-eq-values syms (append x y))
                  (assoc-eq-values syms y))))

(defthm assoc-eq-values-append-when-disjoint-2
  (implies (disjoint (strip-cars x) syms)
           (equal (assoc-eq-values syms (append x y))
                  (assoc-eq-values syms y))))

(defthm assoc-eq-values-atom
  (implies (atom args)
           (not (assoc-eq-values args alist))))

(defthm consp-assoc-eq-values
  (equal (consp (assoc-eq-values args alist))
         (consp args)))

(defthm assoc-eq-values-append
  (equal (assoc-eq-values (append a b) alist)
         (append (assoc-eq-values a alist)
                 (assoc-eq-values b alist))))

(defthm assoc-eq-values-append-pairlis$-when-subset
  (implies (subsetp args1 args2)
           (equal (assoc-eq-values args1 (append (pairlis$ args2 answer)
                                                 x))
                  (assoc-eq-values args1 (pairlis$ args2 answer)))))

(defthm assoc-eq-values-append-pairlis$-when-disjoint-1
  (implies (disjoint args1 args2)
           (equal (assoc-eq-values args1 (append (pairlis$ args2 a)
                                                 b))
                  (assoc-eq-values args1 b))))

(defthm assoc-eq-values-append-pairlis$-when-disjoint-2
  (implies (disjoint args2 args1)
           (equal (assoc-eq-values args1 (append (pairlis$ args2 a)
                                                 b))
                  (assoc-eq-values args1 b))))

(defthm assoc-eq-values-take-1
  (implies (and (no-duplicatesp l)
                (<= n (len l))
                (true-listp x)
                (equal (len l) (len x)))
           (equal (assoc-eq-values (take n l)
                                   (pairlis$ l x))
                  (take n x))))

(defthm assoc-eq-values-take-2
  (implies (and (no-duplicatesp args)
                (<= n (len args)))
           (equal (assoc-eq-values (take n args)
                                   (pairlis$ args answer))
                  (assoc-eq-values (take n args)
                                   (pairlis$ (take n args)
                                             (take n answer))))))

(defthm assoc-eq-values-nthcdr-1
  (implies (and (no-duplicatesp l)
                (true-listp x)
                (equal (len l) (len x)))
           (equal (assoc-eq-values (nthcdr n l)
                                   (pairlis$ l x))
                  (nthcdr n x))))

(defthm assoc-eq-values-nthcdr-2
  (implies (no-duplicatesp args)
           (equal (assoc-eq-values (nthcdr n args)
                                   (pairlis$ args answer))
                  (assoc-eq-values (nthcdr n args)
                                   (pairlis$ (nthcdr n args)
                                             (nthcdr n answer))))))

(defthm not-member-take-nthcdr-lemma
  (implies (and (not (member x l))
                (<= 0 n2)
                (<= (+ n1 n2) (len l)))
           (not (member x (take n1 (nthcdr n2 l))))))

(defthm assoc-eq-values-take-nthcdr
  (implies (and (no-duplicatesp l)
                (<= 0 n2)
                (<= (+ n1 n2) (len l))
                (true-listp x)
                (equal (len l) (len x)))
           (equal (assoc-eq-values (take n1 (nthcdr n2 l))
                                   (pairlis$ l x))
                  (take n1 (nthcdr n2 x))))
  :hints (("Subgoal *1/1"
           :in-theory (disable assoc-eq-values-take-1)
           :use (:instance assoc-eq-values-take-1
                           (n n1)))))

(defthm assoc-eq-values-cons
  (equal (assoc-eq-values (cons a b) alist)
         (cons (assoc-eq-value a alist)
               (assoc-eq-values b alist))))

(defthm singleton-assoc-eq-values
  (implies (equal (len a) 1)
           (equal (assoc-eq-values a alist)
                  (list (assoc-eq-value (car a) alist)))))

(defthm assoc-eq-values-args-pairlis$-args
  (implies (and (no-duplicatesp args)
                (equal (len args) (len list))
                (true-listp list))
           (equal (assoc-eq-values args (pairlis$ args list))
                  list)))

;; ASSOC-EQ-VALUES-SPLITTING-CROCK is used to force a rewrite which goes
;; "against the grain" of the normal rewriting direction of
;; ASSOC-EQ-VALUES-APPEND.

(defthmd assoc-eq-values-splitting-crock
  (implies (<= n (len l))
           (equal (assoc-eq-values l alist)
                  (append (assoc-eq-values (take n l) alist)
                          (assoc-eq-values (nthcdr n l) alist)))))

(defthm assoc-eq-values-make-list
  (equal (assoc-eq-values (make-list n :initial-element name) alist)
         (make-list n :initial-element (assoc-eq-value name alist)))
  :hints (("Goal" :in-theory (enable repeat))))

(defthm assoc-eq-values-subseq-args-pairlis$-args
  (implies (and (<= 0 m)
                (no-duplicatesp args)
                (equal (len args) (len list))
                (true-listp list)
                (<= n (len args)))
           (equal (assoc-eq-values (subseq args m n) (pairlis$ args list))
                  (subseq list m n))))

(defthm assoc-eq-values-update-alist-not-member
  (implies (not (member name names))
           (equal (assoc-eq-values names
                                   (update-alist name value alist))
                  (assoc-eq-values names alist))))

(defthm assoc-eq-values-cdr
  (equal (assoc-eq-values (cdr keys) alist)
         (cdr (assoc-eq-values keys alist))))

(in-theory (disable assoc-eq-values))


