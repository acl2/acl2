;; Copyright (C) 2017, Regents of the University of Texas
;; Written by Cuong Chau (derived from the FM9001 work of Brock and Hunt)
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; The ACL2 source code for the FM9001 work is available at
;; https://github.com/acl2/acl2/tree/master/books/projects/fm9001.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; May 2019

(in-package "ADE")

(include-book "index")

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

(defthm assoc-eq-value-pairlis$-append-member
  (implies (member a x)
           (equal (assoc-eq-value a (pairlis$ (append x y) l))
                  (assoc-eq-value a (pairlis$ x l)))))

(local
 (defun assoc-eq-value-pairlis$-append-not-member-induct (x l)
   (if (atom x)
       l
     (assoc-eq-value-pairlis$-append-not-member-induct (cdr x) (cdr l)))))

(defthm assoc-eq-value-pairlis$-append-not-member
  (implies (not (member a x))
           (equal (assoc-eq-value a (pairlis$ (append x y) l))
                  (assoc-eq-value a (pairlis$ y (nthcdr (len x) l)))))
  :hints (("Goal"
           :induct (assoc-eq-value-pairlis$-append-not-member-induct x l))))

(defthm assoc-eq-value-update-alist-1
  (implies (and (equal occ-name1 occ-name2)
                (consp (assoc-eq occ-name2 st-alist)))
           (equal (assoc-eq-value occ-name1
                                  (update-alist occ-name2 st st-alist))
                  st))
  :hints (("Goal" :in-theory (enable update-alist))))

(defthm assoc-eq-value-update-alist-2
  (implies (not (equal occ-name1 occ-name2))
           (equal (assoc-eq-value occ-name1
                                  (update-alist occ-name2 st st-alist))
                  (assoc-eq-value occ-name1
                                  st-alist)))
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
  (implies (and (natp i)
                (natp m)
                (posp n)
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

(defthm assoc-eq-values-append-when-disjoint
  (implies (or (disjoint syms (strip-cars x))
               (disjoint (strip-cars x) syms))
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

(defthm assoc-eq-values-rev
  (equal (assoc-eq-values (rev syms) alist)
         (rev (assoc-eq-values syms alist))))

(defthm assoc-eq-values-append-pairlis$-when-subset
  (implies (subsetp args1 args2)
           (equal (assoc-eq-values args1 (append (pairlis$ args2 answer)
                                                 x))
                  (assoc-eq-values args1 (pairlis$ args2 answer)))))

(defthm assoc-eq-values-append-pairlis$-when-disjoint
  (implies (or (disjoint args1 args2)
               (disjoint args2 args1))
           (equal (assoc-eq-values args1 (append (pairlis$ args2 a)
                                                 b))
                  (assoc-eq-values args1 b))))

(defthm assoc-eq-values-pairlis$-append-when-subset
  (implies (subsetp x y)
           (equal (assoc-eq-values x (pairlis$ (append y z) l))
                  (assoc-eq-values x (pairlis$ y (take (len y) l)))))
  :hints (("Goal" :in-theory (enable pairlis$-of-take))))

(defthm assoc-eq-values-pairlis$-append-when-disjoint
  (implies
   (or (disjoint x y)
       (disjoint y x))
   (equal (assoc-eq-values x (pairlis$ (append y z) l))
          (assoc-eq-values x (pairlis$ z (take (len z)
                                               (nthcdr (len y) l))))))
  :hints (("Goal" :in-theory (enable disjoint pairlis$-of-take))))

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

(defthm assoc-eq-values-take-nthcdr
  (implies (and (no-duplicatesp l)
                (<= 0 n2)
                (<= (+ n1 n2) (len l))
                (true-listp x)
                (<= (len l) (len x)))
           (equal (assoc-eq-values (take n1 (nthcdr n2 l))
                                   (pairlis$ l x))
                  (take n1 (nthcdr n2 x))))
  :hints (("Subgoal *1/1"
           :in-theory (disable assoc-eq-values-take-1)
           :use (:instance assoc-eq-values-take-1
                           (n n1)))))

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

(defthm assoc-eq-values-of-repeat-cons-1
  (implies (equal sym (car x))
           (equal (assoc-eq-values (repeat n sym)
                                   (cons x l))
                  (repeat n (cdr x))))
  :hints (("Goal" :in-theory (enable repeat))))

(defthm assoc-eq-values-of-repeat-cons-2
  (implies (not (equal sym (car x)))
           (equal (assoc-eq-values (repeat n sym)
                                   (cons x l))
                  (assoc-eq-values (repeat n sym) l)))
  :hints (("Goal" :in-theory (enable repeat))))

(defthm assoc-eq-values-of-repeat-append
  (implies (not (member sym (strip-cars x)))
           (equal (assoc-eq-values (repeat n sym)
                                   (append x y))
                  (assoc-eq-values (repeat n sym) y)))
  :hints (("Goal" :in-theory (enable repeat))))

(in-theory (disable assoc-eq-values))

(defthm assoc-eq-values-of-sis-pairlis$-sis
  (implies (and (natp i)
                (natp m)
                (natp n)
                (<= m i)
                (<= (+ i j) (+ m n))
                (true-listp vals)
                (<= n (len vals)))
           (equal (assoc-eq-values (sis s i j)
                                   (pairlis$ (sis s m n) vals))
                  (take j (nthcdr (- i m) vals))))
  :hints (("Goal" :use sis-of-subset)))
