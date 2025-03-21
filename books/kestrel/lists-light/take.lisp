; A lightweight book about the built-in function take.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; See also firstn.lisp for a related function.

(in-theory (disable take))

;; Param name changed to match std.
(defthm consp-of-take
  (equal (consp (take n xs))
         (not (zp n)))
  :hints (("Goal" :in-theory (enable take))))

;; Stronger than car-of-take from std.
(defthm car-of-take-strong
  (equal (car (take n l))
         (if (zp n)
             nil
           (car l)))
  :hints (("Goal" :expand ((first-n-ac n l nil))
           :in-theory (enable take))))

;; Param name changed to match std.
(defthm take-of-cons
  (equal (take n (cons a x))
         (if (zp n)
             nil
           (cons a (take (+ -1 n) x))))
  :hints (("Goal" :in-theory (enable take))))

(defthm take-of-0
  (equal (take 0 l)
         nil)
  :hints (("Goal" :in-theory (enable take))))

;Disabled since take-of-0 normally suffices.
(defthmd take-when-zp
  (implies (zp n)
           (equal (take n l)
                  nil))
  :hints (("Goal" :in-theory (enable take))))

;; Param name changed to match std.
(defthm take-of-1
  (equal (take 1 x)
         (list (car x)))
  :hints (("Goal" :in-theory (enable take))))

(defthm cdr-of-take
  (equal (cdr (take n l))
         (take (+ -1 n) (cdr l)))
  :hints (("Goal"
           :expand (first-n-ac n l nil)
           :in-theory (enable take))))

;; Param name changed to match std.
(defthm len-of-take
  (equal (len (take n xs))
         (nfix n))
  :hints (("Goal" :in-theory (enable take))))

;name clash with nth-of-take
(defthm nth-of-take-2
  (implies (and (natp n)
                (natp m))
           (equal (nth n (take m lst))
                  (if  (< n m)
                      (nth n lst)
                    nil)))
  :hints (("Goal" :in-theory (enable take nth))))

;todo
(defthm nth-of-take-2-gen
  (equal (nth n (take m lst))
         (if (natp n)
             (if (natp m)
                 ;; usual case:
                 (if (< n m)
                     (nth n lst)
                   nil)
               nil)
           (if (zp m)
               nil
             (car lst))))
  :hints (("Goal" :use nth-of-take-2
           :expand (take m lst)
           :in-theory (disable nth-of-take-2))))

;drop?
(defthm nth-of-take-too-high
  (implies (and (<= m n)
                (natp n)
                (< 0 m))
           (equal (nth n (take m data))
                  nil)))

(defthm nthcdr-of-take
  (equal (nthcdr i (take j x))
         (take (- (nfix j) (nfix i))
               (nthcdr i x)))
  :hints (("Goal" :in-theory (enable take nthcdr))))

(defthmd take-of-nthcdr
  (implies (and (integerp i)
                (<= 0 i)
                (integerp k))
           (equal (take k (nthcdr i x))
                  (nthcdr i (take (+ i k) x))))
  :hints (("Goal" :in-theory (e/d (take) (nthcdr-of-take))
           :use (:instance nthcdr-of-take (j (+ i k))))))

(theory-invariant (incompatible (:rewrite nthcdr-of-take) (:rewrite take-of-nthcdr)))

;rename
(defthm take-does-nothing
  (implies (equal n (len lst))
           (equal (take n lst)
                  (true-list-fix lst)))
  :hints (("Goal" :in-theory (enable take))))

;rename?
;; This variant avoids introducing true-list-fix.
(defthmd take-does-nothing-simple
  (implies (and (equal n (len l))
                (true-listp l))
           (equal (take n l)
                  l))
  :hints (("Goal" :in-theory (enable take))))

(defthm take-iff
  (iff (take n lst)
       (and (natp n)
            (< 0 n)))
  :hints (("Goal" :in-theory (enable take))))

(defthm take-of-true-list-fix
  (equal (take n (true-list-fix lst))
         (take n lst))
  :hints (("Goal" :in-theory (enable take))))

;; see also take-of-take but that one needs repeat
(defthm take-of-take-when-<=
  (implies (and (<= n m)
                (integerp n)
                (natp m))
           (equal (take n (take m lst))
                  (take n lst)))
  :hints (("Goal" :in-theory (enable take))))

;which way do we want to go?
;should we go to subrange?
(defthmd take-of-cdr
  (equal (take n (cdr lst))
         (cdr (take (+ 1 n) lst)))
  :hints (("Goal" :in-theory (enable take))))

;rename
(defthmd cdr-take-plus-1
  (equal (cdr (take (+ 1 n) vals))
         (take n (cdr vals)))
  :hints (("Goal" :in-theory (enable take))))

(theory-invariant (incompatible (:rewrite take-of-cdr) (:rewrite cdr-take-plus-1)))
(theory-invariant (incompatible (:rewrite take-of-cdr) (:rewrite cdr-of-take)))

(local
 (defthm subsetp-equal-of-cons-arg2
   (implies (and (syntaxp (not (and (quotep a)
                                    (quotep y))))
                 (subsetp-equal x y))
            (subsetp-equal x (cons a y)))
   :hints (("Goal" :in-theory (enable subsetp-equal)))))

(defthm subsetp-equal-of-take-and-take
  (implies (<= n1 n2)
           (equal (subsetp-equal (take n1 lst)
                                 (take n2 lst))
                  (if (natp n2)
                      t
                    (zp n1))))
  :hints (("Goal" :in-theory (enable take))))

;matches std
(defthm take-of-append
  (equal (take n (append x y))
         (if (< (nfix n) (len x))
             (take n x)
           (append x (take (- n (len x)) y))))
  :hints (("Goal" :in-theory (enable take ;bozo looped without this?
                                     append true-list-fix))))

;matches std (including param-names)
(defthm take-of-update-nth
  (equal (take n1 (update-nth n2 val x))
         (if (<= (nfix n1) (nfix n2))
             (take n1 x)
           (update-nth n2 val (take n1 x))))
  :hints
  (("Goal" :in-theory (enable TAKE update-nth))))



(local
 (defthm nthcdr-of-nil
  (equal (nthcdr n nil)
         nil)
  :hints (("Goal" :in-theory (enable nthcdr)))))

;name clash with other one
(defthm append-of-take-and-nthcdr-2
  (equal (append (take n l) (nthcdr n l))
         (if (<= (nfix n) (len l))
             l  ;; normal case
           (take n l) ;; filled with nils at the end
           ))
  :hints (("Goal" :in-theory (enable take nthcdr))))

(defthm cadr-of-take
  (equal (cadr (take n lst))
         (if (not (and (integerp n)
                       (< 1 n)))
             nil
           (cadr lst)))
  :hints (("Goal" :in-theory (enable take))))

(defthm take-does-nothing-rewrite
  (implies (natp n)
           (equal (equal x (take n x))
                  (and (true-listp x)
                       (equal (len x) n)))))

(defthm equal-of-take-and-take-same
  (equal (equal (take n1 x) (take n2 x))
         (equal (nfix n1) (nfix n2)))
  :hints (("Goal" :in-theory (enable take))))

(defthmd take-opener-when-not-zp
  (implies (not (zp n))
           (equal (take n lst)
                  (cons (nth 0 lst)
                        (take (+ -1 n) (cdr lst)))))
  :hints (("Goal" :in-theory (enable take))))

(defthmd take-of-+-of-1
  (implies (and (syntaxp (not (quotep n))) ;defeat ACL2 matching (+ 1 n) with a constant
                (natp n))
           (equal (take (+ 1 n) x)
                  (cons (car x)
                        (take n (cdr x)))))
  :hints (("Goal" :in-theory (enable take append))))

(defthmd take-of-+-of-1-alt
  (implies (and (syntaxp (not (quotep n))) ;defeat ACL2 matching (+ 1 n) with a constant
                (< n (len x)) ;drop?
                (natp n))
           (equal (take (+ 1 n) x)
                  (append (take n x)
                          (list (nth n x)))))
  :hints (("Goal" :in-theory (enable take append))))

;; Would like to include take of nil, but that requires repeat to state.

;rename
(defthm update-nth-take-last-element
  (implies (and (< n (len lst))
                (integerp n) ;drop?
                )
           (equal (UPDATE-NTH n val (TAKE (+ 1 n) lst))
                  (append (TAKE n lst) (list val))))
  :hints (("Goal" :in-theory (enable take))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Characterizes the unusual situation when take makes the list longer
(defthm <-of-acl2-count-of-take
  (implies (true-listp l) ; not easy to drop
           (equal (< (acl2-count l) (acl2-count (take n l)))
                  (and (< (len l) n)
                       (natp n))))
  :hints (("Goal" :in-theory (enable take))
          ("subgoal *1/1" :cases ((< (+ 1 (len (cdr l))) n)))))

(defthm <=-of-acl2-count-of-take-linear
  (implies (<= n (len l))
           (<= (acl2-count (take n l)) (acl2-count l)))
  :rule-classes ((:linear :trigger-terms ((acl2-count (take n l)))))
  :hints (("Goal" :in-theory (enable take))))

(defthm <-of-acl2-count-of-take-linear
  (implies (< (nfix n) (len l))
           (< (acl2-count (take n l)) (acl2-count l)))
  :rule-classes ((:linear :trigger-terms ((acl2-count (take n l)))))
  :hints (("Goal" :in-theory (enable take))))

(defthm nth-when-equal-of-take-and-constant
  (implies (and (equal k (take m x))
                (syntaxp (and (quotep k)
                              (not (quotep x)))) ;gen to that k is a smaller term?
                (< n m)
                (natp n)
                (natp m))
           (equal (nth n x)
                  (nth n k))))
