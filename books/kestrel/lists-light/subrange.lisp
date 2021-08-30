; A lightweight book of theorems about subrange.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "subrange-def")
(local (include-book "nthcdr"))
(local (include-book "cons"))
(local (include-book "nth"))
(local (include-book "len"))
(local (include-book "take"))
(local (include-book "append"))
(local (include-book "true-list-fix"))
(local (include-book "kestrel/arithmetic-light/minus" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus-and-minus" :dir :system))

(defthm true-listp-of-subrange-type-prescription
  (true-listp (subrange start end lst))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable subrange))))

;todo: only needed by axe?
(defthm true-listp-of-subrange
  (true-listp (subrange start end vals)))

(defthm subrange-out-of-order
  (implies (and (< end start)
                (integerp end)
                (integerp start))
           (equal (subrange start end lst)
                  nil))
  :hints (("Goal" :in-theory (enable subrange))))

(defthm subrange-out-of-order-cheap
  (implies (and (syntaxp (and (quotep start)
                              (quotep end)))
                (< end start)
                (integerp end)
                (integerp start))
           (equal (subrange start end lst)
                  nil))
  :hints (("Goal" :in-theory (enable subrange))))

(defthm car-of-subrange
  (implies (and (<= start end)
                (natp end))
           (equal (car (subrange start end lst))
                  (nth start lst)))
  :hints (("Goal" :in-theory (enable subrange))))

(defthm cdr-of-subrange
  (implies (natp start)
           (equal (cdr (subrange start end lst))
                  (subrange (+ 1 start) end lst)))
  :hints (("Goal" :in-theory (enable subrange nthcdr-opener-alt))))

(defthm nthcdr-of-subrange
  (implies (and (natp start)
                (natp n)
                (integerp end))
           (equal (nthcdr n (subrange start end lst))
                  (subrange (+ start n) end lst)))
  :hints (("Goal" :in-theory (enable subrange))))

(defthm consp-of-subrange
  (implies (and (natp start)
                (integerp end))
           (equal (consp (subrange start end lst))
                  (<= start end)))
  :hints (("Goal" :in-theory (enable subrange))))

(defthmd subrange-opener
  (implies (and (<= start end)
                (natp start)
                (integerp end))
           (equal (subrange start end lst)
                  (cons (nth start lst)
                        (subrange (+ 1 start) end lst)))))

(defthm subrange-iff
  (implies (integerp end)
           (iff (subrange start end x)
                (<= (nfix start) end)))
  :hints (("Goal" :in-theory (enable subrange))))

(defthm len-of-subrange
  (implies (and (integerp end)
                (integerp start))
           (equal (len (subrange start end lst))
                  (if (< end (nfix start))
                      0
                    (+ 1 (- end (nfix start))))))
  :hints (("Goal" :in-theory (enable subrange take))))

(defthm subrange-same
  (implies (natp start)
           (equal (subrange start start lst)
                  (list (nth start lst))))
  :hints (("Goal" :in-theory (enable subrange))))

(defthm subrange-of-0
  (equal (subrange 0 end lst)
         (take (+ 1 end) lst))
  :hints (("Goal" :in-theory (enable subrange))))

(defthm subrange-is-all
  (implies (and (<= (+ -1 (len lst)) end)
                (natp end))
           (equal (subrange 0 end lst)
                  (take (+ 1 end) lst)))
  :hints (("Goal" :in-theory (enable subrange))))

;use a congruence?
(defthm subrange-of-true-list-fix
  (equal (subrange start end (true-list-fix lst))
         (subrange start end lst))
  :hints (("Goal" :in-theory (enable subrange))))

(defthmd take-of-nthcdr-becomes-subrange
  (implies (and (natp n2)
                (natp n1))
           (equal (take n1 (nthcdr n2 lst))
                  (subrange n2 (+ -1 n1 n2) lst)))
  :hints (("Goal" :in-theory (enable subrange))))

(theory-invariant (incompatible (:rewrite take-of-nthcdr-becomes-subrange) (:definition subrange)))

;rename take-of-subrange
(defthm take-of-subrange-gen
  (implies (and (<= i (+ 1 (- end start)))
                (natp start)
                (natp end)
                (natp i))
           (equal (take i (subrange start end lst))
                  (subrange start (+ start i -1) lst)))
  :hints (("Goal" :in-theory (e/d (subrange) (take-of-nthcdr-becomes-subrange)))))

(defthm subrange-out-of-order-or-singleton
  (implies (and (<= end start)
                (< end (len lst))
                (natp end)
                (integerp start))
           (equal (subrange start end lst)
                  (if (equal end start)
                      (list (nth start lst))
                    nil))))

(defthm nth-of-subrange
  (implies (and (integerp end)
                (natp start)
                (natp n))
           (equal (nth n (subrange start end lst))
                  (if (<= n (- end start))
                      (nth (+ n start) lst)
                    nil)))
  :hints (("Goal" :in-theory (enable subrange))))

(defthm subrange-up-to-end-becomes-nthcdr
  (implies (and (equal len (len lst))
                (natp start) ;new
                )
           (equal (subrange start (+ -1 len) lst)
                  (true-list-fix (nthcdr start lst))))
  :hints (("Goal" :in-theory (e/d (subrange) (TAKE-OF-NTHCDR-BECOMES-SUBRANGE)))))

(defthmd subrange-up-to-end-becomes-nthcdr-strong
  (implies (and (equal k (+ -1 (len lst)))
                (natp start) ;new
                )
           (equal (subrange start k lst)
                  (true-list-fix (nthcdr start lst)))))

(defthm append-of-subrange-and-subrange-adjacent
  (implies (and (equal s2 (+ 1 e1))
                (< e2 (len lst))
                (<= s1 e1)
                (<= s2 e2)
                (natp e1)
                (natp s1)
                ;; (natp s2)
                (natp e2))
           (equal (append (subrange s1 e1 lst) (subrange s2 e2 lst))
                  (subrange s1 e2 lst)))
  :hints (("Goal" :in-theory (enable equal-of-append))))

(defthm subrange-of-1-and-cons
  (implies (natp end)
           (equal (subrange 1 end (cons a x))
                  (subrange 0 (+ -1 end) x)))
  :hints (("Goal" :in-theory (enable subrange))))

(defthm equal-of-cdr-and-subrange-same
  (implies (and (< end (len lst))
                (natp end))
           (equal (equal (cdr lst) (subrange 1 end lst))
                  (and (true-listp lst)
                       (equal (len lst) (+ 1 end))))))

(defthmd equal-of-subrange-opener-helper
  (implies (and (natp low)
                (natp high)
                (<= low high))
           (equal (equal (subrange low high x)
                         y)
                  (and (consp y)
                       (equal (nth low x) (nth 0 y))
                       (equal (subrange (+ 1 low) high x)
                              (cdr y)))))
  :hints (("Goal" :use ((:instance subrange-opener (end high) (start low) (lst x))))))

(defthmd equal-of-subrange-opener
  (implies (and (syntaxp (and (quotep low)
                              (quote high)))
                (natp low)
                (natp high)
                (<= low high))
           (equal (equal (subrange low high x)
                         y)
                  (and (consp y)
                       (equal (nth low x) (nth 0 y))
                       (equal (subrange (+ 1 low) high x)
                              (cdr y)))))
  :hints (("Goal" :use (:instance equal-of-subrange-opener-helper))))

(defthm equal-subrange-nthcdr-rewrite
  (implies (and (equal (+ 1 j) (len x))
                (true-listp x))
           (equal (equal (subrange i j x)
                         (nthcdr i x))
                  t))
  :hints (("Goal" :in-theory (e/d (subrange nthcdr) ()))))

(defthmd take-of-cdr-becomes-subrange
  (implies (and (integerp n)
                (<= 0 n))
           (equal (take n (cdr lst))
                  (subrange 1 n lst)))
  :hints (("Goal" :use (:instance take-of-nthcdr-becomes-subrange (n1 n) (n2 1))
           :in-theory (e/d () (take-of-nthcdr-becomes-subrange)))))

(theory-invariant (incompatible (:rewrite take-of-cdr-becomes-subrange) (:definition subrange)))

(defthmd cdr-of-take-becomes-subrange-better
  (implies (integerp n) ;drop?
           (equal (cdr (take n lst))
                  (subrange 1 (+ -1 n) lst)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :expand (subrange 1 (+ -2 n) (cdr lst))
           :in-theory (e/d (take subrange) (take-of-nthcdr-becomes-subrange)))))

(theory-invariant (incompatible (:rewrite cdr-of-take-becomes-subrange-better) (:definition subrange)))

(defthm subrange-when-start-is-negative
  (implies (< start 0)
           (equal (subrange start end lst)
                  (subrange 0 end lst)))
  :hints (("Goal" :in-theory (e/d (subrange take) (take-of-nthcdr-becomes-subrange)))))

(defthm subrange-when-end-is-negative
  (implies (< end 0)
           (equal (subrange start end lst)
                  nil))
  :hints (("Goal" :in-theory (e/d (subrange take) (take-of-nthcdr-becomes-subrange)))))

(defthm cons-nth-onto-subrange
  (implies (and (equal m (+ 1 k))
                (<= m n)
                (<= n (len lst))
                (natp k)
                ;; (integerp m)
                (natp n))
           (equal (CONS (NTH k lst) (SUBRANGE m n lst))
                  (SUBRANGE k n lst)))
  :hints (("Goal" :in-theory (e/d () (TAKE-OF-NTHCDR-BECOMES-SUBRANGE)))))

(defthm subrange-of-take
  (implies (and (< high n)
                (<= low high)
                (natp low)
                (natp high)
                (natp n))
           (equal (SUBRANGE low high (TAKE n x))
                  (SUBRANGE low high x)))
  :hints (("Goal" :in-theory (e/d (SUBRANGE) (TAKE-OF-NTHCDR-BECOMES-SUBRANGE)))))

(defthmd subrange-of-cons
  (implies (and (natp low)
                (natp high)
                )
           (equal (subrange low high (cons a rest))
                  (if (zp low)
                      (cons a (subrange 0 (+ -1 high) rest))
                    (subrange (+ -1 low) (+ -1 high) rest))))
  :hints (("Goal" :in-theory (e/d (subrange) (take-of-nthcdr-becomes-subrange)))))

;prevents case splits
(defthm subrange-of-cons-constant-version
  (implies (and (syntaxp (quotep low))
                (natp low)
                (natp high)
                )
           (equal (subrange low high (cons a rest))
                  (if (zp low)
                      (cons a (subrange 0 (+ -1 high) rest))
                    (subrange (+ -1 low) (+ -1 high) rest))))
  :hints (("Goal" :use (:instance subrange-of-cons))))

;had to chose this direction due to the variable end not being the the rhs (so would be hard to make it the lhs)
(defthm subrange-to-end-becomes-nthcdr
  (IMPLIES (AND (EQUAL END (+ -1 (LEN LST)))
                (NATP START)
                (TRUE-LISTP LST)
                (<= START END))
           (EQUAL (SUBRANGE START END LST)
                  (NTHCDR START LST)))
  :hints (("Goal" :in-theory (e/d (SUBRANGE) (TAKE-OF-NTHCDR-BECOMES-SUBRANGE)))))

(defthm cons-nth-onto-subrange-alt
  (implies (and (equal m (+ 1 k))
                (<= m n)
                (natp k)
                (natp n))
           (equal (cons (nth k lst) (append (subrange m n lst) y))
                  (append (subrange k n lst) y))))

(defthmd nthcdr-of-take-becomes-subrange
  (implies (and (natp n)
                (natp n2))
           (equal (nthcdr n (take n2 lst))
                  (if (<= n n2)
                      (subrange n (+ -1 n2) lst)
                    nil)))
  :hints (("Goal" :in-theory (e/d (subrange)
                                  (take-of-nthcdr-becomes-subrange
                                   cdr-of-take-becomes-subrange-better
                                   TAKE-OF-CDR-BECOMES-SUBRANGE
                                   )))))

(theory-invariant (incompatible (:rewrite NTHCDR-OF-TAKE-BECOMES-SUBRANGE) (:definition subrange)))

;rename
(defthm subrange-split-top
  (implies (and (natp i)
                (<= low i)
                (natp low)
                (< i (len x)))
           (equal (append (subrange low (+ -1 i) x) (list (nth i x)))
                  (subrange low i x)))
  :hints (("Goal" :in-theory (enable equal-of-append))))

(defthm append-of-take-and-subrange
  (implies (and (natp n)
                (<= m n)
                (natp m))
           (equal (append (take m x) (subrange m n x))
                  (take (+ 1 n) x)))
  :hints (("Goal" :in-theory (enable subrange equal-of-append))))

(defthm subrange-of-append-lemma
  (implies (and (<= (len x) m)
                (natp m))
           (equal (subrange m n (append x y))
                  (subrange (- m (len x))
                            (- n (len x))
                            y)))
  :hints (("Goal" :in-theory (e/d (subrange take-when-zp) ()))))

(defthm subrange-of-cdr
  (implies (and ;(natp low)
            (natp high))
           (equal (subrange low high (cdr lst))
                  (subrange (+ 1 (nfix low)) (+ 1 high) lst)))
  :hints (("Goal" :in-theory (e/d (subrange)
                                  (take-of-nthcdr-becomes-subrange
                                   nthcdr-of-take-becomes-subrange
                                   cdr-of-take-becomes-subrange-better
                                   TAKE-OF-CDR-BECOMES-SUBRANGE)))))

(defthm subrange-of-append-irrel
  (implies (and (natp low)
                (natp high)
                (< high (len x))
                )
           (equal (subrange low high (append x y))
                  (subrange low high x)))
  :hints (("Goal" :in-theory (e/d (subrange TAKE-OF-NTHCDR)
                                  (NTHCDR-OF-TAKE
                                   CDR-OF-TAKE-BECOMES-SUBRANGE-BETTER
                                   NTHCDR-OF-TAKE-BECOMES-SUBRANGE
                                   TAKE-OF-NTHCDR-BECOMES-SUBRANGE
                                   TAKE-OF-CDR-BECOMES-SUBRANGE)))))

(defthm subrange-of-append-lemma2
  (implies (and (< m (len x))
                (natp n)
                (< n (+ (len x) (len y)))
                (<= m n)
                (natp m)
                (true-listp x)
                )
           (equal (subrange m n (append x y))
                  (append (subrange m (min n (+ -1 (len x))) x)
                          (subrange (- m (len x))
                                    (- n (len x))
                                    y))))
  :hints (("Goal" :in-theory (e/d (subrange posp NTHCDR-WHEN-NOT-POSP) ()))))

;can we avoid the case splits?
(defthm subrange-of-append
  (implies (and (natp start)
                (natp end))
           (equal (subrange start end (append x y))
                  (if (< end (len x))
                      (subrange start end x)
                    (if (<= (len x) start)
                        (subrange (- start (len x))
                                  (- end (len x))
                                  y)
                      (append (subrange start (+ -1 (len x)) x)
                              (subrange (- start (len x))
                                        (- end (len x))
                                        y))))))
  :hints (("Goal" :in-theory (enable equal-of-append))))

;use iff?
;drop this one?
;for axe?
(defthm subrange-not-nil1
  (implies (and ;(consp lst)
                (natp start)
                (natp end))
           (equal (equal (subrange start end lst) nil)
                  (< end start)
                  ))
  :hints (("Goal" :in-theory (e/d (subrange) (;anti-subrange
                                              )))))

;use iff?
;for axe?
(defthm subrange-not-nil2
  (implies (and ;(consp lst)
                (natp start)
                (natp end))
           (equal (equal nil (subrange start end lst))
                  (< end start)
                  ))
  :hints (("Goal" :use (:instance subrange-not-nil1)
           :in-theory (disable subrange-not-nil1))))
