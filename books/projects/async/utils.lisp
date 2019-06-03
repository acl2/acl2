;; Copyright (C) 2017, Regents of the University of Texas
;; Written by Cuong Chau (derived from the FM9001 work of Brock and Hunt)
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; The ACL2 source code for the FM9001 work is available at
;; https://github.com/acl2/acl2/tree/master/books/projects/fm9001.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; May 2019

(in-package "ADE")

;;(include-book "std/lists/suffixp" :dir :system)
(include-book "std/lists/take" :dir :system)

(local (include-book "std/lists/sets" :dir :system))

(in-theory (disable take-of-len-free))

;; ======================================================================

; We might further investigate whether we are getting the performance
; we expect (which we can observe using the disassemble$ command).

;; DELETE-TO-EQ

(defun delete-to-eq (name alist)
  (declare (xargs :guard (and (symbolp name)
                              (alistp alist))))
  (if (atom alist)
      nil
    (if (eq name (caar alist))
        (cdr alist)
      (delete-to-eq name (cdr alist)))))

(defthm alistp-delete-to-eq
  (implies (alistp alist)
           (alistp (delete-to-eq name alist))))

;; Update an alist

(defun update-alist (key datum alist)
  (declare (xargs :guard (alistp alist)))
  (cond ((endp alist)
         nil)
        ((equal key (caar alist))
         (acons key datum (cdr alist)))
        (t (cons (car alist)
                 (update-alist key datum (cdr alist))))))

(defthm symbol-alistp-update-alist
  (implies (symbol-alistp alist)
           (symbol-alistp (update-alist key datum alist)))
  :rule-classes :type-prescription)

(defthm consp-of-assoc-update-alist-lemma
  (implies key1
           (equal (consp (assoc key1 (update-alist key2 datum alist)))
                  (consp (assoc key1 alist)))))

(defthm strip-cars-update-alist
  (equal (strip-cars (update-alist key datum alist))
         (strip-cars alist)))

(defthm update-alist-diff-keys
  (implies (not (equal key1 key2))
           (equal (update-alist key1 val1
                                (update-alist key2 val2 alist))
                  (update-alist key2 val2
                                (update-alist key1 val1 alist))))
  :rule-classes ((:rewrite :loop-stopper ((key1 key2)))))

(in-theory (disable update-alist))

;; Some facts...

(defthm nfix-of-nat
  (implies (natp x)
           (equal (nfix x) x)))

(defthmd len-0-is-atom
  (equal (equal (len x) 0)
         (atom x)))

(defthmd pos-len=>cons
  (implies (< 0 (len x))
           (consp x)))

(defthmd open-len
  (and
   (implies (atom x)
            (equal (len x) 0))
   (implies (consp x)
            (equal (len x)
                   (+ 1 (len (cdr x)))))))

(defthmd open-nth
  (and
   (implies (atom l)
            (not (nth n l)))
   (implies (zp n)
            (equal (nth n l)
                   (car l)))
   (implies (not (zp n))
            (equal (nth n l)
                   (nth (- n 1) (cdr l))))))

(defthmd left-associativity-of-append
  (equal (append a (append b c))
         (append (append a b) c)))

(defthm nth-append-<-len
  (implies (and (natp i)
                (< i (len x)))
           (equal (nth i (append x y))
                  (nth i x))))

(defthm nth-append->=-len
  (implies (and (natp i)
                (<= (len x) i))
           (equal (nth i (append x y))
                  (nth (- i (len x)) y)))
  :hints (("Goal" :induct (nth i x))))

(defthm symbol-listp-append
  (implies (and (symbol-listp x)
                (symbol-listp y))
           (symbol-listp (append x y))))

(defthm symbol-listp-remove-duplicates-eq
  (implies (symbol-listp names)
           (symbol-listp (remove-duplicates-equal names))))

(defthm true-listp-union-lemma
  (implies (and (true-listp l1)
                (true-listp l2))
           (true-listp (union-equal l1 l2)))
  :rule-classes :type-prescription)

(defthm member-append
  (implies (or (member a x)
               (member a y))
           (member a (append x y))))

(defthm not-member-append
  (implies (and (not (member e x))
                (not (member e y)))
           (not (member e (append x y)))))

(defthmd not-member=>not-equal-nth
   (implies (and (not (member a x))
                 a)
            (not (equal (nth n x) a))))

(defthm subsetp=>member-nth
  (implies (and (subsetp x y)
                (<= 0 n)
                (< n (len x)))
           (member (nth n x) y)))

(defthmd member-of-true-list-list-is-true-list
  (implies (and (member e x)
                (true-list-listp x))
           (true-listp e)))

;; Some facts about pairlis$

(defthm alistp-pairlis$
  (alistp (pairlis$ symbols values)))

(defthm len-pairlis$
  (equal (len (pairlis$ keys vals))
         (len (double-rewrite keys))))

(defthm symbol-alistp-pairlis$
  ;; This lemma is redundant with SYMBOL-ALISTP-PAIRLIS, but loaded
  ;; because of the BDD package(s).
  (implies (symbol-listp symbols)
	   (symbol-alistp (pairlis$ symbols vals))))

(defthm pairlis$-append
  (implies (equal (len x) (len a))
           (equal (pairlis$ (append x y) (append a b))
                  (append (pairlis$ x a) (pairlis$ y b)))))

(defthmd pairlis$-of-take
  (implies (equal (len x) n)
           (equal (pairlis$ x (take n y))
                  (pairlis$ x y))))

(defthm alistp-append
  (implies (and (alistp x)
		(alistp y))
	   (alistp (append x y))))

(defthm alistp-append-two-pairlis$
  (implies (alistp wire-alist)
           (alistp (append (pairlis$ keys values)
                           wire-alist))))

(defthm symbol-alistp-append
  (implies (and (symbol-alistp x)
		(symbol-alistp y))
	   (symbol-alistp (append x y))))

(defthm symbol-alistp-append-two-pairlis$
  ;; Proved by TAU
  (implies (and (symbol-listp keys)
                (symbol-alistp wire-alist))
           (symbol-alistp (append (pairlis$ keys values)
                                  wire-alist))))

(defthm strip-cars-of-symbol-alist-is-symbol-list
  (implies (symbol-alistp alst)
           (and (symbol-listp (strip-cars alst))
                (eqlable-listp (strip-cars alst))))
  :hints (("Goal" :induct (strip-cars alst))))

(defthm strip-cars-pairlis$
  (implies (true-listp x)
           (equal (strip-cars (pairlis$ x y))
                  x)))

(defthm strip-cdrs-pairlis$
  (implies (and (equal (len x) (len y))
                (true-listp y))
           (equal (strip-cdrs (pairlis$ x y))
                  y)))

(defthm len-strip-cars
  (equal (len (strip-cars x))
         (len x)))

;; ======================================================================

;; DISJOINT

(defun disjoint (x y)
  (declare (xargs :guard (true-listp y)))
  (if (atom x)
      t
    (if (member-equal (car x) y)
        nil
      (disjoint (cdr x) y))))

(defthm disjoint-atom
  (implies (or (atom x) (atom y))
           (disjoint x y)))

(defthm disjoint-cons
  (and
   (equal (disjoint (cons x y) z)
          (and (not (member x z))
               (disjoint y z)))
   (equal (disjoint z (cons x y))
          (and (not (member x z))
               (disjoint z y)))))

(defthm disjoint-append
  (and
   (equal (disjoint x (append y z))
          (and (disjoint x y)
               (disjoint x z)))
   (equal (disjoint (append y z) x)
          (and (disjoint y x)
               (disjoint z x)))))

(defthm disjoint=>not-member-nth
  (implies (and (disjoint x y)
                (<= 0 n)
                (< n (len x)))
           (not (member (nth n x) y))))

(defthm disjoint-commutative
  (implies (disjoint x y)
           (disjoint y x)))

(in-theory (disable disjoint))

;; Lemmas about TAKE and NTHCDR

(defthmd open-take
  (and
   (implies (zp n)
            (equal (take n x) nil))
   (implies (not (zp n))
            (equal (take n x)
                   (cons (car x) (take (1- n) (cdr x)))))))

(defthmd take-of-len-is-itself
  (implies (and (equal n (len l))
                (true-listp l))
           (equal (take n l) l)))

(defthm append-take-lemma
  (implies (and (consp l)
                (true-listp l)
                (equal n (1- (len l))))
           (equal (append (take n l)
                          (list (nth n l)))
                  l)))

(defthmd open-nthcdr
  (and
   (implies (zp n)
            (equal (nthcdr n l) l))
   (implies (not (zp n))
            (equal (nthcdr n l)
                   (nthcdr (1- n) (cdr l))))))

(defthm nthcdr-0
  (equal (nthcdr 0 l) l))

(defthmd nthcdr-of-pos-const-idx
  (implies (and (syntaxp (and (quotep n) (posp (unquote n))))
                (posp n))
           (equal (nthcdr n l)
                  (nthcdr (1- n) (cdr l)))))

(defthm len-nthcdr
  (implies (<= n (len l))
           (equal (len (nthcdr n l))
                  (- (len l) (nfix n)))))

(defthmd car-nthcdr
  (equal (car (nthcdr n l))
         (nth n l)))

(defthmd cdr-nthcdr
  (equal (cdr (nthcdr n l))
         (nthcdr (1+ (nfix n)) l)))

(defthm nthcdr-cons
  (implies (posp i)
           (equal (nthcdr i (cons x y))
                  (nthcdr (1- i) y))))

(defthmd nthcdr-cdr
  (equal (nthcdr n (cdr l))
         (cdr (nthcdr n l))))

(defthm append-take-nthcdr
  (implies (<= n (len l))
           (equal (append (take n l) (nthcdr n l))
                  l)))

(defthm not-member-take-lemma
  (implies (and (not (member x l))
                (<= n (len l)))
           (not (member x (take n l)))))

(defthm not-member-nthcdr-lemma
  (implies (not (member x l))
           (not (member x (nthcdr n l)))))

(defthm nthcdr-append
  (implies (and (integerp n)
                (<= (len x) n))
           (equal (nthcdr n (append x y))
                  (nthcdr (- n (len x)) y)))
  :hints (("Goal" :induct (nthcdr n x))))

(defthm true-list-listp-nthcdr
  (implies (true-list-listp l)
           (true-list-listp (nthcdr n l)))
  :rule-classes :type-prescription)

(defthm nthcdr-of-nthcdr
  (equal (nthcdr m (nthcdr n l))
         (nthcdr (+ (nfix m) (nfix n)) l)))

(defthmd nthcdr-plus
  (implies (and (natp m)
                (natp n))
           (equal (nthcdr (+ m n) l)
                  (nthcdr m (nthcdr n l)))))

(encapsulate
  ()

  (local
   (defthm subsetp-cons
     (implies (subsetp x y)
              (subsetp x (cons a y)))))

  (defthm subsetp-identity
    (subsetp x x))

  (defthm subsetp-take
    (implies (<= n (len l))
             (subsetp (take n l) l)))

  (defthm subsetp-nthcdr
    (subsetp (nthcdr n l) l)))

(defthm subsetp-transitivity
  (implies (and (subsetp x y)
                (subsetp y z))
           (subsetp x z)))

(defthm subsetp-transitivity-take-nthcdr
  (implies (and (<= 0 i2)
                (<= (+ i1 i2) (len x)))
           (subsetp (take i1 (nthcdr i2 x))
                    x)))

(defthm disjoint-take
  (implies (and (disjoint x y)
                (<= n (len x)))
           (disjoint (take n x) y)))

(defthm disjoint-nthcdr
  (implies (disjoint x y)
           (disjoint (nthcdr n x) y)))

(defthm no-duplicatesp-take-lemma
  (implies (and (no-duplicatesp l)
                (<= n (len l)))
           (no-duplicatesp (take n l))))

(defthm no-duplicatesp-nthcdr-lemma
  (implies (no-duplicatesp l)
           (no-duplicatesp (nthcdr n l))))

(defthm disjoint-take-nthcdr-same-list
  (implies (no-duplicatesp l)
           (disjoint (take n l) (nthcdr n l))))

(defthm disjoint-nthcdr-take-of-disjoint-lists
  (implies (and (disjoint l1 l2)
                (<= n2 (len l2)))
           (disjoint (nthcdr n1 l1) (take n2 l2))))

;; TREE-SIZE

(defun tree-size (tree)
  (declare (xargs :guard t))
  (if (atom tree)
      1
    (+ (tree-size (car tree))
       (tree-size (cdr tree)))))

(defthm tree-size-atom
  (implies (atom tree)
           (equal (tree-size tree)
                  1)))

(defthm not-equal-tree-size-tree-0
  (not (equal (tree-size tree) 0)))

(defthm tree-size-1-crock
  (not (equal 1 (tree-size (cons a b)))))

(defthm a-helpful-lemma-for-tree-inductions
  (implies (equal (len a) (tree-size tree))
           (<= (tree-size (car tree))
               (len a)))
  :rule-classes :linear)

(defthm tree-size-lemmas
  (and
   (implies (and (consp tree)
                 (equal size (tree-size tree)))
            (equal (- size (tree-size (car tree)))
                   (tree-size (cdr tree))))
   (implies (and (consp tree)
                 (equal size (tree-size tree)))
            (equal (- size (tree-size (cdr tree)))
                   (tree-size (car tree))))))

(defthm make-list-append-tree-crock
  (implies (consp tree)
           (equal (make-list (+ (tree-size (car tree))
                                (tree-size (cdr tree)))
                             :initial-element value)
                  (make-list (tree-size tree)
                             :initial-element value))))

(in-theory (disable tree-size))

;; TFIRSTN

(defun tfirstn (list tree)
  (declare (xargs :guard (and (true-listp list)
                              (listp tree))))
  (take (tree-size (car tree)) list))

;; TRESTN

(defun trestn (list tree)
  (declare (xargs :guard (and (true-listp list)
                              (listp tree))))
  (nthcdr (tree-size (car tree)) list))

;; TREE-HEIGHT

(defund tree-height (tree)
  (declare (xargs :guard t))
  (if (atom tree)
      1
    (1+ (max (tree-height (car tree))
             (tree-height (cdr tree))))))

;; MAKE-TREE n  -- Makes a tree of size N

(local (include-book "arithmetic-5/top" :dir :system))

(defun make-tree (n)
  (declare (xargs :guard (natp n)))
  (if (zp n)
      nil
    (if (equal n 1)
        nil
      (cons (make-tree (floor n 2))
            (make-tree (- n (floor n 2)))))))

(defthm tree-size-make-tree
  (implies (not (zp n))
           (equal (tree-size (make-tree n))
                  n))
  :hints (("Goal" :in-theory (enable tree-size))))

(defthm consp-make-tree
  (equal (consp (make-tree n))
         (and (natp n)
              (>= n 2))))

(in-theory (disable make-tree))

;; APPEND-REC & PREPEND-REC

(defun append-rec (x y)
  (declare (xargs :guard (true-listp x)))
  (if (atom y)
      nil
    (cons (append x (car y))
          (append-rec x (cdr y)))))

(defun prepend-rec (x y)
  (declare (xargs :guard (true-list-listp x)))
  (if (atom x)
      nil
    (cons (append (car x) y)
          (prepend-rec (cdr x) y))))

(defthm true-list-listp-prepend-rec
  (implies (true-listp y)
           (true-list-listp (prepend-rec x y)))
  :rule-classes :type-prescription)

(defthm member-append-prepend-rec
  (implies (member e x)
           (member (append e e1)
                   (prepend-rec x e1))))

(defthm subsetp-prepend-rec
  (implies (subsetp x y)
           (subsetp (prepend-rec x z)
                    (prepend-rec y z))))

(defthm prepend-rec-of-append
  (equal (prepend-rec (append x y) e)
         (append (prepend-rec x e) (prepend-rec y e))))

(defthm prepend-rec-of-prepend-rec
  (equal (prepend-rec (prepend-rec x y) z)
         (prepend-rec x (append y z))))

;; BOOL->BIT

(defun-inline bool->bit (x)
  (declare (xargs :guard t))
  (if x 1 0))

(in-theory (disable bool->bit))

;; CONS-REC

(defun cons-rec (e l)
  (declare (xargs :guard t))
  (if (atom l)
      nil
    (cons (cons e (car l))
          (cons-rec e (cdr l)))))

(defthm member-cons-cons-rec
  (implies (member x y)
           (member (cons e x)
                   (cons-rec e y))))

;; INTERLEAVE

(defun interleave (l1 l2)
  (declare (xargs :guard t
                  :measure (acl2-count (list l1 l2))))
  (cond ((and (atom l1) (atom l2)) '(nil))
        ((atom l1) (list l2))
        ((atom l2) (list l1))
        (t (append (cons-rec (car l1) (interleave (cdr l1) l2))
                   (cons-rec (car l2) (interleave l1 (cdr l2)))))))

(defthm consp-interleave
  (consp (interleave l1 l2))
  :rule-classes :type-prescription)

(defthm true-list-listp-interleave
  (implies (and (true-listp l1)
                (true-listp l2))
           (true-list-listp (interleave l1 l2)))
  :rule-classes :type-prescription)

(defthm subsetp-prepend-rec-interleave-1
  (implies (and (true-listp y)
                (true-listp z))
           (subsetp (prepend-rec (interleave x y) z)
                    (interleave (append x z) y))))

(defthm subsetp-prepend-rec-interleave-2
  (implies (and (true-listp x)
                (true-listp z))
           (subsetp (prepend-rec (interleave x y) z)
                    (interleave x (append y z)))))

(defthm member-append-interleave-1
  (implies (and (member x (interleave y z))
                (equal y++x1 (append y x1))
                (true-listp x1)
                (true-listp z))
           (member (append x x1)
                   (interleave y++x1 z)))
  :hints (("Goal"
           :in-theory (disable subsetp-prepend-rec-interleave-1)
           :use (:instance subsetp-prepend-rec-interleave-1
                           (x y)
                           (y z)
                           (z x1)))))

(defthm member-append-interleave-2
  (implies (and (member x (interleave y z))
                (equal z++x1 (append z x1))
                (true-listp x1)
                (true-listp y))
           (member (append x x1)
                   (interleave y z++x1)))
  :hints (("Goal"
           :in-theory (disable subsetp-prepend-rec-interleave-2)
           :use (:instance subsetp-prepend-rec-interleave-2
                           (x y)
                           (y z)
                           (z x1)))))

(defthm subsetp-prepend-rec-interleave-cons-1
  (implies (and (equal xe (append x (list e)))
                (true-listp y))
           (subsetp (prepend-rec (interleave x y) (cons e z))
                    (prepend-rec (interleave xe y) z)))
  :hints (("Goal"
           :in-theory (disable prepend-rec-of-prepend-rec)
           :use (:instance prepend-rec-of-prepend-rec
                           (x (interleave x y))
                           (y (list e))))))

(defthm subsetp-prepend-rec-interleave-cons-2
  (implies (and (equal ye (append y (list e)))
                (true-listp x))
           (subsetp (prepend-rec (interleave x y) (cons e z))
                    (prepend-rec (interleave x ye) z)))
  :hints (("Goal"
           :in-theory (disable prepend-rec-of-prepend-rec)
           :use (:instance prepend-rec-of-prepend-rec
                           (x (interleave x y))
                           (y (list e))))))

(in-theory (disable interleave))

;; INTERLEAVE-OF

(defun interleave-of (x y z)
  (declare (xargs :guard t
                  :measure (acl2-count (list x y))))
  (cond ((atom z)
         (and (atom x) (atom y)))
        ((atom x)
         (equal y z))
        ((atom y)
         (equal x z))
        (t (or (and (equal (car x) (car z))
                    (interleave-of (cdr x) y (cdr z)))
               (and (equal (car y) (car z))
                    (interleave-of x (cdr y) (cdr z)))))))

(defthm interleave-of-list-fix
  (implies (and (interleave-of x y z)
                (true-listp x)
                (true-listp y))
           (interleave-of x y (list-fix z))))

(defthm interleave-of-append-1
  (implies (and (interleave-of x y z)
                (true-listp z)
                (true-listp a))
           (interleave-of (append x a) y (append z a))))

(defthm interleave-of-append-2
  (implies (and (interleave-of x y z)
                (true-listp z)
                (true-listp a))
           (interleave-of x (append y a) (append z a))))

(in-theory (disable interleave-of))

;; LEN-1-LISTP

(defun len-1-listp (x)
  (declare (xargs :guard t))
  (if (atom x)
      (null x)
    (and (equal (len (car x)) 1)
         (len-1-listp (cdr x)))))

;; LEN-1-TRUE-LISTP

(defun len-1-true-listp (x)
  (declare (xargs :guard t))
  (and (true-list-listp x)
       (len-1-listp x)))

(defthmd len-1-true-listp=>true-listp
  (implies (len-1-true-listp x)
           (true-listp x))
  :rule-classes :forward-chaining)

(defthm pairlis$-strip-cars
  (implies (len-1-true-listp x)
           (equal (pairlis$ (strip-cars x) nil)
                  x))
  :hints (("Goal" :in-theory (enable len-1-listp))))

(defthm len-1-true-listp-pairlis$-with-nil
 (implies (true-listp x)
          (len-1-true-listp (pairlis$ x nil)))
 :hints (("Goal" :in-theory (enable len-1-listp)))
 :rule-classes (:rewrite :type-prescription))

(in-theory (disable len-1-true-listp))

;; POSITION1

(defun position1 (x l)
  (declare (xargs :guard t))
  (if (atom l)
      nil
    (if (equal x (car l))
        0
      (if (position1 x (cdr l))
          (1+ (position1 x (cdr l)))
        nil))))

(defthm member==>position1
  (implies (member x l)
           (position1 x l)))

(defthm position1-of-append
  (implies (and (not (member a x))
                (member a y))
           (equal (position1 a (append x y))
                  (+ (len x)
                     (position1 a y)))))

(in-theory (disable position1))

;; REMOVE-LST

(defun remove-lst (x y)
  (declare (xargs :guard (true-listp y)))
  (if (atom x)
      y
    (remove-lst (cdr x)
                (remove-equal (car x) y))))

;; ;; SUFFIXP

;; (defthm suffixp-nil
;;   (implies (true-listp y)
;;            (suffixp nil y))
;;   :hints (("Goal" :in-theory (enable suffixp)))
;;   :rule-classes :type-prescription)

;; (defthm suffixp-append
;;   (implies (suffixp x y)
;;            (suffixp (append x z) (append y z)))
;;   :hints (("Goal" :in-theory (enable suffixp)))
;;   :rule-classes :type-prescription)

;; TV-GUARD

(defun tv-guard (tree)
  (declare (xargs :guard t))
  (if (atom tree)
      (null tree)
    (and (tv-guard (car tree))
         (tv-guard (cdr tree)))))

(defthm tv-guard-make-tree
  (tv-guard (make-tree n))
  :hints (("Goal" :in-theory (enable make-tree)))
  :rule-classes :type-prescription)




