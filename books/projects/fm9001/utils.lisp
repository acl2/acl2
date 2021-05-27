;; Copyright (C) 2016, Regents of the University of Texas
;; Written by Cuong Chau (derived from earlier work of Brock and Hunt)
;; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

;; See the README for historical information.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; February 2021

(in-package "FM9001")

(include-book "std/lists/take" :dir :system)
(include-book "std/strings/decimal" :dir :system)
(include-book "std/strings/istrprefixp" :dir :system)

;; ======================================================================

; The atoms of the DE description language are symbols.  We define
; functions to aid their manipulation.

(defun true-list-alistp (x)
  (declare (xargs :guard t))
  (cond ((atom x) (eq x nil))
        (t (and (alistp (car x))
                (true-list-alistp (cdr x))))))

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

;; Update an alist.

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
   (implies (and (consp l)
                 (zp n))
            (equal (nth n l)
                   (car l)))
   (implies (and (consp l)
                 (not (zp n)))
            (equal (nth n l)
                   (nth (- n 1) (cdr l))))))

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

(defthm not-member-append
  (implies (and (not (member e x))
                (not (member e y)))
           (not (member e (append x y)))))

(defthm not-member=>not-equal-nth
  (implies (and (<= 0 n)
                (< n (len x))
                (not (member e x)))
           (not (equal e (nth n x)))))

(defthm subsetp=>member-nth
  (implies (and (subsetp x y)
                (<= 0 n)
                (< n (len x)))
           (member (nth n x) y)))

(defun pair-with-nil (x)
  (declare (xargs :guard t))
  (if (atom x)
      nil
    (cons (cons (car x) nil)
          (pair-with-nil (cdr x)))))

(defun pairs (x y)
  (declare (xargs :guard t))
  (if (atom x)
      nil
    (if (atom y)
        (pair-with-nil x)
      (cons (cons (car x)
                  (car y))
            (pairs (cdr x) (cdr y))))))

(defthm pairs-is-pairlis$
  (equal (pairs    x y)
         (pairlis$ x y)))

(in-theory (disable pairs))

;; Some facts about pairlis$

(defthm alistp-pairlis$
  (alistp (pairlis$ symbols values)))

(defthm len-pairlis$
  (equal (len (pairlis$ keys vals))
         (len (double-rewrite keys))))

(defthm alistp-delete-to-eq
  (implies (alistp alist)
           (alistp (delete-to-eq name alist))))

(defthm symbol-alistp-pairlis$
  ;; This lemma is redundant with SYMBOL-ALISTP-PAIRLIS, but loaded
  ;; because of the BDD package(s).
  (implies (symbol-listp symbols)
	   (symbol-alistp (pairlis$ symbols vals))))

(defthm pairlis$-append
  (implies (equal (len x) (len a))
           (equal (pairlis$ (append x y) (append a b))
                  (append (pairlis$ x a) (pairlis$ y b)))))

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
  ;; Proved by TAU.
  (implies (and (symbol-listp keys)
                (symbol-alistp wire-alist))
           (symbol-alistp (append (pairlis$ keys values)
                                  wire-alist))))

(defthm strip-cars-of-symbol-alist-is-symbol-listp
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

;; Some facts about nthcdr and append

(local
 (defun nthcdr-append-induct (n x y)
   (if (zp n)
       (append x y)
     (nthcdr-append-induct (1- n) (cdr x) y))))

(defthm nthcdr-append
  (implies (and (integerp n)
                (<= (len x) n))
           (equal (nthcdr n (append x y))
                  (nthcdr (- n (len x)) y)))
  :hints (("Goal"
           :induct (nthcdr-append-induct n x y))))

;; ======================================================================

;; BINARY-AND*

(defun binary-and* (x y)
  (declare (xargs :guard t))
  (if x y nil))

(defthm booleanp-binary-and*
  (implies (booleanp y)
           (booleanp (binary-and* x y)))
  :rule-classes :type-prescription)

(in-theory (disable binary-and*))

(defund and*-macro (x)
  (declare (xargs :guard t))
  (cond ((atom x)
         t)
        ((atom (cdr x))
         (car x))
        (t
         `(binary-and* ,(car x)
                       ,(and*-macro (cdr x))))))

(defmacro and* (&rest args)
  (and*-macro args))

;; BINARY-OR*

(defun binary-or* (x y)
  (declare (xargs :guard t))
  (if x x y))

(defthm booleanp-binary-or*
  (implies (and (booleanp x)
                (booleanp y))
           (booleanp (binary-or* x y)))
  :rule-classes :type-prescription)

(in-theory (disable binary-or*))

(defund or*-macro (x)
  (declare (xargs :guard t))
  (cond ((atom x)
         nil)
        ((atom (cdr x))
         (car x))
        (t
         `(binary-or* ,(car x)
                      ,(or*-macro (cdr x))))))

(defmacro or* (&rest args)
  (or*-macro args))

;; NOT*

(defun not* (x)
  (declare (xargs :guard t))
  (not x))

(defthm booleanp-not*
  (booleanp (not* x))
  :rule-classes :type-prescription)

(in-theory (disable not*))

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

(in-theory (disable disjoint))

;; Lemmas about TAKE and NTHCDR

(defthmd open-take
  (and
   (implies (zp n)
            (equal (take n x) nil))
   (implies (not (zp n))
            (equal (take n x)
                   (cons (car x) (take (1- n) (cdr x)))))))

(defthmd open-nthcdr
  (and
   (implies (zp n)
            (equal (nthcdr n l) l))
   (implies (not (zp n))
            (equal (nthcdr n l)
                   (nthcdr (1- n) (cdr l))))))

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

;; POSITION

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

(in-theory (disable position1))

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

(defthmd make-list-append-tree-crock
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

;; MAKE-TREE n  -- Makes a tree of size N.

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

;; TV-GUARD

(defun tv-guard (tree)
  (declare (xargs :guard t))
  (if (atom tree)
      (null tree)
    (and (tv-guard (car tree))
         (tv-guard (cdr tree)))))

;; LEN-1-LISTP

(defund len-1-listp (x)
  (declare (xargs :guard t))
  (if (atom x)
      t
    (and (equal (len (car x)) 1)
         (len-1-listp (cdr x)))))

;; LEN-1-TRUE-LISTP

(defun len-1-true-listp (x)
  (declare (xargs :guard t))
  (and (true-list-listp x)
       (len-1-listp x)))

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

;; ======================================================================

;; Utility functions for indices.

(defun str-append-symbol-underscore (s)
  (declare (xargs :guard (symbolp s)))
  (string-append (symbol-name s) "_"))

(defun append-symbol-string (s str)
  (declare (xargs :guard (and (symbolp s)
                              (stringp str))))
  (string-append (str-append-symbol-underscore s)
                 str))

(defun si (s idx)
  (declare (xargs :guard (and (symbolp s)
                              (natp idx))))
  (intern$ (append-symbol-string s (str::natstr (nfix idx)))
           "FM9001"))

(defun sis (s start-idx count)
  (declare (xargs :guard (and (symbolp s)
                              (natp start-idx)
                              (natp count))))
  (if (zp count)
      nil
    (cons (si s start-idx)
          (sis s (1+ start-idx) (1- count)))))

(defthm consp-sis
  (implies (posp n)
           (consp (sis s m n)))
  :hints (("Goal" :expand (sis s m n)))
  :rule-classes :type-prescription)

(local
 (defthm symbol-inequality
   (implies (and (symbolp s1)
                 (symbolp s2)
                 (not (equal (symbol-name s1)
                             (symbol-name s2))))
            (not (equal s1 s2)))))

(local
 (defthm intern$-diff-strings
   (implies (and (stringp str1)
                 (stringp str2)
                 (not (equal str1 str2)))
            (not (equal (intern$ str1 "FM9001")
                        (intern$ str2 "FM9001"))))
   :hints (("Goal"
            :in-theory (disable (pkg-imports)
                                acl2-package)))))

(local
 (defthm not-prefixp-not-equal
   (implies (not (prefixp x y))
            (not (equal x y)))
   :hints (("Goal" :in-theory (enable prefixp)))))

;; Mihir M. mod: disabled a newly added lemma.
(defthm prefixp-append-relation-1
  (implies (and (not (prefixp x y))
                (not (prefixp y x)))
           (and (not (prefixp (append x a) (append y b)))
                (not (prefixp (append y b) (append x a)))))
  :hints
  (("goal" :in-theory (e/d (prefixp)
                           ((:rewrite acl2::prefixp-of-append-arg1)
                            (:rewrite acl2::prefixp-of-append-arg2))))))

(defthm
  prefixp-append-relation-2
  (implies (not (prefixp x y))
           (not (prefixp (append x a) y)))
  :hints
  (("goal" :in-theory (e/d (prefixp)
                           ((:rewrite acl2::prefixp-of-append-arg1)
                            (:rewrite acl2::prefixp-of-append-arg2))))))

(local
 (defthm istrprefixp-prefixp-explode-relation
   (implies (not (str::istrprefixp str1 str2))
            (not (prefixp (explode str1) (explode str2))))))

(defthm istrprefixp-string-append-relation-1
  (implies (and (not (str::istrprefixp str1 str2))
                (not (str::istrprefixp str2 str1)))
           (not (equal (string-append str1 str3)
                       (string-append str2 str4))))
  :hints (("Goal"
           :in-theory (disable istrprefixp-prefixp-explode-relation)
           :use (istrprefixp-prefixp-explode-relation
                 (:instance istrprefixp-prefixp-explode-relation
                            (str1 str2)
                            (str2 str1))))))

(defthm append-diff-symbols-string-1
  (implies (and (not (str::istrprefixp (str-append-symbol-underscore s1)
                                       (str-append-symbol-underscore s2)))
                (not (str::istrprefixp (str-append-symbol-underscore s2)
                                       (str-append-symbol-underscore s1))))
           (not (equal (append-symbol-string s1 str1)
                       (append-symbol-string s2 str2))))
  :hints (("Goal"
           :in-theory (disable str::istrprefixp
                               string-append))))

(defthm istrprefixp-string-append-relation-2
  (implies (not (str::istrprefixp str2 str1))
           (not (equal str1
                       (string-append str2 str3)))))

(defthm append-diff-symbols-string-2
  (implies (not (str::istrprefixp (str-append-symbol-underscore s2)
                                  (symbol-name s1)))
           (not (equal (symbol-name s1)
                       (append-symbol-string s2 str2))))
  :hints (("Goal"
           :in-theory (disable str::istrprefixp
                               string-append))))

(in-theory (disable str-append-symbol-underscore
                    append-symbol-string))

(defthm si-of-diff-symbols-1
  (implies (and (not (str::istrprefixp (str-append-symbol-underscore s1)
                                       (str-append-symbol-underscore s2)))
                (not (str::istrprefixp (str-append-symbol-underscore s2)
                                       (str-append-symbol-underscore s1))))
           (not (equal (si s1 m) (si s2 n)))))

(defthm si-of-diff-symbols-2
  (implies (not (str::istrprefixp (str-append-symbol-underscore s2)
                                  (symbol-name s1)))
           (not (equal s1 (si s2 n))))
  :hints (("Goal" :in-theory (enable append-symbol-string))))

(defthm append-symbol-diff-strings
  (implies (and (stringp str1)
                (stringp str2)
                (not (equal str1 str2)))
           (not (equal (append-symbol-string s str1)
                       (append-symbol-string s str2))))
  :hints (("Goal"
           :in-theory (enable append-symbol-string))))

(defthm si-of-diff-idxes
  (implies (and (natp m)
                (natp n)
                (not (equal m n)))
           (not (equal (si s m) (si s n)))))

(in-theory (disable si))

(defthm si-sis-diff-symbols-1
  (implies (and (not (str::istrprefixp (str-append-symbol-underscore s1)
                                       (str-append-symbol-underscore s2)))
                (not (str::istrprefixp (str-append-symbol-underscore s2)
                                       (str-append-symbol-underscore s1))))
           (not (member (si s1 k) (sis s2 m n)))))

(defthm si-sis-diff-symbols-2
  (implies (not (str::istrprefixp (str-append-symbol-underscore s2)
                                  (symbol-name s1)))
           (not (member s1 (sis s2 m n)))))

(defthm si-sis-diff-idxes
  (implies (and (natp k)
                (natp m)
                (< k m))
           (not (member (si s k) (sis s m n)))))

(defthm len-sis
  (equal (len (sis s m n))
         (nfix n)))

(defthm no-duplicatesp-sis
  (implies (natp m)
           (no-duplicatesp (sis s m n))))

(defthm disjoint-sis-diff-syms
  (implies (and (not (str::istrprefixp (str-append-symbol-underscore s1)
                                       (str-append-symbol-underscore s2)))
                (not (str::istrprefixp (str-append-symbol-underscore s2)
                                       (str-append-symbol-underscore s1))))
           (disjoint (sis s1 m1 n1) (sis s2 m2 n2))))

(defthm si-member-sis
  (implies (and (natp m)
                (posp n)
                (natp i)
                (<= m i)
                (< i (+ m n)))
           (member (si s i) (sis s m n)))
  :hints (("Goal"
           :expand ((sis s 0 n)
                    (sis s i 1)
                    (sis s i n)))))

(defthmd si-is-nth-of-sis
  (implies (and (natp m)
                (posp n)
                (natp i)
                (<= m i)
                (< i (+ m n)))
           (equal (si s i)
                  (nth (- i m) (sis s m n))))
  :hints (("Goal"
           :expand ((sis s 0 n)
                    (sis s i 1)
                    (sis s i n)))))

(in-theory (disable sis))
