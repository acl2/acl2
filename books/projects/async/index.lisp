;; Copyright (C) 2018, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; May 2019

;; Utility functions for indices

(in-package "ADE")

(include-book "utils")

(include-book "std/strings/decimal" :dir :system)
(include-book "std/strings/istrprefixp" :dir :system)

;; ======================================================================

(defun str-append-symbol-underscore (s)
  (declare (xargs :guard (symbolp s)))
  (string-append (symbol-name s) "_"))

(defun append-symbol-string (s str)
  (declare (xargs :guard (and (symbolp s)
                              (stringp str))))
  (string-append (str-append-symbol-underscore s)
                 str))

;; SI

(defun si (s idx)
  (declare (xargs :guard (and (symbolp s)
                              (natp idx))))
  (intern$ (append-symbol-string s (natstr (nfix idx)))
           "ADE"))

(local
 (defthm symbol-inequality
   (implies (and (not (equal (symbol-name s1)
                             (symbol-name s2)))
                 (symbolp s1)
                 (symbolp s2))
            (not (equal s1 s2)))))

(defthm not-iprefixp-append
  (implies (not (iprefixp x y))
           (not (iprefixp (append x a) y)))
  :hints (("Goal" :in-theory (enable iprefixp))))

(defthm not-istrprefixp-str-append-symbol-underscore
  (implies (not (istrprefixp (str-append-symbol-underscore s2)
                             (symbol-name s1)))
           (not (istrprefixp (str-append-symbol-underscore (si s2 n))
                             (symbol-name s1))))
  :hints (("Goal"
           :use (:instance not-iprefixp-append
                           (x (append (explode (symbol-name s2))
                                      '(#\_)))
                           (y (explode (symbol-name s1)))
                           (a (append (explode (natstr (nfix n)))
                                      '(#\_))))
           :in-theory (disable not-iprefixp-append))))

(defthm not-equal-with-si-of-diff-symbol
  (implies (not (istrprefixp (str-append-symbol-underscore s2)
                             (symbol-name s1)))
           (and (not (equal (symbol-name s1)
                            (symbol-name (si s2 n))))
                (not (equal s1 (si s2 n)))))
  :hints (("Goal" :in-theory (disable str-append-symbol-underscore)))
  :rule-classes ((:rewrite
                  :corollary
                  (implies (not (istrprefixp (str-append-symbol-underscore s2)
                                             (symbol-name s1)))
                           (not (equal (symbol-name s1)
                                       (symbol-name (si s2 n))))))
                 (:rewrite
                  :corollary
                  (implies (not (istrprefixp (str-append-symbol-underscore s2)
                                             (symbol-name s1)))
                           (not (equal s1 (si s2 n)))))))

(encapsulate
  ()

  (local
   (defthm not-member-underscore-natstr
     (not (member #\_ (explode (natstr n))))
     :hints (("Goal" :in-theory (enable basic-natchars
                                        natchars
                                        natstr)))))

  (local
   (defthmd si-of-diff-symbols-aux-1
     (implies (and (< (length str1) (length str2))
                   (equal (char str1 (1- (length str1)))
                          (char str2 (1- (length str2))))
                   (char str1 (1- (length str1)))
                   (not (member (char str1 (1- (length str1)))
                                (explode str3))))
              (not (equal (char (string-append str1 str3)
                                (1- (length str2)))
                          (char (string-append str2 str4)
                                (1- (length str2))))))
     :hints (("Goal" :in-theory (enable not-member=>not-equal-nth)))))

  (local
   (defthmd si-of-diff-symbols-aux-2
     (implies (not (equal (char str1 n) (char str2 n)))
              (not (equal str1 str2)))))

  (local
   (defthm si-of-diff-symbols-aux-3
     (implies (not (equal (length (symbol-name s1))
                          (length (symbol-name s2))))
              (not (equal (symbol-name (si s1 n1))
                          (symbol-name (si s2 n2)))))
     :hints (("Goal"
              :use ((:instance
                     si-of-diff-symbols-aux-1
                     (str1 (str-append-symbol-underscore s1))
                     (str2 (str-append-symbol-underscore s2))
                     (str3 (natstr (nfix n1)))
                     (str4 (natstr (nfix n2))))
                    (:instance
                     si-of-diff-symbols-aux-1
                     (str1 (str-append-symbol-underscore s2))
                     (str2 (str-append-symbol-underscore s1))
                     (str3 (natstr (nfix n2)))
                     (str4 (natstr (nfix n1))))
                    (:instance
                     si-of-diff-symbols-aux-2
                     (n (length (symbol-name s2)))
                     (str1 (append-symbol-string s1 (natstr (nfix n1))))
                     (str2 (append-symbol-string s2 (natstr (nfix n2)))))
                    (:instance
                     si-of-diff-symbols-aux-2
                     (n (length (symbol-name s1)))
                     (str1 (append-symbol-string s2 (natstr (nfix n2))))
                     (str2 (append-symbol-string s1 (natstr (nfix n1))))))))))

  (local
   (defun diff-elementp (x y)
     (declare (xargs :guard t))
     (cond ((atom x) (consp y))
           ((atom y) (consp x))
           (t (or (not (equal (car x) (car y)))
                  (diff-elementp (cdr x) (cdr y)))))))

  (local
   (defthmd not-equal-equiv-diff-elementp
     (implies (and (true-listp x)
                   (true-listp y))
              (equal (not (equal x y))
                     (diff-elementp x y)))))

  (local
   (defthmd diff-elementp-append
     (implies (and (diff-elementp x1 y1)
                   (equal (len x1) (len y1)))
              (diff-elementp (append x1 x2) (append y1 y2)))))

  (local
   (defthm si-of-diff-symbols-aux-4
     (implies (and (equal (length (symbol-name s1))
                          (length (symbol-name s2)))
                   (not (equal (symbol-name s1) (symbol-name s2))))
              (not (equal (symbol-name (si s1 n1))
                          (symbol-name (si s2 n2)))))
     :hints (("Goal"
              :use ((:instance
                     not-equal-equiv-diff-elementp
                     (x (explode (symbol-name s1)))
                     (y (explode (symbol-name s2))))
                    (:instance
                     not-equal-equiv-diff-elementp
                     (x (append (explode (symbol-name s1))
                                (cons #\_ (explode (natstr (nfix n1))))))
                     (y (append (explode (symbol-name s2))
                                (cons #\_ (explode (natstr (nfix n2)))))))
                    (:instance
                     diff-elementp-append
                     (x1 (explode (symbol-name s1)))
                     (x2 (cons #\_ (explode (natstr (nfix n1)))))
                     (y1 (explode (symbol-name s2)))
                     (y2 (cons #\_ (explode (natstr (nfix n2)))))))))))

  (in-theory (disable istrprefixp
                      str-append-symbol-underscore
                      append-symbol-string
                      si))

  (defthm si-of-diff-symbols
    (implies (not (equal (symbol-name s1) (symbol-name s2)))
             (and (not (equal (symbol-name (si s1 n1))
                              (symbol-name (si s2 n2))))
                  (not (equal (si s1 n1) (si s2 n2)))))
    :hints (("Goal" :cases ((equal (length (symbol-name s1))
                                   (length (symbol-name s2))))))
    :rule-classes ((:rewrite
                    :corollary
                    (implies (not (equal (symbol-name s1) (symbol-name s2)))
                             (not (equal (symbol-name (si s1 n1))
                                         (symbol-name (si s2 n2))))))
                   (:rewrite
                    :corollary
                    (implies (not (equal (symbol-name s1) (symbol-name s2)))
                             (not (equal (si s1 n1) (si s2 n2)))))))
  )

(defthm append-symbol-diff-strings
  (implies (and (not (equal str1 str2))
                (stringp str1)
                (stringp str2))
           (not (equal (append-symbol-string s str1)
                       (append-symbol-string s str2))))
  :hints (("Goal" :in-theory (enable append-symbol-string))))

(defthm si-of-diff-idxes
  (implies (and (natp m)
                (natp n)
                (not (equal m n)))
           (and (not (equal (symbol-name (si s m))
                            (symbol-name (si s n))))
                (not (equal (si s m)
                            (si s n)))))
  :hints (("Goal" :in-theory (enable si)))
  :rule-classes ((:rewrite
                  :corollary
                  (implies (and (natp m)
                                (natp n)
                                (not (equal m n)))
                           (not (equal (symbol-name (si s m))
                                       (symbol-name (si s n))))))
                 (:rewrite
                  :corollary
                  (implies (and (natp m)
                                (natp n)
                                (not (equal m n)))
                           (not (equal (si s m)
                                       (si s n)))))))

;; ======================================================================

;; SIS

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

(defthm not-member-with-sis-of-diff-symbol
  (implies (not (istrprefixp (str-append-symbol-underscore s2)
                             (symbol-name s1)))
           (not (member s1 (sis s2 m n)))))

(defthm si-sis-diff-symbols
  (implies (not (equal (symbol-name s1) (symbol-name s2)))
           (not (member (si s1 k) (sis s2 m n)))))

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

(defthm sis-of-singleton
  (equal (sis s m 1)
         (list (si s m)))
  :hints (("Goal" :expand (sis s m 1))))

(defthm disjoint-sis-diff-syms
  (implies (not (equal (symbol-name s1) (symbol-name s2)))
           (disjoint (sis s1 m1 n1) (sis s2 m2 n2))))

(defthm disjoint-sis-same-sym-1
  (implies (and (natp i)
                (natp m)
                (<= (+ i j) m))
           (disjoint (sis s i j) (sis s m n))))

(defthm disjoint-sis-same-sym-2
  (implies (and (natp i)
                (natp m)
                (<= (+ m n) i))
           (disjoint (sis s i j) (sis s m n)))
  :hints (("Goal" :in-theory (enable disjoint-commutative))))

(defthm si-member-sis
  (implies (and (natp i)
                (natp m)
                (natp n)
                (<= m i)
                (< i (+ m n)))
           (member (si s i) (sis s m n)))
  :hints (("Goal"
           :expand ((sis s 0 n)
                    (sis s i 1)
                    (sis s i n)))))

(defthm sis-subset-sis
  (implies (and (natp i)
                (natp m)
                (natp n)
                (<= m i)
                (<= (+ i j) (+ m n)))
           (subsetp (sis s i j)
                    (sis s m n))))

(defthmd si-is-nth-of-sis
  (implies (and (natp i)
                (natp m)
                (natp n)
                (<= m i)
                (< i (+ m n)))
           (equal (si s i)
                  (nth (- i m) (sis s m n))))
  :hints (("Goal"
           :expand ((sis s 0 n)
                    (sis s i 1)
                    (sis s i n)))))

(defthmd nth-of-sis-is-si
  (implies (and (natp i)
                (natp m)
                (natp n)
                (<= m i)
                (< i (+ m n)))
           (equal (nth (- i m) (sis s m n))
                  (si s i)))
  :hints (("Goal" :use si-is-nth-of-sis)))

(defthm position1-si-sis
  (implies (and (natp i)
                (natp m)
                (natp n)
                (<= m i)
                (< i (+ m n)))
           (equal (position1 (si s i) (sis s m n))
                  (- i m)))
  :hints (("Goal" :in-theory (enable position1))))

(defthmd sis-of-subset
  (implies (and (natp i)
                (natp m)
                (natp n)
                (<= m i)
                (<= (+ i j) (+ m n)))
           (equal (sis s i j)
                  (take j (nthcdr (- i m) (sis s m n)))))
  :hints (("Goal"
           :in-theory (enable nth-of-sis-is-si
                              car-nthcdr
                              cdr-nthcdr))))

(in-theory (disable sis))


