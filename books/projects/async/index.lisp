;; Copyright (C) 2018, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; September 2018

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

(defun si (s idx)
  (declare (xargs :guard (and (symbolp s)
                              (natp idx))))
  (intern$ (append-symbol-string s (str::natstr (nfix idx)))
           "ADE"))

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
            (not (equal (intern$ str1 "ADE")
                        (intern$ str2 "ADE"))))
   :hints (("Goal"
            :in-theory (disable (pkg-imports)
                                acl2-package)))))

(local
 (defthm not-prefixp-not-equal
   (implies (not (prefixp x y))
            (not (equal x y)))
   :hints (("Goal" :in-theory (enable prefixp)))))

(defthm prefixp-append-relation-1
  (implies (and (not (prefixp x y))
                (not (prefixp y x)))
           (and (not (prefixp (append x a) (append y b)))
                (not (prefixp (append y b) (append x a)))))
  :hints (("Goal" :in-theory (enable prefixp))))

(defthm prefixp-append-relation-2
 (implies (not (prefixp x y))
          (not (prefixp (append x a) y)))
 :hints (("Goal" :in-theory (enable prefixp))))

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

(defthm sis-of-singleton
  (equal (sis s m 1)
         (list (si s m)))
  :hints (("Goal" :expand (sis s m 1))))

(defthm disjoint-sis-diff-syms
  (implies (and (not (str::istrprefixp (str-append-symbol-underscore s1)
                                       (str-append-symbol-underscore s2)))
                (not (str::istrprefixp (str-append-symbol-underscore s2)
                                       (str-append-symbol-underscore s1))))
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
  (implies (and (natp m)
                (natp n)
                (natp i)
                (<= m i)
                (< i (+ m n)))
           (member (si s i) (sis s m n)))
  :hints (("Goal"
           :expand ((sis s 0 n)
                    (sis s i 1)
                    (sis s i n)))))

(defthm sis-subset-sis
  (implies (and (natp m)
                (natp n)
                (natp i)
                (<= m i)
                (<= (+ i j) (+ m n)))
           (subsetp (sis s i j)
                    (sis s m n))))

(defthmd si-is-nth-of-sis
  (implies (and (natp m)
                (natp n)
                (natp i)
                (<= m i)
                (< i (+ m n)))
           (equal (si s i)
                  (nth (- i m) (sis s m n))))
  :hints (("Goal"
           :expand ((sis s 0 n)
                    (sis s i 1)
                    (sis s i n)))))

(defthmd nth-of-sis-is-si
  (implies (and (natp m)
                (natp n)
                (natp i)
                (<= m i)
                (< i (+ m n)))
           (equal (nth (- i m) (sis s m n))
                  (si s i)))
  :hints (("Goal" :use si-is-nth-of-sis)))

(defthmd sis-of-subset
  (implies (and (natp m)
                (natp n)
                (natp i)
                (<= m i)
                (<= (+ i j) (+ m n)))
           (equal (sis s i j)
                  (take j (nthcdr (- i m) (sis s m n)))))
  :hints (("Goal"
           :in-theory (enable nth-of-sis-is-si
                              car-nthcdr
                              cdr-nthcdr))))

(in-theory (disable sis))


