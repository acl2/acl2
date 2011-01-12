; ACL2 String Library
; Copyright (C) 2009-2010 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "STR")
(include-book "doc")
(local (include-book "unicode/nthcdr" :dir :system))
(local (include-book "arithmetic"))

(defund ichareqv (x y)

  ":Doc-Section Str
   Case-insensitive character equivalence test~/

   ACL2's built-in version of this function, ~il[char-equal], is irritating to use
   because it has standard-char-p guards.  ~c[str::ichareqv] is somewhat less efficient,
   but it works on arbitrary characters and is an equivalence relation.~/

   ~l[str::istreqv]"

  (declare (type character x)
           (type character y))

  (mbe :logic (let ((x (if (characterp x) x (code-char 0)))
                    (y (if (characterp y) y (code-char 0))))
                (if (standard-char-p x)
                    (if (standard-char-p y)
                        (char-equal x y)
                      nil)
                  (eql x y)))
       :exec (if (standard-char-p (the character x))
                 (if (standard-char-p (the character y))
                     (char-equal (the character x) (the character y))
                   nil)
               (eql (the character x) (the character y)))))

(defequiv ichareqv
  :hints(("Goal" :in-theory (enable ichareqv))))



(defund icharlisteqv (x y)

  ":Doc-Section Str
   Case-insensitive character-list equivalence test~/

   We say that two lists are case-insensitively equivalent when they have the same
   length and each of their elements are pairwise ~il[str::ichareqv].~/

   ~l[str::istreqv] and ~pl[str::ichareqv]~/"

   (declare (xargs :guard (and (character-listp x)
                               (character-listp y))))

   (if (consp x)
       (and (consp y)
            (ichareqv (car x) (car y))
            (icharlisteqv (cdr x) (cdr y)))
     (atom y)))

(defequiv icharlisteqv
  :hints(("Goal" :in-theory (enable icharlisteqv))))

(defcong icharlisteqv ichareqv (car x) 1
  :hints(("Goal" :in-theory (enable icharlisteqv))))

(defcong icharlisteqv icharlisteqv (cdr x) 1
  :hints(("Goal" :in-theory (enable icharlisteqv))))

(defcong icharlisteqv ichareqv (nth n x) 2
  :hints(("Goal" :in-theory (enable icharlisteqv))))

(defcong icharlisteqv icharlisteqv (nthcdr n x) 2
  :hints(("Goal" :in-theory (enable icharlisteqv))))

(defthm icharlisteqv-when-not-consp-left
  (implies (not (consp x))
           (equal (icharlisteqv x y)
                  (atom y)))
  :hints(("Goal" :in-theory (enable icharlisteqv))))

(defthm icharlisteqv-when-not-consp-right
  (implies (not (consp y))
           (equal (icharlisteqv x y)
                  (atom x)))
  :hints(("Goal" :in-theory (enable icharlisteqv))))

(defthm icharlisteqv-of-cons-right
  (equal (icharlisteqv x (cons a y))
         (and (consp x)
              (ichareqv (car x) (double-rewrite a))
              (icharlisteqv (cdr x) (double-rewrite y))))
  :hints(("Goal" :in-theory (enable icharlisteqv))))

(defthm icharlisteqv-of-cons-left
  (equal (icharlisteqv (cons a x) y)
         (and (consp y)
              (ichareqv (double-rewrite a) (car y))
              (icharlisteqv (double-rewrite x) (cdr y))))
  :hints(("Goal" :in-theory (enable icharlisteqv))))

(defthm icharlisteqv-when-not-same-lens
  (implies (not (equal (len x) (len y)))
           (not (icharlisteqv x y)))
  :hints(("Goal" :in-theory (enable icharlisteqv))))




(defund istreqv-aux (x y n l)
  (declare (type string x)
           (type string y)
           (type integer n)
           (type integer l)
           (xargs :guard (and (natp n)
                              (natp l)
                              (equal (length x) l)
                              (equal (length y) l)
                              (<= n l))
                  :measure (nfix (- (nfix l) (nfix n)))
                  :guard-hints (("Goal" :in-theory (enable ichareqv)))))
  (mbe :logic
       (if (zp (- (nfix l) (nfix n)))
           t
         (and (ichareqv (char x n) (char y n))
              (istreqv-aux x y (+ (nfix n) 1) l)))
       :exec
       (if (= (the integer n) (the integer l))
           t
         (and (let ((cx (the character (char (the string x) (the integer n))))
                    (cy (the character (char (the string y) (the integer n)))))
                (if (standard-char-p (the character cx))
                    (if (standard-char-p (the character cy))
                        (char-equal (the character cx) (the character cy))
                      nil)
                  (eql (the character cx) (the character cy))))
              (istreqv-aux (the string x)
                                     (the string y)
                                     (the integer (+ (the integer n) 1))
                                     (the integer l))))))

(encapsulate
 ()
 (local (defthm lemma
          (implies (and (< n (len x))
                        (not (ichareqv (nth n x) (nth n y))))
                   (not (icharlisteqv (nthcdr n x) (nthcdr n y))))))

 (local (defthm lemma2
          (implies (and (< n (len x))
                        (equal (len x) (len y))
                        (ichareqv (nth n x) (nth n y)))
                   (equal (icharlisteqv (nthcdr n x) (nthcdr n y))
                          (icharlisteqv (cdr (nthcdr n x)) (cdr (nthcdr n y)))))))

 (defthm istreqv-aux-removal
   (implies (and (stringp x)
                 (stringp y)
                 (natp n)
                 (<= n l)
                 (= l (length x))
                 (= l (length y)))
            (equal (istreqv-aux x y n l)
                   (icharlisteqv (nthcdr n (coerce x 'list))
                                 (nthcdr n (coerce y 'list)))))
   :hints(("Goal"
           :in-theory (enable istreqv-aux)
           :induct (istreqv-aux x y n l)))))

(defun istreqv (x y)

  ":Doc-Section Str
   Case-insensitive string equivalence test~/

   We say that two strings are case-insensitively equivalent when they have the
   same length and each of their characters are pairwise ~il[str::ichareqv].  Logically
   this is identical to ~c[(icharlisteqv (coerce x 'list) (coerce y 'list))], but
   we use a more efficient implementation which avoids coercing the strings.

   NOTE: for reasoning, we leave this function enabled and prefer to work with
   ~c[icharlisteqv] of the coerces as our normal form.~/

   ~l[str::ichareqv] and ~pl[str::icharlisteqv]~/"

  (declare (type string x)
           (type string y))

  (mbe :logic
       (icharlisteqv (coerce x 'list) (coerce y 'list))
       :exec
       (let ((xl (the integer (length (the string x))))
             (yl (the integer (length (the string y)))))
         (and (= (the integer xl) (the integer yl))
              (istreqv-aux (the string x)
                           (the string y)
                           (the integer 0)
                           (the integer xl))))))

