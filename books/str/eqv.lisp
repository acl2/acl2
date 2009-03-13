; ACL2 String Library
; Copyright (C) 2009 Centaur Technology
; Contact: jared@cs.utexas.edu
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.

(in-package "STR")
(include-book "doc")
(local (include-book "arithmetic"))
(local (include-book "char-support"))

(in-theory (disable char<))

(defund char-fix (x)
  (declare (type character x))
  (mbe :logic (if (characterp x) 
                  x
                (code-char 0))
       :exec x))

(defthm char-fix-when-characterp
  (implies (characterp x)
           (equal (char-fix x)
                  x))
  :hints(("Goal" :in-theory (enable char-fix))))



(defund chareqv (x y)

  ":Doc-Section Str
   Case-sensitive character equivalence test~/
 
   ~c[(chareqv x y)] determines if x and y are equivalent when interpreted as characters.
   That is, non-characters are first coerced to be the zero-character, then we ask whether
   the results are equal.~/

   ~l[ichareqv], ~pl[charlisteqv], and ~pl[strlisteqv]"

  (declare (type character x)
           (type character y))

  (mbe :logic (equal (char-fix x) (char-fix y))
       :exec (eql x y)))

(defequiv chareqv 
  :hints(("Goal" :in-theory (enable chareqv))))

(defthm chareqv-of-char-fix
  (chareqv (char-fix x)
           x)
  :hints(("Goal" :in-theory (enable chareqv))))

(defcong chareqv equal (char-fix x) 1
  :hints(("Goal" :in-theory (enable chareqv))))

(defcong chareqv equal (char-code x) 1
  :hints(("Goal" :in-theory (enable chareqv char-fix))))

(defcong chareqv equal (char< x y) 1
  :hints(("Goal" :in-theory (enable chareqv char-fix char<))))

(defcong chareqv equal (char< x y) 2
  :hints(("Goal" :in-theory (enable chareqv char-fix char<))))

(defthm char<-irreflexive
  (equal (char< x x)
         nil)
  :hints(("Goal" :in-theory (enable char<))))

(defthm char<-antisymmetric
  (implies (char< x y)
           (not (char< y x)))
  :hints(("Goal" :in-theory (enable char<))))

(defthm char<-transitive
  (implies (and (char< x y)
                (char< y x))
           (char< x z))
  :hints(("Goal" :in-theory (enable char<))))

(defthm char<-trichotomy-weak
  (implies (and (not (char< x y))
                (not (char< y x)))
           (equal (chareqv x y)
                  t))
  :hints(("Goal" :in-theory (enable char< chareqv char-fix))))

(defthm char<-trichotomy-strong
  (equal (char< x y)
         (and (not (chareqv x y))
              (not (char< y x))))
  :rule-classes ((:rewrite :loop-stopper ((x y)))))



(defund charlisteqv (x y)

  ":Doc-Section Str
   Case-sensitive character-list equivalence test~/
 
   ~c[(charlisteqv x y)] determines if x and y are equivalent when interpreted as character
   lists.  That is, ~c[x] and ~c[y] must have the same length, and their elements must be 
   ~il[chareqv] to one another.~/

   ~l[strlisteqv] and ~pl[icharlisteqv]"

  (declare (xargs :guard (and (character-listp x)
                              (character-listp y))))

  (if (consp x)
      (and (consp y)
           (chareqv (car x) (car y))
           (charlisteqv (cdr x) (cdr y)))
    (atom y)))

(defequiv charlisteqv
  :hints(("Goal" :in-theory (enable charlisteqv))))

(defcong charlisteqv chareqv (car x) 1
  :hints(("Goal" :in-theory (enable charlisteqv))))

(defcong charlisteqv charlisteqv (cdr x) 1
  :hints(("Goal" :in-theory (enable charlisteqv))))

(defcong charlisteqv chareqv (nth n x) 2
  :hints(("Goal" :in-theory (enable charlisteqv))))

(defcong charlisteqv charlisteqv (nthcdr n x) 2
  :hints(("Goal" :in-theory (enable charlisteqv))))

(defthm charlisteqv-when-not-consp-left
  (implies (not (consp x))
           (equal (charlisteqv x y)
                  (atom y)))
  :hints(("Goal" :in-theory (enable charlisteqv))))

(defthm charlisteqv-when-not-consp-right
  (implies (not (consp y))
           (equal (charlisteqv x y)
                  (atom x)))
  :hints(("Goal" :in-theory (enable charlisteqv))))

(defthm charlisteqv-of-cons-right
  (equal (charlisteqv x (cons a y))
         (and (consp x)
              (chareqv (car x) (double-rewrite a))
              (charlisteqv (cdr x) (double-rewrite y))))
  :hints(("Goal" :in-theory (enable charlisteqv))))

(defthm charlisteqv-of-cons-left
  (equal (charlisteqv (cons a x) y) 
         (and (consp y)
              (chareqv (double-rewrite a) (car y))
              (charlisteqv (double-rewrite x) (cdr y))))
  :hints(("Goal" :in-theory (enable charlisteqv))))

(defthm charlisteqv-when-not-same-lens
  (implies (not (equal (len x) (len y)))
           (not (charlisteqv x y)))
  :hints(("Goal" :in-theory (enable charlisteqv))))

