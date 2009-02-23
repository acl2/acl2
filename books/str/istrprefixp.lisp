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
(include-book "ieqv")
(include-book "iprefixp")
(include-book "unicode/nthcdr" :dir :system)
(local (include-book "arithmetic"))

(local (defthm iprefixp-lemma-1
         (implies (and (natp xn)
                       (natp yn)
                       (< xn (len x))
                       (< yn (len y))
                       (not (ichareqv (nth xn x) (nth yn y))))
                  (not (iprefixp (nthcdr xn x) (nthcdr yn y))))
         :hints(("Goal" :in-theory (enable nthcdr nth iprefixp)))))

(local (defthm iprefixp-lemma-2
         (implies (and (natp xn)
                       (natp yn)
                       (< xn (len x))
                       (< yn (len y))
                       (ichareqv (nth xn x) (nth yn y)))
                  (equal (iprefixp (nthcdr xn x) (nthcdr yn y))
                         (iprefixp (cdr (nthcdr xn x)) (cdr (nthcdr yn y)))))
         :hints(("Goal" :in-theory (enable iprefixp nth nthcdr)))))

(defund istrprefixp-impl (x y xn yn xl yl)
  (declare (type string x)
           (type string y)
           (type integer xn)
           (type integer yn)
           (type integer xl)
           (type integer yl)
           (xargs :guard (and (stringp x) 
                              (stringp y)
                              (natp xn)
                              (natp yn)
                              (natp xl)
                              (natp yl)
                              (= xl (length x))
                              (= yl (length y))
                              (<= xn (length x))
                              (<= yn (length y)))
                  :measure (min (nfix (- (nfix xl) (nfix xn)))
                                (nfix (- (nfix yl) (nfix yn))))
                  :guard-hints (("Goal" :in-theory (enable ichareqv)))))
  (cond ((mbe :logic (zp (- (nfix xl) (nfix xn)))
              :exec (= (the integer xn)
                       (the integer xl)))
         t)
        ((mbe :logic (zp (- (nfix yl) (nfix yn)))
              :exec (= (the integer yn)
                       (the integer yl)))
         nil)
        ((mbe :logic (ichareqv (char x xn)
                               (char y yn))
              :exec (let ((cx (the character (char (the string x) (the integer xn))))
                          (cy (the character (char (the string y) (the integer yn)))))
                      (if (standard-char-p (the character cx))
                          (if (standard-char-p (the character cy))
                              (char-equal (the character cx) (the character cy))
                            nil)
                        (eql (the character cx) (the character cy)))))
         (mbe :logic (istrprefixp-impl x y 
                                       (+ (nfix xn) 1)
                                       (+ (nfix yn) 1) 
                                       xl yl)
              :exec  (istrprefixp-impl (the string x)
                                       (the string y)
                                       (the integer (+ (the integer xn) 1))
                                       (the integer (+ (the integer yn) 1))
                                       (the integer xl)
                                       (the integer yl))))
        (t
         nil)))

(defthm istrprefixp-impl-elim
  (implies (and (force (stringp x)) 
                (force (stringp y))
                (force (natp xn))
                (force (natp yn))
                (force (= xl (length x)))
                (force (= yl (length y)))
                (force (<= xn xl))
                (force (<= yn yl)))
           (equal (istrprefixp-impl x y xn yn xl yl)
                  (iprefixp (nthcdr xn (coerce x 'list))
                            (nthcdr yn (coerce y 'list)))))
  :hints(("Goal" :in-theory (enable istrprefixp-impl))))

(defun istrprefixp (x y)

  ":Doc-Section Str
  Case-insensitive string prefix test~/

  ~c[(istrprefixp x y)] determines if the string x is a prefix of the string y, in
  a case-insensitive manner.

  Logically, this is identical to ~c[(iprefixp (coerce x 'list) (coerce y 'list))],
  but we use a more efficient implementation which avoids coercing the strings.~/

  ~l[strprefixp] and ~pl[iprefixp]"

  (declare (type string x)
           (type string y))

  (mbe :logic (iprefixp (coerce x 'list)
                        (coerce y 'list))
       :exec (istrprefixp-impl (the string x)
                               (the string y)
                               (the integer 0)
                               (the integer 0)
                               (the integer (length (the string x)))
                               (the integer (length (the string y))))))
