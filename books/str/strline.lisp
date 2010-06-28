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
(local (include-book "make-event/assert" :dir :system))
(local (include-book "arithmetic"))

(defund charpos-aux (x n xl char)
  (declare (type string x)
           (type integer n)
           (type integer xl)
           (type character char)
           (xargs :guard (and (stringp x)
                              (natp n)
                              (natp xl)
                              (<= n xl)
                              (= xl (length x)))
                  :measure (nfix (- (nfix xl) (nfix n)))))
  (cond ((mbe :logic (zp (- (nfix xl) (nfix n)))
              :exec (= n xl))
         nil)
        ((eql (char x n) char)
         (mbe :logic (nfix n)
              :exec n))
        (t
         (charpos-aux x
                      (mbe :logic (+ 1 (nfix n)) :exec (+ 1 n))
                      xl
                      char))))

(defthm charpos-aux-is-position-ac-of-nthcdr
  (implies (and (stringp x)
                (natp n)
                (= xl (length x)))
           (equal (charpos-aux x n xl char)
                  (position-ac char (nthcdr n (coerce x 'list)) n)))
  :hints(("Goal" :in-theory (enable charpos-aux position-ac))))

(defthm position-ac-lower-bound
  (implies (and (position-ac item x acc)
                (natp acc))
           (<= acc (position-ac item x acc)))
  :rule-classes ((:rewrite) (:linear))
  :hints(("Goal" :in-theory (enable position-ac))))

(defthm position-ac-upper-bound
  (implies (natp acc)
           (<= (position-ac item x acc)
               (+ acc (len x))))
  :rule-classes ((:rewrite) (:linear))
  :hints(("Goal" :in-theory (enable position-ac))))




(defund go-to-line (x n xl curr goal)
  (declare (xargs :guard (and (stringp x)
                              (natp n)
                              (natp xl)
                              (<= n xl)
                              (= xl (length x))
                              (natp curr)
                              (natp goal))
                  :measure (nfix (- (nfix xl) (nfix n))))
           (type string x)
           (type integer n xl curr goal))
  (cond ((mbe :logic (zp (- (nfix xl) (nfix n)))
              :exec (= n xl))
         nil)
        ((= curr goal)
         (mbe :logic (nfix n) :exec n))
        (t
         (go-to-line x
                     (mbe :logic (+ 1 (nfix n)) :exec (+ 1 n))
                     xl
                     (if (eql (char x n) #\Newline)
                         (+ 1 curr)
                       curr)
                     goal))))

(defthm type-of-go-to-line
  (or (not (go-to-line x n xl curr goal))
      (and (integerp (go-to-line x n xl curr goal))
           (<= 0 (go-to-line x n xl curr goal))))
  :rule-classes :type-prescription)

(defthm go-to-line-lower-bound
  (implies (and (go-to-line x n xl curr goal)
                (natp n))
           (<= n (go-to-line x n xl curr goal)))
  :rule-classes ((:rewrite) (:linear))
  :hints(("Goal" :in-theory (enable go-to-line))))

(defthm go-to-line-upper-bound
  (implies (natp xl)
           (<= (go-to-line x n xl curr goal)
               xl))
  :rule-classes ((:rewrite) (:linear))
  :hints(("Goal" :in-theory (enable go-to-line))))



(defund strline (n x)

  ":Doc-Section Str
  Extract a line from a string by its line number~/

  ~c[(strline n x)] extracts the ~c[n]th line from the string ~c[x] and returns
  it as a string.  It returns the empty string if ~c[n] does not refer to a
  valid line.  Note that the first line is 1 (not 0).~/~/"

  (declare (xargs :guard (and (posp n)
                              (stringp x))))
  (let* ((x     (mbe :logic (if (stringp x) x "")
                     :exec x))
         (xl    (length x))
         (start (go-to-line x 0 xl 1 n)))
    (if (not start)
        ""
      (let ((end (charpos-aux x start xl #\Newline)))
        (subseq x start end)))))

(defthm stringp-of-strline
  (stringp (strline n x))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable strline))))


(local (acl2::assert! (equal "foo" (strline 1 "foo
bar
baz"))))

(local (acl2::assert! (equal "bar" (strline 2 "foo
bar
baz"))))

(local (acl2::assert! (equal "baz" (strline 3 "foo
bar
baz"))))

(local (acl2::assert! (equal "" (strline 4 "foo
bar
baz"))))



(defund strlines (a b x)
  (declare (type integer a)
           (type integer b)
           (type string x)
           (xargs :guard (and (posp a)
                              (posp b)
                              (stringp x))))
  (let* ((x  (mbe :logic (if (stringp x) x "")
                  :exec x))
         (xl (length x)))
    (mv-let
     (a b)
     (if (<= a b) (mv a b) (mv b a))
     (let ((start (go-to-line x 0 xl 1 a)))
       (if (not start)
           ""
         (let ((end (go-to-line x start xl a (+ 1 b))))
           (subseq x start end)))))))

(defthm stringp-of-strlines
  (stringp (strlines a b x))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable strlines))))


#||
(defconst *txt* "Line 1
Line 2
Line 3
Line 4
Line 5
Line 6"))

(strlines 1 1 *txt*)
(strlines 1 2 *txt*)
(strlines 1 3 *txt*)
(strlines 1 100 *txt*)
(strlines 2 2 *txt*)
(strlines 2 3 *txt*)
(strlines 2 100 *txt*)

(strlines 2 4 *txt*)
(strlines 2 5 *txt*)
(strlines 2 6 *txt*)
(strlines 2 7 *txt*)

(strlines 7 7 *txt*)
(strlines 7 4 *txt*)

||#