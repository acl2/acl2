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
(local (include-book "arithmetic"))
(local (include-book "unicode/take" :dir :system))


; Redefinition targets (see fast-cat.lisp)
;
; Defining FAST-STRING-APPEND and FAST-STRING-APPEND-LST in the logic here
; allows you to (include-book "str/cat" ...) and use STR::CAT in ordinary books
; without trust tags.  But, when more performance is desired, you can
; additionally (include-book "str/fast-cat"), with a trust-tag, to make
; STR::CAT faster, at least in CCL.

(defun fast-string-append (str1 str2)
  ;; Redefined under-the-hood in fast-cat.lisp
  (declare (xargs :guard (and (stringp str1)
                              (stringp str2))))
  (string-append str1 str2))

(defun fast-string-append-lst (x)
  ;; Redefined under-the-hood in fast-cat.lisp
  (declare (xargs :guard (string-listp x)))
  (string-append-lst x))

(defmacro fast-concatenate (result-type &rest sequences)
  (declare (xargs :guard (member-equal result-type '('string 'list))))
  (cond ((equal result-type ''string)
         (cond ((and sequences
                     (cdr sequences)
                     (null (cddr sequences)))
                (list 'fast-string-append
                      (car sequences)
                      (cadr sequences)))
               (t
                (list 'fast-string-append-lst
                      (cons 'list sequences)))))
        (t
         `(append (list . ,sequences)))))


(defmacro cat (&rest args)

  ":Doc-Section Str
  Concatenate strings~/

  ~c[(cat x y z ...)] is identical to ~c[(concatenate 'string x y z ...)], but
  has a somewhat shorter name.

  Including the optional book \"str/fast-cat\" from :dir :system may speed up
  calls to ~c[str::cat].  ~/ "

  `(fast-concatenate 'string . ,args))


(defund append-chars-aux (x n y)
  (declare (xargs :guard (and (stringp x)
                              (natp n)
                              (< n (length x))))
           (type string x)
           (type integer n))
  (if (zp n)
      (cons (char x 0) y)
    (append-chars-aux x (- n 1) (cons (char x n) y))))

(encapsulate
 ()
 (local (defthm lemma
          (implies (and (not (zp n))
                        (<= n (len x)))
                   (equal (append (simpler-take (- n 1) x) (cons (nth (- n 1) x) y))
                          (append (simpler-take n x) y)))
          :hints(("goal"
                  :in-theory (enable simpler-take)
                  :induct (simpler-take n x)))))

 (defthm append-chars-aux-correct
   (implies (and (stringp x)
                 (natp n)
                 (< n (length x)))
            (equal (append-chars-aux x n y)
                   (append (take (+ 1 n) (coerce x 'list)) y)))
   :hints(("Goal"
           :in-theory (enable append-chars-aux)
           :induct (append-chars-aux x n y)))))

(local (in-theory (disable append-chars-aux-correct)))

(local (defthm append-chars-aux-correct-better
         (implies (and (stringp x)
                       (natp n)
                       (< n (length x)))
                  (equal (append-chars-aux x n y)
                         (append (simpler-take (+ 1 n) (coerce x 'list)) y)))
         :hints(("Goal"
                 :use ((:instance append-chars-aux-correct))))))

(defund append-chars (x y)

  ":Doc-Section Str
  Efficient (append (coerce x 'list) y)~/

  This function is logically equal to ~c[(append (coerce x 'list) y)], but is
  implemented efficiently via ~c[char]. ~/ "

  (declare (xargs :guard (stringp x))
           (type string x))

  (mbe :logic (append (coerce x 'list) y)
       :exec (if (equal x "")
                 y
               (append-chars-aux x (1- (length x)) y))))

(defthm character-listp-of-append-chars
  (equal (character-listp (append-chars x y))
         (character-listp y))
  :hints(("Goal" :in-theory (enable append-chars))))



(defund revappend-chars-aux (x n xl y)
  (declare (xargs :guard (and (stringp x)
                              (natp n)
                              (natp xl)
                              (<= n xl)
                              (equal xl (length x)))
                  :measure (nfix (- (nfix xl) (nfix n)))))
  (if (mbe :logic (zp (- (nfix xl) (nfix n)))
           :exec (= n xl))
      y
    (revappend-chars-aux x
                         (mbe :logic (+ (nfix n) 1)
                              :exec (+ n 1))
                         xl
                         (cons (char x n) y))))

(defthm revappend-chars-aux-correct
  (implies (and (stringp x)
                (natp n)
                (natp xl)
                (<= n xl)
                (equal xl (length x)))
           (equal (revappend-chars-aux x n xl y)
                  (revappend (nthcdr n (coerce x 'list)) y)))
  :hints(("Goal"
          :in-theory (enable revappend-chars-aux)
          :induct (revappend-chars-aux x n xl y))))

(defund revappend-chars (x y)

  ":Doc-Section Str
  Efficient (revappend (coerce x 'list) y~/

  This function is logically equal to ~c[(revappend (coerce x 'list) y)], but
  is implemented efficiently via ~c[char]. ~/ "

  (declare (xargs :guard (stringp x))
           (type string x))

  (mbe :logic (revappend (coerce x 'list) y)
       :exec (revappend-chars-aux x 0 (length x) y)))

(defthm character-listp-of-revappend-chars
  (equal (character-listp (revappend-chars x y))
         (character-listp y))
  :hints(("Goal" :in-theory (enable revappend-chars))))



#||

(include-book ;; newline to fool dependency scanner
 "cat")

;; Simple experiments on fv-1:

(defparameter *str* "Hello, world!")

;; 3.84 seconds, 2.08 GB allocated
(progn
  (gc$)
  (time (loop for i fixnum from 1 to 5000000
              do
              (revappend (coerce *str* 'list) nil))))

;; 2.88 seconds, 1.04 GB allocated
(progn
  (gc$)
  (time (loop for i fixnum from 1 to 5000000
              do
              (STR::revappend-chars *str* nil))))


;; 4.38 seconds, 2.08 GB allocated
(progn
  (gc$)
  (time (loop for i fixnum from 1 to 5000000
              do
              (append (coerce *str* 'list) nil))))

;; 3.00 seconds, 1.04 GB allocated
(progn
  (gc$)
  (time (loop for i fixnum from 1 to 5000000
              do
              (STR::append-chars *str* nil))))

||#
