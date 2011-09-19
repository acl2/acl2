; VL Verilog Toolkit
; Copyright (C) 2008-2011 Centaur Technology
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

(in-package "VL")
(local (include-book "make-event/assert" :dir :system))
(local (include-book "arithmetic"))


; URL Encoding
;
; Per RFC 3986 (http://tools.ietf.org/html/rfc3986), the only unreserved
; characters are ALPHA, DIGIT, -, ., _, and ~.  We implement some functions to
; percent-encode other characters in character lists and strings.
;
;   (vl-url-encode-chars-aux chars acc)
;      URL-encode all chars and revappend the resulting chars into acc.
;
;   (vl-url-encode-chars chars)
;      Return the URL-encoding of a character list as a character list.
;
;   (vl-url-encode-string-aux x n xl acc)
;      URL-encode the string x[n:xl] and revappend the resulting chars into acc
;
;   (vl-url-encode-string x)
;      Return the URL-encoding of a string as a string.

(defund vl-url-encode-char (x)
  (declare (xargs :guard (characterp x)))
  (if (or (and (char<= #\A x) (char<= x #\Z))
          (and (char<= #\a x) (char<= x #\z))
          (and (char<= #\0 x) (char<= x #\9))
          (member x '(#\- #\_ #\. #\~)))
      (list x)
    (let* ((hex-code (cddr (explode-atom (char-code x) 16)))
           (hex-code (if (= (len hex-code) 1)
                         (cons #\0 hex-code)
                       hex-code)))
      (cons #\% hex-code))))

(local
 (progn
   (assert! (equal (coerce (vl-url-encode-char #\a) 'string)           "a"))
   (assert! (equal (coerce (vl-url-encode-char #\Space) 'string)       "%20"))
   (assert! (equal (coerce (vl-url-encode-char (code-char 0)) 'string) "%00"))))

(defund vl-make-url-encode-array (n)
  (declare (xargs :guard (and (natp n)
                              (<= n 255))))
  (if (zp n)
      (list (cons n (vl-url-encode-char (code-char n))))
    (cons (cons n (vl-url-encode-char (code-char n)))
          (vl-make-url-encode-array (- n 1)))))

(defconst *vl-url-encode-array*
  (compress1 'vl-url-encode-array
             (cons '(:header :dimensions (256) :maximum-length 257 :name vl-url-encode-array)
                   (vl-make-url-encode-array 255))))

(defund vl-url-encode-chars-aux (chars acc)
  (declare (xargs :guard (character-listp chars)))
  (if (atom chars)
      acc
    (vl-url-encode-chars-aux
     (cdr chars)
     (revappend (aref1 'vl-url-encode-array *vl-url-encode-array* (char-code (car chars)))
                acc))))

(defthm character-listp-of-vl-url-encode-chars-aux
  (implies (character-listp acc)
           (character-listp (vl-url-encode-chars-aux x acc)))
  :hints(("Goal"
          :induct (vl-url-encode-chars-aux x acc)
          :in-theory (e/d (vl-url-encode-chars-aux) (aref1)))
         (and acl2::stable-under-simplificationp
              '(:in-theory (enable aref1)))))

(defthm true-listp-of-vl-url-encode-chars-aux
  (equal (true-listp (vl-url-encode-chars-aux x acc))
         (true-listp acc))
  :hints(("Goal"
          :in-theory (e/d (vl-url-encode-chars-aux)
                          (aref1)))))



(defund vl-url-encode-chars (x)
  (declare (xargs :guard (character-listp x)))

; This could be optimized with nreverse, but since the printer only uses the
; aux function anyway, I haven't bothered.

  (reverse (vl-url-encode-chars-aux x nil)))

(defthm character-listp-of-vl-url-encode-chars
  (implies (character-listp x)
           (character-listp (vl-url-encode-chars x)))
  :hints(("Goal" :in-theory (enable vl-url-encode-chars))))

(defthm true-listp-of-vl-url-encode-chars
  (true-listp (vl-url-encode-chars x))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable vl-url-encode-chars))))



(defund vl-url-encode-string-aux (x n xl acc)
  (declare (xargs :guard (and (stringp x)
                              (natp n)
                              (natp xl)
                              (<= n xl)
                              (= xl (length x)))
                  :measure (nfix (- (nfix xl) (nfix n)))))
  (if (mbe :logic (zp (- (nfix xl) (nfix n)))
           :exec (= n xl))
      acc
    (let* ((char     (char x n))
           (encoding (aref1 'vl-url-encode-array *vl-url-encode-array* (char-code char))))
      (vl-url-encode-string-aux x
                                (mbe :logic (+ 1 (nfix n)) :exec (+ 1 n))
                                xl
                                (revappend encoding acc)))))

(defthm character-listp-of-vl-url-encode-string-aux
  (implies (and (stringp x)
                (character-listp acc)
                (natp n)
                (natp xl)
                (<= n xl)
                (= xl (length x)))
           (character-listp (vl-url-encode-string-aux x n xl acc)))
  :hints(("Goal"
          :induct (vl-url-encode-string-aux x n xl acc)
          :in-theory (e/d (vl-url-encode-string-aux)
                          (aref1)))
         (and acl2::stable-under-simplificationp
              '(:in-theory (enable aref1)))))

(defund vl-url-encode-string (x)
  (declare (xargs :guard (stringp x)))

; This could be optimized with nreverse, but since the printer only uses the
; aux function anyway, I haven't bothered.

  (reverse (coerce (vl-url-encode-string-aux x 0 (length x) nil) 'string)))

(defthm stringp-of-vl-url-encode-string
  (stringp (vl-url-encode-string x))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable vl-url-encode-string))))


(local (assert!
        (let ((x "foo123$%20 blah !==[]{}7&*^!@&*^&*)($"))
          (equal (vl-url-encode-string x)
                 (coerce (vl-url-encode-chars (coerce x 'list)) 'string)))))
