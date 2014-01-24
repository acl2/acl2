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
(include-book "std/strings/cat" :dir :system)
(local (include-book "misc/assert" :dir :system))
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

(defsection vl-url-encode-char

  (defund vl-url-encode-char (x)
    (declare (xargs :guard (characterp x)))
    (if (or (and (char<= #\A x) (char<= x #\Z))
            (and (char<= #\a x) (char<= x #\z))
            (and (char<= #\0 x) (char<= x #\9))
            (member x '(#\- #\_ #\. #\~)))
        (list x)
      (let* ((hex-code (explode-atom (char-code x) 16))
             (hex-code (if (= (len hex-code) 1)
                           (cons #\0 hex-code)
                         hex-code)))
        (cons #\% hex-code))))

  (local
   (progn
     (assert! (equal (implode (vl-url-encode-char #\a))           "a"))
     (assert! (equal (implode (vl-url-encode-char #\Space))       "%20"))
     (assert! (equal (implode (vl-url-encode-char (code-char 0))) "%00"))))

  (local (in-theory (enable vl-url-encode-char)))

  (defthm character-listp-of-vl-url-encode-char
    (character-listp (vl-url-encode-char x))))


(defsection vl-fast-url-encode-char

  (defund vl-make-url-encode-array (n)
    (declare (xargs :guard (and (natp n)
                                (<= n 255))))
    (if (zp n)
        (list (cons n (vl-url-encode-char (code-char n))))
      (cons (cons n (vl-url-encode-char (code-char n)))
            (vl-make-url-encode-array (- n 1)))))

  (defconst *vl-url-encode-array*
    (compress1 'vl-url-encode-array
               (cons '(:header :dimensions (256)
                               :maximum-length 257
                               :name vl-url-encode-array)
                     (vl-make-url-encode-array 255))))

  (local (in-theory (disable aref1)))

  (local (defun test (n)
           (and (equal (aref1 'vl-url-encode-array *vl-url-encode-array* n)
                       (vl-url-encode-char (code-char n)))
                (if (zp n)
                    t
                  (test (- n 1))))))

  (local (defthm l0
           (implies (and (test n)
                         (natp n)
                         (natp i)
                         (<= i n))
                    (equal (aref1 'vl-url-encode-array *vl-url-encode-array* i)
                           (vl-url-encode-char (code-char i))))))

  (local (defthm l1
           (implies (and (natp i)
                         (<= i 255))
                    (equal (aref1 'vl-url-encode-array *vl-url-encode-array* i)
                           (vl-url-encode-char (code-char i))))
           :hints(("Goal" :use ((:instance l0 (n 255)))))))

  (local (defthm l2
           (implies (characterp x)
                    (equal (aref1 'vl-url-encode-array *vl-url-encode-array*
                                  (char-code x))
                           (vl-url-encode-char x)))))

  (definline vl-fast-url-encode-char (x)
    (declare (xargs :guard (characterp x)))
    (mbe :logic (vl-url-encode-char x)
         :exec (aref1 'vl-url-encode-array *vl-url-encode-array*
                      (char-code x)))))


(defsection vl-url-encode-chars-aux

  (defund vl-url-encode-chars-aux (chars acc)
    (declare (xargs :guard (character-listp chars)))
    (if (atom chars)
        acc
      (vl-url-encode-chars-aux
       (cdr chars)
       (revappend (vl-fast-url-encode-char (car chars)) acc))))

  (local (in-theory (enable vl-url-encode-chars-aux)))

  (defthm character-listp-of-vl-url-encode-chars-aux
    (implies (character-listp acc)
             (character-listp (vl-url-encode-chars-aux x acc))))

  (defthm true-listp-of-vl-url-encode-chars-aux
    (equal (true-listp (vl-url-encode-chars-aux x acc))
           (true-listp acc))))


(defsection vl-url-encode-chars

; This could be optimized with nreverse, but since the printer only uses the
; aux function anyway, I haven't bothered.

  (defund vl-url-encode-chars (x)
    (declare (xargs :guard (character-listp x)))
    (reverse (vl-url-encode-chars-aux x nil)))

  (local (in-theory (enable vl-url-encode-chars)))

  (defthm character-listp-of-vl-url-encode-chars
    (implies (character-listp x)
             (character-listp (vl-url-encode-chars x))))

  (defthm true-listp-of-vl-url-encode-chars
    (true-listp (vl-url-encode-chars x))
    :rule-classes :type-prescription))


(defsection vl-url-encode-string-aux

  (defund vl-url-encode-string-aux (x n xl acc)
    (declare (xargs :guard (and (stringp x)
                                (natp n)
                                (natp xl)
                                (<= n xl)
                                (= xl (length x)))
                    :measure (nfix (- (nfix xl) (nfix n)))))
    (if (mbe :logic (zp (- (nfix xl) (nfix n)))
             :exec (int= n xl))
        acc
      (let* ((char     (char x n))
             (encoding (vl-fast-url-encode-char char))
             (acc      (revappend encoding acc)))
        (vl-url-encode-string-aux x (+ 1 (lnfix n)) xl acc))))

  (local (in-theory (enable vl-url-encode-string-aux)))

  (defthm character-listp-of-vl-url-encode-string-aux
    (implies (and (stringp x)
                  (character-listp acc)
                  (natp n)
                  (natp xl)
                  (<= n xl)
                  (= xl (length x)))
             (character-listp (vl-url-encode-string-aux x n xl acc)))))


(defsection vl-url-encode-string

; This could be optimized with nreverse, but since the printer only uses the
; aux function anyway, I haven't bothered.

  (defund vl-url-encode-string (x)
    (declare (xargs :guard (stringp x)))
    (str::rchars-to-string
     (vl-url-encode-string-aux x 0 (length x) nil)))

  (local (in-theory (enable vl-url-encode-string)))

  (defthm stringp-of-vl-url-encode-string
    (stringp (vl-url-encode-string x))
    :rule-classes :type-prescription))


(local (assert!
        (let ((x "foo123$%20 blah !==[]{}7&*^!@&*^&*)($"))
          (equal (vl-url-encode-string x)
                 (implode (vl-url-encode-chars (explode x)))))))
