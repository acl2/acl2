; VL Verilog Toolkit
; Copyright (C) 2008-2014 Centaur Technology
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

(define vl-url-encode-char ((x :type character))
  :returns (encoding character-listp)
  (if (or (and (char<= #\A x) (char<= x #\Z))
          (and (char<= #\a x) (char<= x #\z))
          (and (char<= #\0 x) (char<= x #\9))
          (member x '(#\- #\_ #\. #\~)))
      (list x)
    (let* ((hex-code (explode-atom (char-code x) 16))
           (hex-code (if (eql (len hex-code) 1)
                         (cons #\0 hex-code)
                       hex-code)))
      (cons #\% hex-code)))
  ///
  (local
   (progn
     (assert! (equal (implode (vl-url-encode-char #\a))           "a"))
     (assert! (equal (implode (vl-url-encode-char #\Space))       "%20"))
     (assert! (equal (implode (vl-url-encode-char (code-char 0))) "%00")))))


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

  (define vl-fast-url-encode-char ((x :type character))
    :inline t
    :enabled t
    (mbe :logic (vl-url-encode-char x)
         :exec (aref1 'vl-url-encode-array *vl-url-encode-array*
                      (char-code x)))))


(define vl-url-encode-chars-aux ((chars character-listp) acc)
  :returns (encoded character-listp :hyp (character-listp acc))
  (if (atom chars)
      acc
    (vl-url-encode-chars-aux
     (cdr chars)
     (revappend (vl-fast-url-encode-char (car chars)) acc)))
  ///
  (defthm true-listp-of-vl-url-encode-chars-aux
    (equal (true-listp (vl-url-encode-chars-aux x acc))
           (true-listp acc))))


(define vl-url-encode-chars ((x character-listp))
  :returns (encoded character-listp)
  :inline t

; This could be optimized with nreverse, but since the printer only uses the
; aux function anyway, I haven't bothered.

  (reverse (vl-url-encode-chars-aux x nil))

  ///
  (defthm true-listp-of-vl-url-encode-chars
    (true-listp (vl-url-encode-chars x))
    :rule-classes :type-prescription))


(define vl-url-encode-string-aux ((x :type string)
                                  (n natp)
                                  (xl (eql xl (length x)))
                                  acc)
  :guard (<= n xl)
  :measure (nfix (- (nfix xl) (nfix n)))
  (b* (((when (mbe :logic (zp (- (nfix xl) (nfix n)))
                   :exec (eql n xl)))
        acc)
       (char     (char x n))
       (encoding (vl-fast-url-encode-char char))
       (acc      (revappend encoding acc)))
    (vl-url-encode-string-aux x (+ 1 (lnfix n)) xl acc))
  ///
  (defthm character-listp-of-vl-url-encode-string-aux
    (implies (and (stringp x)
                  (character-listp acc)
                  (natp n)
                  (natp xl)
                  (<= n xl)
                  (= xl (length x)))
             (character-listp (vl-url-encode-string-aux x n xl acc)))))

(define vl-url-encode-string ((x :type string))
  :inline t
  :returns (encoded stringp :rule-classes :type-prescription)
  (str::rchars-to-string
   (vl-url-encode-string-aux x 0 (length x) nil)))

(local (assert!
        (let ((x "foo123$%20 blah !==[]{}7&*^!@&*^&*)($"))
          (equal (vl-url-encode-string x)
                 (implode (vl-url-encode-chars (explode x)))))))
