; VL 2014 -- VL Verilog Toolkit, 2014 Edition
; Copyright (C) 2008-2015 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "VL2014")
(include-book "std/strings/cat" :dir :system)
(include-book "std/util/defval" :dir :system)
(include-book "centaur/fty/fixequiv" :dir :system)
(include-book "centaur/fty/basetypes" :dir :system)
(local (include-book "std/testing/assert-bang" :dir :system))
(local (include-book "arithmetic"))
(local (std::add-default-post-define-hook :fix))

(defsection url-encoding
  :parents (utilities)
  :short "Functions for % encoding strings for use in URLs, as described in <a
href='http://tools.ietf.org/html/rfc3986'>RFC 3986</a>."

  :long "<p>Per RFC 3986, the only unreserved characters are ALPHA, DIGIT, -,
., _, and ~.  We implement some functions to percent-encode other characters in
character lists and strings.</p>")

(local (xdoc::set-default-parents url-encoding))

(define vl-url-encode-char ((x characterp))
  :short "URL encode a single character. (slow, logically nice version)."
  :returns (encoding character-listp "Encoded version of X, in proper order.")
  :long "<p>See @(see vl-fast-url-encode-char) for an faster, array-lookup
  alternative.</p>"
  (let ((x (char-fix x)))
    (if (or (and (char<= #\A x) (char<= x #\Z))
            (and (char<= #\a x) (char<= x #\z))
            (and (char<= #\0 x) (char<= x #\9))
            (member x '(#\- #\_ #\. #\~)))
        (list x)
      (let* ((hex-code (explode-atom (char-code x) 16))
             (hex-code (if (eql (len hex-code) 1)
                           (cons #\0 hex-code)
                         hex-code)))
        (cons #\% hex-code))))
  ///
  (local
   (progn
     (assert! (equal (implode (vl-url-encode-char #\a))           "a"))
     (assert! (equal (implode (vl-url-encode-char #\Space))       "%20"))
     (assert! (equal (implode (vl-url-encode-char (code-char 0))) "%00")))))


(define vl-make-url-encode-array ((n natp))
  :parents (*vl-url-encode-array*)
  :guard (<= n 255)
  :hooks nil
  (if (zp n)
      (list (cons n (vl-url-encode-char (code-char n))))
    (cons (cons n (vl-url-encode-char (code-char n)))
          (vl-make-url-encode-array (- n 1)))))

(defval *vl-url-encode-array*
  :short "Array binding character codes to the pre-computed URL encodings."
  :showval t
  (compress1 'vl-url-encode-array
             (cons '(:header :dimensions (256)
                     :maximum-length 257
                     :name vl-url-encode-array)
                   (vl-make-url-encode-array 255))))

(define vl-fast-url-encode-char ((x :type character))
  :short "URL encode a single character. (fast, array-based version)"
  :inline t
  :enabled t
  :verify-guards nil
  :hooks nil
  (mbe :logic (vl-url-encode-char x)
       :exec (aref1 'vl-url-encode-array *vl-url-encode-array*
                    (char-code x)))
  ///
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

  (verify-guards vl-fast-url-encode-char$inline))



(define vl-url-encode-chars-aux ((chars character-listp) acc)
  :short "URL encode a list of characters onto an accumulator in reverse order."
  :returns (encoded character-listp :hyp (character-listp acc))
  :verbosep t
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
  :short "Simple way to URL encode a list of characters."
  :returns (encoded character-listp)
  :inline t

; This could be optimized with nreverse, but since the printer only uses the
; aux function anyway, I haven't bothered.

  (reverse (vl-url-encode-chars-aux x nil))

  ///
  (defthm true-listp-of-vl-url-encode-chars
    (true-listp (vl-url-encode-chars x))
    :rule-classes :type-prescription))

(define vl-url-encode-string-aux
  :short "Efficiently way to URL encode a string, in reverse order, without
  exploding it."
  ((x stringp)
   (n natp)
   (xl (eql xl (length x)))
   acc)
  :guard (<= n xl)
  :long "<p>This has such a nice logical definition that we just leave it enabled.</p>"
  :enabled t
; Removed after v7-2 by Matt K. since logically, the definition is
; non-recursive:
; :measure (nfix (- (nfix xl) (nfix n)))
  :verify-guards nil
  :hooks nil
  (mbe :logic
       (vl-url-encode-chars-aux (nthcdr n (explode x)) acc)
       :exec
       (b* (((when (mbe :logic (zp (- (nfix xl) (nfix n)))
                        :exec (eql n xl)))
             acc)
            (char     (char x n))
            (encoding (vl-fast-url-encode-char char))
            (acc      (revappend encoding acc)))
         (vl-url-encode-string-aux x (+ 1 (lnfix n)) xl acc)))
  ///
  (local (in-theory (enable vl-url-encode-string-aux
                            vl-url-encode-chars-aux)))
  (verify-guards vl-url-encode-string-aux))


(define vl-url-encode-string
  :short "Simple way to URL encode a string."
  ((x stringp :type string))
  :returns (encoded stringp :rule-classes :type-prescription)
  :split-types t
  :inline t
  (let ((x (mbe :logic (str-fix x) :exec x)))
    (str::rchars-to-string
     (vl-url-encode-string-aux x 0 (length x) nil)))
  ///
  (local (assert!
          (let ((x "foo123$%20 blah !==[]{}7&*^!@&*^&*)($"))
            (equal (vl-url-encode-string x)
                   (implode (vl-url-encode-chars (explode x))))))))
