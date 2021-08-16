; ACL2 String Library
; Copyright (C) 2009-2016 Centaur Technology
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

(in-package "STR")
(include-book "cat")
(include-book "hex")
(include-book "std/util/defval" :dir :system)
(include-book "centaur/fty/fixequiv" :dir :system)
(include-book "centaur/fty/basetypes" :dir :system)
(local (include-book "std/lists/nthcdr" :dir :system))
(local (include-book "std/typed-lists/character-listp" :dir :system))
(local (std::add-default-post-define-hook :fix))

(defsection url-encoding
  :parents (std/strings)
  :short "Functions for % encoding strings for use in URLs, as described in <a
href='http://tools.ietf.org/html/rfc3986'>RFC 3986</a>."

  :long "<p>Per <a href='https://www.ietf.org/rfc/rfc3986.txt'>RFC 3986</a>,
the only unreserved characters are ALPHA, DIGIT, @('-'), @('.'), @('_'), and
@('~').  We implement some functions to percent-encode other characters in
character lists and strings.</p>")

(xdoc::order-subtopics url-encoding
                       (url-encode-string
                        url-encode-chars
                        url-encode-char))

(local (xdoc::set-default-parents url-encoding))

(define url-encode-char ((x characterp))
  :short "URL encode a single character. (slow, logically nice version)."
  :returns (encoding character-listp "Encoded version of X, in proper order.")
  :long "<p>See @(see fast-url-encode-char) for an faster, array-lookup
  alternative.</p>"
  (b* ((x (char-fix x))
       ((when (or (and (char<= #\A x) (char<= x #\Z))
                  (and (char<= #\a x) (char<= x #\z))
                  (and (char<= #\0 x) (char<= x #\9))
                  (member x '(#\- #\_ #\. #\~))))
        (list x))
       (hex-code (nat-to-hex-chars (char-code x)))
       (hex-code (if (eql (len hex-code) 1)
                     (cons #\0 hex-code)
                   hex-code)))
    (cons #\% hex-code)))


(define make-url-encode-array ((n natp))
  :parents (*url-encode-array*)
  :guard (<= n 255)
  :hooks nil
  (if (zp n)
      (list (cons n (url-encode-char (code-char n))))
    (cons (cons n (url-encode-char (code-char n)))
          (make-url-encode-array (- n 1)))))

(std::defval *url-encode-array*
  :short "Array binding character codes to the pre-computed URL encodings."
  :showval t
  (compress1 'url-encode-array
             (cons '(:header :dimensions (256)
                     :maximum-length 257
                     :name url-encode-array)
                   (make-url-encode-array 255))))

(define fast-url-encode-char ((x :type character))
  :short "URL encode a single character. (fast, array-based version)"
  :inline t
  :enabled t
  :verify-guards nil
  :hooks nil
  (mbe :logic (url-encode-char x)
       :exec (aref1 'url-encode-array *url-encode-array*
                    (char-code x)))
  ///
  (local (in-theory (disable aref1)))

  (local (defun test (n)
           (and (equal (aref1 'url-encode-array *url-encode-array* n)
                       (url-encode-char (code-char n)))
                (if (zp n)
                    t
                  (test (- n 1))))))

  (local (defthm l0
           (implies (and (test n)
                         (natp n)
                         (natp i)
                         (<= i n))
                    (equal (aref1 'url-encode-array *url-encode-array* i)
                           (url-encode-char (code-char i))))))

  (local (defthm l1
           (implies (and (natp i)
                         (<= i 255))
                    (equal (aref1 'url-encode-array *url-encode-array* i)
                           (url-encode-char (code-char i))))
           :hints(("Goal" :use ((:instance l0 (n 255)))))))

  (local (defthm l2
           (implies (characterp x)
                    (equal (aref1 'url-encode-array *url-encode-array*
                                  (char-code x))
                           (url-encode-char x)))))

  (verify-guards fast-url-encode-char$inline))


(define url-encode-chars-aux ((chars character-listp) acc)
  :short "URL encode a list of characters onto an accumulator in reverse order."
  :returns (encoded character-listp :hyp (character-listp acc))
  (if (atom chars)
      acc
    (url-encode-chars-aux
     (cdr chars)
     (revappend (fast-url-encode-char (car chars)) acc)))
  ///
  (defthm true-listp-of-url-encode-chars-aux
    (equal (true-listp (url-encode-chars-aux x acc))
           (true-listp acc))))


(define url-encode-chars ((x character-listp))
  :short "Simple way to URL encode a list of characters."
  :returns (encoded character-listp)
  :inline t
  ;; BOZO could use nreverse here
  (reverse (url-encode-chars-aux x nil))
  ///
  (defthm true-listp-of-url-encode-chars
    (true-listp (url-encode-chars x))
    :rule-classes :type-prescription))

(define url-encode-string-aux
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
       (url-encode-chars-aux (nthcdr n (explode x)) acc)
       :exec
       (b* (((when (mbe :logic (zp (- (nfix xl) (nfix n)))
                        :exec (eql n xl)))
             acc)
            (char     (char x n))
            (encoding (fast-url-encode-char char))
            (acc      (revappend encoding acc)))
         (url-encode-string-aux x (+ 1 (lnfix n)) xl acc)))
  ///
  (local (in-theory (enable url-encode-string-aux
                            url-encode-chars-aux)))
  (verify-guards url-encode-string-aux))


(define url-encode-string
  :short "Simple way to URL encode a string."
  ((x stringp :type string))
  :returns (encoded stringp :rule-classes :type-prescription)
  :split-types t
  :inline t
  (let ((x (mbe :logic (str-fix x) :exec x)))
    (str::rchars-to-string
     (url-encode-string-aux x 0 (length x) nil))))
