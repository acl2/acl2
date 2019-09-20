; ACL2 String Library
; Copyright (C) 2009-2013 Centaur Technology
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
(include-book "cat-base")
(include-book "ieqv")
(include-book "std/util/bstar" :dir :system)
(include-book "std/lists/list-defuns" :dir :system)
(include-book "std/basic/defs" :dir :system)
(local (include-book "arithmetic"))
(local (include-book "std/lists/equiv" :dir :system))


(define append-chars ((x :type string) y)
  :parents (concatenation)
  :short "Append a string's characters onto a list."

  :long "<p>@(call append-chars) takes the characters from the string @('x')
and appends them onto @('y').</p>

<p>Its logical definition is nothing more than @('(append (explode x) y)').</p>

<p>In the execution, we traverse the string @('x') using @(see char) to avoid
the overhead of @(see coerce)-ing it into a character list before performing
the @(see append).  This reduces the overhead from @('2n') conses to @('n')
conses, where @('n') is the length of @('x').</p>"
  :inline t
  (mbe :logic (append (explode x) y)
       :exec (b* (((the (integer 0 *) xl) (length x))
                  ((when (eql xl 0))
                   y)
                  ((the (integer 0 *) n) (- xl 1)))
               (append-chars-aux x n y)))

  :prepwork
  ((defund append-chars-aux (x n y)
     "Appends the characters from x[0:n] onto y"
     (declare (type string x)
              (type (integer 0 *) n)
              (xargs :guard (< n (length x))))
     (if (zp n)
         (cons (char x 0) y)
       (append-chars-aux x
                         (the (integer 0 *) (- n 1))
                         (cons (char x n) y))))

   (local (defthm lemma
            (implies (and (not (zp n))
                          (<= n (len x)))
                     (equal (append (take (- n 1) x) (cons (nth (- n 1) x) y))
                            (append (take n x) y)))
            :hints(("goal"
                    :in-theory (enable acl2::take)
                    :induct (take n x)))))

  (defthm append-chars-aux-correct
    (implies (and (stringp x)
                  (natp n)
                  (< n (length x)))
             (equal (append-chars-aux x n y)
                    (append (take (+ 1 n) (explode x)) y)))
    :hints(("Goal"
            :in-theory (enable append-chars-aux)
            :induct (append-chars-aux x n y)))))
  ///
  (defthm character-listp-of-append-chars
    (equal (character-listp (append-chars x y))
           (character-listp y)))

  (defcong streqv equal (append-chars x y) 1)
  (defcong istreqv icharlisteqv (append-chars x y) 1)
  (defcong list-equiv list-equiv (append-chars x y) 2)
  (defcong charlisteqv charlisteqv (append-chars x y) 2)
  (defcong icharlisteqv icharlisteqv (append-chars x y) 2))



(defsection revappend-chars
  :extension revappend-chars
  (local (in-theory (enable revappend-chars)))

  (defcong streqv equal (revappend-chars x y) 1)
  (defcong istreqv icharlisteqv (revappend-chars x y) 1)
  (defcong list-equiv list-equiv (revappend-chars x y) 2)
  (defcong charlisteqv charlisteqv (revappend-chars x y) 2)
  (defcong icharlisteqv icharlisteqv (revappend-chars x y) 2))


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


(define prefix-strings ((prefix stringp)
                        (x      string-listp))
  :parents (concatenation)
  :short "Concatenates a prefix onto every string in a list of strings."

  :long "<p>@(call prefix-strings) produces a new string list by concatenating
@('prefix') onto every member of @('x').</p>"
  (if (atom x)
      nil
    (cons (cat prefix (car x))
          (prefix-strings prefix (cdr x))))
  ///
  (defthm prefix-strings-when-atom
    (implies (atom x)
             (equal (prefix-strings prefix x)
                    nil)))

  (defthm prefix-strings-of-cons
    (equal (prefix-strings prefix (cons a x))
           (cons (cat prefix a)
                 (prefix-strings prefix x))))

  (defthm string-listp-of-prefix-strings
    (string-listp (prefix-strings prefix x)))

  (defthm len-of-prefix-strings
    (equal (len (prefix-strings prefix x))
           (len x)))

  (defcong streqv equal (prefix-strings prefix x) 1)

  (local (defthmd l0
           (equal (prefix-strings prefix (list-fix x))
                  (prefix-strings prefix x))))

  (defcong list-equiv equal (prefix-strings prefix x) 2
    :hints(("Goal" :in-theory (enable list-equiv)
            :use ((:instance l0 (x x))
                  (:instance l0 (x x-equiv)))))))


(define join ((x string-listp)
              (separator :type string))
  :returns (joined stringp :rule-classes :type-prescription)
  :parents (concatenation)
  :short "Concatenate a list of strings with some separator between."

  :long "<p>@(call join) joins together the list of strings @('x'), inserting
the string @('separator') between the members.  For example:</p>

@({
 (join '(\"a\" \"b\" \"c\") \".\") = \"a.b.c\"
 (join '(\"a\" \"b\" \"c\") \"->\") = \"a->b->c\"
})

<p>We always return a string; an empty @('x') results in the empty string, and
any empty strings within @('x') just implicitly don't contribute to the
result.</p>

<p>Any sort of string concatenation is slow, but @('join') is reasonably
efficient: it creates a single character list for the result (in reverse order)
without any use of @(see coerce), then uses @(see rchars-to-string) to build
and reverse the result string.</p>"

  :prepwork
  ((defund join-aux (x separator acc)
     (declare (xargs :guard (string-listp x))
              (type string separator))
     (cond ((atom x)
            acc)
           ((atom (cdr x))
            (revappend-chars (car x) acc))
           (t
            (let* ((acc (revappend-chars (car x) acc))
                   (acc (revappend-chars separator acc)))
              (join-aux (cdr x) separator acc))))))

  :inline t
  :verify-guards nil
  (mbe :logic
       (cond ((atom x)
              "")
             ((atom (cdr x))
              (str-fix (car x)))
             (t
              (cat (car x) separator (join (cdr x) separator))))
       :exec
       (rchars-to-string (join-aux x separator nil)))
  ///
  (local (in-theory (enable join-aux)))

  (defthm join-aux-removal
    (implies (and (string-listp x)
                  (stringp separator))
             (equal (join-aux x separator acc)
                    (revappend (coerce (join x separator) 'list)
                               acc)))
    :hints(("Goal"
            :induct (join-aux x separator acc)
            :in-theory (enable revappend-chars))))

  (verify-guards join$inline
    :hints(("Goal" :in-theory (enable join join-aux))))

  (local (defthmd l0
           (equal (join (list-fix x) separator)
                  (join x separator))))

  (defcong list-equiv equal (join x separator) 1
    :hints(("Goal" :in-theory (enable list-equiv)
            :use ((:instance l0 (x x))
                  (:instance l0 (x x-equiv))))))

  (defcong streqv equal (join x separator) 2)
  (defcong istreqv istreqv (join x separator) 2))
