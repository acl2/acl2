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
(include-book "eqv")
(include-book "std/lists/prefixp" :dir :system)
(include-book "misc/definline" :dir :system)  ;; bozo
(local (include-book "std/lists/nthcdr" :dir :system))
(local (include-book "arithmetic"))

(local (defthm prefixp-lemma-1
         (implies (and (natp xn)
                       (natp yn)
                       (< xn (len x))
                       (< yn (len y))
                       (not (equal (nth xn x) (nth yn y))))
                  (not (prefixp (nthcdr xn x) (nthcdr yn y))))
         :hints(("Goal" :in-theory (enable nthcdr nth prefixp)))))

(local (defthm prefixp-lemma-2
         (implies (and (natp xn)
                       (natp yn)
                       (< xn (len x))
                       (< yn (len y))
                       (equal (nth xn x) (nth yn y)))
                  (equal (prefixp (nthcdr xn x) (nthcdr yn y))
                         (prefixp (cdr (nthcdr xn x)) (cdr (nthcdr yn y)))))
         :hints(("Goal" :in-theory (enable prefixp nth nthcdr)))))

(defsection strprefixp-impl
  :parents (strprefixp)
  :short "Fast implementation of @(see strprefixp)."

  (defund strprefixp-impl (x y xn yn xl yl)
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
                                  (nfix (- (nfix yl) (nfix yn))))))
    (cond ((mbe :logic (zp (- (nfix xl) (nfix xn)))
                :exec (int= xn xl))
           t)
          ((mbe :logic (zp (- (nfix yl) (nfix yn)))
                :exec (int= yn yl))
           nil)
          ((eql (the character (char x xn))
                (the character (char y yn)))
           (mbe :logic (strprefixp-impl x y
                                        (+ (nfix xn) 1)
                                        (+ (nfix yn) 1)
                                        xl yl)
                :exec  (strprefixp-impl (the string x)
                                        (the string y)
                                        (the integer (+ (the integer xn) 1))
                                        (the integer (+ (the integer yn) 1))
                                        (the integer xl)
                                        (the integer yl))))
          (t
           nil)))

  (local (in-theory (enable strprefixp-impl)))

  (defthm strprefixp-impl-elim
    (implies (and (force (stringp x))
                  (force (stringp y))
                  (force (natp xn))
                  (force (natp yn))
                  (force (= xl (length x)))
                  (force (= yl (length y))))
             (equal (strprefixp-impl x y xn yn xl yl)
                    (prefixp (nthcdr xn (explode x))
                             (nthcdr yn (explode y)))))))

(defsection strprefixp
  :parents (substrings)
  :short "Case-sensitive string prefix test."

  :long "<p>@(call strprefixp) determines if the string @('x') is a prefix of
the string @('y'), in a case-sensitive manner.</p>

<p>Logically, this is identical to</p>

@({
 (prefixp (explode x) (explode y))
})

<p>But we use a more efficient implementation which avoids coercing the strings
into character lists.</p>"

  (definline strprefixp (x y)
    (declare (type string x)
             (type string y))
    (mbe :logic (prefixp (explode x)
                         (explode y))
         :exec (strprefixp-impl (the string x)
                                (the string y)
                                (the integer 0)
                                (the integer 0)
                                (the integer (length (the string x)))
                                (the integer (length (the string y))))))

  (defcong streqv equal (strprefixp x y) 1)
  (defcong streqv equal (strprefixp x y) 2))
