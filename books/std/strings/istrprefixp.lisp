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
(include-book "ieqv")
(include-book "iprefixp")
(include-book "std/basic/defs" :dir :system)
(include-book "misc/definline" :dir :system)  ;; bozo
(local (include-book "std/lists/nthcdr" :dir :system))
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

(defsection istrprefixp
  :parents (substrings)
  :short "Case-insensitive string prefix test."

  :long "<p>@(call istrprefixp) determines if the string @('x') is a
case-insensitive prefix of the string @('y').</p>

<p>Logically, this is identical to</p>
@({
  (iprefixp (explode x) (explode y))
})

<p>But we use a more efficient implementation which avoids coercing the strings
to lists.</p>"

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
                :exec (int= xn xl))
           t)
          ((mbe :logic (zp (- (nfix yl) (nfix yn)))
                :exec (int= yn yl))
           nil)
          ((ichareqv (char x xn) (char y yn))
           (istrprefixp-impl x y
                             (+ 1 (lnfix xn))
                             (+ 1 (lnfix yn))
                             xl yl))
          (t
           nil)))

  (definline istrprefixp (x y)
    (declare (type string x)
             (type string y)
             (xargs :verify-guards nil))
    (mbe :logic (iprefixp (explode x)
                          (explode y))
         :exec (istrprefixp-impl (the string x)
                                 (the string y)
                                 (the integer 0)
                                 (the integer 0)
                                 (the integer (length (the string x)))
                                 (the integer (length (the string y))))))

  (defthm istrprefixp-impl-elim
    (implies (and (force (stringp x))
                  (force (stringp y))
                  (force (natp xn))
                  (force (natp yn))
                  (force (= xl (length x)))
                  (force (= yl (length y))))
             (equal (istrprefixp-impl x y xn yn xl yl)
                    (iprefixp (nthcdr xn (coerce x 'list))
                              (nthcdr yn (coerce y 'list)))))
    :hints(("Goal" :in-theory (enable istrprefixp-impl))))

  (verify-guards istrprefixp$inline)

  (defcong istreqv equal (istrprefixp x y) 1)
  (defcong istreqv equal (istrprefixp x y) 2))


