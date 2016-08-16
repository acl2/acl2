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
(include-book "strprefixp")
(include-book "std/basic/defs" :dir :system)
(local (include-book "arithmetic"))

; BOZO should probably rewrite this to have a nice listrpos function sort of
; thing.

(defsection strrpos-fast
  :parents (strrpos)
  :short "Fast implementation of @(see strrpos)."

  (defund strrpos-fast (x y n xl yl)
    (declare (type string x y)
             (type (integer 0 *) n xl yl)
             (xargs :guard (and (stringp x)
                                (stringp y)
                                (natp xl)
                                (natp yl)
                                (natp n)
                                (<= n (length y))
                                (= xl (length x))
                                (= yl (length y)))
                    :measure (nfix n)))
    ;; N goes from YL to 0.
    (cond ((mbe :logic (prefixp (explode x)
                                (nthcdr n (explode y)))
                :exec (strprefixp-impl (the string x)
                                       (the string y)
                                       (the integer 0)
                                       (the (integer 0 *) n)
                                       (the (integer 0 *) xl)
                                       (the (integer 0 *) yl)))
           (lnfix n))
          ((zp n)
           nil)
          (t
           (strrpos-fast (the string x)
                         (the string y)
                         (the (integer 0 *) (+ -1 (lnfix n)))
                         (the (integer 0 *) xl)
                         (the (integer 0 *) yl)))))

  (local (in-theory (enable strrpos-fast)))

  (defthm strrpos-fast-type
    (or (and (integerp (strrpos-fast x y n xl yl))
             (<= 0 (strrpos-fast x y n xl yl)))
        (not (strrpos-fast x y n xl yl)))
    :rule-classes :type-prescription)

  (defthm strrpos-fast-upper-bound
    (implies (force (natp n))
             (<= (strrpos-fast x y n xl yl) n))
    :rule-classes :linear)

  (defthm strrpos-fast-when-empty
    (implies (and (not (consp (explode x)))
                  (equal xl (length x))
                  (equal yl (length y))
                  (natp n))
             (equal (strrpos-fast x y n xl yl)
                    n))))

(defsection strrpos
  :parents (substrings)
  :short "Locate the last occurrence of a substring."

  :long "<p>@(call strrpos) searches through the string @('y') for the last
occurrence of the substring @('x').  If @('x') occurs somewhere in @('y'), it
returns the starting index of the last occurrence.  Otherwise, it returns
@('nil') to indicate that @('x') never occurs in @('y').</p>

<p>The function is \"efficient\" in the sense that it does not coerce its
arguments into lists, but rather traverses both strings with @(see char).  On
the other hand, it is a naive string search which operates by repeatedly
calling @(see strprefixp), rather than some better algorithm.</p>

<p>Corner case: we say that the empty string <b>is</b> an prefix of any other
string.  As a consequence, @('(strrpos \"\" x)') is (length x) for all
@('x').</p>"

  (definlined strrpos (x y)
    (declare (type string x y))
    (let ((x (mbe :logic (str-fix x) :exec x))
          (y (mbe :logic (str-fix y) :exec y))
          (yl (length (the string y))))
      (declare (type string x y)
               (type (integer 0 *) yl))
      (strrpos-fast (the string x)
                    (the string y)
                    (the (integer 0 *) yl)
                    (the (integer 0 *) (length (the string x)))
                    (the (integer 0 *) yl))))

  (local (in-theory (enable strrpos strrpos-fast)))

  (defthm strrpos-type
    (or (and (integerp (strrpos x y))
             (<= 0 (strrpos x y)))
        (not (strrpos x y)))
    :rule-classes :type-prescription)

  (local (in-theory (enable str-fix)))

  (encapsulate
    ()
    (local (defthm lemma
             (implies (and (stringp x)
                           (stringp y)
                           (natp xl)
                           (natp yl)
                           (natp n)
                           (<= n (length y))
                           (= xl (length x))
                           (= yl (length y))
                           (strrpos-fast x y n xl yl))
                      (prefixp (explode x)
                               (nthcdr (strrpos-fast x y n xl yl)
                                       (explode y))))
             :hints(("Goal" :induct (strrpos-fast x y n xl yl)))))

    (defthm prefixp-of-strrpos
      (implies (strrpos x y)
               (prefixp (explode x)
                        (nthcdr (strrpos x y) (explode y))))))

  (encapsulate
    ()
    (local (defun my-induction (x y n m xl yl)
             (declare (xargs :measure (nfix n)))
             (cond ((prefixp (explode x)
                             (nthcdr n (explode y)))
                    nil)
                   ((zp n)
                    (list x y n m xl yl))
                   (t
                    (my-induction x y
                                  (- (nfix n) 1)
                                  (if (= (nfix n) (nfix m))
                                      (- (nfix m) 1)
                                    m)
                                  xl yl)))))

    (local (defthm lemma
             (implies (and (stringp x)
                           (stringp y)
                           (natp xl)
                           (natp yl)
                           (natp n)
                           (natp m)
                           (>= n m)
                           (<= n (length y))
                           (= xl (length x))
                           (= yl (length y))
                           (prefixp (explode x)
                                    (nthcdr m (explode y))))
                      (and (natp (strrpos-fast x y n xl yl))
                           (>= (strrpos-fast x y n xl yl) m)))
             :hints(("Goal"
                     :induct (my-induction x y n m xl yl)
                     :do-not '(generalize fertilize)))))

    (defthm completeness-of-strrpos
      (implies (and (prefixp (explode x)
                             (nthcdr m (explode y)))
                    (<= m (len y))
                    (force (natp m)))
               (and (natp (strrpos x y))
                    (>= (strrpos x y) m)))))


  (defthm strrpos-upper-bound-weak
    ;; Aah, this force is necessary because explode doesn't properly string-fix
    ;; things.  What a bummer...
    (implies (force (stringp y))
             (<= (strrpos x y)
                 (len (explode y))))
    :rule-classes ((:rewrite) (:linear)))

  (encapsulate
    ()
    (local (defthm lemma
             (implies (and (stringp x)
                           (stringp y)
                           (posp xl)
                           (posp yl)
                           (natp n)
                           (<= n (length y))
                           (= xl (length x))
                           (= yl (length y)))
                      (< (strrpos-fast x y n xl yl) yl))
             :hints(("Goal"
                     :induct (strrpos-fast x y n xl yl)))))

    (defthm strrpos-upper-bound-strong
      (implies (and (not (equal y ""))
                    (not (equal x ""))
                    (force (stringp x))
                    (force (stringp y)))
               (< (strrpos x y)
                  (len (explode y))))
      :rule-classes ((:rewrite) (:linear))))


  (encapsulate
    ()
    (local (defthm lens-same-when-list-equiv
             (implies (list-equiv x y)
                      (equal (len x) (len y)))
             :rule-classes :forward-chaining))

    (local (defthm len-of-nthcdr
             (equal (len (nthcdr n x))
                    (if (< (nfix n) (len x))
                        (- (len x) (nfix n))
                      0))))

    (local (defthm len-bounded-by-prefixp
             (implies (prefixp x y)
                      (<= (len x) (len y)))
             :rule-classes ((:linear) (:forward-chaining))))

    (local (defthm prefixp-of-self-and-cdr
             (equal (prefixp x (cdr x))
                    (atom x))))

    (local (defthm prefixp-of-nthcdr-bounds-n
             (IMPLIES (AND (PREFIXP X (NTHCDR N Y))
                           (case-split (consp x)))
                      (<= (nfix N)
                          (- (LEN Y) (LEN X))))
             :rule-classes ((:rewrite) (:linear))
             :hints(("Goal" :in-theory (enable prefixp nthcdr)))))

    (local (defthm lemma1
             (implies (and (strrpos-fast x y n xl yl)
                           (stringp x)
                           (stringp y)
                           (natp n)
                           (= xl (length x))
                           (= yl (length y))
                           (<= n (length y)))
                      (<= (strrpos-fast x y n xl yl)
                          (- yl xl)))
             :rule-classes ((:rewrite) (:linear))))

    (defthm strrpos-upper-bound-stronger
      (implies (and (strrpos x y)
                    (force (stringp x))
                    (force (stringp y)))
               (<= (strrpos x y)
                   (- (len (explode y))
                      (len (explode x)))))
      :rule-classes ((:rewrite) (:linear)))))
