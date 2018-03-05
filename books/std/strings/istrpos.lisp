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
(include-book "iprefixp")
(include-book "istrprefixp")
(local (include-book "arithmetic"))

(defsection istrpos
  :parents (substrings)
  :short "Case-insensitivly locate the first occurrence of a substring."

  :long "<p>@(call istrpos) is like @(see strpos), but the comparisons are done
in a case insensitive manner.  It returns @('nil') if @('x') never occurs in
@('y'), or returns the index of the first character of the first occurrence
otherwise.</p>

<p>The function is \"efficient\" in the sense that it does not coerce its
arguments into lists, but rather traverses both strings with @(see char).  On
the other hand, it is a naive string search which operates by repeatedly
calling @(see istrprefixp) rather than some better algorithm.</p>

<p>The \"soundness\" and \"completness\" of strpos are established in the
theorems @('iprefixp-of-istrpos') and @('completeness-of-istrpos').</p>"

  (defund istrpos-impl (x y n xl yl)
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
                    :measure (nfix (- (nfix yl) (nfix n)))))
    (cond ((mbe :logic (iprefixp (explode x)
                                 (nthcdr n (explode y)))
                :exec (istrprefixp-impl (the string x)
                                        (the string y)
                                        (the (integer 0 *) 0)
                                        (the (integer 0 *) n)
                                        (the (integer 0 *) xl)
                                        (the (integer 0 *) yl)))
           (lnfix n))
          ((mbe :logic (zp (- (nfix yl) (nfix n)))
                :exec (int= n yl))
           nil)
          (t
           (istrpos-impl (the string x)
                         (the string y)
                         (the (integer 0 *) (+ 1 (the (integer 0 *) (lnfix n))))
                         (the (integer 0 *) xl)
                         (the (integer 0 *) yl)))))

  (definlined istrpos (x y)
    (declare (type string x y))
    (let* ((xl (mbe :logic (len (explode x))
                    :exec (length (the string x))))
           (yl (mbe :logic (len (explode y))
                    :exec (length (the string y)))))
      (declare (type (integer 0 *) xl yl))
      (istrpos-impl (the string x)
                    (the string y)
                    (the (integer 0 *) 0)
                    xl
                    yl)))

  (local (in-theory (enable istrpos istrpos-impl)))

  (defthm istrpos-type
    (or (and (integerp (istrpos x y))
             (<= 0 (istrpos x y)))
        (not (istrpos x y)))
    :rule-classes :type-prescription)

  (encapsulate
    ()
    (local (defthm lemma
             (implies (and (istrpos-impl x y n xl yl)
                           (natp xl)
                           (natp yl)
                           (natp n)
                           ;; (<= n (len (explode y)))
                           (= xl (len (explode x)))
                           (= yl (len (explode y))))
                      (iprefixp (explode x)
                                (nthcdr (istrpos-impl x y n xl yl)
                                        (explode y))))
             :hints(("Goal" :induct (istrpos-impl x y n xl yl)))))

    (defthm iprefixp-of-istrpos
      (implies (istrpos x y)
               (iprefixp (explode x)
                         (nthcdr (istrpos x y) (explode y))))))

  (encapsulate
    ()
    (local (defun my-induction (x y n m xl yl)
             (declare (xargs :measure (nfix (- (nfix yl) (nfix n)))))
             (cond ((iprefixp (explode x)
                              (nthcdr n (explode y)))
                    nil)
                   ((zp (- (nfix yl) (nfix n)))
                    (list x y n m xl yl))
                   (t
                    (my-induction x y
                                  (+ (nfix n) 1)
                                  (if (= (nfix n) (nfix m))
                                      (+ (nfix m) 1)
                                    (nfix m))
                                  xl yl)))))

    (local (defthm lemma
             (implies (and (iprefixp (explode x)
                                     (nthcdr m (explode y)))
                           (natp xl)
                           (natp yl)
                           (natp n)
                           (natp m)
                           (<= n (nfix m))
                           ;; (<= n (len (explode y)))
                           (= xl (len (explode x)))
                           (= yl (len (explode y))))
                      (and (natp (istrpos-impl x y n xl yl))
                           (<= (istrpos-impl x y n xl yl) m)))
             :hints(("Goal"
                     :induct (my-induction x y n m xl yl)
                     :do-not '(generalize fertilize)))))

    (defthm completeness-of-istrpos
      (implies (and (iprefixp (explode x)
                              (nthcdr m (explode y)))
                    (force (natp m)))
               (and (natp (istrpos x y))
                    (<= (istrpos x y) m)))))

  (defcong istreqv equal (istrpos-impl x y n xl yl) 1)
  (defcong istreqv equal (istrpos-impl x y n xl yl) 2)

  (local (in-theory (disable istreqv)))

  (defcong istreqv equal (istrpos x y) 1)
  (defcong istreqv equal (istrpos x y) 2))

