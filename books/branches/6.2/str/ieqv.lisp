; ACL2 String Library
; Copyright (C) 2009-2010 Centaur Technology
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

(in-package "STR")
(include-book "char-case")
(include-book "std/lists/list-defuns" :dir :system)
(local (include-book "std/lists/nthcdr" :dir :system))
(local (include-book "arithmetic"))

(defsection ichareqv
  :parents (equivalences)
  :short "Case-insensitive character equivalence test."
  :long "<p>@(call ichareqv) determines if @('x') and @('y') are equivalent
when interpreted as characters without regard to case.  For instance,
upper-case C is equivalent to lower-case c under this relation.</p>

<p>ACL2 has a built-in version of this function, @(see char-equal), but it is
irritating to use because it has @(see standard-char-p) guards.  In contrast,
@('ichareqv') works on arbitrary characters, with some loss of efficiency.</p>"

  (definlined ichareqv (x y)
    (declare (type character x)
             (type character y))
    (equal (downcase-char x) (downcase-char y)))

  (local (in-theory (enable ichareqv)))

  (defequiv ichareqv)

  (defrefinement chareqv ichareqv))



(defsection icharlisteqv
  :parents (equivalences)
  :short "Case-insensitive character-list equivalence test."

  :long "<p>@(call icharlisteqv) determines if @('x') and @('y') are
case-insensitively equivalent character lists.  That is, @('x') and @('y') must
have the same length and their elements must be @(see ichareqv) to one
another.</p>

<p>See also @(see charlisteqv) for a case-sensitive alternative.</p>"

  (defund icharlisteqv (x y)
    (declare (xargs :guard (and (character-listp x)
                                (character-listp y))))

    (if (consp x)
        (and (consp y)
             (ichareqv (car x) (car y))
             (icharlisteqv (cdr x) (cdr y)))
      (atom y)))

  (local (in-theory (enable icharlisteqv)))

  (defequiv icharlisteqv)

  (defrefinement charlisteqv icharlisteqv
    :hints(("Goal" :in-theory (enable chareqv))))

  (defcong icharlisteqv ichareqv     (car x)      1)
  (defcong icharlisteqv icharlisteqv (cdr x)      1)
  (defcong ichareqv     icharlisteqv (cons a x)   1)
  (defcong icharlisteqv icharlisteqv (cons a x)   2)
  (defcong icharlisteqv equal        (len x)      1)
  (defcong icharlisteqv icharlisteqv (list-fix x) 1)
  (defcong icharlisteqv ichareqv     (nth n x)    2)
  (defcong icharlisteqv icharlisteqv (nthcdr n x) 2)
  (defcong icharlisteqv icharlisteqv (append x y) 1)
  (defcong icharlisteqv icharlisteqv (append x y) 2)
  (defcong icharlisteqv icharlisteqv (acl2::rev x) 1)
  (defcong icharlisteqv icharlisteqv (revappend x y) 2)
  (defcong icharlisteqv icharlisteqv (revappend x y) 1)

  (defthm icharlisteqv-when-not-consp-left
    (implies (not (consp x))
             (equal (icharlisteqv x y)
                    (atom y))))

  (defthm icharlisteqv-when-not-consp-right
    (implies (not (consp y))
             (equal (icharlisteqv x y)
                    (atom x))))

  (defthm icharlisteqv-of-cons-right
    (equal (icharlisteqv x (cons a y))
           (and (consp x)
                (ichareqv (car x) (double-rewrite a))
                (icharlisteqv (cdr x) (double-rewrite y)))))

  (defthm icharlisteqv-of-cons-left
    (equal (icharlisteqv (cons a x) y)
           (and (consp y)
                (ichareqv (double-rewrite a) (car y))
                (icharlisteqv (double-rewrite x) (cdr y)))))

  (defthm icharlisteqv-when-not-same-lens
    (implies (not (equal (len x) (len y)))
             (not (icharlisteqv x y)))))



(defsection istreqv
  :parents (equivalences)
  :short "Case-insensitive string equivalence test."

  :long "<p>@(call istreqv) determines if @('x') and @('y') are
case-insensitively equivalent strings.  That is, @('x') and @('y') must have
the same length and their elements must be @(see ichareqv) to one another.</p>

<p>Logically this is identical to</p>

@({
 (icharlisteqv (coerce x 'list) (coerce y 'list))
})

<p>But we use a more efficient implementation which avoids coercing the
strings into lists.</p>

<p>NOTE: for reasoning, we leave this function enabled and prefer to work with
@(see icharlisteqv) of the coerces as our normal form.</p>"

  (defund istreqv-aux (x y n l)
    (declare (type string x)
             (type string y)
             (type (integer 0 *) n)
             (type (integer 0 *) l)
             (xargs :guard (and (natp n)
                                (natp l)
                                (equal (length x) l)
                                (equal (length y) l)
                                (<= n l))
                    :measure (nfix (- (nfix l) (nfix n)))
                    :guard-hints (("Goal" :in-theory (enable ichareqv)))))
    (mbe :logic
         (if (zp (- (nfix l) (nfix n)))
             t
           (and (ichareqv (char x n) (char y n))
                (istreqv-aux x y (+ (nfix n) 1) l)))
         :exec
         (if (eql n l)
             t
           (and (ichareqv (the character (char x n))
                          (the character (char y n)))
                (istreqv-aux x y
                             (the (integer 0 *) (+ 1 n))
                             l)))))

  (definline istreqv (x y)
    (declare (type string x)
             (type string y)
             (xargs :verify-guards nil))
    (mbe :logic
         (icharlisteqv (coerce x 'list) (coerce y 'list))
         :exec
         (b* (((the (integer 0 *) xl) (length x))
              ((the (integer 0 *) yl) (length y)))
           (and (eql xl yl)
                (istreqv-aux x y 0 xl)))))

  (local (defthm lemma
           (implies (and (< n (len x))
                         (not (ichareqv (nth n x) (nth n y))))
                    (not (icharlisteqv (nthcdr n x) (nthcdr n y))))))

  (local (defthm lemma2
           (implies (and (< n (len x))
                         (equal (len x) (len y))
                         (ichareqv (nth n x) (nth n y)))
                    (equal (icharlisteqv (nthcdr n x) (nthcdr n y))
                           (icharlisteqv (cdr (nthcdr n x)) (cdr (nthcdr n y)))))))

  (defthm istreqv-aux-removal
    (implies (and (stringp x)
                  (stringp y)
                  (natp n)
                  (<= n l)
                  (= l (length x))
                  (= l (length y)))
             (equal (istreqv-aux x y n l)
                    (icharlisteqv (nthcdr n (coerce x 'list))
                                  (nthcdr n (coerce y 'list)))))
    :hints(("Goal"
            :in-theory (enable istreqv-aux)
            :induct (istreqv-aux x y n l))))

  (verify-guards istreqv$inline))
