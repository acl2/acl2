; Reverse Cons
; Copyright (C) 2013 Centaur Technology
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
; Original authors: Jared Davis <jared@centtech.com>
;                   Sol Swords <sswords@centtech.com>

(in-package "ACL2")
(include-book "equiv")
(include-book "rev")
(include-book "append")
(local (include-book "std/basic/inductions" :dir :system))

(defun binary-append-without-guard (x y)
  (declare (xargs :guard t))
  (mbe :logic
       (append x y)
       :exec
       (if (consp x)
           (cons (car x)
                 (binary-append-without-guard (cdr x) y))
         y)))

(defmacro append-without-guard (x y &rest rst)
  (xxxjoin 'binary-append-without-guard (list* x y rst)))


(defsection rcons
  :parents (std/lists)
  :short "Cons onto the back of a list."
  :long "<p>@(call rcons) is like @(see cons), except that instead of putting
@('a') onto front of the list @('x'), it puts it at the end.  To borrow ML
notation, we compute @('x@[a]') instead of @('a::x').  This is obviously quite
inefficient: we have to copy the whole list just to add one element!</p>"

  (defund rcons (a x)
    (declare (xargs :guard t))
    (append-without-guard x (list a)))

  (in-theory (disable (:type-prescription rcons)))
  (local (in-theory (enable rcons)))

  (defthm type-of-rcons
    (and (consp (rcons a x))
         (true-listp (rcons a x)))
    :rule-classes :type-prescription)

  (defthm rcons-of-list-fix
    (equal (rcons a (list-fix x))
           (rcons a x)))

  (defcong list-equiv equal (rcons a x) 2)

  (local (defthm l0
           (equal (list-equiv (cons a x) y)
                  (and (consp y)
                       (equal (car y) a)
                       (list-equiv x (cdr y))))))

  (defthm list-equiv-of-rcons-and-rcons
    (equal (list-equiv (rcons a x) (rcons a y))
           (list-equiv x y))
    :hints(("Goal"
            :induct (acl2::cdr-cdr-induct x y))))

  (defthm len-of-rcons
    (equal (len (rcons a x))
           (+ 1 (len x))))

  (defthm rev-of-rcons
    (equal (rev (rcons a x))
           (cons a (rev x))))

  (defthm append-of-rcons
    (equal (append (rcons a x) y)
           (append x (cons a y))))

  (defthm rcons-of-append
    (equal (rcons a (append x y))
           (append x (rcons a y))))

  (defthm revappend-of-rcons
    (equal (revappend (rcons a x) y)
           (cons a (revappend x y)))))


