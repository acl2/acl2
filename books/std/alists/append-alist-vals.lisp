; Standard Association Lists Library
; Copyright (C) 2013-2014 Centaur Technology
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

(in-package "ACL2")
(include-book "../lists/list-defuns")
(local (include-book "../lists/append"))
(local (include-book "../lists/revappend"))
(local (include-book "../lists/rev"))


(defsection append-alist-vals-exec
  :parents (append-alist-vals)
  :short "Tail-recursive implementation of @(see append-alist-vals)."
  :long "<p>This is used in the implementation of @('append-alist-vals').  You
should never need to reason about this @('-exec') function directly, thanks to
the following rule:</p>

@(def append-alist-vals-exec-removal)"

;; BOZO consider switching this to use nrev.

  (defund append-alist-vals-exec (x acc)
    (declare (xargs :guard t))
    (mbe :logic
         (if (atom x)
             acc
           (append-alist-vals-exec (cdr x)
                                   (revappend (cdar x) acc)))
         :exec
         ;; Tweaks to allow for a guard of T
         (cond ((atom x)
                acc)
               ((atom (car x))
                (append-alist-vals-exec (cdr x) acc))
               (t
                (append-alist-vals-exec (cdr x)
                                        (revappend-without-guard (cdar x) acc)))))))



(defsection append-alist-vals
  :parents (std/alists)
  :short "@(call append-alist-vals) appends all of the values from the alist
@('x') into a single list."

  :long "<p>Our guard is merely @('t'), but typically @('x') should be an alist
of @('(key . value)') pairs where every @('value') is a list of elements.  We
walk through the alist, appending together all of the elements of each
@('value') into a single, flat list.</p>

<p>Note that we do not really treat @('x') as an association list.  That is, we
will include the values from any \"shadowed pairs\" in the list.</p>"

  (defund append-alist-vals (x)
    (declare (xargs :guard t
                    :verify-guards nil))
    (mbe :logic
         (if (atom x)
             nil
           (append (cdar x) (append-alist-vals (cdr x))))
         :exec
         (reverse (append-alist-vals-exec x nil))))

  (local (in-theory (enable append-alist-vals-exec
                            append-alist-vals)))

  (local (defthm true-listp-of-append-alist-vals-exec
           (implies (true-listp acc)
                    (true-listp (append-alist-vals-exec x acc)))
           :rule-classes :type-prescription))

  (local (in-theory (enable append-alist-vals)))

  (defthm append-alist-vals-exec-removal
    (equal (append-alist-vals-exec x acc)
           (revappend (append-alist-vals x) acc))
    :hints(("Goal" :induct (append-alist-vals-exec x acc))))

  (verify-guards append-alist-vals)

  (defthm append-alist-vals-when-atom
    (implies (atom x)
             (equal (append-alist-vals x)
                    nil)))

  (defthm append-alist-vals-of-cons
    (equal (append-alist-vals (cons a x))
           (append (cdr a) (append-alist-vals x))))

  (in-theory (disable (:type-prescription append-alist-vals)))

  (defthm true-listp-of-append-alist-vals
    (true-listp (append-alist-vals x))
    :rule-classes :type-prescription)

  (defthm append-alist-vals-of-append
    (equal (append-alist-vals (append x y))
           (append (append-alist-vals x)
                   (append-alist-vals y))))

  (local (defthm append-alist-vals-of-list-fix
           (equal (append-alist-vals (list-fix x))
                  (append-alist-vals x))))

  (defcong list-equiv equal (append-alist-vals x) 1
    :hints(("Goal"
            :in-theory (e/d (list-equiv)
                            (append-alist-vals-of-list-fix))
            :use ((:instance append-alist-vals-of-list-fix (x x))
                  (:instance append-alist-vals-of-list-fix (x x-equiv)))))))


