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
(include-book "xdoc/top" :dir :system)
(include-book "../lists/list-defuns")

(local (defthm list-fix-when-true-listp
         (implies (true-listp x)
                  (equal (list-fix x) x))
         :hints(("Goal" :in-theory (enable list-fix)))))

(local (defthm append-of-nil
         (equal (append x nil) (list-fix x))
         :hints(("Goal" :in-theory (enable list-fix)))))

(local (defthm associativity-of-append
         (equal (append (append x y) z)
                (append x (append y z)))))

(local
 (encapsulate
   ()
   (local (defthm l0
            (equal (append (append rv (list x1)) y)
                   (append rv (cons x1 y)))))

   (defthm revappend-removal
     (equal (revappend x y) (append (rev x) y))
     :hints(("Goal" :in-theory (enable rev))))))

(local (defthm rev-of-append
         (equal (rev (append x y))
                (append (rev y) (rev x)))
         :hints(("Goal" :in-theory (enable rev)))))

(local (defthm rev-of-rev
         (equal (rev (rev x))
                (list-fix x))
         :hints(("Goal" :in-theory (enable rev list-fix)))))

(defsection append-alist-keys-exec
  :parents (append-alist-keys)
  :short "Tail-recursive implementation of @(see append-alist-keys)."
  :long "<p>This is used in the implementation of @('append-alist-keys').  You
should never need to reason about this @('-exec') function directly, thanks to
the following rule:</p>

@(def append-alist-keys-exec-removal)"

;; BOZO consider switching this to use nrev.

  (defund append-alist-keys-exec (x acc)
    (declare (xargs :guard t))
    (mbe :logic
         (if (atom x)
             acc
           (append-alist-keys-exec (cdr x)
                                   (revappend (caar x) acc)))
         :exec
         ;; Tweaks to allow for a guard of T
         (cond ((atom x)
                acc)
               ((atom (car x))
                (append-alist-keys-exec (cdr x) acc))
               (t
                (append-alist-keys-exec (cdr x)
                                        (revappend-without-guard (caar x) acc)))))))


(defsection append-alist-keys
  :parents (std/alists)
  :short "@(call append-alist-keys) appends all of the values from the alist
@('x') into a single list."

  :long "<p>Our guard is merely @('t'), but typically @('x') should be an alist
of @('(key . value)') pairs where every @('value') is a list of elements.  We
walk through the alist, appending together all of the elements of each
@('value') into a single, flat list.</p>

<p>Note that we do not really treat @('x') as an association list.  That is, we
will include the values from any \"shadowed pairs\" in the list.</p>"

  (defund append-alist-keys (x)
    (declare (xargs :guard t
                    :verify-guards nil))
    (mbe :logic
         (if (atom x)
             nil
           (append (caar x) (append-alist-keys (cdr x))))
         :exec
         (reverse (append-alist-keys-exec x nil))))

  (local (in-theory (enable append-alist-keys-exec
                            append-alist-keys)))

  (local (defthm true-listp-of-append-alist-keys-exec
           (implies (true-listp acc)
                    (true-listp (append-alist-keys-exec x acc)))
           :rule-classes :type-prescription))

  (local (in-theory (enable append-alist-keys)))

  (defthm append-alist-keys-exec-removal
    (equal (append-alist-keys-exec x acc)
           (revappend (append-alist-keys x) acc))
    :hints(("Goal" :induct (append-alist-keys-exec x acc))))

  (verify-guards append-alist-keys)

  (defthm append-alist-keys-when-atom
    (implies (atom x)
             (equal (append-alist-keys x)
                    nil)))

  (defthm append-alist-keys-of-cons
    (equal (append-alist-keys (cons a x))
           (append (car a) (append-alist-keys x))))

  (in-theory (disable (:type-prescription append-alist-keys)))

  (defthm true-listp-of-append-alist-keys
    (true-listp (append-alist-keys x))
    :rule-classes :type-prescription)

  (defthm append-alist-keys-of-append
    (equal (append-alist-keys (append x y))
           (append (append-alist-keys x)
                   (append-alist-keys y))))

  (local (defthm append-alist-keys-of-list-fix
           (equal (append-alist-keys (list-fix x))
                  (append-alist-keys x))
           :hints(("Goal" :in-theory (enable list-fix)))))

  (defcong list-equiv equal (append-alist-keys x) 1
    :hints(("Goal"
            :in-theory (e/d (list-equiv)
                            (append-alist-keys-of-list-fix))
            :use ((:instance append-alist-keys-of-list-fix (x x))
                  (:instance append-alist-keys-of-list-fix (x x-equiv)))))))


