; Standard Association Lists Library
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
(include-book "alist-keys")
;; (local (include-book "std/lists/sets" :dir :system))

(defsection alist-vals
  :parents (std/alists strip-cdrs)
  :short "@(call alist-vals) collects all values bound in an alist."

  :long "<p>This is a \"modern\" equivalent of @(see strip-cdrs), which
properly respects the non-alist convention; see @(see std/alists) for
discussion of this convention.</p>

<p>Note that the list of values returned by @('alist-vals') may include
\"shadowed\" bindings, as in @('((a . 1) (a . 2))').</p>"

  (defund alist-vals (x)
    (declare (xargs :guard t))
    (cond ((atom x)
           nil)
          ((atom (car x))
           (alist-vals (cdr x)))
          (t
           (cons (cdar x) (alist-vals (cdr x))))))

  (local (in-theory (enable alist-vals)))

  (defthm alist-vals-when-atom
    (implies (atom x)
             (equal (alist-vals x)
                    nil)))

  (defthm alist-vals-of-cons
    (equal (alist-vals (cons a x))
           (if (consp a)
               (cons (cdr a) (alist-vals x))
             (alist-vals x))))

  (encapsulate
    ()
    (local (defthmd l0
             (equal (alist-vals (list-fix x))
                    (alist-vals x))))

    (defcong list-equiv equal (alist-vals x) 1
      :hints(("Goal"
              :use ((:instance l0 (x x))
                    (:instance l0 (x acl2::x-equiv)))))))

  (defthm true-listp-of-alist-vals
    (true-listp (alist-vals x))
    :rule-classes :type-prescription)

  (defthm alist-vals-of-hons-acons
    (equal (alist-vals (hons-acons key val x))
           (cons val (alist-vals x))))

  (defthm alist-vals-of-pairlis$
    (implies (equal (len keys) (len vals))
             (equal (alist-vals (pairlis$ keys vals))
                    (list-fix vals))))

  (defthm len-of-alist-vals
    (equal (len (alist-vals x))
           (len (alist-keys x)))
    :hints(("Goal" :in-theory (enable alist-keys alist-vals))))

  (defthm alist-vals-of-append
    (equal (alist-vals (append x y))
           (append (alist-vals x)
                   (alist-vals y))))

  ;; (defthm alist-vals-of-rev
  ;;   (equal (alist-vals (rev x))
  ;;          (rev (alist-vals x))))

  (defthm alist-vals-of-revappend
    (equal (alist-vals (revappend x y))
           (revappend (alist-vals x)
                      (alist-vals y))))

  (defthm member-equal-of-cdr-when-hons-assoc-equal
    (implies (hons-assoc-equal key map)
             (member-equal (cdr (hons-assoc-equal key map))
                           (alist-vals map)))))
