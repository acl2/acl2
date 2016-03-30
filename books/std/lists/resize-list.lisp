; Resize List Lemmas
; Copyright (C) 2008-2013 Centaur Technology
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
; Original authors: Sol Swords <sswords@centtech.com>
;                   Jared Davis <jared@centtech.com>

(in-package "ACL2")
(include-book "list-defuns")
(include-book "xdoc/top" :dir :system)
(local (include-book "repeat"))
(local (include-book "nth"))

(defsection std/lists/resize-list
  :parents (std/lists resize-list)
  :short "Lemmas about @(see resize-list) available in the @(see std/lists)
library."

  "<h4>Trivial reductions</h4>"

  (defthm resize-list-when-zp
    (implies (zp n)
             (equal (resize-list lst n default-value)
                    nil)))

  (defthm resize-list-of-nfix
    (equal (resize-list lst (nfix n) default-value)
           (resize-list lst n default-value)))

  (defthm resize-list-when-atom
    (implies (atom lst)
             (equal (resize-list lst n default-value)
                    (repeat n default-value)))
    :hints(("Goal" :in-theory (enable repeat))))

  "<h4>Relation with other basic list functions</h4>"

  (local (defun my-induct (n m lst)
           (if (zp n)
               (list lst)
             (if (zp m)
                 nil
               (my-induct (- n 1) (- m 1)
                          (if (atom lst)
                              lst
                            (cdr lst)))))))

  (defthm nth-of-resize-list
    (equal (nth n (resize-list lst m default-value))
           (let ((n (nfix n))
                 (m (nfix m)))
             (and (< n m)
                  (if (< n (len lst))
                      (nth n lst)
                    default-value))))
    :hints(("Goal"
            :expand (resize-list lst m default-value)
            :induct (my-induct n m lst))))

  (defthm len-of-resize-list
    (equal (len (resize-list lst n default))
           (nfix n)))

  (defthm resize-list-of-len-free
    (implies (equal (nfix n) (len lst))
             (equal (resize-list lst n default-value)
                    (list-fix lst))))

  (defthm equal-of-resize-list-and-self
    (equal (equal (resize-list lst n default-value) lst)
           (and (true-listp lst)
                (equal (len lst) (nfix n))))))

