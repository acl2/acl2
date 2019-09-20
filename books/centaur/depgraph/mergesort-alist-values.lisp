; VL Verilog Toolkit
; Copyright (C) 2008-2011 Centaur Technology
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

(in-package "DEPGRAPH")
(include-book "std/util/define" :dir :system)
(include-book "std/alists/alist-defuns" :dir :system)
(include-book "std/osets/top" :dir :system)
(local (include-book "std/alists/top" :dir :system))


(define mergesort-alist-values (x)
  :parents (depgraph)
  :short "Sort all of the values bound in an alist."
  (b* (((when (atom x))
        nil)
       ((when (atom (car x)))
        ;; Bad alist convention
        (mergesort-alist-values (cdr x))))
    (cons (cons (caar x)
                (mergesort (cdar x)))
          (mergesort-alist-values (cdr x))))
  ///
  (defthm mergesort-alist-values-when-atom
    (implies (atom x)
             (equal (mergesort-alist-values x)
                    nil)))

  (defthm mergesort-alist-values-of-cons
    (equal (mergesort-alist-values (cons a x))
           (if (atom a)
               (mergesort-alist-values x)
             (cons (cons (car a)
                         (mergesort (cdr a)))
                   (mergesort-alist-values x)))))

  (defthm alistp-of-mergesort-alist-values
    (alistp (mergesort-alist-values x)))

  (defthm hons-assoc-equal-of-mergesort-alist-values
    (equal (hons-assoc-equal key (mergesort-alist-values x))
           (let ((look (hons-assoc-equal key x)))
             (and look
                  (cons (car look) (mergesort (cdr look)))))))

  (defthm alist-keys-of-mergesort-alist-values
    (equal (alist-keys (mergesort-alist-values x))
           (alist-keys x)))

  (encapsulate
    ()
    (local (defthm l0
             (equal (mergesort-alist-values (acl2::list-fix x))
                    (mergesort-alist-values x))
             :hints(("Goal" :induct (len x)))))

    (defcong acl2::list-equiv equal (mergesort-alist-values x) 1
      :hints(("Goal"
              :in-theory (e/d (acl2::list-equiv) (l0))
              :use ((:instance l0 (x x))
                    (:instance l0 (x x-equiv)))))))

  (encapsulate
    ()
    (local (defthm l0
             (implies (acl2::alists-agree keys x y)
                      (acl2::alists-agree keys
                                          (mergesort-alist-values x)
                                          (mergesort-alist-values y)))
             :hints(("Goal" :in-theory (enable acl2::alists-agree)))))

    (local (defthm l1
             (implies (acl2::sub-alistp x y)
                      (acl2::sub-alistp (mergesort-alist-values x)
                                        (mergesort-alist-values y)))
             :hints(("Goal" :in-theory (enable acl2::sub-alistp)))))

    (defcong acl2::alist-equiv acl2::alist-equiv (mergesort-alist-values x) 1
      :hints(("Goal" :in-theory (enable acl2::alist-equiv))))))



(define alist-values-are-sets-p (x)
  :parents (depgraph)
  :short "Recognizer for alists whose every value is an ordered set."
  (b* (((when (atom x))
        t)
       ((when (atom (car x)))
        ;; Non-alist convention
        (alist-values-are-sets-p (cdr x))))
    (and (setp (cdar x))
         (alist-values-are-sets-p (cdr x))))
  ///
  (defthm alist-values-are-sets-p-when-atom
    (implies (not (consp x))
             (equal (alist-values-are-sets-p x)
                    t)))

  (defthm alist-values-are-sets-p-of-cons
    (equal (alist-values-are-sets-p (cons a x))
           ;; Goofy, don't need to check consp because if it's an atom, then
           ;; its cdr is NIL, which is a fine set.
           (and (setp (cdr a))
                (alist-values-are-sets-p x))))

  (defthm setp-of-lookup-when-alist-values-are-sets-p
    (implies (alist-values-are-sets-p x)
             (setp (cdr (hons-assoc-equal a x)))))

  (defthm alist-values-are-sets-p-of-hons-shrink-alist
    (implies (and (alist-values-are-sets-p x)
                  (alist-values-are-sets-p ans))
             (alist-values-are-sets-p (hons-shrink-alist x ans))))

  (defthm alist-values-are-sets-p-of-mergesort-alist-values
    (alist-values-are-sets-p (mergesort-alist-values x))
    :hints(("Goal" :induct (len x))))

  (encapsulate
    ()
    (local (defthm l0
             (equal (alist-values-are-sets-p (acl2::list-fix x))
                    (alist-values-are-sets-p x))
             :hints(("Goal" :induct (len x)))))

    (defcong acl2::list-equiv equal (alist-values-are-sets-p x) 1
      :hints(("Goal"
              :in-theory (e/d (acl2::list-equiv) (l0))
              :use ((:instance l0 (x x))
                    (:instance l0 (x x-equiv)))))))

  ;; BOZO prove alist-equiv congruence
  )

