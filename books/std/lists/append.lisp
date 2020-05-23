; Append lemmas
; Copyright (C) 2005-2013 Kookamara LLC
;
; Contact:
;
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759, USA
;   http://www.kookamara.com/
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
; Original author: Jared Davis <jared@kookamara.com>
;
; append.lisp
; This file was originally part of the Unicode library.

(in-package "ACL2")
(include-book "list-fix")
(local (include-book "std/basic/inductions" :dir :system))


(defsection std/lists/append
  :parents (std/lists append)
  :short "Lemmas about @(see append) available in the @(see std/lists)
library."

  (local (defthm len-when-consp
           (implies (consp x)
                    (< 0 (len x)))
           :rule-classes ((:linear) (:rewrite))))

  (defthm append-when-not-consp
    (implies (not (consp x))
             (equal (append x y)
                    y)))

  (defthm append-of-cons
    (equal (append (cons a x) y)
           (cons a (append x y))))

  (defthm true-listp-of-append
    (equal (true-listp (append x y))
           (true-listp y)))

  (defthm consp-of-append
    ;; Note that data-structures/list-defthms has a similar rule, except that
    ;; it adds two type-prescription corollaries.  I found these corollaries to
    ;; be expensive, so I don't bother with them.
    (equal (consp (append x y))
           (or (consp x)
               (consp y))))

  (defthm append-under-iff
    (iff (append x y)
         (or (consp x)
             y)))

  (defthm len-of-append
    (equal (len (append x y))
           (+ (len x) (len y))))

  ;; (defthm nth-of-append
  ;;   (equal (nth n (append x y))
  ;;          (if (< (nfix n) (len x))
  ;;              (nth n x)
  ;;            (nth (- n (len x)) y))))

  (defthm equal-when-append-same
    (equal (equal (append x y1)
                  (append x y2))
           (equal y1 y2)))

  (local (defthm append-nonempty-list
           (implies (consp x)
                    (not (equal (append x y) y)))
           :hints(("Goal" :use ((:instance len (x (append x y)))
                                (:instance len (x y)))))))

  (defthm equal-of-append-and-append-same-arg2
    (equal (equal (append x1 y) (append x2 y))
           (equal (true-list-fix x1) (true-list-fix x2)))
    :hints(("Goal" :induct (cdr-cdr-induct x1 x2))))

  (defthm append-of-nil
    (equal (append x nil)
           (list-fix x)))

  ;; Disable this built-in ACL2 rule since append-of-nil is stronger.
  (in-theory (disable append-to-nil))

  (defthm list-fix-of-append
    (equal (list-fix (append x y))
           (append x (list-fix y))))

  (defthm car-of-append
    (equal (car (append x y))
           (if (consp x)
               (car x)
             (car y))))

  (defthmd car-of-append-when-consp
    (implies (consp x)
             (equal (car (append x y))
                    (car x))))

  (theory-invariant (incompatible (:rewrite car-of-append-when-consp)
                                  (:rewrite car-of-append))
                    :key car-of-append-consp-invariant
                    :error t)

  (defthmd cdr-of-append
    (equal (cdr (append x y))
           (if (consp x)
               (append (cdr x) y)
             (cdr y))))

  (defthm cdr-of-append-when-consp
; We enable the version that requires consp, because it's less likely we want
; to unconditionally open-up (cdr (append ...)) unless we know ... is a consp.
    (implies (consp x)
             (equal (cdr (append x y))
                    (append (cdr x) y))))

  (theory-invariant (incompatible (:rewrite cdr-of-append-when-consp)
                                  (:rewrite cdr-of-append))
                    :key cdr-of-append-consp-invariant
                    :error t)

  (defthm associativity-of-append
    (equal (append (append a b) c)
           (append a (append b c))))

  (defcong element-list-equiv element-list-equiv (append a b) 1)
  (table listfix-rules 'element-list-equiv-implies-element-list-equiv-append-1 t)
  (defcong element-list-equiv element-list-equiv (append a b) 2)
  (table listfix-rules 'element-list-equiv-implies-element-list-equiv-append-2 t)

  (def-listp-rule element-list-p-of-append-true-list
    (equal (element-list-p (append a b))
           (and (element-list-p (list-fix a))
                (element-list-p b)))
    :requirement true-listp
    :name element-list-p-of-append))
