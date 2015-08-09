; Lemmas about remove
; Copyright (C) 2013 Kookamara LLC
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

(in-package "ACL2")
(include-book "xdoc/top" :dir :system)
(include-book "list-defuns")
(include-book "abstract")
(local (include-book "duplicity"))
(local (include-book "append"))
(local (include-book "sets"))

(defsection std/lists/remove
  :parents (std/lists remove)
  :short "Lemmas about @(see remove) available in the @(see std/lists)
library."

  (defthm remove-when-atom
    (implies (atom x)
             (equal (remove a x)
                    nil)))

  (defthm remove-of-cons
    (equal (remove a (cons b x))
           (if (equal a b)
               (remove a x)
             (cons b (remove a x)))))

  (defthm consp-of-remove
    ;; BOZO consider all-equalp or similar instead?
    (equal (consp (remove a x))
           (not (subsetp x (list a)))))

  (defthm remove-under-iff
    (iff (remove a x)
         (not (subsetp x (list a)))))

  (defthm remove-when-non-member
    (implies (not (member a x))
             (equal (remove a x)
                    (list-fix x))))

  (defthm upper-bound-of-len-of-remove-weak
    (<= (len (remove a x))
        (len x))
    :rule-classes ((:rewrite) (:linear)))

  (defthm upper-bound-of-len-of-remove-strong
    (implies (member a x)
             (< (len (remove a x))
                (len x)))
    :rule-classes :linear)

  (defthm len-of-remove-exact
    ;; May not always be desirable, but leave it enabled by default; if someone
    ;; disables this, they will still have at least the basic upper bound
    ;; theorems above.
    (equal (len (remove a x))
           (- (len x) (duplicity a x))))

  (defthm remove-is-commutative
    (equal (remove b (remove a x))
           (remove a (remove b x))))

  (defthm remove-is-idempotent
    (equal (remove a (remove a x))
           (remove a x)))

  (defthm duplicity-of-remove
    (equal (duplicity a (remove b x))
           (if (equal a b)
               0
             (duplicity a x))))

  ;; Note: proved elsewhere in std:

  ;; (defcong list-equiv equal (remove a x) 2)
  ;; (defcong set-equiv set-equiv (remove a x) 2)

  ;; (defthm member-of-remove
  ;;   (iff (member a (remove b x))
  ;;        (and (member a x)
  ;;             (not (equal a b)))))

  ;; (defthm subsetp-of-remove1
  ;;   (equal (subsetp x (remove a y))
  ;;          (and (subsetp x y)
  ;;               (not (member a x)))))

  ;; (defthm subsetp-of-remove2
  ;;   (implies (subsetp x y)
  ;;            (subsetp (remove a x) y))))

  (defthm remove-of-append
    (equal (remove a (append x y))
           (append (remove a x)
                   (remove a y))))

  (defthm remove-of-revappend
    (equal (remove a (revappend x y))
           (revappend (remove a x)
                      (remove a y))))

  (defthm remove-of-rev
    (equal (remove a (rev x))
           (rev (remove a x))))

  (defthm remove-of-union-equal
    (equal (remove a (union-equal x y))
           (union-equal (remove a x)
                        (remove a y))))

  (defthm remove-of-intersection-equal
    (equal (remove a (intersection-equal x y))
           (intersection-equal (remove a x)
                               (remove a y))))

  (defthm remove-of-set-difference-equal
    (equal (remove a (set-difference-equal x y))
           (set-difference-equal (remove a x) y)))

  (def-listp-rule element-list-p-of-remove
    (implies (element-list-p x)
             (element-list-p (remove a x)))))





