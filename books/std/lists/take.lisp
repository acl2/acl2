; Take lemmas
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
; Contributing author: Alessandro Coglio <coglio@kestrel.edu>
;
; take.lisp
; This file was originally part of the Unicode library.

(in-package "ACL2")

(include-book "list-fix")
(include-book "equiv")
(local (include-book "std/basic/inductions" :dir :system))
;; Mihir M. mod: The sets book is included to help with
;; no-duplicatesp-of-take; and the definitions repeat, take-of-too-many, and
;; subsetp-of-repeat from the repeat book are introduced prematurely in order
;; to prove subsetp-of-take.
(local (include-book "std/lists/sets" :dir :system))

(local (defun repeat (n x)
         (if (zp n)
             nil
           (cons x (repeat (- n 1) x)))))

(local
 (defthm take-of-too-many
   (implies (<= (len x) (nfix n))
            (equal (take n x)
                   (append x (repeat (- (nfix n) (len x)) nil))))))

(local
 (defthm subsetp-of-repeat
   (iff (subsetp-equal (repeat n x) y)
        (or (zp n) (member-equal x y)))
   :hints (("goal" :in-theory (enable subsetp-equal repeat)))))

(defsection std/lists/take
  :parents (std/lists take)
  :short "Lemmas about @(see take) available in the @(see std/lists) library."

  (defthm consp-of-take
    (equal (consp (take n xs))
           (not (zp n))))

  (defthm take-under-iff
    (iff (take n xs)
         (not (zp n))))

  (defthm len-of-take
    (equal (len (take n xs))
           (nfix n)))

  (defthm take-of-cons
    (equal (take n (cons a x))
           (if (zp n)
               nil
             (cons a (take (1- n) x)))))

  (defthm take-of-append
    (equal (take n (append x y))
           (if (< (nfix n) (len x))
               (take n x)
             (append x (take (- n (len x)) y))))
    :hints(("Goal" :induct (take n x))))

  (defthm take-of-zero
    (equal (take 0 x)
           nil))

  (defthm take-of-1
    (equal (take 1 x)
           (list (car x))))

  (defthm car-of-take
    (implies (<= 1 (nfix n))
             (equal (car (take n x))
                    (car x))))

  (defthm second-of-take
    (implies (<= 2 (nfix n))
             (equal (second (take n x))
                    (second x))))

  (defthm third-of-take
    (implies (<= 3 (nfix n))
             (equal (third (take n x))
                    (third x))))

  (defthm fourth-of-take
    (implies (<= 4 (nfix n))
             (equal (fourth (take n x))
                    (fourth x))))

  (defthm take-of-len-free
    (implies (equal len (len x))
             (equal (take len x)
                    (list-fix x))))

  (defthm equal-of-take-and-list-fix
    (equal (equal (take n x) (list-fix x))
           (equal (len x) (nfix n))))

  (defthm take-of-len
    (equal (take (len x) x)
           (list-fix x)))

  (defthm subsetp-of-take
    (iff (subsetp (take n x) x)
         (or (<= (nfix n) (len x))
             (member-equal nil x)))
    :hints (("goal" :induct (mv (member-equal nil x) (take n x)))))

  (defthm take-fewer-of-take-more
    ;; Note: see also repeat.lisp for related cases and a stronger rule that
    ;; case-splits.
    (implies (<= (nfix a) (nfix b))
             (equal (take a (take b x))
                    (take a x))))

  (defthm take-of-take-same
    ;; Note: see also repeat.lisp for related cases and a stronger rule that
    ;; case-splits.
    (equal (take a (take a x))
           (take a x)))

  (defthm no-duplicatesp-of-take
    (implies (and (no-duplicatesp-equal l)
                  (<= (nfix n) (len l)))
             (no-duplicatesp-equal (take n l))))

  ;; Mihir M. mod: this lemma is useful in a few different places when
  ;; reasoning about take, decrementing n but keeping l the same.
  (defthmd take-as-append-and-nth
    (equal (take n l) (if (zp n)
                          nil
                        (append (take (- n 1) l) (list (nth (- n 1) l)))))
    :rule-classes :definition)

  (theory-invariant (incompatible (:rewrite take-as-append-and-nth) (:definition take)))

  (defcong list-equiv equal (take n x) 2
    :hints(("Goal"
            :induct (and (take n x)
                         (cdr-cdr-induct x x-equiv)))))

  (defcong list-equiv equal (take n x) 2)


  (defcong list-equiv equal (butlast lst n) 1
    :hints(("Goal" :induct (cdr-cdr-induct lst lst-equiv))))


  (local (defthm element-list-p-of-take-nil
           (implies (element-p nil)
                    (element-list-p (take n nil)))))

  (def-listp-rule element-list-p-of-take
    (implies (element-list-p (double-rewrite x))
             (iff (element-list-p (take n x))
                  (or (element-p nil)
                      (<= (nfix n) (len x))))))

  (def-projection-rule elementlist-projection-of-take-nil-preserving
    (implies (equal nil (element-xformer nil))
             (equal (elementlist-projection (take n x))
                    (take n (elementlist-projection x))))
    :hints (("goal" :induct (take n x)))
    :name elementlist-projection-of-take
    :requirement nil-preservingp
    :body (equal (elementlist-projection (take n x))
                 (take n (elementlist-projection x))))

  (def-projection-rule elementlist-projection-of-take
    (implies (<= (nfix n) (len x))
             (equal (elementlist-projection (take n x))
                    (take n (elementlist-projection x))))
    :hints (("goal" :induct (take n x)))
    :name elementlist-projection-of-take
    :requirement (not nil-preservingp)))


(defsection first-n
  :parents (std/lists take)
  :short "@(call first-n) is logically identical to @('(take n x)'), but its
guard does not require @('(true-listp x)')."

  :long "<p><b>Reasoning Note.</b> We leave @('first-n') enabled, so it will
just get rewritten into @('take').  You should typically never write a theorem
about @('first-n'): write theorems about @('take') instead.</p>"

  (local (defthm l0
           (equal (append (repeat n x) (cons x y))
                  (cons x (append (repeat n x) y)))))

  (local (defthm l1
           (equal (make-list-ac n val acc)
                  (append (repeat n val) acc))
           :hints(("Goal"
                   :induct (make-list-ac n val acc)))))

  (local (defthm l2
           (implies (atom x)
                    (equal (take n x)
                           (make-list n)))))

  (defun first-n (n x)
    (declare (xargs :guard (natp n)))
    (mbe :logic (take n x)
         :exec
         (cond ((zp n)
                nil)
               ((atom x)
                (make-list n))
               (t
                (cons (car x)
                      (first-n (- n 1) (cdr x))))))))
