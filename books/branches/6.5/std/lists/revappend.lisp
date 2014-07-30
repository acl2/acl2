; Revappend lemmas
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
; revappend.lisp
; This file was originally part of the Unicode library.

(in-package "ACL2")
(include-book "list-fix")

(local (defthm len-when-consp
         (implies (consp x)
                  (< 0 (len x)))
         :rule-classes ((:linear) (:rewrite))))

(defsection std/lists/revappend
  :parents (std/lists revappend)
  :short "Lemmas about @(see revappend) available in the @(see std/lists)
library."

  :long "<p>Note: we typically avoid reasoning about @('revappend') because
the following rule can always rewrite it away:</p>

@(thm revappend-removal)

<p>However, if for some reason you need to disable @('revappend-removal'),
these lemmas may be useful.</p>"

  (defthm true-listp-of-revappend
    (equal (true-listp (revappend x y))
           (true-listp y)))

  (defthm consp-of-revappend
    (equal (consp (revappend x y))
           (or (consp x)
               (consp y))))

  (defthm len-of-revappend
    (equal (len (revappend x y))
           (+ (len x)
              (len y))))

  ;; (defthm nth-of-revappend
  ;;   (equal (nth n (revappend x y))
  ;;          (if (< (nfix n) (len x))
  ;;              (nth (- (len x) (+ 1 (nfix n))) x)
  ;;            (nth (- n (len x)) y))))

  (defthm equal-when-revappend-same
    (equal (equal (revappend x y1)
                  (revappend x y2))
           (equal y1 y2)))

  (defthm list-fix-of-revappend
    (equal (list-fix (revappend x y))
           (revappend x (list-fix y))))

  (local (defthm revappend-lengths-x
           (implies (not (equal (len x1) (len x2)))
                    (not (equal (revappend x1 y)
                                (revappend x2 y))))
           :hints(("Goal" :use ((:instance len (x (revappend x1 y)))
                                (:instance len (x (revappend x2 y))))))))


  (local (defthm revappend-nonempty-list
           (implies (consp x)
                    (not (equal (revappend x y) y)))
           :hints(("Goal" :use ((:instance len (x (revappend x y)))
                                (:instance len (x y)))))))

  (local (defun revappend-induction-2-2 (x1 x2 a1 a2)
           (if (and (consp x1)
                    (consp x2))
               (revappend-induction-2-2 (cdr x1) (cdr x2) (cons (car x1) a1) (cons (car x2) a2))
             (list x1 x2 a1 a2))))

  (local (defthm revappend-unequal-accs
           (implies (and (equal (len a1) (len a2))
                         (not (equal a1 a2)))
                    (not (equal (revappend x1 a1)
                                (Revappend x2 a2))))
           :hints (("goal" :induct (revappend-induction-2-2 x1 x2 a1 a2))
                   (and stable-under-simplificationp
                        '(:cases ((consp x2))))
                   (and stable-under-simplificationp
                        '(:cases ((consp x1)))))))

  (local (defun revappend-induction-2 (x y acc)
           (if (and (consp x)
                    (consp y))
               (revappend-induction-2 (cdr x) (cdr y) (cons (car x) acc))
             (list x y acc))))

  (defthm equal-of-revappends-when-true-listps
    (implies (and (true-listp x1)
                  (true-listp x2))
             (equal (equal (revappend x1 y)
                           (revappend x2 y))
                    (equal x1 x2)))
    :hints(("Goal"
            :induct (revappend-induction-2 x1 x2 y))
           (and stable-under-simplificationp
                '(:expand ((revappend x1 y)
                           (revappend x2 y))))))

  (def-listp-rule element-list-p-of-revappend
    (implies (element-list-p x)
             (equal (element-list-p (revappend x y))
                    (element-list-p y))))

  (def-listfix-rule element-list-fix-of-revappend
    (equal (element-list-fix (revappend x y))
           (revappend (element-list-fix x)
                      (element-list-fix y))))

  (def-projection-rule elementlist-projection-of-revappend
    (equal (elementlist-projection (revappend x y))
           (revappend (elementlist-projection x)
                      (elementlist-projection y)))))
