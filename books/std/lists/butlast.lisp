; Butlast lemmas
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
; butlast.lisp

(in-package "ACL2")
(include-book "abstract")
(local (include-book "take"))

(local (defthm commutativity-2-of-+
         (equal (+ x (+ y z)) (+ y (+ x z)))))

(local (defthm fold-consts-in-+
         (implies (and (syntaxp (quotep x))
                       (syntaxp (quotep y)))
                  (equal (+ x (+ y z)) (+ (+ x y) z)))))

(local (in-theory (enable take-redefinition)))

(defthm butlast-redefinition
  (equal (butlast x n)
         (if (>= (nfix n) (len x))
             nil
           (cons (car x)
                 (butlast (cdr x) n))))
  :rule-classes ((:definition :clique (butlast)
                  :controller-alist ((butlast t t)))))

(defun butlast-induction (x n)
  (if (>= (nfix n) (len x))
      nil
    (cons (car x)
          (butlast-induction (cdr x) n))))

(defthm use-butlast-induction
  t
  :rule-classes ((:induction
                  :pattern (butlast x n)
                  :scheme (butlast-induction x n))))

  
(def-listp-rule element-list-p-of-butlast
  (implies (element-list-p (double-rewrite x))
           (element-list-p (butlast x n))))

