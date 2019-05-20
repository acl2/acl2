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

(local (in-theory (enable take)))

(defsection std/lists/butlast
  :parents (std/lists butlast)
  :short "Lemmas about @(see butlast) available in the @(see std/lists)
  library."

  "<p>The usual definition of @('butlast') is in terms of @(see take).  But
  it's often more convenient to reason about @('butlast') directly.  In that
  case, its recursive redefinition may be what you want:</p>"

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

  "<p>For use with @(see std::deflist):</p>"

  (def-listp-rule element-list-p-of-butlast
    (implies (element-list-p (double-rewrite x))
             (element-list-p (butlast x n)))))
