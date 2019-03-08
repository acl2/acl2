; Pseudo-term-fix.lisp: Fixing function for pseudo-terms, transparent to evaluators.

; Copyright (C) 2019 Centaur Technology
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
; Original author: Sol Swords <sswords@centtech.com>

(in-package "ACL2")

(include-book "tools/flag" :dir :system)

;; Defines an induction scheme for the evaluator.

(defmacro def-ev-ind (ev ev-list)
  (let* ((ev-ind (intern-in-package-of-symbol
                  (concatenate 'string (symbol-name ev) "-IND")
                  ev))
         (ev-list-ind (intern-in-package-of-symbol
                       (concatenate 'string (symbol-name ev-list) "-IND")
                       ev-list))
         (ev-flag (intern-in-package-of-symbol
                   (concatenate 'string (symbol-name ev) "-FLAG")
                   ev)))
    `(progn
       (mutual-recursion
        (defun ,ev-ind (x a)
          (cond ((atom x) (and x (symbolp x) (cdr (assoc x a))))
                ((eq (car x) 'quote) (cadr x))
                ((symbolp (car x)) (,ev-list-ind (cdr x) a))
                ((atom (car x)) nil)
                (t (let* ((args (,ev-list (cdr x) a))
                          (new-a (pairlis$ (cadr (car x)) args)))
                     (list (,ev-ind (caddr (car x)) new-a)
                           (,ev-list-ind (cdr x) a))))))
        (defun ,ev-list-ind (x a)
          (if (atom x)
              nil
            (cons (,ev-ind (car x) a)
                  (,ev-list-ind (cdr x) a)))))

       (flag::make-flag ,ev-flag ,ev-ind
                        :flag-mapping ((,ev-ind . ,ev)
                                       (,ev-list-ind . ,ev-list))))))
