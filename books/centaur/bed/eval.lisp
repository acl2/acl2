; Centaur BED Library
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

(in-package "BED")
(include-book "ops")

(define bed-env-lookup (var env)
  (b* (((when (or (eq var t)
                  (eq var nil)))
        ;; Goofy restriction to agree with aig-eval
        var)
       (look (hons-get var env))
       ((unless look)
        ;; Goofy default value agrees with aig-env-lookup
        t))
    (and (cdr look) t))
  ///
  (defthm bed-env-lookup-of-nil
    (equal (bed-env-lookup nil env)
           nil))
  (defthm bed-env-lookup-of-t
    (equal (bed-env-lookup t env)
           t)))

(local (in-theory (disable bitp)))

(define bed-eval ((x   "BED to evaluate")
                  (env "Fast alist mapping variables to Booleans (t/nil)"))
  :returns (bit bitp)
  :parents (bed)
  :short "Semantics of BEDs."
  :verify-guards nil
  (b* (((when (atom x))
        (if x 1 0))
       ((cons a b) x)

       ((unless (integerp b))
        ;; Variable node -- lazily evaluate whichever branch we need.
        (if (bed-env-lookup a env)
            (bed-eval (car$ b) env)
          (bed-eval (cdr$ b) env)))

       ;; Operator node, we'll evaluate both branches
       (op    (bed-op-fix b))
       (left  (bed-eval (car$ a) env))
       (right (bed-eval (cdr$ a) env)))
    (bed-op-eval op left right))
  ///
  (verify-guards bed-eval)
  (memoize 'bed-eval :condition '(consp x))

  (defthm bed-eval-when-atom
    (implies (atom x)
             (equal (bed-eval x env)
                    (if x 1 0))))

  (defthm bed-eval-of-var
    (implies (and (consp x)
                  (not (integerp (cdr x))))
             (equal (bed-eval x env)
                    (if (bed-env-lookup (car x) env)
                        (bed-eval (car (cdr x)) env)
                      (bed-eval (cdr (cdr x)) env)))))

  (defthm bed-eval-when-known-op
    (implies (and (equal (bed-op-fix op) fixed-op)
                  (integerp op))
             (equal (bed-eval (cons leftright op) env)
                    (bed-op-eval fixed-op
                                 (bed-eval (car leftright) env)
                                 (bed-eval (cdr leftright) env))))))
