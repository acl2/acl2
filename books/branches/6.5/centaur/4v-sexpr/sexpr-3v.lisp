; S-Expressions for 4-Valued Logic
; Copyright (C) 2010-2012 Centaur Technology
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
(include-book "sexpr-eval")

(defsection 3v-syntax-sexprp
  :parents (4v-sexprs)
  :short "Recognizer for @(see 4v-sexprs) that cannot evaluate to Z."

  (defund 3v-syntax-sexprp (x)
    (declare (xargs :guard t))
    (and (consp x)
         (let ((fn (car x)))
           (not (or (eq fn (4vz))
                    (eq fn 'id)
                    (eq fn 'res)
                    (eq fn 'zif)
                    (eq fn 'tristate))))))

  (local (in-theory (enable* 3v-syntax-sexprp
                             (:ruleset 4v-op-defs))))

  (defmacro prove-3vp (f args)
    `(defthm ,(intern-in-package-of-symbol
               (concatenate 'string "3VP-OF-" (symbol-name f))
               f)
       (equal (equal (4vz) (,f . ,args))
              nil)))

  (prove-3vp 4v-unfloat (a))
  (prove-3vp 4v-not (a))
  (prove-3vp 4v-xdet (a))
  (prove-3vp 4v-and (a b))
  (prove-3vp 4v-or (a b))
  (prove-3vp 4v-xor (a b))
  (prove-3vp 4v-iff (a b))
  (prove-3vp 4v-ite (c a b))
  (prove-3vp 4v-ite* (c a b))
  (prove-3vp 4v-pullup (a))

  (defthm 3vp-sexpr-eval-when-3v-syntax-sexprp
    (implies (3v-syntax-sexprp x)
             (equal (equal (4vz) (4v-sexpr-eval x env))
                    nil))
    :hints(("Goal"
            :expand ((4v-sexpr-eval x env))
            :in-theory (e/d* (4v-sexpr-apply)
                             ((:ruleset 4v-op-defs)))))))
