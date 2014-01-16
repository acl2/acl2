; S-Expressions for 4-Valued Logic
; Copyright (C) 2010-2012 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
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
