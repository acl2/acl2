; FGL - A Symbolic Simulation Framework for ACL2
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

; Executable ACL2 term validation with plist-worldp guards.

(in-package "FGL")

(include-book "std/util/defines" :dir :system)
(include-book "clause-processors/pseudo-term-fty" :dir :system)
(local (include-book "std/lists/acl2-count" :dir :system))

(local (std::add-default-post-define-hook :fix))
(std::make-returnspec-config :hints-sub-returnnames t)

(define easy-arity ((fn (or (and (consp fn)
                                 (consp (cdr fn))
                                 (true-listp (cadr fn)))
                            (symbolp fn)))
                    (w plist-worldp))
  :returns (nargs (equal nargs (arity fn w))
                  :hints(("Goal" :in-theory (enable arity length))))
  (cond ((acl2::flambdap fn) (length (acl2::lambda-formals fn)))
        (t (let ((temp (getpropc fn 'formals t w)))
             (cond ((eq temp t) nil)
                   (t (if (stringp temp) (length temp) (len temp))))))))

(defines easy-termp
  (define easy-termp (x (w plist-worldp))
    :no-function t
    :verify-guards nil
    :returns (ans (equal ans (termp x w))
                  :hints ('(:expand ((termp x w)))))
    :prepwork ((local (in-theory (disable termp term-listp
                                          acl2::legal-variablep
                                          acl2::arglistp1
                                          acl2::all-vars1
                                          acl2-count
                                          true-listp))))
    (cond ((acl2::variablep x) (acl2::legal-variablep x))
          ((acl2::fquotep x)
           (and (consp (cdr x)) (null (cddr x))))
          ((symbolp (car x))
           (let ((arity (easy-arity (car x) w)))
             (and arity
                  (easy-term-listp (cdr x) w)
                  (eql (length (cdr x)) arity))))
          ((and (consp (car x))
                (true-listp (car x))
                (eq (caar x) 'lambda)
                (eql 3 (length (car x)))
                (acl2::arglistp (cadr (car x)))
                (easy-termp (caddr (car x)) w)
                (null (set-difference-eq (all-vars (caddr (car x)))
                                         (cadr (car x))))
                (easy-term-listp (cdr x) w)
                (eql (length (cadr (car x)))
                     (length (cdr x))))
           t)
          (t nil)))
  (define easy-term-listp (x (w plist-worldp))
    :no-function t
    :returns (ans (equal ans (term-listp x w))
                  :hints ('(:expand ((term-listp x w)))))
    (cond ((atom x) (equal x nil))
          ((easy-termp (car x) w)
           (easy-term-listp (cdr x) w))
          (t nil)))
  ///
  (local (defthm symbolp-when-legal-variablep
           (implies (acl2::legal-variablep x)
                    (symbolp x))
           :hints(("Goal" :in-theory (enable acl2::legal-variablep)))))
  (local (defthm symbol-listp-when-arglistp1
           (implies (acl2::arglistp1 x)
                    (symbol-listp x))
           :hints(("Goal" :in-theory (enable acl2::arglistp1)))))
  (local (defthm true-listp-when-arglistp1
           (implies (acl2::arglistp1 x)
                    (true-listp x))
           :hints(("Goal" :in-theory (enable acl2::arglistp1)))))

  #!acl2
  (local (flag::make-flag all-vars1-flag all-vars1))
  #!acl2
  (local (defthm-all-vars1-flag
           (defthm true-listp-of-all-vars1
             (implies (true-listp ans)
                      (true-listp (all-vars1 term ans)))
             :hints ('(:expand ((all-vars1 term ans))))
             :flag all-vars1)
           (defthm true-listp-of-all-vars1-lst
             (implies (true-listp ans)
                      (true-listp (all-vars1-lst lst ans)))
             :hints ('(:expand ((all-vars1-lst lst ans))))
             :flag all-vars1-lst)))

  (defthm-easy-termp-flag
    (defthm termp-implies-pseudo-termp
      (implies (termp x w)
               (pseudo-termp x))
      :hints ('(:expand ((termp x w)
                         (pseudo-termp x))))
      :flag easy-termp)
    (defthm term-listp-implies-pseudo-term-listp
      (implies (term-listp x w)
               (pseudo-term-listp x))
      :hints ('(:expand ((term-listp x w)
                         (pseudo-term-listp x))))
      :flag easy-term-listp))


  (verify-guards easy-termp))
