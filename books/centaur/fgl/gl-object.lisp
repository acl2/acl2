; GL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2018 Centaur Technology
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

(in-package "FGL")
(include-book "centaur/fty/deftypes" :dir :system)
(include-book "centaur/misc/numlist" :dir :system)
(include-book "centaur/fty/baselists" :dir :system)
(include-book "clause-processors/pseudo-term-fty" :dir :system)

(fty::deftypes gl-object
  (fty::defflexsum gl-object
    (:g-concrete
     :cond (or (atom x)
               (eq (car x) :g-concrete))
     :shape (and (not (member x '(:g-concrete
                                  :g-boolean
                                  :g-integer
                                  :g-ite
                                  :g-apply
                                  :g-var)))
                 (or (atom x)
                     (consp (cdr x))
                     (member (cdr x)
                             '(:g-concrete
                               :g-boolean
                               :g-integer
                               :g-ite
                               :g-apply
                               :g-var))))
     :fields ((val :acc-body
                   (if (consp x) (cdr x) x)))
     :ctor-body (if (and (atom val)
                         (not (and (symbolp val) ;; optimization
                                   (member-eq val '(:g-concrete
                                                    :g-boolean
                                                    :g-integer
                                                    :g-ite
                                                    :g-apply
                                                    :g-var)))))
                    val
                  (cons :g-concrete val))
     :type-name g-concrete)
    (:g-boolean
     :cond (eq (car x) :g-boolean)
     :fields ((bool :acc-body (cdr x)))
     :ctor-body (cons :g-boolean bool)
     :type-name g-boolean)
    (:g-integer
     :cond (eq (car x) :g-integer)
     :fields ((bits :acc-body (cdr x) :type true-listp))
     :ctor-body (cons :g-integer bits)
     :type-name g-integer)
    (:g-ite
     :cond (eq (car x) :g-ite)
     :shape (and (consp (cdr x))
                 (consp (cddr x)))
     :fields ((test :type gl-object :acc-body (cadr x))
              (then :type gl-object :acc-body (caddr x))
              (else :type gl-object :acc-body (cdddr x)))
     :ctor-body (cons :g-ite (cons test (cons then else)))
     :type-name g-ite)
    (:g-apply
     :cond (eq (car x) :g-apply)
     :shape (consp (cdr x))
     :fields ((fn :type pseudo-fnsym :acc-body (cadr x))
              (args :type gl-objectlist :acc-body (cddr x)))
     :ctor-body (cons :g-apply (cons fn args))
     :type-name g-apply)
    (:g-var
     :cond (eq (car x) :g-var)
     :fields ((name :type pseudo-var :acc-body (cdr x)))
     :ctor-body (cons :g-var name)
     :type-name g-var)
    (:g-cons
     :fields ((car :type gl-object :acc-body (car x))
              (cdr :type gl-object :acc-body (cdr x)))
     :ctor-body (cons car cdr)
     :type-name g-cons)

    :post-pred-events
    ((local (defthm gl-object-p-of-cons
              (implies (and (gl-object-p x)
                            (gl-object-p y))
                       (gl-object-p (cons x y)))
              :hints (("goal" :expand ((gl-object-p x)
                                       (gl-object-p (cons x y)))))))))
  (fty::deflist gl-objectlist :elt-type gl-object :true-listp t))
     

(defsection g-int
  :parents (shape-specs)
  :short "Create a g-binding for an integer."
  :long "<p>This is a low-level way to create a custom shape specifier for a
signed integer.  You might generally prefer higher-level tools like @(see
auto-bindings).</p>"

  (defun g-int (start by n)
    (declare (xargs :guard (and (acl2-numberp start)
                                (acl2-numberp by)
                                (natp n))))
    (g-integer (numlist start by n))))
