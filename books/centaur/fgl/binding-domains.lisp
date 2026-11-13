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

; Structural binding domains for interpreter stack proofs.

(in-package "FGL")

(include-book "stack-ev")

; Replace values by NIL, retaining ordered keys (including duplicates).

(define fgl-bindings-domain ((x fgl-object-bindings-p))
  :returns (domain fgl-object-bindings-p)
  (if (atom x)
      nil
    (if (and (consp (car x)) (pseudo-var-p (caar x)))
        (cons (cons (caar x) nil) (fgl-bindings-domain (cdr x)))
      (fgl-bindings-domain (cdr x))))
  ///
  (deffixequiv fgl-bindings-domain
    :hints (("Goal" :in-theory (enable fgl-object-bindings-fix))))
  (defthm alist-keys-of-fgl-bindings-domain
    (equal (alist-keys (fgl-bindings-domain x))
           (alist-keys (fgl-object-bindings-fix x)))
    :hints (("Goal" :in-theory (enable fgl-object-bindings-fix))))

  (defthm fgl-bindings-domain-of-append
    (equal (fgl-bindings-domain (append x y))
           (append (fgl-bindings-domain x) (fgl-bindings-domain y)))
    :hints (("Goal" :in-theory (enable fgl-bindings-domain))))

  (defthm fgl-bindings-domain-of-concretize
    (equal (fgl-bindings-domain (fgl-object-bindings-concretize x env logicman))
           (fgl-bindings-domain x))
    :hints (("Goal" :in-theory (enable fgl-bindings-domain fgl-object-bindings-concretize))))

  (defthm hons-assoc-equal-of-fgl-bindings-domain
    (iff (hons-assoc-equal k (fgl-bindings-domain x))
         (hons-assoc-equal k (fgl-object-bindings-fix x)))
    :hints (("Goal" :in-theory (enable fgl-bindings-domain fgl-object-bindings-fix)))))

(define minor-stack-binding-domains ((x minor-stack-p))
  :measure (acl2-count x)
  :ruler-extenders :all
  :returns (domains minor-stack-p)
  (cons (make-minor-frame :bindings
                          (fgl-bindings-domain (minor-frame->bindings (car x))))
        (and (consp (cdr x)) (minor-stack-binding-domains (cdr x))))
  ///

  (deffixequiv minor-stack-binding-domains
    :hints (("Goal" :in-theory (enable minor-stack-binding-domains minor-stack-fix default-car))))

  (defthm minor-stack-binding-domains-of-concretize
    (equal (minor-stack-binding-domains (fgl-minor-stack-concretize x env logicman))
           (minor-stack-binding-domains x))
    :hints (("Goal" :in-theory (enable minor-stack-binding-domains
                                       fgl-minor-stack-concretize fgl-minor-frame-concretize)))))

(define stack-binding-domains ((x major-stack-p))
  :measure (acl2-count x)
  :ruler-extenders :all
  :returns (domains major-stack-p)
  (cons (make-major-frame :bindings
                          (fgl-bindings-domain (major-frame->bindings (car x)))
                          :minor-stack
                          (minor-stack-binding-domains (major-frame->minor-stack (car x))))
        (and (consp (cdr x)) (stack-binding-domains (cdr x))))
  ///

  (deffixequiv stack-binding-domains
    :hints (("Goal" :in-theory (enable stack-binding-domains major-stack-fix default-car))))

  (defthm stack-binding-domains-of-concretize
    (equal (stack-binding-domains (fgl-major-stack-concretize x env logicman))
           (stack-binding-domains x))
    :hints (("Goal" :in-theory (enable stack-binding-domains
                                       fgl-major-stack-concretize fgl-major-frame-concretize))))

  (defthm stack-binding-domains-of-set-rule
    (equal (stack-binding-domains (stack$a-set-rule rule stack))
           (stack-binding-domains stack))
    :hints (("Goal" :in-theory (enable stack-binding-domains minor-stack-binding-domains stack$a-set-rule))))

  (defthm stack-binding-domains-of-set-phase
    (equal (stack-binding-domains (stack$a-set-phase phase stack))
           (stack-binding-domains stack))
    :hints (("Goal" :in-theory (enable stack-binding-domains minor-stack-binding-domains stack$a-set-phase))))

  (defthm stack-binding-domains-of-set-term
    (equal (stack-binding-domains (stack$a-set-term term stack))
           (stack-binding-domains stack))
    :hints (("Goal" :in-theory (enable stack-binding-domains minor-stack-binding-domains stack$a-set-term))))

  (defthm stack-binding-domains-of-set-term-index
    (equal (stack-binding-domains (stack$a-set-term-index idx stack))
           (stack-binding-domains stack))
    :hints (("Goal" :in-theory (enable stack-binding-domains minor-stack-binding-domains stack$a-set-term-index))))

  (defthm stack-binding-domains-of-push-scratch
    (equal (stack-binding-domains (stack$a-push-scratch obj stack))
           (stack-binding-domains stack))
    :hints (("Goal" :in-theory (enable stack-binding-domains minor-stack-binding-domains stack$a-push-scratch))))

  (defthm stack-binding-domains-of-pop-scratch
    (equal (stack-binding-domains (stack$a-pop-scratch  stack))
           (stack-binding-domains stack))
    :hints (("Goal" :in-theory (enable stack-binding-domains minor-stack-binding-domains stack$a-pop-scratch))))

  (defthm stack-binding-domains-of-update-scratch
    (equal (stack-binding-domains (stack$a-update-scratch n obj stack))
           (stack-binding-domains stack))
    :hints (("Goal" :in-theory (enable stack-binding-domains minor-stack-binding-domains stack$a-update-scratch))))

  (defthm stack-binding-domains-of-set-bindings
    (equal (stack-binding-domains (stack$a-set-bindings bindings stack))
           (stack$a-set-bindings (fgl-bindings-domain bindings) (stack-binding-domains stack)))
    :hints (("Goal" :in-theory (enable stack-binding-domains minor-stack-binding-domains
                                       fgl-bindings-domain stack$a-set-bindings default-car))))

  (defthm stack-binding-domains-of-add-binding
    (equal (stack-binding-domains (stack$a-add-binding var val stack))
           (stack$a-add-binding (pseudo-var-fix var) nil (stack-binding-domains stack)))
    :hints (("Goal" :in-theory (enable stack-binding-domains minor-stack-binding-domains
                                       fgl-bindings-domain stack$a-add-binding default-car))))

  (defthm stack-binding-domains-of-set-minor-bindings
    (equal (stack-binding-domains (stack$a-set-minor-bindings bindings stack))
           (stack$a-set-minor-bindings (fgl-bindings-domain bindings) (stack-binding-domains stack)))
    :hints (("Goal" :in-theory (enable stack-binding-domains minor-stack-binding-domains
                                       fgl-bindings-domain stack$a-set-minor-bindings default-car))))

  (defthm stack-binding-domains-of-add-minor-bindings
    (equal (stack-binding-domains (stack$a-add-minor-bindings bindings stack))
           (stack$a-add-minor-bindings (fgl-bindings-domain bindings) (stack-binding-domains stack)))
    :hints (("Goal" :in-theory (enable stack-binding-domains minor-stack-binding-domains
                                       fgl-bindings-domain stack$a-add-minor-bindings default-car))))

  (defthm stack-binding-domains-of-push-frame
    (equal (stack-binding-domains (stack$a-push-frame  stack))
           (stack$a-push-frame  (stack-binding-domains stack)))
    :hints (("Goal" :in-theory (enable stack-binding-domains minor-stack-binding-domains
                                       fgl-bindings-domain stack$a-push-frame default-car))))

  (defthm stack-binding-domains-of-pop-frame
    (equal (stack-binding-domains (stack$a-pop-frame  stack))
           (stack$a-pop-frame  (stack-binding-domains stack)))
    :hints (("Goal" :in-theory (enable stack-binding-domains minor-stack-binding-domains
                                       fgl-bindings-domain stack$a-pop-frame default-car))))

  (defthm stack-binding-domains-of-push-minor-frame
    (equal (stack-binding-domains (stack$a-push-minor-frame  stack))
           (stack$a-push-minor-frame  (stack-binding-domains stack)))
    :hints (("Goal" :in-theory (enable stack-binding-domains minor-stack-binding-domains
                                       fgl-bindings-domain stack$a-push-minor-frame default-car))))

  (defthm stack-binding-domains-of-pop-minor-frame
    (equal (stack-binding-domains (stack$a-pop-minor-frame  stack))
           (stack$a-pop-minor-frame  (stack-binding-domains stack)))
    :hints (("Goal" :in-theory (enable stack-binding-domains minor-stack-binding-domains
                                       fgl-bindings-domain stack$a-pop-minor-frame default-car))))

  (defthm bindings-of-stack-binding-domains
    (equal (stack$a-bindings (stack-binding-domains x))
           (fgl-bindings-domain (stack$a-bindings x)))
    :hints (("Goal" :in-theory (enable stack-binding-domains stack$a-bindings))))

  (defthm minor-bindings-of-stack-binding-domains
    (equal (stack$a-minor-bindings (stack-binding-domains x))
           (fgl-bindings-domain (stack$a-minor-bindings x)))
    :hints (("Goal" :in-theory (enable stack-binding-domains minor-stack-binding-domains
                                       stack$a-minor-bindings)))))
