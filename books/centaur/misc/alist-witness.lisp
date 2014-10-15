; Centaur Miscellaneous Books
; Copyright (C) 2008-2011 Centaur Technology
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

; alist-witness.lisp -- witnessing strategy for reasoning about alist equivs

(in-package "ACL2")

(include-book "misc/hons-help2" :dir :system)
(include-book "alist-defs")
(include-book "std/lists/sets" :dir :system)
(include-book "std/alists/top" :dir :system)
(include-book "witness-cp")


(defsection alists-agree-witnessing
  (defwitness alists-agree-witnessing
    :predicate (not (alists-agree keys al1 al2))
    :expr (not (let ((x (alists-disagree-witness keys al1 al2)))
                 (implies (member-equal x keys)
                          (equal (hons-assoc-equal x al1)
                                 (hons-assoc-equal x al2)))))
    :hints ('(:in-theory '(alists-agree-iff-witness)))
    :generalize (((alists-disagree-witness keys al1 al2) . adw)))

  (definstantiate alists-agree-instancing
    :predicate (alists-agree keys al1 al2)
    :vars (x)
    :expr (implies (member x keys)
                   (equal (hons-assoc-equal x al1)
                          (hons-assoc-equal x al2)))
    :hints ('(:in-theory '(alists-agree-hons-assoc-equal))))

  (defexample alists-agree-hons-assoc-equal-example
    :pattern (hons-assoc-equal x a)
    :templates (x)
    :instance-rulename alists-agree-instancing)

  (defexample alists-agree-member-keys-example
    :pattern (member-equal x (alist-keys a))
    :templates (x)
    :instance-rulename alists-agree-instancing))




(defsection sub-alistp-witnessing
  (defwitness sub-alistp-witnessing
    :predicate (not (sub-alistp al1 al2))
    :expr (not (let ((x (not-sub-alistp-witness al1 al2)))
                 (implies (hons-assoc-equal x al1)
                          (equal (hons-assoc-equal x al1)
                                 (hons-assoc-equal x al2)))))
    :hints ('(:in-theory '(sub-alistp-iff-witness)))
    :generalize (((not-sub-alistp-witness al1 al2) . nsaw)))

  (definstantiate sub-alistp-instancing
    :predicate (sub-alistp al1 al2)
    :vars (x)
    :expr (implies (hons-assoc-equal x al1)
                   (equal (hons-assoc-equal x al1)
                          (hons-assoc-equal x al2)))
    :hints ('(:in-theory '(sub-alistp-hons-assoc-equal))))

  (defexample sub-alistp-hons-assoc-equal-example
    :pattern (hons-assoc-equal x a)
    :templates (x)
    :instance-rulename sub-alistp-instancing)

  (defexample sub-alistp-member-keys-example
    :pattern (member-equal x (alist-keys a))
    :templates (x)
    :instance-rulename sub-alistp-instancing))


(defsection alist-equiv-witnessing
  (defwitness alist-equiv-witnessing
    :predicate (not (alist-equiv al1 al2))
    :expr (not (let ((x (alist-equiv-bad-guy al1 al2)))
                 (equal (hons-assoc-equal x al1)
                        (hons-assoc-equal x al2))))
    :hints ('(:in-theory '(alist-equiv-iff-agree-on-bad-guy)))
    :generalize (((alist-equiv-bad-guy al1 al2) . aebg)))

  (definstantiate alist-equiv-instancing
    :predicate (alist-equiv al1 al2)
    :vars (x)
    :expr (equal (hons-assoc-equal x al1)
                 (hons-assoc-equal x al2))
    :hints ('(:by (:instance alist-equiv-implies-equal-hons-assoc-equal-2
                   (a al1) (a-equiv al2)))))

  (defexample alist-equiv-hons-assoc-equal-example
    :pattern (hons-assoc-equal x a)
    :templates (x)
    :instance-rulename alist-equiv-instancing)

  (defexample alist-equiv-member-keys-example
    :pattern (member-equal x (alist-keys a))
    :templates (x)
    :instance-rulename alist-equiv-instancing))


(defsection alists-compatible-witnessing
  (defwitness alists-compatible-witnessing
    :predicate (not (alists-compatible al1 al2))
    :expr (not (let ((x (alists-incompatible-witness al1 al2)))
                 (implies (and (hons-assoc-equal x al1)
                               (hons-assoc-equal x al2))
                          (equal (hons-assoc-equal x al1)
                                 (hons-assoc-equal x al2)))))
    :hints ('(:in-theory '(alists-compatible-iff-agree-on-bad-guy)))
    :generalize (((alists-incompatible-witness al1 al2) . aebg)))

  (definstantiate alists-compatible-instancing
    :predicate (alists-compatible al1 al2)
    :vars (x)
    :expr (implies (and (hons-assoc-equal x al1)
                        (hons-assoc-equal x al2))
                   (equal (hons-assoc-equal x al1)
                          (hons-assoc-equal x al2)))
    :hints ('(:in-theory '(alists-compatible-hons-assoc-equal))))

  (defexample alists-compatible-hons-assoc-equal-example
    :pattern (hons-assoc-equal x a)
    :templates (x)
    :instance-rulename alists-compatible-instancing)

  (defexample alists-compatible-member-keys-example
    :pattern (member-equal x (alist-keys a))
    :templates (x)
    :instance-rulename alists-compatible-instancing))

(def-witness-ruleset alist-reasoning-rules
  '(alists-agree-witnessing
    alists-agree-instancing
    alists-agree-hons-assoc-equal-example
    alists-agree-member-keys-example
    sub-alistp-witnessing
    sub-alistp-instancing
    sub-alistp-hons-assoc-equal-example
    sub-alistp-member-keys-example
    alist-equiv-witnessing
    alist-equiv-instancing
    alist-equiv-hons-assoc-equal-example
    alist-equiv-member-keys-example
    alists-compatible-witnessing
    alists-compatible-instancing
    alists-compatible-hons-assoc-equal-example
    alists-compatible-member-keys-example))


(defmacro alist-reasoning ()
  '(and stable-under-simplificationp
        (witness :ruleset alist-reasoning-rules)))
