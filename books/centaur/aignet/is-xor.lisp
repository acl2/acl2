; AIGNET - And-Inverter Graph Networks
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


(in-package "AIGNET")

(include-book "semantics")
(local (std::add-default-post-define-hook :fix))

(define id-is-xor ((id natp) aignet)
  :guard (id-existsp id aignet)
  :returns (mv is-xor
               (child1 litp :rule-classes :type-prescription)
               (child2 litp :rule-classes :type-prescription))
  :prepwork ((local (in-theory (disable lookup-id-in-bounds-when-positive
                                        lookup-id-out-of-bounds
                                        satlink::equal-of-lit-negate-backchain))))
  (b* (((unless (int= (id->type id aignet) (gate-type)))
        (mv nil 0 0))
       (f0 (gate-id->fanin0 id aignet))
       (f1 (gate-id->fanin1 id aignet))
       ((when (int= (id->regp id aignet) 1))
        ;; it's an explicit XOR gate
        (mv t f0 f1))
       ((unless (and (int= (lit-neg f0) 1)
                     (int= (lit-neg f1) 1)
                     (int= (id->type (lit-id f0) aignet) (gate-type))
                     (int= (id->regp (lit-id f0) aignet) 0)
                     (int= (id->type (lit-id f1) aignet) (gate-type))
                     (int= (id->regp (lit-id f1) aignet) 0)))
        (mv nil 0 0))
       (f00 (gate-id->fanin0 (lit-id f0) aignet))
       (f10 (gate-id->fanin1 (lit-id f0) aignet))
       (f01 (gate-id->fanin0 (lit-id f1) aignet))
       (f11 (gate-id->fanin1 (lit-id f1) aignet))
       (nf01 (lit-negate f01))
       (nf11 (lit-negate f11))
       ((when (or (and (int= f00 nf01)
                       (int= f10 nf11))
                  (and (int= f00 nf11)
                       (int= f10 nf01))))
        (mv t f00 f10)))
    (mv nil 0 0))
  ///
  (defret aignet-litp-of-<fn>
    (and (aignet-litp child1 aignet)
         (aignet-litp child2 aignet)))

  (defretd id-eval-when-id-is-xor
    (implies is-xor
             (equal (id-eval id in-vals reg-vals aignet)
                    (acl2::b-xor (lit-eval child1 in-vals reg-vals aignet)
                                 (lit-eval child2 in-vals reg-vals aignet))))
    :hints (("goal" :expand ((id-eval id in-vals reg-vals aignet)
                             (id-eval (lit-id (fanin 0 (lookup-id id aignet)))
                                      in-vals reg-vals aignet)
                             (id-eval (lit-id (fanin 1 (lookup-id id aignet)))
                                      in-vals reg-vals aignet))
             :in-theory (enable lit-eval eval-and-of-lits eval-xor-of-lits))
            (and stable-under-simplificationp
                 '(:in-theory (enable b-xor)))))

  (defretd <fn>-not-xor-implies-and
    (implies (not is-xor)
             (iff (equal (ctype (stype (car (lookup-id id aignet)))) (gate-ctype))
                  (equal (stype (car (lookup-id id aignet))) (and-stype)))))

  (defret lit-id-bound-of-id-is-xor-child1
    (implies is-xor
             (< (lit->var child1) (nfix id)))
    :rule-classes :linear)

  (defret lit-id-bound-of-id-is-xor-child2
    (implies is-xor
             (< (lit->var child2) (nfix id)))
    :rule-classes :linear))


(define lit-is-xor ((lit litp) aignet)
  :guard (fanin-litp lit aignet)
  :returns (mv is-xor
               (child1 litp :rule-classes :type-prescription)
               (child2 litp :rule-classes :type-prescription))
  :prepwork ((local (in-theory (disable lookup-id-in-bounds-when-positive
                                        lookup-id-out-of-bounds
                                        satlink::equal-of-lit-negate-backchain))))
  (b* (((mv is-xor fanin0 fanin1) (id-is-xor (lit->var lit) aignet)))
    (mv is-xor (lit-negate-cond fanin0 (lit->neg lit)) fanin1))
  ///
  (defret aignet-litp-of-<fn>
    (and (aignet-litp child1 aignet)
         (aignet-litp child2 aignet)))

  (defretd lit-eval-when-lit-is-xor
    (implies is-xor
             (equal (lit-eval lit in-vals reg-vals aignet)
                    (acl2::b-xor (lit-eval child1 in-vals reg-vals aignet)
                                 (lit-eval child2 in-vals reg-vals aignet))))
    :hints (("goal" :expand ((lit-eval lit in-vals reg-vals aignet))
             :in-theory (enable id-eval-when-id-is-xor))
            (and stable-under-simplificationp
                 '(:in-theory (enable b-xor)))))

  (defretd <fn>-not-xor-implies-and
    (implies (not is-xor)
             (iff (equal (ctype (stype (car (lookup-id (lit->var lit) aignet)))) (gate-ctype))
                  (equal (stype (car (lookup-id (lit->var lit) aignet))) (and-stype))))
    :hints(("Goal" :in-theory (enable id-is-xor-not-xor-implies-and))))

  (defret lit-id-bound-of-<fn>-child1
    (implies is-xor
             (< (lit->var child1) (lit->var lit)))
    :rule-classes :linear)

  (defret lit-id-bound-of-<fn>-child2
    (implies is-xor
             (< (lit->var child2) (lit->var lit)))
    :rule-classes :linear))
