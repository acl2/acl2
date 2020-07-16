; Copyright (C) 2020 Centaur Technology
; AIGNET - And-Inverter Graph Networks
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
(include-book "levels")
(include-book "centaur/fty/baselists" :dir :system)
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "std/lists/sets" :dir :system))
(local (include-book "std/basic/arith-equivs" :dir :system))

(local
 #!acl2
 (fty::deflist nat-list
  :elt-type nat
  :pred nat-listp
  :true-listp t
  :elementp-of-nil nil))


(local (defthm member-equal-of-nat-list-fix
         (implies (member-equal x y)
                  (member-equal (nfix x) (acl2::nat-list-fix y)))
         :hints(("Goal" :in-theory (enable acl2::nat-list-fix)))))

(local (defthm subsetp-equal-of-nat-list-fix
         (implies (subsetp-equal x y)
                  (subsetp-equal (acl2::nat-list-fix x) (acl2::nat-list-fix y)))
         :hints(("Goal" :in-theory (enable subsetp-equal acl2::nat-list-fix)))))

(local (defcong acl2::set-equiv acl2::set-equiv (acl2::nat-list-fix x) 1
         :hints(("Goal" :in-theory (enable acl2::set-equiv)))))

(defines id-eval-toggle
  :prepwork ((local (in-theory (disable lookup-id-in-bounds-when-positive
                                        lookup-id-out-of-bounds))))
  :ruler-extenders :lambdas
  (define lit-eval-toggle ((lit litp) (toggles nat-listp) invals regvals aignet)
    :guard (and (fanin-litp lit aignet)
                (<= (num-ins aignet) (bits-length invals))
                (<= (num-regs aignet) (bits-length regvals)))
    :measure (acl2::two-nats-measure (lit-id lit) 1)
    :verify-guards nil
    :returns (val bitp :rule-classes :type-prescription)
    (b-xor (id-eval-toggle (lit-id lit) toggles invals regvals aignet)
           (lit-neg lit)))

  (define eval-and-of-lits-toggle ((lit1 litp)
                            (lit2 litp)
                            (toggles nat-listp)
                            invals regvals aignet)
    :guard (and (fanin-litp lit1 aignet)
                (fanin-litp lit2 aignet)
                (<= (num-ins aignet) (bits-length invals))
                (<= (num-regs aignet) (bits-length
                                       regvals)))
    :measure (acl2::two-nats-measure
              (max (lit-id lit1)
                   (lit-id lit2))
              2)
    :returns (val bitp :rule-classes :type-prescription)
    (b-and (lit-eval-toggle lit1 toggles invals regvals aignet)
           (lit-eval-toggle lit2 toggles invals regvals aignet)))

  (define eval-xor-of-lits-toggle ((lit1 litp)
                            (lit2 litp)
                            (toggles nat-listp)
                            invals regvals aignet)
    :guard (and (fanin-litp lit1 aignet)
                (fanin-litp lit2 aignet)
                (<= (num-ins aignet) (bits-length invals))
                (<= (num-regs aignet) (bits-length
                                       regvals)))
    :measure (acl2::two-nats-measure
              (max (lit-id lit1)
                   (lit-id lit2))
              2)
    :returns (val bitp :rule-classes :type-prescription)
    (b-xor (lit-eval-toggle lit1 toggles invals regvals aignet)
           (lit-eval-toggle lit2 toggles invals regvals aignet)))

  (define id-eval-toggle ((id natp) (toggles nat-listp) invals regvals aignet)
    :guard (and (id-existsp id aignet)
                (<= (num-ins aignet) (bits-length invals))
                (<= (num-regs aignet) (bits-length regvals)))
    :measure (acl2::two-nats-measure id 0)
    :hints(("Goal" :in-theory (enable aignet-idp)))
    :returns (val bitp :rule-classes :type-prescription)
    (let ((ans
           (b* (((unless (mbt (id-existsp id aignet)))
                 ;; out-of-bounds IDs are false
                 0)
                (type (id->type id aignet)))
             (aignet-case
               type
               :gate (b* ((f0 (gate-id->fanin0 id aignet))
                          (f1 (gate-id->fanin1 id aignet)))
                       (if (int= (id->regp id aignet) 1)
                           (eval-xor-of-lits-toggle
                            f0 f1 toggles invals regvals aignet)
                         (eval-and-of-lits-toggle
                          f0 f1 toggles invals regvals aignet)))
               :in    (if (int= (id->regp id aignet) 1)
                          (get-bit (ci-id->ionum id aignet) regvals)
                        (get-bit (ci-id->ionum id aignet) invals))
               :const 0))))
      (if (member (lnfix id) (acl2::nat-list-fix toggles))
          (b-not ans)
        ans)))
  ///
  (fty::deffixequiv-mutual id-eval-toggle)
  (verify-guards id-eval-toggle)

  (std::defret-mutual <fn>-set-equiv-congruence-on-toggles
    (defret <fn>-set-equiv-congruence-on-toggles
      (implies (acl2::set-equiv toggles toggles2)
               (equal val (id-eval-toggle id toggles2 invals regvals aignet)))
      :rule-classes :congruence
      :fn id-eval-toggle)
    (defret <fn>-set-equiv-congruence-on-toggles
      (implies (acl2::set-equiv toggles toggles2)
               (equal val (lit-eval-toggle lit toggles2 invals regvals aignet)))
      :rule-classes :congruence
      :fn lit-eval-toggle)
    (defret <fn>-set-equiv-congruence-on-toggles
      (implies (acl2::set-equiv toggles toggles2)
               (equal val (eval-and-of-lits-toggle lit1 lit2 toggles2 invals regvals aignet)))
      :rule-classes :congruence
      :fn eval-and-of-lits-toggle)
    (defret <fn>-set-equiv-congruence-on-toggles
      (implies (acl2::set-equiv toggles toggles2)
               (equal val (eval-xor-of-lits-toggle lit1 lit2 toggles2 invals regvals aignet)))
      :rule-classes :congruence
      :fn eval-xor-of-lits-toggle))


  (std::defret-mutual <fn>-when-empty-toggles
    (defret <fn>-when-empty-toggles :pre-bind ((toggles nil))
      (equal val (id-eval id invals regvals aignet))
      :hints ('(:expand ((id-eval id invals regvals aignet)
                         (:free (toggles) <call>))))
      :fn id-eval-toggle)
    (defret <fn>-when-empty-toggles :pre-bind ((toggles nil))
      (equal val (lit-eval lit invals regvals aignet))
      :hints ('(:expand ((lit-eval lit invals regvals aignet)
                         (:free (toggles) <call>))))
      :fn lit-eval-toggle)
    (defret <fn>-when-empty-toggles :pre-bind ((toggles nil))
      (equal val (eval-and-of-lits lit1 lit2 invals regvals aignet))
      :hints ('(:expand ((eval-and-of-lits lit1 lit2 invals regvals aignet)
                         (:free (toggles) <call>))))
      :fn eval-and-of-lits-toggle)
    (defret <fn>-when-empty-toggles :pre-bind ((toggles nil))
      (equal val (eval-xor-of-lits lit1 lit2 invals regvals aignet))
      :hints ('(:expand ((eval-xor-of-lits lit1 lit2 invals regvals aignet)
                         (:free (toggles) <call>))))
      :fn eval-xor-of-lits-toggle))

  (std::defret-mutual <fn>-add-toggle-when-greater
    (defret <fn>-add-toggle-when-greater
      (implies (< (nfix id) (nfix toggle))
               (equal (let ((toggles (cons toggle toggles))) <call>)
                      val))
      :hints ('(:expand ((:free (toggles) <call>))))
      :fn id-eval-toggle)
    (defret <fn>-add-toggle-when-greater
      (implies (< (lit->var lit) (nfix toggle))
               (equal (let ((toggles (cons toggle toggles))) <call>)
                      val))
      :hints ('(:expand ((:free (toggles) <call>))))
      :fn lit-eval-toggle)
    (defret <fn>-add-toggle-when-greater
      (implies (and (< (lit->var lit1) (nfix toggle))
                    (< (lit->var lit2) (nfix toggle)))
               (equal (let ((toggles (cons toggle toggles))) <call>)
                      val))
      :hints ('(:expand ((:free (toggles) <call>))))
      :fn eval-and-of-lits-toggle)
    (defret <fn>-add-toggle-when-greater
      (implies (and (< (lit->var lit1) (nfix toggle))
                    (< (lit->var lit2) (nfix toggle)))
               (equal (let ((toggles (cons toggle toggles))) <call>)
                      val))
      :hints ('(:expand ((:free (toggles) <call>))))
      :fn eval-xor-of-lits-toggle))

  (local (defthm aignet-node-level-when-not-aignet-idp
           (implies (not (aignet-idp id aignet))
                    (equal (aignet-node-level id aignet) 0))
           :hints(("Goal" :in-theory (enable aignet-node-level)))))

  (local (defthm aignet-node-level-when-not-gate
           (implies (not (equal (ctype (stype (car (lookup-id id aignet)))) :gate))
                    (equal (aignet-node-level id aignet) 0))
           :hints(("Goal" :in-theory (enable aignet-node-level)))))

  (std::defret-mutual <fn>-add-toggle-when-level-greater
    (defret <fn>-add-toggle-when-level-greater
      (implies (< (aignet-node-level id aignet) (aignet-node-level toggle aignet))
               (equal (let ((toggles (cons toggle toggles))) <call>)
                      val))
      :hints ('(:expand ((:free (toggles) <call>)
                         (aignet-node-level id aignet))
                :in-theory (enable* acl2::arith-equiv-forwarding)))
      :fn id-eval-toggle)
    (defret <fn>-add-toggle-when-level-greater
      (implies (< (aignet-node-level (lit->var lit) aignet) (aignet-node-level toggle aignet))
               (equal (let ((toggles (cons toggle toggles))) <call>)
                      val))
      :hints ('(:expand ((:free (toggles) <call>))))
      :fn lit-eval-toggle)
    (defret <fn>-add-toggle-when-level-greater
      (implies (and (< (aignet-node-level (lit->var lit1) aignet) (aignet-node-level toggle aignet))
                    (< (aignet-node-level (lit->var lit2) aignet) (aignet-node-level toggle aignet)))
               (equal (let ((toggles (cons toggle toggles))) <call>)
                      val))
      :hints ('(:expand ((:free (toggles) <call>))))
      :fn eval-and-of-lits-toggle)
    (defret <fn>-add-toggle-when-level-greater
      (implies (and (< (aignet-node-level (lit->var lit1) aignet) (aignet-node-level toggle aignet))
                    (< (aignet-node-level (lit->var lit2) aignet) (aignet-node-level toggle aignet)))
               (equal (let ((toggles (cons toggle toggles))) <call>)
                      val))
      :hints ('(:expand ((:free (toggles) <call>))))
      :fn eval-xor-of-lits-toggle)))


(define output-eval-toggle ((n natp) (toggles nat-listp) invals regvals aignet)
  :guard (and (< n (num-outs aignet))
              (<= (num-ins aignet) (bits-length invals))
              (<= (num-regs aignet) (bits-length regvals)))
  (lit-eval-toggle (outnum->fanin n aignet) toggles invals regvals aignet))

(define nxst-eval-toggle ((n natp) (toggles nat-listp) invals regvals aignet)
  :guard (and (< n (num-regs aignet))
              (<= (num-ins aignet) (bits-length invals))
              (<= (num-regs aignet) (bits-length regvals)))
  (lit-eval-toggle (regnum->nxst n aignet) toggles invals regvals aignet))

