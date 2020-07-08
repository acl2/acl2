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
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))



(defines id-eval-toggle
  :prepwork ((local (in-theory (disable lookup-id-in-bounds-when-positive
                                        lookup-id-out-of-bounds))))
  :ruler-extenders :lambdas
  (define lit-eval-toggle ((lit litp) (toggle natp) invals regvals aignet)
    :guard (and (fanin-litp lit aignet)
                (<= (num-ins aignet) (bits-length invals))
                (<= (num-regs aignet) (bits-length regvals)))
    :measure (acl2::two-nats-measure (lit-id lit) 1)
    :verify-guards nil
    (b-xor (id-eval-toggle (lit-id lit) toggle invals regvals aignet)
           (lit-neg lit)))

  (define eval-and-of-lits-toggle ((lit1 litp)
                            (lit2 litp)
                            (toggle natp)
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
    (b-and (lit-eval-toggle lit1 toggle invals regvals aignet)
           (lit-eval-toggle lit2 toggle invals regvals aignet)))

  (define eval-xor-of-lits-toggle ((lit1 litp)
                            (lit2 litp)
                            (toggle natp)
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
    (b-xor (lit-eval-toggle lit1 toggle invals regvals aignet)
           (lit-eval-toggle lit2 toggle invals regvals aignet)))

  (define id-eval-toggle ((id natp) (toggle natp) invals regvals aignet)
    :guard (and (id-existsp id aignet)
                (<= (num-ins aignet) (bits-length invals))
                (<= (num-regs aignet) (bits-length regvals)))
    :measure (acl2::two-nats-measure id 0)
    :hints(("Goal" :in-theory (enable aignet-idp)))
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
                            f0 f1 toggle invals regvals aignet)
                         (eval-and-of-lits-toggle
                          f0 f1 toggle invals regvals aignet)))
               :in    (if (int= (id->regp id aignet) 1)
                          (get-bit (ci-id->ionum id aignet) regvals)
                        (get-bit (ci-id->ionum id aignet) invals))
               :const 0))))
      (if (eql (lnfix id) (lnfix toggle))
          (b-not ans)
        ans)))
  ///
  (fty::deffixequiv-mutual id-eval-toggle)
  (verify-guards id-eval-toggle)

  (defthm id-eval-toggle-when-less
    (implies (< (nfix x) (nfix toggle))
             (equal (id-eval-toggle x toggle invals regvals aignet)
                    (id-eval x invals regvals aignet)))
    :hints (("goal" :induct (id-eval-ind x aignet)
             :expand ((id-eval x invals regvals aignet)
                      (id-eval-toggle x toggle invals regvals aignet)
                      (:free (x) (lit-eval x invals regvals aignet))
                      (:free (x y) (lit-eval-toggle x y invals regvals aignet))
                      (:free (x y) (eval-and-of-lits x y invals regvals aignet))
                      (:free (x y z) (eval-and-of-lits-toggle x y z invals regvals aignet))
                      (:free (x y) (eval-xor-of-lits x y invals regvals aignet))
                      (:free (x y z) (eval-xor-of-lits-toggle x y z invals regvals aignet))))))

  (defthm id-eval-toggle-when-level-less
    (implies (< (aignet-node-level x aignet) (aignet-node-level toggle aignet))
             (equal (id-eval-toggle x toggle invals regvals aignet)
                    (id-eval x invals regvals aignet)))
    :hints (("goal" :induct (id-eval-ind x aignet)
             :expand ((id-eval x invals regvals aignet)
                      (aignet-node-level x aignet)
                      (id-eval-toggle x toggle invals regvals aignet)
                      (:free (x) (lit-eval x invals regvals aignet))
                      (:free (x y) (lit-eval-toggle x y invals regvals aignet))
                      (:free (x y) (eval-and-of-lits x y invals regvals aignet))
                      (:free (x y z) (eval-and-of-lits-toggle x y z invals regvals aignet))
                      (:free (x y) (eval-xor-of-lits x y invals regvals aignet))
                      (:free (x y z) (eval-xor-of-lits-toggle x y z invals regvals aignet))))
            (and stable-under-simplificationp
                 '(:expand ((aignet-node-level toggle aignet)))))))



(define output-eval-toggle ((n natp) (toggle natp) invals regvals aignet)
  :guard (and (< n (num-outs aignet))
              (<= (num-ins aignet) (bits-length invals))
              (<= (num-regs aignet) (bits-length regvals)))
  (lit-eval-toggle (outnum->fanin n aignet) toggle invals regvals aignet))

(define nxst-eval-toggle ((n natp) (toggle natp) invals regvals aignet)
  :guard (and (< n (num-regs aignet))
              (<= (num-ins aignet) (bits-length invals))
              (<= (num-regs aignet) (bits-length regvals)))
  (lit-eval-toggle (regnum->nxst n aignet) toggle invals regvals aignet))

