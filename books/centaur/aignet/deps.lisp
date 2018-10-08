; AIGNET - And-Inverter Graph Networks
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
; Original author: Sol Swords <sswords@centtech.com>

(in-package "AIGNET")
(include-book "semantics")
;; (include-book "construction")

(local (std::add-default-post-define-hook :fix))

(define depends-on ((id natp)
                    (ci-id natp)
                    aignet)
  :guard (and (id-existsp id aignet)
              (id-existsp ci-id aignet))
  :measure (nfix id)
  (aignet-case (id->type id aignet)
    :gate (or (depends-on (lit->var (gate-id->fanin0 id aignet)) ci-id aignet)
              (depends-on (lit->var (gate-id->fanin1 id aignet)) ci-id aignet))
    :ci (equal (lnfix ci-id) (lnfix id))
    :const nil)
  ///
  (defthm depends-on-of-extension
    (implies (and (aignet-extension-binding)
                  (aignet-idp id orig))
             (equal (depends-on id ci-id new)
                    (depends-on id ci-id orig)))
    :hints (("goal" :induct (depends-on id ci-id new))))

  (defthm id-eval-of-update-ins-when-not-depends-on
    (implies (and (not (depends-on id ci-id aignet))
                  (equal (stype (car (lookup-id ci-id aignet))) (pi-stype))
                  (equal (stype-count :pi (cdr (lookup-id ci-id aignet))) (nfix n)))
             (equal (id-eval id (update-nth n val invals) regvals aignet)
                    (id-eval id invals regvals aignet)))
    :hints (("goal" :induct (id-eval-ind id aignet)
             :expand ((:free (invals) (id-eval id invals regvals aignet))
                      (:free (lit invals regvals) (lit-eval lit invals regvals aignet))
                      (:free (lit1 lit2 invals regvals) (eval-and-of-lits lit1 lit2 invals regvals aignet))
                      (:free (lit1 lit2 invals regvals) (eval-xor-of-lits lit1 lit2 invals regvals aignet))))))

  (defthm lit-eval-of-update-ins-when-not-depends-on
    (implies (and (not (depends-on (lit->var lit) ci-id aignet))
                  (equal (stype (car (lookup-id ci-id aignet))) (pi-stype))
                  (equal (stype-count :pi (cdr (lookup-id ci-id aignet))) (nfix n)))
             (equal (lit-eval lit (update-nth n val invals) regvals aignet)
                    (lit-eval lit invals regvals aignet)))
    :hints (("goal" 
             :expand ((:free (lit invals regvals) (lit-eval lit invals regvals aignet))))))

  (defthm id-eval-of-update-regs-when-not-depends-on
    (implies (and (not (depends-on id ci-id aignet))
                  (equal (stype (car (lookup-id ci-id aignet))) (reg-stype))
                  (equal (stype-count :reg (cdr (lookup-id ci-id aignet))) (nfix n)))
             (equal (id-eval id invals (update-nth n val regvals) aignet)
                    (id-eval id invals regvals aignet)))
    :hints (("goal" :induct (id-eval-ind id aignet)
             :expand ((:free (regvals) (id-eval id invals regvals aignet))
                      (:free (lit invals regvals) (lit-eval lit invals regvals aignet))
                      (:free (lit1 lit2 invals regvals) (eval-and-of-lits lit1 lit2 invals regvals aignet))
                      (:free (lit1 lit2 invals regvals) (eval-xor-of-lits lit1 lit2 invals regvals aignet))))))

  (defthm lit-eval-of-update-regs-when-not-depends-on
    (implies (and (not (depends-on (lit->var lit) ci-id aignet))
                  (equal (stype (car (lookup-id ci-id aignet))) (reg-stype))
                  (equal (stype-count :reg (cdr (lookup-id ci-id aignet))) (nfix n)))
             (equal (lit-eval lit invals (update-nth n val regvals) aignet)
                    (lit-eval lit invals regvals aignet)))
    :hints (("goal" 
             :expand ((:free (lit invals regvals) (lit-eval lit invals regvals aignet))))))

  (defthm depends-on-of-0
    (not (depends-on 0 n aignet)))

  (defthm depends-on-of-fanin
    (implies (and (not (depends-on id ci-id aignet))
                  (equal (ctype (stype (car (lookup-id id aignet)))) (gate-ctype)))
             (and (not (depends-on (lit->var (fanin :gate0 (lookup-id id aignet))) ci-id aignet))
                  (not (depends-on (lit->var (fanin :gate1 (lookup-id id aignet))) ci-id aignet)))))

  (defthm depends-on-of-id-fix
    (equal (depends-on (aignet-id-fix id aignet) ci-id aignet)
           (depends-on id ci-id aignet))
    :hints(("Goal" :in-theory (enable aignet-id-fix)))))
