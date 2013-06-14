; AIGNET - And-Inverter Graph Networks
; Copyright (C) 2013 Centaur Technology
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

(in-package "AIGNET")

(include-book "aig-cnf")
(include-book "centaur/satlink/top" :dir :system)

(local (include-book "centaur/satlink/cnf-basics" :dir :system))

(local (in-theory (disable nth update-nth aig-eval)))

(define aig-sat ((aig "any old aig")
                 &key
                 ((config satlink::config-p) 'satlink::*default-config*))
  :returns (mv (status "one of :sat, :unsat, or :failed")
               (env    "alist binding aig vars to t/nil, when sat"))
  :guard-debug t
  (b* (;; Locally create arrays to work with
       ((local-stobjs satlink::env$ sat-lits aignet)
        (mv status env satlink::env$ sat-lits aignet))

       ;; Convert the AIG into a CNF formula, using fancy AIGNET algorithm
       ((mv cnf ?lit vars sat-lits aignet)
        (aig->cnf aig sat-lits aignet))

       ((mv result satlink::env$)
        (satlink::sat cnf satlink::env$ :config config))

       ((unless (eq result :sat))
        (mv result nil satlink::env$ sat-lits aignet))

       (env (aig-cnf-vals->env satlink::env$ vars sat-lits aignet)))

    (mv :sat env satlink::env$ sat-lits aignet))

  ///
  (defthm aig-sat-when-sat
    (implies (eq (mv-nth 0 (aig-sat aig :config config)) :sat)
             (aig-eval aig (mv-nth 1 (aig-sat aig :config config)))))

  (defthm aig-sat-when-unsat
    (implies (aig-eval aig env)
             (not (equal (mv-nth 0 (aig-sat aig :config config)) :unsat)))
    :hints (("goal" :use ((:instance aig-satisfying-assign-induces-aig->cnf-satisfying-assign
                                     (sat-lits (create-sat-lits))
                                     (aignet (acl2::create-aignet))))
             :in-theory (disable aig-satisfying-assign-induces-aig->cnf-satisfying-assign)))))



#||

(in-package "ACL2")

(tshell-ensure)

(aignet::aig-sat nil)
(aignet::aig-sat 'x)

(aignet::aig-sat (aig-and 'x 'y))

(aignet::aig-sat (aig-ite 'x 'y 'z))

(aignet::aig-sat (aig-and
                   (aig-ite 'x 'y 'z)
                   (aig-ite 'x (aig-not 'y) (aig-not 'z))))

(aignet::aig-sat '(1 2 3 4 5 2))


||#
