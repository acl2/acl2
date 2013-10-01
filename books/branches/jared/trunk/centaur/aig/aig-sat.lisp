; Centaur AIG Library
; Copyright (C) 2008-2013 Centaur Technology
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
; Original authors: Jared Davis <jared@centtech.com>
;                   Sol Swords <sswords@centtech.com>

(in-package "ACL2")
(include-book "centaur/aignet/aig-cnf" :dir :system)
(include-book "centaur/satlink/top" :dir :system)
(local (include-book "centaur/satlink/cnf-basics" :dir :system))
(local (in-theory (disable nth update-nth aig-eval)))

(define aig-sat
  :parents (aig)
  :short "Determine whether an AIG is satisfiable."
  ((aig "The AIG to inspect.")
   &key
   ((config satlink::config-p "How to invoke the SAT solver.")
    'satlink::*default-config*))
  :returns (mv (status "Either :sat, :unsat, or :failed")
               (env    "When :sat, an (ordinary, slow) alist binding the
                        aig vars to t/nil."))

  :long "<p>This is a convenient, high level way to ask a SAT solver whether a
Hons AIG is satisfiable.  When the AIG is satisfiable, you get back a
satisfying assignment in terms of the Hons AIG's variables.</p>

<p>This function should only fail if there is some problem with the SAT solver,
e.g., it produces output that @(see satlink) does not understand.</p>

<p>The underlying mechanism takes advantage of @(see aignet) to carry out the
<see topic='@(url aignet-cnf)'>cnf conversion</see> and @(see satlink) to call
the SAT solver.  As a picture:</p>

@({
           convert                export              dimacs
    AIG -------------> AIGNET -----------------> CNF -------> Solver
     ||                  ||                       ||            |
     ||                  ||                       ||            | interpret
  satisfying          satisfying               satisfying       |  output
   alist or  <-------  array or   <-----------  assign or  <----'
   'unsat'    convert  'unsat'      translate   'unsat'
})

<p>We simply trust the SAT solver if it says @('unsat'), but the other
translation and conversion steps are all verified.</p>"

  (b* (;; Locally create arrays to work with
       ((local-stobjs satlink::env$ aignet::sat-lits aignet::aignet)
        (mv status env satlink::env$ aignet::sat-lits aignet::aignet))

       ;; Convert the AIG into a CNF formula, using fancy AIGNET algorithm
       ((mv cnf ?lit vars aignet::sat-lits aignet::aignet)
        (aignet::aig->cnf aig aignet::sat-lits aignet::aignet))

       ((mv result satlink::env$)
        (satlink::sat cnf satlink::env$ :config config))

       ((unless (eq result :sat))
        (mv result nil satlink::env$ aignet::sat-lits aignet))

       (env (aignet::aig-cnf-vals->env satlink::env$ vars aignet::sat-lits aignet)))

    (mv :sat env satlink::env$ aignet::sat-lits aignet))

  ///
  (defthm aig-sat-when-sat
    (b* (((mv status env) (aig-sat aig :config config)))
      (implies (equal status :sat)
               (aig-eval aig env))))

  (defthm aig-sat-when-unsat
    (b* (((mv status &) (aig-sat aig :config config)))
      (implies (aig-eval aig env)
               (not (equal status :unsat))))
    :hints (("goal"
             :use ((:instance
                    aignet::aig-satisfying-assign-induces-aig->cnf-satisfying-assign
                    (aignet::aig      aig)
                    (aignet::env      env)
                    (aignet::sat-lits (aignet::create-sat-lits))
                    (aignet::aignet   (acl2::create-aignet))))
             :in-theory (disable
                         aignet::aig-satisfying-assign-induces-aig->cnf-satisfying-assign)))))


