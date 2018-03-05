; Centaur AIG Library
; Copyright (C) 2008-2013 Centaur Technology
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
; Original authors: Jared Davis <jared@centtech.com>
;                   Sol Swords <sswords@centtech.com>

(in-package "ACL2")
(include-book "centaur/aignet/aig-cnf" :dir :system)
(include-book "centaur/satlink/top" :dir :system)
(local (include-book "centaur/satlink/cnf-basics" :dir :system))
(local (in-theory (disable nth update-nth aig-eval)))



(local (defthm true-listp-accumulate-aig-vars
         (equal (true-listp (mv-nth 1 (acl2::accumulate-aig-vars x nodetable acc)))
                (true-listp acc))
         :hints(("Goal" :in-theory (enable acl2::accumulate-aig-vars)))))

(define aig-sat
  :parents (aig)
  :short "Determine whether an AIG is satisfiable."
  ((aig "The AIG to inspect.")
   &key
   ((config satlink::config-p "How to invoke the SAT solver.")
    'satlink::*default-config*)
   ((gatesimp aignet::gatesimp-p) '(aignet::default-gatesimp))
   ((transform-config) 'nil))
  :returns (mv (status "Either :sat, :unsat, or :failed")
               (env    "When :sat, an (ordinary, slow) alist binding the
                        aig vars to t/nil."))

  :long "<p>This is a convenient, high level way to ask a SAT solver whether a
Hons AIG is satisfiable.  When the AIG is satisfiable, you get back a
satisfying assignment in terms of the Hons AIG's variables.</p>

<p>This function should only fail if there is some problem with the SAT solver,
e.g., it produces output that @(see satlink) does not understand.</p>

<p>The underlying mechanism takes advantage of @(see aignet) to carry out the
<see topic='@(url aignet::aignet-cnf)'>cnf conversion</see> and @(see satlink)
to call the SAT solver.  As a picture:</p>

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
        (aignet::aig->cnf aig aignet::sat-lits aignet::aignet :transform-config transform-config :gatesimp gatesimp))

       ((mv result satlink::env$)
        (satlink::sat cnf satlink::env$ :config config))

       ((unless (eq result :sat))
        (mv result nil satlink::env$ aignet::sat-lits aignet))

       (env (aignet::aig-cnf-vals->env satlink::env$ vars aignet::sat-lits aignet)))

    (mv :sat env satlink::env$ aignet::sat-lits aignet))

  ///
  (defthm aig-sat-when-sat
    (b* (((mv status env) (aig-sat aig :config config :transform-config transform-config :gatesimp gatesimp)))
      (implies (equal status :sat)
               (aig-eval aig env)))
    :hints(("Goal" :in-theory (disable aignet::vars-of-aig->cnf))))

  (defthm aig-sat-when-unsat
    (b* (((mv status &) (aig-sat aig :config config :transform-config transform-config :gatesimp gatesimp)))
      (implies (aig-eval aig env)
               (not (equal status :unsat))))
    :hints (("goal"
             :use ((:instance
                    aignet::aig-satisfying-assign-induces-aig->cnf-satisfying-assign
                    (aig      aig)
                    (env      env)
                    (gatesimp gatesimp)
                    (transform-config transform-config)
                    (sat-lits (aignet::create-sat-lits))
                    (aignet   (acl2::create-aignet))))
             :in-theory (disable
                         aignet::aig-satisfying-assign-induces-aig->cnf-satisfying-assign)))))


