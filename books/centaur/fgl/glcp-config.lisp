; GL - A Symbolic Simulation Framework for ACL2
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
; Original author: Sol Swords <sswords@centtech.com>

(in-package "FGL")
;; (include-book "shape-spec-defs")
(include-book "centaur/fty/deftypes" :dir :system)
(include-book "centaur/fty/basetypes" :dir :system)

(include-book "centaur/fty/bitstruct" :dir :system)

(fty::defbitstruct gl-function-mode
  :parents (fgl)
  :short "Limitations on what the FGL interpreter will do to resolve a call of a given function."
  ((dont-concrete-exec booleanp
    "If true, skip attempting to concretely execute the function in the case when
     all the arguments are explicit.")
   (dont-expand-def booleanp
    "If true, skip expanding the function's definition after attempting ~
     rewrites and primitive execution.")
   (dont-rewrite booleanp
    "If true, skip applying rewrite rules to calls of the function.")
   (dont-rewrite-under-if-test booleanp
    "If true, skip applying rewrite rules to calls of the function when trying
     to resolve an IF test to a Boolean formula.")
   (dont-primitive-exec booleanp
    "If true, skip applying primitives to calls of the function.")))

(fty::defmap gl-function-mode-alist :key-type symbolp :val-type gl-function-mode :true-listp t)

(define gl-function-mode-lookup ((fn symbolp)
                                 (alist gl-function-mode-alist-p))
  :returns (mode gl-function-mode-p)
  (or (cdr (hons-get fn (make-fast-alist (gl-function-mode-alist-fix alist)))) 0))

(defprod glcp-config
  ((trace-rewrites booleanp :default nil)
   (reclimit posp :rule-classes (:rewrite :type-prescription) :default 1000000)
   (make-ites booleanp :default nil)
   (rewrite-rule-table :default nil)
   (definition-table :default nil)
   (branch-merge-rules :default nil)
   (function-modes :default nil gl-function-mode-alist)
   (prof-enabledp booleanp :default t)
   (sat-config)


   (abort-indeterminate booleanp :default t)
   (abort-ctrex booleanp :default t)
   (exec-ctrex booleanp :default t)
   (ctrex-transform :default '(lambda (x) x))
   (abort-vacuous booleanp :default t)
   (check-vacuous booleanp :default t)

   (n-counterexamples natp :rule-classes (:rewrite :type-prescription) :default 3)
   (hyp-clk posp :rule-classes (:rewrite :type-prescription) :default 1000000)
   (clause-proc symbolp :rule-classes (:rewrite :type-prescription))
   (overrides) ;;  acl2::interp-defs-alistp but might be too expensive to check
     ;;  the guards in clause processors
   (param-bfr :default t)
   (term-level-counterexample-scheme symbolp :default :depgraph)
   top-level-term
   ;; (shape-spec-alist shape-spec-bindingsp)
   run-before-cases
   run-after-cases
   case-split-override
   (lift-ifsp booleanp :default t)
   (split-conses booleanp :default nil)
   (split-fncalls booleanp :default nil)
   
   )
  :layout :tree)


(defund-inline glcp-config-update-param (p config)
  (declare (xargs :guard (glcp-config-p config)))
  (change-glcp-config config :param-bfr p))

(defthm param-bfr-of-glcp-config-update-param
  (equal (glcp-config->param-bfr (glcp-config-update-param p config))
         p)
  :hints(("Goal" :in-theory (enable glcp-config-update-param))))

(defthm glcp-config->overrides-of-glcp-config-update-param
  (equal (glcp-config->overrides (glcp-config-update-param p config))
         (glcp-config->overrides config))
  :hints(("Goal" :in-theory (enable glcp-config-update-param))))

(defthm glcp-config->top-level-term-of-glcp-config-update-param
  (equal (glcp-config->top-level-term (glcp-config-update-param p config))
         (glcp-config->top-level-term config))
  :hints(("Goal" :in-theory (enable glcp-config-update-param))))



(defund-inline glcp-config-update-term (term config)
  (declare (xargs :guard (glcp-config-p config)))
  (change-glcp-config config :top-level-term term))

(defthm param-bfr-of-glcp-config-update-term
  (equal (glcp-config->param-bfr (glcp-config-update-term term config))
         (glcp-config->param-bfr config))
  :hints(("Goal" :in-theory (enable glcp-config-update-term))))

(defthm glcp-config->overrides-of-glcp-config-update-term
  (equal (glcp-config->overrides (glcp-config-update-term term config))
         (glcp-config->overrides config))
  :hints(("Goal" :in-theory (enable glcp-config-update-term))))

(defthm glcp-config->top-level-term-of-glcp-config-update-term
  (equal (glcp-config->top-level-term (glcp-config-update-term term config))
         term)
  :hints(("Goal" :in-theory (enable glcp-config-update-term))))


