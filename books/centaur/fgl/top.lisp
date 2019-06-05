; GL - A Symbolic Simulation Framework for ACL2
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

(in-package "FGL")

(include-book "clauseproc")
(include-book "def-gl-rewrite")
;; (include-book "subst-functions")
(include-book "primitives")
(include-book "fgarrays")
(include-book "aig-eval")
(include-book "ipasir-sat")
(include-book "satlink-sat")
(include-book "ctrex-utils")

;; ----------------------------------------------------------------------
;; Install GL primitives:  This event collects the primitives defined in
;; primitives, fgarrays, and fast-alists and defines a new function
;; top-primitive-fncall, which is attached to gl-primitive-fncall-stub.
;; This event may be repeated later (with a different prefix instead of top)
;; to install more primitives.

(install-gl-primitives top)



;; ----------------------------------------------------------------------
;; Def-fancy-ev-primitives.  This event collects the functions that are stored
;; in the fancy-ev-primitives table (added by fancy-ev-add-primitive) and
;; installs them in a new function that is attached to fancy-ev-primitive.
;; These functions can then be used in syntax-bind forms.  (They could be used
;; in syntaxp/bind-free forms as well, but at the moment those won't be
;; translated if interp-st is used.)
(fancy-ev-add-primitive interp-st-prev-bindings
                        (< 1 (interp-st-stack-frames interp-st)))

(fancy-ev-add-primitive interp-st-sat-counterexample t)
(fancy-ev-add-primitive interp-st-monolithic-sat-counterexample t)

(fancy-ev-add-primitive interp-st-counterex-stack-prev-bindings/print-errors
                        (< 1 (interp-st-stack-frames interp-st)))

(fancy-ev-add-primitive interp-st-counterex-bindings/print-errors
                        (and (gl-object-bindings-p x)
                             (interp-st-bfr-listp (gl-object-bindings-bfrlist x))))

(fancy-ev-add-primitive interp-st-counterex-stack-bindings/print-errors t)

(fancy-ev-add-primitive interp-st-counterex-bindings
                        (and (gl-object-bindings-p x)
                             (interp-st-bfr-listp (gl-object-bindings-bfrlist x))))

(fancy-ev-add-primitive interp-st-counterex-stack-bindings t)

(fancy-ev-add-primitive get-global (and (symbolp x)
                                        (boundp-global x state)))

(def-fancy-ev-primitives counterex-primitives)



(defun show-counterexample (msg)
  (declare (ignore msg))
  nil)

(table gl-fn-modes 'show-counterexample
       (make-gl-function-mode :dont-concrete-exec t))

(def-gl-rewrite show-counterexample-rw
  (equal (show-counterexample msg)
         (b* (((list error bindings vars)
               (syntax-bind alists
                            (b* (((mv sat-ctrex-err interp-st)
                                  (interp-st-sat-counterexample interp-st state))
                                 ((when sat-ctrex-err)
                                  (g-concrete
                                   (list (msg "error getting SAT counterexample: ~@0" sat-ctrex-err)
                                         nil nil)))
                                 ((mv bindings-vals var-vals)
                                  (interp-st-counterex-stack-prev-bindings/print-errors interp-st state)))
                              (g-concrete (list nil bindings-vals var-vals)))))
              ((when error)
               (cw "~@0: ~@1" msg error)))
           (cw "~@0: Counterexample -- bindings: ~x1 variables: ~x2~%"
               msg bindings vars))))


;; Convenience macro to create a glcp-config object that captures the current
;; definitions, rewrite rules, branch merge rules, and function modes from
;; their respective tables.
(defmacro default-glcp-config ()
  '(make-glcp-config
    :rewrite-rule-table (table-alist 'gl-rewrite-rules (w state))
    :definition-table (table-alist 'gl-definition-rules (w state))
    :branch-merge-rules (table-alist 'gl-branch-merge-rules (w state))
    :function-modes (table-alist 'gl-fn-modes (w state))
    :trace-rewrites (and (boundp-global :fgl-trace-rewrites state)
                         (@ :fgl-trace-rewrites))))

