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
(include-book "def-fgl-thm")
(include-book "def-gl-rewrite")
;; (include-book "subst-functions")
(include-book "primitives")
(include-book "fgarrays")
(include-book "aig-eval")
(include-book "sat-default")
(include-book "ctrex-utils")
(include-book "doc")
(include-book "pathcond-fix")
(include-book "def-fgl-thm")
(include-book "centaur/aignet/transform-utils" :dir :system)
(local (in-theory (disable w)))

;; ----------------------------------------------------------------------
;; Install GL primitives:  This event collects the primitives defined in
;; primitives, fgarrays, and fast-alists and defines a new function
;; top-primitive-fncall, which is attached to gl-primitive-fncall-stub.
;; This event may be repeated later (with a different prefix instead of top)
;; to install more primitives.

(install-gl-primitives top)
(install-gl-metafns top)



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

(fancy-ev-add-primitive gl-interp-store-debug-info (not (eq msg :unreachable)))

(define interp-st-print-aignet-stats ((name stringp) interp-st)
  (stobj-let ((logicman (interp-st->logicman interp-st)))
             (ans)
             (stobj-let ((aignet (logicman->aignet logicman)))
                        (ans)
                        (aignet::print-aignet-stats name aignet)
                        ans)
             ans))

(fancy-ev-add-primitive interp-st-print-aignet-stats (stringp name))

(fancy-ev-add-primitive magitastic-ev (and (pseudo-termp x)
                                           (symbol-alistp alist)
                                           (natp reclimit)))

(fancy-ev-add-primitive interp-st->user-scratch$inline t)

(fancy-ev-add-primitive gl-interp-store-debug-info (not (eq msg :unreachable)))

(def-fancy-ev-primitives counterex-primitives)



(disable-definition show-counterexample)

(disable-definition show-top-counterexample)

;; Note: this function will just get interpreted by fancy-ev when running under
;; show-counterexample-rw below, so we don't bother verifying guards etc.
(define show-counterexample-bind ((params gl-object-p)
                                  (interp-st interp-st-bfrs-ok)
                                  state)
  :verify-guards nil
  (b* (((unless (gl-object-case params :g-concrete))
        (mv (list (msg "error: params provided were not concrete-valued") nil nil) interp-st))
       (params (g-concrete->val params))
       ((mv sat-ctrex-err interp-st)
        (interp-st-sat-counterexample params interp-st state))
       ((when sat-ctrex-err)
        (mv (g-concrete
             (list (msg "error getting SAT counterexample: ~@0" sat-ctrex-err)
                   nil nil))
            interp-st))
       ((mv bindings-vals var-vals interp-st)
        (interp-st-counterex-stack-prev-bindings/print-errors interp-st state)))
    (mv (g-concrete (list nil bindings-vals var-vals)) interp-st)))

(def-gl-rewrite show-counterexample-rw
  (equal (show-counterexample params msg)
         (b* (((list (list error bindings vars) &)
               (syntax-bind alists
                            (show-counterexample-bind params interp-st state)))
              ((when error)
               (cw "~@0: ~@1" msg error)))
           (cw "~@0: Counterexample -- bindings: ~x1 variables: ~x2~%"
               msg bindings vars))))



;; Note: this function will just get interpreted by fancy-ev when running under
;; show-counterexample-rw below, so we don't bother verifying guards etc.
(define show-top-counterexample-bind ((params gl-object-p)
                                      (interp-st interp-st-bfrs-ok)
                                      state)
  :verify-guards nil
  (b* (((unless (gl-object-case params :g-concrete))
        (mv (list (msg "error: params provided were not concrete-valued") nil nil) interp-st))
       (params (g-concrete->val params))
       ((mv sat-ctrex-err interp-st)
        (interp-st-sat-counterexample params interp-st state))
       ((when sat-ctrex-err)
        (mv (g-concrete
             (list (msg "error getting SAT counterexample: ~@0" sat-ctrex-err)
                   nil nil))
            interp-st))
       ((mv bindings-vals var-vals interp-st)
        (interp-st-counterex-stack-bindings/print-errors interp-st state)))
    (mv (g-concrete (list nil bindings-vals var-vals)) interp-st)))

(def-gl-rewrite show-top-counterexample-rw
  (equal (show-top-counterexample params msg)
         (b* (((list (list error bindings vars) &)
               (syntax-bind alists
                            (show-top-counterexample-bind params interp-st state)))
              ((when error)
               (cw "~@0: ~@1" msg error)))
           (cw "~@0: Counterexample -- bindings: ~x1 variables: ~x2~%"
               msg bindings vars))))


(define fgl-sat-check/print-counterexample (params msg x)
  :parents (fgl-solving)
  :short "Check satisfiability during FGL interpretation and print counterexamples."
  :long "
<p>Similar to @(see fgl-sat-check), but this version additionally prints the
counterexample bindings, when satisfiable, for the context from which it was
called.  Its functionality depends on the rewrite rule
@('fgl-sat-check/print-counterexample-rw').  The extra argument @('msg') should
be a string or message identifying the particular SAT check.</p>"
  (declare (ignore params msg))
  (if x t nil)
  ///

  (disable-definition fgl-sat-check/print-counterexample)

  (def-gl-rewrite fgl-sat-check/print-counterexample-rw
    (equal (fgl-sat-check/print-counterexample params msg x)
           (b* ((ans (fgl-sat-check params x))
                (unsatp (syntax-bind unsat (eq ans nil)))
                ((when unsatp) ans)
                ((list (list error bindings vars) &)
                 (syntax-bind alists
                              (show-counterexample-bind params interp-st state)))
                ((when error)
                 (b* ((?ignore (cw "~@0: ~@1" msg error)))
                   ans))
                (?ignore (cw "~@0: Counterexample -- bindings: ~x1 variables: ~x2~%"
                             msg bindings vars)))
             ans))
    :hints(("Goal" :in-theory (enable fgl-sat-check)))))




(table fgl-config-table)

(define glcp-config-lookup ((table-key symbolp)
                            (state-key symbolp)
                            default
                            (alist alistp)
                            state)
  (b* (((when (boundp-global state-key state))
        (f-get-global state-key state))
       (look (assoc table-key alist))
       ((when look) (cdr look)))
    default))
        

;; Convenience macro to create a glcp-config object that captures the current
;; definitions, rewrite rules, branch merge rules, and function modes from
;; their respective tables.
(defmacro default-glcp-config ()
  '(b* ((configtab (table-alist 'fgl-config-table (w state))))
     (make-glcp-config
      :rewrite-rule-table (table-alist 'gl-rewrite-rules (w state))
      :definition-table (table-alist 'gl-definition-rules (w state))
      :branch-merge-rules (cdr (assoc 'FGL::GL-BRANCH-MERGE-RULES (table-alist 'gl-branch-merge-rules (w state))))
      :function-modes (table-alist 'gl-fn-modes (w state))
      :trace-rewrites (glcp-config-lookup :trace-rewrites :fgl-trace-rewrites nil configtab state)
      :reclimit (glcp-config-lookup :reclimit :fgl-reclimit 10000 configtab state)
      :make-ites (glcp-config-lookup :make-ites :fgl-make-ites nil configtab state)
      :prof-enabledp (glcp-config-lookup :prof-enabledp :fgl-prof-enabledp t configtab state)
      :sat-config (glcp-config-lookup :sat-config :fgl-sat-config nil configtab state))))



;; Debugging utilities

(define interp-st-extract-stack (interp-st)
  (stobj-let ((stack (interp-st->stack interp-st)))
             (stk)
             (stack-extract stack)
             stk))

(define major-stack->debug ((x major-stack-p))
  :measure (len x)
  :ruler-extenders (cons)
  (cons (major-frame->debug (car x))
        (and (consp (cdr x))
             (major-stack->debug (cdr x)))))

(define major-stack->debugframes-aux ((n natp) (x major-stack-p))
  :measure (len x)
  :ruler-extenders (cons)
  (cons (cons (lnfix n) (major-frame->debug (car x)))
        (and (consp (cdr x))
             (major-stack->debugframes-aux (1+ (lnfix n)) (cdr x)))))

(define major-stack->debugframes ((x major-stack-p))
  (major-stack->debugframes-aux 0 x))

(define interp-st-extract-bvar-db (interp-st)
  (stobj-let ((bvar-db (interp-st->bvar-db interp-st)))
             (db)
             (bvar-db-debug bvar-db)
             db))


(defmacro fgl-error! (&key msg debug-obj)
  `(syntax-interp
    (b* ((interp-st 'interp-st)) ;; fake
      (gl-interp-store-debug-info ,msg ,debug-obj interp-st))))

(defmacro fgl-error (&key msg debug-obj)
  `(fgl-prog2 (fgl-error! :msg ,msg :debug-obj ,debug-obj)
              nil))

(defmacro fgl-assert! (cond &key msg debug-obj)
  `(if ,cond
       nil
     (fgl-error!
      ,@(if msg
            `(:msg ,msg)
          `(:msg (gl-msg "Assertion failed: ~x0" ',cond)))
      ,@(if debug-obj
            `(:debug-obj ,debug-obj)
          `(:debug-obj ',cond)))))

(defmacro fgl-assert (cond &key msg debug-obj)
  `(fgl-prog2 (fgl-assert! :cond ,cond :msg ,msg :debug-obj ,debug-obj)
              nil))

(defmacro with-branch-on-if-flag (flag term)
  `(b* (((list fgl-with-branch-on-if-flag &)
         (syntax-interp
          (b* ((interp-st 'interp-st) ;; hack
               (flags (interp-st->flags interp-st))
               (flag (interp-flags->branch-on-ifs flags))
               (new-flags (!interp-flags->branch-on-ifs ,flag flags)))
            (list flag
                  (update-interp-st->flags new-flags interp-st)))))
        (ans ,term)
        (?fgl-interp-ignore
         (b* ((interp-st 'interp-st)
              (flags (interp-st->flags interp-st))
              (new-flags (!interp-flags->branch-on-ifs fgl-with-branch-on-if-flag flags)))
           (update-interp-st->flags new-flags interp-st))))
     ans))

(defmacro with-fgl-testbench! (term)
  `(with-branch-on-if-flag nil ,term))

(defmacro with-fgl-testbench (term)
  `(fgl-prog2 (with-fgl-testbench! ,term) nil))

(defmacro without-fgl-testbench! (term)
  `(with-branch-on-if-flag t ,term))

(defmacro without-fgl-testbench (term)
  `(with-branch-on-if-flag t (narrow-equiv nil ,term)))
