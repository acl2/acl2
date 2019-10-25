; FGL - A Symbolic Simulation Framework for ACL2
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
(include-book "def-fgl-rewrite")
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
;; Install FGL primitives:  This event collects the primitives defined in
;; primitives, fgarrays, and fast-alists and defines a new function
;; top-primitive-fncall, which is attached to fgl-primitive-fncall-stub.
;; This event may be repeated later (with a different prefix instead of top)
;; to install more primitives.

(install-fgl-metafns top)



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
                        (and (fgl-object-bindings-p x)
                             (interp-st-bfr-listp (fgl-object-bindings-bfrlist x))))

(fancy-ev-add-primitive interp-st-counterex-stack-bindings/print-errors t)

(fancy-ev-add-primitive interp-st-counterex-bindings
                        (and (fgl-object-bindings-p x)
                             (interp-st-bfr-listp (fgl-object-bindings-bfrlist x))))

(fancy-ev-add-primitive interp-st-counterex-stack-bindings t)

(fancy-ev-add-primitive get-global (and (symbolp x)
                                        (boundp-global x state)))

(fancy-ev-add-primitive fgl-interp-store-debug-info (not (eq msg :unreachable)))

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

(fancy-ev-add-primitive fgl-interp-store-debug-info (not (eq msg :unreachable)))

(def-fancy-ev-primitives counterex-primitives)



(disable-definition show-counterexample)

(disable-definition show-top-counterexample)

;; Note: this function will just get interpreted by fancy-ev when running under
;; show-counterexample-rw below, so we don't bother verifying guards etc.
(define show-counterexample-bind ((params fgl-object-p)
                                  (interp-st interp-st-bfrs-ok)
                                  state)
  :verify-guards nil
  (b* (((unless (fgl-object-case params :g-concrete))
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

(def-fgl-rewrite show-counterexample-rw
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
(define show-top-counterexample-bind ((params fgl-object-p)
                                      (interp-st interp-st-bfrs-ok)
                                      state)
  :verify-guards nil
  (b* (((unless (fgl-object-case params :g-concrete))
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

(def-fgl-rewrite show-top-counterexample-rw
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

  (def-fgl-rewrite fgl-sat-check/print-counterexample-rw
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

(define minor-stack->debug ((x minor-stack-p))
  :measure (len x)
  :ruler-extenders (cons)
  (cons (minor-frame->debug (car x))
        (and (consp (cdr x))
             (minor-stack->debug (cdr x)))))

(define minor-stack->debugframes-aux ((n natp) (x minor-stack-p))
  :measure (len x)
  :ruler-extenders (cons)
  (cons (cons (lnfix n) (minor-frame->debug (car x)))
        (and (consp (cdr x))
             (minor-stack->debugframes-aux (1+ (lnfix n)) (cdr x)))))

(define minor-stack->debugframes ((x minor-stack-p))
  (minor-stack->debugframes-aux 0 x))

(define interp-st-extract-bvar-db (interp-st)
  (stobj-let ((bvar-db (interp-st->bvar-db interp-st)))
             (db)
             (bvar-db-debug bvar-db)
             db))


(defmacro fgl-error! (&key msg debug-obj)
  `(syntax-interp
    (b* ((interp-st 'interp-st)) ;; fake
      (fgl-interp-store-debug-info ,msg ,debug-obj interp-st))))

(defmacro fgl-error (&key msg debug-obj)
  `(fgl-prog2 (fgl-error! :msg ,msg :debug-obj ,debug-obj)
              nil))

(defmacro fgl-assert! (cond &key msg debug-obj)
  `(if ,cond
       nil
     (fgl-error!
      ,@(if msg
            `(:msg ,msg)
          `(:msg (fgl-msg "Assertion failed: ~x0" ',cond)))
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
