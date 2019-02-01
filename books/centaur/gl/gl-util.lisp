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

(in-package "GL")
(include-book "tools/flag" :dir :system)
(include-book "std/util/bstar" :dir :system)
(include-book "std/lists/acl2-count" :dir :system)
(include-book "clause-processors/term-vars" :dir :system)


(verify-termination acl2::def-body)

(verify-guards fgetprop)

(verify-termination acl2::latest-body)
(verify-guards acl2::latest-body)

(verify-termination body)

(defun wgetprop-fn (sym prop default world)
  (declare (xargs :guard (and (symbolp sym) (symbolp prop)
                              (plist-worldp world))))
  (b* ((look1 (ec-call (assoc-equal sym (table-alist 'override-props world))))
       (look2 (and look1 (ec-call (assoc-equal prop (ec-call (cdr look1)))))))
    (if look2
        (ec-call (cdr look2))
      (getprop sym prop default 'acl2::current-acl2-world world))))

(defmacro wgetprop (sym prop &optional default (world 'world))
  `(wgetprop-fn ,sym ,prop ,default ,world))

(defun incat-fn (pkg-witness name)
  (let ((pkg-witness
         (cond ((let ((p (symbol-package-name pkg-witness)))
                  (or (equal p "KEYWORD")
                      (equal p acl2::*MAIN-LISP-PACKAGE-NAME*)))
                'genvar) ;; in package "GL"
               (t pkg-witness))))
    (acl2::intern-in-package-of-symbol name pkg-witness)))

(defmacro incat (sym &rest strings)
  `(incat-fn ,sym
             (concatenate 'string . ,strings)))

(defun my-def-body (name world)
  (let ((def-body (ec-call (acl2::def-body name world))))
    (and (not (acl2::access acl2::def-body def-body :hyp))
         (eq (acl2::access acl2::def-body def-body :equiv)
             'equal)
         `(equal ,(acl2::fcons-term
                   name (acl2::access acl2::def-body def-body :formals))
                 ,(acl2::access acl2::def-body def-body :concl)))))

;; (defun my-def-corollary (name world)
;;   (declare (xargs :guard (and (plist-worldp world)
;;                               (symbolp name))))
;;   (let ((classes (wgetprop name 'acl2::classes)))
;;     (if classes
;;         (wgetprop name 'acl2::theorem)
;;       (ec-call (my-def-body name world)))))


(defun preferred-defs-table-guard (fn thm world)
  (b* ((formals (wgetprop fn 'formals :none))
       ((when (eq formals :none))
        (cw "Error setting preferred-defs: ~x0 is not a function symbol (it
does not have a FORMALS property.)~%" fn))
       (rule (wgetprop thm 'theorem :none))
       ((when (eq rule :none))
        (cw "Error setting preferred-defs: ~x0 is not the name of a theorem.~%"
            thm))
       ((unless (and (eql (len rule) 3)
                     (eq (car rule) 'equal)
                     (consp (cadr rule))
                     (eq (caadr rule) fn)))
        (cw "Error setting preferred-defs: Theorem ~x0 does not have the
required form: ~x1~%."
            thm `(equal (,fn . ,formals) body)))
       ((unless (equal (cdadr rule) formals))
        (cw "Error setting preferred-defs: Theorem ~x0 does not have the
required form: ~x1.~%
In particular, the formals of ~x2 are different from the variable names used in
the theorem.  Try instead using the form
 (GL::SET-PREFERRED-DEF ~x2 ~x0)
to correct this.~%"
            thm `(equal (,fn . ,formals) body) fn))
       (missing-vars (set-difference-eq (all-vars rule) formals))
       ((when missing-vars)
        (cw "Error setting preferred-defs: The definition body suggested by
theorem ~x0 contains the variables ~x1, which are not among the formals of
~x2.~%"
            thm missing-vars fn)))
    t))

(table preferred-defs nil nil :guard
       (preferred-defs-table-guard acl2::key acl2::val world))

(defun set-preferred-def-fn (fn thm world)
  (b* ((formals (wgetprop fn 'formals :none))
       ((when (eq formals :none))
        (cw "Error in set-preferred-def: ~x0 is not a function symbol (it
does not have a FORMALS property.)~%" fn))
       (rule (wgetprop thm 'theorem :none))
       ((when (eq rule :none))
        (cw "Error in set-preferred-def: ~x0 is not the name of a theorem.~%"
            thm))
       ((unless (and (eql (len rule) 3)
                     (eq (car rule) 'equal)
                     (consp (cadr rule))
                     (eq (caadr rule) fn)))
        (cw "Error in set-preferred-def: Theorem ~x0 does not have the
required form: ~x1~%."
            thm `(equal (,fn . ,formals) body)))
       (rule-formals (cdadr rule))
       (events (if (equal formals rule-formals)
                   nil
                 `((table override-props
                          ',fn
                          (cons ',(cons 'formals rule-formals)
                                (cdr (assoc ',fn (table-alist 'override-props world))))))))
       (missing-vars (set-difference-eq (all-vars rule) rule-formals))
       ((when missing-vars)
        (cw "Error in set-preferred-def: The definition body suggested by
theorem ~x0 contains the variables ~x1, which are not among the arguments
passed to ~x2 in that theorem.~%"
            thm missing-vars fn)))
    (cons 'progn (append events
                         `((table preferred-defs ',fn ',thm))))))

(defmacro set-preferred-def (fn thm)
  `(make-event (set-preferred-def-fn ',fn ',thm (w state))))

(defmacro gl-clause-proc-exec-fns-table ()
  '(table-alist 'gl-clause-proc-exec-fns world))

(defmacro gl-clause-proc-forbidden-exec-fns ()
  '(cdr (assoc 'forbid (gl-clause-proc-exec-fns-table))))

(defmacro forbid-clause-proc-exec-fns (fns)
  `(progn
     (value-triple
      (not (cw "NOTE: Forbid-clause-proc-exec-fns currently doesn't do ~
                anything useful; it is conceivable that it may again in the ~
                future.~%")))
     (table gl-clause-proc-exec-fns
            'forbid
            (append ,fns (gl-clause-proc-forbidden-exec-fns)))))

;; (defmacro gl-clause-proc-auto-exec-fns ()
;;   '(cdr (assoc 'auto (gl-clause-proc-exec-fns-table))))

(defmacro add-clause-proc-exec-fns (fns)
  (declare (ignore fns))
  `(value-triple
    (not (cw "DEPRECATED: Add-clause-proc-exec-fns is no longer necessary; GL ~
              clause processors no longer have a fixed set of functions they ~
              can concretely execute.~%"))))



(defun norm-function-body (fn world)
  (declare (xargs :guard (and (symbolp fn) (plist-worldp world))))
  ;; If there is no entry in the table-alist, produce the unnormalized-body.
  (let* ((alst (table-alist 'preferred-defs world))
         (entry (ec-call (assoc-equal fn alst))))
    (if (and (consp entry) (symbolp (cdr entry)))
        (let* ((name (cdr entry))
               (rule (wgetprop name 'theorem))
               (formals (wgetprop fn 'formals)))
          (and (eql (len rule) 3)
               (eq (car rule) 'equal)
               (consp (cadr rule))
               (eq (caadr rule) fn)
               (equal (cdadr rule) formals)
               (caddr rule)))
      (wgetprop fn 'unnormalized-body))))

(defun norm-function-body-and-def-name (fn world)
  (declare (xargs :guard (and (symbolp fn) (plist-worldp world))))
  ;; If there is no entry in the table-alist, produce the unnormalized-body.
  (let* ((alst (table-alist 'preferred-defs world))
         (entry (ec-call (assoc-equal fn alst))))
    (if (and (consp entry) (symbolp (cdr entry)))
        (let* ((name (cdr entry))
               (rule (wgetprop name 'theorem))
               (formals (wgetprop fn 'formals)))
          (if (and (eql (len rule) 3)
                   (eq (car rule) 'equal)
                   (consp (cadr rule))
                   (eq (caadr rule) fn)
                   (equal (cdadr rule) formals))
              (mv (cdr entry) (caddr rule))
            (mv nil nil)))
      (mv fn (wgetprop fn 'unnormalized-body)))))

(in-theory (disable norm-function-body-and-def-name
                    norm-function-body))
(program)

(defun gl-fnsym (fn)
  ;; [Jared] To better support inline functions, I changed the way these names
  ;; are generated, so that they always end with $.  This prevents the GL version
  ;; of an inline/notinline function from ever ending with $inline/$notinline.
  (incat 'gl-sym::foo
         (symbol-package-name fn) "::" (symbol-name fn) "$"))

(defmacro glr (fn &rest args)
  `(,(gl-fnsym fn) ,@args))

(defmacro glc (fn &rest args)
  `(,(gl-fnsym fn) ,@args hyp clk config bvar-db state))




(defun def-acl2-aliases (lst)
  (if (atom lst)
      nil
    (let ((macro (incat 'acl2::foo (symbol-name (car lst)))))
      (list* `(defmacro
               ,macro (&rest args)
               `(,',(car lst) . ,args))
;;             `(add-macro-alias ,macro ,(car lst))
             (def-acl2-aliases (cdr lst))))))

(make-event
 `(progn
    . ,(def-acl2-aliases
         '(g-boolean
           g-boolean-p g-boolean->bool
           g-number g-number-p g-number->num
           g-integer g-integer-p g-integer->bits
           g-concrete g-concrete-p g-concrete->obj
           g-ite g-ite-p g-ite->test g-ite->then g-ite->else
           g-apply g-apply-p g-apply->fn g-apply->args
           g-var g-var-p g-var->name))))


(logic)






;; A version of ACL2's dumb-negate-lit that behaves logically wrt an evaluator.
(defund dumb-negate-lit (term)
  (declare (xargs :guard (pseudo-termp term)))
  (cond ((null term) ''t)
        ((atom term) `(not ,term))
        ((eq (car term) 'quote)
         (acl2::kwote (not (cadr term))))
        ((eq (car term) 'not)
         (cadr term))
        ((eq (car term) 'equal)
         (cond ((or (eq (cadr term) nil)
                    (equal (cadr term) ''nil))
                (caddr term))
               ((or (eq (caddr term) nil)
                    (equal (caddr term) ''nil))
                (cadr term))
               (t `(not ,term))))
        (t `(not ,term))))

(defthm pseudo-termp-of-dumb-negate-lit
  (implies (pseudo-termp term)
           (pseudo-termp (dumb-negate-lit term)))
  :hints(("Goal" :in-theory (enable dumb-negate-lit pseudo-termp))))


(acl2::defund-inline maybe-fmt-to-comment-window (test str alist col evisc-tuple print-base-radix)
  (declare (xargs :guard t))
  (and test
       (fmt-to-comment-window str alist col evisc-tuple print-base-radix)))

(defmacro maybe-cw (test str &rest args)
  `(maybe-fmt-to-comment-window ,test ,str
                                (pairlis2 acl2::*base-10-chars* (list ,@args))
                                0 nil nil))

(acl2::defund-inline observation-uninhibited (state)
  (declare (xargs :guard t :stobjs state
                  :guard-hints (("goal" :in-theory (e/d (state-p1)
                                                        (state-p-implies-and-forward-to-state-p1))))))
  
  (not (let ((lst (f-get-global 'acl2::inhibit-output-lst state)))
         (and (true-listp lst)
              (member-eq 'acl2::observation lst)))))

(defmacro obs-cw (str &rest args)
  `(maybe-cw (observation-uninhibited state)
             ,str . ,args))


