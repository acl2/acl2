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
(include-book "subst-functions")
(include-book "primitives")
(include-book "fgarrays")
(include-book "sat")


(program)

(defun attachment-pairs (fns wrld)
  (b* (((when (atom fns)) nil)
       (fn (car fns))
       (pair (acl2::attachment-pair fn wrld))
       ((unless (consp pair))
        (attachment-pairs (cdr fns) wrld)))
    (cons pair (attachment-pairs (cdr fns) wrld))))

(defun attachment-pairs! (fns wrld)
  (b* (((when (atom fns)) nil)
       (fn (car fns))
       (pair (acl2::attachment-pair fn wrld))
       ((unless (consp pair))
        (er hard? 'attachment-pairs!
            "Function ~x0 is required to have an attachment.")))
    (cons pair (attachment-pairs! (cdr fns) wrld))))
    

(defun gl-clause-proc-define-subst-functions (prefix constname wrld)
  (b* ((pairs (append (attachment-pairs '(fgl-ev
                                          fgl-ev-list
                                          fgl-ev-meta-extract-global-badguy
                                          fgl-ev-falsify
                                          fgl-apply
                                          fgl-object-eval-fn
                                          fgl-objectlist-eval-fn
                                          fgl-object-alist-eval-fn)
                                        wrld)
                      (attachment-pairs! '(gl-primitive-fncall-stub
                                           gl-primitive-formula-checks-stub) wrld)))
       ((mv event subst)
        (substitute-functions
         prefix '(gl-interp-cp) pairs wrld)))
    `(progn ,event
            (defconst ,constname ',subst))))


(defun gl-clause-proc-correctness-thm (prefix subst)
  `(defthm ,(intern-in-package-of-symbol
             (concatenate 'string (symbol-name prefix) "-GL-INTERP-CP-CORRECT")
             prefix)
     ,(sublis (pairlis$ (strip-cars subst)
                        (acl2::strip-cadrs subst))
              '(implies (and (pseudo-term-listp clause)
                             (alistp a)
                             (fgl-ev
                              (meta-extract-global-fact+
                               (mv-nth 0 (fgl-ev-meta-extract-global-badguy state))
                               (mv-nth 1 (fgl-ev-meta-extract-global-badguy state))
                               state)
                              (fgl-ev-falsify
                               (meta-extract-global-fact+
                                (mv-nth 0 (fgl-ev-meta-extract-global-badguy state))
                                (mv-nth 1 (fgl-ev-meta-extract-global-badguy state))
                                state)))
                             (fgl-ev (conjoin-clauses
                                      (acl2::clauses-result (gl-interp-cp clause hint state)))
                                     a))
                        (fgl-ev (disjoin clause) a)))
     :hints (("goal" :by (:functional-instance gl-interp-cp-correct1
                          . ,subst)
              :do-not '(preprocess simplify)))
     :rule-classes :clause-processor))


(defun def-gl-clause-proc-fn (name wrld)
  (declare (xargs :mode :program)
           (ignore wrld))
  (b* (((unless (str::strsuffixp "-GL-INTERP-CP" (symbol-name name)))
        (er hard? 'def-gl-clause-proc-fn "Name must end in -GL-INTERP-CP"))
       (prefix (intern-in-package-of-symbol
                (subseq (symbol-name name) 0 (- (length (symbol-name name))
                                                (length "-GL-INTERP-CP")))
                name))
       (prefix- (intern-in-package-of-symbol
                 (concatenate 'string (symbol-name prefix) "-")
                 name))
       (constname (intern-in-package-of-symbol
                   (concatenate 'string "*" (symbol-name name) "-SUBST*")
                   name))
       ;; (default-hints (default-hints wrld))
       ;; (pairs (append (attachment-pairs '(fgl-ev
       ;;                                    fgl-ev-list
       ;;                                    fgl-ev-meta-extract-global-badguy
       ;;                                    fgl-ev-falsify
       ;;                                    fgl-apply
       ;;                                    fgl-object-eval
       ;;                                    fgl-objectlist-eval)
       ;;                                  wrld)
       ;;                (attachment-pairs! '(gl-primitive-fncall-stub) wrld)))
       ;; ((mv event subst)
       ;;  (substitute-functions
       ;;   prefix
       ;;   '(gl-interp-cp)
       ;;   pairs
       ;;   wrld))
       )
    `(with-output :off :all :on (error summary) :gag-mode nil
       (progn
         (install-gl-primitives ,prefix)
         (make-event
          (acl2::template-subst
           '(set-default-hints
             '((let ((term (car (last clause))))
                 (case-match term
                   (('equal (fn . args) . &)
                    (cond ((or (member fn '(<prefix>-ev
                                            <prefix>-ev-list))
                               (not (symbol-listp args)))
                           '(:do-not nil :in-theory (enable)))
                          ;; ((member fn '(<prefix>-ev-falsify
                          ;;               <prefix>-meta-extract-global-badguy))
                          ;;  `(:by 
                          (t `(:clause-processor (beta-reduce-by-hint-cp clause ',fn state)
                               :do-not nil :in-theory (enable)))))
                   (& (cond ((member-atoms '<prefix>-primitive-fncall term)
                             '(:do-not nil :in-theory (enable)))
                            ((member-atoms '<prefix>-ev-meta-extract-global-badguy term)
                             '(:by <prefix>-ev-meta-extract-global-badguy))
                            ((member-atoms '<prefix>-ev-falsify term)
                             `(:clause-processor (beta-reduce-by-hint-cp clause '<prefix>-ev-falsify state)
                               :do-not nil :in-theory (enable)))
                            (t '(:do-not nil
                                 :in-theory (enable <prefix>-ev-of-fncall-args
                                                    <prefix>-ev-of-nonsymbol-atom
                                                    <prefix>-ev-of-bad-fncall)))))))))
           :str-alist `(("<PREFIX>" ,,(symbol-name prefix) . ,',prefix))))
         (make-event
          (gl-clause-proc-define-subst-functions ',prefix- ',constname (w state)))
         
         (make-event
          (gl-clause-proc-correctness-thm ',prefix ,constname))))))

(defmacro def-gl-clause-proc (name)
  `(make-event
    (def-gl-clause-proc-fn ',name (w state))))

(logic)
(set-ignore-ok t)
(set-irrelevant-formals-ok t)

(set-case-split-limitations '(0 1000))
(def-gl-clause-proc top-gl-interp-cp)

(defmacro default-glcp-config ()
  '(make-glcp-config
    :rewrite-rule-table (table-alist 'gl-rewrite-rules (w state))
    :definition-table (table-alist 'gl-definition-rules (w state))
    :branch-merge-rules (table-alist 'gl-branch-merge-rules (w state))
    :function-modes (table-alist 'gl-fn-modes (w state))))

