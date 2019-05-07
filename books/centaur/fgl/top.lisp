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
    


(defun def-gl-clause-proc-fn (name wrld)
  (declare (xargs :mode :program))
  (b* (((unless (str::strsuffixp "GL-INTERP-CP" (symbol-name name)))
        (er hard? 'def-gl-clause-proc-fn "Name must end in GL-INTERP-CP"))
       (prefix (intern-in-package-of-symbol
                (subseq (symbol-name name) 0 (- (length (symbol-name name))
                                                (length "GL-INTERP-CP")))
                name))
       (pairs (append (attachment-pairs '(fgl-ev
                                          fgl-ev-list
                                          fgl-ev-meta-extract-global-badguy
                                          fgl-ev-falsify
                                          fgl-object-eval
                                          fgl-objectlist-eval)
                                        wrld)
                      (attachment-pairs! '(gl-primitive-fncall-stub) wrld)))
       ((mv event subst)
        (substitute-functions
         prefix
         '(gl-interp-cp)
         pairs
         wrld)))
    `(with-output :off :all :on (error summary) :gag-mode nil
       (progn
         ,event
         (defconst ,(intern-in-package-of-symbol
                     (concatenate 'string "*" (symbol-name name) "-SUBST*")
                     name)
           ',subst)

         (defthm ,(intern-in-package-of-symbol
                   (concatenate 'string (symbol-name name) "-CORRECT")
                   name)
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
                                . ,subst)))
           :rule-classes :clause-processor)))))

(defmacro def-gl-clause-proc (name)
  `(make-event
    (def-gl-clause-proc-fn ',name (w state))))

(logic)
(set-ignore-ok t)
(set-irrelevant-formals-ok t)


(def-gl-clause-proc top-gl-interp-cp)

(defmacro default-glcp-config ()
  '(make-glcp-config
    :rewrite-rule-table (table-alist 'gl-rewrite-rules (w state))
    :definition-table (table-alist 'gl-definition-rules (w state))
    :branch-merge-rules (table-alist 'gl-branch-merge-rules (w state))
    :function-modes (table-alist 'gl-fn-modes (w state))))

