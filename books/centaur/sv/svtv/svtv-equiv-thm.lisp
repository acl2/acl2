; SV - Symbolic Vector Hardware Analysis Framework
; Copyright (C) 2022 Intel Corporation
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
; Original author: Mertcan Temel <mert.temel@intel.com>
;; This file is copied over from svtv-override-fact.lisp and updated to fit the needs

(in-package "SV")

(include-book "svtv-override-fact")

(std::def-primitive-aggregate svtv-equiv-thm-data
  (name
   input-vars-1
   input-vars-2
   input-var-bindings-1
   input-var-bindings-2
   output-vars-1
   output-vars-2
   hyp
   concl
   svtv-1
   svtv-2
   triples-name-1
   triples-name-2
   triples-val-1
   triples-val-2
   enable
   lemma-defthm
   lemma-args
   no-lemmas
   hints
   pkg-sym))

(program)

(defun svtv-equiv-thm-suffix-index-to-var (var index)
  (intern$ (str::cat (symbol-name var)
                     "-"
                     (str::int-to-dec-string index))
           (symbol-package-name var)))

(defun svtv-equiv-thm-suffix-index-to-vars-for-svassocs (vars index)
  (if (atom vars)
      nil
    (cons `(,(svtv-equiv-thm-suffix-index-to-var (car vars) index)
            ',(car vars))
          (svtv-equiv-thm-suffix-index-to-vars-for-svassocs (cdr vars) index))))

(defun svtv-equiv-thm-suffix-index-to-vars (vars index)
  (if (atom vars)
      nil
    (cons (svtv-equiv-thm-suffix-index-to-var (car vars) index)
          (svtv-equiv-thm-suffix-index-to-vars (cdr vars) index))))

(defun svtv-equiv-thm-suffix-index-to-bindings (bindings index)
  (b* ((vars (svtv-equiv-thm-suffix-index-to-vars (strip-cars bindings) index)))
    (pairlis$ vars (strip-cdrs bindings))))

(defun svtv-equiv-thm-suffix-index-to-hyps (masks index)
  (if (atom masks)
      nil
    (b* ((rest (svtv-equiv-thm-suffix-index-to-hyps (cdr masks) index))
         (cur (car masks)))
      (case-match cur
        (('unsigned-byte-p num var)
         (b* ((new-var (svtv-equiv-thm-suffix-index-to-var var index)))
           (cons `(unsigned-byte-p ,num ,new-var)
                 rest)))
        (&
         rest)))))

(defun svtv-equiv-thm-input-vars-to-alist (input-vars index)
  (if (atom input-vars)
      nil
    (cons `(cons
            ',(car input-vars)
            ,(svtv-equiv-thm-suffix-index-to-var (car input-vars) index))
          (svtv-equiv-thm-input-vars-to-alist (cdr input-vars) index))))

(defun svtv-equiv-thm-initial-override-lemma (x)
  (declare (Xargs :mode :program))
  (b* (((svtv-equiv-thm-data x))
       (template '(<defthm> <name>-equiv-lemma
                            (implies <hyp>
                                     (b* ((run-1 (svtv-run (<svtv-1>)
                                                           (append <input-bindings-1>
                                                                   <input-vars-1>)
                                                           :include '<outputs-list-1>))
                                          (run-2 (svtv-run (<svtv-2>)
                                                           (append <input-bindings-2>
                                                                   <input-vars-2>)
                                                           :include '<outputs-list-2>))
                                          ((svassocs <outputs-1>) run-1)
                                          ((svassocs <outputs-2>) run-2))
                                       (and <integerp-concls>
                                            <concl>)))
                            <args>)))
    (acl2::template-subst
     template
     :atom-alist `((<defthm> . ,x.lemma-defthm)
                   (<hyp> . ,x.hyp)
                   (<concl> . ,x.concl)
                   (<svtv-1> . ,x.svtv-1)
                   (<svtv-2> . ,x.svtv-2)
                   (<input-bindings-1>
                    . (list . ,(svtv-ovfact-input-var-bindings-alist-termlist x.input-var-bindings-1)))
                   (<input-bindings-2>
                    . (list . ,(svtv-ovfact-input-var-bindings-alist-termlist x.input-var-bindings-2)))
                   (<input-vars-1> . (list . ,(svtv-equiv-thm-input-vars-to-alist x.input-vars-1 1)))
                   (<input-vars-2> . (list . ,(svtv-equiv-thm-input-vars-to-alist x.input-vars-2 2)))
                   (<outputs-list-1> . ,x.output-vars-1)
                   (<outputs-list-2> . ,x.output-vars-2))
     :splice-alist `((<outputs-1>
                      . ,(svtv-equiv-thm-suffix-index-to-vars-for-svassocs x.output-vars-1 1))
                     (<outputs-2>
                      . ,(svtv-equiv-thm-suffix-index-to-vars-for-svassocs x.output-vars-2 2)) ;;;;
                     (<integerp-concls>
                      . ,(svtv-ovfact-integerp-conclusions-aux (append
                                                                (svtv-equiv-thm-suffix-index-to-vars
                                                                 x.output-vars-1 1)
                                                                (svtv-equiv-thm-suffix-index-to-vars
                                                                 x.output-vars-2 2))))
                     (<args> . ,x.lemma-args))
     :str-alist `(("<NAME>" . ,(symbol-name x.name)))
     :pkg-sym x.pkg-sym)))

(defun svtv-equiv-thm-input-binding-hyp-termlist (input-var-bindings index)
  (b* (((when (atom input-var-bindings)) nil)
       ((list name term) (car input-var-bindings)))
    (cons `(equal ,(svtv-equiv-thm-suffix-index-to-var name index) ,term)
          (svtv-equiv-thm-input-binding-hyp-termlist (cdr input-var-bindings) index))))

(defun svtv-equiv-mono-lemma (x i)
  (b* (((svtv-equiv-thm-data x))
       (template '(defthm <name>-<<=-lemma-<i>
                    (b* (((svassocs <input-var-svassocs>
                                    <input-unbound-svassocs>)
                          <env>))
                      (implies (and <input-binding-hyp>
                                    (svex-env-keys-no-1s-p
                                     (svar-override-triplelist->testvars (<triples>)) <env>))
                               (b* ((run (svtv-run (<svtv>) <env>))

                                    (lemma-run (svtv-run (<svtv>)
                                                         (append <input-bindings>
                                                                 <input-vars>))))
                                 (svex-env-<<= lemma-run run))))
                    :hints (("goal" :use ((:instance <svtv>-overrides-correct
                                                     (spec-env <env>)
                                                     (lemma-env
                                                      (b* ((?run (svtv-run (<svtv>) <env>))

                                                           ((svassocs <input-unbound-svassocs>) <env>))
                                                        (append <input-bindings>
                                                                <input-vars>)))))
                             :in-theory '((:CONGRUENCE CONS-4VEC-EQUIV-CONGRUENCE-ON-V-UNDER-SVEX-ENV-EQUIV)
                                          (:CONGRUENCE SVEX-ENVS-SIMILAR-IMPLIES-EQUAL-SVEX-ENV-<<=-1)
                                          (:DEFINITION 4VEC-EQUIV$INLINE)
                                          (:DEFINITION DOUBLE-REWRITE)
                                          (:DEFINITION NOT)
                                          (:DEFINITION SYNP)
                                          (2VEC-P$INLINE)
                                          (4VEC-FIX$INLINE)
                                          (ALIST-KEYS)
                                          (ATOM)
                                          (BINARY-APPEND)
                                          (<svtv>-NON-TRIPLE-OVERRIDE-TESTS)
                                          (CAR)
                                          (CDR)
                                          (CONS)
                                          (CONSP)
                                          (EQUAL)
                                          (HONS-DUPS-P)
                                          (NOT)
                                          (SVAR-FIX$INLINE)
                                          (SVAR-P)
                                          (SVARLIST-FILTER)
                                          (TRUE-LIST-FIX)
                                          (:META HONS-INTERSECTION-FORCE-EXECUTE)
                                          (:META HONS-SET-DIFF-FORCE-EXECUTE)
                                          (:REWRITE 4VEC-<<=-2VEC)
                                          (:REWRITE 4VEC-FIX-OF-4VEC)
                                          (:REWRITE 4VEC-FIX-UNDER-4VEC-EQUIV)
                                          (:REWRITE 4VEC-P-OF-SVEX-ENV-LOOKUP)
                                          (:REWRITE ACL2::ALIST-KEYS-OF-CONS)
                                          (:REWRITE ACL2::APPEND-OF-CONS)
                                          (:REWRITE ACL2::APPEND-OF-NIL)
                                          (:REWRITE ACL2::APPEND-WHEN-NOT-CONSP)
                                          (:REWRITE CAR-CONS)
                                          (:REWRITE CDR-CONS)
                                          (:REWRITE ACL2::LIST-FIX-OF-CONS)
                                          (:REWRITE SVARLIST-FIX-WHEN-SVARLIST-P)
                                          (:REWRITE SVARLIST-P-OF-SVAR-OVERRIDE-TRIPLELIST->VALVARS)
                                          (:REWRITE SVARLIST-P-OF-SVAR-OVERRIDE-TRIPLELIST-OVERRIDE-VARS)
                                          (:REWRITE SVEX-ENV-<<=-EACH-OF-CONS)
                                          (:REWRITE SVEX-ENV-<<=-EACH-OF-NIL)
                                          (:REWRITE SVEX-ENV-<<=-IS-SVEX-ENV-<<=-EACH-WHEN-NO-DUPLICATE-KEYS)
                                          (:REWRITE SVEX-ENV-<<=-NECC)
                                          (:REWRITE SVEX-ENV-<<=-REFL)
                                          (:REWRITE SVEX-ENV-EXTRACT-OF-CONS)
                                          (:REWRITE SVEX-ENV-EXTRACT-OF-NIL)
                                          (:REWRITE SVEX-ENV-EXTRACT-OF-VARIABLE-FREE-TERM)
                                          (:REWRITE SVEX-ENV-LOOKUP-OF-CONS)
                                          (:REWRITE SVEX-ENV-REMOVEKEYS-OF-VARIABLE-FREE-TERM)
                                          (:REWRITE SVEX-ENVS-AGREE-OF-NIL)
                                          (:TYPE-PRESCRIPTION SVEX-ENV-<<=)
                                          (:TYPE-PRESCRIPTION SVEX-ENV-LOOKUP)
                                          (svar-override-triple->refvar)
                                          svex-env-fix-when-svex-env-p
                                          acl2::svex-env-p-of-svtv-run
                                          alist-keys-of-svtv-run
                                          <svtv>-refvars-subset-of-output-vars
                                          lookup-of-svtv-pipeline-override-triples-extract
                                          svar-override-triplelist-lookup-valvar-force-execute))))))
    (acl2::template-subst
     template
     :atom-alist
     (if (equal i 1)
         `((<env> . env-1)
           (<svtv> . ,x.svtv-1)
           (<triples> . ,x.triples-name-1)
           (<input-bindings> . (list . ,(svtv-ovfact-input-var-bindings-alist-termlist x.input-var-bindings-1)))
           (<input-vars> . (list . ,(svtv-equiv-thm-input-vars-to-alist
                                     x.input-vars-1 1)))
           )
       `((<env> . env-2)
         (<svtv> . ,x.svtv-2)
         (<triples> . ,x.triples-name-2)
         (<input-bindings> . (list . ,(svtv-ovfact-input-var-bindings-alist-termlist x.input-var-bindings-2)))
         (<input-vars> . (list . ,(svtv-equiv-thm-input-vars-to-alist
                                   x.input-vars-2 2)))
         ))
     :splice-alist
     (if (equal i 1)
         `((<input-var-svassocs> . ,(svtv-equiv-thm-suffix-index-to-vars-for-svassocs
                                     (strip-cars x.input-var-bindings-1) 1))
           (<input-unbound-svassocs> . ,(svtv-equiv-thm-suffix-index-to-vars-for-svassocs
                                         x.input-vars-1 1))
           (<input-binding-hyp> .  ,(svtv-equiv-thm-input-binding-hyp-termlist x.input-var-bindings-1 1)))
       `((<input-var-svassocs> . ,(svtv-equiv-thm-suffix-index-to-vars-for-svassocs
                                   (strip-cars x.input-var-bindings-2) 2))
         (<input-unbound-svassocs> . ,(svtv-equiv-thm-suffix-index-to-vars-for-svassocs
                                       x.input-vars-2 2))
         (<input-binding-hyp> .  ,(svtv-equiv-thm-input-binding-hyp-termlist x.input-var-bindings-2 2))))
     :str-alist `(("<I>" . ,(str::int-to-dec-string i))
                  ("<NAME>" . ,(symbol-name x.name))
                  ("<SVTV>" . ,(symbol-name (if (equal i 1) x.svtv-1 x.svtv-2))))
     :pkg-sym x.pkg-sym)))

(defun svtv-equiv-thm-input-var-instantiation (input-vars index)
  (if (atom input-vars)
      nil
    (cons `(,(intern$ (str::cat (symbol-name (car input-vars))
                                "-"
                                (str::int-to-dec-string index))
                      (symbol-package-name (car input-vars)))
            (svex-env-lookup ',(car input-vars)
                             ,(if (equal index 1) 'env-1 'env-2)))
          (svtv-equiv-thm-input-var-instantiation (cdr input-vars) index))))

(defun svtv-equiv-thm-final-thm (x)
  (b* (((svtv-equiv-thm-data x))
       (template '(defthm <name>
                    (b* (((svassocs <input-var-svassocs-1>) env-1)
                         ((svassocs <input-var-svassocs-2>) env-2)
                         (run-1 (svtv-run (<svtv-1>) env-1))
                         (run-2 (svtv-run (<svtv-2>) env-2)))
                      (implies (and <hyp>
                                    <input-binding-hyp>
                                    (svex-env-keys-no-1s-p
                                     (svar-override-triplelist->testvars (<triples-1>)) env-1)
                                    (svex-env-keys-no-1s-p
                                     (svar-override-triplelist->testvars (<triples-2>)) env-2))
                               (b* (((svassocs <outputs-1>) run-1)
                                    ((svassocs <outputs-2>) run-2))
                                 <concl>)))
                    :hints (:@ :no-lemmas <hints>)
                    (:@ (not :no-lemmas)
                        (("goal" :use (<name>-<<=-lemma-1
                                       <name>-<<=-lemma-2
                                       (:instance <name>-equiv-lemma
                                                  <input-var-instantiation-1>
                                                  <input-var-instantiation-2>))
                          :in-theory '((BINARY-APPEND)
                                       (CONS)
                                       (INTEGERP)
                                       (MEMBER-EQUAL)
                                       (SVAR-FIX$INLINE)
                                       (TRUE-LIST-FIX)
                                       (:REWRITE ACL2::APPEND-OF-CONS)
                                       (:REWRITE ACL2::APPEND-OF-NIL)
                                       (:REWRITE ACL2::APPEND-WHEN-NOT-CONSP)
                                       (:REWRITE ACL2::LIST-FIX-OF-CONS)
                                       (:REWRITE SVEX-ENV-LOOKUP-IN-SVTV-RUN-WITH-INCLUDE)
                                       (:REWRITE SVEX-ENV-LOOKUP-WHEN-INTEGERP-AND-<<=)
                                       (:TYPE-PRESCRIPTION SVEX-ENV-<<=)
                                       (:TYPE-PRESCRIPTION SVEX-ENV-LOOKUP)
                                       <enable>)))))))
    (acl2::template-subst
     template
     :atom-alist
     `((<hyp> . ,x.hyp)
       (<concl> . ,x.concl)
       (<svtv-1> . ,x.svtv-1)
       (<svtv-2> . ,x.svtv-2)
       (<triples-1> . ,x.triples-name-1)
       (<triples-2> . ,x.triples-name-2)
       (<hints> . ,x.hints))
     :splice-alist
     `((<input-var-svassocs-1> . ,(svtv-equiv-thm-suffix-index-to-vars-for-svassocs
                                   (append x.input-vars-1 (strip-cars x.input-var-bindings-1))
                                   1))
       (<input-var-svassocs-2> . ,(svtv-equiv-thm-suffix-index-to-vars-for-svassocs
                                   (append x.input-vars-2 (strip-cars x.input-var-bindings-2))
                                   2))

       (<input-binding-hyp> .  ,(append
                                 (svtv-equiv-thm-input-binding-hyp-termlist x.input-var-bindings-1 1)
                                 (svtv-equiv-thm-input-binding-hyp-termlist
                                  x.input-var-bindings-2 2)))

       (<input-var-instantiation-1> . ,(svtv-equiv-thm-input-var-instantiation
                                        x.input-vars-1 1))
       (<input-var-instantiation-2> . ,(svtv-equiv-thm-input-var-instantiation
                                        x.input-vars-2 2))
       (<outputs-1> . ,(svtv-equiv-thm-suffix-index-to-vars-for-svassocs x.output-vars-1 1))
       (<outputs-2> . ,(svtv-equiv-thm-suffix-index-to-vars-for-svassocs x.output-vars-2 2))
       (<enable> . ,x.enable))
     :str-alist `(("<NAME>" . ,(symbol-name x.name)))
     :features (and x.no-lemmas '(:no-lemmas))
     :pkg-sym x.pkg-sym)))

(defun svtv-equiv-thm-precheck-for-errors (x)
  (b* (((svtv-equiv-thm-data x)))
    (or (svtv-ovfact-check-variable-list "Input-vars-1" x.input-vars-1)
        (svtv-ovfact-check-variable-list "Input-vars-2" x.input-vars-2)
        (svtv-ovfact-check-variable-list "Output-vars-1" x.output-vars-1)
        (svtv-ovfact-check-variable-list "Output-vars-2" x.output-vars-2)
        (and (not (acl2::doublet-listp x.input-var-bindings-1))
             "Input-var-bindings-1 must be a list of two-element lists")
        (and (not (acl2::doublet-listp x.input-var-bindings-2))
             "Input-var-bindings-2 must be a list of two-element lists")
        (svtv-ovfact-check-variable-list "Keys of input-var-bindings-1"
                                         (strip-cars x.input-var-bindings-1))
        (svtv-ovfact-check-variable-list "Keys of input-var-bindings-2"
                                         (strip-cars x.input-var-bindings-2))
        (let ((dup-tail (acl2::hons-dups-p (append x.input-vars-1
                                                   (strip-cars x.input-var-bindings-1)
                                                   x.output-vars-1))))
          (and dup-tail
               (msg "Input and output variables should not ~
                     intersect, but ~x0 is present in more than one for svtv-1"
                    (car dup-tail))))
        (let ((dup-tail (acl2::hons-dups-p (append x.input-vars-2
                                                   (strip-cars x.input-var-bindings-2)
                                                   x.output-vars-2))))
          (and dup-tail
               (msg "Input and output variables should not ~
                     intersect, but ~x0 is present in more than one for svtv-2"
                    (car dup-tail))))
        (let ((dup-tail (acl2::hons-dups-p (append x.input-vars-1
                                                   (strip-cars x.input-var-bindings-1)
                                                   x.output-vars-1
                                                   (acl2::all-vars x.concl)))))
          (and dup-tail
               (msg "Concl should not include a variable with the same name as ~
                     inputs and outputs. Instead of using ~x0, use ~x0-1 instead."
                    (car dup-tail))))
        (let ((dup-tail (acl2::hons-dups-p (append x.input-vars-2
                                                   (strip-cars x.input-var-bindings-2)
                                                   x.output-vars-2
                                                   (acl2::all-vars x.concl)))))
          (and dup-tail
               (msg "Concl should not include a variable with the same name as ~
                     inputs and outputs. Instead of using ~x0, use ~x0-2 instead."
                    (car dup-tail))))
        (let ((dup-tail (acl2::hons-dups-p (append x.input-vars-1
                                                   (strip-cars x.input-var-bindings-1)
                                                   x.output-vars-1
                                                   (acl2::all-vars x.hyp)))))
          (and dup-tail
               (msg "Hyp should not include a variable with the same name as ~
                     inputs and outputs. Instead of using ~x0, use ~x0-1 instead."
                    (car dup-tail))))
        (let ((dup-tail (acl2::hons-dups-p (append x.input-vars-2
                                                   (strip-cars x.input-var-bindings-2)
                                                   x.output-vars-2
                                                   (acl2::all-vars x.hyp)))))
          (and dup-tail
               (msg "Hyp should not include a variable with the same name as ~
                     inputs and outputs. Instead of using ~x0, use ~x0-2 instead."
                    (car dup-tail)))))))

(defun svtv-equiv-thm-events (x)
  (b* (((svtv-equiv-thm-data x))
       (err (svtv-equiv-thm-precheck-for-errors x))
       ((when err) (er hard? `(def-svtv-equiv-thm ,x.name) "Error: ~@0" err)))
    `(defsection ,x.name
       ,@(and (not x.no-lemmas)
              `((local ,(svtv-equiv-thm-initial-override-lemma x))
                (local ,(svtv-equiv-mono-lemma x 1))
                (local ,(svtv-equiv-mono-lemma x 2))))
       ,(svtv-equiv-thm-final-thm x))))

(defun svtv-equiv-thm-fn (name args state)
  (declare (xargs :stobjs state))
  (b* ((defaults (table-alist 'svtv-equiv-thm-defaults (w state)))
       (ctx `(def-svtv-equiv-thm ,name))
       ((std::extract-keyword-args
         :defaults defaults
         :ctx ctx
         svtv-1
         svtv-2
         input-vars-1
         input-vars-2
         output-vars-1
         output-vars-2
         input-var-bindings-1
         input-var-bindings-2
         enable
         unsigned-byte-hyps
         (hyp 't)
         concl
         (lemma-defthm 'fgl::def-fgl-thm)
         lemma-args
         no-lemmas
         hints
         (pkg-sym name))
        args)

       (triples-1 (acl2::template-subst
                   '<svtv>-pipeline-override-triples
                   :str-alist `(("<SVTV>" . ,(symbol-name svtv-1)))
                   :pkg-sym pkg-sym))
       ((mv err triples-val-1) (magic-ev-fncall triples-1 nil state t t))
       ((when err) (er soft ctx "Couldn't evaluate ~x0" (list triples-1)))
       (triples-2 (acl2::template-subst
                   '<svtv>-pipeline-override-triples
                   :str-alist `(("<SVTV>" . ,(symbol-name svtv-2)))
                   :pkg-sym pkg-sym))
       ((mv err triples-val-2) (magic-ev-fncall triples-2 nil state t t))
       ((when err) (er soft ctx "Couldn't evaluate ~x0" (list triples-2)))

       ((mv err svtv-val-1) (magic-ev-fncall svtv-1 nil state t t))
       ((when err) (er soft ctx "Couldn't evaluate ~x0" (list svtv-1)))
       ((mv err svtv-val-2) (magic-ev-fncall svtv-2 nil state t t))
       ((when err) (er soft ctx "Couldn't evaluate ~x0" (list svtv-2)))
       (hyp (if unsigned-byte-hyps
                (b* ((inmasks-1 (svtv->inmasks svtv-val-1))
                     (inmasks-2 (svtv->inmasks svtv-val-2))
                     (inputs-1 input-vars-1)
                     (inputs-2 input-vars-2)
                     (masks-1 (acl2::fal-extract inputs-1 inmasks-1))
                     (masks-2 (acl2::fal-extract inputs-2 inmasks-2))
                     )
                  `(and ,@(svtv-equiv-thm-suffix-index-to-hyps (svtv-unsigned-byte-hyps masks-1) 1)
                        ,@(svtv-equiv-thm-suffix-index-to-hyps (svtv-unsigned-byte-hyps masks-2) 2)
                        ,hyp))
              hyp)))

    (value
     (svtv-equiv-thm-events
      (make-svtv-equiv-thm-data
       :name name
       :input-vars-1 input-vars-1
       :input-vars-2 input-vars-2
       :output-vars-1 output-vars-1
       :output-vars-2 output-vars-2
       :input-var-bindings-1 input-var-bindings-1
       :input-var-bindings-2 input-var-bindings-2
       :enable enable
       :hyp hyp
       :concl concl
       :svtv-1 svtv-1
       :svtv-2 svtv-2
       :lemma-defthm lemma-defthm
       :lemma-args lemma-args
       :triples-name-1 triples-1
       :triples-val-1 triples-val-1
       :triples-name-2 triples-2
       :triples-val-2 triples-val-2
       :hints hints
       :no-lemmas no-lemmas
       :pkg-sym pkg-sym)))))

(defmacro def-svtv-equiv-thm (name &rest args)
  `(make-event (svtv-equiv-thm-fn ',name ',args state)))
