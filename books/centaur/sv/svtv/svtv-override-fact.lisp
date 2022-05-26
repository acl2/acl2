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
; Original author: Sol Swords <sol.swords@intel.com>

(in-package "SV")


(include-book "svtv-fsm-override")

(std::def-primitive-aggregate svtv-override-fact
  (name
   override-vars
   input-vars
   input-var-bindings
   output-vars
   output-parts
   output-part-vars
   hyp
   concl
   svtv
   enable
   triples-name
   triples-val
   lemma-defthm
   lemma-args
   no-lemmas
   hints
   pkg-sym))

(program)


(defun svtv-ovfact-input-var-bindings-alist-termlist (input-var-bindings)
  (b* (((when (atom input-var-bindings)) nil)
       ((list name term) (car input-var-bindings)))
    (cons `(cons ',name ,term)
          (svtv-ovfact-input-var-bindings-alist-termlist (cdr input-var-bindings)))))

(defun svtv-ovfact-var-alist-termlist (vars)
  (if (atom vars)
      nil
    (b* ((name (car vars)))
      (cons `(cons ',name ,name)
            (svtv-ovfact-var-alist-termlist (cdr vars))))))

(defun svtv-ovfact-override-test-alist (override-valnames triples triples-name)
  (b* (((when (Atom override-valnames)) nil)
       (trip (svar-override-triplelist-lookup-valvar (Car override-valnames) triples))
       ((unless trip) (er hard? 'def-svtv-override-fact "Override name not present in triples ~x0: ~x1~%"
                          (list triples-name) (car override-valnames)))
       ((svar-override-triple trip)))
    (cons (cons trip.testvar -1)
          (svtv-ovfact-override-test-alist (cdr override-valnames) triples triples-name))))

(defun svtv-ovfact-integerp-conclusions-aux (outputs)
  (if (Atom outputs)
      nil
    (cons `(integerp ,(car outputs))
          (svtv-ovfact-integerp-conclusions-aux (cdr outputs)))))

(defun svtv-ovfact-output-expressions (x)
  (b* (((svtv-override-fact x)))
    (append (set-difference-eq x.output-vars x.output-part-vars)
            x.output-parts)))

(defun svtv-ovfact-integerp-conclusions (x)
  (svtv-ovfact-integerp-conclusions-aux
   (svtv-ovfact-output-expressions x)))

(defun svtv-ovfact-initial-override-lemma (x)
  (declare (Xargs :mode :program))
  (b* (((svtv-override-fact x))
       (template '(<defthm> <name>-override-lemma
                    (implies <hyp>
                             (b* ((run (svtv-run (<svtv>)
                                                 (append <input-bindings>
                                                         <input-vars>
                                                         <override-tests>
                                                         <override-vals>)
                                                 :include '<outputs-list>))
                                  ((svassocs <outputs>) run))
                               (and <integerp-concls>
                                    <concl>)))
                    <args>)))
    (acl2::template-subst
     template
     :atom-alist `((<defthm> . ,x.lemma-defthm)
                   (<hyp> . ,x.hyp)
                   (<svtv> . ,x.svtv)
                   (<concl> . ,x.concl)
                   (<input-bindings> . (list . ,(svtv-ovfact-input-var-bindings-alist-termlist x.input-var-bindings)))
                   (<input-vars> . (list . ,(svtv-ovfact-var-alist-termlist x.input-vars)))
                   (<override-tests> . ',(svtv-ovfact-override-test-alist x.override-vars x.triples-val x.triples-name))
                   (<override-vals> . (list . ,(svtv-ovfact-var-alist-termlist x.override-vars)))
                   (<outputs-list> . ,x.output-vars))
     :splice-alist `((<outputs> . ,x.output-vars)
                     (<integerp-concls> . ,(svtv-ovfact-integerp-conclusions x))
                     (<args> . ,x.lemma-args))
     :str-alist `(("<NAME>" . ,(symbol-name x.name)))
     :pkg-sym x.pkg-sym)))




(defun svtv-ovfact-override-svassocs (override-valnames triples triples-name)
  (b* (((when (Atom override-valnames)) nil)
       (trip (svar-override-triplelist-lookup-valvar (Car override-valnames) triples))
       ((unless trip) (er hard? 'def-svtv-override-fact "Override name not present in triples ~x0: ~x1~%"
                          (list triples-name) (car override-valnames)))
       ((svar-override-triple trip)))
    (cons (if (eq trip.valvar trip.refvar)
              trip.valvar
            `(,trip.valvar ',trip.refvar))
          (svtv-ovfact-override-svassocs (cdr override-valnames) triples triples-name))))

(defun svtv-ovfact-input-binding-hyp-termlist (input-var-bindings)
  (b* (((when (atom input-var-bindings)) nil)
       ((list name term) (car input-var-bindings)))
    (cons `(equal ,name ,term)
          (svtv-ovfact-input-binding-hyp-termlist (cdr input-var-bindings)))))

(defun svtv-ovfact-mono-lemma (x)
  (b* (((svtv-override-fact x))
       (template '(defthm <name>-<<=-lemma
                    (b* (((svassocs <input-var-svassocs>
                                    <input-unbound-svassocs>) env))
                      (implies (and <input-binding-hyp>
                                    (svex-env-keys-no-1s-p
                                     (svar-override-triplelist->testvars (<triples>)) env))
                               (b* ((run (svtv-run (<svtv>) env))
                                    ((svassocs <override-svassocs>) run)
                                    (lemma-run (svtv-run (<svtv>)
                                                         (append <input-bindings>
                                                                 <input-vars>
                                                                 <override-tests>
                                                                 <override-vals>))))
                               (svex-env-<<= lemma-run run))))
                    :hints (("goal" :use ((:instance <svtv>-overrides-correct
                                           (spec-env env)
                                           (lemma-env
                                            (b* ((?run (svtv-run (<svtv>) env))
                                                 ((svassocs <override-svassocs>) run)
                                                 ((svassocs <input-unbound-svassocs>) env))
                                              (append <input-bindings>
                                                      <input-vars>
                                                      <override-tests>
                                                      <override-vals>)))))
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
     `((<svtv> . ,x.svtv)
       (<triples> . ,x.triples-name)
       (<input-bindings> . (list . ,(svtv-ovfact-input-var-bindings-alist-termlist x.input-var-bindings)))
       (<input-vars> . (list . ,(svtv-ovfact-var-alist-termlist x.input-vars)))
       (<override-tests> . ',(svtv-ovfact-override-test-alist x.override-vars x.triples-val x.triples-name))
       (<override-vals> . (list . ,(svtv-ovfact-var-alist-termlist x.override-vars))))
     :splice-alist
     `((<input-var-svassocs> . ,(strip-cars x.input-var-bindings))
       (<input-unbound-svassocs> . ,x.input-vars)
       (<override-svassocs> . ,(svtv-ovfact-override-svassocs x.override-vars x.triples-val x.triples-name))
       (<input-binding-hyp> .  ,(svtv-ovfact-input-binding-hyp-termlist x.input-var-bindings)))
     :str-alist `(("<NAME>" . ,(symbol-name x.name))
                  ("<SVTV>" . ,(symbol-name x.svtv)))
     :pkg-sym x.pkg-sym)))


(defun svtv-ovfact-override-var-instantiation (override-vars svtv)
  (if (atom override-vars)
      nil
    (cons `(,(car override-vars) (svex-env-lookup ',(car override-vars) (svtv-run (,svtv) env)))
          (svtv-ovfact-override-var-instantiation (cdr override-vars) svtv))))

(defun svtv-ovfact-input-var-instantiation (input-vars)
  (if (atom input-vars)
      nil
    (cons `(,(car input-vars) (svex-env-lookup ',(car input-vars) env))
          (svtv-ovfact-input-var-instantiation (cdr input-vars)))))

(defun svtv-ovfact-final-thm (x)
  (b* (((svtv-override-fact x))
       (template '(defthm <name>
                    (b* (((svassocs <input-var-svassocs>) env)
                         (run (svtv-run (<svtv>) env))
                         ((svassocs <override-svassocs>) run))
                      (implies (and <hyp>
                                    <input-binding-hyp>
                                    (svex-env-keys-no-1s-p
                                     (svar-override-triplelist->testvars (<triples>)) env))
                               (b* (((svassocs <outputs>) run))
                                 <concl>)))
                    :hints (:@ :no-lemmas <hints>)
                    (:@ (not :no-lemmas)
                     (("goal" :use (<name>-<<=-lemma
                                    (:instance <name>-override-lemma
                                     <override-var-instantiation>
                                     <input-var-instantiation>))
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
       (<svtv> . ,x.svtv)
       (<triples> . ,x.triples-name)
       (<hints> . ,x.hints))
     :splice-alist
     `((<input-var-svassocs> . ,(append x.input-vars (strip-cars x.input-var-bindings)))
       (<override-svassocs> . ,(svtv-ovfact-override-svassocs x.override-vars x.triples-val x.triples-name))
       (<input-binding-hyp> .  ,(svtv-ovfact-input-binding-hyp-termlist x.input-var-bindings))
       (<override-var-instantiation> . ,(svtv-ovfact-override-var-instantiation x.override-vars x.svtv))
       (<input-var-instantiation> . ,(svtv-ovfact-input-var-instantiation x.input-vars))
       (<outputs> . ,x.output-vars)
       (<enable> . ,x.enable))
     :str-alist `(("<NAME>" . ,(symbol-name x.name)))
     :features (and x.no-lemmas '(:no-lemmas))
     :pkg-sym x.pkg-sym)))


(defun find-illegal-variable (x)
  (if (atom x)
      nil
    (if (acl2::legal-variablep (car x))
        (find-illegal-variable (cdr x))
      x)))
    

(defun svtv-ovfact-check-variable-list (name x)
  (b* ((illegal-tail (find-illegal-variable x))
       ((when illegal-tail)
        (msg "~s0 must be a list of legal variables, but contains ~x1" name (car illegal-tail)))
       (dup-tail (acl2::hons-dups-p x))
       ((when dup-tail)
        (msg "~s0 cannot contain duplicates but ~x1 is duplicated" name (car dup-tail))))
    nil))

(defun svtv-ovfact-error (x)
  (b* (((svtv-override-fact x)))
    (or (svtv-ovfact-check-variable-list "Override-vars" x.override-vars)
        (svtv-ovfact-check-variable-list "Input-vars" x.input-vars)
        (svtv-ovfact-check-variable-list "Output-vars" x.output-vars)
        (and (not (acl2::doublet-listp x.input-var-bindings))
             "Input-var-bindings must be a list of two-element lists")
        (svtv-ovfact-check-variable-list "Keys of input-var-bindings" (strip-cars x.input-var-bindings))
        (let ((dup-tail (acl2::hons-dups-p (append x.input-vars
                                                   (strip-cars x.input-var-bindings)
                                                   x.override-vars
                                                   x.output-vars))))
          (and dup-tail
               (msg "Input, output, and override variables should not ~
                     intersect, but ~x0 is present in more than one"
                    (car dup-tail)))))))

(defun svtv-override-fact-events (x)
  (b* (((svtv-override-fact x))
       (err (svtv-ovfact-error x))
       ((when err) (er hard? `(def-svtv-override-fact ,x.name) "Error: ~@0" err)))
    `(defsection ,x.name
       ,@(and (not x.no-lemmas)
              `((local ,(svtv-ovfact-initial-override-lemma x))
                (local ,(svtv-ovfact-mono-lemma x))))
       ,(svtv-ovfact-final-thm x))))

; (table svtv-override-fact-defaults nil nil :clear)

(defun svtv-ovfact-translate-lst (x ctx w state)
  (declare (xargs :stobjs state))
  (if (atom x)
      (value nil)
    (er-let* ((first (acl2::translate (car x) t nil nil ctx w state))
              (rest (svtv-ovfact-translate-lst (cdr x) ctx w state)))
      (value (cons first rest)))))

(define svtv-unsigned-byte-hyps ((x svar-boolmasks-p))
  :hooks nil
  (b* (((when (atom x)) nil)
       ((unless (mbt (consp (car x)))) (svtv-unsigned-byte-hyps (cdr x)))
       ((cons var mask) (car x)))
    (cons `(unsigned-byte-p ,(integer-length mask) ,var)
          (svtv-unsigned-byte-hyps (cdr x)))))

(defun svtv-override-fact-fn (name args state)
  (declare (xargs :stobjs state))
  (b* ((defaults (table-alist 'svtv-override-fact-defaults (w state)))
       (ctx `(def-svtv-override-fact ,name))
       ((std::extract-keyword-args
         :defaults defaults
         :ctx ctx
         svtv
         override-vars
         input-vars
         output-vars
         output-parts
         input-var-bindings
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
       (triples (acl2::template-subst
                 '<svtv>-pipeline-override-triples
                 :str-alist `(("<SVTV>" . ,(symbol-name svtv)))
                 :pkg-sym pkg-sym))
       ((mv err triples-val) (magic-ev-fncall triples nil state t t))
       ((when err) (er soft ctx "Couldn't evaluate ~x0" (list triples)))
       ((mv err trans-parts state) (svtv-ovfact-translate-lst output-parts ctx (w state) state))
       ((when err) (er soft ctx "Couldn't translate output-parts: ~@0~%" err))
       (output-part-vars (all-vars1-lst trans-parts nil))
       ((mv err svtv-val) (magic-ev-fncall svtv nil state t t))
       ((when err) (er soft ctx "Couldn't evaluate ~x0" (list svtv)))
       (hyp (if unsigned-byte-hyps
                (b* ((inmasks (svtv->inmasks svtv-val))
                     (inputs (append input-vars override-vars))
                     (masks (acl2::fal-extract inputs inmasks)))
                  `(and ,@(svtv-unsigned-byte-hyps masks) ,hyp))
              hyp)))
       
    (value
     (svtv-override-fact-events
      (make-svtv-override-fact
       :name name
       :override-vars override-vars
       :input-vars input-vars
       :output-vars output-vars
       :output-parts output-parts
       :output-part-vars output-part-vars
       :input-var-bindings input-var-bindings
       :enable enable
       :hyp hyp
       :concl concl
       :svtv svtv
       :triples-name triples
       :triples-val triples-val
       :lemma-defthm lemma-defthm
       :lemma-args lemma-args
       :hints hints
       :no-lemmas no-lemmas
       :pkg-sym pkg-sym)))))

(defmacro def-svtv-override-fact (name &rest args)
  `(make-event (svtv-override-fact-fn ',name ',args state)))
     
                           


(defxdoc def-svtv-override-fact
  :parents (svtv-data)
  :short "Prove a theorem about an SVTV using a specific input env, perhaps
with overrides, then generalize it to remove overrides and reliance on a
particular shape of input env."
  :long "
<p>Usage:</p>
@({
 (def-svtv-override-fact theorem-name
   :svtv svtv-name
   :input-vars input-variable-list
   :input-var-bindings input-variable-binding-list
   :override-vars override-variable-list
   :output-vars output-variable-list
   :output-parts output-part-list
   :hyp hypothesis-term
   :concl conclusion-term
   :enable rules-list
   :unsigned-byte-hyps nil
   :no-lemmas nil)
 })

<p>For each of the keyword arguments, if absent a default will be looked up in
the @(see table) @('svtv-override-fact-defaults'), which may be (locally)
modified by users in order to avoid (for example) the need to repeatedly
specify the same SVTV in every form.</p>

<p>Prerequisites: The SVTV in question must have certain theorems already
proved about it, in particular those generated by @(see
def-svtv-override-thms).  (This event has its own prerequisites as well.)</p>

<p>We briefly describe the arguments of the macro and then we'll describe the
theorem proved in FGL and the generalized corollary this macro generates.</p>

<h3>Arguments</h3>

<ul>
<li>@(':svtv') is the name of the SVTV</li>
<li>@(':input-vars') are the names of any input variables of the SVTV that will
appear in the hypothesis or conclusion, except those that are bound in
@(':input-var-bindings')</li>
<li>@(':input-var-bindings') is a list of @('let')-like bindings of input
variables to expressions</li>

<li>@(':override-vars') is a list of override-value variables of the SVTV to be
overridden in the FGL theorem.  These should have corresponding override test
and reference variables (i.e. they should appear in the
@('<svtv>-pipeline-override-triples') generated by @('def-svtv-override-thms').</li>

<li>@(':output-vars') is a list of output variables of the SVTV that are used in the conclusion.</li>

<li>@(':output-parts') is a list of 4vec expressions -- part selects, zero
extends, shifts, concatenations -- of the output variables.  The given parts of
the outputs will be proved to be integerp in order to use a monotonicity
argument.  Variables that are not mentioned in output-parts will be proved
integerp as a whole.</li>

<li>@(':hyp') is a term (default T), which may reference variables
listed in input-vars and override-vars as well as variables used in the
expressions of input-bindings</li>

<li>@(':concl') is a term which may reference the same variables available to
@(':hyp') as well as the output-vars.</li>

<li>@(':enable') is a list of rules to be included in the theory for the final
generalized theorm, mainly useful when specifying @(':output-parts').</li>

<li>@(':lemma-defthm') defaults to @('fgl::def-fgl-thm') but can be set
to (e.g.) @('defthm') or @('fgl::def-fgl-param-thm') to change how the initial
lemma is proved.</li>

<li>@(':lemma-args') gives additional arguments to be passed to the form
proving the initial lemma, which could be hints for a @('defthm') form or FGL
keyword args for @('fgl::def-fgl-thm') or @('fgl::def-fgl-param-thm').</li>

<li>@(':no-lemmas') says to skip the initial override theorem and monotonicity lemma
and tries to prove the final theorem directly, with the hints given by the user.</li>

<li>@(':hints') are hints for the final theorem, only used if @(':no-lemmas') is set.</li>

<li>@(':unsigned-byte-hyps') says to automatically add @('unsigned-byte-p')
hypotheses for each input and override variable.</li>
</ul>

<h3>Initial override theorem</h3>

<p>The initial override theorem is typically proved with FGL. It says that
under the given hypotheses, a run of the SVTV on a particular, explicitly
constructed environment produces outputs satisfying the conclusion.  In
addition, it proves that those outputs are integers (whereas they could
otherwise be arbitrary @(see 4vec)s including X and Z bits).  The environment
is constructed as follows:</p>

<ul>
<li>Input variables bound in @(':input-var-bindings') are bound to their respective values</li>
<li>Input variables listed in @(':input-vars') are bound to variables of the same name</li>
<li>Override value variables listed in @(':override-vars') are bound to variables of the same name</li>
<li>Override test variables corresponding to the override value variables
listed in @(':override-vars') are all bound to -1.</li>
</ul>

<p>For example, the following form:</p>

@({
 (def-svtv-override-fact partial-prods-to-product
   :svtv multiplier-svtv
   :input-var-bindings ((opcode *mul-opcode*))
   :override-vars (partial-products)
   :output-vars (product)
   :hyp (unsigned-byte-p 128 partial-products)
   :concl (equal product (sum-partial-products partial-products)))
 })
<p>produces approximately the following initial lemma:</p>
@({
 (fgl::def-fgl-thm partial-prods-to-product-override-lemma
   (implies (unsigned-byte-p 128 partial-products)
            (b* ((run (svtv-run (multiplier-svtv)
                                `((opcode . ,*mul-opcode*)
                                  (partial-products . ,partial-products)
                                  (override-partial-products . -1))))
                 (product (svex-env-lookup 'product run)))
              (and (integerp product)
                   (equal product (sum-partial-products partial-products))))))
 })

<h3>Generalized theorem</h3>

<p>The generalized theorem refers to a single free variable @('env') rather
than a free variable for each input and override value.  It binds @('run') to
the run of the SVTV on that env.  Input variables -- both those listed in
@(':input-vars') and the keys of @(':input-var-bindings') -- are bound to their
lookups in @('env'), outputs are bound (as usual) to their lookups in @('run'),
and override variables are bound to the lookups of their respective reference
variables in @('run').  In addition to the explicit hypothesis, the theorem
adds hypotheses that each variable bound in @(':input-var-bindings') is bound
to its respective value in @('env'), and one more hypothesis stating that none
of the override test variables of the SVTV pipeline-override-triples are bound
to anything containing 1 bits (effectively, @('env') does not set any
conditional overrides).</p>

<p>For example, the form above produces approximately the following generalized theorem:</p>
@({
 (defthm partial-prods-to-product
   (b* ((opcode (svex-env-lookup 'opcode env))
        (run (svtv-run (multiplier-svtv) env))
        (partial-products (svex-env-lookup 'partial-products run)))
     (implies (and (unsigned-byte-p 128 partial-products)
                   (equal opcode *mul-opcode*)
                   (svex-env-keys-no-1s-p
                    (svar-override-triplelist->testvars
                     (multiplier-svtv-pipeline-override-triples))
                    env))
              (b* ((product (svex-env-lookup 'product run)))
                (equal product (sum-partial-products partial-products))))))
 })
")
