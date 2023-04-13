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

(include-book "override-common")
(include-book "structure")
(include-book "centaur/fgl/portcullis" :dir :system)

(local (std::add-default-post-define-hook :fix))

(define svtv-override-triplemap->tests ((triplemap svtv-override-triplemap-p))
  :returns (tests svexlist-p)
  (if (atom triplemap)
      nil
    (if (mbt (and (consp (car triplemap))
                  (svar-p (caar triplemap))))
        (cons (svtv-override-triple->test (cdar triplemap))
              (svtv-override-triplemap->tests (cdr triplemap)))
      (svtv-override-triplemap->tests (cdr triplemap))))
  ///
  (local (in-theory (enable svtv-override-triplemap-fix))))

(define svtv-override-triplemaplist->tests ((x svtv-override-triplemaplist-p))
  :returns (tests svexlist-p)
  (if (atom x)
      nil
    (append (svtv-override-triplemap->tests (car x))
            (svtv-override-triplemaplist->tests (cdr x)))))

(define svtv-override-triplemap->vals ((triplemap svtv-override-triplemap-p))
  :returns (vals svexlist-p)
  (if (atom triplemap)
      nil
    (if (mbt (and (consp (car triplemap))
                  (svar-p (caar triplemap))))
        (cons (svtv-override-triple->val (cdar triplemap))
              (svtv-override-triplemap->vals (cdr triplemap)))
      (svtv-override-triplemap->vals (cdr triplemap))))
  ///
  (local (in-theory (enable svtv-override-triplemap-fix))))

(define svtv-override-triplemaplist->vals ((x svtv-override-triplemaplist-p))
  :returns (vals svexlist-p)
  (if (atom x)
      nil
    (append (svtv-override-triplemap->vals (car x))
            (svtv-override-triplemaplist->vals (cdr x)))))




(std::def-primitive-aggregate svtv-generalized-thm
  (name
   spec-override-vars
   spec-override-var-bindings
   override-vars
   override-var-bindings
   input-vars
   input-var-bindings
   output-vars
   output-parts
   output-part-vars
   hyp
   concl
   run-before-concl
   svtv
   ideal
   svtv-spec
   enable
   triples-name
   triple-val-alist
   lemma-nonlocal
   lemma-defthm
   lemma-args
   lemma-use-ideal
   lemma-use-svtv-spec
   no-lemmas
   no-integerp
   final-defthm
   final-args
   hints
   rule-classes
   pkg-sym))

(program)


(defun svtv-genthm-input-var-bindings-alist-termlist (input-var-bindings)
  (b* (((when (atom input-var-bindings)) nil)
       ((list name term) (car input-var-bindings)))
    (cons `(cons ',name ,term)
          (svtv-genthm-input-var-bindings-alist-termlist (cdr input-var-bindings)))))

(defun svtv-genthm-var-alist-termlist (vars)
  (if (atom vars)
      nil
    (b* ((name (car vars)))
      (cons `(cons ',name ,name)
            (svtv-genthm-var-alist-termlist (cdr vars))))))

(defun svtv-genthm-override-test-alist (override-valnames triple-val-alist triples-name)
  (b* (((when (Atom override-valnames)) nil)
       (valvar (car override-valnames))
       (trip (cdr (hons-get valvar triple-val-alist)))
       ((unless trip) (er hard? 'def-svtv-generalized-thm "Override name not present in triples ~x0: ~x1~%"
                          (list triples-name) (car override-valnames)))
       ((svtv-override-triple trip))
       ((unless (svex-case trip.test :var))
        (svtv-genthm-override-test-alist (cdr override-valnames) triple-val-alist triples-name)))
    (cons (cons (svex-var->name trip.test) -1)
          (svtv-genthm-override-test-alist (cdr override-valnames) triple-val-alist triples-name))))

(defun svtv-genthm-integerp-conclusions-aux (outputs)
  (if (Atom outputs)
      nil
    (cons `(integerp ,(car outputs))
          (svtv-genthm-integerp-conclusions-aux (cdr outputs)))))

(defun svtv-genthm-output-expressions (x)
  (b* (((svtv-generalized-thm x)))
    (append (set-difference-eq x.output-vars x.output-part-vars)
            x.output-parts)))

(defun svtv-genthm-integerp-conclusions (x)
  (svtv-genthm-integerp-conclusions-aux
   (svtv-genthm-output-expressions x)))

(define svex-env-extract-non-2vecs ((vars svarlist-p)
                                    (env svex-env-p))
  :mode :logic
  :returns (non-2vecs svex-env-p)
  (if (atom vars)
      nil
    (b* ((look (sv::svex-env-lookup (car vars) env))
         ((when (sv::2vec-p look))
          (svex-env-extract-non-2vecs (cdr vars) env)))
      (cons (cons (svar-fix (car vars)) look)
            (svex-env-extract-non-2vecs (cdr vars) env)))))

(defun svtv-genthm-initial-override-lemma (x)
  (declare (Xargs :mode :program))
  (b* (((svtv-generalized-thm x))
       (template '(<defthm> <name>-override-lemma
                    (implies <hyp>
                             (b* ((run (:@ (and (not :use-ideal)
                                                (not :use-svtv-spec))
                                           (svtv-run (<svtv>)
                                                     (append <input-bindings>
                                                             <input-vars>
                                                             <override-tests>
                                                             <override-bindings>
                                                             <override-vals>)
                                                     :include
                                                     '<outputs-list>))
                                       (:@ (or :use-ideal :use-svtv-spec)
                                           (svex-env-reduce '<outputs-list>
                                                            (svtv-spec-run ((:@ :use-ideal <ideal>)
                                                                            (:@ :use-svtv-spec <svtv-spec>))
                                                                           (append <input-bindings>
                                                                                   <input-vars>
                                                                                   <override-tests>
                                                                                   <override-bindings>
                                                                                   <override-vals>)))))
                                  ((svassocs <outputs>) run))
                               (progn$
                                <run-before-concl>
                                (and (:@ (not :no-integerp)
                                      (or (and <integerp-concls>)
                                          (progn$
                                           (cw "*** Failed: Some output variables contained Xes/Zs:~%")
                                           (svtv-print-alist-readable
                                            (svex-env-extract-non-2vecs
                                             '<outputs-list> run))
                                           nil)))
                                     <concl>))))
                    <args>)))
    (acl2::template-subst
     template
     :atom-alist `((<defthm> . ,x.lemma-defthm)
                   (<hyp> . ,x.hyp)
                   (<svtv> . ,x.svtv)
                   (<svtv-spec> . ,x.svtv-spec)
                   (<ideal> . ,x.ideal)
                   (<concl> . ,x.concl)
                   (<input-bindings> . (list . ,(svtv-genthm-input-var-bindings-alist-termlist x.input-var-bindings)))
                   (<input-vars> . (list . ,(svtv-genthm-var-alist-termlist x.input-vars)))
                   (<override-tests> . ',(svtv-genthm-override-test-alist
                                          (append (alist-keys x.spec-override-var-bindings)
                                                  (alist-keys x.override-var-bindings)
                                                  x.spec-override-vars
                                                  x.override-vars)
                                          x.triple-val-alist x.triples-name))
                   (<override-bindings> . (list . ,(svtv-genthm-input-var-bindings-alist-termlist
                                                    (append x.spec-override-var-bindings
                                                            x.override-var-bindings))))
                   (<override-vals> . (list . ,(svtv-genthm-var-alist-termlist (append x.spec-override-vars x.override-vars))))
                   (<outputs-list> . ,x.output-vars))
     :splice-alist `((<run-before-concl> . ,(and x.run-before-concl (list x.run-before-concl)))
                     (<outputs> . ,x.output-vars)
                     (<integerp-concls> . ,(if x.no-integerp nil (svtv-genthm-integerp-conclusions x)))
                     (<args> . ,x.lemma-args))
     :str-alist `(("<NAME>" . ,(symbol-name x.name)))
     :features (append (and x.lemma-use-ideal '(:use-ideal))
                       (and x.lemma-use-svtv-spec '(:use-svtv-spec))
                       (and x.no-integerp '(:no-integerp)))
     :pkg-sym x.pkg-sym)))



(defun svtv-genthm-override-svassocs (override-valnames triple-val-alist triples-name)
  (b* (((when (Atom override-valnames)) nil)
       (valvar (car override-valnames))
       (trip (cdr (hons-get valvar triple-val-alist)))
       ((unless trip) (er hard? 'def-svtv-generalized-thm "Override name not present in triples ~x0: ~x1~%"
                          (list triples-name) (car override-valnames)))
       ((svtv-override-triple trip)))
    (cons (if (eq valvar trip.refvar)
              valvar
            `(,valvar ',trip.refvar))
          (svtv-genthm-override-svassocs (cdr override-valnames) triple-val-alist triples-name))))


(defun svtv-genthm-input-binding-hyp-termlist (input-var-bindings)
  (b* (((when (atom input-var-bindings)) nil)
       ((list name term) (car input-var-bindings)))
    (cons `(equal ,name ,term)
          (svtv-genthm-input-binding-hyp-termlist (cdr input-var-bindings)))))




(defun svtv-genthm-input-var-instantiation (input-vars)
  (if (atom input-vars)
      nil
    (cons `(,(car input-vars) (svex-env-lookup ',(car input-vars) env))
          (svtv-genthm-input-var-instantiation (cdr input-vars)))))




(defun find-illegal-variable (x)
  (if (atom x)
      nil
    (if (acl2::legal-variablep (car x))
        (find-illegal-variable (cdr x))
      x)))
    

(defun svtv-genthm-check-variable-list (name x)
  (b* ((illegal-tail (find-illegal-variable x))
       ((when illegal-tail)
        (msg "~s0 must be a list of legal variables, but contains ~x1" name (car illegal-tail)))
       (dup-tail (acl2::hons-dups-p x))
       ((when dup-tail)
        (msg "~s0 cannot contain duplicates but ~x1 is duplicated" name (car dup-tail))))
    nil))

(defun svtv-genthm-error (x)
  (b* (((svtv-generalized-thm x)))
    (or (svtv-genthm-check-variable-list "Override-vars" x.override-vars)
        (svtv-genthm-check-variable-list "Input-vars" x.input-vars)
        (svtv-genthm-check-variable-list "Output-vars" x.output-vars)
        (and (not (acl2::doublet-listp x.input-var-bindings))
             "Input-var-bindings must be a list of two-element lists")
        (svtv-genthm-check-variable-list "Keys of input-var-bindings" (strip-cars x.input-var-bindings))
        (let ((dup-tail (acl2::hons-dups-p (append x.input-vars
                                                   (strip-cars x.input-var-bindings)
                                                   x.override-vars
                                                   x.output-vars))))
          (and dup-tail
               (msg "Input, output, and override variables should not ~
                     intersect, but ~x0 is present in more than one"
                    (car dup-tail)))))))




(defun svtv-genthm-translate-lst (x ctx w state)
  (declare (xargs :stobjs state))
  (if (atom x)
      (value nil)
    (er-let* ((first (acl2::translate (car x) t nil nil ctx w state))
              (rest (svtv-genthm-translate-lst (cdr x) ctx w state)))
      (value (cons first rest)))))

(define svtv-unsigned-byte-hyps ((x svar-boolmasks-p))
  :hooks nil
  (b* (((when (atom x)) nil)
       ((unless (mbt (consp (car x)))) (svtv-unsigned-byte-hyps (cdr x)))
       ((cons var mask) (car x)))
    (cons `(unsigned-byte-p ,(integer-length mask) ,var)
          (svtv-unsigned-byte-hyps (cdr x)))))




;; In the context of these svtv-genthm functions, triples is an alist mapping
;; value variables to reference variables, derived from the triplemaplist.
(defun svtv-genthm-override-var-instantiation (override-vars triple-val-alist triples-name run)
  (b* (((when (Atom override-vars)) nil)
       (valvar (car override-vars))
       (trip (cdr (hons-get valvar triple-val-alist)))
       ((unless trip) (er hard? 'def-svtv-generalized-thm "Override name not present in triples ~x0: ~x1~%"
                            (list triples-name) valvar)))
    (cons `(,valvar (svex-env-lookup ',(svtv-override-triple->refvar trip) ,run))
          (svtv-genthm-override-var-instantiation (cdr override-vars) triple-val-alist triples-name run))))

(defun svtv-genthm-spec-override-var-instantiation (override-vars)
  (b* (((when (Atom override-vars)) nil)
       (valvar (car override-vars)))
    (cons `(,valvar (svex-env-lookup ',valvar env))
          (svtv-genthm-spec-override-var-instantiation (cdr override-vars)))))


(defun svtv-genthm-override-subst (override-vars triple-val-alist triples-name)
  (b* (((when (Atom override-vars)) nil)
       (valvar (car override-vars))
       (trip (cdr (hons-get valvar triple-val-alist)))
       ((unless trip) (er hard? 'def-svtv-generalized-thm "Override name not present in triples ~x0: ~x1~%"
                          (list triples-name) valvar))
       ((svtv-override-triple trip)))
    ;(cons (cons valvar trip.val)
    (if (svex-case trip.test :var)
        (cons (cons (svex-var->name trip.test) -1)
              (svtv-genthm-override-subst (cdr override-vars) triple-val-alist triples-name))
      (svtv-genthm-override-subst (cdr override-vars) triple-val-alist triples-name))))





(defun svtv-genthm-final-thm (x)
  (declare (xargs :mode :program))
  (b* (((svtv-generalized-thm x))
       (run (cond (x.ideal     `(svtv-spec-run (,x.ideal) env :base-ins base-ins :initst initst))
                  (x.svtv-spec `(svtv-spec-run (,x.svtv-spec) env :base-ins base-ins :initst initst))
                  (t           `(svtv-run (,x.svtv) env))))
       (template
         '(<defthm> <name>
            (b* (((svassocs <input-var-svassocs>
                            <spec-override-svassocs>) env)
                 (run <run>
                      )
                 ((svassocs <override-svassocs>) run))
              (implies (and <hyp>
                            <input-binding-hyp>
                            <override-binding-hyp>
                            (svtv-override-triplemaplist-envs-match
                             (<triplemaps>) env <const-overrides>)
                            (:@ (or :use-ideal :use-svtv-spec)
                             (svarlist-override-p (svex-envlist-all-keys base-ins) nil)))
                       (b* (((svassocs <outputs>) run))
                         <concl>)))
            <args>
            (:@ :no-lemmas <hints-hints>)
            (:@ (not :no-lemmas)
             :hints (("Goal" :use ((:instance
                                    (:@ (and (not :use-ideal)
                                             (not :use-svtv-spec))
                                     <svtv>-refines-<svtv>)
                                    (:@ :use-ideal
                                     (:@ :lemma-use-ideal <ideal>-refines-<ideal>)
                                     (:@ (not :lemma-use-ideal) <ideal>-refines-<svtv>))
                                    (:@ :use-svtv-spec
                                     (:@ :lemma-use-svtv-spec <svtv>-spec-refines-<svtv>-spec)
                                     (:@ (not :lemma-use-svtv-spec) <svtv>-spec-refines-<svtv>))
                                    (spec-pipe-env env)
                                    (:@ (or :use-ideal :use-svtv-spec)
                                     (spec-base-ins base-ins)
                                     (spec-initst initst))
                                    (pipe-env (b* ((?run <run>)
                                                   ((svassocs <override-inst-svassocs>) run)
                                                   ((svassocs <spec-override-inst-svassocs>
                                                              <input-unbound-svassocs>) env))
                                                (APPEND <input-bindings>
                                                        <input-vars>
                                                        <override-tests>
                                                        <override-bindings>
                                                        <override-vals>))))
                                   (:instance <name>-override-lemma
                                    <spec-override-var-instantiation>
                                    <override-var-instantiation>
                                    <input-var-instantiation>))
                      :in-theory (acl2::e/d**
                                  (;; (:EXECUTABLE-COUNTERPART <SVTV>-TRIPLEMAPLIST)
                                   (:REWRITE SVARLIST-P-OF-<SVTV>-INPUT-VARS)
                                   (:ruleset svtv-generalized-thm-rules)
                                   <enable>)
                                  )
                      :do-not '(generalize fertilize eliminate-destructors)
                      :do-not-induct t
                      )
                     . <hints>))
            :rule-classes <rule-classes>)))
    (acl2::template-subst
     template
     :atom-alist
     `((<hyp> . ,x.hyp)
       (<concl> . ,x.concl)
       (<ideal> . ,x.ideal)
       (<defthm> . ,x.final-defthm)
       (<triplemaps> . ,x.triples-name)
       (<const-overrides> . ',(svtv-genthm-override-subst
                               (append (alist-keys x.spec-override-var-bindings) x.spec-override-vars)
                               x.triple-val-alist x.triples-name))
       (<run> . ,run)
       (<hints> . ,x.hints)
       (<input-bindings> . (list . ,(svtv-genthm-input-var-bindings-alist-termlist x.input-var-bindings)))
       (<input-vars> . (list . ,(svtv-genthm-var-alist-termlist x.input-vars)))
       (<override-tests> . ',(svtv-genthm-override-test-alist
                              (append (alist-keys x.override-var-bindings)
                                      (alist-keys x.spec-override-var-bindings)
                                      x.spec-override-vars
                                      x.override-vars)
                              x.triple-val-alist x.triples-name))
       (<override-bindings> . (list . ,(svtv-genthm-input-var-bindings-alist-termlist
                                        (append x.spec-override-var-bindings x.override-var-bindings))))
       (<override-vals> . (list . ,(svtv-genthm-var-alist-termlist (append x.spec-override-vars x.override-vars))))
       (<rule-classes> . ,x.rule-classes))
     :splice-alist
     `((<input-var-svassocs> . ,(append x.input-vars (strip-cars x.input-var-bindings)))
       (<input-unbound-svassocs> . ,x.input-vars)
       (<override-svassocs> . ,(svtv-genthm-override-svassocs (append x.override-vars (alist-keys x.override-var-bindings))
                                                              x.triple-val-alist x.triples-name))
       (<override-inst-svassocs> . ,(svtv-genthm-override-svassocs x.override-vars
                                                              x.triple-val-alist x.triples-name))
       (<spec-override-svassocs> . ,(append x.spec-override-vars (alist-keys x.spec-override-var-bindings)))
       (<spec-override-inst-svassocs> . ,x.spec-override-vars
                                      ;; (svtv-genthm-override-svassocs x.spec-override-vars
                                      ;;                                   x.triple-val-alist x.triples-name)
                                      )
       (<input-binding-hyp> .  ,(svtv-genthm-input-binding-hyp-termlist x.input-var-bindings))
       (<override-binding-hyp> .  ,(svtv-genthm-input-binding-hyp-termlist (append x.spec-override-var-bindings
                                                                                   x.override-var-bindings)))
       (<override-var-instantiation> . ,(svtv-genthm-override-var-instantiation x.override-vars x.triple-val-alist x.triples-name run))
       (<spec-override-var-instantiation> . ,(svtv-genthm-spec-override-var-instantiation x.spec-override-vars))
       (<input-var-instantiation> . ,(svtv-genthm-input-var-instantiation x.input-vars))
       (<outputs> . ,x.output-vars)
       (<enable> . ,x.enable)
       (<hints-hints> . ,(and x.hints `(:hints ,x.hints)))
       (<args> . ,x.final-args))
     :str-alist `(("<NAME>" . ,(symbol-name x.name))
                  ("<SVTV>" . ,(symbol-name x.svtv))
                  ("<IDEAL>" . ,(symbol-name x.ideal)))
     :features (append (and x.no-lemmas '(:no-lemmas))
                       (and x.ideal '(:use-ideal))
                       (and x.svtv-spec '(:use-svtv-spec))
                       (and x.lemma-use-ideal '(:lemma-use-ideal))
                       (and x.lemma-use-svtv-spec '(:lemma-use-svtv-spec)))
     :pkg-sym x.pkg-sym)))




(defun svtv-generalized-thm-events (x)
  (b* (((svtv-generalized-thm x))
       (err (svtv-genthm-error x))
       ((when err) (er hard? `(def-svtv-generalized-thm ,x.name) "Error: ~@0" err)))
    `(defsection ,x.name
       ,@(and (not x.no-lemmas)
              (let ((lemma (svtv-genthm-initial-override-lemma x)))
                (if x.lemma-nonlocal
                    `(,lemma)
                  `((local ,lemma)))))
       ,(svtv-genthm-final-thm x))))



(defun svtv-generalized-thm-fn (name args state)
  (declare (xargs :stobjs state))
  (b* ((defaults (table-alist 'svtv-generalized-thm-defaults (w state)))
       (ctx `(def-svtv-generalized-thm ,name))
       ((std::extract-keyword-args
         :defaults defaults
         :ctx ctx
         svtv
         ideal
         svtv-spec
         spec-override-var-bindings
         spec-override-vars
         override-var-bindings
         override-vars
         input-vars
         output-vars
         output-parts
         input-var-bindings
         enable
         unsigned-byte-hyps
         (hyp 't)
         concl
         (run-before-concl 'nil)
         (lemma-defthm 'fgl::def-fgl-thm)
         lemma-args
         lemma-nonlocal
         lemma-use-ideal
         lemma-use-svtv-spec
         no-lemmas
         no-integerp
         hints
         (final-defthm 'defthm)
         final-args
         (rule-classes ':rewrite)
         (pkg-sym name))
        args)

       ((mv err trans-parts state) (svtv-genthm-translate-lst output-parts ctx (w state) state))
       ((when err) (er soft ctx "Couldn't translate output-parts: ~@0~%" err))
       (output-part-vars (all-vars1-lst trans-parts nil))
       ((mv err svtv-val) (magic-ev-fncall svtv nil state t t))
       ((when err) (er soft ctx "Couldn't evaluate ~x0" (list svtv)))
       (triplemaplist (acl2::template-subst
                 '<svtv>-triplemaplist
                 :str-alist `(("<SVTV>" . ,(symbol-name svtv)))
                 :pkg-sym pkg-sym))
       ((mv err triplemaplist-val) (magic-ev-fncall triplemaplist nil state t t))
       ((when err) (er soft ctx "Couldn't evaluate ~x0" (list triplemaplist)))

       (triplelist (svtv-override-triplemaplist-to-triplelist triplemaplist-val))
       (triple-val-alist (svtv-override-triplelist-val-alist triplelist))


       (input-vars (if (equal input-vars :all)
                       (b* ((all-ins (svtv->ins svtv-val))
                            (ovr-controls (svex-alist-vars (svtv-override-triplemaplist->tests triplemaplist-val)))
                            (ovr-signals (svex-alist-vars (svtv-override-triplemaplist->vals triplemaplist-val)))
                            (all-ins (acl2::hons-set-diff all-ins (append ovr-controls ovr-signals
                                                                          (alist-keys input-var-bindings)))))
                         all-ins)
                     input-vars))
       (hyp (if unsigned-byte-hyps
                (b* ((inmasks (svtv->inmasks svtv-val))
                     (inputs (append input-vars override-vars spec-override-vars))
                     (masks (acl2::fal-extract inputs inmasks))
                     (hyps (if (eq (car hyp) 'and) (cdr hyp) (list hyp))))
                  `(and ,@(svtv-unsigned-byte-hyps masks) . ,hyps))
              hyp))

       ;; (override-subst (make-fast-alist (svtv-genthm-override-subst override-vars triple-val-alist triplemaplist)))
       ;; (mux-<<=-triples
       ;;  (svtv-override-triplemaplist-analyze-necessary-mux-<<=-checks triplemaplist-val override-subst))
       ;; (muxtests (svtv-override-triplemaplist-analyze-necessary-muxtests triplemaplist-val override-subst (make-fast-alist const-overrides)))

       ;; (constlist-hyp `(and ,(if mux-<<=-triples
       ;;                           `(svtv-override-triplelist-muxes-<<=-of-nil(if consts
       ;;                    `(svtv-override-constantlist-ok ',consts run)
       ;;                  t))
       ((acl2::with-fast triple-val-alist)))

    (value
     (svtv-generalized-thm-events
      (make-svtv-generalized-thm
       :name name
       :override-vars override-vars
       :override-var-bindings override-var-bindings
       :spec-override-vars spec-override-vars
       :spec-override-var-bindings spec-override-var-bindings
       :input-vars input-vars
       :output-vars output-vars
       :output-parts output-parts
       :output-part-vars output-part-vars
       :input-var-bindings input-var-bindings
       :enable enable
       :hyp hyp
       :concl concl
       :run-before-concl run-before-concl
       :svtv svtv
       :svtv-spec svtv-spec
       :ideal ideal
       :lemma-nonlocal lemma-nonlocal
       :lemma-defthm lemma-defthm
       :lemma-args lemma-args
       :lemma-use-ideal lemma-use-ideal
       :lemma-use-svtv-spec lemma-use-svtv-spec
       :hints hints
       :triples-name triplemaplist
       :triple-val-alist triple-val-alist
       :no-lemmas no-lemmas
       :no-integerp no-integerp
       :final-defthm final-defthm
       :final-args final-args
       :rule-classes rule-classes
       :pkg-sym pkg-sym)))))

(defmacro def-svtv-generalized-thm (name &rest args)
  `(make-event (svtv-generalized-thm-fn ',name ',args state)))


