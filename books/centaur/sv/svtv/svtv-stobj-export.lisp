; Centaur SV Hardware Verification Tutorial
; Copyright (C) 2016 Centaur Technology
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
; Original authors: Sol Swords <sswords@centtech.com>


(in-package "SV")

(include-book "svtv-stobj")
(include-book "centaur/misc/nth-equiv" :dir :system)
(include-book "clause-processors/meta-extract-user" :dir :system)
(include-book "clause-processors/pseudo-term-fty" :dir :system)

(defsection svtv-data-obj
  (local (defun svtv-data-obj-fields-from-decls (decls)
           (if (atom decls)
               nil
             (cons (list (caar decls)
                         (cadr (assoc-keyword :pred (cdar decls))))
                   (svtv-data-obj-fields-from-decls (cdr decls))))))

  (make-event
   `(defprod svtv-data-obj
      ,(svtv-data-obj-fields-from-decls *svtv-data-nonstobj-fields*))))

(defsection svtv-data-to-obj
  (local (defun svtv-data-obj-ctor-from-decls (decls)
           (if (atom decls)
               nil
             (append
              `(,(intern-in-package-of-symbol (symbol-name (caar decls)) :keyword)
                (,(intern-in-package-of-symbol
                   (concatenate 'string "SVTV-DATA->" (symbol-name (caar decls)))
                   'sv-package)
                 svtv-data))
              (svtv-data-obj-ctor-from-decls (cdr decls))))))

  (make-event
   `(define svtv-data-to-obj (svtv-data)
      :returns (obj svtv-data-obj-p)
      (make-svtv-data-obj
       . ,(svtv-data-obj-ctor-from-decls *svtv-data-nonstobj-fields*)))))



(defsection svtv-data-to-stobj-logic
  (local (defun svtv-data-list-elems-from-decls (decls)
           (if (atom decls)
               nil
             (cons (intern-in-package-of-symbol
                    (concatenate 'string "X." (symbol-name (caar decls)))
                    'sv-package)
                   (svtv-data-list-elems-from-decls (cdr decls))))))

  (local (defun svtv-data-obj-to-stobj-thms-from-decls (decls)
           (declare (xargs :mode :program))
           (if (atom decls)
               nil
             (cons (acl2::template-subst
                    '(defret svtv-data-><field>-of-<fn>
                       (equal (svtv-data$c-><field> new-svtv-data)
                              (svtv-data-obj-><field> x))
                       :hints (("goal"
                                :in-theory (enable svtv-data$c-><field>
                                                   svtv-data$c-><field>^))))
                    :str-alist `(("<FIELD>" . ,(symbol-name (caar decls))))
                    :pkg-sym 'sv-package)
                   (svtv-data-obj-to-stobj-thms-from-decls (cdr decls))))))

  (make-event
   `(define svtv-data-obj-to-stobj-logic ((x svtv-data-obj-p))
      :returns new-svtv-data
      (non-exec
       (b* (((svtv-data-obj x))
            ((mv & & moddb aliases)
             (svtv-design-flatten x.design :moddb nil :aliases nil)))
         (list ,@(svtv-data-list-elems-from-decls *svtv-data-nonstobj-fields*)
               moddb aliases)))
      ///
      (defret svtv-data->moddb-of-<fn>
        (equal (svtv-data$c->moddb new-svtv-data)
               (mv-nth 2 (svtv-design-flatten (svtv-data-obj->design x) :moddb nil :aliases nil)))
        :hints(("Goal" :in-theory (enable svtv-data$c->moddb))))

      (defret svtv-data->aliases-of-<fn>
        (equal (svtv-data$c->aliases new-svtv-data)
               (mv-nth 3 (svtv-design-flatten (svtv-data-obj->design x) :moddb nil :aliases nil)))
        :hints(("Goal" :in-theory (enable svtv-data$c->aliases))))

      . ,(svtv-data-obj-to-stobj-thms-from-decls *svtv-data-nonstobj-fields*))))


(defsection svtv-data-equiv

  ;; (make-event
  ;;  (let ((len (+ 2 (len *svtv-data-nonstobj-fields*))))
  ;;    `(define nth-svtv-data-field (n x)
  ;;       :verify-guards nil
  ;;       (nth (if (< (nfix n) ,len) n 0) x)
  ;;       ///
  ;;       (defthm nth-svtv-data-field-correct
  ;;         (implies (< (nfix n) ,len)
  ;;                  (equal (nth-svtv-data-field n x)
  ;;                         (nth n x)))))))

  ;; (def-universal-equiv svtv-data-equiv
  ;;   :qvars n
  ;;   :equiv-terms ((equal (nth-svtv-data-field n x))))

  ;; (local
  ;;  (make-event
  ;;   (let ((len (+ 2 (len *svtv-data-nonstobj-fields*))))
  ;;     `(defthm nths-equal-when-svtv-data-equiv
  ;;        (implies (and (svtv-data-equiv x y)
  ;;                      (< (nfix n) ,len))
  ;;                 (equal (equal (nth n x) (nth n y)) t))
  ;;        :hints (("goal" :use svtv-data-equiv-necc))))))

  ;; (local (in-theory (disable nth)))

  (local (defun svtv-data-equivs-from-decls (decls)
           (declare (xargs :mode :program))
           (if (atom decls)
               nil
             (cons (acl2::template-subst
                    '(equal (svtv-data$c-><field> x) (svtv-data$c-><field> y))
                    :str-alist `(("<FIELD>" . ,(symbol-name (caar decls))))
                    :pkg-sym 'sv-package)
                   (svtv-data-equivs-from-decls (cdr decls))))))


  (local (defun svtv-data-equiv-congruences-from-decls (n equiv decls)
           (declare (xargs :mode :program))
           (if (atom decls)
               nil
             (cons (acl2::template-subst
                    '(defcong <equiv> equal (svtv-data$c-><field> svtv-stobj) 1)
                    :str-alist `(("<FIELD>" . ,(symbol-name (caar decls))))
                    :atom-alist `((<n> . ,n)
                                  (<equiv> . ,equiv))
                    :pkg-sym 'sv-package)
                   (svtv-data-equiv-congruences-from-decls (+ 1 n) equiv (cdr decls))))))

  (make-event
   (let ((decls *svtv-data-nonstobj-fields*))
     `(define svtv-data-expequiv (x y)
        :verify-guards nil
        :non-executable t
        (and . ,(svtv-data-equivs-from-decls decls))
        ///
        (defequiv  svtv-data-expequiv)
        . ,(svtv-data-equiv-congruences-from-decls 0 'svtv-data-expequiv decls))))

  (make-event
   (let ((ext-decls (append *svtv-data-nonstobj-fields* '((moddb) (aliases)))))
   `(define svtv-data-equiv (x y)
      :verify-guards nil
      :non-executable t
      (and . ,(svtv-data-equivs-from-decls ext-decls))
      ///
      (defequiv  svtv-data-equiv)
      (defrefinement svtv-data-equiv svtv-data-expequiv
        :hints(("Goal" :in-theory (enable svtv-data-expequiv))))
      . ,(svtv-data-equiv-congruences-from-decls 0 'svtv-data-equiv '((moddb) (aliases))))))

  
  (defcong svtv-data-equiv equal (svtv-data$c-flatten-okp svtv-data flatten) 1
    :hints(("Goal" :in-theory (enable svtv-data$c-flatten-okp))))

  (defcong svtv-data-equiv equal (svtv-data$c-flatnorm-okp svtv-data flatnorm) 1
    :hints(("Goal" :in-theory (enable svtv-data$c-flatnorm-okp))))

  (defcong svtv-data-equiv equal (svtv-data$c-phase-fsm-okp svtv-data phase-fsm) 1
    :hints(("Goal" :in-theory (enable svtv-data$c-phase-fsm-okp))))

  (defcong svtv-data-equiv equal (svtv-data$c-namemap-okp svtv-data namemap) 1
    :hints(("Goal" :in-theory (enable svtv-data$c-namemap-okp))))

  (defcong svtv-data-expequiv equal (svtv-data$c-cycle-fsm-okp svtv-data cycle-fsm) 1
    :hints (("goal" :cases ((svtv-data$c-cycle-fsm-okp svtv-data cycle-fsm)))
            (and stable-under-simplificationp
                 `(:expand (,(assoc 'svtv-data$c-cycle-fsm-okp clause))))))

  (defcong svtv-data-expequiv equal (svtv-data$c-pipeline-okp svtv-data pipeline) 1
    :hints (("goal" :cases ((svtv-data$c-pipeline-okp svtv-data pipeline)))
            (and stable-under-simplificationp
                 `(:expand (,(assoc 'svtv-data$c-pipeline-okp clause))))))

  (defcong svtv-data-equiv equal (svtv-data$ap svtv-data) 1
    :hints(("Goal" :in-theory (enable svtv-data$ap)))))


(defthm svtv-data-obj-to-stobj-logic-of-svtv-data-to-obj-under-expequiv
  (svtv-data-expequiv (svtv-data-obj-to-stobj-logic (svtv-data-to-obj svtv-data))
                      svtv-data)
  :hints(("Goal" :in-theory (enable svtv-data-expequiv svtv-data-to-obj))))

(defthm svtv-data-obj-to-stobj-logic-of-svtv-data-to-obj
  (implies (and (svtv-data$ap svtv-data)
                (svtv-data$c->flatten-validp svtv-data))
           (svtv-data-equiv (svtv-data-obj-to-stobj-logic (svtv-data-to-obj svtv-data))
                            svtv-data))
  :hints(("Goal" :in-theory (enable svtv-data-equiv svtv-data-to-obj))
         (and stable-under-simplificationp
              '(:in-theory (enable svtv-data$ap svtv-data$c-flatten-okp)))))


(make-event
 (mv nil
     `(defun svtv-data-obj-test ()
        (declare (xargs :guard t))
        ',(svtv-data-to-obj svtv-data))
     state svtv-data))
     
(defevaluator svtv-data-obj-ev svtv-data-obj-ev-lst
  ((svtv-data$ap x)
   (svtv-data-obj-to-stobj-logic x)
   ;; mextract-ev reqs

   (typespec-check ts x)
   (if a b c)
   (equal a b)
   (not a)
   (iff a b)
   (implies a b))
  :namedp t)

(acl2::def-meta-extract svtv-data-obj-ev svtv-data-obj-ev-lst)


(define svtv-data-to-obj-cp ((clause pseudo-term-listp) hint state svtv-data)
  :returns (mv err clauses)
  (declare (ignore hint))
  (b* ((clause (acl2::pseudo-term-list-fix clause))
       ((unless (mbt (non-exec (svtv-data$ap svtv-data))))
        (mv "impossible" nil))
       ((unless (eql (len clause) 1))
        (mv "wrong number of lits" nil))
       (lit (car clause))
       ((mv err func)
        (acl2::pseudo-term-case lit
          :fncall (b* (((unless (eq lit.fn 'svtv-data$ap))
                        (mv "not svtv-data$ap" nil))
                       ((unless (eql (len lit.args) 1))
                        (mv "svtv-data$ap wrong arity" nil))
                       (arg (car lit.args)))
                    (acl2::pseudo-term-case arg
                      :fncall (b* (((unless (eq arg.fn 'svtv-data-obj-to-stobj-logic))
                                    (mv "not svtv-data-obj-to-stobj-logic" nil))
                                   ((unless (eql (len arg.args) 1))
                                    (mv "svtv-data-obj-to-stobj-logic wrong arity" nil))
                                   (obj (car arg.args)))
                                (acl2::pseudo-term-case obj
                                  :fncall (b* (((unless (atom obj.args))
                                                (mv "arguments to obj function" nil)))
                                            (mv nil obj.fn))
                                  :otherwise (mv "bad obj" nil)))
                      :otherwise (mv "bad arg" nil)))
          :otherwise (mv "bad lit" nil)))
       ((when err) (mv err nil))
       ((mv ok formals body) (acl2::fn-get-def func state))
       ((unless ok) (mv "func undefined" nil))
       ((unless (eq formals nil)) (mv "func wrong arity" nil))
       ((unless (pseudo-termp body))
        (mv "bad body" nil))
       ((unless (acl2::pseudo-term-case body :quote))
        (mv "func not quoted value" nil))
       (obj (acl2::pseudo-term-quote->val body))
       (svtv-data-obj (svtv-data-to-obj svtv-data))
       ((unless (hons-equal obj svtv-data-obj))
        (mv "not equal" nil))
       ((unless (svtv-data->flatten-validp svtv-data))
        (mv "flatten not valid" nil)))
    (mv nil nil))
  ///
  (local (defthm equal-of-len
           (implies (syntaxp (quotep n))
                    (equal (equal (len x) n)
                           (cond ((eql n 0) (atom x))
                                 ((posp n) (and (consp x)
                                                (equal (len (cdr x)) (1- n))))
                                 (t nil))))
           :hints(("Goal" :in-theory (enable len)))))
  (local (in-theory (disable len)))

  (local (acl2::def-join-thms  svtv-data-obj-ev))
  (local (acl2::def-ev-pseudo-term-fty-support svtv-data-obj-ev svtv-data-obj-ev-lst))
          

  (defthm svtv-data-to-obj-cp-correct
    (implies (and (pseudo-term-listp clause)
                  (alistp a)
                  (svtv-data-obj-ev-meta-extract-global-facts)
                  (svtv-data-obj-ev (acl2::conjoin-clauses
                                      (acl2::clauses-result
                                 (svtv-data-to-obj-cp clause hint state svtv-data)))
                               a))
             (svtv-data-obj-ev (disjoin clause) a))
    :hints (("goal" :do-not-induct t
             :in-theory (enable svtv-data-obj-ev-disjoin-when-consp)
             ))
    :otf-flg t
    :rule-classes :clause-processor))
  





(defun def-svtv-data-export-fn (name stobj)
  (Declare (xargs :mode :program))
  (acl2::template-subst
   '(with-output :off (event) :stack :push
      (make-event
       (b* ((obj (svtv-data-to-obj <stobj>))
            (events
             `(progn (define <name> ()
                       :no-function t
                       :returns (obj svtv-data-obj-p)
                       ',obj)
                     (with-output :stack :pop
                       (progn
                         (defthm flatten-validp-of-<name>
                           (svtv-data-obj->flatten-validp (<name>)))
                         (in-theory (disable (<name>)))
                         (defthm <name>-correct
                           (svtv-data$ap (svtv-data-obj-to-stobj-logic (<name>)))
                           :hints (("goal" :clause-processor (svtv-data-to-obj-cp clause nil state <stobj>)))))))))
         (mv nil events state <stobj>))))
   :atom-alist `((<name> . ,name)
                 (<stobj> . ,stobj))
   :str-alist `(("<NAME>" . ,(symbol-name name)))
   :pkg-sym name))

(defmacro def-svtv-data-export (name &key (stobj 'svtv-data))
  (def-svtv-data-export-fn name stobj))




(make-event
 (b* ((svtv-data (update-svtv-data->design (make-design :top "" :modalist
                                                        (list (cons "" (make-module))))
                                           svtv-data))
      ((mv err svtv-data) (svtv-data-compute-flatten svtv-data))
      ((when err) (mv err nil state svtv-data)))
   (mv nil '(value-triple :ok) state svtv-data)))

(encapsulate
  (((test-svtv-data-obj) => * :formals nil :guard t))
  (local (def-svtv-data-export test-svtv-data-obj))

  (defthm flatten-validp-of-test-svtv-data-obj
    (svtv-data-obj->flatten-validp (test-svtv-data-obj))
    :hints(("Goal" :in-theory (enable (test-svtv-data-obj)))))

  (defthm test-svtv-data-obj-correct
    (svtv-data$ap (svtv-data-obj-to-stobj-logic (test-svtv-data-obj))))

  (defthm test-svtv-data-obj-svtv-data-obj-p
    (svtv-data-obj-p (test-svtv-data-obj))
    :hints(("Goal" :in-theory (enable (test-svtv-data-obj))))))


(defsection svtv-data$ap-of-svtv-data-obj-to-stobj-logic
  (defthm svarlist-addr-p-design-of-svtv-data-obj
    (implies (svtv-data$ap (svtv-data-obj-to-stobj-logic x))
             (svarlist-addr-p (modalist-vars (design->modalist (svtv-data-obj->design x)))))
    :hints(("Goal" :in-theory (enable svtv-data$ap))))

  (defthm flatten-of-svtv-data-obj
    (implies (and (svtv-data$ap (svtv-data-obj-to-stobj-logic x))
                  (svtv-data-obj->flatten-validp x))
             (b* (((svtv-data-obj x))
                  ((mv err res ?moddb ?aliases)
                   (svtv-design-flatten (svtv-data-obj->design x) :moddb nil :aliases nil)))
               (and (not err)
                    (equal x.flatten res))))
    :hints(("Goal" :in-theory (enable svtv-data$ap svtv-data$c-flatten-okp))))
  

  (defthm flatnorm-of-svtv-data-obj
    (implies (and (svtv-data$ap (svtv-data-obj-to-stobj-logic x))
                  (svtv-data-obj->flatten-validp x)
                  (svtv-data-obj->flatnorm-validp x))
             (b* (((mv ?err ?res ?moddb ?aliases)
                   (svtv-design-flatten (svtv-data-obj->design x) :moddb nil :aliases nil)))
               (equal (svtv-data-obj->flatnorm x)
                      (svtv-normalize-assigns res aliases))))
    :Hints(("Goal" :in-theory (enable svtv-data$ap
                                      svtv-data$c-flatten-okp
                                      svtv-data$c-flatnorm-okp))))

  (defthm phase-fsm-validp-of-svtv-data-obj
    (implies (and (svtv-data$ap (svtv-data-obj-to-stobj-logic x))
                  (svtv-data-obj->phase-fsm-validp x)
                  (svtv-data-obj->flatten-validp x))
             (base-fsm-eval-equiv
              (svtv-data-obj->phase-fsm x)
              (b* (((mv & res & aliases)
                    (svtv-design-flatten (svtv-data-obj->design x) :moddb nil :aliases nil)))
                (svtv-compose-assigns/delays
                 (svtv-normalize-assigns res aliases)))))
    :hints(("Goal" :in-theory (enable svtv-data$ap
                                      svtv-data$c-flatten-okp))))

  (defthm namemap-validp-of-svtv-data-obj
    (implies (and (svtv-data$ap (svtv-data-obj-to-stobj-logic x))
                  (svtv-data-obj->namemap-validp x)
                  (svtv-data-obj->flatten-validp x))
             (b* (((svtv-data-obj x))
                  ((mv ?err ?res ?moddb ?aliases)
                   (svtv-design-flatten x.design :moddb nil :aliases nil))
                  (modidx (moddb-modname-get-index (design->top x.design) moddb))
                  ((mv err namemap)
                   (svtv-namemap->lhsmap
                               x.user-names modidx moddb aliases)))
               (and (not err)
                    (equal x.namemap namemap))))
    :hints (("goal" :in-theory (enable svtv-data$ap svtv-data$c-namemap-okp))))

  (defthm cycle-fsm-validp-of-svtv-data-obj
    (implies (and (svtv-data$ap (svtv-data-obj-to-stobj-logic x))
                  (svtv-data-obj->cycle-fsm-validp x)
                  (svtv-data-obj->flatten-validp x))
             (b* (((svtv-data-obj x))
                  ((base-fsm x.phase-fsm))
                  (statevars (svex-alist-keys x.phase-fsm.nextstate))
                  (prev-st (svex-env-extract statevars env))
                  ((base-fsm x.cycle-fsm)))
               (and (svex-envs-equivalent
                     (svex-alist-eval x.cycle-fsm.values env)
                     (svtv-cycle-eval-outs env prev-st x.cycle-phases x.phase-fsm))
                    (svex-envs-equivalent
                     (svex-alist-eval x.cycle-fsm.nextstate env)
                     (svtv-cycle-eval-nextst env prev-st x.cycle-phases x.phase-fsm))
                    (equal (svex-alist-keys x.cycle-fsm.nextstate) statevars))))
    :hints (("goal" :in-theory (e/d (svtv-data$ap)
                                    (svtv-data$c-cycle-fsm-okp-necc))
             :use ((:instance svtv-data$c-cycle-fsm-okp-necc
                    (svtv-data$c (svtv-data-obj-to-stobj-logic x))
                    (cycle-fsm (svtv-data-obj->cycle-fsm x)))))))

  (defthm pipeline-validp-of-svtv-data-obj
    (implies (and (svtv-data$ap (svtv-data-obj-to-stobj-logic x))
                  (svtv-data-obj->pipeline-validp x)
                  (svtv-data-obj->flatten-validp x))
             (b* (((svtv-data-obj x))
                  (rename-fsm (make-svtv-fsm :base-fsm x.cycle-fsm
                                             :namemap x.namemap))
                  ((pipeline-setup x.pipeline-setup))
                  (run (svtv-fsm-run
                        (svex-alistlist-eval x.pipeline-setup.inputs env)
                        (svex-alistlist-eval x.pipeline-setup.overrides env)
                        (svex-alist-eval x.pipeline-setup.initst env)
                        rename-fsm
                        (svtv-probealist-outvars x.pipeline-setup.probes))))
               (and (equal (svex-alist-keys x.pipeline-setup.initst)
                           (svex-alist-keys (base-fsm->nextstate x.cycle-fsm)))
                    (svex-envs-equivalent
                     (svex-alist-eval x.pipeline env)
                     (svtv-probealist-extract x.pipeline-setup.probes run)))))
    :hints (("goal" :in-theory (e/d (svtv-data$ap)
                                    (svtv-data$c-pipeline-okp-necc))
             :use ((:instance svtv-data$c-pipeline-okp-necc
                    (svtv-data$c (svtv-data-obj-to-stobj-logic x))
                    (results (svtv-data-obj->pipeline x)))))))
  )

(defconst *svtv-data-import-template*
  '(define svtv-data-import-<obj-fn> (svtv-data)
     :guard-hints <hints>
     :guard-simplify nil
     (b* (((svtv-data-obj obj) (<obj-fn>))
          (svtv-data (svtv-data-invalidate svtv-data))

          (svtv-data (update-svtv-data->design obj.design svtv-data))
          ((mv ?err svtv-data) (svtv-data-compute-flatten svtv-data))
          ;; err is impossible due to flatten-validp

          (svtv-data (update-svtv-data->flatnorm obj.flatnorm svtv-data))
          (svtv-data (update-svtv-data->flatnorm-validp obj.flatnorm-validp svtv-data))

          (svtv-data (update-svtv-data->phase-fsm obj.phase-fsm svtv-data))
          (svtv-data (update-svtv-data->phase-fsm-validp obj.phase-fsm-validp svtv-data))

          (svtv-data (update-svtv-data->cycle-phases obj.cycle-phases svtv-data))
          (svtv-data (update-svtv-data->cycle-fsm obj.cycle-fsm svtv-data))
          (svtv-data (update-svtv-data->cycle-fsm-validp obj.cycle-fsm-validp svtv-data))

          (svtv-data (update-svtv-data->user-names obj.user-names svtv-data))
          (svtv-data (update-svtv-data->namemap obj.namemap svtv-data))
          (svtv-data (update-svtv-data->namemap-validp obj.namemap-validp svtv-data))

          (svtv-data (update-svtv-data->pipeline-setup obj.pipeline-setup svtv-data))
          (svtv-data (update-svtv-data->pipeline obj.pipeline svtv-data))
          (svtv-data (update-svtv-data->pipeline-validp obj.pipeline-validp svtv-data)))
       svtv-data)))

(defmacro def-svtv-data-import (name &key hints)
  (b* ((hints (or hints
                  `(("goal" :by (:functional-instance (:guard-theorem svtv-data-import-test-svtv-data-obj)
                                 (test-svtv-data-obj ,name)))))))
    `(make-event
      (acl2::template-subst
       *svtv-data-import-template*
       :atom-alist '((<obj-fn> . ,name)
                     (<hints> . ,hints))
       :str-alist '(("<OBJ-FN>" . ,(symbol-name name)))
       :pkg-sym ',name))))

(def-svtv-data-import test-svtv-data-obj
  :hints (("goal" :in-theory (enable svtv-data$c-compute-flatten
                                     NORMALIZE-STOBJS-OF-SVTV-DESIGN-FLATTEN
                                     svtv-data$c-namemap-okp
                                     svtv-data$c-cycle-fsm-okp
                                     svtv-data$c-pipeline-okp))))



(defun def-svtv-data-export/import-fn (name stobj)
  (Declare (xargs :mode :program))
   `(progn (def-svtv-data-export ,name :stobj ,stobj)
           (def-svtv-data-import ,name)))

(defmacro def-svtv-data-export/import (name &key (stobj 'svtv-data))
  (def-svtv-data-export/import-fn name stobj))
