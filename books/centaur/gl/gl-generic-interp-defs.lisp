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
(include-book "ite-merge")
(include-book "gtests")
(include-book "glcp-templates")
(include-book "shape-spec-defs")
(include-book "symbolic-arithmetic")
(include-book "param")
(include-book "bfr-sat")
(include-book "glcp-config")
(include-book "gl-mbe")
(include-book "split-args")
(include-book "glcp-unify-defs")
(include-book "centaur/misc/rewrite-rule" :dir :system)
(include-book "centaur/misc/beta-reduce-full" :dir :system)
(include-book "glcp-geval")
(include-book "constraint-db-deps")
(include-book "prof")
(include-book "rewrite-tables")
(verify-termination acl2::evisc-tuple)
(verify-guards acl2::evisc-tuple)

(defun glcp-case-split-report (test then else)
  (declare (xargs :guard t)
           (ignore test then else))
  nil)

(set-state-ok t)

(defun glcp-error-fn (msg interp-st state)
  (declare (xargs :guard t :stobjs (state interp-st)))
  (mv msg nil interp-st state))

(defmacro glcp-error (msg)
  `(glcp-error-fn ,msg interp-st state))

(add-macro-alias glcp-error glcp-error-fn)

(defun preferred-defs-to-overrides (alist state)
  (declare (xargs :stobjs state :guard t))
  (if (atom alist)
      (value nil)
    (b* (((when (atom (car alist)))
          (preferred-defs-to-overrides (cdr alist) state))
         ((cons fn defname) (car alist))
         ((unless (and (symbolp fn) (symbolp defname) (not (eq fn 'quote))))
          (mv
           (acl2::msg "~
The GL preferred-defs table contains an invalid entry ~x0.
The key and value of each entry should both be function symbols."
                      (car alist))
           nil state))
         (rule (ec-call (fgetprop defname 'theorem nil (w state))))
         ((unless rule)
          (mv
           (acl2::msg "~
The preferred-defs table contains an invalid entry ~x0.
The :definition rule ~x1 was not found in the ACL2 world."
                      (car alist) defname)
           nil state))
         ((unless (case-match rule
                    (('equal (rulefn . &) &) (equal fn rulefn))))
          (mv
           (acl2::msg "~
The preferred-defs table contains an invalid entry ~x0.
The :definition rule ~x1 is not suitable as a GL override.
Either it is a conditional definition rule, it uses a non-EQUAL
equivalence relation, or its format is unexpected.  The rule
found is ~x2." (car alist) defname rule)
           nil state))
         (formals (cdadr rule))
         (body (caddr rule))
         ((unless (and (nonnil-symbol-listp formals)
                       (acl2::no-duplicatesp formals)))
          (mv
           (acl2::msg "~
The preferred-defs table contains an invalid entry ~x0.
The formals used in :definition rule ~x1 either are not all
variable symbols or have duplicates, making this an unsuitable
definition for use in a GL override.  The formals listed are
~x2." (car alist) defname formals)
           nil state))
         ((unless (pseudo-termp body))
          (mv
           (acl2::msg "~
The preferred-defs table contains an invalid entry ~x0.
The definition body, ~x1, is not a pseudo-term."
                      (car alist) body)
           nil state))
         ((er rest) (preferred-defs-to-overrides (cdr alist) state)))
      (value (hons-acons fn (list* formals body defname)
                         rest)))))


(acl2::def-meta-extract glcp-generic-geval-ev glcp-generic-geval-ev-lst)

(encapsulate (((glcp-generic-run-gified * * hyp * * bvar-db state)
    => (mv * * hyp)
    :formals (fn actuals hyp clk config bvar-db state)
    :guard (and (symbolp fn)
                (true-listp actuals)
                (glcp-config-p config)
                (natp clk)))
   ;; ((glcp-generic-geval-ev * *) => *)
   ;; ((glcp-generic-geval-ev-lst * *) => *)
   ;; ((glcp-generic-geval * *) => *)
   )

  ;; (local (def-eval-g glcp-generic-geval
  ;;          (if gl-cp-hint shape-spec-obj-in-range return-last use-by-hint equal
  ;;              acl2::typespec-check implies iff not cons gl-aside gl-ignore gl-error)))

  ;; (local (defun glcp-generic-geval (x env)
  ;;          (generic-geval x env)))

  (local (defun glcp-generic-run-gified (fn actuals hyp clk config bvar-db state)
           (declare (xargs :stobjs (hyp bvar-db state)
                           :guard (and (symbolp fn)
                                       (natp clk)))
                    (ignorable fn actuals hyp clk config bvar-db state))
           (let ((hyp (lbfr-hyp-fix hyp)))
             (mv nil nil hyp))))

  (def-hyp-congruence glcp-generic-run-gified)
  ;; (local (acl2::defevaluator-fast
  ;;         glcp-generic-ev glcp-generic-ev-lst
  ;;         ((if a b c)
  ;;          (gl-cp-hint x)
  ;;          (shape-spec-obj-in-range a b)
  ;;          (return-last fn arg1 arg2)
  ;;          (use-by-hint x)
  ;;          (equal a b)
  ;;          (acl2::typespec-check ts x)
  ;;          (implies a b)
  ;;          (iff a b)
  ;;          (not x)
  ;;          (cons a b)
  ;;          (gl-aside x)
  ;;          (gl-ignore x)
  ;;          (gl-error x))
  ;;         :namedp t))



  (defthm glcp-generic-run-gified-correct
    (implies (and (bfr-hyp-eval hyp (car env))
                  ;; (gobj-listp actuals)
                  (mv-nth 0 (glcp-generic-run-gified fn actuals hyp
                                                     clk config bvar-db state)))
             (equal (glcp-generic-geval
                     (mv-nth 1 (glcp-generic-run-gified
                                fn actuals hyp clk config bvar-db state))
                     env)
                    (glcp-generic-geval-ev
                     (cons fn
                           (acl2::kwote-lst
                            (glcp-generic-geval-list actuals env))) nil))))

  (defthm gobj-depends-on-of-glcp-generic-run-gified
    (implies (not (gobj-list-depends-on k p actuals))
             (not (gobj-depends-on k p (mv-nth 1 (glcp-generic-run-gified
                                                  fn actuals hyp clk config bvar-db state))))))


  ;; (defthm true-listp-glcp-generic-run-gified
  ;;   (true-listp (glcp-generic-run-gified fn actuals hyp clk config bvar-db state)))

  ;; (make-event
  ;;  `(progn
  ;;     . ,(acl2::defevaluator-fast-form/defthms-named
  ;;         'glcp-generic-geval-ev 'glcp-generic-geval-ev-lst
  ;;         '((if a b c)
  ;;           (gl-cp-hint x)
  ;;           (shape-spec-obj-in-range a b)
  ;;           (return-last fn arg1 arg2)
  ;;           (use-by-hint x)
  ;;           (equal a b)
  ;;           (acl2::typespec-check ts x)
  ;;           (implies a b)
  ;;           (iff a b)
  ;;           (not x)
  ;;           (cons a b)
  ;;           (gl-aside x)
  ;;           (gl-ignore x)
  ;;           (gl-error x)))))

  )

(defun general-concrete-listp (x)
  (declare (xargs :guard t))
  (if (atom x)
      (eq x nil)
    (and (general-concretep (car x))
         (general-concrete-listp (cdr x)))))

(defun general-concrete-obj-list (x)
  (declare (xargs :guard (general-concrete-listp x)))
  (if (atom x)
      nil
    (cons (general-concrete-obj (car x))
          (general-concrete-obj-list (cdr x)))))


(mutual-recursion ;; sublis-into-term
 (defun sublis-into-term (x alist)
   (declare (xargs :guard t))
   (cond ((null x) nil)
         ((atom x)
          (let ((look (hons-assoc-equal x alist)))
            (if look (acl2::kwote (cdr look)) x)))
         ((eq (car x) 'quote) x)
         (t (cons (car x) (sublis-into-list (cdr x) alist)))))
 (defun sublis-into-list (x alist)
   (declare (xargs :guard t))
   (if (atom x)
       nil
     (cons (sublis-into-term (car x) alist)
           (sublis-into-list (cdr x) alist)))))

(defund gl-aside-wormhole (term alist)
  (declare (xargs :guard t))
  (wormhole 'glcp-interp-gl-aside
            '(lambda (whs) whs)
            nil
            `(prog2$ ,(sublis-into-term
                       term alist)
                     (value :q))
            :ld-prompt nil
            :ld-pre-eval-print nil
            :ld-post-eval-print nil
            :ld-verbose nil))

(defthmd acl2-count-last-cdr-when-cadr-hack
  (implies (< 1 (len x))
           (< (acl2-count (car (last x)))
              (+ 1 (acl2-count (cdr x)))))
  :rule-classes (:rewrite :linear))



;; BOZO replace with defaggrify-defrec
(make-event ;; rewrite-rule b* binder
 `(acl2::def-b*-binder rewrite-rule
    :body
    #!acl2
    (std::da-patbind-fn 'rewrite-rule
                        #!GL ',(let ((fields '(rune hyps lhs rhs equiv subclass heuristic-info)))
                                 (pairlis$ fields (std::da-accessor-names 'acl2::rewrite-rule fields)))
                        args forms rest-expr)))

;; used for measure
(defun pos-fix (x)
  (if (posp x) x 1))


(defund glcp-relieve-hyp-synp (hyp bindings state)
  (declare (xargs :stobjs state
                  :guard (and (consp hyp)
                              (pseudo-termp hyp))))
  (b* ((args (cdr hyp))
       ((unless #!acl2 (and
                        ;; check that synp is defined as expected
                        (fn-check-def 'synp state '(vars form term) ''t)
                        ;; check that all three args are quoted
                        (equal (len args) 3)
                        (quote-listp args)))
        (mv (acl2::msg "Bad synp hyp: ~x0~%" hyp) nil nil))
       (hyp-form (second (second args)))
       ((unless (and (consp hyp-form) (eq (car hyp-form) 'syntaxp)))
        (mv (acl2::msg "Bind-free isn't supported yet: ~x0~%" hyp) nil nil))
       (form (second ;; unquote
              (third args)))
       ((unless (and (pseudo-termp form)
                     (symbol-alistp bindings)))
        (mv (acl2::msg "ill-formed syntaxp form: ~x0~%" form) nil nil))
       ((mv err val) (acl2::magic-ev form bindings state t t))
       ((when err)
        (mv (acl2::msg "synp error: ~@0~%" (if (eq err t) "error" err)) nil nil)))
    (mv nil val bindings)))


(mutual-recursion ;; gl-term-to-apply-obj
 (defun gl-term-to-apply-obj (x alist)
   (declare (xargs :guard (pseudo-termp x)
                   :verify-guards nil))
   (b* (((when (atom x))
         (and x (mbt (symbolp x))
              (cdr (hons-assoc-equal x alist))))
        ((when (eq (car x) 'quote)) (g-concrete-quote (cadr x)))
        (args (gl-termlist-to-apply-obj-list (cdr x) alist))
        (fn (car x))
        ((when (consp fn))
         (b* ((formals (cadr fn))
              (body (caddr fn)))
           (gl-term-to-apply-obj body (pairlis$ formals args))))
        ((when (eq fn 'if))
         (g-ite (first args) (second args) (third args)))
        ((when (eq fn 'cons))
         (gl-cons (first args) (second args))))
     (g-apply fn args)))
 (defun gl-termlist-to-apply-obj-list (x alist)
   (declare (xargs :guard (pseudo-term-listp x)))
   (if (atom x)
       nil
     (cons (gl-term-to-apply-obj (car x) alist)
           (gl-termlist-to-apply-obj-list (cdr x) alist)))))

(in-theory (disable gl-term-to-apply-obj
                    gl-termlist-to-apply-obj-list))


(flag::make-flag gl-term-to-apply-obj-flag gl-term-to-apply-obj)

(defthm-gl-term-to-apply-obj-flag
  (defthm true-listp-gl-termlist-to-apply-obj-list
    (true-listp (gl-termlist-to-apply-obj-list x alist))
    :hints ('(:expand ((gl-termlist-to-apply-obj-list x alist))))
    :rule-classes :type-prescription
    :flag gl-termlist-to-apply-obj-list)
  :skip-others t)

(verify-guards gl-term-to-apply-obj)

;; NOTE.  This is provably equal to pseudo-term-listp, but we use it
;; differently.  When an element is a symbol, it stands for an equivalence
;; relation; otherwise, it is a context "fixing" term.
(defun contextsp (x)
  (declare (xargs :guard t))
  (if (atom x)
      (eq x nil)
    (and (or (symbolp (car x))
             (pseudo-termp (car x)))
         (contextsp (cdr x)))))


;; (defund-nx glcp-generic-eval-context-equivs (contexts x y a)
;;   (b* (((when (atom contexts))
;;         (equal (glcp-generic-geval-ev x a)
;;                (glcp-generic-geval-ev y a)))
;;        (ctx (car contexts))
;;        (ctx-fn (if (symbolp ctx)
;;                    ctx
;;                  `(lambda (x y)
;;                     (equal ,ctx
;;                            ((lambda (x) ,ctx) y))))))
;;     (or (glcp-generic-geval-ev (list ctx-fn x y) a)
;;         (glcp-generic-eval-context-equivs (cdr contexts) x y a))))

;; (defun-sk glcp-generic-equiv-under-contexts (contexts x y)
;;   (forall (a)
;;           (glcp-generic-eval-context-equivs contexts x y a))
;;   :rewrite :direct)


(defun-sk glcp-generic-equiv-relp (f)
  (forall (a x y z)
          (and (booleanp (glcp-generic-geval-ev (list f x y) a))
               (glcp-generic-geval-ev (list f x x) a)
               (implies (glcp-generic-geval-ev (list f x y) a)
                        (glcp-generic-geval-ev (list f y x) a))
               (implies (and (glcp-generic-geval-ev (list f x y) a)
                             (glcp-generic-geval-ev (list f y z) a))
                        (glcp-generic-geval-ev (list f x z) a))))
  :rewrite :direct)

(in-theory (disable glcp-generic-equiv-relp))

(defun proper-contextsp (contexts)
  (if (atom contexts)
      t
    (and (or (not (symbolp (car contexts)))
             (glcp-generic-equiv-relp (car contexts)))
         (proper-contextsp (cdr contexts)))))

(defund-nx glcp-generic-eval-context-equiv (contexts x y)
  (b* (((when (atom contexts)) (equal x y))
       (ctx (car contexts))
       (ctx-fn (if (symbolp ctx)
                   ctx
                 `(lambda (x y)
                    (equal ((lambda (x) ,ctx) x)
                           ((lambda (x) ,ctx) y))))))
    (or (glcp-generic-geval-ev (list ctx-fn (kwote x) (kwote y)) nil)
        (glcp-generic-eval-context-equiv (cdr contexts) x y))))


(defthmd glcp-generic-eval-context-equiv-commute
  (implies (and (proper-contextsp contexts)
                (glcp-generic-eval-context-equiv contexts x y))
           (glcp-generic-eval-context-equiv contexts y x))
  :hints (("goal" :induct (glcp-generic-eval-context-equiv contexts x y)
           :in-theory (enable glcp-generic-eval-context-equiv
                              glcp-generic-geval-ev-of-fncall-args)
           :expand ((glcp-generic-eval-context-equiv contexts y x)
                    (proper-contextsp contexts)))))

(defun glcp-generic-eval-context-equiv-chain (contexts chain)
  (declare (xargs :hints(("Goal" :in-theory (enable acl2-count)))))
  (if (atom (cdr chain))
      t
    (and (glcp-generic-eval-context-equiv contexts
                                          (car chain)
                                          (cadr chain))
         (glcp-generic-eval-context-equiv-chain contexts (cdr chain)))))

(defun-sk glcp-generic-eval-context-equiv* (contexts x y)
  (exists chain
          (and (consp chain)
               (equal (car chain) x)
               (equal (car (last chain)) y)
               (glcp-generic-eval-context-equiv-chain contexts chain))))

(in-theory (disable glcp-generic-eval-context-equiv*))

(defthm glcp-generic-eval-context-equiv*-refl
  (glcp-generic-eval-context-equiv* contexts x x)
  :hints (("goal" :use ((:instance glcp-generic-eval-context-equiv*-suff
                         (chain (list x)) (y x))))))



(defthm glcp-generic-eval-context-equiv*-chain-append
  (implies (and (glcp-generic-eval-context-equiv-chain contexts c1)
                (glcp-generic-eval-context-equiv-chain contexts c2)
                (equal (car (last c1)) (car c2)))
           (glcp-generic-eval-context-equiv-chain contexts (append c1 (cdr
                                                                       c2))))
  :hints(("Goal" :in-theory (disable glcp-generic-eval-context-equiv-commute))))


(defsection glcp-generic-eval-context-equiv*-trans
  (local (defthm last-of-append-when-first/last-equal
           (implies (equal (car b) (car (last a)))
                    (equal (car (last (append a (cdr b))))
                           (car (last b))))))

  (local (defthm car-append-when-consp
           (implies (consp x)
                    (equal (car (append x y))
                           (car x)))))

  (defthm glcp-generic-eval-context-equiv*-trans
    (implies (and (glcp-generic-eval-context-equiv* contexts x y)
                  (glcp-generic-eval-context-equiv* contexts y z))
             (glcp-generic-eval-context-equiv* contexts x z))
    :hints (("goal" :use ((:instance glcp-generic-eval-context-equiv*-suff
                           (chain (append
                                   (glcp-generic-eval-context-equiv*-witness
                                    contexts x y)
                                   (cdr (glcp-generic-eval-context-equiv*-witness
                                         contexts y z))))
                           (y z)))
             :expand ((glcp-generic-eval-context-equiv* contexts x y)
                      (glcp-generic-eval-context-equiv* contexts y z))))))


(encapsulate nil

  (local (defthm chain-of-append-when-last/first-related
           (implies (and (consp x)
                         (glcp-generic-eval-context-equiv contexts (car (last x))
                                                          (car y))
                         (glcp-generic-eval-context-equiv-chain contexts x)
                         (glcp-generic-eval-context-equiv-chain contexts y))
                    (glcp-generic-eval-context-equiv-chain contexts (append x
                                                                            y)))))

  (local (defthm last-of-append-when-consp-second
           (implies (consp y)
                    (equal (last (append x y))
                           (last y)))))


  (local (defthm car-last-of-rev
           (implies (consp x)
                    (equal (car (last (acl2::rev x)))
                           (car x)))
           :hints(("Goal" :in-theory (enable acl2::rev)))))

  (defthmd glcp-generic-eval-context-equiv-chain-rev
    (implies (and (proper-contextsp contexts)
                  (glcp-generic-eval-context-equiv-chain contexts chain))
             (glcp-generic-eval-context-equiv-chain contexts (acl2::rev chain)))
    :hints(("Goal" :in-theory (e/d (acl2::rev) (proper-contextsp))
            :induct (acl2::rev chain))
           (and stable-under-simplificationp
                '(:expand ((acl2::rev (cdr chain)))
                  :in-theory (e/d (glcp-generic-eval-context-equiv-commute)
                                  (acl2::associativity-of-append))))))

  (local (in-theory (enable glcp-generic-eval-context-equiv-chain-rev)))

  (local (defthm consp-rev
           (equal (consp (acl2::rev x))
                  (consp x))))

  (local (defthm car-append-when-consp
           (implies (consp x)
                    (equal (car (append x y))
                           (car x)))))


  (local (defthm car-rev-when-consp
           (implies (consp x)
                    (equal (car (acl2::rev x))
                           (car (last x))))
           :hints(("Goal" :in-theory (enable acl2::rev)))))

  (defthmd glcp-generic-eval-context-equiv*-commute
    (implies (and (proper-contextsp contexts)
                  (glcp-generic-eval-context-equiv* contexts x y))
             (glcp-generic-eval-context-equiv* contexts y x))
    :hints (("goal" :use ((:instance glcp-generic-eval-context-equiv*-suff
                           (chain (acl2::rev
                                   (glcp-generic-eval-context-equiv*-witness
                                    contexts x y)))
                           (x y) (y x)))
             :in-theory (disable proper-contextsp)
             :expand ((glcp-generic-eval-context-equiv* contexts x y))))))


(defthm g-ite->test-acl2-count-decr
  (implies (equal (tag x) :g-ite)
           (< (acl2-count (g-ite->test x)) (acl2-count x)))
  :hints(("Goal" :in-theory (enable tag g-ite->test)))
  :rule-classes :linear)

(defthm g-ite->then-acl2-count-decr
  (implies (equal (tag x) :g-ite)
           (< (acl2-count (g-ite->then x)) (acl2-count x)))
  :hints(("Goal" :in-theory (enable tag g-ite->then)))
  :rule-classes :linear)

(defthm g-ite->else-acl2-count-decr
  (implies (equal (tag x) :g-ite)
           (< (acl2-count (g-ite->else x)) (acl2-count x)))
  :hints(("Goal" :in-theory (enable tag g-ite->else)))
  :rule-classes :linear)



(in-theory (disable glcp-generic-equiv-relp))

(defsection ensure-equiv-relationp

  (acl2::def-unify glcp-generic-geval-ev glcp-generic-geval-ev-alist)
  (acl2::def-meta-extract glcp-generic-geval-ev glcp-generic-geval-ev-lst)

  (defund search-match-in-conjunction (pat term)
    (declare (xargs :guard (and (pseudo-termp pat)
                                (pseudo-termp term))))
    (b* (((mv ok &) (acl2::simple-one-way-unify term pat nil))
         ((when ok) t)
         ((when (atom term)) nil)
         ((unless (and (eq (car term) 'if)
                       (equal (fourth term) ''nil)))
          nil))
      (or (search-match-in-conjunction pat (second term))
          (search-match-in-conjunction pat (third term)))))

  (defthmd glcp-generic-geval-ev-theoremp-of-conjunction
    (implies (and (equal (car term) 'if)
                  (equal (fourth term) ''nil))
             (iff (glcp-generic-geval-ev-theoremp term)
                  (and (glcp-generic-geval-ev-theoremp (second term))
                       (glcp-generic-geval-ev-theoremp (third term)))))
    :hints (("goal" :use ((:instance glcp-generic-geval-ev-falsify
                           (x term) (a (glcp-generic-geval-ev-falsify (second term))))
                          (:instance glcp-generic-geval-ev-falsify
                           (x term) (a (glcp-generic-geval-ev-falsify (third term))))
                          (:instance glcp-generic-geval-ev-falsify
                           (x (second term))
                           (a (glcp-generic-geval-ev-falsify term)))
                          (:instance glcp-generic-geval-ev-falsify
                           (x (third term))
                           (a (glcp-generic-geval-ev-falsify term))))
             :in-theory (disable pseudo-termp pseudo-term-listp))))

  (local (in-theory (enable glcp-generic-geval-ev-theoremp-of-conjunction)))

  (defthmd search-match-in-conjunction-correct
    (implies (and (glcp-generic-geval-ev-theoremp term)
                  (pseudo-termp term)
                  (pseudo-termp pat)
                  (search-match-in-conjunction pat term))
             (glcp-generic-geval-ev pat a))
    :hints(("Goal" :in-theory (e/d (search-match-in-conjunction)
                                   (glcp-generic-geval-ev-alist
                                    symbol-listp
                                    nonnil-symbol-listp))
            :induct (search-match-in-conjunction pat term))
           (and stable-under-simplificationp
                '(:use ((:instance glcp-generic-geval-ev-falsify
                         (x term)
                         (a (glcp-generic-geval-ev-alist
                             (mv-nth 1 (acl2::simple-one-way-unify term pat nil))
                             a))))))))

  (defund check-equiv-formula (form e)
    (declare (xargs :guard (and (pseudo-termp form)
                                (symbolp e)
                                (not (eq e 'quote)))))
    (and (search-match-in-conjunction `(booleanp (,e x y)) form)
         (search-match-in-conjunction `(,e x x) form)
         (search-match-in-conjunction `(implies (,e x y) (,e y x)) form)
         (search-match-in-conjunction `(implies (if (,e x y)
                                                    (,e y z)
                                                  'nil)
                                                (,e x z))
                                      form)))

  (local (defthm lemma1
           (implies (and (pseudo-termp form)
                         (glcp-generic-geval-ev-theoremp form)
                         (search-match-in-conjunction `(booleanp (,e x y)) form)
                         (symbolp e)
                         (not (equal e 'quote)))
                    (booleanp (glcp-generic-geval-ev (list e x y) a)))
           :hints (("goal" :in-theory (e/d (check-equiv-formula
                                            glcp-generic-geval-ev-of-fncall-args)
                                           (search-match-in-conjunction-correct))
                    :use ((:instance search-match-in-conjunction-correct
                           (term form) (pat `(booleanp (,e x y)))
                           (a `((x . ,(glcp-generic-geval-ev x a))
                                (y . ,(glcp-generic-geval-ev y a))
                                (z . ,(glcp-generic-geval-ev z a))))))))))

  (local (defthm lemma2
           (implies (and (pseudo-termp form)
                         (glcp-generic-geval-ev-theoremp form)
                         (search-match-in-conjunction `(,e x x) form)
                         (symbolp e)
                         (not (equal e 'quote)))
                    (glcp-generic-geval-ev (list e x x) a))
           :hints (("goal" :in-theory (e/d (check-equiv-formula
                                            glcp-generic-geval-ev-of-fncall-args)
                                           (search-match-in-conjunction-correct))
                    :use ((:instance search-match-in-conjunction-correct
                           (term form) (pat `(,e x x))
                           (a `((x . ,(glcp-generic-geval-ev x a))
                                (y . ,(glcp-generic-geval-ev y a))
                                (z . ,(glcp-generic-geval-ev z a))))))))))

  (local (defthm lemma3
           (implies (and (pseudo-termp form)
                         (glcp-generic-geval-ev-theoremp form)
                         (search-match-in-conjunction
                          `(implies (,e x y) (,e y x)) form)
                         (symbolp e)
                         (not (equal e 'quote))
                         (glcp-generic-geval-ev (list e x y) a))
                    (glcp-generic-geval-ev (list e y x) a))
           :hints (("goal" :in-theory (e/d (check-equiv-formula
                                            glcp-generic-geval-ev-of-fncall-args)
                                           (search-match-in-conjunction-correct))
                    :use ((:instance search-match-in-conjunction-correct
                           (term form) (pat `(implies (,e x y) (,e y x)))
                           (a `((x . ,(glcp-generic-geval-ev x a))
                                (y . ,(glcp-generic-geval-ev y a))
                                (z . ,(glcp-generic-geval-ev z a))))))))))

  (local (defthm lemma4
           (implies (and (pseudo-termp form)
                         (glcp-generic-geval-ev-theoremp form)
                         (search-match-in-conjunction
                          `(implies (if (,e x y) (,e y z) 'nil) (,e x z)) form)
                         (symbolp e)
                         (not (equal e 'quote))
                         (glcp-generic-geval-ev (list e x y) a)
                         (glcp-generic-geval-ev (list e y z) a))
                    (glcp-generic-geval-ev (list e x z) a))
           :hints (("goal" :in-theory (e/d (check-equiv-formula
                                            glcp-generic-geval-ev-of-fncall-args)
                                           (search-match-in-conjunction-correct))
                    :use ((:instance search-match-in-conjunction-correct
                           (term form) (pat `(implies (if (,e x y) (,e y z) 'nil) (,e x z)))
                           (a `((x . ,(glcp-generic-geval-ev x a))
                                (y . ,(glcp-generic-geval-ev y a))
                                (z . ,(glcp-generic-geval-ev z a))))))))))

  (defthmd check-equiv-formula-correct
    (implies (and (check-equiv-formula form e)
                  (glcp-generic-geval-ev-theoremp form)
                  (pseudo-termp form)
                  (symbolp e)
                  (not (eq e 'quote)))
             (glcp-generic-equiv-relp e))
    :hints(("Goal" :in-theory '(check-equiv-formula
                                glcp-generic-equiv-relp
                                lemma1 lemma2 lemma3 lemma4))))

  (local (in-theory (enable check-equiv-formula-correct)))

  (local (in-theory (disable w)))

  (defund check-equiv-rule (rune e w)
    (declare (xargs :guard (and (symbolp e)
                                (not (eq e 'quote))
                                (plist-worldp w))))
    (b* ((rule (if (symbolp rune)
                   rune
                 (and (symbol-listp rune)
                      (cadr rune))))
         ((unless rule) nil)
         (form (acl2::meta-extract-formula-w rule w))
         ((unless (pseudo-termp form)) nil))
      (check-equiv-formula form e)))

  (defthmd check-equiv-rule-correct
    (implies (and (check-equiv-rule rune e w)
                  (glcp-generic-geval-ev-meta-extract-global-facts)
                  (equal w (w state))
                  (symbolp e) (not (eq e 'quote)))
             (glcp-generic-equiv-relp e))
    :hints(("Goal" :in-theory (e/d (check-equiv-rule)
                                   (pseudo-termp)))))

  (local (in-theory (enable check-equiv-rule-correct)))


  (defund congruences-find-equiv-rule (congs e w)
    (declare (xargs :guard (and (symbolp e)
                                (not (eq e 'quote))
                                (plist-worldp w))))
    (b* (((when (atom congs)) nil)
         (cong (car congs))
         ((unless (and (acl2::weak-congruence-rule-p cong)
                       (eq (acl2::access acl2::congruence-rule
                                         cong :equiv)
                           e)))
          (congruences-find-equiv-rule (cdr congs) e w))
         (rune (acl2::access acl2::congruence-rule cong :rune)))
      (or (check-equiv-rule rune e w)
          (congruences-find-equiv-rule (cdr congs) e w))))

  (defthmd congruences-find-equiv-rule-correct
    (implies (and (congruences-find-equiv-rule congs e w)
                  (glcp-generic-geval-ev-meta-extract-global-facts)
                  (equal w (w state))
                  (symbolp e) (not (eq e 'quote)))
             (glcp-generic-equiv-relp e))
    :hints(("Goal" :in-theory (e/d (congruences-find-equiv-rule)
                                   (pseudo-termp
                                    acl2::weak-congruence-rule-p
                                    default-car)))))

  (local (in-theory (enable congruences-find-equiv-rule-correct)))

  (defund ensure-equiv-relationp (e w)
    (declare (xargs :guard (and (symbolp e)
                                (plist-worldp w))))
    (b* (((when (member-eq e '(equal iff))) t)
         ((when (eq e 'quote)) nil)
         (coarsenings (getprop e 'acl2::coarsenings nil 'current-acl2-world w))
         ((unless coarsenings) nil)
         ;; shortcut: ACL2 always stores e as a coarsening of itself if it's an
         ;; equivalence relation.  In fact, it should only have coarsenings if it
         ;; is one.  But we don't get to assume that in meta-extract so we look
         ;; for a theorem stating it.
         (congruences (getprop e 'acl2::congruences nil 'current-acl2-world w))
         (equal-congs (cdr (hons-assoc-equal 'equal congruences)))
         (first-arg-congs (and (consp equal-congs) (car equal-congs))))
      (congruences-find-equiv-rule first-arg-congs e w)))

  (defthmd ensure-equiv-relationp-correct
    (implies (and (ensure-equiv-relationp e w)
                  (glcp-generic-geval-ev-meta-extract-global-facts)
                  (equal w (w state))
                  (symbolp e))
             (glcp-generic-equiv-relp e))
    :hints(("Goal" :in-theory (e/d (ensure-equiv-relationp)
                                   (pseudo-termp
                                    acl2::weak-congruence-rule-p
                                    default-car))
            :expand ((glcp-generic-equiv-relp 'iff)
                     (glcp-generic-equiv-relp 'equal))))))


;; X is a gobj. Returns OK, repl, negp.
;; OK implies that equiv-term <=> (xor negp (equiv x repl)) of x, where equiv
;; is an equivalence ok under the contexts.
(defund check-equiv-replacement (x equiv-term contexts state)
  (declare (xargs :guard (contextsp contexts)
                  :stobjs state)
           (ignorable state))
  ;; BOZO fix these to work with context fixing terms, refinements, etc
  (b* (((when (hqual x equiv-term))
        (mv t nil t))
       ((unless (and (consp equiv-term)
              (eq (tag equiv-term) :g-apply)))
        (mv nil nil nil))
       (equiv (g-apply->fn equiv-term))
       ((unless (and (symbolp equiv)
                     (not (eq equiv 'quote))
                     (or (eq equiv 'equal)
                         (member-eq equiv contexts))))
        (mv nil nil nil))
       (args (g-apply->args equiv-term))
       ((unless (equal (len args) 2))
        (mv nil nil nil))
       ((when (hqual (car args) x))
        (mv t (cadr args) nil))
       ((when (hqual (cadr args) x))
        (mv t (car args) nil)))
    (mv nil nil nil)))


;; (defund check-equiv-replacement-ok (x equiv-term contexts state)
;;   (declare (xargs :guard (contextsp contexts)
;;                   :stobjs state)
;;            (ignorable state))
;;   ;; BOZO fix these to work with context fixing terms, refinements, etc
;;   (b* (((unless (and (consp equiv-term)
;;                      (eq (tag equiv-term) :g-apply)))
;;         nil)
;;        (equiv (g-apply->fn equiv-term))
;;        ((unless (and (symbolp equiv)
;;                      (not (eq equiv 'quote))
;;                      (or (eq equiv 'equal)
;;                          (member-eq equiv contexts))))
;;         nil)
;;        (args (g-apply->args equiv-term))
;;        ((unless (equal (len args) 2))
;;         nil)
;;        ((when (or (hqual (car args) x)
;;                   (hqual (cadr args) x)))
;;         t))
;;     nil))

;; (trace$ (check-equiv-replacement :cond (check-equiv-replacement-ok x equiv-term
;;                                                                    contexts
;;                                                                    state)
;;                                  :entry (list 'check-equiv)
;;                                  :exit (list 'check-equiv x (cadr values))
;;                                  :evisc-tuple '(nil 5 10 nil)
;;                                  :hide nil))


(define try-equivalences (x bvars pathcond
                            (contexts contextsp) p bvar-db state)
  :guard (non-exec (ec-call (bvar-listp bvars bvar-db)))
  (b* (((when (atom bvars)) (mv nil nil))
       (bvar (car bvars))
       (equiv-term (get-bvar->term bvar bvar-db))
       ((mv check-ok repl negp)
        (check-equiv-replacement x equiv-term contexts state))
       ((unless check-ok)
        (try-equivalences x (cdr bvars) pathcond contexts p bvar-db state))
       ((when negp)
        (if (false-under-hyp
             (hyp-fix (bfr-to-param-space p (bfr-var bvar))
                      pathcond)
             pathcond)
            (mv t repl)
          (try-equivalences x (cdr bvars) pathcond contexts p bvar-db state)))
       ((unless (true-under-hyp
                 (hyp-fix (bfr-to-param-space p (bfr-var bvar))
                          pathcond)
                 pathcond))
        (try-equivalences x (cdr bvars) pathcond contexts p bvar-db state)))
    (mv t repl)))



(define try-equivalences-loop (x pathcond
                                 (contexts contextsp)
                                 (clk natp)
                                 p bvar-db state)
  :measure (nfix clk)
  (b* (((when (zp clk)) (mv "try-equivalences ran out of clock -- equiv loop?"
                            x))
       (equivs (get-term->equivs x bvar-db))
       ((mv ok repl) (try-equivalences x equivs pathcond contexts p bvar-db
                                       state))
       ((when ok)
        (try-equivalences-loop repl pathcond contexts (1- clk) p bvar-db
                               state)))
    (mv nil x)))


(defund maybe-add-equiv-term (test-obj bvar bvar-db state)
  (declare (xargs :stobjs (bvar-db state)
                  :guard (and (integerp bvar)
                              (<= (base-bvar bvar-db) bvar)
                              (< bvar (next-bvar bvar-db))))
           (ignorable state))
  (b* (;; (equivp (getprop fn 'acl2::coarsenings nil 'current-acl2-world (w state)))
       ;; ((unless equivp)
       ;;  ;; not an equivalence relation
       ;;  bvar-db)
       ((unless (consp test-obj))
        bvar-db)

       ((when (eq (tag test-obj) :g-var))
        (add-term-equiv test-obj bvar bvar-db))

       ((unless (eq (tag test-obj) :g-apply))
        bvar-db)

       (fn (g-apply->fn test-obj))
       (args (g-apply->args test-obj))

       ((unless (and (eq fn 'equal)
                     (equal (len args) 2)))
        (add-term-equiv test-obj bvar bvar-db))
       ((list a b) args)
       ;; The rest is just a heuristic determination of which should rewrite to
       ;; the other.
       (a-goodp (or (atom a)
                    (member (tag a) '(:g-integer :g-boolean))
                    (general-concretep a)))
       ((when a-goodp)
        (add-term-equiv b bvar bvar-db))
       (b-goodp (or (atom b)
                    (member (tag b) '(:g-integer :g-boolean))
                    (general-concretep b)))
       ((when b-goodp)
        (add-term-equiv a bvar bvar-db)))
    bvar-db))

;; (defund glcp-generic-geval-ev-theoremsp (rules)
;;   (if (atom rules)
;;       t
;;     (and (glcp-generic-geval-ev-theoremp (car rules))
;;          (glcp-generic-geval-ev-theoremsp (cdr rules)))))



;; (defund meta-extract-formulas (names wrld)
;;   (declare (xargs :guard (plist-worldp wrld)))
;;   (b* (((when (atom names)) nil)
;;        (name (car names))
;;        ((unless (symbolp name)) (meta-extract-formulas (cdr names) wrld))
;;        (thm (acl2::meta-extract-formula-w name wrld)))
;;     (cons thm (meta-extract-formulas (cdr names) wrld))))

;; (defthm glcp-generic-geval-ev-theoremsp-of-meta-extract-formulas
;;   (implies (and (glcp-generic-geval-ev-meta-extract-global-facts)
;;                 (equal wrld (w state)))
;;            (glcp-generic-geval-ev-theoremsp (meta-extract-formulas names wrld)))
;;   :hints(("Goal" :in-theory (e/d (glcp-generic-geval-ev-theoremsp
;;                                   meta-extract-formulas)
;;                                  (w)))))

(defund conjunction-to-list (x)
  (declare (xargs :guard (pseudo-termp x)))
  (if (or (atom x)
          (not (eq (car x) 'if))
          (not (equal (fourth x) ''nil)))
      (list x)
    (cons (second x)
          (conjunction-to-list (third x)))))

(defthm conjunction-to-list-pseudo-term-listp
  (implies (pseudo-termp x)
           (pseudo-term-listp (conjunction-to-list x)))
  :hints(("Goal" :in-theory (enable conjunction-to-list))))


(defsection glcp-branch-merge-formula-to-rule

  (local (defthm pseudo-termp-subterms
           (implies (and (pseudo-termp x)
                         (consp x)
                         (not (eq (car x) 'quote)))
                    (and (pseudo-termp (cadr x))
                         (pseudo-termp (caddr x))
                         (pseudo-termp (cadddr x))
                         (implies (cdr x)
                                  (consp (cdr x)))
                         (implies (cddr x)
                                  (consp (cddr x)))
                         (implies (cdddr x)
                                  (consp (cdddr x)))))
           :hints(("Goal" :expand ((pseudo-termp x)
                                   (pseudo-term-listp (cdr x))
                                   (pseudo-term-listp (cddr x))
                                   (pseudo-term-listp (cdddr x)))))))

  (local (in-theory (disable acl2::beta-reduce-full
                             pseudo-termp)))


  (defund glcp-branch-merge-formula-to-rule (name wrld)
    (declare (xargs :guard (and (symbolp name) (plist-worldp wrld))
                    :guard-hints
                    (("goal" :use ((:instance
                                    acl2::pseudo-termp-of-beta-reduce-full
                                    (x (acl2::meta-extract-formula-w name wrld))))
                      :in-theory (disable acl2::pseudo-termp-of-beta-reduce-full)))))
    (b* ((thm (acl2::meta-extract-formula-w name wrld))
         ((unless (pseudo-termp thm)) (mv nil nil))
         (thm (acl2::beta-reduce-full thm))
         ((when (atom thm)) (mv nil nil))
         ((mv hyps concl)
          (if (eq (car thm) 'implies)
              (mv (conjunction-to-list (second thm))
                  (third thm))
            (mv nil thm)))
         ((when (atom concl)) (mv nil nil))
         (equiv (car concl))
         ((unless (and (symbolp equiv)
                       (not (eq equiv 'quote))
                       (getprop equiv 'acl2::coarsenings nil 'current-acl2-world wrld)
                       (eql (len concl) 3)))
          (mv nil nil)))
      (mv t (acl2::make-rewrite-rule
             :rune `(:gl-branch-merge ,name)
             :nume -1
             :hyps hyps
             :equiv equiv
             :lhs (second concl)
             :rhs (third concl)
             :subclass 'acl2::backchain)))))

(defund glcp-branch-merge-formulas-to-rules (names wrld)
  (declare (xargs :guard (plist-worldp wrld)))
  (b* (((when (atom names)) nil)
       ((unless (symbolp (car names)))
        (glcp-branch-merge-formulas-to-rules (cdr names) wrld))
       ((mv ok rule) (glcp-branch-merge-formula-to-rule (car names) wrld)))
    (if ok
        (cons rule (glcp-branch-merge-formulas-to-rules (cdr names) wrld))
      (glcp-branch-merge-formulas-to-rules (cdr names) wrld))))


(defund glcp-get-branch-merge-rules (fn wrld)
  (declare (xargs :guard (and (symbolp fn)
                              (plist-worldp wrld))))
  (b* ((thms (cdr (hons-assoc-equal fn (acl2::table-alist 'gl-branch-merge-rules wrld)))))
    (glcp-branch-merge-formulas-to-rules thms wrld)))

(memoize 'glcp-get-branch-merge-rules)

(defun weak-rewrite-rule-listp (x)
  (declare (xargs :guard t))
  (if (atom x)
      (eq x nil)
    (and (acl2::weak-rewrite-rule-p (car x))
         (weak-rewrite-rule-listp (cdr x)))))

(defund rewrite-rules->runes (x)
  (declare (xargs :guard (weak-rewrite-rule-listp x)))
  (if (atom x)
      nil
    (cons (acl2::rewrite-rule->rune (car x))
          (rewrite-rules->runes (cdr x)))))

(defun-inline glcp-if-or-condition (test tbr contexts)
  (declare (xargs :guard t))
  (and (hons-equal test tbr)
       ;; dumb
       (or (not contexts) (equal contexts '(iff)))))

(defun-inline glcp-or-test-contexts (contexts)
  (declare (xargs :guard t))
  (if (equal contexts '(iff))
      '(iff)
    nil))

(defund glcp-lift-ifsp (fn flg w)
  (declare (xargs :guard (and (symbolp fn)
                              (plist-worldp w))))
  (and flg
       (not (cdr (hons-assoc-equal fn (table-alist 'gl-if-opaque-fns w))))))



(defthmd acl2-count-of-car
  (<= (acl2-count (car x)) (acl2-count x))
  :rule-classes :linear)

(defthmd acl2-count-of-cdr
  (<= (acl2-count (cdr x)) (acl2-count x))
  :rule-classes :linear)

(defthmd acl2-count-of-car-g-apply->args
  (implies (equal (tag x) :g-apply)
           (< (acl2-count (car (g-apply->args x))) (acl2-count x)))
  :hints(("Goal" :in-theory (enable acl2-count-of-car)))
  :rule-classes :linear)

(defthmd acl2-count-of-cadr-g-apply->args
  (implies (equal (tag x) :g-apply)
           (< (acl2-count (cadr (g-apply->args x))) (acl2-count x)))
  :hints(("Goal" :in-theory (enable acl2-count-of-car
                                    acl2-count-of-cdr)))
  :rule-classes :linear)

;; (local (defthm acl2-count-of-g-apply->args-consp
;;          (implies (consp x)
;;                   (< (acl2-count (g-apply->args x)) (acl2-count x)))
;;          :rule-classes :linear))

(encapsulate nil
  (local (defthm acl2-count-of-g-concrete->obj
           (implies (equal (tag x) :g-concrete)
                    (< (acl2-count (g-concrete->obj x))
                       (acl2-count x)))
           :rule-classes :linear))
  (local (defthm acl2-count-of-car-strong
           (implies (consp x)
                    (< (acl2-count (car X)) (acl2-count x)))
           :rule-classes :linear))
  (local (defthm acl2-count-of-cdr-strong
           (implies (consp x)
                    (< (acl2-count (cdr X)) (acl2-count x)))
           :rule-classes :linear))

  (local (defthm acl2-count-of-g-concrete
           (equal (acl2-count (g-concrete x))
                  (+ 1 (acl2-count x)))
           :hints(("Goal" :in-theory (enable g-concrete)))))

  (defthmd acl2-count-of-general-consp-car
    (implies (general-consp x)
             (< (acl2-count (general-consp-car x))
                (acl2-count x)))
    :hints(("Goal" :in-theory (enable mk-g-concrete)))
    :rule-classes :linear)

  (defthmd acl2-count-of-general-consp-cdr
    (implies (general-consp x)
             (< (acl2-count (general-consp-cdr x))
                (acl2-count x)))
    :hints(("Goal" :in-theory (enable mk-g-concrete)))
    :rule-classes :linear))


(define glcp-vacuity-check (hyp-bfr (config glcp-config-p))
  :returns (mv (err)
               (unsat-p))
  (b* (((unless (glcp-config->check-vacuous config))
        (mv nil nil)) ;; no error, not unsat
       ((mv vac-check-sat vac-check-succeeded &)
        (bfr-vacuity-check hyp-bfr))
       ((when (and (glcp-config->abort-vacuous config)
                   (or (not vac-check-sat)
                       (not vac-check-succeeded))))
        (mv (if vac-check-succeeded
                "Hypothesis is not satisfiable"
              "Error in vacuity check")
            vac-check-succeeded)))
    (mv nil
        (and vac-check-succeeded
             (not vac-check-sat))))
  ///
  (std::defretd glcp-vacuity-check-unsat-implies
    (implies unsat-p
             (not (bfr-eval hyp-bfr env)))
    :hints(("Goal" :in-theory (enable bfr-vacuity-check-unsat)))))



(defconst *glcp-generic-template-subst*
  (glcp-name-subst 'glcp-generic))

(make-event ;; glcp-generic-interp
 (sublis *glcp-generic-template-subst*
         *glcp-interp-template*))





