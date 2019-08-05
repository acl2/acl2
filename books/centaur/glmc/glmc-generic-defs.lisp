; GLMC -- Hardware model checking interface
; Copyright (C) 2017 Centaur Technology
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

(include-book "glmc-templates")
(include-book "bfr-mcheck")
(include-book "centaur/gl/ctrex-utils" :dir :system)
(include-book "shape-spec-invert")
(include-book "centaur/gl/gl-generic-interp-defs" :dir :system)
(include-book "std/strings/strsubst" :dir :system)
(include-book "std/util/defenum" :dir :system)
(include-book "centaur/gl/shape-spec-defs" :dir :system)
(include-book "std/alists/fal-extract" :dir :system)
(include-book "clause-processors/bindinglist" :dir :system)
(local (include-book "tools/trivial-ancestors-check" :dir :system))
(local (include-book "system/f-put-global" :dir :system))
;; (local (include-book "clause-processors/just-expand" :dir :system))

(local (in-theory (enable get-global)))

(defun glmc-name (clause-proc orig-name)
  (intern-in-package-of-symbol
   (str::strsubst "GLMC" (symbol-name clause-proc)
                  (symbol-name orig-name))
   clause-proc))

(defun glmc-name-list (clause-proc names)
  (if (atom names)
      nil
    (cons (glmc-name clause-proc (car names))
          (glmc-name-list clause-proc (cdr names)))))

(defun glmc-name-subst (clause-proc)
  (b* ((glcp-name (intern-in-package-of-symbol
                   (concatenate 'string (symbol-name clause-proc) "-GLCP")
                   clause-proc))
       (glcp-subst (glcp-name-subst glcp-name)))
    (append (pairlis$ *glmc-fnnames* (glmc-name-list clause-proc *glmc-fnnames*))
            glcp-subst)))

(defconst *glmc-generic-name-subst*
  (append (pairlis$ *glmc-fnnames* (glmc-name-list 'glmc-generic *glmc-fnnames*))
          *glcp-generic-template-subst*))

(set-state-ok t)

(std::defaggregate hyp-tuple
  ((name stringp)
   (term pseudo-termp)
   (alist alistp))
  :layout :list)

(std::deflist hyp-tuplelist-p (x)
  (hyp-tuple-p x))

(std::deflist variable-listp (x)
  (variablep x))

(std::defenum st-hyp-method-p
  (:inductive-sat :inductive-clause :mcheck))

(std::defaggregate glmc-config
  ((glcp-config glcp-config-p :default (make-glcp-config))
   (st-var variablep :default 'acl2::st)
   (in-vars variable-listp :default '(acl2::ins))
   (frame-ins pseudo-term-listp :default '((car acl2::ins)))
   (rest-ins pseudo-term-listp :default '((cdr acl2::ins)))
   (end-ins pseudo-termp :default '(not (consp acl2::ins)))
   (frame-in-vars variable-listp :default '(acl2::in))
   (in-measure pseudo-termp :default '(len acl2::ins))
   (run pseudo-termp)
   (st-hyp pseudo-termp)
   (in-hyp pseudo-termp)
   (bindings acl2::bindinglist-p)
   (bound-vars symbol-listp)
   (initstp pseudo-termp)
   (nextst pseudo-termp)
   (constr pseudo-termp)
   (prop pseudo-termp)
   (st-hyp-method st-hyp-method-p :default 'nil)
   (hints)
   (main-rewrite-rules :default ':default)
   (main-branch-merge-rules :default ':default)
   (extract-rewrite-rules :default ':default)
   (extract-branch-merge-rules :default ':default)))

(acl2::def-b*-binder glmc-config+
  :decls ((declare (xargs :guard (symbolp (car args)))))
  :body
  `(b* (((glmc-config . ,args) . ,acl2::forms)
        (glmc-config+-tmp-config ,(car args))
        ((glcp-config ,(car args) :quietp t)
         ,(intern-in-package-of-symbol (concatenate 'string (symbol-name (car args)) ".GLCP-CONFIG")
                                       (car args)))
        (,(intern-in-package-of-symbol (concatenate 'string "?" (symbol-name (car args)))
                                       (car args))
         glmc-config+-tmp-config))
     ,acl2::rest-expr))

(defthm glcp-config-p-of-glcp-config-update-param
  (implies (glcp-config-p config)
           (glcp-config-p (glcp-config-update-param param config)))
  :hints(("Goal" :in-theory (enable glcp-config-update-param))))

(define glmc-config-update-param (param (config glmc-config-p))
  :returns (new-config glmc-config-p :hyp :guard) 
  (b* (((glmc-config config))
       (glcp-config (glcp-config-update-param param config.glcp-config)))
    (change-glmc-config config :glcp-config glcp-config))
  ///
  (std::defret param-bfr-of-glmc-config-update-param
    (b* (((glmc-config+ new-config)))
      (equal new-config.param-bfr param)))

  (std::defret other-fields-of-glmc-config-update-param
    (b* (((glmc-config+ new-config))
         ((glmc-config+ config)))
      (and (equal new-config.st-hyp config.st-hyp)
           (equal new-config.in-hyp config.in-hyp)
           (equal new-config.prop config.prop)
           (equal new-config.initstp config.initstp)
           (equal new-config.constr config.constr)
           (equal new-config.nextst config.nextst)
           (equal new-config.st-var config.st-var)))
    :hints(("Goal" :in-theory (enable glcp-config-update-param))))


  (defthm glcp-config-update-param-redundant
    (equal (glcp-config-update-param p1 (glcp-config-update-param p2 config))
           (glcp-config-update-param p1 config))
    :hints(("Goal" :in-theory (enable glcp-config-update-param))))

  (defthm glcp-config-of-glmc-config-update-param
    (equal (glmc-config->glcp-config (glmc-config-update-param hyp-bfr config))
           (glcp-config-update-param  hyp-bfr (glmc-config->glcp-config config)))
    :hints(("Goal" :in-theory (enable glmc-config-update-param)))))


(define glcp-config-update-rewrites ((config glcp-config-p)
                                     (rewrites)
                                     (branch-merges))
  :returns (new-config glcp-config-p :hyp :guard)
  (b* (((glcp-config config)))
    (change-glcp-config config
                        :rewrite-rule-table (if (eq rewrites :default)
                                                config.rewrite-rule-table
                                              rewrites)
                        :branch-merge-rules (if (eq branch-merges :default)
                                                config.branch-merge-rules
                                              branch-merges)))
  ///
  (std::defret glcp-config->overrides-of-glcp-config-update-rewrites
    (equal (glcp-config->overrides new-config)
           (glcp-config->overrides config)))

  (std::defret glcp-config->shape-spec-alist-of-glcp-config-update-rewrites
    (equal (glcp-config->shape-spec-alist new-config)
           (glcp-config->shape-spec-alist config))))

(define glmc-config-update-rewrites ((config glmc-config-p)
                                     (rewrites)
                                     (branch-merges))
  :returns (new-config glmc-config-p :hyp :guard) 
  (b* (((glmc-config config))
       (glcp-config (glcp-config-update-rewrites config.glcp-config rewrites branch-merges)))
    (change-glmc-config config :glcp-config glcp-config))
  ///

  (std::defret other-fields-of-glmc-config-update-rewrites
    (b* (((glmc-config+ new-config))
         ((glmc-config+ config)))
      (and (equal new-config.st-hyp config.st-hyp)
           (equal new-config.in-hyp config.in-hyp)
           (equal new-config.prop config.prop)
           (equal new-config.initstp config.initstp)
           (equal new-config.constr config.constr)
           (equal new-config.nextst config.nextst)
           (equal new-config.st-var config.st-var)
           (equal new-config.bindings config.bindings))))

  (std::defret glcp-config-of-glmc-config-update-rewrites
    (equal (glmc-config->glcp-config new-config)
           (glcp-config-update-rewrites (glmc-config->glcp-config config) rewrites branch-merges))
    :hints(("Goal" :in-theory (enable glmc-config-update-rewrites)))))


(define reset-interp-st (interp-st)
  :returns (new-interp-st (equal new-interp-st (create-interp-st)))
  :prepwork ((local (defthmd take-open
                      (implies (syntaxp (quotep n))
                               (equal (take n x)
                                      (if (zp n)
                                          nil
                                        (cons (car x) (take (1- n) (cdr x))))))))
             (local (defthm cddddddr-of-take-6
                      (equal (cddr (cddddr (take 6 x))) nil)
                      :hints(("Goal" :in-theory (enable take-open))))))
  (b* ((interp-st (mbe :logic (non-exec (take 6 interp-st))
                       :exec interp-st))
       (interp-st (update-is-obligs nil interp-st))
       (interp-st (update-is-constraint nil interp-st))
       (interp-st (update-is-constraint-db nil interp-st))
       (interp-st (update-is-add-bvars-allowed nil interp-st))
       (interp-st (update-is-backchain-limit nil interp-st)))
    (acl2::stobj-let
     ((interp-profiler (is-prof interp-st)))
     (interp-profiler)
     (b* ((interp-profiler (mbe :logic (non-exec (take 6 interp-profiler))
                                :exec interp-profiler))
          (interp-profiler (update-prof-enabledp nil interp-profiler))
          (interp-profiler (update-prof-indextable nil interp-profiler))
          (interp-profiler (update-prof-totalcount 0 interp-profiler))
          (interp-profiler (update-prof-nextindex 0 interp-profiler))
          (interp-profiler (resize-prof-array 0 interp-profiler))
          (interp-profiler (update-prof-stack nil interp-profiler)))
       interp-profiler)
     interp-st)))
       


(define init-interp-st (interp-st (config glmc-config-p) state)
  :guard (non-exec (equal interp-st (create-interp-st)))
  :returns (mv er new-interp-st)
  (b* ((interp-st (mbe :logic (non-exec (create-interp-st)) :exec interp-st))
       ((glmc-config+ config))
       (interp-st (update-is-constraint (bfr-constr-init) interp-st))
       (interp-st (update-is-add-bvars-allowed t interp-st))
       (interp-st (update-is-prof-enabledp config.prof-enabledp interp-st))
       (constraint-db (ec-call (gbc-db-make-fast (table-alist 'gl-bool-constraints (w state)))))
       ((unless (ec-call (gbc-db-emptyp constraint-db)))
        (mv "The constraint database stored in the table ~
             GL::GL-BOOL-CONSTRAINTS contains nonempty substitutions -- ~
             somehow it has gotten corrupted!~%"
            interp-st))
       (interp-st (update-is-constraint-db constraint-db interp-st)))
    (mv nil interp-st))
  ///
  (std::defret constraint-of-init-interp-st
    (bfr-hyp-eval (nth *is-constraint* new-interp-st) env))

  (std::defret obligs-of-init-interp-st
    (equal (nth *is-obligs* new-interp-st) nil))

  (std::defret empty-constraint-db-of-init-interp-st
    (implies (not er)
             (gbc-db-emptyp (nth *is-constraint-db* new-interp-st))))

  (std::defret empty-constraint-of-init-interp-st
    (equal (nth *is-constraint* new-interp-st) (bfr-constr-init)))

  (std::defret init-interp-st-normalize
    (implies (syntaxp (not (equal interp-st ''nil)))
             (equal (init-interp-st interp-st config state)
                    (init-interp-st nil config state)))))


(define alist-extract (keys alist)
  :returns (new-alist (equal new-alist (acl2::fal-extract keys alist)))
  (b* (((when (atom keys)) nil)
       (look (hons-assoc-equal (car keys) alist))
       ((when look)
        (cons look (alist-extract (cdr keys) alist))))
    (alist-extract (cdr keys) alist)))


(define glcp-parametrize-interp-state (pathcond-bfr
                                       interp-st)
  :returns (mv contra new-interp-st)
  (b* (((mv contra constraint &)
        (bfr-constr-assume
         (bfr-to-param-space pathcond-bfr
                             (bfr-constr->bfr (is-constraint interp-st)))
         (bfr-constr-init)))

       (interp-st (update-is-constraint constraint interp-st))
       (constraint-db (parametrize-constraint-db pathcond-bfr (is-constraint-db interp-st)))
       (interp-st (update-is-constraint-db constraint-db interp-st)))
    (mv contra interp-st)))



(define glcp-parametrize-accs (pathcond-bfr interp-st bvar-db1 bvar-db)
  :returns (mv contra new-interp-st new-bvar-db)
  (b* ((bvar-db (init-bvar-db (base-bvar bvar-db1) bvar-db))
       (bvar-db (parametrize-bvar-db pathcond-bfr bvar-db1 bvar-db))
       ((mv contra1 interp-st)
        (glcp-parametrize-interp-state pathcond-bfr interp-st)))
    (mv contra1 interp-st bvar-db)))


(define glcp-bfr-to-pathcond (bfr pathcond)
  :returns (mv contra new-pathcond)
  (b* ((pathcond-bfr (bfr-to-param-space bfr bfr))
       (pathcond (bfr-hyp-init pathcond))
       ((mv contra pathcond ?undo) (bfr-assume pathcond-bfr pathcond)))
    (mv contra pathcond)))



(define glcp-prepare-param-inputs (pathcond-bfr
                                           pathcond
                                           interp-st
                                           bvar-db1
                                           bvar-db)
  :guard (acl2::interp-defs-alistp (is-obligs interp-st))
  :enabled t
  :returns (mv contra new-pathcond new-interp-st new-bvar-db)
  (b* (((mv contra1 interp-st bvar-db)
        (glcp-parametrize-accs pathcond-bfr interp-st bvar-db1 bvar-db))
       
       ((mv contra2 pathcond) (glcp-bfr-to-pathcond pathcond-bfr pathcond)))
    
    (mv (or contra1 contra2)
        pathcond interp-st bvar-db)))

(acl2::defstobj-clone hyp-bvar-db bvar-db :prefix "HYP-")


(defines gobj-vars
  (define gobj-vars (x)
    :verify-guards nil
    :measure (acl2-count x)
    :returns (vars set::setp)
    (if (atom x)
        nil
      (case (tag x)
        ((:g-integer :g-boolean :g-concrete) nil)
        (:g-var (set::insert (g-var->name x) nil))
        (:g-apply (gobj-list-vars (g-apply->args x)))
        (:g-ite (set::union (gobj-vars (g-ite->test x))
                            (set::union (gobj-vars (g-ite->then x))
                                        (gobj-vars (g-ite->else x)))))
        (t (set::union (gobj-vars (car x))
                       (gobj-vars (cdr x)))))))
  (define gobj-list-vars (x)
    :returns (vars set::setp)
    (if (atom x)
        nil
      (set::union (gobj-vars (car x))
                  (gobj-list-vars (cdr x)))))
  ///
  (verify-guards gobj-vars))

(defines glmc-gobj-to-term
  (define glmc-gobj-to-term (x)
    :measure (acl2-count x)
    :returns (mv err (term pseudo-termp))
    (if (general-concretep x)
        (mv nil (kwote (general-concrete-obj x)))
      (case (tag x)
        (:g-boolean
         (mv "contained a symbolic Boolean" '<symbolic-bool>))
        (:g-integer
         (mv "contained a symbolic integer" '<symbolic-num>))
        (:g-var (b* ((name (g-var->name x)))
                  (if (and (symbolp name) name)
                      (mv nil name)
                    (mv (msg "contained bad variable name: ~x0" name)
                        '<bad-variable>))))
        (:g-apply (b* (((mv er1 args) (glmc-gobj-list-to-terms (g-apply->args x)))
                       (fn (g-apply->fn x))
                       ((mv er2 fn)
                        (if (and (symbolp fn) (not (eq fn 'quote)))
                            (mv nil fn)
                          (mv (msg "contained bad function name: ~x0" fn)
                              '<bad-function-name>))))
                    (mv (or er2 er1) (cons fn args))))
        (:g-ite (b* (((mv er1 test) (glmc-gobj-to-term (g-ite->test x)))
                     ((mv er2 then) (glmc-gobj-to-term (g-ite->then x)))
                     ((mv er3 else) (glmc-gobj-to-term (g-ite->else x))))
                  (mv (or er1 er2 er3) `(if ,test ,then ,else))))
        (t (b* (((mv er1 car) (glmc-gobj-to-term (car x)))
                ((mv er2 cdr) (glmc-gobj-to-term (cdr x))))
             (mv (or er1 er2) `(cons ,car ,cdr)))))))
  (define glmc-gobj-list-to-terms (x)
    :returns (mv er (terms pseudo-term-listp))
    (b* (((when (atom x)) (mv nil nil))
         ((mv er1 car) (glmc-gobj-to-term (car x)))
         ((mv er2 cdr) (glmc-gobj-list-to-terms (cdr x))))
      (mv (or er1 er2) (cons car cdr)))))

(define glmc-bvar-db-to-state-updates ((idx natp)
                                       (state-vars variable-listp)
                                       bvar-db)
    :guard (and (<= (base-bvar bvar-db) idx)
                (<= idx (next-bvar bvar-db)))
    :measure (nfix (- (next-bvar bvar-db) (nfix idx)))
    :returns (updates pseudo-term-alistp)
    (b* ((idx (lnfix idx))
         ((when (mbe :logic (zp (- (next-bvar bvar-db) idx))
                     :exec (eql (next-bvar bvar-db) idx)))
          nil)
         (gobj (get-bvar->term idx bvar-db))
         (vars (gobj-vars gobj))
         (state-bitp (acl2::hons-intersect-p vars state-vars))
         ((unless state-bitp)
          (glmc-bvar-db-to-state-updates (1+ idx) state-vars bvar-db))
         ((mv to-term-er term) (glmc-gobj-to-term gobj))
         (bad-state-vars (acl2::hons-set-diff vars state-vars))
         ((when bad-state-vars)
          (cw "Warning: The following term containing both state and input ~
             variables was turned into a symbolic bit.  In the Boolean model ~
             it will be treated as an input, which may lead to false ~
             counterexamples:~%~x0~%" term)
          (glmc-bvar-db-to-state-updates (1+ idx) state-vars bvar-db))
         ((when to-term-er)
          (cw "Warning: The following term perhaps should be considered a state ~
             bit, but it was rejected because it ~@0. It will instead be ~
             treated as an input bit, which may lead to false ~
             counterexamples:~%~x1~%" to-term-er term)
          (glmc-bvar-db-to-state-updates (1+ idx) state-vars bvar-db)))
      (cons (cons idx term)
            (glmc-bvar-db-to-state-updates (1+ idx) state-vars bvar-db))))



(defthm true-listp-caar-of-bindinglist
  (implies (acl2::bindinglist-p x)
           (true-listp (caar x)))
  :hints(("Goal" :in-theory (enable acl2::bindinglist-p))))

(defthm true-listp-cdar-of-bindinglist
  (implies (acl2::bindinglist-p x)
           (true-listp (cdar x)))
  :hints(("Goal" :in-theory (enable acl2::bindinglist-p))))

(defthm true-listp-of-union-equal
  (implies (true-listp y)
           (true-listp (union-equal x y)))
  :rule-classes :type-prescription)

(local
 (defthm symbol-listp-of-set-diff
   (implies (symbol-listp x)
            (symbol-listp (set-difference-eq x y)))
   :hints(("Goal" :in-theory (enable set-difference-eq)))))


(local (defthm symbol-listp-of-union
         (implies (and (symbol-listp x)
                       (symbol-listp y))
                  (symbol-listp (union-eq x y)))))


                               

(local (defthm symbol-listp-when-variable-listp
         (implies (and (variable-listp x)
                       (true-listp x))
                  (symbol-listp x))))

(defthm variable-listp-alist-keys-of-shape-spec-bindings
  (implies (shape-spec-bindingsp x)
           (variable-listp (alist-keys x)))
  :hints(("Goal" :in-theory (enable alist-keys))))

(define glmc-syntax-checks ((config glmc-config-p))
  :returns (er)
  (b* (((glmc-config+ config))

       (non-st-hyp-vars (remove config.st-var (simple-term-vars config.st-hyp)))
       ((when (consp non-st-hyp-vars))
        (msg "State hyp contains variables other than the state var ~x0: ~x1~%"
             config.st-var non-st-hyp-vars))

       ;; (non-st-initst-vars (remove config.st-var (simple-term-vars config.initstp)))
       ;; ((when (consp non-st-initst-vars))
       ;;  (msg "Init state predicate contains variables other than the state var ~x0: ~x1~%"
       ;;       config.st-var non-st-initst-vars))

       (in-hyp-vars (simple-term-vars config.in-hyp))

       ;; ((when (member config.st-var in-hyp-vars))
       ;;  (msg "Input hyp refers to the state variable ~x0~%" config.st-var))

       ((unless (hons-assoc-equal config.st-var config.shape-spec-alist))
        (msg "State var ~x0 is not bound in the shape spec bindings~%" config.st-var))

       (shape-spec-bound-vars (alist-keys config.shape-spec-alist))

       (in-hyp-unbound-vars (acl2::hons-set-diff in-hyp-vars shape-spec-bound-vars))
       ((when (consp in-hyp-unbound-vars))
        (msg "Input hyp contains variables not bound in the shape spec bindings: ~x0~%"
             in-hyp-unbound-vars))

       (bindings-vars (acl2::bindinglist-free-vars config.bindings))
       (bindings-unbound-vars (acl2::hons-set-diff bindings-vars shape-spec-bound-vars))
       ((when (consp bindings-unbound-vars))
        (msg "B* bindings contain variables not bound in the shape spec bindings: ~x0~%"
             bindings-unbound-vars))

       (bindings-bound-vars (acl2::bindinglist-bound-vars config.bindings))
       ((when (member config.st-var bindings-bound-vars))
        (msg "B* bindings rebind the state variable"))

       (all-bound-vars (union-eq shape-spec-bound-vars
                                      bindings-bound-vars))

       (initst-vars (simple-term-vars config.initstp))
       (initst-unbound-vars (acl2::hons-set-diff initst-vars all-bound-vars))
       ((when (consp initst-unbound-vars))
        (msg "Initial state predicate contains unbound variables: ~x0~%"
             initst-unbound-vars))

       (nextst-vars (simple-term-vars config.nextst))
       (nextst-unbound-vars (acl2::hons-set-diff nextst-vars all-bound-vars))
       ((when (consp nextst-unbound-vars))
        (msg "Nextstate contains unbound variables: ~x0~%"
             nextst-unbound-vars))

       (prop-vars (simple-term-vars config.prop))
       (prop-unbound-vars (acl2::hons-set-diff prop-vars all-bound-vars))
       ((when (consp prop-unbound-vars))
        (msg "Property contains unbound variables: ~x0~%"
             prop-unbound-vars))

       (constr-vars (simple-term-vars config.constr))
       (constr-unbound-vars (acl2::hons-set-diff constr-vars all-bound-vars))
       ((when (consp constr-unbound-vars))
        (msg "Constraint contains unbound variables: ~x0~%"
             constr-unbound-vars))

       (shape-specs (shape-spec-bindings->sspecs config.shape-spec-alist))
       (dupe-indices (acl2::duplicated-members (shape-spec-list-indices shape-specs)))
       ((when dupe-indices)
        (msg "The shape specs contain duplicated indices: ~x0~%" dupe-indices))

       (dupe-vars (acl2::duplicated-members (shape-spec-list-vars shape-specs)))
       ((when dupe-vars)
        (msg "The shape specs contain duplicated vars: ~x0~%" dupe-vars)))

    nil)
  ///
  (std::defret shape-specs-duplicate-free-by-glmc-syntax-checks
    (implies (not er)
             (b* ((shape-specs (shape-spec-bindings->sspecs (glcp-config->shape-spec-alist (glmc-config->glcp-config config)))))
               (and (no-duplicatesp (shape-spec-list-indices shape-specs))
                    (no-duplicatesp (shape-spec-list-vars shape-specs))))))

  (local (defthm consp-of-set-diff
           (equal (consp (set-difference$ a b))
                  (not (subsetp a b)))
           :hints(("Goal" :in-theory (enable set-difference$ subsetp)))))

  (local (defthm consp-of-remove
           (equal (consp (remove x y))
                  (not (subsetp y (list x))))
           :hints(("Goal" :in-theory (enable subsetp remove)))))
  
  (std::defret vars-subset-of-bound-by-glmc-syntax-checks
    (implies (not er)
             (b* (((glmc-config config))
                  (shape-specs (glcp-config->shape-spec-alist config.glcp-config))
                  (shape-spec-bound-vars (alist-keys shape-specs))
                  (bindings-bound-vars (acl2::bindinglist-bound-vars config.bindings))
                  (all-bound-vars (append shape-spec-bound-vars bindings-bound-vars)))
               (and (subsetp-equal (simple-term-vars config.st-hyp) (list config.st-var))
                    (subsetp-equal (simple-term-vars config.st-hyp) shape-spec-bound-vars)
                    (subsetp-equal (acl2::bindinglist-free-vars config.bindings) shape-spec-bound-vars)
                    ;; (subsetp-equal (simple-term-vars config.initstp) (list config.st-var))
                    (subsetp-equal (simple-term-vars config.in-hyp) shape-spec-bound-vars)
                    ;; (not (member config.st-var (simple-term-vars config.in-hyp)))
                    ;; (subsetp-equal (simple-term-vars config.in-hyp) (remove config.st-var bound-vars))
                    (not (member config.st-var bindings-bound-vars))
                    (subsetp-equal (simple-term-vars config.nextst) all-bound-vars)
                    (subsetp-equal (simple-term-vars config.initstp) all-bound-vars)
                    (subsetp-equal (simple-term-vars config.prop) all-bound-vars)
                    (subsetp-equal (simple-term-vars config.constr) all-bound-vars)
                    (hons-assoc-equal config.st-var shape-specs)
                    (member config.st-var shape-spec-bound-vars))))))


(std::defaggregate glmc-fsm
  ((nextst bfr-updates-p)
   (prop)
   (fsm-constr)
   (bit-constr)
   (initst)
   (st-hyp)
   (hyp)
   (st-hyp-next)
   (interp-clauses pseudo-term-list-listp)
   (hyp-var-bound natp :rule-classes (:rewrite :type-prescription))
   (var-bound natp :rule-classes (:rewrite :type-prescription))))


(define glmc-clause-syntax-checks ((config glmc-config-p))
  (b* (((glmc-config+ config))
       (config.in-vars (list-fix config.in-vars))
       ((unless (subsetp-equal (simple-term-vars config.in-measure) config.in-vars))
        (msg "Measure should only depend on the input vars ~x0." config.in-vars))
       ((unless (subsetp-equal (simple-term-vars-lst config.rest-ins) config.in-vars))
        (msg "Rest-ins should only depend on the input vars ~x0." config.in-vars))
       ((unless (equal (len config.frame-ins) (len config.frame-in-vars)))
        (msg "Frame-ins should be the same length as frame-in-vars."))
       ((unless (equal (len config.in-vars) (len config.rest-ins)))
        (msg "Rest-ins should be the same length as in-vars"))
       ((unless (no-duplicatesp-equal (cons config.st-var (append config.in-vars (list-fix config.frame-in-vars)))))
        (msg "Duplicate variables")))
    nil)
  ///
  (defthm glmc-clause-syntax-checks-implies
    (implies (not (glmc-clause-syntax-checks config))
             (b* (((glmc-config+ config)))
               (and (subsetp (simple-term-vars config.in-measure) config.in-vars)
                    (subsetp (simple-term-vars-lst config.rest-ins) config.in-vars)
                    (equal (len config.frame-ins) (len config.frame-in-vars))
                    (equal (len config.in-vars) (len config.rest-ins))
                    (no-duplicatesp config.in-vars)
                    (no-duplicatesp config.frame-in-vars)
                    (not (intersectp-equal config.in-vars config.frame-in-vars))
                    (not (intersectp-equal config.frame-in-vars config.in-vars))
                    (not (member config.st-var config.in-vars))
                    (not (member config.st-var config.frame-in-vars))
                    (not (member config.st-var (simple-term-vars config.in-measure)))
                    (not (intersectp-equal config.frame-in-vars (simple-term-vars config.in-measure)))
                    (not (intersectp-equal (simple-term-vars config.in-measure) config.frame-in-vars))
                    (not (member config.st-var (simple-term-vars-lst config.rest-ins)))
                    (not (intersectp-equal config.frame-in-vars (simple-term-vars-lst config.rest-ins)))
                    (not (intersectp-equal (simple-term-vars-lst config.rest-ins) config.frame-in-vars)))))
    :hints ((acl2::set-reasoning))))


(define glmc-measure-clauses ((config glmc-config-p))
  :guard (not (glmc-clause-syntax-checks config))
  :returns (measure-clauses pseudo-term-list-listp :hyp :guard
                            :hints(("Goal" :in-theory (enable length pseudo-termp))))
  (b* (((glmc-config+ config)))
    (list `((not (gl-cp-hint 'measure-check))
            (o-p ,config.in-measure))
          `((not (gl-cp-hint 'measure-check))
            ,config.end-ins
            (o< ((lambda ,(list-fix config.in-vars)
                   ,config.in-measure)
                 . ,config.rest-ins)
                ,config.in-measure)))))

(define glmc-run-check-clause ((config glmc-config-p))
  :guard (not (glmc-clause-syntax-checks config))
  :returns (run-clause pseudo-term-listp :hyp :Guard
                       :hints(("Goal" :in-theory (enable length  pseudo-termp))))
  :prepwork ((local (defthm pseudo-term-listp-when-variable-listp
                      (implies (and (variable-listp x)
                                    (true-listp x))
                               (pseudo-term-listp x))
                      :hints(("Goal" :in-theory (enable pseudo-term-listp variable-listp  pseudo-termp)))))
             (local (defthm symbol-listp-when-variable-listp
                      (implies (and (variable-listp x)
                                    (true-listp x))
                               (symbol-listp x))
                      :hints(("Goal" :in-theory (enable variable-listp)))))
             (local (defthm pseudo-term-listp-append
                      (implies (and (pseudo-term-listp (list-fix x))
                                    (pseudo-term-listp y))
                               (pseudo-term-listp (append x y))))))
  (b* (((glmc-config+ config)))
    `((not (gl-cp-hint 'run-check))
      (not (if ,config.end-ins
               't
             ((lambda (,@(list-fix config.frame-in-vars) ,@(list-fix config.in-vars) ,config.st-var)
                (if (not ,config.in-hyp)
                    't
                  (if (not ,(acl2::bindinglist-to-lambda-nest-exec
                             config.bindings config.constr))
                      't
                    (if (not ,(acl2::bindinglist-to-lambda-nest-exec
                               config.bindings config.prop))
                        'nil
                      ((lambda (,@(list-fix config.in-vars) ,config.st-var)
                         (if (not ,config.st-hyp)
                             'nil
                           ,config.run))
                       ,@(list-fix config.in-vars)
                       ,(acl2::bindinglist-to-lambda-nest-exec 
                         config.bindings config.nextst))))))
              ,@config.frame-ins
              ,@config.rest-ins
              ,config.st-var)))
      ,config.run)))

(define glmc-clause-check-clause ((clause pseudo-term-listp)
                                          (config glmc-config-p))
  :guard (not (glmc-clause-syntax-checks config))
  :returns (clause-clause pseudo-term-listp :hyp :guard)
  :prepwork ((local (defthm pseudo-term-listp-when-variable-listp
                      (implies (and (variable-listp x)
                                    (true-listp x))
                               (pseudo-term-listp x))
                      :hints(("Goal" :in-theory (enable pseudo-term-listp variable-listp  pseudo-termp)))))
             (local (defthm symbol-listp-when-variable-listp
                      (implies (and (variable-listp x)
                                    (true-listp x))
                               (symbol-listp x))
                      :hints(("Goal" :in-theory (enable variable-listp)))))
             (local (defthm pseudo-term-listp-append
                      (implies (and (pseudo-term-listp (list-fix x))
                                    (pseudo-term-listp y))
                               (pseudo-term-listp (append x y))))))
  ;; (implies (implies (and config.st-hyp config.initstp) config.run) clause)
  (b* (((glmc-config config)))
    `((not (gl-cp-hint 'clause-check))
      (not (implies (if ((lambda (,@(list-fix config.frame-in-vars) ,@(list-fix config.in-vars) ,config.st-var)
                           ,(acl2::bindinglist-to-lambda-nest-exec config.bindings config.initstp))
                         ,@config.frame-ins
                         ,@config.rest-ins
                         ,config.st-var)
                        ,config.st-hyp
                      'nil)
                    ,config.run))
      . ,clause)))


(define glmc-state-hyp-is-inductive-clause ((config glmc-config-p))
  :returns (clauses pseudo-term-list-listp :hyp :guard)
  (b* (((glmc-config config))
       ((unless (eq config.st-hyp-method :inductive-clause))
        nil))
    `(((not (gl-cp-hint 'st-hyp-inductive))
       (not ,config.st-hyp)
       (not ,config.in-hyp)
       ((lambda (,config.st-var)
          ,config.st-hyp)
        ,(acl2::bindinglist-to-lambda-nest-exec config.bindings config.nextst))))))

(local (defthm pseudo-term-list-listp-of-append
         (implies (and (pseudo-term-list-listp a)
                       (pseudo-term-list-listp b))
                  (pseudo-term-list-listp (append a b)))
         :hints(("Goal" :in-theory (enable pseudo-term-list-listp)))))


(define glmc-clause-check ((clause pseudo-term-listp)
                                   (config glmc-config-p))
  :returns (clauses pseudo-term-list-listp :hyp :guard)
  :guard (not (glmc-clause-syntax-checks config))
  ;; The clause should look something like
  ;; ((not (in-hyp-list ins))
  ;;  (not (st-hyp st))
  ;;  (not (initstp st))
  ;;  (check-run st ins))
  ;; where check-run is something like
  ;;   (cond ((atom ins) t)
  ;;         ((not (constr st (car ins))) t)
  ;;         ((not (prop st (car ins))) nil)
  ;;         (t (check-run (nextst st (car ins)) (cdr ins))))
  ;; We need to show that what we'll prove through model checking implies this clause.
  ;; We'll first show that check-run is of the appropriate form
  ;; 
  (list* (glmc-clause-check-clause clause config)
         (glmc-run-check-clause config)
         (append (glmc-measure-clauses config)
                 (glmc-state-hyp-is-inductive-clause config))))

(define glmc-check-st-hyp-inductive ((config glmc-config-p)
                                     (fsm glmc-fsm-p)
                                     bvar-db
                                     state)
  :returns (mv er new-state)
  (b* (((glmc-fsm fsm))
       ((glmc-config+ config))
       ((unless (eq config.st-hyp-method :inductive-sat))
        ;; not our job to check here
        (mv nil state))
       (sat-problem (bfr-and (bfr-to-param-space fsm.hyp fsm.hyp)
                             (bfr-not fsm.st-hyp-next)))
       ((mv sat successp ctrex) (bfr-sat sat-problem))
       ((when (and sat successp))
        (b* (((mv er & state)
              (ec-call
               (glcp-gen/print-ctrexamples
                ctrex "ERROR"
                "Counterexample to state hyp inductiveness"
                (change-glcp-config config.glcp-config
                                    :top-level-term `(implies (if ,config.in-hyp ,config.st-hyp 'nil)
                                                              ((lambda (,config.st-var)
                                                                 ,config.st-hyp)
                                                               ,config.nextst))
                                    :param-bfr fsm.hyp)
                bvar-db state)))
             ((when er) (mv er state)))
          (mv (msg "Counterexamples for state hyp inductiveness found; aborting") state)))
       ((when successp)
        (mv nil state)))
    (mv (msg "SAT check for state hyp inductiveness failed; aborting") state)))

(define glmc-process-ctrex-one-env ((name stringp)
                                    (config glcp-config-p)
                                    env
                                    gobj-alist
                                    hyp-bfr
                                    bvar-db
                                    state)
  :prepwork ((local (in-theory (disable glcp-ctrex-complete-single-assign
                                        glcp-ctrex-bits-to-objs
                                        bindings-quote-if-needed
                                        glcp-ctrex-check-bvar-db
                                        glcp-pretty-print-bvar-db-violations))))
  (b* (((glcp-config config))
       (assign (ec-call (glcp-ctrex-complete-single-assign name env config.shape-spec-alist hyp-bfr)))
       ((glcp-obj-ctrex ctrex)
        (ec-call (glcp-ctrex-bits-to-objs
                  assign gobj-alist bvar-db config state)))
       ;; (bindings (ec-call (bindings-quote-if-needed ctrex.obj-alist)))
       ;; Check bvar-db for mismatches
       (unparam-env (bfr-unparam-env hyp-bfr (ec-call (car ctrex.genv))))
       (bvar-db-info (ec-call (glcp-ctrex-check-bvar-db
                               (next-bvar bvar-db) ctrex.genv unparam-env bvar-db state))))
    (and (hons-assoc-equal "FAIL" bvar-db-info)
         (prog2$ (cw "Some IF test terms were assigned inconsistent values:~%")
                 (glcp-pretty-print-bvar-db-violations bvar-db-info)))
    ctrex.obj-alist))



(define glmc-process-ctrex-inputs ((config glcp-config-p)
                                   envs
                                   gobj-alist
                                   hyp-bfr
                                   bvar-db
                                   state)
  (if (atom envs)
      nil
    (cons (glmc-process-ctrex-one-env "input" config (car envs) gobj-alist hyp-bfr bvar-db state)
          (glmc-process-ctrex-inputs config (cdr envs) gobj-alist hyp-bfr bvar-db state))))

(define bindings-list-quote-if-needed (x)
  (if (atom x)
      nil
    (cons (ec-call (bindings-quote-if-needed (car x)))
          (bindings-list-quote-if-needed (cdr x)))))


(define glmc-process-ctrex ((config glmc-config-p)
                            initst
                            ins
                            hyp-bfr
                            bvar-db
                            state)
  (b* (((glmc-config+ config) (glmc-config-update-param hyp-bfr config))
       (alist (gobj-alist-to-param-space
               (ec-call (shape-spec-to-gobj config.shape-spec-alist))
               hyp-bfr))
       (state-alist (list (hons-assoc-equal config.st-var alist)))
       (in-alist (acl2::hons-set-diff alist state-alist))
       (initial-state-objs (glmc-process-ctrex-one-env
                            "initial state" config.glcp-config initst state-alist hyp-bfr bvar-db state))
       (input-objs (glmc-process-ctrex-inputs
                    config.glcp-config ins in-alist hyp-bfr bvar-db state))
       (state (f-put-global ':glmc-ctrex-initial-state initial-state-objs state))
       (state (f-put-global ':glmc-ctrex-inputs input-objs state))
       (quoted-initsts (ec-call (bindings-quote-if-needed initial-state-objs)))
       (quoted-ins (bindings-list-quote-if-needed input-objs)))
    (mv (msg "Counterexample: Initial state: ~x0~%Inputs: ~x1~%" quoted-initsts quoted-ins)
        state)))


(define glmc-mcheck-full-property ((config glmc-config-p)
                                   (fsm glmc-fsm-p))
  (b* (((glmc-config+ config))
       ((glmc-fsm fsm)))
    (if (mbe :logic (or (eq config.st-hyp-method :inductive-sat)
                        (eq config.st-hyp-method :inductive-clause))
             :exec (not (eq config.st-hyp-method :mcheck)))
        fsm.prop
      (bfr-and fsm.prop fsm.st-hyp-next))))

(define glmc-fsm-perform-mcheck ((config glmc-config-p)
                                 (fsm glmc-fsm-p)
                                 bvar-db state)
  :returns (mv er new-state)
  
  (b* (((glmc-fsm fsm))
       (?config config)
       (?bvar-db bvar-db)
       ((mv result ?ctrex-initst ?ctrex-ins)
        (bfr-mcheck (glmc-mcheck-full-property config fsm)
                    (bfr-and fsm.fsm-constr fsm.bit-constr (bfr-to-param-space fsm.hyp fsm.hyp))
                    fsm.nextst
                    fsm.initst
                    fsm.var-bound))
       ((when (eq result :refuted))
        (b* (((mv ctrex-msg state)
              (glmc-process-ctrex config ctrex-initst ctrex-ins fsm.hyp bvar-db state)))
          (cw! "~@0" ctrex-msg)
          (mv "Counterexample!" state)))
       ((when (eq result :proved))
        (mv nil state)))
    (mv (msg "Model checking failed!") state))
  ///
  (std::defret glmc-fsm-perform-mcheck-er
    (iff er
         (not (equal :proved
                     (b* (((glmc-fsm fsm)))
                       (mv-nth 0 (bfr-mcheck (glmc-mcheck-full-property config fsm)
                                             (bfr-and fsm.fsm-constr fsm.bit-constr (bfr-to-param-space fsm.hyp fsm.hyp))
                                             fsm.nextst
                                             fsm.initst
                                             fsm.var-bound))))))))
  

(local (defthm pseudo-term-listp-when-variable-listp
         (implies (and (variable-listp x)
                       (true-listp x))
                  (pseudo-term-listp x))
         :hints(("Goal" :in-theory (enable pseudo-term-listp variable-listp pseudo-termp)))))

(local (defthm variable-listp-alist-keys-of-shape-spec-bindings
         (implies (shape-spec-bindingsp x)
                  (variable-listp (alist-keys x)))
         :hints(("Goal" :in-theory (enable shape-spec-bindingsp)))))
  
(define glcp-cov-clause ((hypo pseudo-termp) (bindings shape-spec-bindingsp))
  :returns (cov-clause pseudo-term-listp :hyp :guard)
  (list '(not (gl-cp-hint 'coverage))
        (dumb-negate-lit hypo)
        (shape-spec-list-oblig-term (shape-spec-bindings->sspecs bindings) (alist-keys bindings))))

(define glmc-cov-clause ((config glmc-config-p))
  :returns (cov-clause pseudo-term-listp :hyp :guard)
  (b* (((glmc-config+ config)))
    (glcp-cov-clause `(if ,config.st-hyp ,config.in-hyp 'nil) config.shape-spec-alist)))


  

(local (defthm state-of-preferred-defs-to-overrides
         (equal (mv-nth 2 (preferred-defs-to-overrides table state))
                state)
         :hints(("Goal" :in-theory (enable preferred-defs-to-overrides)))))

  
(define glmc-config-load-overrides ((config glmc-config-p)
                                    state)
  :returns (mv er (new-config
                   (implies (not er) (glmc-config-p new-config))
                   :hyp (glmc-config-p config))
               (new-state (equal new-state state)))
  (b* (((er overrides)
        (preferred-defs-to-overrides
         (table-alist 'preferred-defs (w state)) state))
       ((glmc-config+ config))
       (glcp-config (change-glcp-config config.glcp-config
                                        :overrides overrides
                                        :rewrite-rule-table (table-alist 'gl-rewrite-rules (w state))
                                        :branch-merge-rules (gl-branch-merge-rules (w state)))))
    (value (change-glmc-config config :glcp-config glcp-config))))


(defsection glmc-generic
  (set-verify-guards-eagerness 0)

  (make-event
   (sublis *glmc-generic-name-subst*
           *glmc-full-template*)))

