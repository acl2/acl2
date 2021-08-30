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

(defconst *glmc-interp-hyp-template*
  '(define glmc-interp-hyp ((hyp-name stringp)
                            (hypo pseudo-termp)
                            (alist)
                            pathcond
                            (config glcp-config-p)
                            interp-st
                            bvar-db
                            state)
     :guard (and (acl2::interp-defs-alistp (glcp-config->overrides config))
                 (acl2::interp-defs-alistp (is-obligs interp-st)))
     :returns (mv hyp-bfr er new-pathcond new-interp-st new-bvar-db new-state)
     (b* (((glcp-config config))
          ((mv hyp-bfr er pathcond interp-st bvar-db state)
           (time$ (interp-test hypo alist pathcond config.hyp-clk config interp-st bvar-db state)
                  :msg "; ~s0: ~st seconds, ~sa bytes.~%"
                  :args (list hyp-name)))
          ((when er)
           (mv nil
               (msg "Error interpreting ~s0 hyp: ~@1" hyp-name er)
               pathcond interp-st bvar-db state))
          ((mv er ?unsat) (glcp-vacuity-check hyp-bfr config))
          ((when er)
           (mv nil
               (msg "Vacuity check for ~s0 hyp failed: ~@1" hyp-name er)
               pathcond interp-st bvar-db state)))
       (mv hyp-bfr nil pathcond interp-st bvar-db state))))

(defconst *glmc-interp-hyp-tuples-template*
  '(define glmc-interp-hyp-tuples ((tuples hyp-tuplelist-p)
                                   pathcond
                                   (config glcp-config-p)
                                   interp-st
                                   bvar-db
                                   state)
     :guard (and (acl2::interp-defs-alistp (glcp-config->overrides config))
                 (acl2::interp-defs-alistp (is-obligs interp-st)))
     :returns (mv bfr-list er new-pathcond new-interp-st new-bvar-db new-state)
     (b* (((when (atom tuples))
           (b* ((pathcond (lbfr-hyp-fix pathcond)))
             (mv nil nil pathcond interp-st bvar-db state)))
          ((hyp-tuple tuple) (car tuples))
          ((mv bfr er pathcond interp-st bvar-db state)
           (glmc-interp-hyp tuple.name tuple.term tuple.alist pathcond config interp-st bvar-db state))
          ((when er)
           (mv nil er pathcond interp-st bvar-db state))
          ((mv rest er pathcond interp-st bvar-db state)
           (glmc-interp-hyp-tuples (cdr tuples) pathcond config interp-st bvar-db state)))
       (mv (and (not er) (cons bfr rest))
           er pathcond interp-st bvar-db state))))


(defconst *glmc-interp-hyps-template*
  '(define glmc-interp-hyps ((config glmc-config-p)
                             ;; pathcond
                             interp-st
                             bvar-db
                             state)
     :guard (b* (((glmc-config+ config)))
              (and (acl2::interp-defs-alistp config.overrides)
                   (acl2::interp-defs-alistp (is-obligs interp-st))
                   (non-exec (equal interp-st (create-interp-st)))))
     :returns (mv st-hyp-bfr in-hyp-bfr er new-interp-st new-bvar-db new-state)
     :ret-patbinder t
     (b* (((glmc-config+ config) (glmc-config-update-param t config))
          ((acl2::local-stobjs pathcond)
           (mv st-hyp-bfr in-hyp-bfr er pathcond interp-st bvar-db state))
          
          (next-bvar (shape-spec-max-bvar-list (shape-spec-bindings->sspecs config.shape-spec-alist)))
          (bvar-db (init-bvar-db next-bvar bvar-db))

          ((mv er interp-st) (init-interp-st interp-st config state))
          ((when er)
           (mv nil nil er pathcond interp-st bvar-db state))

          (pathcond (bfr-hyp-init pathcond))

          (alist (shape-specs-to-interp-al config.shape-spec-alist))

          (st-alist (alist-extract (list config.st-var) alist))
          ;; (in-alist (acl2::fal-extract (remove-equal config.st-var (alist-keys alist)) alist))

          (tuples (list (make-hyp-tuple :name "state" :term config.st-hyp :alist st-alist)
                        (make-hyp-tuple :name "input" :term config.in-hyp :alist alist)))

          ((mv (acl2::nths st-hyp-bfr in-hyp-bfr) er pathcond interp-st bvar-db state)
           (glmc-interp-hyp-tuples tuples pathcond config.glcp-config interp-st bvar-db state))
          ((when er)
           (mv nil nil er pathcond interp-st bvar-db state)))

       (mv st-hyp-bfr in-hyp-bfr nil pathcond interp-st bvar-db state))))

(defconst *glmc-ev-bindinglist-template*
  '(define glmc-ev-bindinglist ((x acl2::bindinglist-p) (a alistp))
     ;; Returns the alist for evaluating a body term nested inside all the
     ;; bindings.
     :returns (final-alist alistp)
     (b* (((when (atom x)) (acl2::alist-fix a))
          ((cons formals actuals) (car x))
          (new-bindings (pairlis$ formals (geval-ev-lst actuals a))))
       (glmc-ev-bindinglist (cdr x) (append new-bindings a)))))

(defconst *glmc-interp-bindinglist-template*
  '(define glmc-interp-bindinglist ((x acl2::bindinglist-p)
                                    (alist)
                                    (pathcond)
                                    (clk natp)
                                    (config glcp-config-p)
                                    interp-st bvar-db state)
     :guard (and (acl2::interp-defs-alistp (is-obligs interp-st))
                 (acl2::interp-defs-alistp (glcp-config->overrides config)))
     :returns (mv new-alist err new-pathcond new-interp-st new-bvar-db new-state)
     (b* (((when (atom x))
           (b* ((pathcond (lbfr-hyp-fix pathcond)))
             (glcp-value alist)))
          ((cons formals actuals) (car x))
          ((glcp-er actuals) (interp-list actuals alist pathcond clk config interp-st bvar-db state))
          (new-alist (append (pairlis$ formals actuals) alist)))
       (glmc-interp-bindinglist (cdr x) new-alist pathcond clk config interp-st bvar-db state))))


(defconst *glmc-interp-nonhyps-template*
  '(define glmc-interp-nonhyps ((config glmc-config-p)
                                hyp-bfr
                                interp-st
                                bvar-db
                                hyp-bvar-db
                                state)
     :guard (b* (((glmc-config+ config)))
              (and (acl2::interp-defs-alistp config.overrides)
                   (acl2::interp-defs-alistp (is-obligs interp-st))))
     :returns (mv initst-bfr constr-bfr prop-bfr st-hyp-next-bfr nextst er new-interp-st new-bvar-db new-state)
     :ret-patbinder t
     (b* (((glmc-config+ config) (glmc-config-update-param hyp-bfr config))
          ((acl2::local-stobjs pathcond)
           (mv initst-bfr constr-bfr prop-bfr st-hyp-next-bfr nextst-obj er pathcond interp-st bvar-db state))

          ((mv contra pathcond interp-st bvar-db)
           (glcp-prepare-param-inputs hyp-bfr pathcond interp-st hyp-bvar-db bvar-db))

          ((when contra)
           (mv nil nil nil nil nil
               "Contradiction in constraints or hypothesis"
               pathcond interp-st bvar-db state))

          (alist1 (gobj-alist-to-param-space (shape-specs-to-interp-al config.shape-spec-alist) hyp-bfr))
          ((mv alist er pathcond interp-st bvar-db state)
           (time$ (glmc-interp-bindinglist config.bindings alist1 pathcond config.concl-clk config.glcp-config interp-st bvar-db state)
                  :msg "; ~s0: ~st seconds, ~sa bytes.~%"
                  :args '(glmc-interp-bindinglist)))
          ((when er)
           (mv nil nil nil nil nil er pathcond interp-st bvar-db state))

          ((mv nextst er pathcond interp-st bvar-db state)
           (time$ (interp-term-equivs config.nextst alist nil pathcond config.concl-clk config.glcp-config interp-st bvar-db state)
                  :msg "; glmc interp nextst: ~st seconds, ~sa bytes.~%"))
          ((when er)
           (mv nil nil nil nil nil er pathcond interp-st bvar-db state))
          
          ;; (st-alist (alist-extract (list config.st-var) alist))
          (nextst-alist (list (cons config.st-var nextst)))

          (tuples (list (make-hyp-tuple :name "initst" :term config.initstp :alist alist)
                        (make-hyp-tuple :name "constraint" :term config.constr :alist alist)
                        (make-hyp-tuple :name "prop" :term config.prop :alist alist)
                        (make-hyp-tuple :name "st-hyp-next" :term config.st-hyp :alist nextst-alist)))
          
          ((mv (acl2::nths initst-bfr constr-bfr prop-bfr st-hyp-next-bfr) er pathcond interp-st bvar-db state)
           (glmc-interp-hyp-tuples tuples pathcond config.glcp-config interp-st bvar-db state))
          ((when er)
           (mv nil nil nil nil nil er pathcond interp-st bvar-db state)))

       (mv initst-bfr constr-bfr prop-bfr st-hyp-next-bfr nextst nil pathcond interp-st bvar-db state))))


(defconst *glmc-mcheck-main-interps-template*
  '(define glmc-mcheck-main-interps ((config glmc-config-p)
                                     interp-st
                                     bvar-db
                                     state)
     :guard (and (acl2::interp-defs-alistp (glcp-config->overrides (glmc-config->glcp-config config)))
                 (non-exec (equal interp-st (create-interp-st))))
     :returns (mv nextst prop-bfr constr-bfr initst-bfr st-hyp-bfr hyp-bfr st-hyp-next-bfr
                  (hyp-max-bvar (implies (not er) (natp hyp-max-bvar)) :rule-classes :type-prescription)
                  er new-interp-st new-bvar-db new-state)
     (b* (((acl2::local-stobjs hyp-bvar-db)
           (mv nextst prop-bfr constraint-bfr initstp-bfr st-hyp-bfr hyp-bfr st-hyp-next-bfr hyp-max-bvar er interp-st bvar-db hyp-bvar-db state))
          ((glmc-config+ config))
          (bvar-db (init-bvar-db 0 bvar-db)) ;; nonsense

          ((mv st-hyp-bfr in-hyp-bfr er interp-st hyp-bvar-db state)
           (time$ (glmc-interp-hyps config interp-st hyp-bvar-db state)
                  :msg "; ~s0: ~st seconds, ~sa bytes.~%"
                  :args '(glmc-interp-hyps)))
          ((when er)
           (mv nil nil nil nil nil nil nil nil er interp-st bvar-db hyp-bvar-db state))

          (hyp-bfr (bfr-and in-hyp-bfr st-hyp-bfr))

          (hyp-max-bvar (next-bvar hyp-bvar-db))

          ((mv initst-bfr constr-bfr prop-bfr st-hyp-next-bfr nextst er interp-st bvar-db state)
           (time$ (glmc-interp-nonhyps config hyp-bfr interp-st bvar-db hyp-bvar-db state)
                  :msg "; ~s0: ~st seconds, ~sa bytes.~%"
                  :args '(glmc-interp-nonhyps)))
          ((when er)
           (mv nil nil nil nil nil nil nil nil er interp-st bvar-db hyp-bvar-db state)))

       (mv nextst prop-bfr constr-bfr initst-bfr st-hyp-bfr hyp-bfr st-hyp-next-bfr hyp-max-bvar nil interp-st bvar-db hyp-bvar-db state))))



;; x is the bindings of 
(defconst *glmc-interp-bvar-alist-template*
  '(define glmc-interp-bvar-alist ((x pseudo-term-alistp)
                                   (alist)
                                   pathcond
                                   (config glcp-config-p)
                                   interp-st
                                   bvar-db
                                   state)

     :guard (b* (((glcp-config config)))
              (and (acl2::interp-defs-alistp config.overrides)
                   (acl2::interp-defs-alistp (is-obligs interp-st))
                   (bfr-varnamelist-p (alist-keys x))))
     :returns (mv (updates bfr-updates-p)
                  er 
                  new-pathcond
                  new-interp-st
                  new-bvar-db
                  new-state)
     :guard-hints (("goal" :in-theory (enable pseudo-term-alistp)))
     (b* (((when (atom x))
           (b* ((pathcond (lbfr-hyp-fix pathcond)))
             (mv nil nil pathcond interp-st bvar-db state)))
          ((unless (mbt (and (consp (car x))
                             (bfr-varname-p (caar x)))))
           (glmc-interp-bvar-alist
            (cdr x) alist pathcond config interp-st bvar-db state))
          ((cons var term) (car x))
          ((mv bfr er pathcond interp-st bvar-db state)
           (interp-test term alist pathcond (glcp-config->concl-clk config) config interp-st bvar-db state))
          ((when er) (mv nil er pathcond interp-st bvar-db state))
          ((mv rest er pathcond interp-st bvar-db state)
           (glmc-interp-bvar-alist (cdr x) alist pathcond config interp-st bvar-db state)))
       (mv (and (not er) (cons (cons var bfr) rest))
           er pathcond interp-st bvar-db state))))


(defconst *glmc-interp-gvar-alist-template*
  '(define glmc-interp-gvar-alist ((x pseudo-term-alistp)
                                   (alist)
                                   pathcond
                                   (config glcp-config-p)
                                   interp-st
                                   bvar-db
                                   state)

     :guard (b* (((glcp-config config)))
              (and (acl2::interp-defs-alistp config.overrides)
                   (acl2::interp-defs-alistp (is-obligs interp-st))
                   (variable-listp (alist-keys x))))
     :returns (mv (updates gobj-alistp :hyp (variable-listp (alist-keys x)))
                  er 
                  new-pathcond
                  new-interp-st
                  new-bvar-db
                  new-state)
     :guard-hints (("goal" :in-theory (enable pseudo-term-alistp)))
     (b* (((when (atom x))
           (b* ((pathcond (lbfr-hyp-fix pathcond)))
             (mv nil nil pathcond interp-st bvar-db state)))
          ((unless (mbt (and (consp (car x)))))
           (glmc-interp-gvar-alist
            (cdr x) alist pathcond config interp-st bvar-db state))
          ((cons var term) (car x))
          ((mv bfr er pathcond interp-st bvar-db state)
           (interp-term-equivs
            term alist nil pathcond (glcp-config->concl-clk config) config interp-st bvar-db state))
          ((when er) (mv nil er pathcond interp-st bvar-db state))
          ((mv rest er pathcond interp-st bvar-db state)
           (glmc-interp-gvar-alist (cdr x) alist pathcond config interp-st bvar-db state)))
       (mv (and (not er) (cons (cons var bfr) rest))
           er pathcond interp-st bvar-db state))))


(defconst *glmc-next-state-template*
  '(define glmc-next-state ((nextst-obj)
                            hyp-bfr
                            (config glmc-config-p)
                            interp-st
                            bvar-db
                            state)
     :guard (b* (((glmc-config+ config)))
              (and (acl2::interp-defs-alistp config.overrides)
                   (acl2::interp-defs-alistp (is-obligs interp-st))
                   (hons-assoc-equal config.st-var config.shape-spec-alist)))
     :returns (mv (updates bfr-updates-p) er new-interp-st new-bvar-db new-state)

     :prepwork ((local (defthm shape-specp-of-lookup-in-shape-spec-bindings
                         (implies (and (shape-spec-bindingsp x)
                                       (hons-assoc-equal k x))
                                  (shape-specp (cadr (hons-assoc-equal k x))))
                         :hints(("Goal" :in-theory (enable hons-assoc-equal)))))
                (local (defthm consp-of-lookup-in-shape-spec-bindings
                         (implies (and (shape-spec-bindingsp x)
                                       (hons-assoc-equal k x))
                                  (consp (cdr (hons-assoc-equal k x))))
                         :hints(("Goal" :in-theory (enable hons-assoc-equal)))))

                (local (defthm bfr-varnamelist-p-when-nat-listp+
                         (implies (nat-listp x)
                                  (bfr-varnamelist-p x))
                         :hints(("Goal" :in-theory (enable bfr-varnamelist-p)))))
                (local (defthm pseudo-termp-when-variablep
                         (implies (variablep x)
                                  (pseudo-termp x))
                         :hints(("Goal" :in-theory (enable pseudo-termp))))))
     
     (b* ((config (glmc-config-update-param hyp-bfr config))
          ((glmc-config+ config))
          ((acl2::local-stobjs pathcond)
           (mv updates er pathcond interp-st bvar-db state))

          (next-bvar (next-bvar bvar-db))

          ((mv ?contra pathcond) (glcp-bfr-to-pathcond hyp-bfr pathcond))
          
          (st-shape-spec (cadr (hons-assoc-equal config.st-var config.shape-spec-alist)))
          ((mv bvar-bindings gvar-bindings) (shape-spec-invert st-shape-spec config.st-var))

          (interp-st (update-is-add-bvars-allowed nil interp-st))

          (st-alist `((,config.st-var . ,nextst-obj)))

          (- (cw "; glmc-next-state: ~x0 shape-spec Boolean variables to be ~
                  extracted from the next-state object~%"
                 (len bvar-bindings)))

          ((mv updates1 er pathcond interp-st bvar-db state)
           (time$ (glmc-interp-bvar-alist
                   bvar-bindings st-alist
                   pathcond config.glcp-config interp-st bvar-db state)
                  :msg "; ~s0: ~st seconds, ~sa bytes.~%"
                  :args '(glmc-interp-bvar-alist)))
          ((when er)
           (mv nil
               (msg "Error extracting the shape spec bits from the next state object: ~@0"
                    (if (or (stringp er) (consp er)) er (msg "~x0" er)))
               pathcond interp-st bvar-db state))

          (- (cw "; glmc-next-state: ~x0 shape-spec object variables to be ~
                  extracted from the next-state object~%"
                 (len gvar-bindings)))

          ((mv gvar-updates er pathcond interp-st bvar-db state)
           (time$ (glmc-interp-gvar-alist
                   gvar-bindings st-alist pathcond config.glcp-config interp-st bvar-db state)
                  :msg "; ~s0: ~st seconds, ~sa bytes.~%"
                  :args '(glmc-interp-gvar-alist)))
          ((when er)
           (mv nil
               (msg "Error extracting the shape spec variables from the next state object: ~@0"
                    (if (or (stringp er) (consp er)) er (msg "~x0" er)))
               pathcond interp-st bvar-db state))

          (bvar-db-alist
           (time$ (glmc-bvar-db-to-state-updates (base-bvar bvar-db) (alist-keys gvar-updates) bvar-db)
                  :msg "; ~s0: ~st seconds, ~sa bytes.~%"
                  :args '(glmc-bvar-db-to-state-updates)))

          (- (cw "; glmc-next-state: ~x0 bvar-db variables to be extracted from the next-state object~%"
                 (len bvar-db-alist)))

          ((mv updates2 er pathcond interp-st bvar-db state)
           (time$ (glmc-interp-bvar-alist
                   bvar-db-alist gvar-updates pathcond config.glcp-config interp-st bvar-db state)
                  :msg "; ~s0: ~st seconds, ~sa bytes.~%"
                  :args '(glmc-interp-bvar-alist)))
          ((when er)
           (mv nil
               (msg "Error extracting bvar-db variable updates: ~@0"
                    (if (or (stringp er) (consp er)) er (msg "~x0" er)))
               pathcond interp-st bvar-db state))

          ((unless (equal (next-bvar bvar-db) next-bvar))
           (mv nil
               "Programming error in glmc-next-state: bvar-db was unexpectedly updated"
               pathcond interp-st bvar-db state)))

       (mv (acl2::append-without-guard updates1 updates2)
           nil pathcond interp-st bvar-db state))))


(defconst *glmc-mcheck-to-fsm-template*
  '(define glmc-mcheck-to-fsm ((config glmc-config-p)
                               bvar-db
                               interp-st
                               state)
     :returns (mv fsm
                  er new-bvar-db new-interp-st new-state)
     :guard (b* (((glmc-config+ config)))
              (acl2::interp-defs-alistp config.overrides))

     (b* (((glmc-config+ config))
          (interp-st (reset-interp-st interp-st))

          (bvar-db (init-bvar-db 0 bvar-db))
          (er (glmc-syntax-checks config))
          ((when er) (mv nil er bvar-db interp-st state))

          ((mv nextst-obj prop-bfr fsm-constr-bfr initst-bfr st-hyp-bfr hyp-bfr st-hyp-next-bfr ?hyp-max-bvar
               er interp-st bvar-db state)
           (b* ((config (b* (((glmc-config+ config1) config))
                          (glmc-config-update-rewrites
                           config config1.main-rewrite-rules config1.main-branch-merge-rules))))
             (time$ (glmc-mcheck-main-interps config interp-st bvar-db state)
                    :msg "; ~s0: ~st seconds, ~sa bytes.~%"
                    :args '(glmc-mcheck-main-interps))))
          (interp-st (is-prof-report interp-st))
          (interp-st (is-prof-reset interp-st))
          ((when er) (mv nil er bvar-db interp-st state))

          ((mv nextst-bfrs er interp-st bvar-db state)
           (b* ((config (b* (((glmc-config+ config1) config))
                          (glmc-config-update-rewrites
                           config config1.extract-rewrite-rules config1.extract-branch-merge-rules))))
             (time$ (glmc-next-state nextst-obj hyp-bfr config interp-st bvar-db state)
                    :msg "; ~s0: ~st seconds, ~sa bytes.~%"
                    :args '(glmc-next-state))))
          (interp-st (is-prof-report interp-st))
          ((when er) (mv nil er bvar-db interp-st state))

          (bit-constr-bfr (bfr-constr->bfr (is-constraint interp-st))))

       (mv (make-glmc-fsm :nextst nextst-bfrs
                          :prop prop-bfr
                          :fsm-constr fsm-constr-bfr
                          :bit-constr bit-constr-bfr
                          :initst initst-bfr
                          :st-hyp st-hyp-bfr
                          :st-hyp-next st-hyp-next-bfr
                          :hyp hyp-bfr
                          :hyp-var-bound hyp-max-bvar
                          :interp-clauses (acl2::interp-defs-alist-clauses (is-obligs interp-st))
                          :var-bound (next-bvar bvar-db))
           nil bvar-db interp-st state))))


(defconst *glmc-template*
  '(define glmc ((clause pseudo-term-listp)
                 config
                 interp-st
                 state)
     :returns (mv er
                  new-clauses
                  new-interp-st
                  new-state)
     (b* (((unless (glmc-config-p config))
           (mv "Bad GLMC config" nil interp-st state))
          ((mv er config state) (glmc-config-load-overrides config state))
          ((when er) (mv er nil interp-st state))
          ((glmc-config+ config))
          ((unless (acl2::interp-defs-alistp config.overrides))
           (mv "Bad overrides in GLMC config" nil interp-st state))
          (er (glmc-clause-syntax-checks config))
          ((when er)
           (mv er nil interp-st state))
          ((unless (bfr-mode))
           (mv "Glmc only works in AIG mode" nil interp-st state))
          ((acl2::local-stobjs bvar-db)
           (mv er clauses bvar-db interp-st state))
          ((mv fsm er bvar-db interp-st state)
           (time$ (glmc-mcheck-to-fsm config bvar-db interp-st state)
                  :msg "; ~s0: ~st seconds, ~sa bytes.~%"
                  :args '(glmc-mcheck-to-fsm)))
          ((when er)
           (mv er nil bvar-db interp-st state))

          ((mv er state) (glmc-check-st-hyp-inductive config fsm bvar-db state))
          ((when er)
           (mv er nil bvar-db interp-st state))

          ((mv er state) (glmc-fsm-perform-mcheck config fsm bvar-db state))
          ((when er)
           (mv er nil bvar-db interp-st state))

          (clause-clauses (glmc-clause-check clause config))
          (cov-clause (glmc-cov-clause config)))
       (mv nil
           (cons cov-clause
                 (append clause-clauses
                         (glmc-fsm->interp-clauses fsm)))
           bvar-db interp-st state))))


(defconst *glmc-fnnames*
  '(glmc-interp-hyp
    glmc-interp-hyp-tuples
    glmc-interp-hyps
    glmc-ev-bindinglist
    glmc-interp-bindinglist
    glmc-interp-nonhyps
    glmc-mcheck-main-interps
    glmc-interp-bvar-alist
    glmc-interp-gvar-alist
    glmc-next-state
    glmc-mcheck-to-fsm
    glmc))

(defconst *glmc-full-template*
  `(progn ,*glmc-interp-hyp-template*
          ,*glmc-interp-hyp-tuples-template*
          ,*glmc-interp-hyps-template*
          ,*glmc-ev-bindinglist-template*
          ,*glmc-interp-bindinglist-template*
          ,*glmc-interp-nonhyps-template*
          ,*glmc-mcheck-main-interps-template*
          ,*glmc-interp-bvar-alist-template*
          ,*glmc-interp-gvar-alist-template*
          ,*glmc-next-state-template*
          ,*glmc-mcheck-to-fsm-template*
          ,*glmc-template*))
