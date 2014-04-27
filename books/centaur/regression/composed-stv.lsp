; Copyright David Rager, 2014

; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.

(in-package "ACL2")

(include-book "common")
(include-book "make-event/eval-tests" :dir :system)

(defmodules *mods*
  (vl::make-vl-loadconfig
   :start-files (list "composed-stv.v")))

(defconst *double-reg*
  (vl::vl-module->esim
   (vl::vl-find-module "compose"
                       (vl::vl-design->mods
                        (vl::vl-translation->good *mods*)))))

(defstv double-reg-full-stv
  :mod *double-reg*
  :inputs '(("clk" 0 ~)
            ("d" d _))
  :outputs '(("qq" _ _ _ qq _)))

(defstv double-reg-decomp-stv
  :mod *double-reg*
  :inputs '(("clk" 0 ~)
            ("d" d _))
; We have to override the q in the third slot (as opposed to the second),
; because it is the third slot that is "clocked in" to the register.
  :overrides '(("q" _ _ q _))
  :outputs '(("qq" _ _ _ qq _)))


(def-gl-thm double-reg-decomp-is-full-with-exact-inputs
  :hyp (double-reg-decomp-stv-autohyps)
  :concl (b* ((comp1-outs (stv-run (double-reg-decomp-stv)
                                   `((d . ,d))))
              (q (cdr (assoc 'q comp1-outs)))
              (comp2-outs (stv-run (double-reg-decomp-stv)
                                   `((q . ,q))))
              (comp-qq (cdr (assoc 'qq comp2-outs)))
              (full-outs (stv-run (double-reg-full-stv)
                                  `((d . ,d))))
              (full-qq (cdr (assoc 'qq full-outs))))
           (equal comp-qq full-qq))
  :g-bindings (double-reg-decomp-stv-autobinds))
(in-theory (disable double-reg-decomp-is-full-with-exact-inputs))

(def-gl-thm double-reg-decomp-is-full-with-over-general-inputs
; This passes because we use the autoins for both composition components.
  :hyp (double-reg-decomp-stv-autohyps)
  :concl (b* ((comp1-outs (stv-run (double-reg-decomp-stv)
                                     (double-reg-decomp-stv-autoins)))
                (q (cdr (assoc 'q comp1-outs)))
                (comp2-outs (stv-run (double-reg-decomp-stv)
                                     (double-reg-decomp-stv-autoins)))
                (comp-qq (cdr (assoc 'qq comp2-outs)))
                (full-outs (stv-run (double-reg-full-stv)
                                    (double-reg-full-stv-autoins)))
                (full-qq (cdr (assoc 'qq full-outs))))
           (equal comp-qq full-qq))
  :g-bindings (double-reg-decomp-stv-autobinds))
(in-theory (disable double-reg-decomp-is-full-with-over-general-inputs))

(def-gl-thm double-reg-decomp-spec
  :hyp (double-reg-decomp-stv-autohyps)
  :concl (b* ((comp1-outs (stv-run (double-reg-decomp-stv)
                                   `((d . ,d))))
              (q (cdr (assoc 'q comp1-outs)))
              (comp2-outs (stv-run (double-reg-decomp-stv)
                                   `((q . ,q))))
              (comp-qq (cdr (assoc 'qq comp2-outs))))
           (equal comp-qq d))
  :g-bindings (double-reg-decomp-stv-autobinds))
(in-theory (disable double-reg-decomp-spec))

(def-gl-thm double-reg-full-spec
  :hyp (double-reg-decomp-stv-autohyps)
  :concl (b* ((full-outs (stv-run (double-reg-full-stv)
                                  `((d . ,d))))
              (full-qq (cdr (assoc 'qq full-outs))))
           (equal full-qq d))
  :g-bindings (double-reg-decomp-stv-autobinds))
(in-theory (disable double-reg-full-spec))

(include-book "centaur/esim/stv/stv-decomp-proofs" :dir :system)

(def-gl-thm double-reg-decomp-cutpoint-type-with-autohyps
  :hyp (double-reg-decomp-stv-autohyps)
  :concl (b* ((comp1-outs (stv-run (double-reg-decomp-stv)
                                   (double-reg-decomp-stv-autoins)))
              (q (cdr (assoc 'q comp1-outs))))
           (natp q))
  :g-bindings (gl::auto-bindings (:nat d 1)))
(in-theory (disable double-reg-decomp-cutpoint-type-with-autohyps))

(def-gl-thm double-reg-decomp-cutpoint-type-with-specific-hyps
; Note that this lemma also passes in D directly, instead of using autoins.
; This may be another source of discrepancy.
  :hyp (and (natp d)
            (< d (expt 2 1)))
  :concl (b* ((comp1-outs (stv-run (double-reg-decomp-stv)
                                   `((d . ,d))))
              (q (cdr (assoc 'q comp1-outs))))
           (natp q))
  :g-bindings (gl::auto-bindings (:nat d 1)))
(in-theory (disable double-reg-decomp-cutpoint-type-with-specific-hyps))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Scenario 0
;
; This one works.  It uses autohyps and autoins in both the theorem and in the
; hyps for the type lemma.
;
; Note that it doesn't matter whether we keep stv-decomp-4v-env-equiv-meta-rule
; disabled until stable-under-simplificationp.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm double-reg-decomp-is-full-via-rewriting-passes
  (implies (double-reg-decomp-stv-autohyps)
           (b* ((comp1-ins (double-reg-decomp-stv-autoins))
                (comp1-outs (stv-run (double-reg-decomp-stv)
                                     comp1-ins))
                (q (cdr (assoc 'q comp1-outs)))

                (Comp2-ins (double-reg-decomp-stv-autoins))
                (comp2-outs (stv-run (double-reg-decomp-stv)
                                     comp2-ins))
                (comp-qq (cdr (assoc 'qq comp2-outs)))

                (full-ins (double-reg-full-stv-autoins))
                (full-outs (stv-run (double-reg-full-stv)
                                    full-ins))
                (full-qq (cdr (assoc 'qq full-outs))))
             (equal comp-qq full-qq)))
     :hints (("goal"
              :use ((:instance double-reg-decomp-cutpoint-type-with-autohyps))
              :in-theory (set-difference-theories (stv-decomp-theory)
                                                  '(;stv-decomp-4v-env-equiv-meta-rule
                                                    ))
              )
             (and stable-under-simplificationp
                  '(:in-theory (union-theories (stv-decomp-theory)
                                               '(pairlis$-of-cons
                                                 pairlis$-when-atom))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Scenario 1
;
; In this scenario we change the second use of autoin's to only pass in the
; variables we need bound.  This results in an environment mismatch, which
; causes the following error:
;
;; HARD ACL2 ERROR in STV-DECOMP-PROCESS-ALIST-TERM:  Couldn't process:
;;  (REVAPPEND (PAIRLIS$ '(Q[0])
;;                      (IF (EQUAL (4V-TO-NAT #) 'X)
;;                          '(X)
;;                          (IF (IF # # #) (BOOL-TO-4V-LST #) '#)))
;;            'NIL)
;
; However, we are able to prevent this error from happenning by changing the
; rule that forces the obligation that causes stv-decomp-process-alist-term to
; need to process the environment as stated.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-fail
(defthm double-reg-decomp-is-full-via-rewriting-challenge-1
  (implies (double-reg-decomp-stv-autohyps)
           (b* ((comp1-outs (stv-run (double-reg-decomp-stv)
                                     (double-reg-decomp-stv-autoins)))
                (q (cdr (assoc 'q comp1-outs)))
                (comp2-outs (stv-run (double-reg-decomp-stv)
                                     `((q . ,q))))
                (comp-qq (cdr (assoc 'qq comp2-outs)))

                (full-outs (stv-run (double-reg-full-stv)
                                    `((d . ,d))))
                (full-qq (cdr (assoc 'qq full-outs))))
             (equal comp-qq full-qq)))
     :hints (("goal"
; Question: the type lemma must have exactly the hyps as the hyps given in this
; theorem.  Even if the current hyps imply the hyps of the type lemma, it
; doesn't work.
              :use ((:instance double-reg-decomp-cutpoint-type-with-autohyps))
;               :in-theory (stv-decomp-theory)
             :in-theory (set-difference-theories (stv-decomp-theory)
                                                 '(stv-decomp-4v-env-equiv-meta-rule))
             )
           (and stable-under-simplificationp
                '(:in-theory (union-theories (stv-decomp-theory)
                                             '(pairlis$-of-cons
                                               pairlis$-when-atom)))))))

(redef)
(skip-proofs
(defthmd 4v-sexpr-eval-list-of-composition
  (implies (and (bind-free (find-composition-in-alist alist) (sexpr-alist env))
                (equal sexpr-vars (4v-sexpr-vars-1pass-list
                                   (sexpr-rewrite-default-list sexprs)))
                (force (4v-env-equiv (4v-alist-extract sexpr-vars alist)
                                     (4v-alist-extract sexpr-vars
                                                       (append (4v-sexpr-eval-alist sexpr-alist env)
                                                               env)))))
           (equal (4v-sexpr-eval-list sexprs alist)
                  (4v-sexpr-eval-list
                   (4v-sexpr-restrict-list-fast sexprs sexpr-alist)
                   env)))))

(defthm double-reg-decomp-is-full-via-rewriting-challenge-1
  (implies (double-reg-decomp-stv-autohyps)
           (b* ((comp1-outs (stv-run (double-reg-decomp-stv)
                                     ;(double-reg-decomp-stv-autoins)
                                     `((d . ,d))
                                     ))
                (q (cdr (assoc 'q comp1-outs)))
                (comp2-outs (stv-run (double-reg-decomp-stv)
                                     `((q . ,q))))
                (comp-qq (cdr (assoc 'qq comp2-outs)))

                (full-outs (stv-run (double-reg-full-stv)
                                    `((d . ,d))))
                (full-qq (cdr (assoc 'qq full-outs))))
             (equal comp-qq full-qq)))
     :hints (("goal"
              :use ((:instance double-reg-decomp-cutpoint-type-with-specific-hyps))
              :in-theory (set-difference-theories (stv-decomp-theory)
                                                  '(stv-decomp-4v-env-equiv-meta-rule)))
           (and stable-under-simplificationp
                '(:in-theory (union-theories (stv-decomp-theory)
                                             '(pairlis$-of-cons
                                               pairlis$-when-atom))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Scenario 2
;
; If we use explicit ins for the first decomposition, we can use the stronger
; type lemma (because it has weaker hypotheses).
;
; This is good news and works as we [might] expect.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm double-reg-decomp-is-full-via-rewriting-challenge-2
  (implies (double-reg-decomp-stv-autohyps)
           (b* ((comp1-outs (stv-run (double-reg-decomp-stv)
                                     `((d . ,d))
                                     ))
                (q (cdr (assoc 'q comp1-outs)))
                (comp2-outs (stv-run (double-reg-decomp-stv)
                                     `((q . ,q))))
                (comp-qq (cdr (assoc 'qq comp2-outs)))

                (full-outs (stv-run (double-reg-full-stv)
                                    `((d . ,d))))
                (full-qq (cdr (assoc 'qq full-outs))))
             (equal comp-qq full-qq)))
     :hints (("goal"
              :use ((:instance double-reg-decomp-cutpoint-type-with-specific-hyps))
              :in-theory (set-difference-theories (stv-decomp-theory)
                                                  '(stv-decomp-4v-env-equiv-meta-rule)))
           (and stable-under-simplificationp
                '(:in-theory (union-theories (stv-decomp-theory)
                                             '(pairlis$-of-cons
                                               pairlis$-when-atom))))))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Scenario 3
;
; Disabling the meta rule until it's stable-under-simplification results in
; the a case split.  Can we make that case-split go away by allowing the meta
; rule to fire earlier?
;
; Currently we get this error:
;; HARD ACL2 ERROR in STV-DECOMP-PROCESS-ALIST-TERM:  Couldn't process:
;; (REVAPPEND (PAIRLIS$ '(D[0]) (BOOL-TO-4V-LST (INT-TO-V D '1))) 'NIL)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-fail
(defthm double-reg-decomp-is-full-via-rewriting-challenge-3
  (implies (double-reg-decomp-stv-autohyps)
           (b* ((comp1-outs (stv-run (double-reg-decomp-stv)
                                     `((d . ,d))
                                     ))
                (q (cdr (assoc 'q comp1-outs)))
                (comp2-outs (stv-run (double-reg-decomp-stv)
                                     `((q . ,q))))
                (comp-qq (cdr (assoc 'qq comp2-outs)))

                (full-outs (stv-run (double-reg-full-stv)
                                    `((d . ,d))))
                (full-qq (cdr (assoc 'qq full-outs))))
             (equal comp-qq full-qq)))
     :hints (("goal"
              :use ((:instance double-reg-decomp-cutpoint-type-with-specific-hyps))
              :in-theory (set-difference-theories (stv-decomp-theory)
                                                  '(;stv-decomp-4v-env-equiv-meta-rule
                                                    )))
           (and stable-under-simplificationp
                '(:in-theory (union-theories (stv-decomp-theory)
                                             '(pairlis$-of-cons
                                               pairlis$-when-atom))))))
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Scenario 4
;
; Using the autohyps type lemma causes the error generatd from a submission
; similar to Scenario 3 to be more verbose.  This tends to imply that an
; approach similar to Scenario 3 is more favorable.
;
;; HARD ACL2 ERROR in STV-DECOMP-PROCESS-ALIST-TERM:  Couldn't process:
;; (REVAPPEND (PAIRLIS$ '(D[0])
;;                      (BOOL-TO-4V-LST (INT-TO-V D '1)))
;;            (REVAPPEND (PAIRLIS$ '(Q[0])
;;                                 (BOOL-TO-4V-LST (INT-TO-V Q #)))
;;                       'NIL))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-fail
(defthm double-reg-decomp-is-full-via-rewriting-challenge-3
  (implies (double-reg-decomp-stv-autohyps)
           (b* ((comp1-outs (stv-run (double-reg-decomp-stv)
                                     (double-reg-decomp-stv-autoins)
                                     ))
                (q (cdr (assoc 'q comp1-outs)))
                (comp2-outs (stv-run (double-reg-decomp-stv)
                                     `((q . ,q))))
                (comp-qq (cdr (assoc 'qq comp2-outs)))

                (full-outs (stv-run (double-reg-full-stv)
                                    `((d . ,d))))
                (full-qq (cdr (assoc 'qq full-outs))))
             (equal comp-qq full-qq)))
     :hints (("goal"
              :use ((:instance double-reg-decomp-cutpoint-type-with-autohyps))
              :in-theory (set-difference-theories (stv-decomp-theory)
                                                  '(;stv-decomp-4v-env-equiv-meta-rule
                                                    )))
           (and stable-under-simplificationp
                '(:in-theory (union-theories (stv-decomp-theory)
                                             '(pairlis$-of-cons
                                               pairlis$-when-atom))))))
)
