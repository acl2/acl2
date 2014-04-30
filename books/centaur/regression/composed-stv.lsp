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
(include-book "misc/eval" :dir :system)

(defmodules *mods*
  (vl::make-vl-loadconfig
   :start-files (list "composed-stv.v")))

(defconst *double-reg*
  (vl::vl-module->esim
   (vl::vl-find-module "compose"
                       (vl::vl-design->mods
                        (vl::vl-translation->good *mods*)))))

(defconst *triple-reg*
  (vl::vl-module->esim
   (vl::vl-find-module "compose_three"
                       (vl::vl-design->mods
                        (vl::vl-translation->good *mods*)))))

(defconst *quadruple-reg*
  (vl::vl-module->esim
   (vl::vl-find-module "compose_four"
                       (vl::vl-design->mods
                        (vl::vl-translation->good *mods*)))))

(defstv double-reg-full-stv
  :mod *double-reg*
  :inputs '(("clk" 0 ~)
            ("d" d _))
; It doesn't matter whether we observe qq in the 4th or 5th slot.  Though, it's
; best to make it the same slot as in the decomp-stv.
  :outputs '(("qq" _ _ _ _ qq _)))

(defstv double-reg-decomp-stv
  :mod *double-reg*
  :inputs '(("clk" 0 ~)
            ("d" d _))
; We have to override the q in the third slot (as opposed to the second),
; because it is the third slot that is "clocked in" to the register.
  :overrides '(("q" _ _ q _))
  :outputs '(("qq" _ _ _ _ qq _)))

(defstv triple-reg-full-stv
  :mod *triple-reg*
  :inputs '(("clk" 0 ~)
            ("d" d _))
  :outputs '(("qqq" _ _ _ _ _ _ qqq _)))

(defstv triple-reg-decomp-stv
  :mod *triple-reg*
  :inputs '(("clk" 0 ~)
            ("d" d _))
  :overrides '(("q" _ _ q _)
               ("qq" _ _ _ _ qq _))
  :outputs '(("qqq" _ _ _ _ _ _ qqq _)))


(defstv quadruple-reg-full-stv
  :mod *quadruple-reg*
  :inputs '(("clk" 0 ~)
            ("d" d _))
  :outputs '(("qqqq" _ _ _ _ _ _ _ _ qq _)))

(defstv quadruple-reg-decomp-stv
  :mod *quadruple-reg*
  :inputs '(("clk" 0 ~)
            ("d" d _))
  :overrides '(("q" _ _ q _)
               ("qq" _ _ _ _ qq _)
               ("qqq" _ _ _ _ _ _ qqq _))
  :outputs '(("qqqq" _ _ _ _ _ _ _ _ qqqq _)))




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

(def-gl-thm double-reg-decomp-is-full-with-autoins
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
(in-theory (disable double-reg-decomp-is-full-with-autoins))

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

(include-book "centaur/esim/stv/stv-decomp-proofs-even-better" :dir :system)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Setup typing lemmas
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

(def-gl-thm triple-reg-decomp-cutpoint-type-with-autohyps
  :hyp (force (triple-reg-decomp-stv-autohyps))
  :concl (b* ((comp1-outs (stv-run (triple-reg-decomp-stv)
                                   (triple-reg-decomp-stv-autoins)))
              (q (cdr (assoc 'q comp1-outs)))

              (comp2-outs (stv-run (triple-reg-decomp-stv)
                                   (triple-reg-decomp-stv-autoins)))
              (qq (cdr (assoc 'qq comp2-outs))))
           (and (natp q)
                (natp qq)))
  :g-bindings (gl::auto-bindings (:nat d 1)))
(in-theory (disable triple-reg-decomp-cutpoint-type-with-autohyps))

(def-gl-thm triple-reg-decomp-cutpoint-type-with-specific-hyps
  :hyp (and (force (natp d))
            (force (< d (expt 2 1))))
  :concl (b* ((comp1-outs (stv-run (triple-reg-decomp-stv)
                                   `((d . ,d))))
              (q (cdr (assoc 'q comp1-outs)))
              (comp2-outs (stv-run (triple-reg-decomp-stv)
                                   `((q . ,q))))
              (qq (cdr (assoc 'qq comp2-outs))))
           (and (natp q)
                (natp qq)))
  :g-bindings (gl::auto-bindings (:nat d 1)))
(in-theory (disable triple-reg-decomp-cutpoint-type-with-specific-hyps))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; [DOUBLE REG] Scenario 0
;
; This one works.  It uses autohyps and autoins in both the theorem and in the
; hyps for the type lemma.
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd double-reg-decomp-is-full-via-rewriting-passes
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
              :in-theory (stv-decomp-theory))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; [DOUBLE REG] Scenario 1
;
; In this scenario we change the second use of autoin's to only pass in the
; variables we need bound.  This used to result in an environment mismatch but
; no longer does so since we improved 4v-sexpr-eval-list-of-composition.
;
; For the sake of future debugging, the error we used to receive looked like:
;
; HARD ACL2 ERROR in STV-DECOMP-4V-ENV-EQUIV-META:  Not equivalent
;
; Where a-al is:
;; ((Q[0] 4V-SEXPR-EVAL '(NOT D[0])
;;        (CONS (CONS 'D[0] (BOOL-TO-4V (LOGBITP '0 D)))
;;              (CONS (CONS 'Q[0] (BOOL-TO-4V (LOGBITP '0 Q)))
;;                    'NIL))))
; and b-al is:
;; ((Q[0] 4V-SEXPR-EVAL '(NOT D[0])
;;        (CONS (CONS 'D[0] (BOOL-TO-4V (LOGBITP '0 D)))
;;              (CONS (CONS 'Q[0] (BOOL-TO-4V (LOGBITP '0 Q)))
;;                    'NIL)))
;;  (D[0] BOOL-TO-4V (LOGBITP '0 D))
;;  (Q[0] BOOL-TO-4V (LOGBITP '0 Q)))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd double-reg-decomp-is-full-via-rewriting-challenge-1
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
              :in-theory (stv-decomp-theory))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; [DOUBLE REG] Scenario 2
;
; If we use explicit ins for the first decomposition, we can use the stronger
; type lemma (because it has weaker hypotheses).
;
; This is good news and works as we [might] expect.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd double-reg-decomp-is-full-via-rewriting-challenge-2
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
; [DOUBLE REG] Scenario 3
;
; We used to have a problem with revappend of pairlist$. But that is now
; solved.  We include the obsolete error for future reference.
;
;; HARD ACL2 ERROR in STV-DECOMP-PROCESS-ALIST-TERM:  Couldn't process:
;; (REVAPPEND (PAIRLIS$ '(D[0]) (BOOL-TO-4V-LST (INT-TO-V D '1))) 'NIL)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd double-reg-decomp-is-full-via-rewriting-challenge-3
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
              :in-theory (stv-decomp-theory))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; [DOUBLE REG] Scenario 4
;
; Using the autohyps type lemma caused the error generatd from a submission
; similar to Scenario 3 to be more verbose. We include it here for future
; reference.  This may be a clue as to how using autohyps vs specific hyps in
; the typing lemma can affect the proof.
;
;; HARD ACL2 ERROR in STV-DECOMP-PROCESS-ALIST-TERM:  Couldn't process:
;; (REVAPPEND (PAIRLIS$ '(D[0])
;;                      (BOOL-TO-4V-LST (INT-TO-V D '1)))
;;            (REVAPPEND (PAIRLIS$ '(Q[0])
;;                                 (BOOL-TO-4V-LST (INT-TO-V Q #)))
;;                       'NIL))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defthmd double-reg-decomp-is-full-via-rewriting-challenge-4
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
              :use ((:instance double-reg-decomp-cutpoint-type-with-autohyps))
              :in-theory (stv-decomp-theory))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; [TRIPLE REG] Scenario 0
;
; This one doesn't work.  It uses autohyps and autoins in both the theorem and
; in the hyps for the type lemma.  It errors out in the way that we expect when
; we're missing an applicable type lemma
;
;; HARD ACL2 ERROR in STV-DECOMP-4V-ENV-EQUIV-META:  Not equivalent
;; See :doc topic symbolic-test-vector-composition.
;; A-alist:
;; ((QQ[0] CAR
;;         (IF (EQUAL (4V-TO-NAT #) 'X)
;;             '(X)
;;             (IF (IF # # #) (BOOL-TO-4V-LST #) '#))))
;;
;; B-alist:
;; ((QQ[0] BOOL-TO-4V (LOGBITP '0 QQ)))
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-fail
(defthmd triple-reg-decomp-is-full-via-rewriting-fails-with-hard-error
  (implies (triple-reg-decomp-stv-autohyps)
           (b* ((comp1-ins (triple-reg-decomp-stv-autoins))
                (comp1-outs (stv-run (triple-reg-decomp-stv)
                                     comp1-ins))
                (q (cdr (assoc 'q comp1-outs)))

                (comp2-ins (triple-reg-decomp-stv-autoins))
                (comp2-outs (stv-run (triple-reg-decomp-stv)
                                     comp2-ins))
                (qq (cdr (assoc 'qq comp2-outs)))

                (comp3-ins (triple-reg-decomp-stv-autoins))
                (comp3-outs (stv-run (triple-reg-decomp-stv)
                                     comp3-ins))
                (comp-qqq (cdr (assoc 'qqq comp3-outs)))


                (full-ins (triple-reg-full-stv-autoins))
                (full-outs (stv-run (triple-reg-full-stv)
                                    full-ins))
                (full-qqq (cdr (assoc 'qqq full-outs))))
             (equal comp-qqq full-qqq)))
     :hints (("goal"
              :use ((:instance triple-reg-decomp-cutpoint-type-with-autohyps))
              :in-theory (stv-decomp-theory))))
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; [TRIPLE REG] Scenario 1
;
; This one also doesn't work but seems to get closer.  It uses specific hyps
; and specific inputs for both the theorem and in the hyps for the type lemma.
;
; Provided the wrapper functions do what I'd expect, it's pretty obvious from
; looking at the checkpoint why this is true.  It looks like the '(not (not
; (not d[0]))) just needs to be rewritten via sexpr-rewrites once more.  (not
; (not a)) is already part of *sexpr-rewrites*, so I'm not sure what to do yet.
;
;; (EQUAL
;;  (4V-TO-NAT (4V-SEXPR-EVAL-LIST '((NOT (NOT (NOT D[0]))))
;;                                 (LIST (CONS 'D[0]
;;                                             (BOOL-TO-4V (LOGBITP 0 D))))))
;;  (V-TO-NAT
;;       (BOOL-FROM-4V-LIST
;;            (4V-SEXPR-EVAL-LIST '((NOT D[0]))
;;                                (LIST (CONS 'D[0]
;;                                            (BOOL-TO-4V (LOGBITP 0 D)))))))))
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-fail
(defthmd triple-reg-decomp-is-full-via-rewriting-passes
  (implies (and (natp d)
                (< d (expt 2 1))
                (b* ((comp1-ins `((d . ,d)))
                     (comp1-outs (stv-run (triple-reg-decomp-stv)
                                          comp1-ins))
                     (q (cdr (assoc 'q comp1-outs)))

                     (comp2-ins `((q . ,q)))
                     (comp2-outs (stv-run (triple-reg-decomp-stv)
                                          comp2-ins))
                     (qq (cdr (assoc 'qq comp2-outs)))

                     ;; (comp3-ins `((qq . ,qq)))
                     ;; (comp3-outs (stv-run (triple-reg-decomp-stv)
                     ;;                      comp3-ins))
                     ;; (comp-qqq (cdr (assoc 'qqq comp3-outs)))


                     ;; (full-ins (triple-reg-full-stv-autoins))
                     ;; (full-outs (stv-run (triple-reg-full-stv)
                     ;;                     full-ins))
                     ;; (full-qqq (cdr (assoc 'qqq full-outs)))
                     )
                  (and (natp q)
                       (natp qq))))
           (b* ((comp1-ins `((d . ,d)))
                (comp1-outs (stv-run (triple-reg-decomp-stv)
                                     comp1-ins))
                (q (cdr (assoc 'q comp1-outs)))

                (comp2-ins `((q . ,q)))
                (comp2-outs (stv-run (triple-reg-decomp-stv)
                                     comp2-ins))
                (qq (cdr (assoc 'qq comp2-outs)))

                (comp3-ins `((qq . ,qq)))
                (comp3-outs (stv-run (triple-reg-decomp-stv)
                                     comp3-ins))
                (comp-qqq (cdr (assoc 'qqq comp3-outs)))


                (full-ins (triple-reg-full-stv-autoins))
                (full-outs (stv-run (triple-reg-full-stv)
                                    full-ins))
                (full-qqq (cdr (assoc 'qqq full-outs))))
             (equal comp-qqq full-qqq)))
  :hints (("goal"
           :use ((:instance triple-reg-decomp-cutpoint-type-with-specific-hyps))
           :in-theory (stv-decomp-theory))))
)



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Utility functions (some redefinitions)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define stv-decomp-4v-env-equiv-meta ((x pseudo-termp))
  (b* (((unless (and (consp x) (eq (car x) '4v-env-equiv)))
        (er hard? 'stv-decomp-4v-env-equiv-meta "Bad term: ~x0" x)
        x)
       ((list a b) (cdr x))
       ((mv err a-al) (stv-decomp-process-alist-term a))
       ((when err)
        (er hard? 'stv-decomp-process-alist-term "~@0" err)
        x)
       ((mv err b-al) (stv-decomp-process-alist-term b))
       ((when err)
        (er hard? 'stv-decomp-process-alist-term "~@0" err)
        x)
       ((when (alist-equiv a-al b-al))
        ''t))
    (sneaky-save 'a-al a-al)
    (sneaky-save 'b-al b-al)
    (er hard? 'stv-decomp-4v-env-equiv-meta "Not equivalent")
    x)
  ///
  (defthmd stv-decomp-4v-env-equiv-meta-rule
    (equal (stv-decomp-ev x env)
           (stv-decomp-ev (stv-decomp-4v-env-equiv-meta x) env))
    :rule-classes ((:meta :trigger-fns (4v-env-equiv)))))

(defun my-alist-equiv-bad-guy (a b)
  (cond ((atom a)
         (atom b)) ; none left behind
        ((assoc (caar a) b)
         (let ((match (assoc (caar a) b)))
           (if (equal (cdr match)
                      (cdar a))
               (my-alist-equiv-bad-guy (vl::vl-remove-keys (list (caar a))
                                                           (cdr a))
                                       (vl::vl-remove-keys (list (caar a))
                                                           b))
             (cons (list (car a) match)
                   (my-alist-equiv-bad-guy

                    (vl::vl-remove-keys (list (caar a))
                                        (cdr a))
                    (vl::vl-remove-keys (list (caar a))
                                        b))))))
        (t (cons (car a)
                 (my-alist-equiv-bad-guy

                  (vl::vl-remove-keys (list (caar a))
                                      (cdr a))
                  (vl::vl-remove-keys (list (caar a))
                                      b))))))

; For example, undo back to
; double-reg-decomp-is-full-via-rewriting-challenge-1-fails, perform the above
; defs, run double-reg-decomp-is-full-via-rewriting-challenge-1-fails, then
; run the following forms.

(defconsts (*a-al* state)
  (sneaky-load 'a-al state))
  ;; (mv-let (a-al state)
  ;;   (sneaky-load 'a-al state)
  ;;   (mv (car a-al) state)))

(defconsts (*b-al* state)
  (sneaky-load 'b-al state))
  ;; (mv-let (b-al state)
  ;;   (sneaky-load 'b-al state)
  ;;   (mv (car b-al) state)))

(my-alist-equiv-bad-guy *a-al* *b-al*)
