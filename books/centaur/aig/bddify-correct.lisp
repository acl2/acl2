; Centaur AIG Library
; Copyright (C) 2008-2011 Centaur Technology
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


(in-package "ACL2")
(include-book "bddify")
(include-book "centaur/ubdds/param" :dir :system)
(include-book "centaur/ubdds/lite" :dir :system)
(include-book "std/lists/suffixp" :dir :system)
(include-book "clause-processors/witness-cp" :dir :system)
(include-book "clause-processors/just-expand" :dir :system)
(include-book "centaur/misc/universal-equiv" :dir :system)
(include-book "std/basic/defs" :dir :system)
(in-theory (disable equal-by-eval-bdds
                    aig-q-compose-correct))

(set-inhibit-warnings "theory")


;; --------- UBDDP-VAL-ALISTP

;; Recognizes an alist for which each value is a UBDDP.

(defn ubddp-val-alistp (al)
  (if (atom al)
      t
    (and (or (atom (car al))
             (ubddp (cdar al)))
         (ubddp-val-alistp (cdr al)))))

(local
 (defthm ubddp-val-alistp-hons-assoc-equal
   (implies (ubddp-val-alistp al)
            (ubddp (cdr (hons-assoc-equal x al))))))


(defthm ubddp-aig-q-compose
  (implies (ubddp-val-alistp al)
           (ubddp (aig-q-compose x al))))


;; (local (q-witness-mode t))

;; (local
;;  (defthm qs-subset-to-equal-form
;;    (implies (and (ubddp a) (ubddp b))
;;             (equal (qs-subset a b)
;;                    (equal (q-implies a b) t)))
;;    :hints (("goal" :in-theory (enable qs-subset)))))

(local
 (in-theory (disable qs-subset-when-booleans
                     transitivity-of-qs-subset
                     qs-subset
                     eval-bdd
                     equal-of-booleans-rewrite
                     eval-bdd-when-non-consp-values
                     eval-bdd-when-not-consp
                     number-subtrees
                     (force)
                     )))



(defn subalistp (sub al)
  (if (atom sub)
      t
    (and (or (atom (car sub))
             (equal (car sub)
                    (hons-assoc-equal (caar sub) al)))
         (subalistp (cdr sub) al))))




(def-universal-equiv bdd-equiv
  :qvars (env)
  :equiv-terms ((equal (eval-bdd x env))))

(defcong bdd-equiv equal (eval-bdd x env) 1
  :hints(("Goal" :in-theory (enable bdd-equiv-necc))))

(defun-sk bdd-impl (x y)
  (forall env
          (implies (eval-bdd x env)
                   (eval-bdd y env))))

(in-theory (disable bdd-impl))


(definstantiate bdds-equal
  :predicate (equal x y)
  :vars (env)
  :expr (equal (eval-bdd x env) (eval-bdd y env))
  :hints ('(:in-theory nil))
  :restriction
  (if (match-term-pattern x (cdr (assoc-equal 'bdd (table-alist 'term-patterns
                                                                world))))
      (match-term-pattern y (cdr (assoc-equal 'bdd (table-alist 'term-patterns
                                                                world))))
    'nil))

(definstantiate bdds-bdd-equiv
  :predicate (bdd-equiv x y)
  :vars (env)
  :expr (equal (eval-bdd x env) (eval-bdd y env))
  :hints ('(:in-theory '(bdd-equiv-necc))))

(definstantiate not-bdd
  :predicate (not x)
  :vars (env)
  :expr (not (eval-bdd x env))
  :hints ('(:in-theory '(eval-bdd-of-nil)))
  :restriction
  (match-term-pattern x (cdr (assoc-equal 'bdd (table-alist 'term-patterns
                                                            world)))))

(definstantiate bdds-subset
  :predicate (bdd-impl x y)
  :vars (env)
  :expr (implies (eval-bdd x env) (eval-bdd y env))
  :hints ('(:by bdd-impl-necc)))

(defexample bdd-example-template
  :pattern (eval-bdd x env)
  :templates (env)
  :instance-rules (bdds-equal bdds-bdd-equiv not-bdd bdds-subset))

(defexample bdd-eval-alst-example-template
  :pattern (bdd-eval-alst x env)
  :templates (env)
  :instance-rules (bdds-equal bdds-bdd-equiv not-bdd bdds-subset))

(defwitness bdd-equiv-witnessing
  :predicate (not (bdd-equiv x y))
  :expr (let ((env (bdd-equiv-witness x y)))
          (not (equal (eval-bdd x env) (eval-bdd y env))))
  :hints ('(:in-theory (enable bdd-equiv)))
  :generalize (((bdd-equiv-witness x y) . env)))

(defwitness bdd-impl-witnessing
  :predicate (not (bdd-impl x y))
  :expr (let ((env (bdd-impl-witness x y)))
          (not (implies (eval-bdd x env) (eval-bdd y env))))
  :hints ('(:in-theory (enable bdd-impl)))
  :generalize (((bdd-impl-witness x y) . env)))



(def-witness-ruleset bdd-equality-rules
  '(bdd-example-template
    bdd-eval-alst-example-template
    not-bdd bdds-equal bdds-bdd-equiv bdd-equiv-witnessing
    bdds-subset bdd-impl-witnessing))



(defmacro simple-bdd-reasoning ()
  '(witness :ruleset bdd-equality-rules))


(defcong bdd-equiv equal (bdd-impl a b) 1
  :hints (("goal" :cases ((bdd-impl a b)))
          (simple-bdd-reasoning)))

(defcong bdd-equiv equal (bdd-impl a b) 2
  :hints (("goal" :cases ((bdd-impl a b)))
          (simple-bdd-reasoning)))

(defcong bdd-equiv bdd-equiv (q-and a b) 1
  :hints ((simple-bdd-reasoning)))

(defcong bdd-equiv bdd-equiv (q-and a b) 2
  :hints ((simple-bdd-reasoning)))

(defcong bdd-equiv bdd-equiv (q-not x) 1
  :hints ((simple-bdd-reasoning)))


(defthm bdd-impl-self
  (bdd-impl x x)
  :hints ((simple-bdd-reasoning)))

(defthm bdd-impl-nil-is-bdd-equiv-nil
  (equal (bdd-impl x nil)
         (bdd-equiv x nil))
  :hints (("goal" :cases ((bdd-impl x nil)))
          (simple-bdd-reasoning)))

(defthm bdd-impl-t-is-bdd-equiv-t
  (equal (bdd-impl t x)
         (bdd-equiv x t))
  :hints (("goal" :cases ((bdd-impl t x)))
          (simple-bdd-reasoning)))

(defthm aig-q-compose-nil
  (equal (aig-q-compose nil a)
         nil))


(defthm bdd-impl-transitive-1
  (implies (and (bdd-impl a b)
                (bdd-impl b c))
           (bdd-impl a c))
  :hints ((simple-bdd-reasoning)))

(defthm bdd-impl-transitive-2
  (implies (and (bdd-impl b c)
                (bdd-impl a b))
           (bdd-impl a c)))

(local
 (progn
   (defthm subalistp-hons-assoc-equal
     (implies (and (subalistp sub al)
                   (hons-assoc-equal x sub))
              (equal (hons-assoc-equal x sub)
                     (hons-assoc-equal x al))))


   (defthm ubddp-val-alistp-subalistp
     (implies (and (ubddp-val-alistp b)
                   (subalistp a b))
              (ubddp-val-alistp a))
     :hints (("Subgoal *1/4"
              :use ((:instance ubddp-val-alistp-hons-assoc-equal
                               (x (caar a)) (al b)))
              :in-theory (disable ubddp-val-alistp-hons-assoc-equal))))

   (in-theory (disable ubddp))

   ;; (defthm ubddp-aig-q-simplify
   ;;   (implies (ubddp-val-alistp al)
   ;;            (and (ubddp (mv-nth 0 (aig-q-simplify x al)))
   ;;                 (ubddp (mv-nth 1 (aig-q-simplify x al))))))

   (defthm ubddp-aig-q-compose
     (implies (ubddp-val-alistp al)
              (ubddp (aig-q-compose x al))))



   (add-bdd-fn-pat aig-q-compose)


   ;; (defthm aig-q-compose-aig-and
   ;;   (implies (ubddp-val-alistp al)
   ;;            (equal (aig-q-compose (aig-and a b) al)
   ;;                   (q-and (aig-q-compose a al)
   ;;                          (aig-q-compose b al))))
   ;;   :hints (("goal" :in-theory (enable aig-and))))

   ;; (defthm aig-q-compose-aig-not
   ;;   (implies (ubddp-val-alistp al)
   ;;            (equal (aig-q-compose (aig-not x) al)
   ;;                   (q-not (aig-q-compose x al))))
   ;;   :hints (("goal" :in-theory (enable aig-not))))



   (in-theory (disable aig-q-compose))


   (defthm merge-hi-lo-bounds-0-b
     (implies (and ;; (ubddp-val-alistp al)
                   ;; (ubddp hi1) (ubddp hi2)
                   ;; (ubddp lo1) (ubddp lo2)
                   (implies (eval-bdd lo1 v)
                            (eval-bdd hi1 v))
                   (implies (eval-bdd lo2 v)
                            (eval-bdd hi2 v)))
              (let ((ans (merge-hi-lo hi1 hi2 lo1 lo2 a11 a22 hc1 hc2 lc1 lc2)))
                (equal (eval-bdd (mv-nth 0 ans) v)
                       (eval-bdd (q-and hi1 hi2) v)))))

   (defthm merge-hi-lo-bounds-1-b
     (implies (and ;; (ubddp-val-alistp al)
                   ;; (ubddp hi1) (ubddp hi2)
                   ;; (ubddp lo1) (ubddp lo2)
                   (implies (eval-bdd lo1 v)
                            (eval-bdd hi1 v))
                   (implies (eval-bdd lo2 v)
                            (eval-bdd hi2 v)))
              (let ((ans (merge-hi-lo hi1 hi2 lo1 lo2 a11 a22 hc1 hc2 lc1 lc2)))
                (equal (eval-bdd (mv-nth 1 ans) v)
                       (eval-bdd (q-and lo1 lo2) v)))))

   (in-theory (enable aig-q-compose-correct))

   (defthm merge-hi-lo-aig-q-compose
     (implies (and ;; (ubddp-val-alistp al)
                   ;; (ubddp hi1) (ubddp hi2)
                   ;; (ubddp lo1) (ubddp lo2)
                   (implies (eval-bdd lo1 v)
                            (eval-bdd (aig-q-compose a1 al) v))
                   (implies (eval-bdd (aig-q-compose a1 al) v)
                            (eval-bdd hi1 v))
                   (implies (eval-bdd lo2 v)
                            (eval-bdd (aig-q-compose a2 al) v))
                   (implies (eval-bdd (aig-q-compose a2 al) v)
                            (eval-bdd hi2 v)))
              (let ((ans (merge-hi-lo hi1 hi2 lo1 lo2 a1 a2 hc1 hc2 lc1 lc2)))
                (equal (aig-eval (mv-nth 2 ans) (bdd-eval-alst al v))
                       (eval-bdd (q-and (aig-q-compose a1 al)
                                        (aig-q-compose a2 al)) v))))
     :hints (("goal" :in-theory (e/d (merge-hi-lo)))))

   (defthm ubddp-merge-hi-lo
     (implies (and (ubddp hi1) (ubddp hi2)
                   (ubddp lo1) (ubddp lo2))
              (let ((ans (merge-hi-lo hi1 hi2 lo1 lo2 a11 a22 hc1 hc2 lc1 lc2)))
                (and (ubddp (mv-nth 0 ans))
                     (ubddp (mv-nth 1 ans)))))
     :hints (("goal" :in-theory (e/d (merge-hi-lo)))))

   (add-bdd-pat (mv-nth 0 (merge-hi-lo . &)))
   (add-bdd-pat (mv-nth 1 (merge-hi-lo . &)))

   (defthm prune-by-count-nil-impl
     (implies (and ;; (ubddp b)
                   (not (eval-bdd b v)))
              (not (eval-bdd (mv-nth 0 (prune-by-count b cnt max nil)) v))))

   (defthm prune-by-count-t-impl
     (implies (and ;; (ubddp b)
                   (eval-bdd b v))
              (equal (eval-bdd (mv-nth 0 (prune-by-count b cnt max t)) v) t)))

   (defthm ubddp-prune-by-count
     (implies (and (ubddp b) (ubddp def))
              (ubddp (mv-nth 0 (prune-by-count b cnt max def))))
     :hints (("goal" :in-theory (enable prune-by-count))))


   (add-bdd-pat (mv-nth 0 (prune-by-count . &)))

   (in-theory (disable merge-hi-lo prune-by-count))

   (defthm ubddp-and-bddify-x-weakening
     (implies (and (ubddp hi1) (ubddp hi2)
                   (ubddp lo1) (ubddp lo2))
              (let ((ans (and-bddify-x-weakening
                          hi1 hi2 lo1 lo2 a11 a22 hc1 hc2 lc1 lc2 max)))
                (and (ubddp (mv-nth 0 ans))
                     (ubddp (mv-nth 1 ans)))))
     :hints (("goal" :in-theory (enable and-bddify-x-weakening))))

   (defthm and-bddify-x-weakening-bounds
     (implies (and ;; (ubddp-val-alistp al)
                   ;; (ubddp hi1) (ubddp hi2)
                   ;; (ubddp lo1) (ubddp lo2)
                   (implies (eval-bdd lo1 v)
                            (eval-bdd (aig-q-compose a1 al) v))
                   (implies (eval-bdd (aig-q-compose a1 al) v)
                            (eval-bdd hi1 v))
                   (implies (eval-bdd lo2 v)
                            (eval-bdd (aig-q-compose a2 al) v))
                   (implies (eval-bdd (aig-q-compose a2 al) v)
                            (eval-bdd hi2 v)))
              (let ((ans (and-bddify-x-weakening
                          hi1 hi2 lo1 lo2 a11 a22 hc1 hc2 lc1 lc2 max)))
                (and (implies (eval-bdd  (q-and (aig-q-compose a1 al)
                                                (aig-q-compose a2 al)) v)
                              (eval-bdd (mv-nth 0 ans) v))
                     (implies (not (eval-bdd (q-and (aig-q-compose a1 al)
                                                    (aig-q-compose a2 al)) v))
                              (not (eval-bdd (mv-nth 1 ans) v))))))
     :hints (("goal" :in-theory (e/d (and-bddify-x-weakening) nil)
              :do-not-induct t)
             (and stable-under-simplificationp
                  '(:in-theory (enable (:type-prescription eval-bdd))))
             (simple-bdd-reasoning)))





   (defthm and-bddify-x-weakening-impl
     (implies (and (bdd-impl lo1 (aig-q-compose a1 al))
                   (bdd-impl (aig-q-compose a1 al) hi1)
                   (bdd-impl lo2 (aig-q-compose a2 al))
                   (bdd-impl (aig-q-compose a2 al) hi2))
              (and (bdd-impl (q-and (aig-q-compose a1 al)
                                    (aig-q-compose a2 al))
                             (mv-nth 0 (and-bddify-x-weakening
                                        hi1 hi2 lo1 lo2 a1 a2 hc1 hc2 lc1 lc2
                                        max)))
                   (bdd-impl (mv-nth 1 (and-bddify-x-weakening
                                        hi1 hi2 lo1 lo2 a1 a2 hc1 hc2 lc1 lc2
                                        max))
                             (q-and (aig-q-compose a1 al)
                                    (aig-q-compose a2 al)))))
     :hints ((simple-bdd-reasoning)
             (and stable-under-simplificationp
                  '(:use ((:instance and-bddify-x-weakening-bounds
                           (a11 a1) (a22 a2) (al al) (v env0)))))))



   (defthm and-bddify-x-weakening-q-compose
     (implies (and ;; (ubddp-val-alistp al)
                   ;; (ubddp hi1) (ubddp hi2)
                   ;; (ubddp lo1) (ubddp lo2)
                   (implies (eval-bdd lo1 v)
                            (eval-bdd (aig-q-compose a1 al) v))
                   (implies (eval-bdd (aig-q-compose a1 al) v)
                            (eval-bdd hi1 v))
                   (implies (eval-bdd lo2 v)
                            (eval-bdd (aig-q-compose a2 al) v))
                   (implies (eval-bdd (aig-q-compose a2 al) v)
                            (eval-bdd hi2 v)))
              (equal (aig-eval (mv-nth 2 (and-bddify-x-weakening
                                          hi1 hi2 lo1 lo2 a1 a2 hc1 hc2 lc1 lc2 max))
                               (bdd-eval-alst al v))
                     (eval-bdd (q-and (aig-q-compose a1 al)
                                      (aig-q-compose a2 al)) v)))
     :hints (("goal" :in-theory (e/d (and-bddify-x-weakening))
              :do-not-induct t)
             (simple-bdd-reasoning)))

   (defthm and-bddify-x-weakening-equiv
     (implies (and (bdd-impl lo1 (aig-q-compose a1 al))
                   (bdd-impl (aig-q-compose a1 al) hi1)
                   (bdd-impl lo2 (aig-q-compose a2 al))
                   (bdd-impl (aig-q-compose a2 al) hi2))
              (bdd-equiv (aig-q-compose
                          (mv-nth 2 (and-bddify-x-weakening
                                     hi1 hi2 lo1 lo2 a1 a2 hc1 hc2 lc1 lc2
                                     max))
                          al)
                         (q-and (aig-q-compose a1 al)
                                (aig-q-compose a2 al))))
     :hints (("goal" :in-theory (disable and-bddify-x-weakening))
             (simple-bdd-reasoning)))))




(defun abs-fmemo-okp (fmemo al)
  (or (atom fmemo)
      (and (consp (car fmemo))
           (consp (cdar fmemo))
           (bdd-equiv (cadar fmemo)
                      (aig-q-compose (caar fmemo) al))
           (consp (cddar fmemo))
           (bdd-equiv (aig-q-compose (caddar fmemo) al)
                      (aig-q-compose (caar fmemo) al))
           (abs-fmemo-okp (cdr fmemo) al))))

(defun abs-fmemo-wfp (fmemo)
  (or (atom fmemo)
      (and (consp (car fmemo))
           (consp (cdar fmemo))
           (ubddp (cadar fmemo))
           (abs-fmemo-wfp (cdr fmemo)))))

(local
 (progn
   (defthm abs-fmemo-okp-hons-assoc-equal-rw1
     (implies (and (abs-fmemo-okp fmemo al)
                   (hons-assoc-equal x fmemo))
              (bdd-equiv (cadr (hons-assoc-equal x fmemo))
                         (aig-q-compose x al))))


   (defthm abs-fmemo-okp-hons-assoc-equal-rw2
     (implies (and (abs-fmemo-okp fmemo al)
                   (hons-assoc-equal x fmemo))
              (and (bdd-equiv (aig-q-compose (caddr (hons-assoc-equal x fmemo)) al)
                              (aig-q-compose x al)))))

   (defthm abs-fmemo-okp-hons-assoc-equal-ubddp
     (implies (and (abs-fmemo-wfp fmemo)
                   (hons-assoc-equal x fmemo))
              (ubddp (cadr (hons-assoc-equal x fmemo))))
     :hints (("goal" :in-theory (enable hons-assoc-equal))))

   ;; (defun abs-fmemo-okp-point (fmemo al v)
   ;;   (or (atom fmemo)
   ;;       (and (consp (car fmemo))
   ;;            (consp (cdar fmemo))
   ;;            (equal (eval-bdd (cadar fmemo) v)
   ;;                   (eval-bdd (aig-q-compose (caar fmemo) al) v))
   ;;            (consp (cddar fmemo))
   ;;            (equal (eval-bdd (aig-q-compose (caddar fmemo) al) v)
   ;;                   (eval-bdd (aig-q-compose (caar fmemo) al) v))
   ;;            (abs-fmemo-okp-point (cdr fmemo) al v))))


   ;; (defthm abs-fmemo-okp-point-hons-assoc-equal-rw1
   ;;   (implies (and (bind-free '((al . al)) (al))
   ;;                 (abs-fmemo-okp-point fmemo al v)
   ;;                 (hons-assoc-equal x fmemo))
   ;;            (equal (eval-bdd (cadr (hons-assoc-equal x fmemo)) v)
   ;;                   (eval-bdd (aig-q-compose x al) v))))


   ;; (defthm abs-fmemo-okp-point-hons-assoc-equal-rw2
   ;;   (implies (and (abs-fmemo-okp-point fmemo al v)
   ;;                 (hons-assoc-equal x fmemo))
   ;;            (and (equal (eval-bdd (aig-q-compose
   ;;                                   (caddr (hons-assoc-equal x fmemo)) al) v)
   ;;                        (eval-bdd (aig-q-compose x al) v))
   ;;                 ;;                 (simplifiedp (caddr (hons-assoc-equal x fmemo)) al)
   ;;                 )))

   ))



(defun apqs-memo-okp (memo al)
  (or (atom memo)
      (and (consp (car memo))
           (consp (cdar memo))
           (not (hqual (cadar memo) (caddar memo))) ;; ??
           (bdd-impl (aig-q-compose (caar memo) al) (cadar memo))
           (consp (cddar memo))
           (bdd-impl (caddar memo) (aig-q-compose (caar memo) al))
           (consp (cdddar memo))
           (bdd-equiv (aig-q-compose (car (cdddar memo)) al)
                      (aig-q-compose (caar memo) al))
           (apqs-memo-okp (cdr memo) al))))

(defun apqs-memo-wfp (memo)
  (or (atom memo)
      (and (consp (car memo))
           (consp (cdar memo))
           (ubddp (cadar memo))
           (ubddp (caddar memo))
           (apqs-memo-wfp (cdr memo)))))



(local
 (progn
   (defthm apqs-memo-okp-hons-assoc-equal-bdd-impl
     (implies (and (apqs-memo-okp memo al)
                   (hons-assoc-equal x memo))
              (and (bdd-impl (aig-q-compose x al) (cadr (hons-assoc-equal x memo)))
                   (bdd-impl (caddr (hons-assoc-equal x memo)) (aig-q-compose x
                                                                              al)))))

   (defthm apqs-memo-okp-hons-assoc-equal-bdd-impl-trans-1
     (implies (and (apqs-memo-okp memo al)
                   (hons-assoc-equal x memo)
                   (bdd-impl y (aig-q-compose x al)))
              (bdd-impl y (cadr (hons-assoc-equal x memo))))
     :hints(("Goal" :in-theory (disable apqs-memo-okp hons-assoc-equal))))

   (defthm apqs-memo-okp-hons-assoc-equal-bdd-impl-trans-2
     (implies (and (apqs-memo-okp memo al)
                   (hons-assoc-equal x memo)
                   (bdd-impl (aig-q-compose x al) y))
              (bdd-impl (caddr (hons-assoc-equal x memo)) y)))

   (defthm apqs-memo-okp-hons-assoc-equal-aig-q-compose-equal
     (implies (and (apqs-memo-okp memo al)
                   (hons-assoc-equal x memo))
              (bdd-equiv (aig-q-compose (car (cdddr (hons-assoc-equal x memo))) al)
                         (aig-q-compose x al))))


   (defthm apqs-memo-okp-hons-assoc-equal-ubddp
     (implies (and (apqs-memo-wfp memo)
                   (hons-assoc-equal x memo))
              (and (ubddp (cadr (hons-assoc-equal x memo)))
                   (ubddp (caddr (hons-assoc-equal x memo))))))

   (local
    (defthm apqs-memo-okp-consp-cdr-hons-assoc-equal
      (implies (and (bind-free '((al . al)) (al))
                    (apqs-memo-okp memo al)
                    (hons-assoc-equal x memo))
               (and (consp (cdr (hons-assoc-equal x memo)))
                    (consp (cddr (hons-assoc-equal x memo)))
                    (consp (cdddr (hons-assoc-equal x memo)))))))


   ;; (defthm apqs-memo-okp-hons-assoc-equal-pick-a-point
   ;;   (implies (and (apqs-memo-okp memo al)
   ;;                 (hons-assoc-equal x memo))
   ;;            (and (implies (eval-bdd (aig-q-compose x al) v)
   ;;                          (eval-bdd (cadr (hons-assoc-equal x memo)) v))
   ;;                 (implies (not (eval-bdd (aig-q-compose x al) v))
   ;;                          (not (eval-bdd (caddr (hons-assoc-equal x memo))
   ;;                                         v)))
   ;;                 (implies (eval-bdd (caddr (hons-assoc-equal x memo)) v)
   ;;                          (eval-bdd (cadr (hons-assoc-equal x memo)) v))
   ;;                 (implies (not (eval-bdd (cadr (hons-assoc-equal x memo)) v))
   ;;                          (not (eval-bdd (caddr (hons-assoc-equal x memo))
   ;;                                         v)))))
   ;;   :hints (("goal" :induct (hons-assoc-equal x memo)
   ;;            :expand ((apqs-memo-okp memo al)))
   ;;           (simple-bdd-reasoning)))


   (in-theory (disable and-bddify-x-weakening
                       ubddp-val-alistp-subalistp
                       subalistp hons-assoc-equal
                       subalistp-hons-assoc-equal))

   (in-theory (enable aig-q-compose))

   (add-bdd-pat (car (cdr (hons-assoc-equal x memo))))

   (add-bdd-pat (car (cdr (cdr (hons-assoc-equal x memo)))))


   ;; (defun apqs-memo-okp-point (memo al vals)
   ;;   (or (atom memo)
   ;;       (and (consp (car memo))
   ;;            (consp (cdar memo))
   ;;            (not (hqual (cadar memo) (caddar memo)))
   ;;            (implies (eval-bdd (aig-q-compose (caar memo) al) vals)
   ;;                     (eval-bdd (cadar memo) vals))
   ;;            (consp (cddar memo))
   ;;            (implies (eval-bdd (caddar memo) vals)
   ;;                     (eval-bdd (aig-q-compose (caar memo) al) vals))
   ;;            (consp (cdddar memo))
   ;;            (equal (eval-bdd (aig-q-compose (car (cdddar memo)) al) vals)
   ;;                   (eval-bdd (aig-q-compose (caar memo) al) vals))
   ;;            (apqs-memo-okp-point (cdr memo) al vals))))


   ;; (defthm apqs-memo-okp-point-hons-assoc-equal-impl
   ;;   (implies (and (apqs-memo-okp-point memo al v)
   ;;                 (hons-assoc-equal x memo))
   ;;            (and (implies (eval-bdd (aig-q-compose x al) v)
   ;;                          (eval-bdd (cadr (hons-assoc-equal x memo)) v))
   ;;                 (implies (not (eval-bdd (aig-q-compose x al) v))
   ;;                          (not (eval-bdd (caddr (hons-assoc-equal x memo)) v)))
   ;;                 (implies (eval-bdd (caddr (hons-assoc-equal x memo)) v)
   ;;                          (eval-bdd (cadr (hons-assoc-equal x memo)) v))
   ;;                 (implies (not (eval-bdd (cadr (hons-assoc-equal x memo)) v))
   ;;                          (not (eval-bdd (caddr (hons-assoc-equal x memo))
   ;;                                         v)))))
   ;;   :hints (("goal" :in-theory (e/d (hons-assoc-equal) (aig-q-compose)))))

   ;; (defthm apqs-memo-okp-point-hons-assoc-equal-aig-q-compose-equal
   ;;   (implies (and (apqs-memo-okp-point memo al v)
   ;;                 (hons-assoc-equal x memo))
   ;;            (equal (aig-eval (car (cdddr (hons-assoc-equal x memo)))
   ;;                             (bdd-eval-alst al v))
   ;;                   (eval-bdd (aig-q-compose x al) v)))
   ;;   :hints (("goal" :in-theory (e/d (hons-assoc-equal) (aig-q-compose)))))


   ;; ;; (defthm apqs-memo-okp-point-hons-assoc-equal-ubddp
   ;; ;;   (implies (and (bind-free '((al . al) (v . v)) (al v))
   ;; ;;                 (apqs-memo-okp-point memo al v)
   ;; ;;                 (hons-assoc-equal x memo))
   ;; ;;            (and (ubddp (cadr (hons-assoc-equal x memo)))
   ;; ;;                 (ubddp (caddr (hons-assoc-equal x memo)))))
   ;; ;;   :hints (("goal" :in-theory (e/d (hons-assoc-equal) (aig-q-compose)))))

   ;; (local
   ;;  (defthm apqs-memo-okp-point-consp-cdr-hons-assoc-equal
   ;;    (implies (and (bind-free '((al . al) (v . v)) (al v))
   ;;                  (apqs-memo-okp-point memo al v)
   ;;                  (hons-assoc-equal x memo))
   ;;             (and (consp (cdr (hons-assoc-equal x memo)))
   ;;                  (consp (cddr (hons-assoc-equal x memo)))
   ;;                  (consp (cdddr (hons-assoc-equal x memo)))))
   ;;    :hints (("goal" :in-theory (e/d (hons-assoc-equal) (aig-q-compose))))))


   (add-bdd-pat (mv-nth 0 (and-bddify-x-weakening . &)))
   (add-bdd-pat (mv-nth 1 (and-bddify-x-weakening . &)))
   (add-bdd-pat (mv-nth 0 (aig-bddify-x-weakening . &)))
   (add-bdd-pat (mv-nth 1 (aig-bddify-x-weakening . &)))

   (in-theory (disable hons-assoc-equal))

   ;; (defthm apqs-memo-lookup-ok-point
   ;;   (implies (and (abs-fmemo-okp-point fmemo al v)
   ;;                 (apqs-memo-okp-point memo al v))
   ;;            (b* (((mv ok hi lo a & &)
   ;;                  (apqs-memo-lookup x fmemo memo)))
   ;;              (implies ok
   ;;                       (and (equal (aig-eval a (bdd-eval-alst al v))
   ;;                                   (eval-bdd (aig-q-compose x al) v))
   ;;                            (implies (eval-bdd (aig-q-compose x al) v)
   ;;                                     (eval-bdd hi v))
   ;;                            (implies (not (eval-bdd (aig-q-compose x al) v))
   ;;                                     (not (eval-bdd lo v)))
   ;;                            (implies (eval-bdd lo v)
   ;;                                     (eval-bdd hi v))
   ;;                            (implies (not (eval-bdd hi v))
   ;;                                     (not (eval-bdd lo v)))))))
   ;;   :hints(("Goal" :induct (abs-fmemo-okp-point fmemo al v)
   ;;           :expand ((abs-fmemo-okp-point fmemo al v)
   ;;                    (hons-assoc-equal x fmemo)))))

   (defthm apqs-memo-lookup-ok
     (implies (and (abs-fmemo-okp fmemo al)
                   (apqs-memo-okp memo al))
              (b* (((mv ok hi lo a & &)
                    (apqs-memo-lookup x fmemo memo)))
                (implies ok
                         (and (bdd-equiv (aig-q-compose a al)
                                         (aig-q-compose x al))
                              (bdd-impl (aig-q-compose x al)
                                        hi)
                              (bdd-impl lo (aig-q-compose x al))
                              (bdd-impl lo hi)))))
     :hints (("goal"
              :in-theory (e/d (abs-fmemo-okp-hons-assoc-equal-rw1
                               abs-fmemo-okp-hons-assoc-equal-rw2)
                              (abs-fmemo-okp
                               apqs-memo-okp
                               hons-assoc-equal)))))

   (defthm apqs-memo-lookup-ubddp
     (b* (((mv ok hi lo ?a & &)
           (apqs-memo-lookup x fmemo memo)))
       (implies (and ok
                     (abs-fmemo-wfp fmemo)
                     (apqs-memo-wfp memo))
                (and (ubddp hi)
                     (ubddp lo)))))

   (add-bdd-pat (mv-nth 1 (apqs-memo-lookup . &)))
   (add-bdd-pat (mv-nth 2 (apqs-memo-lookup . &)))

   (in-theory (disable apqs-memo-lookup))

   ;; (defthm apqs-memo-cache-ok-point
   ;;   (implies (and (equal (aig-eval a (bdd-eval-alst al v))
   ;;                        (eval-bdd (aig-q-compose x al) v))
   ;;                 (implies (eval-bdd lo v)
   ;;                          (aig-eval x (bdd-eval-alst al v)))
   ;;                 (implies (eval-bdd (aig-q-compose x al) v)
   ;;                          (eval-bdd hi v))
   ;;                 (abs-fmemo-okp-point fmemo al v)
   ;;                 (apqs-memo-okp-point memo al v))
   ;;            (mv-let (fmemo memo)
   ;;              (apqs-memo-cache x hi lo a hc lc fmemo memo)
   ;;              (and (abs-fmemo-okp-point fmemo al v)
   ;;                   (apqs-memo-okp-point memo al v)))))

   (defthm apqs-memo-cache-ok
     (implies (and (double-rewrite (bdd-equiv (aig-q-compose a al)
                                              (aig-q-compose x al)))
                   (double-rewrite (bdd-impl lo (aig-q-compose x al)))
                   (double-rewrite (bdd-impl (aig-q-compose x al) hi))
                   (abs-fmemo-okp fmemo al)
                   (apqs-memo-okp memo al))
              (mv-let (fmemo memo)
                (apqs-memo-cache x hi lo a hc lc fmemo memo)
                (and (abs-fmemo-okp fmemo al)
                     (apqs-memo-okp memo al))))
     :hints ((simple-bdd-reasoning)))

   (defthm apqs-memo-cache-wfp
     (implies (and (ubddp hi)
                   (ubddp lo)
                   (abs-fmemo-wfp fmemo)
                   (apqs-memo-wfp memo))
              (b* (((mv fmemo memo)
                    (apqs-memo-cache x hi lo a hc lc fmemo memo)))
                (and (abs-fmemo-wfp fmemo)
                     (apqs-memo-wfp memo)))))

   (in-theory (disable apqs-memo-cache))




   (include-book "tools/with-quoted-forms" :dir :system)


   ;; (defthm aig-bddify-x-weakening-ok-point
   ;;   (implies (and (abs-fmemo-okp-point fmemo al v)
   ;;                 (apqs-memo-okp-point memo al v))
   ;;            (b* (((mv hi lo a & & fmemo memo)
   ;;                  (aig-bddify-x-weakening x al max fmemo memo))
   ;;                 (exact-bdd (aig-q-compose x al)))
   ;;              (and (abs-fmemo-okp-point fmemo al v)
   ;;                   (apqs-memo-okp-point memo al v)
   ;;                   ;; Concept!!! This theorem shows that the upper and
   ;;                   ;; lower bounds returned really are upper and lower
   ;;                   ;; bounds of the exact result.  (Therefore, if the
   ;;                   ;; bounds are equal, they equal the exact result.)
   ;;                   (implies (eval-bdd exact-bdd v)
   ;;                            (eval-bdd hi v))
   ;;                   (implies (not (eval-bdd exact-bdd v))
   ;;                            (not (eval-bdd lo v)))
   ;;                   (equal (aig-eval a (bdd-eval-alst al v))
   ;;                          (eval-bdd exact-bdd v)))))
   ;;   :hints (("goal" :induct (aig-bddify-x-weakening x al max fmemo memo)
   ;;            :do-not '(generalize fertilize)
   ;;            :do-not-induct t)
   ;;           (and (consp id)
   ;;                (equal (car id) '(0 1))
   ;;                '(:restrict ((aig-bddify-x-weakening
   ;;                              ((x x)) ((x nil)) ((x t)))
   ;;                             (aig-q-compose ((x x)) ((x nil)) ((x t))
   ;;                                            ((x (cdr (hons-assoc-equal x
   ;;                                                                       al))))))))

   ;;           (if (subsetp-equal '((NOT (CDR X)) (NOT (CONSP X))) clause)
   ;;               (with-quoted-forms
   ;;                (b* (((mv hi1 lo1 a11 hc1 lc1 fmemo memo)
   ;;                      (aig-bddify-x-weakening (car x) al max fmemo memo))
   ;;                     ((mv hi2 lo2 a22 hc2 lc2 & &)
   ;;                      (aig-bddify-x-weakening
   ;;                       (cdr x) al max fmemo memo)))
   ;;                  `(:use ((:instance and-bddify-x-weakening-bounds
   ;;                                     (a1 (car x)) (a2 (cdr x))
   ;;                                     . ,(var-fq-bindings
   ;;                                         (hi1 lo1 a11 hc1 lc1 hi2 lo2 a22 hc2
   ;;                                              lc2))))
   ;;                         :in-theory (disable and-bddify-x-weakening-bounds))))
   ;;             (value nil))
   ;;           (simple-bdd-reasoning)))


   (defthm aig-bddify-x-weakening-ok-ubddp
     (implies (and (ubddp-val-alistp al)
                   (abs-fmemo-wfp fmemo)
                   (apqs-memo-wfp memo))
              (b* (((mv hi lo ?a & & fmemo memo)
                    (aig-bddify-x-weakening x al max fmemo memo)))
                (and (ubddp hi) (ubddp lo)
                     (abs-fmemo-wfp fmemo)
                     (apqs-memo-wfp memo))))
     :hints ((just-induct-and-expand
              (aig-bddify-x-weakening x al max fmemo memo))
             '(:in-theory (disable aig-bddify-x-weakening))))

   ;; (defthm abs-fmemo-okp-implies-abs-fmemo-okp-point
   ;;   (implies (abs-fmemo-okp fmemo al)
   ;;            (abs-fmemo-okp-point fmemo al v))
   ;;   :hints (("goal" :in-theory (enable abs-fmemo-okp abs-fmemo-okp-point)
   ;;            :induct t)
   ;;           (simple-bdd-reasoning)))


   ;; (defthm apqs-memo-okp-implies-apqs-memo-okp-point
   ;;   (implies (apqs-memo-okp memo al)
   ;;            (apqs-memo-okp-point memo al v))
   ;;   :hints (("goal" :in-theory (enable apqs-memo-okp apqs-memo-okp-point)
   ;;            :induct t)
   ;;           (simple-bdd-reasoning)))



   ;; (defun abs-fmemo-not-okp-witness (fmemo al)
   ;;   (cond ((atom fmemo) nil)
   ;;         ((not (bdd-equiv (cadar fmemo)
   ;;                          (aig-q-compose (caar fmemo) al)))
   ;;          (bdd-equiv-witness (cadar fmemo)
   ;;                             (aig-q-compose (caar fmemo) al)))
   ;;         ((not (bdd-equiv (aig-q-compose (caddar fmemo) al)
   ;;                          (aig-q-compose (caar fmemo) al)))
   ;;          (bdd-equiv-witness (aig-q-compose (caddar fmemo) al)
   ;;                             (aig-q-compose (caar fmemo) al)))
   ;;         (t (abs-fmemo-not-okp-witness (cdr fmemo) al))))

   ;; (defthm abs-fmemo-not-okp-witness-correct
   ;;   (implies (not (abs-fmemo-okp fmemo al))
   ;;            (not (abs-fmemo-okp-point
   ;;                  fmemo al
   ;;                  (abs-fmemo-not-okp-witness fmemo al))))
   ;;   :hints (("goal" :in-theory (enable abs-fmemo-okp abs-fmemo-okp-point
   ;;                                      ubddp-val-alistp
   ;;                                      bdd-equiv)
   ;;            :induct t)))

   ;; (defthmd abs-fmemo-not-okp-witness-rw
   ;;   (iff (abs-fmemo-okp fmemo al)
   ;;        (abs-fmemo-okp-point
   ;;         fmemo al
   ;;         (abs-fmemo-not-okp-witness fmemo al))))

   ;; (defthm abs-fmemo-okp-point-with-witness
   ;;   (implies (abs-fmemo-okp-point
   ;;             fmemo al
   ;;             (abs-fmemo-not-okp-witness fmemo al))
   ;;            (abs-fmemo-okp-point fmemo al v)))

   ;; (in-theory (disable abs-fmemo-not-okp-witness))


   ;; ;; (defthm find-diff-theorem
   ;; ;;   (implies (and (ubddp a)
   ;; ;;                 (ubddp b)
   ;; ;;                 (not (equal a b)))
   ;; ;;            (equal (eval-bdd b (find-diff a b))
   ;; ;;                   (not (eval-bdd a (find-diff a b)))))
   ;; ;;   :hints(("Goal" :in-theory (enable ubddp eval-bdd find-diff)
   ;; ;;           :induct (find-diff a b)))
   ;; ;;   :rule-classes nil)


   ;; ;; (mutual-recursion
   ;; ;;  (defun find-find-diff (x)
   ;; ;;    (cond ((or (atom x)
   ;; ;;               (eq (car x) 'quote))
   ;; ;;           nil)
   ;; ;;          ((eq (car x) 'find-diff)
   ;; ;;           (list (cdr x)))
   ;; ;;          (t (find-find-diff-list (cdr x)))))
   ;; ;;  (defun find-find-diff-list (x)
   ;; ;;    (if (atom x)
   ;; ;;        nil
   ;; ;;      (append (find-find-diff (car x))
   ;; ;;              (find-find-diff-list (cdr x))))))

   ;; ;; (defun find-diff-insts (lst)
   ;; ;;   (if (atom lst)
   ;; ;;       nil
   ;; ;;     (let ((a (caar lst))
   ;; ;;           (b (cadar lst)))
   ;; ;;       (cons `(:instance find-diff-theorem (a ,a) (b ,b))
   ;; ;;             (find-diff-insts (cdr lst))))))

   ;; ;; (defun find-diff-hint (clause)
   ;; ;;   (let ((insts (find-find-diff-list clause)))
   ;; ;;     (and insts
   ;; ;;          `(:use ,(find-diff-insts insts)))))



   ;; (defun apqs-memo-not-okp-witness (memo al)
   ;;   (cond ((atom memo) nil)
   ;;         ((not (bdd-impl (aig-q-compose (caar memo) al) (cadar memo)))
   ;;          (bdd-impl-witness (aig-q-compose (caar memo) al) (cadar memo)))
   ;;         ((not (bdd-impl (caddar memo) (aig-q-compose (caar memo) al)))
   ;;          (bdd-impl-witness (caddar memo) (aig-q-compose (caar memo) al)))
   ;;         ((not (bdd-equiv (aig-q-compose (car (cdddar memo)) al)
   ;;                          (aig-q-compose (caar memo) al)))
   ;;          (bdd-equiv-witness (aig-q-compose (car (cdddar memo)) al)
   ;;                             (aig-q-compose (caar memo) al)))
   ;;         (t (apqs-memo-not-okp-witness (cdr memo) al))))

   ;; (defthm apqs-memo-not-okp-witness-correct
   ;;   (implies (not (apqs-memo-okp memo al))
   ;;            (not (apqs-memo-okp-point
   ;;                  memo al
   ;;                  (apqs-memo-not-okp-witness memo al))))
   ;;   :hints (("goal"
   ;;            :induct (apqs-memo-not-okp-witness memo al)
   ;;            :expand ((apqs-memo-not-okp-witness memo al)
   ;;                     (apqs-memo-okp memo al)
   ;;                     (:free (x) (apqs-memo-okp-point memo al x)))
   ;;            :in-theory (e/d (bdd-equiv bdd-impl)
   ;;                            (aig-eval)))))



   ;; (defthmd apqs-memo-not-okp-witness-rw
   ;;   (iff (apqs-memo-okp memo al)
   ;;        (apqs-memo-okp-point
   ;;         memo al
   ;;         (apqs-memo-not-okp-witness memo al))))

   ;; (defthm apqs-memo-point-with-witness
   ;;   (implies (apqs-memo-okp-point
   ;;             memo al
   ;;             (apqs-memo-not-okp-witness memo al))
   ;;            (apqs-memo-okp-point memo al v)))
   ))


;; (defexample abs-fmemo-okp-point-template
;;   :pattern (abs-fmemo-okp-point x al env)
;;   :templates (env)
;;   :instance-rules (bdds-equal bdds-bdd-equiv not-bdd bdds-subset))

;; (defexample apqs-memo-okp-point-template
;;   :pattern (apqs-memo-okp-point x al env)
;;   :templates (env)
;;   :instance-rules (bdds-equal bdds-bdd-equiv not-bdd bdds-subset))


;; (table witness-cp-rulesets
;;        'bdd-equality-rules
;;        (append '(abs-fmemo-okp-point-template
;;                  apqs-memo-okp-point-template)
;;                (cdr (assoc 'bdd-equality-rules
;;                            (table-alist 'witness-cp-rulesets world)))))

(defthm aig-q-compose-of-and-under-bdd-equiv
  (implies (and (not (aig-atom-p x))
                (cdr x))
           (bdd-equiv (aig-q-compose x al)
                      (q-and (aig-q-compose (car x) al)
                             (aig-q-compose (cdr x) al))))
  :hints ((simple-bdd-reasoning)))

(defthm aig-q-compose-of-not-under-bdd-equiv
  (implies (and (not (aig-atom-p x))
                (not (cdr x)))
           (bdd-equiv (aig-q-compose x al)
                      (q-not (aig-q-compose (car x) al))))
  :hints ((simple-bdd-reasoning)))

(defthm aig-q-compose-of-aig-not
  (bdd-equiv (aig-q-compose (aig-not x) al)
             (q-not (aig-q-compose x al)))
  :hints((simple-bdd-reasoning)))

(defthm aig-q-compose-of-var
  (implies (aig-var-p x)
           (equal (aig-q-compose x al)
                  (aig-alist-lookup x al))))

(defthm aig-q-compose-of-const
  (implies (booleanp x)
           (equal (aig-q-compose x al) x)))

(defthm bdd-impl-of-q-not
  (equal (bdd-impl (q-not a) (q-not b))
         (bdd-impl b a))
  :hints (("goal" :cases ((bdd-impl b a)))
          (simple-bdd-reasoning)))

(defthm bdd-equiv-of-q-not
  (equal (bdd-equiv (q-not a) (q-not b))
         (bdd-equiv a b))
  :hints (("goal" :cases ((bdd-equiv a b)))
          (simple-bdd-reasoning)))

(defthm bdd-impl-t
  (equal (bdd-impl x t) t)
  :hints((simple-bdd-reasoning)))

(defthm bdd-impl-nil
  (equal (bdd-impl nil x) t)
  :hints((simple-bdd-reasoning)))


(defthm bdd-impl-of-and-bddify-x-weakening-1
  (implies (and (bind-free '((al . al)) (al))
                (bdd-impl (q-and (aig-q-compose a1 al)
                                 (aig-q-compose a2 al))
                          x)
                (bdd-impl lo1 (aig-q-compose a1 al))
                (bdd-impl (aig-q-compose a1 al) hi1)
                (bdd-impl lo2 (aig-q-compose a2 al))
                (bdd-impl (aig-q-compose a2 al) hi2))
           (bdd-impl (mv-nth 1 (and-bddify-x-weakening
                                hi1 hi2 lo1 lo2 a1 a2 hc1 hc2 lc1 lc2
                                max))
                     x)))

(defthm bdd-equiv-nil-of-and-bddify-x-weakening-1
  (implies (and (bind-free '((al . al)) (al))
                (bdd-equiv (q-and (aig-q-compose a1 al)
                                 (aig-q-compose a2 al))
                           nil)
                (bdd-impl lo1 (aig-q-compose a1 al))
                (bdd-impl (aig-q-compose a1 al) hi1)
                (bdd-impl lo2 (aig-q-compose a2 al))
                (bdd-impl (aig-q-compose a2 al) hi2))
           (bdd-equiv (mv-nth 1 (and-bddify-x-weakening
                                 hi1 hi2 lo1 lo2 a1 a2 hc1 hc2 lc1 lc2
                                 max))
                      nil))
  :hints (("goal" :use ((:instance bdd-impl-of-and-bddify-x-weakening-1
                         (x nil))))))

(defthm bdd-impl-of-and-bddify-x-weakening-0
  (implies (and (bind-free '((al . al)) (al))
                (bdd-impl x
                          (q-and (aig-q-compose a1 al)
                                 (aig-q-compose a2 al)))
                (bdd-impl lo1 (aig-q-compose a1 al))
                (bdd-impl (aig-q-compose a1 al) hi1)
                (bdd-impl lo2 (aig-q-compose a2 al))
                (bdd-impl (aig-q-compose a2 al) hi2))
           (bdd-impl x
                     (mv-nth 0 (and-bddify-x-weakening
                                hi1 hi2 lo1 lo2 a1 a2 hc1 hc2 lc1 lc2
                                max)))))

(defthm bdd-equiv-t-of-and-bddify-x-weakening-1
  (implies (and (bind-free '((al . al)) (al))
                (bdd-equiv (q-and (aig-q-compose a1 al)
                                  (aig-q-compose a2 al))
                           t)
                (bdd-impl lo1 (aig-q-compose a1 al))
                (bdd-impl (aig-q-compose a1 al) hi1)
                (bdd-impl lo2 (aig-q-compose a2 al))
                (bdd-impl (aig-q-compose a2 al) hi2))
           (bdd-equiv (mv-nth 0 (and-bddify-x-weakening
                                hi1 hi2 lo1 lo2 a1 a2 hc1 hc2 lc1 lc2
                                max))
                      t))
  :hints (("goal" :use ((:instance bdd-impl-of-and-bddify-x-weakening-0
                         (x t))))))

(defthm aig-bddify-x-weakening-ok
  (implies (and (abs-fmemo-okp fmemo al)
                (apqs-memo-okp memo al))
           (b* (((mv hi lo a & & fmemo memo)
                 (aig-bddify-x-weakening x al max fmemo memo))
                (exact-bdd (aig-q-compose x al)))
             (and (abs-fmemo-okp fmemo al)
                  (apqs-memo-okp memo al)
                  ;; Concept!!! This theorem shows that the upper and
                  ;; lower bounds returned really are upper and lower
                  ;; bounds of the exact result.  (Therefore, if the
                  ;; bounds are equal, they equal the exact result.)
                  (bdd-impl exact-bdd hi)
                  (bdd-impl lo exact-bdd)
                  (bdd-equiv (aig-q-compose a al)
                             exact-bdd))))
  :hints ((just-induct-and-expand
           (aig-bddify-x-weakening x al max fmemo memo))
          '(:in-theory (disable aig-bddify-x-weakening
                                aig-q-compose))))

(defun bdd-equiv-list (x y)
  (declare (xargs :measure (+ (len x) (len y))))
  (if (and (atom x) (atom y))
      t
    (and (consp x) (consp y)
         (bdd-equiv (car x) (car y))
         (bdd-equiv-list (cdr x) (cdr y)))))

(defthm bdd-equiv-when-both-implications
  (implies (and (bdd-impl a b)
                (bdd-impl b a))
           (equal (bdd-equiv a b) t))
  :hints ((simple-bdd-reasoning)))


(defthm bdd-equiv-list-refl
  (bdd-equiv-list x x)
  :hints(("Goal" :induct (len x))))

(defequiv bdd-equiv-list :otf-flg t
  :hints(("Goal" :in-theory (enable default-car default-cdr))))

(defthm aig-bddify-list-x-weakening-ok
  (implies (and (abs-fmemo-okp fmemo al)
                (apqs-memo-okp memo al))
           (b* ((ans (aig-bddify-list-x-weakening x al max fmemo memo))
                ((mv bdds aigs fmemo memo exact) ans)
                (exact-bdds (aig-q-compose-list x al)))
             (and (abs-fmemo-okp fmemo al)
                  (apqs-memo-okp memo al)
                  (implies exact
                           (bdd-equiv-list bdds exact-bdds))
                  (bdd-equiv-list (aig-q-compose-list aigs al)
                                  exact-bdds))))
  :hints (("goal" :induct (aig-bddify-list-x-weakening x al max fmemo memo)
           :expand ((aig-bddify-list-x-weakening x al max fmemo memo))
           :in-theory (disable (:definition aig-bddify-list-x-weakening)))
          (and (member-equal '(NOT (CONSP X)) clause)
              `(:use ((:instance aig-bddify-x-weakening-ok
                                 (x (car x))))
                :in-theory (disable aig-bddify-x-weakening-ok
                                    aig-bddify-x-weakening)))))





;; Done with X-WEAKENING, on to VAR-WEAKENING...

(set-inhibit-warnings "theory")

(defund bdd-max-depth (x)
  (declare (xargs :hints (("goal" :in-theory (enable ubdd-fix)))))
  (if (atom (ubdd-fix x))
      0
    (+ 1 (max (bdd-max-depth (qcar x))
              (bdd-max-depth (qcdr x))))))

(defund bdd-al-max-depth (al)
  (if (atom al)
      0
    (max (bdd-max-depth (ec-call (cdr (car al))))
         (bdd-al-max-depth (cdr al)))))

(defthm bdd-al-max-depth-hons-assoc-equal
  (implies (<= (bdd-al-max-depth al) n)
           (<= (bdd-max-depth (cdr (hons-assoc-equal x al))) n))
  :hints(("Goal" :in-theory (enable bdd-al-max-depth hons-assoc-equal)))
  :rule-classes (:rewrite :linear))


(local (include-book "std/lists/take" :dir :system))

(defthm bdd-equiv-of-ubdd-fix
  (bdd-equiv (ubdd-fix x) x)
  :hints(("Goal" :in-theory (enable bdd-equiv))))

(defcong bdd-equiv equal (ubdd-fix x) 1
  :hints (("Goal" :use ((:instance eval-bdd-diff-witness-corr
                         (a (ubdd-fix x)) (b (ubdd-fix x-equiv)))))))

(add-bdd-pat (ubdd-fix . &))

(defthmd not-consp-ubdd-fix
  (equal (consp (ubdd-fix x))
         (and (not (bdd-equiv x t))
              (not (bdd-equiv x nil))))
  :hints(("Goal" :use ((:instance (:type-prescription ubdd-fix)))
          :in-theory (disable (:type-prescription ubdd-fix)))
         (simple-bdd-reasoning)))

(local (defun eval-bdd-take-ind (x n vals)
         (declare (xargs :measure (acl2-count x)))
         (cond ((atom x) (list n vals))
               ((atom vals) (eval-bdd-take-ind (cdr x) (1- n) nil))
               ((zp n) x)
               (t (eval-bdd-take-ind (if (car vals) (car x) (cdr x))
                                     (1- n) (cdr vals))))))

(defthm eval-bdd-of-take
  (implies (<= (bdd-max-depth x) (nfix n))
           (equal (eval-bdd x (take n vals))
                  (eval-bdd x vals)))
  :hints(("Goal" :induct (eval-bdd-take-ind x n vals)
          :expand ((:free (vals) (eval-bdd x vals))
                   (bdd-max-depth x)
                   (take n vals))
          :in-theory (e/d (default-cdr not-consp-ubdd-fix)
                          (take-when-atom
                           take-of-too-many)))))

(defcong bdd-equiv bdd-equiv (qcar x) 1
  :hints (("goal" :in-theory (disable bdd-equiv-is-an-equivalence))
          (and stable-under-simplificationp
               '(:use ((:instance bdd-equiv-necc
                        (y x-equiv)
                        (env (cons t (bdd-equiv-witness
                                      (qcar x) (qcar x-equiv))))))
                 :expand ((:free (vars) (eval-bdd x vars))
                          (:free (vars) (eval-bdd x-equiv vars))
                          (:free (vars) (eval-bdd nil vars)))
                 :in-theory (disable bdd-equiv-implies-equal-eval-bdd-1
                                     bdd-equiv-is-an-equivalence
                                     bdd-equiv-when-both-implications)))
          (and stable-under-simplificationp
               `(:expand (,(car (last clause))))))
  :otf-flg t)

(defcong bdd-equiv bdd-equiv (qcdr x) 1
  :hints (("goal" :in-theory (disable bdd-equiv-is-an-equivalence))
          (and stable-under-simplificationp
               '(:use ((:instance bdd-equiv-necc
                        (y x-equiv)
                        (env (cons nil (bdd-equiv-witness
                                        (qcdr x) (qcdr x-equiv))))))
                 :expand ((:free (vars) (eval-bdd x vars))
                          (:free (vars) (eval-bdd x-equiv vars))
                          (:free (vars) (eval-bdd nil vars)))
                 :in-theory (disable bdd-equiv-implies-equal-eval-bdd-1
                                     bdd-equiv-is-an-equivalence
                                     bdd-equiv-when-both-implications)))
          (and stable-under-simplificationp
               `(:expand (,(car (last clause))))))
  :otf-flg t)


(defun two-bdd-ind (x y)
  (declare (xargs :measure (+ (acl2-count x) (acl2-count y))))
  (if (and (atom x) (atom y))
      (list x y)
    (list (two-bdd-ind (qcar x) (qcar y))
          (two-bdd-ind (qcdr x) (qcdr y)))))

(defcong bdd-equiv equal (bdd-max-depth x) 1
  :hints(("Goal" :induct (two-bdd-ind x x-equiv)
          :expand ((bdd-max-depth x)
                   (bdd-max-depth x-equiv))
          :in-theory (disable qcar qcdr))
         (and stable-under-simplificationp
              '(:in-theory (e/d (ubdd-fix)
                                (qcar qcdr))))))


(local (in-theory (enable not-consp-ubdd-fix)))

(local
 (progn
   (in-theory (disable default-car default-cdr
                       default-+-1 default-+-2
                       default-<-1 default-<-2
                       aig-q-compose-correct
                       aig-bddify-x-weakening
                       al-max-depth
                       nonnegative-integer-quotient))

   (include-book "arithmetic/top-with-meta" :dir :system)


   ;; -------- Misc lemmas about basic functions.

   (defthm len-append
     (equal (len (append a b))
            (+ (len a) (len b))))

   (defn cons-make-list (n element final-tail)
     (if (not (posp n))
         final-tail
       (cons element (cons-make-list (1- n) element final-tail))))

   (defthm len-cons-make-list
     (equal (len (cons-make-list n m ac))
            (+ (nfix n) (len ac))))


   (encapsulate nil
     (defthm nth-append
       (equal (nth n (append a b))
              (if (< (nfix n) (len a))
                  (nth n a)
                (nth (- n (len a)) b)))))

   (defthm eval-bdd-depth-append
     (implies (<= (bdd-max-depth x) (len l))
              (equal (eval-bdd x (append l l2))
                     (eval-bdd x l)))
     :hints (("goal" :in-theory (enable max (:i eval-bdd))
              :induct (eval-bdd x l)
              :expand ((bdd-max-depth x)
                       (:free (vals) (eval-bdd x vals))))
             (and stable-under-simplificationp
                  '(:use ((:instance eval-bdd-ubdd-fix
                           (env (append l l2)))
                          (:instance eval-bdd-ubdd-fix
                           (env l)))
                    :in-theory (disable eval-bdd-ubdd-fix)))))

   (encapsulate
     nil
     (local (defthm cons-make-list-elt-to-tail
              (equal (cons-make-list m elt (cons elt tail))
                     (cons-make-list (+ 1 (nfix m)) elt tail))))

     (defthm make-list-cons-make-list
       (equal (make-list-ac n elt tail)
              (cons-make-list n elt tail))
       :hints (("goal" :induct (make-list-ac n elt tail)
                :in-theory (disable make-list-ac-removal)))))

   (defun eval-bdd-depth-ind (x n)
     (if (atom x)
         n
       (list (eval-bdd-depth-ind (car x) (1- n))
             (eval-bdd-depth-ind (cdr x) (1- n)))))

   (defthm eval-bdd-make-list
     (equal (eval-bdd x (cons-make-list n nil nil))
            (eval-bdd x nil))
     :hints (("goal" :in-theory (enable cons-make-list eval-bdd)
              :induct (eval-bdd-depth-ind x n))))

   (defthm eval-bdd-ap-make-list
     (equal (eval-bdd x (append vars (cons-make-list n nil nil)))
            (eval-bdd x vars))
     :hints(("Goal" :in-theory (enable eval-bdd))))


   ;; (defthm not-equal-x-t-implies-q-not
   ;;   (implies (and (ubddp x) (not (equal x t)))
   ;;            (q-not x))
   ;;   :hints (("goal" :in-theory (enable q-not ubddp))))


   ;; (defthm len-find-diff
   ;;   (<= (len (find-diff x y))
   ;;       (max (max-depth x)
   ;;            (max-depth y)))
   ;;   :hints (("goal" :in-theory (enable max max-depth find-diff)
   ;;            :induct (find-diff x y)))
   ;;   :rule-classes nil)

   ;; (defthm len-find-diff-bounds
   ;;   (implies (and (<= (max-depth x) n)
   ;;                 (<= (max-depth y) n))
   ;;            (<= (len (find-diff x y)) n))
   ;;   :hints (("goal" :use len-find-diff
   ;;            :in-theory (enable max))))



   (defthmd qv-plus-one
     (equal (cons (qv n) (qv n))
            (qv (+ 1 (nfix n))))
     :hints(("Goal" :in-theory (enable qv))))





   ;; (local (q-witness-mode t))
   ;; (defthm not-q-and-q-not
   ;;   (implies (ubddp x)
   ;;            (equal (q-and x (q-not x)) nil)))

   ;; (defthm not-q-not-q-and
   ;;   (implies (ubddp x)
   ;;            (equal (q-and (q-not x) x) nil)))



   ;; (defthm q-not-equal-t
   ;;   (implies (ubddp x)
   ;;            (equal (equal (q-not x) t)
   ;;                   (equal x nil)))
   ;;   :hints (("goal" :in-theory (enable q-not))))

   ;; (defthm q-not-equal-nil
   ;;   (implies (ubddp x)
   ;;            (equal (equal (q-not x) nil)
   ;;                   (equal x t)))
   ;;   :hints (("goal" :in-theory (enable q-not))))

   ;; (defthm q-not-iff-nonnil
   ;;   (implies (ubddp x)
   ;;            (iff (q-not x)
   ;;                 (not (equal x t))))
   ;;   :hints (("goal" :in-theory (enable q-not))))


   ;; (defthm q-and-not-equal-t
   ;;   (implies (and (ubddp x) (ubddp y)
   ;;                 (not (equal x t))
   ;;                 (not (equal y t)))
   ;;            (not (equal (q-and x y) t))))

   (defthm nth-len-lst
     (implies (<= (len lst) (nfix n))
              (equal (nth n lst) nil)))

   (defun count-down-two (n m)
     (if (zp n)
         m
       (count-down-two (1- n) (1- m))))

   (encapsulate nil
     (local (include-book "arithmetic/top-with-meta" :dir :system))
     (defthm nth-cons-make-list
       (equal (nth n (cons-make-list m elt tail))
              (if (< (nfix n) (nfix m))
                  elt
                (if (< (nfix n) (+ (nfix m) (len tail)))
                    (nth (- (nfix n) (nfix m)) tail)
                  nil)))
       :hints (("goal" :in-theory (enable cons-make-list)
                :induct (count-down-two m n)))))))


;; (defthm eval-bdd-equals-t
;;   (implies (and (ubddp x)
;;                 (eval-bdd x vals))
;;            (equal (equal (eval-bdd x vals) t) t)))


;; --------- SUFFIXP


(local
 (progn
   (in-theory (enable suffixp))

   (defthm suffixp-transitive-3
     (implies (and (suffixp a b)
                   (suffixp b c)
                   (suffixp c d))
              (and (suffixp a c)
                   (suffixp b d)
                   (suffixp a d)))
     :rule-classes nil)

   (defthm suffixp-transitive-4
     (implies (and (suffixp a b)
                   (suffixp b c)
                   (suffixp c d)
                   (suffixp d e))
              (and (suffixp a c)
                   (suffixp a d)
                   (suffixp a e)
                   (suffixp b d)
                   (suffixp b e)
                   (suffixp c e)))
     :hints (("Goal" :use (suffixp-transitive-3
                           (:instance suffixp-transitive-3
                            (a b)
                            (b c)
                            (c d)
                            (d e))
                           (:instance suffixp-transitive
                            (c e)))
              :in-theory (disable suffixp-transitive)))
     :rule-classes nil)


   (defthmd suffixp-len-<=
     (implies (suffixp x y)
              (equal (<= (len y) (len x))
                     (equal x y))))

   (defthm suffixp-len
     (implies (suffixp x y)
              (<= (len x) (len y)))
     :rule-classes (:rewrite :linear))




   ;; -------- AIG-Q-COMPOSE

   ;; AIG-Q-COMPOSE (defined in aig.lisp) takes an AIG as input along with an
   ;; alist which maps the variable symbols of the AIG to BDDs.  The output is the
   ;; BDD of the function expressed by the AIG, with the BDDs of the alist
   ;; substituted for the variables.

   ;; (defthm aig-q-compose-aig-and-eval
   ;;   (implies (ubddp-val-alistp al)
   ;;            (equal (eval-bdd (aig-q-compose (aig-and a b) al) vl)
   ;;                   (eval-bdd (q-and (aig-q-compose a al)
   ;;                                    (aig-q-compose b al)) vl)))
   ;;   :hints (("goal" :in-theory (enable aig-and))))
   ;;           ("Subgoal *1/2" :use ((:instance ubddp-implies-eval-bdd-blp
   ;;                                            (x (cdr (hons-assoc-equal a al)))
   ;;                                            (vals vl))))))



   (defthm aig-q-compose-aig-and
     (bdd-equiv (aig-q-compose (aig-and a b) al)
                (q-and (aig-q-compose a al)
                       (aig-q-compose b al)))
     :hints(("goal" :in-theory (enable aig-q-compose-correct))
            (simple-bdd-reasoning)))


   ;; (defthm aig-q-compose-aig-not-eval
   ;;   (implies (ubddp-val-alistp al)
   ;;            (equal (eval-bdd (aig-q-compose (aig-not x) al) vl)
   ;;                   (eval-bdd (q-not (aig-q-compose x al)) vl)))
   ;;   :hints (("goal" :in-theory (enable aig-not))))

   ;; (encapsulate nil
   ;;   (local (q-witness-mode t))
   ;;   (add-bdd-fn-pat aig-q-compose)
   ;;   (defthm aig-q-compose-aig-not
   ;;     (implies (ubddp-val-alistp al)
   ;;              (equal (aig-q-compose (aig-not x) al)
   ;;                     (q-not (aig-q-compose x al))))
   ;;     :hints(("Goal" :in-theory (enable aig-not)))))



   ;; (defthm aig-q-compose-t-or-nil
   ;;   (and (equal (aig-q-compose t al) t)
   ;;        (equal (aig-q-compose nil al) nil))
   ;;   :hints (("Goal" :in-theory (enable aig-q-compose))))

   ;; (defthmd aig-q-compose-and-decomp-x
   ;;   (implies (and (syntaxp (equal x 'x))
   ;;                 (consp x) (cdr x)
   ;;                 (ubddp-val-alistp al))
   ;;            (equal (aig-q-compose x al)
   ;;                   (q-and (aig-q-compose (car x) al)
   ;;                          (aig-q-compose (cdr x) al)))))

   ;; (defthmd aig-q-compose-not-decomp-x
   ;;   (implies (and (syntaxp (equal x 'x))
   ;;                 (consp x) (not (cdr x))
   ;;                 (ubddp-val-alistp al))
   ;;            (equal (aig-q-compose x al)
   ;;                   (q-not (aig-q-compose (car x) al)))))

   ;; -------- MAX-DEPTH

   ;; MAX-DEPTH (defined in misc.lisp) measures the maximum depth of a cons tree,
   ;; but for BDDs it is useful for limiting the variables that the BDD depends
   ;; upon -- i.e. if (< (max-depth x) n), then x is independent of the nth variable.


   (encapsulate nil
     (local (include-book "arithmetic/top-with-meta" :dir :system))
     (local (defthm bdd-max-depth-q-and-ubddp
              (implies (and (ubddp a) (ubddp b))
                       (<= (bdd-max-depth (q-and a b))
                           (max (bdd-max-depth a)
                                (bdd-max-depth b))))
              :hints (("goal" :in-theory (e/d* (q-and bdd-max-depth)
                                               ((force) ;; qcar qcdr
                                                ))
                       :induct (q-and a b)))))

     (defthm bdd-max-depth-q-and
       (<= (bdd-max-depth (q-and a b))
           (max (bdd-max-depth a)
                (bdd-max-depth b)))
       :hints (("goal" :use ((:instance bdd-max-depth-q-and-ubddp
                              (a (ubdd-fix a)) (b (ubdd-fix b))))
                :in-theory (disable bdd-max-depth-q-and-ubddp)))
       :rule-classes :linear))

   (defthm bdd-max-depth-q-and-bound
     (implies (and (<= (bdd-max-depth a) n)
                   (<= (bdd-max-depth b) n))
              (<= (bdd-max-depth (q-and a b)) n))
     :hints (("goal" :in-theory (e/d (max) (bdd-max-depth-q-and))
              :use bdd-max-depth-q-and))
     :rule-classes (:rewrite :linear))

   (encapsulate nil
     (local (defthm bdd-max-depth-q-not-ubddp
              (implies (ubddp x)
                       (equal (bdd-max-depth (q-not x))
                              (bdd-max-depth x)))
              :hints (("goal" :in-theory (e/d ((:i q-not) ubddp max
                                               bdd-max-depth)
                                              ((:d q-not)))
                       :induct (q-not x)
                       :expand ((bdd-max-depth (q-not x))
                                (bdd-max-depth x)))
                      (and stable-under-simplificationp
                           '(:expand ((:with q-not (q-not x))))))))

     (defthm bdd-max-depth-q-not
       (equal (bdd-max-depth (q-not x))
              (bdd-max-depth x))
       :hints (("goal" :use ((:instance bdd-max-depth-q-not-ubddp
                              (x (ubdd-fix x))))
                :in-theory (disable bdd-max-depth-q-not-ubddp)))))


   (defthm bdd-max-depth-aig-q-compose
     (implies (and (<= (bdd-al-max-depth al) n))
              (<= (bdd-max-depth (aig-q-compose x al)) n))
     :rule-classes (:rewrite :linear))

   ;; -------- Q-SAT

   ;; Q-SAT (defined in qi.lisp) makes a satisfying variable assignment for a BDD,
   ;; if one exists.

   ;; (defthm q-sat-correct
   ;;   (implies (and x (ubddp x))
   ;;            (equal (eval-bdd x (q-sat x)) t))
   ;;   :hints (("goal" :induct (q-sat x)
   ;;            :in-theory (enable ubddp eval-bdd q-sat))))

   ;; (defthm q-sat-correct-append
   ;;   (implies (and (case-split x) (ubddp x))
   ;;            (equal (eval-bdd x (append (q-sat x) y)) t))
   ;;   :hints (("goal" :induct (q-sat x)
   ;;            :in-theory (enable ubddp eval-bdd q-sat))))


   ;; (defthm eval-bdd-q-sat-not
   ;;   (implies (and (ubddp x) (not (equal x t)))
   ;;            (not (eval-bdd x (q-sat (q-not x)))))
   ;;   :hints (("goal" :use ((:instance eval-bdd-of-q-not
   ;;                                    (values (q-sat (q-not x)))))
   ;;            :in-theory (e/d (q-sat) (eval-bdd-of-q-not))
   ;;            :cases ((q-not x)))))


   ;; (defthm eval-bdd-q-sat-not-ap
   ;;   (implies (and (ubddp x) (case-split (not (equal x t))))
   ;;            (not (eval-bdd x (append (q-sat (q-not x)) y))))
   ;;   :hints (("goal" :use ((:instance eval-bdd-of-q-not
   ;;                                    (values (append (q-sat (q-not x)) y))))
   ;;            :in-theory (e/d (q-sat) (eval-bdd-of-q-not)))))

   ;; (defthm q-sat-len
   ;;   (<= (len (q-sat x)) (bdd-max-depth x))
   ;;   :rule-classes (:rewrite :linear)
   ;;   :hints (("goal" :in-theory (enable bdd-max-depth max q-sat))))


   ;; (defthm q-sat-not-len
   ;;   (implies (ubddp x)
   ;;            (<= (len (q-sat (q-not x))) (bdd-max-depth x)))
   ;;   :hints (("goal" :in-theory (enable q-not ubddp q-sat)))
   ;;   :rule-classes (:rewrite :linear))



   ;; (defthm q-and-not-t-boolean
   ;;   (implies (and (not (booleanp a))
   ;;                 (not (booleanp b))
   ;;                 (ubddp a)
   ;;                 (ubddp b)
   ;;                 (q-and a b))
   ;;            (not (booleanp (q-and a b))))
   ;;   :hints (("goal" :in-theory (e/d (booleanp) (eval-bdd-of-q-and))
   ;;            :use ((:instance eval-bdd-of-q-and
   ;;                             (x a) (y b)
   ;;                             (values (q-sat (q-not a)))))
   ;;            :do-not-induct t)))
   ))

;; -------- ASSIGN-FOR-BDD-AL.

;; See the documentation of AIG-BDDIFY-VAR-WEAKENING and ABS-BDD-AL-OKP.
;; ASSIGN-FOR-BDD-AL takes a "short" variable assignment (length less than n)
;; and lengthens it using the BDDs stored in BDD-AL to generate the later
;; variable numbers.

(defun assign-for-bdd-al-rec (bdd-al vars)
  (if (atom bdd-al)
      vars
    (let ((vars (assign-for-bdd-al-rec (cdr bdd-al) vars)))
      (append vars
              (list (eval-bdd (caar bdd-al) vars))))))

(defun lengthen-to-n (lst n)
  (append lst
          (make-list (- n (len lst)))))

(defun assign-for-bdd-al (bdd-al vars n)
  (assign-for-bdd-al-rec bdd-al (lengthen-to-n vars n)))

(local
 (progn
   (defthm len-assign-for-bdd-al-rec
     (equal (len (assign-for-bdd-al-rec bdd-al vars))
            (+ (len vars) (len bdd-al))))

   (defthm len-assign-for-bdd-al
     (implies (<= (len vars) (nfix n))
              (equal (len (assign-for-bdd-al bdd-al vars n))
                     (+ (len bdd-al) (nfix n)))))

   (defthm eval-assign-for-bdd-al-rec-at-less-depth
     (implies (<= (bdd-max-depth x) (len vars))
              (equal (eval-bdd x (assign-for-bdd-al-rec bdd-al vars))
                     (eval-bdd x vars)))
     :rule-classes ((:rewrite :backchain-limit-lst 2)))

   (defthm assign-for-bdd-al-depth
     (implies (and (<= (bdd-max-depth x) (nfix n))
                   (<= (len vars) (nfix n)))
              (equal (eval-bdd x (assign-for-bdd-al bdd-al vars n))
                     (eval-bdd x vars)))
     :rule-classes ((:rewrite :backchain-limit-lst 2))
     :hints(("Goal" :in-theory (disable append-of-nil))))

   (in-theory (disable assign-for-bdd-al cons-make-list))

   (defthm assign-for-bdd-al-depth-hons-assoc-equal
     (implies (and (<= (len vars) (nfix n))
                   (<= (bdd-al-max-depth al) (nfix n)))
              (equal (eval-bdd (cdr (hons-assoc-equal x al))
                               (assign-for-bdd-al bdd-al vars n))
                     (eval-bdd (cdr (hons-assoc-equal x al)) vars))))

   (defthm assign-for-bdd-al-rec-extend
     (implies (<= (bdd-max-depth x) (+ (len vars) (len bdd-al)))
              (equal (eval-bdd x (assign-for-bdd-al-rec (cons z bdd-al) vars))
                     (eval-bdd x (assign-for-bdd-al-rec bdd-al vars))))
     :hints (("Goal" :do-not-induct t
              :in-theory (enable assign-for-bdd-al-rec))))

   (defthm assign-for-bdd-al-extend
     (implies (and (<= (bdd-max-depth x) (+ n (len bdd-al)))
                   (integerp n)
                   (<= (len vars) n))
              (equal (eval-bdd x (assign-for-bdd-al (cons z bdd-al) vars n))
                     (eval-bdd x (assign-for-bdd-al bdd-al vars n))))
     :hints (("Goal" :do-not-induct t
              :in-theory (enable assign-for-bdd-al))))


   (defthm assign-for-bdd-al-rec-shrink
     (implies (and (<= (bdd-max-depth x) (+ (len vars) (len bdd-al) (- k)))
                   (< k (len bdd-al)))
              (equal (eval-bdd x (assign-for-bdd-al-rec (nthcdr k bdd-al) vars))
                     (eval-bdd x (assign-for-bdd-al-rec bdd-al vars))))
     :hints (("goal" :induct (nthcdr k bdd-al))))

   (defthm assign-for-bdd-al-shrink
     (implies (and (<= (bdd-max-depth x) (+ n (len bdd-al) (- k)))
                   (integerp n)
                   (<= (len vars) n)
                   (< k (len bdd-al)))
              (equal (eval-bdd x (assign-for-bdd-al (nthcdr k bdd-al) vars n))
                     (eval-bdd x (assign-for-bdd-al bdd-al vars n))))
     :hints (("goal" :induct (nthcdr k bdd-al))))

   (defthm assign-for-bdd-al-suffix
     (implies (and (<= (bdd-max-depth x) (+ n (len bdd-al)))
                   (integerp n)
                   (<= (len vars) n)
                   (suffixp bdd-al bdd-al2))
              (equal (eval-bdd x (assign-for-bdd-al bdd-al vars n))
                     (eval-bdd x (assign-for-bdd-al bdd-al2 vars n))))
     :hints (("goal" :in-theory (e/d (suffixp-equals-nthcdr)
                                     (assign-for-bdd-al-shrink))
              :use ((:instance assign-for-bdd-al-shrink
                               (k (- (len bdd-al2) (len bdd-al)))
                               (bdd-al bdd-al2)))
              :do-not-induct t)))))

;; -------- BDDS-COMPATIBLE-FOR-AL.

;; BDDS-COMPATIBLE-FOR-AL is a (non-executable) function that decides whether
;; BDD (of (+ N (LEN BDD-AL)) variables) is equivalent under the composition
;; given by BDD-AL to BDDF (of N variables.)  I.E., BDDS-COMPATIBLE-FOR-AL is
;; true if for all variable assignments VARS of length <= N,
;; (eval-bdd bdd (assign-for-bdd-al bdd-al vars n)) equals
;; (eval-bdd bddf vars).

;; (defchoose vars-for-bdd-al-mismatch vars (bddf bdd bdd-al n)
;;   (and (<= (len vars) (nfix n))
;;        (not (equal (eval-bdd bddf vars)
;;                    (eval-bdd bdd (assign-for-bdd-al bdd-al vars n))))))

;; (defun bdds-compatible-for-al (bddf bdd bdd-al n)
;;   (let ((vars (vars-for-bdd-al-mismatch bddf bdd bdd-al n)))
;;     (or (< (nfix n) (len vars))
;;         (equal (eval-bdd bddf vars)
;;                (eval-bdd bdd (assign-for-bdd-al bdd-al vars n))))))


(defun-sk bdds-compatible-for-al (bddf bdd bdd-al n)
  (forall vars
          (implies (<= (len vars) (nfix n))
                   (equal (eval-bdd bddf vars)
                          (eval-bdd bdd (assign-for-bdd-al bdd-al vars n))))))

(in-theory (disable bdds-compatible-for-al))
(defcong bdd-equiv equal (bdds-compatible-for-al bddf bdd bdd-al n) 1
  :hints (("goal" :cases ((bdds-compatible-for-al bddf bdd bdd-al n)))
          (and stable-under-simplificationp
               (let ((exp (if (eq (caar clause) 'not)
                              (car (last clause))
                            (car clause))))
                 `(:expand (,exp)
                   :use ((:instance bdds-compatible-for-al-necc
                          (bddf ,(if (eq (cadr exp) 'bddf)
                                     'bddf-equiv
                                   'bddf))
                          (vars (bdds-compatible-for-al-witness
                                 . ,(cdr exp))))))))))

(defcong bdd-equiv equal (bdds-compatible-for-al bddf bdd bdd-al n) 2
  :hints (("goal" :cases ((bdds-compatible-for-al bddf bdd bdd-al n)))
          (and stable-under-simplificationp
               (let ((exp (if (eq (caar clause) 'not)
                              (car (last clause))
                            (car clause))))
                 `(:expand (,exp)
                   :use ((:instance bdds-compatible-for-al-necc
                          (bdd ,(if (eq (caddr exp) 'bdd)
                                     'bdd-equiv
                                   'bdd))
                          (vars (bdds-compatible-for-al-witness
                                 . ,(cdr exp))))))))))




;; (defun shorten-bdd-assign (bdd vals)
;;   (cond ((atom bdd) nil)
;;         ((atom vals) vals)
;;         (t
;;          (cons (car vals)
;;                (shorten-bdd-assign (if (car vals)
;;                                        (car bdd)
;;                                      (cdr bdd))
;;                                    (cdr vals))))))

;; (defthm eval-bdd-of-shorten-bdd-assign
;;   (equal (eval-bdd x (shorten-bdd-assign x vals))
;;          (eval-bdd x vals))
;;   :hints(("Goal" :induct (shorten-bdd-assign x vals)
;;           :expand ((:free (vals) (eval-bdd x vals))))))

;; (defthm bdd-max-depth-shorten-bdd-assign
;;   (<= (len (shorten-bdd-assign bdd vals))
;;       (bdd-max-depth bdd))
;;   :hints(("Goal" :in-theory (enable bdd-max-depth)))
;;   :rule-classes :linear)

;; (in-theory (disable shorten-bdd-assign
;;                     bdds-compatible-for-al-necc))


(local
 (progn
   (defthm bdds-compatible-for-al-self
     (implies (<= (bdd-max-depth bdd) (nfix n))
              (bdds-compatible-for-al bdd bdd bdd-al n))
     :hints(("Goal" :in-theory (enable bdds-compatible-for-al))))



   (defthm bdds-compatible-with-boolean
     (implies (and (syntaxp (or (equal bdd ''nil) (equal bdd ''t)))
                   (booleanp bdd) ; (ubddp bddf)
                   (<= (bdd-max-depth bddf) (nfix n)))
              (equal (bdds-compatible-for-al bddf bdd bdd-al n)
                     (bdd-equiv bddf bdd)))
     :hints (("goal" :in-theory (e/d (booleanp)
                                     (nfix))
              :cases ((bdd-equiv bddf bdd)))
             (and stable-under-simplificationp
                  '(:use ((:instance bdds-compatible-for-al-necc
                           (bdd t)
                           (vars (take n (bdd-equiv-witness bddf t))))
                          (:instance bdds-compatible-for-al-necc
                           (bdd nil)
                           (vars (take n (bdd-equiv-witness bddf nil)))))
                    :in-theory (e/d (booleanp bdd-equiv)
                                    (nfix)))))
     :otf-flg t)

   (defthm bdds-compatible-rw
     (implies (and (bdds-compatible-for-al bddf bdd bdd-al n)
                   (<= (len vars) (nfix n)))
              (equal (eval-bdd bdd (assign-for-bdd-al bdd-al vars n))
                     (eval-bdd bddf vars)))
     :hints (("goal" :use bdds-compatible-for-al-necc)))

   (defthm bdds-compatible-q-nots-compatible
     (implies (bdds-compatible-for-al bddf bdd bdd-al n)
              (bdds-compatible-for-al (q-not bddf) (q-not bdd) bdd-al n))
     :hints (("goal"
              :in-theory (enable bdds-compatible-for-al)
              :restrict ((bdds-compatible-rw ((bddf (q-not bddf)))))
              :use ((:instance bdds-compatible-for-al-necc
                     (vars (bdds-compatible-for-al-witness
                            (q-not bddf) (q-not bdd) bdd-al n)))))))

   (defthm bdds-compatible-q-ands-compatible
     (implies (and (bdds-compatible-for-al bdd1f bdd1 bdd-al n)
                   (bdds-compatible-for-al bdd2f bdd2 bdd-al n))
              (bdds-compatible-for-al (q-and bdd1f bdd2f)
                                      (q-and bdd1 bdd2) bdd-al n))
     :hints (("goal"
              :restrict ((bdds-compatible-rw ((bddf (q-and bdd1f bdd2f)))))
              :use ((:instance bdds-compatible-for-al-necc
                               (bddf bdd1f) (bdd bdd1)
                               (vars (bdds-compatible-for-al-witness
                                      (q-and bdd1f bdd2f)
                                      (q-and bdd1 bdd2) bdd-al n)))
                    (:instance bdds-compatible-for-al-necc
                               (bddf bdd2f) (bdd bdd2)
                               (vars (bdds-compatible-for-al-witness
                                      (q-and bdd1f bdd2f)
                                      (q-and bdd1 bdd2) bdd-al n)))))
             (and stable-under-simplificationp
                  `(:expand (,(car (last clause)))))))



   (defthmd bdds-compatible-degenerate-and
     (implies (and (bdds-compatible-for-al bdd1f bdd1 bdd-al n)
                   (bdds-compatible-for-al bdd2f bdd2 bdd-al n)
                   (<= (bdd-max-depth bdd1f) (nfix n))
                   (<= (bdd-max-depth bdd2f) (nfix n))
                   (bdd-impl bdd1 bdd2))
              (bdd-impl bdd1f bdd2f))
     :hints (("goal" :do-not-induct t
              :in-theory (e/d ()
                              (bdds-compatible-for-al nfix
                                                      bdds-compatible-for-al-necc
                                                      ;; eval-bdd-when-bdd-impl
                                                      bdds-compatible-rw)))
             (and stable-under-simplificationp
                  '(:use ((:instance bdds-compatible-for-al-necc
                           (bddf bdd1f) (bdd bdd1)
                           (vars (take n (bdd-impl-witness bdd1f bdd2f))))
                          (:instance bdds-compatible-for-al-necc
                           (bddf bdd2f) (bdd bdd2)
                           (vars (take n (bdd-impl-witness bdd1f bdd2f)))))))
             (simple-bdd-reasoning)))

   (defthmd bdds-compatible-degenerate-and1
     (implies (and (bdds-compatible-for-al bdd2f bdd2 bdd-al n)
                   (bdds-compatible-for-al bdd1f bdd1 bdd-al n)
                   (<= (bdd-max-depth bdd2f) (nfix n))
                   (<= (bdd-max-depth bdd1f) (nfix n))
                   (bdd-equiv (q-and bdd1 bdd2) bdd1))
              (bdd-equiv (q-and bdd1f bdd2f) bdd1f))
     :hints (("goal" :do-not-induct t
              :in-theory (disable bdds-compatible-for-al nfix
                                  bdds-compatible-for-al-necc
                                  ;; eval-bdd-when-bdd-impl
                                  bdds-compatible-rw)
              :use ((:instance bdds-compatible-for-al-necc
                     (bddf bdd1f) (bdd bdd1)
                     (vars (take n (bdd-equiv-witness (q-and bdd1f bdd2f) bdd1f))))
                    (:instance bdds-compatible-for-al-necc
                     (bddf bdd2f) (bdd bdd2)
                     (vars (take n (bdd-equiv-witness (q-and bdd1f bdd2f)
                                                      bdd1f))))))
             (simple-bdd-reasoning)))

   (defthmd bdds-compatible-degenerate-and2
     (implies (and (bdds-compatible-for-al bdd2f bdd2 bdd-al n)
                   (bdds-compatible-for-al bdd1f bdd1 bdd-al n)
                   (<= (bdd-max-depth bdd2f) (nfix n))
                   (<= (bdd-max-depth bdd1f) (nfix n))
                   (bdd-equiv (q-and bdd1 bdd2) bdd2))
              (bdd-equiv (q-and bdd1f bdd2f) bdd2f))
     :hints (("goal" :do-not-induct t
              :in-theory (disable bdds-compatible-for-al nfix
                                  bdds-compatible-for-al-necc
                                  ;; eval-bdd-when-bdd-impl
                                  bdds-compatible-rw)
              :use ((:instance bdds-compatible-for-al-necc
                               (bddf bdd1f) (bdd bdd1)
                               (vars (take n (bdd-equiv-witness (q-and bdd1f bdd2f) bdd2f))))
                    (:instance bdds-compatible-for-al-necc
                     (bddf bdd2f) (bdd bdd2)
                     (vars (take n (bdd-equiv-witness (q-and bdd1f bdd2f) bdd2f))))))
             (simple-bdd-reasoning)))


   (defthm bdds-compatible-for-al-extend
     (implies (and (<= (bdd-max-depth x) (+ n (len bdd-al)))
                   (natp n)
                   (bdds-compatible-for-al y x bdd-al n))
              (bdds-compatible-for-al y x (cons z bdd-al) n))
     :hints (("Goal" :do-not-induct t
              :in-theory (enable bdds-compatible-for-al)
              :restrict ((bdds-compatible-for-al ((bdd-al (cons z bdd-al))))))))

   (defthm bdds-compatible-for-al-suffix
     (implies (and (<= (bdd-max-depth x) (+ n (len bdd-al)))
                   (natp n)
                   (suffixp bdd-al bdd-al2)
                   (bdds-compatible-for-al y x bdd-al n))
              (bdds-compatible-for-al y x bdd-al2 n))
     :hints (("goal" :do-not-induct t
              :in-theory (e/d (bdds-compatible-for-al) (bdds-compatible-rw))
              :use ((:instance bdds-compatible-for-al-necc
                               (bddf y) (bdd x) (bdd-al bdd-al)
                               (vars (bdds-compatible-for-al-witness
                                      y x bdd-al2 n)))))))

   (defthm bdds-compatible-for-al-cons
     (implies (and (<= (bdd-max-depth x) (+ n (len bdd-al)))
                   (natp n)
                   (bdds-compatible-for-al y x bdd-al n))
              (bdds-compatible-for-al y x (cons z bdd-al) n))
     :hints (("goal" :do-not-induct t
              :in-theory (disable bdds-compatible-for-al-suffix)
              :use ((:instance bdds-compatible-for-al-suffix
                               (bdd-al2 (cons z bdd-al)))))))

   (in-theory (disable bdds-compatible-for-al bdds-compatible-for-al-necc))))

;; --------- ABS-BDD-AL-OKP

;; ABS-BDD-AL-OKP recognizes a well-formed BDD-AL input for
;; AIG-BDDIFY-VAR-WEAKENING.  An ABS-BDD-AL-OKP object is an alist where each entry
;; is of a shape (BDD QVAR . COUNT), each BDD being UBDDP and each QVAR being a
;; BDD variable, and with the requirement that the QVARs are reverse-ordered,
;; so that if (cadr (cadr bdd-al)) equals (qvar k), then (cadr (car bdd-al))
;; equals (qvar (+ 1 k)).  Furthermore, the last QVAR is (QVAR N).

(defun abs-bdd-al-okp (bdd-al n)
  (or (atom bdd-al)
      (and (consp (car bdd-al))
           (consp (cdar bdd-al))
           (equal (cadar bdd-al)
                  (qv (+ n (len (cdr bdd-al)))))
           (<= (bdd-max-depth (caar bdd-al))
               (+ n (len (cdr bdd-al))))
           (abs-bdd-al-okp (cdr bdd-al) n))))

(defthmd bdd-max-depth-qv
  (equal (bdd-max-depth (qv n))
         (+ 1 (nfix n)))
  :hints(("Goal" :in-theory (e/d (bdd-max-depth (:i qv))
                                 (not-consp-ubdd-fix))
          :induct (qv n)
          :expand ((bdd-max-depth (qv n))))
         (and stable-under-simplificationp
              '(:expand ((qv n))))))

(local
 (progn
   (defthm abs-bdd-al-okp-cons
     (implies (and (abs-bdd-al-okp bdd-al n)
                   (natp n)
                   (equal var (qv (+ n (len bdd-al))))
                   (<= (bdd-max-depth bdd) (+ n (len bdd-al))))
              (abs-bdd-al-okp (cons (cons bdd (cons var cnt)) bdd-al) n)))

   (defthm abs-bdd-al-okp-hons-assoc-equal-ubddp
     (implies (and (bind-free '((n . n)) (n))
                   (abs-bdd-al-okp bdd-al n))
              (ubddp (cadr (hons-assoc-equal x bdd-al))))
     :hints(("Goal" :in-theory (enable hons-assoc-equal))))

   (defthm abs-bdd-al-okp-hons-assoc-equal-consp
     (implies (and (bind-free '((n . n)) (n))
                   (abs-bdd-al-okp bdd-al n)
                   (natp n)
                   (hons-assoc-equal x bdd-al))
              (consp (cadr (hons-assoc-equal x bdd-al))))
     :hints(("Goal" :in-theory (enable hons-assoc-equal)))
     :rule-classes :type-prescription)

   (defthm abs-bdd-al-okp-hons-assoc-equal-depth
     (implies (and (bind-free '((n . n)) (n))
                   (abs-bdd-al-okp bdd-al n)
                   (hons-assoc-equal x bdd-al))
              (<= (bdd-max-depth (cadr (hons-assoc-equal x bdd-al)))
                  (+ n (len bdd-al))))
     :hints (("Goal" :in-theory (e/d (bdd-max-depth bdd-max-depth-qv
                                                hons-assoc-equal)
                                     (equal-by-eval-bdds))))
     :rule-classes :linear)



   (defthm abs-bdd-al-okp-hons-assoc-equal-depth-rw
     (implies (and (abs-bdd-al-okp bdd-al n)
                   (hons-assoc-equal x bdd-al))
              (<= (bdd-max-depth (cadr (hons-assoc-equal x bdd-al)))
                  (+ n (len bdd-al))))
     :hints(("Goal" :in-theory (enable hons-assoc-equal))))

   (encapsulate
     nil
     (local (defthm abs-bdd-al-okp-hons-assoc-equal-depth-x
              (implies (and (abs-bdd-al-okp bdd-al n)
                            (hons-assoc-equal x bdd-al))
                       (<= (bdd-max-depth x)
                           (+ n (len bdd-al))))
              :hints(("Goal" :in-theory (enable hons-assoc-equal)))
              :rule-classes (:rewrite :linear)))

     (defthm eval-bdd-assign-for-bdd-al
       (implies (and (bind-free '((al . al)) (al))
                     (abs-bdd-al-okp bdd-al n)
                     (integerp n)
                     (<= (len vars) n)
                     (hons-assoc-equal x bdd-al))
                (equal (eval-bdd (cadr (hons-assoc-equal x bdd-al))
                                 (assign-for-bdd-al bdd-al vars n))
                       (eval-bdd x (assign-for-bdd-al bdd-al vars n))))
       :hints (("goal" :induct (hons-assoc-equal x bdd-al)
                :in-theory (enable hons-assoc-equal))
               ("subgoal *1/2" :expand (assign-for-bdd-al bdd-al vars n))
               ("subgoal *1/3" :use ((:instance assign-for-bdd-al-extend
                                      (x (cadr (hons-assoc-equal x bdd-al)))
                                      (bdd-al (cdr bdd-al))
                                      (z (car bdd-al)))
                                     (:instance assign-for-bdd-al-extend
                                      (bdd-al (cdr bdd-al))
                                      (z (car bdd-al))))
                :in-theory (e/d (hons-assoc-equal)
                                (assign-for-bdd-al-extend))))))

   (defthm abs-bdd-al-okp-bdd-compatible-hons-assoc-equal
     (implies (and (bind-free '((al . al)) (al))
                   (abs-bdd-al-okp bdd-al n)
                   (natp n)
                   (bdds-compatible-for-al bdd1f x bdd-al n)
                   (hons-assoc-equal x bdd-al))
              (bdds-compatible-for-al bdd1f (cadr (hons-assoc-equal x bdd-al))
                                      bdd-al n))
     :hints (("goal" :do-not-induct t
              :in-theory (enable bdds-compatible-for-al)
              :restrict ((bdds-compatible-for-al ((bdd (cadr (hons-assoc-equal x bdd-al)))))))))





   (encapsulate
     nil

     (local
      (encapsulate nil
        (local (include-book "arithmetic/top-with-meta" :dir :system))
        (defthm nth-assign-for-bdd-al-rec-above-vars
          (implies (and (natp n)
                        (<= (len vars) n)
                        (< n (+ (len vars) (len bdd-al))))
                   (equal (nth n (assign-for-bdd-al-rec bdd-al vars))
                          (eval-bdd (car (nth (+ -1 (len bdd-al) (- n) (len vars)) bdd-al))
                                    (assign-for-bdd-al-rec
                                     (nthcdr (+ (len bdd-al) (- n) (len vars)) bdd-al)
                                     vars))))
          :hints (("goal" :induct (assign-for-bdd-al-rec bdd-al vars))))))

     (local
      (defthm nth-assign-for-bdd-al-rec-below-vars
        (implies (and (natp n)
                      (< n (len vars)))
                 (equal (nth n (assign-for-bdd-al-rec bdd-al vars))
                        (nth n vars)))))

     (defthm nth-assign-for-bdd-al-rec
       (implies (and (natp n)
                     (< n (+ (len vars) (len bdd-al))))
                (equal (nth n (assign-for-bdd-al-rec bdd-al vars))
                       (if (< n (len vars))
                           (nth n vars)
                         (eval-bdd (car (nth (+ -1 (len bdd-al) (- n) (len vars)) bdd-al))
                                   (assign-for-bdd-al-rec
                                    (nthcdr (+ (len bdd-al) (- n) (len vars)) bdd-al)
                                    vars)))))))


   (defthm nth-abs-bdd-al-okp-depth
     (implies (and (natp k)
                   (< k (len bdd-al))
                   (abs-bdd-al-okp bdd-al n))
              (< (bdd-max-depth (car (nth k bdd-al)))
                 (+ n (len bdd-al) (- k))))
     :rule-classes (:rewrite :linear))

   ;; Skipped this
   (defthm nth-assign-for-bdd-al-rec-abs-bdd-al-okp
     (implies (and (natp k)
                   (< k (+ (len vars) (len bdd-al)))
                   (abs-bdd-al-okp bdd-al (len vars)))
              (equal (nth k (assign-for-bdd-al-rec bdd-al vars))
                     (if (< k (len vars))
                         (nth k vars)
                       (eval-bdd (car (nth (+ -1 (len bdd-al) (- k) (len vars)) bdd-al))
                                 (assign-for-bdd-al-rec bdd-al vars)))))
     :hints (("goal" :do-not-induct t
              :in-theory (disable equal-of-booleans-rewrite))
             ("goal'" :cases ((equal k (len vars))))))

   (encapsulate nil
     (local (include-book "arithmetic/top-with-meta" :dir :system))
     (defthm nth-assign-for-bdd-al-bdd-al-okp
       (implies (and (natp k)
                     (natp n)
                     (<= (len vars) n)
                     (< k (+ n (len bdd-al)))
                     (abs-bdd-al-okp bdd-al n))
                (equal (nth k (assign-for-bdd-al bdd-al vars n))
                       (if (< k (len vars))
                           (nth k vars)
                         (if (< k n)
                             nil
                           (eval-bdd (car (nth (+ -1 (len bdd-al) (- k) n) bdd-al))
                                     (assign-for-bdd-al bdd-al vars n))))))
       :hints (("goal" :do-not-induct t
                :in-theory (e/d (assign-for-bdd-al) (nth-assign-for-bdd-al-rec))))))

   (encapsulate nil
     (local (include-book "arithmetic/top-with-meta" :dir :system))
     (defthm bdds-compatible-for-al-extend-for-x
       (implies (and (natp n)
                     (abs-bdd-al-okp bdd-al n)
                     (bdds-compatible-for-al x bdd bdd-al n)
                     (<= (bdd-max-depth bdd) (+ n (len bdd-al))))
                (bdds-compatible-for-al
                 x (qv (+ n (len bdd-al)))
                 (cons (list* bdd (qv (+ n (len bdd-al))) cnt) bdd-al)
                 n))
       :hints (("goal" :do-not-induct t
                :in-theory (e/d (bdds-compatible-for-al abs-bdd-al-okp) (bdds-compatible-rw))
                :restrict ((bdds-compatible-for-al
                            ((bdd (qv (+ n (len bdd-al)))))))
                :use ((:instance bdds-compatible-rw
                                 (bddf x)
                                 (vars (bdds-compatible-for-al-witness
                                        x (qv (+ n (len bdd-al)))
                                        (cons (list* bdd (qv (+ n (len bdd-al))) cnt) bdd-al)
                                        n))))))
       :otf-flg t))

   (in-theory (disable bdds-compatible-for-al))))




;; --------- ABS-MEMO-OKP

;; Recognizes a good MEMO argument to AIG-BDDIFY-VAR-WEAKENING.  Such an object is
;; an alist where each entry is shaped like (X BDD AIG . COUNT), where X and
;; AIG are AIGs, (AIG-Q-COMPOSE X AL) and (AIG-Q-COMPOSE AIG AL) are equal, and
;; BDD is a representation of (AIG-Q-COMPOSE X AL) using BDD-AL, i.e.
;; (BDDS-COMPATIBLE-FOR-AL (AIG-Q-COMPOSE X AL) BDD BDD-AL N) holds.

(defun abs-memo-okp (memo n al bdd-al)
  (or (atom memo)
      (and (consp (car memo))
           (consp (cdar memo))
           ; (not (booleanp (cadar memo)))
           (bdds-compatible-for-al
            (aig-q-compose (caar memo) al)
            (cadar memo) bdd-al n)
           (<= (bdd-max-depth (cadar memo)) (+ n (len bdd-al)))
           (consp (cddar memo))
           (bdd-equiv (aig-q-compose (caddar memo) al)
                      (aig-q-compose (caar memo) al))
           (abs-memo-okp (cdr memo) n al bdd-al))))

(local
 (progn
   (defthm abs-memo-okp-hons-assoc-equal-linear
     (implies (and (bind-free '((al . al) (n . n)) (al n))
                   (abs-memo-okp memo n al bdd-al)
                   (hons-assoc-equal x memo))
              (<= (bdd-max-depth (cadr (hons-assoc-equal x memo)))
                  (+ n (len bdd-al))))
     :hints(("Goal" :in-theory (enable hons-assoc-equal)))
     :rule-classes :linear)

   (defthm abs-memo-okp-hons-assoc-equal-rw1
     (implies (and (abs-memo-okp memo n al bdd-al)
                   (hons-assoc-equal x memo))
              (bdds-compatible-for-al
               (aig-q-compose x al)
               (cadr (hons-assoc-equal x memo)) bdd-al n))
     :hints(("Goal" :in-theory (enable hons-assoc-equal))))

   (defthm abs-memo-okp-hons-assoc-equal-rw2
     (implies (and (bind-free '((al . al)) (al))
                   (abs-memo-okp memo n al bdd-al)
                   (hons-assoc-equal x memo))
              (<= (bdd-max-depth (cadr (hons-assoc-equal x memo)))
                  (+ n (len bdd-al))))
     :hints(("Goal" :in-theory (enable hons-assoc-equal))))

   (defthm abs-memo-okp-hons-assoc-equal-rw3
     (implies (and ;; (bind-free '((n . n)) (n))
               (abs-memo-okp memo n al bdd-al)
               (hons-assoc-equal x memo))
              (bdd-equiv (aig-q-compose (caddr (hons-assoc-equal x memo)) al)
                         (aig-q-compose x al)))
     :hints(("Goal" :in-theory (enable hons-assoc-equal))))

   ;; (defthm abs-memo-okp-hons-assoc-equal-ubddp
   ;;   (implies (and (bind-free '((al . al)) (al))
   ;;                 (abs-memo-okp memo n al bdd-al)
   ;;                 (hons-assoc-equal x memo))
   ;;            (not (booleanp (cadr (hons-assoc-equal x memo)))))
   ;;   :hints(("Goal" :in-theory (enable hons-assoc-equal))))

   (defthm abs-memo-okp-extend-bdd-al
     (implies (and (abs-memo-okp memo n al bdd-al)
                   (natp n))
              (abs-memo-okp memo n al (cons z bdd-al))))

   (defthm abs-memo-okp-consp-cdr-hons-assoc-equal
     (implies (and (bind-free '((al . al)) (al))
                   (abs-memo-okp memo n al bdd-al)
                   (hons-assoc-equal x memo))
              (and (consp (cdr (hons-assoc-equal x memo)))
                   (consp (cddr (hons-assoc-equal x memo)))))
     :hints(("Goal" :in-theory (enable hons-assoc-equal))))

   (defthm bdds-compatible-bdd-max-depth-implies-equiv
     (implies (and ;;(ubddp bddf) (ubddp bdd)
                   (<= (bdd-max-depth bddf) (nfix n))
                   (<= (bdd-max-depth bdd) (nfix n)))
              (equal (bdds-compatible-for-al bddf bdd bdd-al n)
                     (bdd-equiv bddf bdd)))
     :hints (("Goal" :in-theory (disable
                                 nfix equal-by-eval-bdds
                                 bdds-compatible-rw)
              :cases ((bdd-equiv bddf bdd))
              :use ((:instance bdds-compatible-for-al-necc
                     (vars (take n (bdd-equiv-witness bddf bdd)))))
              :do-not-induct t)
             (simple-bdd-reasoning))
     :rule-classes nil)


   (defthm abs-memo-okp-bdd-max-depth-implies-equal-q-compose
     (implies (and (hons-assoc-equal x memo)
                   (<= (bdd-max-depth (cadr (hons-assoc-equal x memo)))
                       (bdd-al-max-depth al))
                   (abs-memo-okp memo (bdd-al-max-depth al)
                                 al bdd-al))
              (equal (bdd-equiv (cadr (hons-assoc-equal x memo))
                                (aig-q-compose x al))
                     t))
     :hints (("Goal" :use ((:instance abs-memo-okp-hons-assoc-equal-rw1
                                      (n (bdd-al-max-depth al)))
                           (:instance bdds-compatible-bdd-max-depth-implies-equiv
                                      (bddf (aig-q-compose x al))
                                      (bdd (cadr (hons-assoc-equal x memo)))
                                      (n (bdd-al-max-depth al))))
              :in-theory (disable abs-memo-okp-hons-assoc-equal-rw1)
              :do-not-induct t)))))

;; --------- AIG-BDDIFY-VAR-WEAKENING

;; AIG-BDDIFY-VAR-WEAKENING, defined in aig.lisp, attempts to simultaneously
;; simplify an input AIG and produce its BDD given by a variable assignment AL.
;; BDD sizes are limited to MAX-COUNT; when a BDD is generated which is larger
;; than MAX-COUNT, it is replaced by a fresh variable, so that while the BDD
;; produced won't be an exact representation of the AIG, it can still be used
;; to simplify the AIG further.

;; The inputs of AIG-BDDIFY-VAR-WEAKENING are:

;; X is the input AIG

;; AL is an alist mapping variables of X to BDDs

;; MAX-COUNT is the threshold beyond which large BDDs are approximated.

;; FMEMO is a table that holds calculated answers that are exact, in that
;; no BDD approximations affected them.

;; MEMO holds calculated answers which are not exact, in that BDD
;; approximations may have affected them.

;; BDD-AL records what fresh variables have been substituted for what BDDs

;; NXTBDD holds the next fresh variable not present in either AL or BDD-AL.


;; The outputs are (MV AIG BDD COUNT FMEMO MEMO BDD-AL NXTBDD EXACT, where

;; AIG is an AIG which is equivalent to X under AL, i.e.
;; (equal (aig-q-compose x al) (aig-q-compose aig al)).  If EXACT, then AIG is
;; "fully simplified" (see SIMPLIFIEDP.)

;; BDD is an approximation of (aig-q-compose x al); if EXACT holds, then BDD
;; equals (aig-q-compose x al).

;; COUNT is an overapproximation of the size (number-bdd-branches) of BDD.

;; FMEMO, MEMO, BDD-AL, NXTBDD are as described in the inputs.

;; EXACT is a flag saying whether or not any approximations were used.

(local
 (progn
   (in-theory (enable qv-plus-one))

   (defthm max-depth-when-bdd-equiv-aig-q-compose
     (implies (and (bdd-equiv bdd (aig-q-compose aig al))
                   (<= (bdd-al-max-depth al) n))
              (<= (bdd-max-depth bdd) n))
     :rule-classes :linear)

   (defthm q-and-self
     (bdd-equiv (q-and x x) x)
     :hints ((simple-bdd-reasoning)))

   ;; (defthm bdds-compatible-with-boolean-equiv
   ;;   (implies (and (syntaxp (or (equal bdd ''nil) (equal bdd ''t)))
   ;;                 (booleanp bdd) ; (ubddp bddf)
   ;;                 (bdd-equiv x bddf)
   ;;                 (<= (bdd-max-depth x) (nfix n)))
   ;;            (equal (bdds-compatible-for-al bddf bdd bdd-al n)
   ;;                   (bdd-equiv bddf bdd)))
   ;;   :hints(("Goal" :in-theory (enable booleanp))))

   ;; (defthm bdds-compatible-with-boolean-equiv-and
   ;;   (implies (and (syntaxp (or (equal bdd ''nil) (equal bdd ''t)))
   ;;                 (booleanp bdd) ; (ubddp bddf)
   ;;                 (bdd-equiv x a)
   ;;                 (<= (bdd-max-depth x) (nfix n))
   ;;                 (<= (bdd-max-depth b) (nfix n)))
   ;;            (equal (bdds-compatible-for-al (q-and a b) bdd bdd-al n)
   ;;                   (bdd-equiv (q-and a b) bdd)))
   ;;   :hints(("Goal" :in-theory (enable booleanp)
   ;;           :use ((:instance bdds-compatible-with-boolean
   ;;                  (bddf (q-and x b)))))))


   ;; Lemma: the various invariants are preserved under the AND case.
   (encapsulate
     nil
     (local (defthm len-cons-open (equal (len (cons a b)) (+ 1 (len b)))))
     (local (in-theory (e/d*
                        ()
                        ((:rules-of-class :type-prescription :here)
                         aig-q-compose
                         bdds-compatible-for-al-self
                         aig-q-compose-of-var
                         aig-q-compose-of-not-under-bdd-equiv
                         aig-q-compose-of-and-under-bdd-equiv
                         set::double-containment
                         bdd-impl-transitive-2
                         bdd-impl-transitive-1
                         qv ;;qv-+1
                         bdd-max-depth abs-memo-okp abs-fmemo-okp
                         hons-assoc-equal bdd-al-max-depth
                         max ;;blp-implies-t
                         ;;qvar-of-non-natp
                         bdds-compatible-q-ands-compatible
                         ;; bdds-compatible-with-boolean-equiv
                         bdds-compatible-degenerate-and
                         bdds-compatible-degenerate-and2
                         bdd-equiv-when-both-implications
                         ;; bdds-compatible-with-boolean
                         mv-nth-cons-meta
                         q-and-of-self-slow
                         booleanp not
                         ;; booleanp-compound-recognizer
                         ubddp ;;simplifiedp
                         abs-bdd-al-okp
                         bdds-compatible-for-al-suffix
                         bdds-compatible-for-al-cons
                         suffixp-of-self
                         assign-for-bdd-al-suffix
                         suffixp-len len
;                     (:REWRITE |(equal (- x) (- y))|)
;                     (:REWRITE |(< (- x) (- y))|)
;                            (:REWRITE |(< (- x) 0)|)
;                            (:REWRITE |(< d (+ c x))|)
                         (:REWRITE SUFFIXP-TRANSITIVE)
                         (:REWRITE ABS-FMEMO-OKP-HONS-ASSOC-EQUAL-RW1)
;                         (:REWRITE FOLD-CONSTANTS-IN-PLUS)
                         (:DEFINITION UBDDP-VAL-ALISTP))
                        ((:type-prescription len)
                         (:type-prescription bdd-max-depth)
                         (:type-prescription bdd-al-max-depth)
                         (:type-prescription count-branches-to)
                         (:type-prescription hons-assoc-equal)
                         (:type-prescription abs-bdd-al-okp-hons-assoc-equal-consp)
                         (:type-prescription qv)
                         bdd-max-depth-qv))))
     (local (in-theory (enable and-bddify-var-weakening)))
     (defthm and-bddify-var-weakening-ok
       (implies (and (<= (bdd-max-depth bdd1) (+ n (len bdd-al)))
                     (<= (bdd-max-depth bdd2) (+ n (len bdd-al)))
                     (abs-bdd-al-okp bdd-al n)
                     (natp n)
                     (<= (bdd-al-max-depth al) n)
                     (bdds-compatible-for-al
                      (aig-q-compose aig1 al) bdd1 bdd-al n)
                     (bdds-compatible-for-al
                      (aig-q-compose aig2 al) bdd2 bdd-al n)

                     (case-split
                      ;;(and (implies (booleanp bdd1) exact1)
                           (implies exact1
                                    (bdd-equiv (aig-q-compose aig1 al) bdd1)))
                     (case-split
                      ;; (and (implies (booleanp bdd2) exact2)
                           (implies exact2
                                    (bdd-equiv (aig-q-compose aig2 al) bdd2)))
                     (<= 1 max-count)
                     (abs-memo-okp memo n al bdd-al)
                     (equal nxtbdd (qv (+ n (len bdd-al)))))
                (b* (((mv bdd aig & new-bdd-al new-nxtbdd exact)
                      (and-bddify-var-weakening bdd1 aig1 count1 exact1
                                                bdd2 aig2 count2 exact2
                                                max-count bdd-al nxtbdd))
                     (exact-bdd (q-and (aig-q-compose aig1 al)
                                       (aig-q-compose aig2 al))))
                  (and (<= (len bdd-al) (len new-bdd-al))
                       (suffixp bdd-al new-bdd-al)
                       (<= (bdd-max-depth bdd) (+ n (len new-bdd-al)))
                       (abs-bdd-al-okp new-bdd-al n)
                       (bdds-compatible-for-al
                        exact-bdd bdd new-bdd-al n)
                       (bdd-equiv (aig-q-compose aig al)
                                  exact-bdd)
                       ;; (implies (booleanp bdd) exact)
                       (implies exact
                                (bdd-equiv bdd exact-bdd))
                       (abs-memo-okp memo n al new-bdd-al)
                       (equal new-nxtbdd (qv (+ n (len new-bdd-al)))))))
       :hints (("Goal"
                :expand ((and-bddify-var-weakening bdd1 aig1 count1 exact1
                                                   bdd2 aig2 count2 exact2
                                                   max-count bdd-al nxtbdd))
                :do-not-induct t)
               (and stable-under-simplificationp
                    (cond ((member-equal '(not (equal (q-binary-and bdd1 bdd2) bdd1)) clause)
                           '(:use ((:instance bdds-compatible-degenerate-and1
                                    (bdd1f (aig-q-compose aig1 al))
                                    (bdd2f (aig-q-compose aig2 al))))))
                          ((member-equal '(not (equal (q-binary-and bdd1 bdd2) bdd2)) clause)
                            '(:use ((:instance bdds-compatible-degenerate-and2
                                    (bdd1f (aig-q-compose aig1 al))
                                    (bdd2f (aig-q-compose aig2 al))))))
                          (t
                           '(:use ((:instance bdds-compatible-q-ands-compatible
                                    (bdd1f (aig-q-compose aig1 al))
                                    (bdd2f (aig-q-compose aig2 al))))))))
               (and stable-under-simplificationp
                    (cond ((member-equal '(q-binary-and bdd1 bdd2) clause)
                           '(:use ((:instance bdds-compatible-with-boolean
                                    (bddf (q-and (aig-q-compose aig1 al)
                                                 (aig-q-compose aig2 al)))
                                    (bdd nil)))))))

               ;;              (:instance bdds-compatible-degenerate-and2
               ;;               (bdd1f (aig-q-compose aig1 al))
               ;;               (bdd2f (aig-q-compose aig2 al))))))
               ;; (and stable-under-simplificationp
               ;;      '(:in-theory (enable not booleanp mv-nth)))
               )))

   (defthm and-bddify-var-weakening-suffixp-rw
       (implies (and (suffixp x bdd-al)
                     (case-split (<= (bdd-max-depth bdd1) (+ n (len bdd-al))))
                     (case-split (<= (bdd-max-depth bdd2) (+ n (len bdd-al))))
                     (abs-bdd-al-okp bdd-al n)
                     (natp n)
                     (<= (bdd-al-max-depth al) n)
                     (bdds-compatible-for-al
                      (aig-q-compose aig1 al) bdd1 bdd-al n)
                     (bdds-compatible-for-al
                      (aig-q-compose aig2 al) bdd2 bdd-al n)

                     (case-split
                      ;;(and (implies (booleanp bdd1) exact1)
                           (implies exact1
                                    (bdd-equiv (aig-q-compose aig1 al) bdd1)))
                     (case-split
                      ;; (and (implies (booleanp bdd2) exact2)
                           (implies exact2
                                    (bdd-equiv (aig-q-compose aig2 al) bdd2)))
                     (<= 1 max-count)
                     (abs-memo-okp memo n al bdd-al)
                     (equal nxtbdd (qv (+ n (len bdd-al)))))
                (b* (((mv ?bdd ?aig & new-bdd-al ?new-nxtbdd ?exact)
                      (and-bddify-var-weakening bdd1 aig1 count1 exact1
                                                bdd2 aig2 count2 exact2
                                                max-count bdd-al nxtbdd)))
                  (suffixp x new-bdd-al)))
       :hints (("goal" :use and-bddify-var-weakening-ok
                :in-theory '(suffixp-transitive))))

   (local (add-bdd-pat (mv-nth 0 (and-bddify-var-weakening . &))))
   (local (add-bdd-pat (mv-nth 4 (and-bddify-var-weakening . &))))))

(encapsulate
  nil
  (local
   (progn
     (defun aig-bddify-var-weakening-induct (x al max-count fmemo memo bdd-al nxtbdd)
       (if (not (aig-atom-p x))
           (if (cdr x)
               (if (not (or (hons-get x memo) (hons-get x fmemo)))
                   (list (aig-bddify-var-weakening-induct (car x) al max-count fmemo memo
                                                          bdd-al nxtbdd)
                         (b* (((mv & & & fmemo memo bdd-al nxtbdd &)
                               (aig-bddify-var-weakening (car x) al max-count fmemo memo
                                                         bdd-al nxtbdd)))
                           (aig-bddify-var-weakening-induct (cdr x) al max-count fmemo memo
                                                            bdd-al nxtbdd)))
                 nil)
             (aig-bddify-var-weakening-induct (car x) al max-count fmemo memo
                                              bdd-al nxtbdd))
         (list x al max-count fmemo memo bdd-al nxtbdd)))

     (in-theory (e/d* (abs-fmemo-okp-hons-assoc-equal-rw1
                       abs-fmemo-okp-hons-assoc-equal-rw2)
                      (len not
                           aig-bddify-var-weakening)))

     (add-bdd-pat (mv-nth 0 (aig-bddify-var-weakening . &)))
     (add-bdd-pat (mv-nth 6 (aig-bddify-var-weakening . &)))))

  (local (defthm bdd-max-depth-when-booleanp
           (implies (booleanp x)
                    (equal (bdd-max-depth x) 0))
           :hints(("Goal" :in-theory (enable booleanp)))
           :rule-classes ((:rewrite :backchain-limit-lst 0))))

  (local (in-theory (disable and-bddify-var-weakening
                             aig-q-compose
                             ;and-bddify-var-weakening-ok
                             ;and-bddify-var-weakening-suffixp-rw
                             suffixp
                             aig-bddify-var-weakening
                             set::double-containment
                             aig-bddify-var-weakening-cache-insert
                             abs-fmemo-okp abs-memo-okp
                             ;; aig-bddify-var-weakening-cache-lookup
                             )))

  (defthm fmemo-ok-of-aig-bddify-var-weakening-cache-insert
    (implies (and (implies exact
                           (bdd-equiv (aig-q-compose x al)
                                      bdd))
                  (bdd-equiv (aig-q-compose x al)
                             (aig-q-compose aig al))
                  (abs-fmemo-okp fmemo al))
             (abs-fmemo-okp
              (mv-nth 0
                      (aig-bddify-var-weakening-cache-insert
                       exact x aig (list* bdd aig count) fmemo memo))
              al))
    :hints(("Goal" :in-theory (enable aig-bddify-var-weakening-cache-insert
                                      abs-fmemo-okp))))

  (defthm memo-ok-of-aig-bddify-var-weakening-cache-insert
    (implies (and (bdds-compatible-for-al
                   (aig-q-compose x al) bdd bdd-al n)
                  (bdd-equiv (aig-q-compose x al)
                             (aig-q-compose aig al))
                  (<= (bdd-max-depth bdd) (+ n (len bdd-al)))
                  (abs-memo-okp memo n al bdd-al))
             (abs-memo-okp
              (mv-nth 1
                      (aig-bddify-var-weakening-cache-insert
                       exact x aig (list* bdd aig count) fmemo memo))
              n al bdd-al))
    :hints(("Goal" :in-theory (enable aig-bddify-var-weakening-cache-insert
                                      abs-memo-okp))))


  (without-waterfall-parallelism
   (defthm aig-bddify-var-weakening-ok
     (implies (and (abs-bdd-al-okp bdd-al n)
                   (integerp n)
                   (<= (bdd-al-max-depth al) n)
                   (abs-fmemo-okp fmemo al)
                   (abs-memo-okp memo n al bdd-al)
                   (<= 1 max-count)
                   (equal nxtbdd (qv (+ n (len bdd-al)))))
              (b* (((mv bdd aig & new-fmemo new-memo new-bdd-al new-nxtbdd exact)
                    (aig-bddify-var-weakening
                     x al max-count fmemo memo bdd-al nxtbdd))
                   (exact-bdd (aig-q-compose x al)))
                (and (suffixp bdd-al new-bdd-al)
                     (<= (len bdd-al) (len new-bdd-al))
                     (<= (bdd-max-depth bdd) (+ n (len new-bdd-al)))
                     (abs-bdd-al-okp new-bdd-al n)
                     (bdds-compatible-for-al
                      exact-bdd bdd new-bdd-al n)
                     (bdd-equiv (aig-q-compose aig al) exact-bdd)
                     (implies exact
                              (bdd-equiv bdd exact-bdd))
                     (abs-memo-okp new-memo n al new-bdd-al)
                     (abs-fmemo-okp new-fmemo al)
                     (equal new-nxtbdd (qv (+ n (len new-bdd-al)))))))
     :hints (("goal" :induct (aig-bddify-var-weakening-induct
                              x al max-count fmemo memo bdd-al nxtbdd)
              :expand ((:free (nxtbdd)
                              (aig-bddify-var-weakening
                               x al max-count fmemo memo bdd-al nxtbdd)))
              :do-not-induct t)
             ;; ("Subgoal *1/4" :in-theory (enable aig-q-compose bdd-max-depth booleanp))
             ;; ("Subgoal *1/3" :in-theory (enable aig-q-compose-not-decomp-x booleanp))
             ;; ("Subgoal *1/2" :in-theory (disable qv)) ;;aig-q-compose-and-decomp-x))
             ;; ("Subgoal *1/1" :in-theory (e/d (aig-q-compose-and-decomp-x)
             ;;                                 (and-bddify-var-weakening
             ;;                                  qv len
             ;;                                  mv-nth-cons-meta
             ;;                                  hons-assoc-equal
             ;;                                  equal-of-booleans-rewrite
             ;;                                  ;; normalize-terms-such-as-a/a+b-+-b/a+b
             ;;                                  ;;                                             normalize-addends
             ;;                                  and-bddify-var-weakening-ok)))
             ;; (and (equal (car id) '(0 1))
             ;;      '(:restrict
             ;;        ((aig-bddify-var-weakening ((x x)) ((x t)) ((x nil))))
             ;;        :expand
             ;;        ((:free (nxtbdd)
             ;;                (aig-bddify-var-weakening
             ;;                 x al max-count fmemo memo bdd-al nxtbdd)))))


             (if (case-match id (((0 1) (1 &) . 0) t))
                 (with-quoted-forms
                  (b* (((mv bdd1 aig1 count1 fmemo memo bdd-al nxtbdd exact1)
                        (aig-bddify-var-weakening
                         (car x) al max-count fmemo memo bdd-al
                         (qv (+ n (len bdd-al)))))
                       ((mv bdd2 aig2 count2 & memo bdd-al nxtbdd exact2)
                        (aig-bddify-var-weakening
                         (cdr x) al max-count fmemo memo bdd-al nxtbdd)))
                    `(:use ((:instance
                             and-bddify-var-weakening-ok
                             . ,(var-fq-bindings
                                 (bdd1 aig1 count1 exact1 bdd2 aig2 count2 exact2
                                       bdd-al nxtbdd memo))))
                           :in-theory (disable and-bddify-var-weakening-ok
                                               and-bddify-var-weakening-suffixp-rw))))
               (value nil))
             ))))

(in-theory (disable aig-bddify-var-weakening))


;; Inductive invariant on some of the inputs/outputs of AIG-BDDIFY-VAR-WEAKENING.
(defun abs-args-okp (fmemo memo bdd-al nxtbdd al n)
  (and (integerp n)
       (<= (bdd-al-max-depth al) n)
       (abs-bdd-al-okp bdd-al n)
       (abs-fmemo-okp fmemo al)
       (abs-memo-okp memo n al bdd-al)
       (equal nxtbdd (qv (+ n (len bdd-al))))))







(defthm aig-bddify-var-weakening-ok-if-args-ok
  ;; Concept!!!  This theorem says that (1.) The BDD result is
  ;; "compatible" with the exact BDD, in the sense that BDD-AL
  ;; describes a way to make a substitution into the result to get the
  ;; exact BDD, and (2.) if EXACT is T, then the BDD returned is equal
  ;; to the exact BDD.
  (implies
   (and (abs-args-okp fmemo memo bdd-al nxtbdd al n)
        (<= 1 max-count))
   (b* (((mv bdd aig & new-fmemo new-memo new-bdd-al new-nxtbdd exact)
         (aig-bddify-var-weakening
          x al max-count fmemo memo bdd-al nxtbdd))
        (exact-bdd (aig-q-compose x al)))
       (and
        (abs-args-okp new-fmemo new-memo new-bdd-al new-nxtbdd al n)

        (suffixp bdd-al new-bdd-al)
        (<= (len bdd-al) (len new-bdd-al))

        (<= (bdd-max-depth bdd) (+ n (len new-bdd-al)))
        ;; 1.
        (bdds-compatible-for-al exact-bdd bdd new-bdd-al n)

        (bdd-equiv (aig-q-compose aig al) exact-bdd)
        ;; 2.
        (implies exact
                 (and (bdd-equiv bdd exact-bdd)
                      ;; (simplifiedp aig al)
                      ))))))

(defthm aig-bddify-var-weakening-ok-if-args-ok-2
  (implies (and (abs-args-okp fmemo memo bdd-al nxtbdd al n)
                (<= 1 max-count))
           (b* (((mv & aig & new-fmemo new-memo new-bdd-al new-nxtbdd &)
                 (aig-bddify-var-weakening
                  x al max-count fmemo memo bdd-al nxtbdd))
                (exact-bdd (aig-q-compose x al)))
             (and
              (abs-args-okp new-fmemo new-memo new-bdd-al new-nxtbdd al n)
              (bdd-equiv (aig-q-compose aig al) exact-bdd)))))


(defthm abs-args-okp-start
  (abs-args-okp 'fmemo 'memo 'bdd-al
                (qv (bdd-al-max-depth al))
                al (bdd-al-max-depth al)))

(in-theory (disable abs-args-okp))



(defthm ubdd-listp-aig-q-compose-list
  (implies (ubddp-val-alistp al)
           (ubdd-listp (aig-q-compose-list x al))))

(local
 (progn
   (in-theory (enable max))
   (in-theory (disable suffixp-len))))


(local (defthm max-depth-gte-bdd-max-depth
         (<= (bdd-max-depth x) (max-depth x))
         :hints(("Goal" :in-theory (enable bdd-max-depth max-depth ubdd-fix
                                           qcar qcdr)))
         :rule-classes ((:linear :trigger-terms ((max-depth x))))))


(defthm abs-recheck-exactness-ok
  (implies (and (bind-free '((bdd-al . bdd-al)) (bdd-al))
                (abs-fmemo-okp fmemo al)
                (integerp n)
                (abs-memo-okp memo n al bdd-al)
                (<= (bdd-al-max-depth al) n))
           (abs-fmemo-okp
            (mv-nth 0 (abs-recheck-exactness x fmemo memo done n))
            al))
  :hints (("goal" :induct (abs-recheck-exactness x fmemo memo done n)
           :in-theory (disable aig-q-compose
                               aig-q-compose-of-and-under-bdd-equiv))
          (and stable-under-simplificationp
               '(:use ((:instance bdds-compatible-bdd-max-depth-implies-equiv
                        (bddf (aig-q-compose x al))
                        (bdd (cadr (hons-assoc-equal x memo)))
                        (bdd-al bdd-al) (n n)))))))

(defthm abs-recheck-exactness-top-fmemo-ok
  (implies (and (bind-free '((bdd-al . bdd-al)) (bdd-al))
                (abs-memo-okp memo n al bdd-al)
                (abs-fmemo-okp fmemo al)
                (integerp n)
                (<= (bdd-al-max-depth al) n))
           (and (abs-fmemo-okp
                 (mv-nth 0 (abs-recheck-exactness-top x fmemo memo n))
                 al)
                (implies
                 (mv-nth 1 (abs-recheck-exactness-top x fmemo memo n))
                 (bdd-equiv (mv-nth 2 (abs-recheck-exactness-top
                                       x fmemo memo n))
                            (aig-q-compose x al)))))
  :hints (("goal" :in-theory (e/d ()
                                  (abs-recheck-exactness
                                   abs-fmemo-okp-hons-assoc-equal-rw1))
           :use ((:instance abs-fmemo-okp-hons-assoc-equal-rw1
                  (fmemo (mv-nth 0 (abs-recheck-exactness
                                    x fmemo memo 'done n)))))
           :do-not-induct t)))

(in-theory (disable abs-recheck-exactness-top))

(local (in-theory (enable abs-args-okp)))

(defthm abs-recheck-exactness-top-abs-args-okp
  (implies (and ; (abs-args-okp fmemo1 memo1 bdd-al1 nxtbdd1 al n)
                (abs-args-okp fmemo2 memo2 bdd-al2 nxtbdd2 al n))
           (b* (((mv new-fmemo exact bdd)
                 (abs-recheck-exactness-top x fmemo2 memo2 n)))
             (and (abs-args-okp new-fmemo memo2 bdd-al2 nxtbdd2 al n)
                  (implies exact
                           (bdd-equiv bdd (aig-q-compose x al))))))
  :hints (("goal" :in-theory (disable abs-recheck-exactness-top-fmemo-ok)
           :use ((:instance abs-recheck-exactness-top-fmemo-ok
                            (fmemo fmemo2) (bdd-al bdd-al2) (memo memo2))))))

(in-theory (disable abs-recheck-exactness-top abs-args-okp
                    abs-recheck-exactness-top-fmemo-ok))



(local
 (defthm abs-args-okp-change-fmemo
   (implies (and (abs-args-okp fmemo1 memo1 bdd-al1 nxtbdd1 al n1)
                 (abs-args-okp fmemo2 memo2 bdd-al2 nxtbdd2 al n2))
            (abs-args-okp fmemo1 memo2 bdd-al2 nxtbdd2 al n2))
   :hints(("Goal" :in-theory (enable abs-args-okp)))))

(encapsulate
 nil
 ;; (local (defthm abs-args-okp-implies-ubddp-val-alistp
 ;;          (implies (abs-args-okp fmemo memo bdd-al nxtbdd al n)
 ;;                   (ubddp-val-alistp al))
 ;;          :hints (("goal" :in-theory (enable abs-args-okp)))))
 (local (in-theory (disable ; aig-bddify-var-weakening-ok-if-args-ok
                            aig-bddify-var-weakening-ok bdd-max-depth
                            hons-assoc-equal ;; blp-implies-t
                            mv-nth-cons-meta
                            bdds-compatible-for-al-self)))

 (without-waterfall-parallelism
  (defthm aig-bddify-list-var-weakening-ok
    (implies (and (abs-args-okp fmemo memo bdd-al nxtbdd al n)
                  (<= 1 max-count))
             (b* ((ans
                   (aig-bddify-list-var-weakening
                    x al max-count fmemo memo bdd-al nxtbdd n))
                  ((mv bdds aigs new-fmemo ?new-memo exact)
                   ans)
                  (exact-bdds (aig-q-compose-list x al)))
               (and
                (abs-args-okp new-fmemo memo bdd-al nxtbdd al n)

                (bdd-equiv-list (aig-q-compose-list aigs al) exact-bdds)

                (implies exact
                         (and (bdd-equiv-list bdds exact-bdds)
                              ;; (fv-simplifiedp-list aigs al)
                              )))))
    :hints (("Goal" :induct (aig-bddify-list-var-weakening
                             x al max-count fmemo memo bdd-al nxtbdd n)
             :in-theory (enable aig-bddify-list-var-weakening))
            (if (equal id (parse-clause-id "Subgoal *1/2"))
                (with-quoted-forms
                 (b* (((mv & & & fmemo2 memo2 bdd-al2 nxtbdd2 &)
                       (aig-bddify-var-weakening
                        (car x) al max-count fmemo memo bdd-al nxtbdd)))
                   `(:use
                     ((:instance
                       aig-bddify-var-weakening-ok-if-args-ok-2
                       (x (car x)))
                      (:instance
                       abs-recheck-exactness-top-abs-args-okp
                       (x (car x)) ;;  (fmemo1 fmemo)
                       (fmemo2 ,(fq fmemo2))
                       (memo2 ,(fq memo2))
                       (bdd-al2 ,(fq bdd-al2))
                       (nxtbdd2 ,(fq nxtbdd2))))
                     :in-theory (e/d (aig-bddify-list-var-weakening ;;  mv-nth
                                      eql)
                                     (aig-bddify-var-weakening-ok-if-args-ok-2
                                      aig-bddify-var-weakening-ok-if-args-ok
                                      abs-recheck-exactness-top-abs-args-okp)))))
              (value nil))))))







(defthm apqs-memo-okp-atom
  (implies (and (syntaxp (quotep a))
                (atom a))
           (apqs-memo-okp a al)))

(defthm abs-fmemo-okp-atom
  (implies (and (syntaxp (quotep a))
                (atom a))
           (abs-fmemo-okp a al)))

(defthm aig-bddify-list-iter1-ok
  (implies (and (<= (bdd-al-max-depth al) var-depth)
                (integerp var-depth)
                (abs-fmemo-okp fmemo al)
                (equal nxtbdd (qv var-depth)))
           (b* ((ans (aig-bddify-list-iter1 tries x al fmemo nxtbdd var-depth
                                            maybe-wash-args map))
                ((mv bdds new-aigs exact) ans)
                (exact-bdds (aig-q-compose-list x al)))
             (and (implies exact (bdd-equiv-list bdds exact-bdds))
                  (bdd-equiv-list (aig-q-compose-list new-aigs al)
                                  exact-bdds))))
  :hints(("Goal" :in-theory (e/d* (abs-args-okp)
                                  ((:definition aig-bddify-list-iter1)
                                   abs-fmemo-okp
                                   aig-q-compose
                                   ubddp-val-alistp
                                   ; apqs-memo-not-okp-witness-rw
                                   aig-bddify-list-var-weakening
                                   aig-bddify-list-var-weakening-ok
                                   aig-bddify-list-x-weakening-ok
                                   aig-bddify-list-x-weakening
                                   apqs-memo-okp
                                   aig-q-compose-list
                                   ubdd-listp
                                   ; bdd-impl-to-equal-form
                                   nth len nth-len-lst
                                   (:rules-of-class
                                    :type-prescription :here))
                                  ((:type-prescription bdd-al-max-depth)
                                   (:type-prescription posfix-type)))
          :induct (aig-bddify-list-iter1 tries x al fmemo nxtbdd var-depth
                                         maybe-wash-args map)
          :expand ((aig-bddify-list-iter1 tries x al fmemo (qv var-depth)
                                          var-depth maybe-wash-args map)))
         '(:use ((:instance aig-bddify-list-x-weakening-ok
                            (max (posfix (cadr (car tries))))
                            (memo 'memo))
                 (:instance aig-bddify-list-var-weakening-ok
                  (memo 'memo)
                  (bdd-al 'bdd-al)
                  (max-count (posfix (cadr (car tries))))
                  (nxtbdd (qv var-depth))
                  (n var-depth))))))

(in-theory (disable aig-bddify-list-iter1))

(encapsulate
  nil
  (local
   (progn
     (defthm lookup-bddify-extract-bool-alist-when-not-in-valal
       (implies (or (not (hons-assoc-equal x valal))
                    (not (booleanp (cdr (hons-assoc-equal x valal)))))
                (equal (hons-assoc-equal x (bddify-extract-bool-alist keyal valal
                                                                      last))
                       (hons-assoc-equal x last)))
       :hints(("Goal" :in-theory (e/d (hons-assoc-equal)))))

     (defthm car-hons-assoc-equal
       (equal (car (hons-assoc-equal x al))
              (and (hons-assoc-equal x al) x))
       :hints(("Goal" :in-theory (enable hons-assoc-equal))))

     (defthm cons-x-cdr-hons-assoc-equal
       (implies (hons-assoc-equal x al)
                (equal (cons x (cdr (hons-assoc-equal x al)))
                       (hons-assoc-equal x al)))
       :hints(("Goal" :in-theory (enable hons-assoc-equal))))))

  (defthm lookup-bddify-extract-bool-alist
    (equal (hons-assoc-equal x (bddify-extract-bool-alist keyal valal last))
           (or (and (hons-assoc-equal x keyal)
                    (hons-assoc-equal x valal)
                    (booleanp (cdr (hons-assoc-equal x valal)))
                    (hons-assoc-equal x valal))
               (hons-assoc-equal x last)))
    :hints(("Goal" :in-theory (e/d (hons-assoc-equal))))))

(defthm aig-q-compose-of-aig-restrict-of-bddify-extract
  (implies (atom last)
           (bdd-equiv (aig-q-compose
                       (aig-restrict x (bddify-extract-bool-alist keyal al last))
                       al)
                      (aig-q-compose x al)))
  :hints(("Goal" :induct t)
         (and stable-under-simplificationp
              '(:in-theory (enable hons-assoc-equal)))))

(defthm aig-q-compose-list-of-aig-restrict-list-of-bddify-extract
  (implies (atom last)
           (bdd-equiv-list
            (aig-q-compose-list
             (aig-restrict-list x (bddify-extract-bool-alist keyal al last))
             al)
            (aig-q-compose-list x al)))
  :hints (("goal" :induct t)))

(local (defthm bdd-al-max-depth-<=-al-max-depth
         (<= (bdd-al-max-depth x) (al-max-depth x))
         :hints(("Goal" :in-theory (enable bdd-al-max-depth al-max-depth)))
         :rule-classes ((:linear :trigger-terms ((al-max-depth x)))
                        :rewrite)))

(defthm aig-bddify-list-ok
  (b* ((ans (aig-bddify-list tries x al maybe-wash-args))
       ((mv bdds new-aigs exact) ans)
       (exact-bdds (aig-q-compose-list x al)))
    (and (implies exact (bdd-equiv-list bdds exact-bdds))
         (bdd-equiv-list (aig-q-compose-list new-aigs al)
                         exact-bdds)))
  :hints(("Goal" :in-theory (e/d () (eval-bdd-cp-hint))
          :do-not-induct t)))

(in-theory (disable aig-bddify-list))


(defthm aig-bddify-list-x-weakening-true-listp
  (true-listp (mv-nth 0 (aig-bddify-list-x-weakening
                         lst al max-nodes fmemo memo))))

(defthm aig-bddify-list-var-weakening-true-listp
  (true-listp (mv-nth 0 (aig-bddify-list-var-weakening
                         lst al max-nodes fmemo memo bdd-al nxtbdd
                         var-depth))))

(defthm aig-bddify-list-iter1-true-listp
  (true-listp (mv-nth 0 (aig-bddify-list-iter1
                         tries x al fmemo nxtbdd var-depth maybe-wash-args map)))
  :hints(("Goal" :in-theory (e/d* (aig-bddify-list-iter1)
                                  (aig-bddify-list-x-weakening
                                   aig-bddify-list-var-weakening)))))

(defthm aig-bddify-list-true-listp
  (true-listp (mv-nth 0 (aig-bddify-list
                         tries x al maybe-wash-args)))
  :hints(("Goal" :in-theory (enable aig-bddify-list))))


(defun vars-to-bdd-bindings (x n)
  (declare (xargs :guard (natp n)))
  (let ((n (lnfix n)))
    (if (atom x)
        nil
      (hons-acons (car x) (qv n)
                  (vars-to-bdd-bindings (cdr x) (1+ n))))))

;; SAT procedure for an AIG using BDDIFY.
;; BOZO produce a satisfying assignment
(defund aig-bddify-sat (x)
  (declare (xargs :guard t))
  (b* ((vars (aig-vars x))
       (bindings (vars-to-bdd-bindings vars 0))
       ((mv bdd & exact)
        (ec-call (aig-bddify *bddify-default-tries*
                             x bindings nil))))
    (if exact
        (if (eval-bdd bdd (bdd-sat-dfs bdd))
            '(sat)
          '(unsat))
      '(failed))))

(defcong bdd-equiv-list bdd-equiv (car x) 1
  :hints(("Goal" :in-theory (enable default-car))))

(defcong bdd-equiv-list bdd-equiv-list (cdr x) 1
  :hints(("Goal" :in-theory (enable default-cdr))))

(defcong bdd-equiv bdd-equiv-list (cons a b) 1)
(defcong bdd-equiv-list bdd-equiv-list (cons a b) 2)

(encapsulate nil
  (local
   (progn
     (in-theory (enable aig-bddify-sat))
     (defthm ubddp-val-alistp-vars-to-bdd-bindings
       (acl2::ubddp-val-alistp (vars-to-bdd-bindings x n)))


     (local (include-book "arithmetic/top-with-meta" :dir :system))

     (defthm hons-assoc-equal-vars-to-bdd-bindings
       (implies (member-equal x vars)
                (equal (hons-assoc-equal x (vars-to-bdd-bindings vars n))
                       (cons x (qv (+ (nfix n) (- (len vars) (len (member-equal x vars))))))))
       :hints(("Goal" :in-theory (enable hons-assoc-equal))))


     (defun vars-to-bdd-env (vars aig-env)
       (if (atom vars)
           nil
         (cons (let ((look (hons-get (car vars) aig-env)))
                 (or (not look) (cdr look)))
               (vars-to-bdd-env (cdr vars) aig-env))))

     (defthm nth-vars-to-bdd-env
       (implies (< (nfix n) (len vars))
                (equal (nth n (vars-to-bdd-env vars aig-env))
                       (if (hons-assoc-equal (nth n vars) aig-env)
                           (cdr (hons-assoc-equal (nth n vars) aig-env))
                         t))))

     (defthm len-member-equal
       (implies (member-equal x vars)
                (and (< 0 (len (member-equal x vars)))
                     (<= (len (member-equal x vars)) (len vars))))
       :rule-classes :linear)

     (defthm nth-of-index
       (implies (member-equal x lst)
                (equal (nth (+ (len lst) (- (len (member-equal x lst)))) lst)
                       x)))

     (defthm idx-rewrite
       (implies (member-equal x vars)
                (< (nfix (+ (len vars) (- (len (member-equal x vars)))))
                   (len vars))))

     (defthm aig-q-compose-vars-to-bdd-env
       (implies (subsetp-equal (acl2::aig-vars x) vars)
                (equal (acl2::eval-bdd (acl2::aig-q-compose
                                        x (vars-to-bdd-bindings vars n))
                                       (append (make-list n)
                                               (vars-to-bdd-env vars aig-env)))
                       (acl2::aig-eval x aig-env)))
       :hints (("goal" :induct (acl2::aig-eval x aig-env)
                :in-theory (e/d (subsetp-equal
                                 acl2::aig-env-lookup
                                 acl2::aig-alist-lookup) (nfix)))
               (and stable-under-simplificationp
                    '(:in-theory (enable nfix)))))))

  (defthm aig-bddify-sat-correct-for-unsat
    (implies (not (equal (aig-eval x env) nil))
             (not (equal (car (aig-bddify-sat x)) 'unsat)))
    :hints (("goal" :use ((:instance aig-q-compose-vars-to-bdd-env
                           (n 0) (vars (aig-vars x))
                           (aig-env env))
                          (:instance bdd-sat-dfs-correct
                           (x (mv-nth 0 (aig-bddify *bddify-default-tries*
                                                    x (vars-to-bdd-bindings
                                                       (aig-vars x) 0) nil)))
                           (vars (vars-to-bdd-env (aig-vars x) env))))
             :in-theory (disable aig-q-compose-vars-to-bdd-env
                                 bdd-sat-dfs-correct)
             :do-not-induct t)))) 
