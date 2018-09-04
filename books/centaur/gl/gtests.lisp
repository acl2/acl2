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
(include-book "hyp-fix")
(include-book "gtypes")
(include-book "tools/mv-nth" :dir :system)
(local (include-book "gtype-thms"))
(local (include-book "bfr-reasoning"))
(set-inhibit-warnings "theory")

(define mk-g-bdd-ite (bdd then else hyp)
  (let ((test (hf bdd)))
    (cond ((th test) then)
          ((fh test) else)
          (t (mk-g-ite (mk-g-boolean bdd) then else))))
  ///
  (def-hyp-congruence mk-g-bdd-ite)

  (defthm mk-g-bdd-ite-correct
    (implies (double-rewrite (bfr-hyp-eval hyp (car env)))
             (equal (generic-geval (mk-g-bdd-ite bdd then else hyp) env)
                    (if (bfr-eval bdd (car env))
                        (generic-geval then env)
                      (generic-geval else env))))
    :hints(("Goal" :in-theory (enable true-under-hyp
                                      false-under-hyp))
           (bfr-reasoning)))

  (defthm mk-g-bdd-ite-of-bfr-hyp-fix
    (equal (mk-g-bdd-ite bdd then else (bfr-hyp-fix hyp))
           (mk-g-bdd-ite bdd then else hyp)))

  (defthm gobj-depends-on-of-mk-g-bdd-ite
    (implies (and (not (pbfr-depends-on k p bdd))
                  (not (gobj-depends-on k p then))
                  (not (gobj-depends-on k p else)))
             (not (gobj-depends-on k p (mk-g-bdd-ite bdd then else hyp))))
    :hints(("Goal" :in-theory (enable mk-g-bdd-ite)))))



;; Returns an MV of: (COND, UNDEF, OBJ).
;; UNDEF is a BDD giving the condition under which X is a G-APPLY object
;; The aggregate such object (cases containing only G-APPLYs) is passed back as OBJ.
;; COND is a BDD giving the conditions under which X is nonnil versus nil, when
;; it is not a G-APPLY.
;; All of the return values are <= hyp.
(with-output :off (prove event)
  (define gtests (x hyp)
    :returns (mv nonnilp unknownp unknown-obj same-hyp)
    :verify-guards nil
    (let* ((hyp (lbfr-hyp-fix hyp)))
      (if (atom x)
          (mv (hf (if x t nil))
              (hf nil) nil hyp)
        (pattern-match x
          ((g-concrete obj)
           (mv (hf (if obj t nil))
               (hf nil) nil hyp))
          ((g-boolean bool) (mv (hf bool) (hf nil) nil hyp))
          ((g-integer &) (mv (hf t) (hf nil) nil hyp))
          ((g-apply & &) (mv (hf nil) (hf t) x hyp))
          ((g-var &)   (mv (hf nil) (hf t) x hyp))
          ((g-ite test then else)
           (b* (((mv cc uc oc hyp)
                 (gtests test hyp))
                ((mv contra1 hyp undo1) (bfr-assume (bfr-or cc uc) hyp))
                ((when contra1) ;; test is always false -- cannot be either unknown (uc) or true (cc)
                 (b* ((hyp (bfr-unassume hyp undo1)))
                   (gtests else hyp)))
                ((mv c1 u1 o1 hyp) (gtests then hyp))
                (hyp (bfr-unassume hyp undo1))
                ((mv contra0 hyp undo0) (bfr-assume (bfr-or (hf (bfr-not cc)) uc) hyp))
                ((when contra0)
                 (b* ((hyp (bfr-unassume hyp undo0)))
                   (mv (hf c1) (hf u1) o1 hyp)))
                ((mv c0 u0 o0 hyp) (gtests else hyp))
                (hyp (bfr-unassume hyp undo0))
                ((when (and (eq uc nil)
                            (eq u1 nil)
                            (eq u0 nil)))
                 ;; common case
                 (mv (hf (bfr-ite cc c1 c0)) nil nil hyp))

                ;;    (known-ans (hf (bfr-ite cc c1 c0)))
                ;;    (unknown (hf (bfr-or uc (bfr-or u1 u0))))
                ;;    (obj (mk-g-ite (mk-g-bdd-ite uc oc (mk-g-boolean cc) hyp)
                ;;                   (mk-g-bdd-ite u1 o1 (mk-g-boolean c1) hyp)
                ;;                   (mk-g-bdd-ite u0 o0 (mk-g-boolean c0) hyp))))
                ;; (mv known-ans unknown obj hyp)))
                (known-ans (hf (bfr-ite cc c1 c0)))

                ;; To have a known value when the condition is unknown,
                ;; both branches must have known values that are equal.
                ;; If the condition is known, the branch indicated must be
                ;; known.  This gives the negation of that condition.
                (unknown (hf (cond ((eq uc t) (bfr-or (bfr-or u1 u0)
                                                      (bfr-xor c1 c0)))
                                   ((eq uc nil) (bfr-ite cc u1 u0))
                                   (t (bfr-ite
                                       uc
                                       (bfr-or (bfr-or u1 u0)
                                               (bfr-xor c1 c0))
                                       (bfr-ite cc u1 u0)))))))
             (if (eq unknown nil)
                 (mv known-ans unknown nil hyp)
               (b* ( ;; When do we have u0 and when do we have u1?
                    (unknown-cond
                     (mk-g-bdd-ite uc oc (mk-g-boolean cc) hyp))

                    (unknown-obj1
                     (mk-g-bdd-ite u1 o1 (mk-g-boolean c1) hyp))

                    (unknown-obj0
                     (mk-g-bdd-ite u0 o0 (mk-g-boolean c0) hyp))

                    ;; Unknown object to return
                    (unknown-obj
                     (mk-g-ite unknown-cond
                               unknown-obj1
                               unknown-obj0)))
                 (mv known-ans unknown unknown-obj hyp)))))

          (& (mv (hf t) (hf nil) nil hyp)))))
    ///
    (verify-guards gtests
      :hints(("Goal" :in-theory (disable gtests))))

    (def-hyp-congruence gtests
      :pres-hints (("Goal" :in-theory (disable (:d gtests))
                    :induct (gtests x hyp))
                   '(:expand ((gtests x hyp))))
      :hyp-fix-hints (("goal" :expand ((gtests x hyp)
                                       (gtests x (bfr-hyp-fix hyp))))))))

(in-theory (disable (:definition gtests)))



(local
 (progn


   (defthmd bfr-eval-nonnil-forward
     (implies (bfr-eval x y) x)
     :rule-classes :forward-chaining)

   (local (in-theory (enable bfr-eval-nonnil-forward)))




   (defun-nx gnuo-ind (x hyp)
     (let ((hyp (lbfr-hyp-fix hyp)))
       (if (atom x)
           hyp
         (pattern-match x
           ((g-ite test then else)
            (b* ((?ign (gnuo-ind test hyp))
                 ((mv ?cc ?uc ?oc ?hypx) (gtests test hyp))
                 ((mv ?contra1 hyp1 ?undo1) (bfr-assume (bfr-or cc uc) hyp))
                 ((mv ?contra0 hyp0 ?undo0) (bfr-assume (bfr-or (hf (bfr-not cc)) uc) hyp)))
              (if contra1
                  (gnuo-ind else hyp)
                (if contra0
                    (gnuo-ind then hyp1)
                  (list (gnuo-ind then hyp1)
                        (gnuo-ind else hyp0))))))
           (& hyp)))))

   ;; (defun gnuo-ind (x hyp)
   ;;   (if (atom x)
   ;;       hyp
   ;;     (pattern-match x
   ;;       ((g-concrete &)
   ;;        hyp)
   ;;       ((g-boolean &) hyp)
   ;;       ((g-number &) hyp)
   ;;       ((g-apply & &) hyp)
   ;;       ((g-var &)  hyp)
   ;;       ((g-ite test then else)
   ;;        (b* ((?foo
   ;;              (gnuo-ind test hyp))
   ;;             ((mv cc uc &)
   ;;              (gtests test hyp))
   ;;             (cc-t (th cc))
   ;;             (cc-nil (fh cc)))
   ;;          (cond
   ;;           ((and (fh uc) cc-t)
   ;;            (gnuo-ind then hyp))
   ;;           ((and (fh uc) cc-nil)
   ;;            (gnuo-ind else hyp))
   ;;           (t (b* ((hyp1 (bfr-or cc uc))
   ;;                   (hyp0 (bfr-or (hf (bfr-not cc)) uc)))
   ;;                (list (gnuo-ind then hyp1)
   ;;                      (gnuo-ind else hyp0)))))))
   ;;       (& hyp))))



   (local
    (in-theory (disable (:definition generic-geval)
                        bfr-eval bfr-eval-list
                        bfr-eval-booleanp)))))

(local
 (progn

   (defthm gtests-hyp-fixedp
     (and (hyp-fixedp (mv-nth 0 (gtests x hyp)) hyp)
          (hyp-fixedp (mv-nth 1 (gtests x hyp)) hyp))
     :hints (("goal" :induct (gnuo-ind x hyp)
              :in-theory (enable (:i gtests))
              :expand ((gtests x hyp)))
             (and stable-under-simplificationp
                  '(:in-theory (enable hyp-fixedp)))
             ;; (and (subgoal-of "Subgoal *1/" id)
             ;;      '(:expand ((gtests x hyp))))
             ))




   (add-bfr-pat (mv-nth 0 (gtests . &)))
   (add-bfr-pat (mv-nth 1 (gtests . &)))



   (local (bfr-reasoning-mode t))

   (local (in-theory (disable* hyp-fix-of-hyp-fixedp
                               (:type-prescription bfr-eval)
                               (:type-prescription true-under-hyp)
                               (:type-prescription false-under-hyp)
                               (:type-prescription q-implies-fn)
                               (:type-prescription bfr-ite-fn)
                               (:type-prescription booleanp)
                               equal-of-booleans-rewrite
                               default-car default-cdr
                               bfr-eval-nonnil-forward
                               hons-assoc-equal
                               not)))
   (local (in-theory (enable true-under-hyp-point
                             false-under-hyp-point)))
   ;; (defun expand-hyps1 (fns clause)
   ;;   (if (atom clause)
   ;;       nil
   ;;     (let ((lit (car clause)))
   ;;       (case-match lit
   ;;         (('not (fn . args))
   ;;          (if (member fn fns)
   ;;              (cons (cons fn args)
   ;;                    (expand-hyps1 fns (cdr clause)))
   ;;            (expand-hyps1 fns (cdr clause))))
   ;;         (& (expand-hyps1 fns (cdr clause)))))))

   ;; (defun expand-hyps (fns clause)
   ;;   (let ((lst (expand-hyps1 fns clause)))
   ;;     (and lst (list :computed-hint-replacement t :expand lst))))

   (local (in-theory (disable gtests
                              generic-geval
                              set::double-containment
                              tag-when-atom
                              generic-geval-non-cons)))


   (local (in-theory (disable bfr-assume-correct
                              true-under-hyp-point
                              false-under-hyp-point
                              true-listp
                              mv-nth-cons-meta
                              (:t mk-g-bdd-ite)
                              (:t mk-g-boolean)
                              (:t bfr-hyp-fix)
                              bfr-hyp-fix-when-hyp$ap
                              (:t bfr-hyp-eval)
                              set::sets-are-true-lists
                              )))

   (defthm gtests-correct
     (mv-let (cc uc uo)
       (gtests x hyp)
       (implies (bfr-hyp-eval hyp (car env))
                (iff (generic-geval x env)
                     (if (bfr-eval uc (car env))
                         (generic-geval uo env)
                       (bfr-eval cc (car env))))))
     :hints (("Goal" :induct (gnuo-ind x hyp)
              :expand ((gtests x hyp)
                       (generic-geval x env)
                       (generic-geval nil env))
              :in-theory (disable bfr-assume-correct
                                  true-under-hyp-point
                                  false-under-hyp-point)
              ;; :in-theory (e/d* ())
              :do-not-induct t)
             ;; (and stable-under-simplificationp
             ;;      '(:expand
             ;;        ((gtests x hyp)
             ;;         (generic-geval x env)
             ;;         (generic-geval nil env)
             ;;         (gtests nil hyp))
             ;;        :do-not '(generalize
             ;;                  fertilize
             ;;                  eliminate-destructors)))
             (and stable-under-simplificationp
                  '(:in-theory (e/d (bfr-assume-correct)
                                    (true-under-hyp-point
                                     false-under-hyp-point)))))
     :rule-classes nil)))

(defthm gobj-depends-on-of-gtests
  (implies (not (gobj-depends-on k p x))
           (mv-let (cc uc uo)
             (gtests x hyp)
             (and (not (pbfr-depends-on k p cc))
                  (not (pbfr-depends-on k p uc))
                  (not (gobj-depends-on k p uo)))))
  :hints (("goal" :induct (gnuo-ind x hyp)
           :expand ((gtests x hyp))
           :in-theory (e/d ()))
          ;; (and stable-under-simplificationp
          ;;      '(:expand ((gtests x hyp)
          ;;                 (gtests nil hyp)
          ;;                 (gobj-depends-on k p x))))
          ))



(defthm gtests-nonnil-correct
  (b* (((mv ?nonnil ?unknown ?obj) (gtests x hyp)))
    (implies (and (not (bfr-eval unknown (car env)))
                  (bfr-hyp-eval hyp (car env)))
             (equal (bfr-eval nonnil (car env))
                    (if (generic-geval x env) t nil))))
  :hints (("goal" :use
           ((:instance gtests-correct))
           :in-theory (enable (:type-prescription bfr-eval)))))

(defthm gtests-obj-correct
  (b* (((mv ?nonnil ?unknown ?obj) (gtests x hyp)))
    (implies (and (bfr-eval unknown (car env))
                  (bfr-hyp-eval hyp (car env)))
             (iff (generic-geval obj env)
                  (generic-geval x env))))
  :hints (("goal" :use
           ((:instance gtests-correct)))))




;; Useful rules
(defthm bfr-assume-of-gtests-possibly-true
  (b* (((mv nonnil unknown &) (gtests obj hyp))
       ((mv & hyp1 &) (bfr-assume$a (bfr-binary-or nonnil unknown) hyp)))
    (implies (and (generic-geval obj env)
                  (bfr-hyp-eval hyp (car env)))
             (bfr-hyp-eval hyp1 (car env)))))


(defthm bfr-assume-of-gtests-possibly-false
  (b* (((mv nonnil unknown &) (gtests obj hyp))
       ((mv & hyp1 &) (bfr-assume$a (bfr-binary-or (bfr-not nonnil) unknown) hyp)))
    (implies (and (not (generic-geval obj env))
                  (bfr-hyp-eval hyp (car env)))
             (bfr-hyp-eval hyp1 (car env)))))
