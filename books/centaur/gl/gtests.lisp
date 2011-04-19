

(in-package "GL")

(set-inhibit-warnings "theory")

(include-book "hyp-fix")
(include-book "gtypes")
(local (include-book "gtype-thms"))
(local (include-book "hyp-fix-logic"))

(include-book "tools/mv-nth" :dir :system)

(defun mk-g-bdd-ite (bdd then else hyp)
  (declare (xargs :guard (and (bfr-p bdd)
                              (bfr-p hyp)
                              (gobjectp then)
                              (gobjectp else))))
  (let ((bdd (bfrfix bdd))
        (then (mbe :logic (gobj-fix then) :exec then))
        (else (mbe :logic (gobj-fix else) :exec else))
        (hyp (bfrfix hyp)))
    (let ((test (hf bdd)))
      (cond ((th test) then)
            ((fh test) else)
            (t (mk-g-ite (mk-g-boolean bdd) then else))))))

(defthm mk-g-bdd-ite-gobjectp
  (gobjectp (mk-g-bdd-ite bdd then else hyp)))

(defthm mk-g-bdd-ite-correct
  (implies (bfr-eval hyp (car env))
           (equal (generic-geval (mk-g-bdd-ite bdd then else hyp) env)
                  (if (bfr-eval bdd (car env))
                      (generic-geval then env)
                    (generic-geval else env))))
  :hints(("Goal" :in-theory (enable true-under-hyp
                                    false-under-hyp))
         (bfr-reasoning)))

(in-theory (disable mk-g-bdd-ite))



;; Returns an MV of: (COND, UNDEF, OBJ).
;; UNDEF is a BDD giving the condition under which X is a G-APPLY object
;; The aggregate such object (cases containing only G-APPLYs) is passed back as OBJ.
;; COND is a BDD giving the conditions under which X is nonnil versus nil, when
;; it is not a G-APPLY.
;; All of the return values are <= hyp.
(defun gobj-nonnil-unknown-obj (x hyp)
  (declare (xargs :guard (and (gobjectp x) (bfr-p hyp))
                  :verify-guards nil))
  (if (atom x)
      (mv (hf (if x t nil))
          (hf nil) nil)
    (pattern-match x
      ((g-concrete obj)
       (mv (hf (if obj t nil))
           (hf nil) nil))
      ((g-boolean bool) (mv (hf bool) (hf nil) nil))
      ((g-number &) (mv (hf t) (hf nil) nil))
      ((g-apply & &) (mv (hf nil) (hf t) x))
      ((g-var &)   (mv (hf nil) (hf t) x))
      ((g-ite test then else)
       (b* (((mv cc uc oc)
             (gobj-nonnil-unknown-obj test hyp))
            (cc-t (th cc))
            (cc-nil (fh cc)))
         (cond
          ((and (fh uc) cc-t)
           (gobj-nonnil-unknown-obj then hyp))
          ((and (fh uc) cc-nil)
           (gobj-nonnil-unknown-obj else hyp))
          (t (b* ((uc-t (th uc))
                  (uc-nil (fh uc))
                  (hyp1 (bfr-or cc uc))
                  ((mv c1 u1 o1) (gobj-nonnil-unknown-obj then hyp1))
                  (hyp0 (bfr-or (hf (bfr-not cc)) uc))
                  ((mv c0 u0 o0) (gobj-nonnil-unknown-obj else hyp0))
                  ;; maybe should be able to prove this is hyp-fixed:
                  (known-ans (hf (bfr-ite cc c1 c0)))

                  ;; To have a known value when the condition is unknown,
                  ;; both branches must have known values that are equal.
                  ;; If the condition is known, the branch indicated must be
                  ;; known.  This gives the negation of that condition.
                  (unknown (hf (cond (uc-t (bfr-or (bfr-or u1 u0)
                                                 (bfr-xor c1 c0)))
                                     (uc-nil (bfr-ite cc u1 u0))
                                     (t (bfr-ite
                                         uc
                                         (bfr-or (bfr-or u1 u0)
                                               (bfr-xor c1 c0))
                                         (bfr-ite cc u1 u0)))))))
               (if (fh unknown)
                   (mv known-ans unknown nil)
                 (b* ( ;; When do we have u0 and when do we have u1?
                      (unknown-cond
                       (mk-g-bdd-ite uc oc (mk-g-boolean cc) hyp))

                      (unknown-obj1
                       (mk-g-bdd-ite u1 o1 (mk-g-boolean c1) hyp1))

                      (unknown-obj0
                       (mk-g-bdd-ite u0 o0 (mk-g-boolean c0) hyp0))

                      ;; Unknown object to return
                      (unknown-obj
                       (mk-g-ite unknown-cond
                                     unknown-obj1
                                     unknown-obj0)))
                   (mv known-ans unknown unknown-obj))))))))
      (& (mv (hf t) (hf nil) nil)))))


(in-theory (disable (:definition gobj-nonnil-unknown-obj)))



(local
 (progn


   (defthmd bfr-eval-nonnil-forward
     (implies (bfr-eval x y) x)
     :rule-classes :forward-chaining)

   (local (in-theory (enable bfr-eval-nonnil-forward)))




   (defun gnuo-ind (x hyp)
     (if (atom x)
         hyp
       (pattern-match x
         ((g-concrete &)
          hyp)
         ((g-boolean &) hyp)
         ((g-number &) hyp)
         ((g-apply & &) hyp)
         ((g-var &)  hyp)
         ((g-ite test then else)
          (b* ((?foo
                (gnuo-ind test hyp))
               ((mv cc uc &)
                (gobj-nonnil-unknown-obj test hyp))
               (cc-t (th cc))
               (cc-nil (fh cc)))
            (cond
             ((and (fh uc) cc-t)
              (gnuo-ind then hyp))
             ((and (fh uc) cc-nil)
              (gnuo-ind else hyp))
             (t (b* ((hyp1 (bfr-or cc uc))
                     (hyp0 (bfr-or (hf (bfr-not cc)) uc)))
                  (list (gnuo-ind then hyp1)
                        (gnuo-ind else hyp0)))))))
         (& hyp))))



   (local 
    (in-theory (disable (:definition generic-geval)
                        bfr-eval bfr-p bfr-eval-list
                        components-to-number-alt-def
                        gobjectp gobjectp-def
                        bfr-eval-booleanp)))



   (defthm bfr-p-gobj-nonnil-unknown-obj
     (implies (and (gobjectp x) (bfr-p hyp))
              (and (bfr-p (mv-nth 0 (gobj-nonnil-unknown-obj x hyp)))
                   (bfr-p (mv-nth 1 (gobj-nonnil-unknown-obj x hyp)))))
     :hints ((and (subgoal-of "Subgoal *1/" id)
                  '(:expand ((gobj-nonnil-unknown-obj x hyp))))))

   (defthm gobjectp-gobj-nonnil-unknown-obj
     (implies (and (gobjectp x) (bfr-p hyp))
              (gobjectp (mv-nth 2 (gobj-nonnil-unknown-obj x hyp))))
     :hints ((and (subgoal-of "Subgoal *1/" id)
                  '(:expand ((gobj-nonnil-unknown-obj x hyp))))))))



(verify-guards gobj-nonnil-unknown-obj
               :hints (("goal" :do-not-induct t)))

(local
 (progn


   (add-bfr-fn-pat hyp-fix)

   (defthm gobj-nonnil-unknown-obj-hyp-fixedp
     (implies (and (gobjectp x) (bfr-p hyp))
              (and (hyp-fixedp (mv-nth 0 (gobj-nonnil-unknown-obj x hyp)) hyp)
                   (hyp-fixedp (mv-nth 1 (gobj-nonnil-unknown-obj x hyp)) hyp)))
     :hints ((and (subgoal-of "Subgoal *1/" id)
                  '(:expand ((gobj-nonnil-unknown-obj x hyp))))))




   (add-bfr-pat (mv-nth 0 (gobj-nonnil-unknown-obj . &)))
   (add-bfr-pat (mv-nth 1 (gobj-nonnil-unknown-obj . &)))



   (local (bfr-reasoning-mode t))

   (local (in-theory (disable* hyp-fix-of-hyp-fixedp
                               (:type-prescription bfr-eval)
                               (:type-prescription true-under-hyp)
                               (:type-prescription false-under-hyp)
                               (:type-prescription bfr-p)
                               (:type-prescription gobjectp)
                               (:type-prescription q-implies-fn)
                               (:type-prescription g-ite-p)
                               (:type-prescription g-var-p)
                               (:type-prescription g-apply-p)
                               (:type-prescription bfr-ite-fn)
                               (:type-prescription booleanp)
                               equal-of-booleans-rewrite
                               tag-when-g-var-p
                               g-ite-p-when-wrong-tag
                               g-var-p-when-wrong-tag
                               tag-when-g-number-p
                               tag-when-g-boolean-p
                               tag-when-g-concrete-p
                               default-car default-cdr
                               bfr-eval-nonnil-forward
                               generic-geval-non-gobjectp
                               gobj-fix-when-not-gobjectp
                               hons-assoc-equal
                               break-g-number
                               not
                               (:ruleset gl-tag-forward))))
   (local (in-theory (enable true-under-hyp-point
                             false-under-hyp-point)))
   (defun expand-hyps1 (fns clause)
     (if (atom clause)
         nil
       (let ((lit (car clause)))
         (case-match lit
           (('not (fn . args))
            (if (member fn fns)
                (cons (cons fn args)
                      (expand-hyps1 fns (cdr clause)))
              (expand-hyps1 fns (cdr clause))))
           (& (expand-hyps1 fns (cdr clause)))))))

   (defun expand-hyps (fns clause)
     (let ((lst (expand-hyps1 fns clause)))
       (and lst (list :computed-hint-replacement t :expand lst))))


   (defthm gobj-nonnil-unknown-obj-correct
     (mv-let (cc uc uo)
       (gobj-nonnil-unknown-obj x hyp)
       (implies (and (gobjectp x)
                     (bfr-p hyp)
                     (bfr-eval hyp (car env)))
                (iff (generic-geval x env)
                     (if (bfr-eval uc (car env))
                         (generic-geval uo env)
                       (bfr-eval cc (car env))))))
     :hints (("Goal" :induct (gnuo-ind x hyp)
              :in-theory (e/d* ((:ruleset gl-wrong-tag-rewrites))
                               (gobj-nonnil-unknown-obj
                                generic-geval
                                generic-geval-non-cons))
              :do-not-induct t)
             (and stable-under-simplificationp
                  '(:expand
                    ((gobj-nonnil-unknown-obj x hyp)
                     (gobj-nonnil-unknown-obj nil hyp)
                     (generic-geval x env)
                     (generic-geval nil env))
                    :do-not '(generalize
                              fertilize
                              eliminate-destructors))))
     :rule-classes nil)))






;; BOZO The conses produced by this function are unnecessary except that we
;; need to figure out how to deal with mv-lets that get translated to a form
;; where they can't then be submitted.
(defun gtests (test hyp)
  (declare (xargs :guard (and (gobjectp test) (bfr-p hyp))))
  (let ((test (mbe :logic (gobj-fix test) :exec test))
        (hyp (bfrfix hyp)))
    (mv-let (nonnil unknown obj)
      (gobj-nonnil-unknown-obj test hyp)
      (list* nonnil unknown obj))))

(defun gtestsp (tests)
  (declare (xargs :guard t))
  (and (consp tests)
       (consp (cdr tests))
       (bfr-p (car tests))
       (bfr-p (cadr tests))
       (gobjectp (cddr tests))))


(defun gtests-nonnil (tests)
  (declare (xargs :guard (gtestsp tests)))
  (car tests))

(defun gtests-unknown (tests)
  (declare (xargs :guard (gtestsp tests)))
  (cadr tests))

(defun gtests-obj (tests)
  (declare (xargs :guard (gtestsp tests)))
  (cddr tests))



(defthm gtestsp-gtests
  (gtestsp (gtests test hyp)))

(defthm gtests-wfp
  (let ((tests (gtests test hyp)))
    (and (gobjectp (gtests-obj tests))
         (bfr-p (gtests-nonnil tests))
         (bfr-p (gtests-unknown tests))
         (bfr-p (gtests-nonnil tests))
         (bfr-p (gtests-unknown tests))
;;          (hyp-fixedp (gtests-nonnil tests) hyp)
;;          (hyp-fixedp (gtests-unknown tests) hyp)
         )))


(defthm gtests-nonnil-correct
  (implies (and (not (bfr-eval (gtests-unknown (gtests x hyp)) (car env)))
                (bfr-eval hyp (car env)))
           (equal (bfr-eval (gtests-nonnil (gtests x hyp)) (car env))
                  (if (generic-geval x env) t nil)))
  :hints (("goal" :use
           ((:instance gobj-nonnil-unknown-obj-correct
                       (x (gobj-fix x)) (hyp (bfr-fix hyp))))
           :in-theory (enable (:type-prescription bfr-eval)))))

(defthm gtests-obj-correct
  (implies (and (bfr-eval (gtests-unknown (gtests x hyp)) (car env))
                (bfr-eval hyp (car env)))
           (iff (generic-geval (gtests-obj (gtests x hyp)) env)
                (generic-geval x env)))
  :hints (("goal" :use
           ((:instance gobj-nonnil-unknown-obj-correct
                       (x (gobj-fix x)) (hyp (bfr-fix hyp)))))))

(in-theory (disable gtests gtestsp gtests-unknown gtests-obj gtests-nonnil))






