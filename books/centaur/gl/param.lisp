

(in-package "GL")

(include-book "shape-spec")


(local (include-book "gtype-thms"))
(local (include-book "data-structures/no-duplicates" :dir :system))
(local (include-book "tools/mv-nth" :dir :system))
(local (include-book "ihs/ihs-lemmas" :dir :system))

(include-book "centaur/ubdds/param" :dir :system)
(include-book "centaur/ubdds/lite" :dir :system)
(include-book "../aig/misc")
(local (include-book "../aig/eval-restrict"))

(local (in-theory (disable acl2::append-of-nil)))

(defun bfr-to-param-space (p x)
  (declare (xargs :guard t)
           (ignorable p))
  (bfr-case :bdd (acl2::to-param-space p x)
            :aig (acl2::aig-restrict
                  x (acl2::aig-extract-iterated-assigns-alist p 10))))

(defun bfr-list-to-param-space (p x)
  (declare (xargs :guard t)
           (ignorable p))
  (bfr-case :bdd (acl2::to-param-space-list p x)
            :aig (acl2::aig-restrict-list
                  x (acl2::aig-extract-iterated-assigns-alist p 10))))

;; (local
;;  (defthm bfr-p-to-param-space
;;    (implies (bfr-p x)
;;             (bfr-p (bfr-to-param-space p x)))
;;    :hints(("Goal" :in-theory (enable bfr-p)))))

;; (local
;;  (defthm bfr-listp-to-param-space-list
;;    (implies (bfr-listp lst)
;;             (bfr-listp (bfr-list-to-param-space p lst)))
;;    :hints(("Goal" :in-theory (enable bfr-listp bfr-p)))))

(in-theory (disable bfr-to-param-space bfr-list-to-param-space))

(defund gnumber-to-param-space (n p)
  (declare (xargs :guard t))
  (b* (((mv rnum rden inum iden) (break-g-number n)))
    (mk-g-number (bfr-list-to-param-space p rnum)
                 (bfr-list-to-param-space p rden)
                 (bfr-list-to-param-space p inum)
                 (bfr-list-to-param-space p iden))))
  ;; (and (consp n)
  ;;      (cons (bfr-list-to-param-space p (car n))
  ;;            (and (consp (cdr n))
  ;;                 (cons (bfr-list-to-param-space p (cadr n))
  ;;                       (and (consp (cddr n))
  ;;                            (cons (bfr-list-to-param-space p (caddr n))
  ;;                                  (and (consp (cdddr n))
  ;;                                       (list (bfr-list-to-param-space
  ;;                                              p (cadddr n)))))))))))

;; (local
;;  (defthm wf-g-numberp-gnumber-to-param-space
;;    (implies (wf-g-numberp n)
;;             (wf-g-numberp (gnumber-to-param-space n p)))
;;    :hints(("Goal" :in-theory (enable wf-g-numberp gnumber-to-param-space)))))

(mutual-recursion
 (defun gobj-to-param-space (x p)
   (declare (xargs :guard t
                   :verify-guards nil))
   (if (atom x)
       x
     (pattern-match x
       ((g-concrete &) x)
       ((g-boolean b) (mk-g-boolean (bfr-to-param-space p b)))
       ((g-number n) (gnumber-to-param-space n p))
       ((g-ite if then else)
        (mk-g-ite (gobj-to-param-space if p)
                  (gobj-to-param-space then p)
                  (gobj-to-param-space else p)))
       ((g-apply fn args) (g-apply fn (gobj-list-to-param-space args p)))
       ((g-var &) x)
       (& (gl-cons (gobj-to-param-space (car x) p)
                   (gobj-to-param-space (cdr x) p))))))
 (defun gobj-list-to-param-space (x p)
   (declare (xargs :guard t))
   (if (atom x)
       nil
     (cons (gobj-to-param-space (car x) p)
           (gobj-list-to-param-space (cdr x) p)))))

;; (local (in-theory (enable tag-when-g-var-p
;;                           tag-when-g-ite-p
;;                           tag-when-g-apply-p
;;                           tag-when-g-number-p
;;                           tag-when-g-boolean-p
;;                           tag-when-g-concrete-p)))

;; (defthm gobjectp-gobj-to-param-space
;;   (implies (gobjectp x)
;;            (gobjectp (gobj-to-param-space x p)))
;;   :hints(("Goal" :in-theory (e/d (gobjectp-def gobj-to-param-space)
;;                                  ((force))))))

(verify-guards gobj-to-param-space
               :hints(("Goal" :in-theory (e/d () ((force))))))

(defun bfr-param-env (p env)
  (declare (xargs :guard t)
           (ignorable p))
  (bfr-case :bdd (acl2::param-env p env)
            :aig env))

(defund genv-param (p env)
  (declare (xargs :guard (consp env))
           (ignorable p))
  (cons (bfr-param-env p (car env))
        (cdr env)))

;; (local
;;  (defthmd gobjectp-g-number-2
;;    (implies (and (wf-g-numberp (g-number->num x))
;;                  (g-number-p x))
;;             (gobjectp x))
;;    :hints(("Goal" :in-theory (enable g-number-p g-number->num tag gobjectp-def)))
;;    :rule-classes ((:rewrite :backchain-limit-lst (nil 0)))))

;; (local
;;  (defthm gobjectp-g-number-list1
;;    (implies (bfr-listp x)
;;             (gobjectp (g-number (list x))))
;;    :hints(("Goal" :in-theory (enable gobjectp-def tag g-number-p
;;                                      wf-g-numberp-simpler-def)))))

;; (local
;;  (defthm gobjectp-g-number-list2
;;    (implies (and (bfr-listp x)
;;                  (bfr-listp y))
;;             (gobjectp (g-number (list x y))))
;;    :hints(("Goal" :in-theory (enable gobjectp-def tag g-number-p
;;                                      wf-g-numberp-simpler-def)))))

;; (local
;;  (defthm gobjectp-g-number-list3
;;    (implies (and (bfr-listp x)
;;                  (bfr-listp y)
;;                  (bfr-listp z))
;;             (gobjectp (g-number (list x y z))))
;;    :hints(("Goal" :in-theory (enable gobjectp-def tag g-number-p
;;                                      wf-g-numberp-simpler-def)))))

;; (local
;;  (defthm gobjectp-g-number-list4
;;    (implies (and (bfr-listp x)
;;                  (bfr-listp y)
;;                  (bfr-listp z)
;;                  (bfr-listp w))
;;             (gobjectp (g-number (list x y z w))))
;;    :hints(("Goal" :in-theory (enable gobjectp-def tag g-number-p
;;                                      wf-g-numberp-simpler-def)))))

;; (local
;;  (defthm wf-g-numberp-implies-bfr-listps
;;    (implies (wf-g-numberp (g-number->num x))
;;             (and (bfr-listp (car (g-number->num x)))
;;                  (bfr-listp (cadr (g-number->num x)))
;;                  (bfr-listp (caddr (g-number->num x)))
;;                  (bfr-listp (cadddr (g-number->num x)))))
;;    :hints(("Goal" :in-theory (enable wf-g-numberp)))))

;; (local
;;  (defthmd gobjectp-g-boolean-2
;;    (implies (and (bfr-p (g-boolean->bool x))
;;                  (g-boolean-p x))
;;             (gobjectp x))
;;    :hints(("Goal" :in-theory (enable gobjectp-def g-boolean-p g-boolean->bool
;;                                      tag)))
;;    :rule-classes ((:rewrite :backchain-limit-lst (nil 0)))))

;; (local
;;  (defthm gobjectp-g-ite-p
;;    (implies (and (g-ite-p x)
;;                  (gobjectp (g-ite->test x))
;;                  (gobjectp (g-ite->then x))
;;                  (gobjectp (g-ite->else x)))
;;             (equal (gobj-fix x) x))
;;    :hints(("Goal" :in-theory (enable gobjectp-def g-ite-p g-ite->test
;;                                      g-ite->then g-ite->else tag)))))


(local
 (defthm bfr-eval-to-param-space
   (implies (bfr-eval p env)
            (equal (bfr-eval (bfr-to-param-space p x)
                             (bfr-param-env p env))
                   (bfr-eval x env)))
   :hints(("Goal" :in-theory (e/d* (bfr-eval
                                    bfr-to-param-space
                                    acl2::param-env-to-param-space))))))

(local
 (defthm bfr-eval-list-to-param-space-list
   (implies (bfr-eval p env)
            (equal (bfr-eval-list (bfr-list-to-param-space p x)
                                  (bfr-param-env p env))
                   (bfr-eval-list x env)))
   :hints(("Goal" :in-theory (enable bfr-eval-list
                                     bfr-eval
                                     bfr-list-to-param-space)))))

(local
 (defthm nth-open-const-idx
   (implies (syntaxp (quotep n))
            (equal (nth n lst)
                   (if (zp n)
                       (car lst)
                     (nth (1- n) (cdr lst)))))
   :hints(("Goal" :in-theory (enable nth)))))

(local
 (defthm bfr-eval-list-nil
   (Equal (bfr-eval-list nil env)
          nil)
   :hints (("goal" :in-theory (enable bfr-eval-list)))))

(local
 (defthm bfr-eval-list-t
   (Equal (bfr-eval-list '(t) env)
          '(t))
   :hints (("goal" :in-theory (enable bfr-eval-list)))))

(defthm gnumber-to-param-space-correct
  (implies (bfr-eval p (car env))
           (equal (generic-geval (gnumber-to-param-space n p)
                                 (cons (bfr-param-env p (car env))
                                       (cdr env)))
                  (generic-geval (g-number n) env)))
  :hints(("Goal" :in-theory (e/d (gnumber-to-param-space
                                  generic-geval)
                                 (components-to-number-alt-def
                                  break-g-number
                                  bfr-param-env)))))


(defthm-gobj->term-flag
  (defthm gobj-to-param-space-correct
    (implies (bfr-eval p (car env))
             (equal (generic-geval (gobj-to-param-space x p)
                                   (genv-param p env))
                    (generic-geval x env)))
    :flag gobj)
  (defthm gobj-list-to-param-space-correct
    (implies (bfr-eval p (car env))
             (equal (generic-geval-list (gobj-list-to-param-space x p)
                                        (genv-param p env))
                    (generic-geval-list x env)))
    :flag list)
    :hints(("Goal" :in-theory
            (e/d* (genv-param
                   ;; gobjectp-g-boolean-2
                   ;; gobjectp-g-number-2
                   default-car default-cdr)
                  ((force) bfr-eval-list
                   components-to-number-alt-def
                   boolean-listp bfr-eval
                   (:rules-of-class :type-prescription :here)
; generic-geval-when-g-var-tag
                   
;                 bfr-eval-of-non-consp-cheap
;                 bfr-eval-when-not-consp
                   bfr-to-param-space
                   bfr-list-to-param-space
                   bfr-param-env
                   ;;break-g-number
                   generic-geval
                   hons-assoc-equal)
                  ((:type-prescription len)))
            :expand ((gobj-to-param-space x p)
                     (gobj-list-to-param-space x p))
            :do-not-induct t)
           (and stable-under-simplificationp
                (flag::expand-calls-computed-hint
                 acl2::clause '(generic-geval generic-geval-list)))))



(defun shape-spec-to-gobj-param (spec p)
  (declare (xargs :guard (shape-specp spec)))
  (gobj-to-param-space (shape-spec-to-gobj spec) p))

(defun shape-spec-to-env-param (x obj p)
  (declare (xargs :guard (shape-specp x)))
  (genv-param p (shape-spec-to-env x obj)))


(defthm eval-bfr-to-param-space-self
  (implies (bfr-eval x (car env))
           (bfr-eval (bfr-to-param-space x x) (car (genv-param x env))))
  :hints(("Goal" :in-theory (enable bfr-eval bfr-to-param-space genv-param
                                    bfr-param-env
                                    default-car))))
