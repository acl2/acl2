
(in-package "GL")

(include-book "bvecs")
(include-book "centaur/ubdds/param" :dir :system)

(include-book "../aig/misc")
(local (include-book "../aig/eval-restrict"))

(local (in-theory (disable acl2::append-of-nil)))


(defun bfr-list-to-param-space (p x)
  (declare (xargs :guard t
                  :guard-hints ('(:in-theory (enable bfr-to-param-space
                                                     bfr-list-to-param-space))))
           (ignorable p))
  (mbe :logic (if (atom x)
                  nil
                (cons (bfr-to-param-space p (car x))
                      (bfr-list-to-param-space p (cdr x))))
       :exec (if (atom x)
                 nil
               (bfr-case :bdd (acl2::to-param-space-list p x)
                         :aig (acl2::aig-restrict-list
                               x (acl2::aig-extract-iterated-assigns-alist p 10))))))


(defthm bfr-eval-list-to-param-space-list
  (implies (bfr-eval p env)
           (equal (bfr-eval-list (bfr-list-to-param-space p x)
                                 (bfr-param-env p env))
                  (bfr-eval-list x env)))
  :hints(("Goal" :in-theory (e/d (bfr-eval-list
                                  bfr-list-to-param-space)
                                 (bfr-param-env)))))

(defthm bfr-eval-list-to-param-space-list-with-unparam-env
  (implies (syntaxp (not (and (consp env)
                              (eq (car env) 'bfr-param-env))))
           (equal (bfr-eval-list (bfr-list-to-param-space p x)
                                 env)
                  (bfr-eval-list x (bfr-unparam-env p env))))
  :hints(("Goal" :in-theory (e/d (bfr-eval-list
                                  bfr-list-to-param-space)
                                 (bfr-param-env)))))

(defthm bfr-list->s-to-param-space-list
  (implies (bfr-eval p env)
           (equal (bfr-list->s (bfr-list-to-param-space p x)
                               (bfr-param-env p env))
                  (bfr-list->s x env)))
  :hints(("Goal" :in-theory (e/d (bfr-list->s
                                  scdr s-endp
                                  default-car
                                  bfr-list-to-param-space)
                                 (bfr-to-param-space
                                  bfr-param-env))
          :induct (bfr-list-to-param-space p x)
          :expand ((bfr-list->s x env)))))

(defthm bfr-list->s-to-param-space-list-with-unparam-env
  (implies (syntaxp (not (and (consp env)
                              (eq (car env) 'bfr-param-env))))
           (equal (bfr-list->s (bfr-list-to-param-space p x)
                               env)
                  (bfr-list->s x (bfr-unparam-env p env))))
  :hints(("Goal" :in-theory (e/d (bfr-list->s
                                  scdr s-endp
                                  default-car
                                  bfr-list-to-param-space)
                                 (bfr-to-param-space
                                  bfr-param-env))
          :induct (bfr-list-to-param-space p x)
          :expand ((:free (env) (bfr-list->s x env))))))

(defthm bfr-list->u-to-param-space-list
  (implies (bfr-eval p env)
           (equal (bfr-list->u (bfr-list-to-param-space p x)
                               (bfr-param-env p env))
                  (bfr-list->u x env)))
  :hints(("Goal" :in-theory (e/d (bfr-list->u scdr s-endp
                                              ;; bfr-eval
                                              bfr-list-to-param-space)
                                 (bfr-to-param-space
                                  bfr-param-env)))))

(defthm bfr-list->u-to-param-space-list-with-unparam-env
  (implies (syntaxp (not (and (consp env)
                              (eq (car env) 'bfr-param-env))))
           (equal (bfr-list->u (bfr-list-to-param-space p x)
                               env)
                  (bfr-list->u x (bfr-unparam-env p env))))
  :hints(("Goal" :in-theory (e/d (bfr-list->u scdr s-endp
                                              ;; bfr-eval
                                              bfr-list-to-param-space)
                                 (bfr-to-param-space
                                  bfr-param-env)))))

(defund genv-param (p env)
  (declare (xargs :guard (consp env))
           (ignorable p))
  (cons (bfr-param-env p (car env))
        (cdr env)))

(defund genv-unparam (p env)
  (declare (xargs :guard (consp env))
           (ignorable p))
  (cons (bfr-unparam-env p (car env))
        (cdr env)))
