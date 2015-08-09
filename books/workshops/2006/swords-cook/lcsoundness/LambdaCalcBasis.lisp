(in-package "ACL2")

(set-ignore-ok :warn)

(include-book "data-structures/list-theory" :dir :system)
(include-book "defsum")
(local (include-book "defsum-thms"))

;; stype ::= bool | type -> type
(defsum stype
  (bool)
  (fun (stype-p domain) (stype-p range)))

;; A varname is a paired symbol and natural, so that we have a simple way of
;; generating new unique ones.
(defsum varname
  (VN (symbolp name) (natp num)))

;; type of a list of varnames
(deflist varname-listp (l)
  (declare (xargs :guard t))
  varname-p)

(defthm acl2-numberp-varname-num
  (implies (varname-p x)
           (acl2-numberp (vn-num x)))
  :hints (("Goal" :use varname-possibilities
           :in-theory (disable varname-possibilities))))


;; expression ::= TRUE | FALSE |
;;                LAMBDA varname : type . expression |
;;                APP expression expression |
;;                VAR varname |
;;                IFELSE expression expression expression
(defsum expression
    (TRUE)
    (FALSE)
    (LAM (varname-p var) (stype-p type) (expression-p body))
    (APP (expression-p fun) (expression-p arg))
    (VAR (varname-p name))
    (IFELSE (expression-p cond)
            (expression-p case1)
            (expression-p case2)))


;; Typing derivations, checked by valid-typing.
;; The type of the argument in an application needs to be specified for T-APP;
;; everything else is syntax-driven.
(defsum type-deriv
  (T-TRUE)
  (T-FALSE)
  (T-VAR)
  (T-ABS (type-deriv-p body))
  (T-APP (stype-p argtype)
         (type-deriv-p fun)
         (type-deriv-p arg))
  (T-IF (type-deriv-p cond)
        (type-deriv-p case1)
        (type-deriv-p case2)))

;; Evaluation derivations, checked by valid-evaluation.
(defsum eval-deriv
  (E-AppAbs)
  (E-APP1 (eval-deriv-p fun))
  (E-APP2 (eval-deriv-p arg))
  (E-IFCOND (eval-deriv-p cond))
  (E-IFTRUE)
  (E-IFFALSE))



;; An environment is an alist associating variable names with types.
(defun environment-p (env)
  (declare (xargs :guard t))
  (if (and (consp env) (consp (car env)))
      (and (varname-p (caar env))
           (stype-p (cdar env))
           (environment-p (cdr env)))
    (null env)))

;; Various lemmas about environments.
(defthm environment-assoc
	(implies (environment-p env)
                 (alistp env)))

(defthm alistp-assoc-cons
  (implies (and (alistp a)
                (assoc-equal k a))
           (consp (assoc-equal k a))))


(defthm environment-p-assoc-type
  (implies (and (environment-p env)
                (assoc-equal key env))
           (stype-p (cdr (assoc-equal key env)))))



;; These functions and lemmas mainly form the basis for the weakening
;; and alpha-substitution lemmas.  We're concerned with environments
;; that get modified up to a certain suffix, beyond which we don't
;; care.

;; Is suf a suffix of env?
(defun is-suffix (suf env)
  (if (equal suf env)
      t
    (if (atom env)
        nil
      (is-suffix suf (cdr env)))))


(defthm is-suffix-len
  (implies (< (len env) (len suffix))
           (not (is-suffix suffix env)))
  :rule-classes nil)

(defthm is-suffix-not-equal-cons
  (not (is-suffix (cons a x) x))
  :hints (("Goal" :use (:instance is-suffix-len
                                 (env x)
                                 (suffix (cons a x))))))


;; Substitute all bindings of v1 for v2 up to suffix.
(defun env-subst-up-to (v1 v2 suff env)
  (declare (xargs :guard (alistp env)))
  (if (equal suff env)
      env
    (if (atom env)
        env
      (cons
       (if (equal (caar env) v1)
           (cons v2 (cdar env))
         (car env))
       (env-subst-up-to v1 v2 suff (cdr env))))))


(defthm env-subst-up-to-assoc-other
  (implies (and (not (equal v v1))
                (not (equal v v2)))
           (equal (assoc-equal v (env-subst-up-to v1 v2 suff env))
                  (assoc-equal v env))))

;; Insert a binding of k to v just before suffix.
(defun insert-assoc (k v suffix alist)
  (declare (xargs :guard (alistp alist)))
  (if (equal suffix alist)
      (cons (cons k v) alist)
    (if (atom alist)
        alist
      (cons (car alist)
            (insert-assoc k v suffix (cdr alist))))))

(defthm assoc-insert-assoc
  (implies (not (equal key k))
           (equal (assoc-equal key (insert-assoc k v suffix alist))
                  (assoc-equal key alist))))

(defthm cons-insert-assoc
  (implies (is-suffix suffix alist)
           (equal (cons a (insert-assoc k v suffix alist))
                  (insert-assoc k v suffix (cons a alist)))))

;; Is the key bound before the suffix?
(defun is-bound-before-suffix (key suff alist)
  (declare (xargs :guard (alistp alist)))
  (if (equal suff alist)
      nil
    (if (atom alist)
        nil
      (or (equal (caar alist) key)
          (is-bound-before-suffix key suff (cdr alist))))))



(defthm is-bound-before-suffix-env-subst-up-to
  (implies (and (is-bound-before-suffix v suff env)
                (not (is-bound-before-suffix v2 suff env)))
           (equal (cdr (assoc-equal v2 (env-subst-up-to v v2 suff env)))
                  (cdr (assoc-equal v env)))))


(defthm is-bound-before-suffix-env-subst-assoc1
  (implies (and (is-bound-before-suffix v suff env)
                (not (is-bound-before-suffix v2 suff env)))
           (assoc-equal v2 (env-subst-up-to v v2 suff env))))




;; This sums up all the requirements for alpha substitution to work
;; with a given environment.
(defun alpha-subst-env-okp (v1 v2 suffix env)
  (and (is-bound-before-suffix v1 suffix env)
       (not (is-bound-before-suffix v2 suffix env))
       (is-suffix suffix env)))

(defthm alpha-subst-env-okp-base
  (implies (not (equal v1 v2))
           (alpha-subst-env-okp v1 v2 env (cons (cons v1 typ) env))))

(defthm alpha-subst-env-okp-cons
  (implies (and (not (equal v v2))
                (alpha-subst-env-okp v1 v2 env1 env2))
           (alpha-subst-env-okp v1 v2 env1 (cons (cons v typ) env2))))

(defthm alpha-subst-env-okp-implies-assoc-env-subst-up-to
  (implies (alpha-subst-env-okp v1 v2 suffix env)
           (assoc-equal v2 (env-subst-up-to v1 v2 suffix env))))

(defthm alpha-subst-env-okp-cdr-assocs-env-subst
  (implies (alpha-subst-env-okp v1 v2 suffix env)
           (equal (cdr (assoc-equal v2 (env-subst-up-to v1 v2 suffix env)))
                  (cdr (assoc-equal v1 env)))))

(defthm alpha-subst-env-okp-suffix-not-cons
  (not (alpha-subst-env-okp v1 v2 (cons a env) env)))


(in-theory (disable alpha-subst-env-okp))







;; This describes the requirements for the permutation lemma;
;; env-same-bindings checks whether each variable bound in env1 has
;; the same binding in env1 and env2.
(defun env-same-bindings1 (tail full env2)
  (declare (xargs :guard (and (alistp tail)
                              (alistp full)
                              (alistp env2))))
  (if (atom tail)
      t
    (and (equal (assoc-equal (caar tail) full)
                (assoc-equal (caar tail) env2))
         (env-same-bindings1 (cdr tail) full env2))))

(defthm env-same-bindings1-assoc-equal
  (implies (and (env-same-bindings1 tail full env2)
                (assoc-equal x tail))
           (equal (assoc-equal x full)
                  (assoc-equal x env2))))

(defthm env-same-bindings1-cons2
  (implies (env-same-bindings1 tail full env2)
           (env-same-bindings1 tail (cons x full) (cons x env2))))


(defthm env-same-bindings1-refl
  (env-same-bindings1 a b b))

(defthm env-same-bindings1-cons-twice
  (implies (not (equal (car a) (car b)))
           (env-same-bindings1
            tail (list* a b env) (list* b a env))))

(defthm env-same-bindings1-cons-redundant
  (implies (equal t1 t2)
           (env-same-bindings1 tail (list* (cons v t1)
                                           (cons v t3)
                                           env)
                               (list* (cons v t2)
                                      env))))

(defun env-same-bindings (env1 env2)
  (declare (xargs :guard (and (alistp env1) (alistp env2))))
  (env-same-bindings1 env1 env1 env2))

(defthm env-same-bindings-assoc-equal
  (implies (and (env-same-bindings env1 env2)
                (assoc-equal x env1))
           (equal (assoc-equal x env2)
                  (assoc-equal x env1))))

(defthm env-same-bindings-cons
  (implies (env-same-bindings env1 env2)
           (env-same-bindings (cons x env1) (cons x env2))))

(defthm env-same-bindings-cons-twice
  (implies (not (equal (car a) (car b)))
           (env-same-bindings (list* a b env) (list* b a env))))

(defthm env-same-bindings-cons-redundant
  (implies (equal t1 t2)
           (env-same-bindings (list* (cons v t1)
                                     (cons v t3)
                                     env)
                              (list* (cons v t2)
                                     env))))



(defthm same-bindings1-insert-assoc
  (implies (is-suffix suffix env)
           (env-same-bindings1 tail (cons (cons k v) env)
                               (cons (cons k v)
                                     (insert-assoc k v2 suffix env))))
  :hints (("Goal" :induct (env-same-bindings1 tail env env)
           :in-theory (disable cons-insert-assoc))))

(defthm same-bindings1-insert-assoc1
  (implies (is-suffix suffix env)
           (env-same-bindings1 tail (cons (cons k v) env)
                               (insert-assoc k v2 suffix
                                             (cons (cons k v) env))))
  :hints (("Goal" :use same-bindings1-insert-assoc
           :in-theory (disable same-bindings1-insert-assoc))))

(defthm same-bindings-insert-assoc
  (implies (is-suffix suffix env)
           (env-same-bindings (cons (cons k v) env)
                              (insert-assoc k v2 suffix
                                            (cons (cons k v) env)))))

(in-theory (disable env-same-bindings))




(defun forcelist-fn (hyps)
  (declare (xargs :mode :program))
  (if (atom hyps)
      nil
    (cons `(force ,(car hyps))
          (forcelist-fn (cdr hyps)))))

(defmacro force-and (&rest hyps)
  (cons 'and (forcelist-fn hyps)))
