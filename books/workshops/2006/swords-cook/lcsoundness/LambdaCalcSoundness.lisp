; (ld "LambdaCalc-Sol.lisp" :ld-pre-eval-print t)




(in-package "ACL2")

(include-book "LambdaCalcBasis")


;;----------------------------------------------------------------------------
;; is-used-in and used-var-list
;; These are necessary for defining a
;; capture-avoiding alpha-substitution.
;;----------------------------------------------------------------------------

(defun is-used-in (name expr)
  (declare (xargs :guard (and (varname-p name)
                              (expression-p expr))))
  (pattern-match
   expr
   ((VAR !name) t)
   ((LAM !name & &) t)
   ((LAM & & body) (is-used-in name body))
   ((APP fun arg) (or (is-used-in name fun)
                        (is-used-in name arg)))
   ((IFELSE cond case1 case2)
    (or (is-used-in name cond)
        (is-used-in name case1)
        (is-used-in name case2)))))

(defun used-var-list (expr)
  (declare (xargs :guard (expression-p expr)))
  (pattern-match
   expr
   ((VAR name) (list name))
   ((LAM var & body) (cons var (used-var-list body)))
   ((APP fun arg) (append (used-var-list fun)
                            (used-var-list arg)))
   ((IFELSE cond case1 case2)
    (append (used-var-list cond)
            (used-var-list case1)
            (used-var-list case2)))))


(defthm used-var-list-varname-list
  (implies (expression-p expr)
           (varname-listp (used-var-list expr))))

(defthm is-used-in-used-var-list
  (iff (is-used-in var expr)
       (member-equal var (used-var-list expr))))


(in-theory (disable is-used-in-used-var-list))




;;----------------------------------------------------------------------------
;; unique-varname
;; Given a variable name and a list of already-used names,
;; unique-varname comes up with a new name not in the list.
;;----------------------------------------------------------------------------

(defun unique-varname (try used)
  (declare (xargs :measure (+ (if (VN-p try) 0 1) (acl2-count used))
                  :guard (and (varname-p try)
                              (varname-listp used))
                  :guard-hints
                  (("Goal" :do-not '(eliminate-destructors)
                    :use (:theorem
                          (implies (natp (vn-num try))
                                   (natp (+ 1 (vn-num try)))))))))
  (if (not (member-equal try used))
      try
    (pattern-match
     try
     ((VN name num)
      (unique-varname (VN name (1+ num)) (remove-equal try used)))
     (& (unique-varname (VN 'x 0) used)))))


(defthm unique-increasing
  (implies (and (VN-p var)
                (member-equal var list))
           (< (VN-num var)
              (VN-num (unique-varname var list))))
  :hints (("Goal" :induct (unique-varname var list)))
  :rule-classes (:rewrite :linear))



(defthm unique-not-in-list
  (not (member-equal (unique-varname var list)
                     list))
  :hints (("Subgoal *1/2" :use unique-increasing
           :in-theory (disable unique-increasing))))


(defthm unique-not-equal
  (implies (member-equal var list)
           (not (equal var (unique-varname var list)))))


(defthm unique-append
  (and (not (member-equal (unique-varname var (append list1 list2))
                          list2))
       (not (member-equal (unique-varname var (append list1 list2))
                          list1)))
  :hints (("Goal" :use (:instance unique-not-in-list
                                  (list (append list1 list2)))
           :in-theory (disable unique-not-in-list))))


(defthm unique-cons-append
  (and (not (member-equal
             (unique-varname var (cons v (append list1 list2)))
             list2))
       (not (member-equal
             (unique-varname var (cons v (append list1 list2)))
             list1)))
  :hints (("Goal" :use (:instance unique-not-in-list
                                  (list (cons v (append list1 list2))))
           :in-theory (disable unique-not-in-list))))

(defthm unique-not-equal2
  (implies (member-equal v list)
           (not (equal v (unique-varname var list)))))


(defthm varname-p-unique-varname
  (implies (varname-p try)
           (varname-p (unique-varname try used)))
  :hints (("Subgoal *1/2" :use (:theorem (implies (natp (vn-num try))
                                                  (natp (+ 1 (vn-num try))))))))

(in-theory (disable unique-varname))

;;----------------------------------------------------------------------------
;; alpha-subst
;; Substitutes var2 for var1 everywhere it appears - even binding and bound
;; occurrences.  (Because of this we need to make sure that var2 does not occur
;; in term.)
;;----------------------------------------------------------------------------

(defun alpha-subst (var1 var2 term)
  (declare (xargs :guard (and (varname-p var1)
                              (varname-p var2)
                              (expression-p term))))
  (pattern-match term
    ((VAR !var1) (VAR var2))
    ((LAM !var1 typ body)
     (LAM var2 typ (alpha-subst var1 var2 body)))
    ((LAM v typ body)
     (LAM v typ (alpha-subst var1 var2 body)))
    ((APP fun arg)
     (APP (alpha-subst var1 var2 fun)
          (alpha-subst var1 var2 arg)))
    ((IFELSE cond case1 case2)
     (IFELSE (alpha-subst var1 var2 cond)
             (alpha-subst var1 var2 case1)
             (alpha-subst var1 var2 case2)))
    (& term)))


(defthm alpha-subst-expression-measure
  (= (expression-measure (alpha-subst var1 var2 term))
     (expression-measure term)))

(defthm expression-p-alpha-subst
  (implies (and (expression-p term)
                (varname-p var2))
           (expression-p (alpha-subst var1 var2 term))))

(in-theory (disable alpha-subst))

;;----------------------------------------------------------------------------
;; subst-expression
;; Substitutes free occurrences of (var name) in expr for
;; value.  If value contains free variables, any rebindings
;; of those variables in whose scope name occurs are renamed.
;;----------------------------------------------------------------------------

(defun subst-expression (value name expr)
  (declare (xargs :measure (expression-measure expr)
                  :guard (and (expression-p value)
                              (varname-p name)
                              (expression-p expr))
                  :verify-guards nil))
    (pattern-match
     expr

     ((LAM !name & &) expr)

     ((LAM var type body)
      (if (is-used-in var value)
          (let* ((newvar
                  (unique-varname var (cons name
                                            (append (used-var-list value)
                                                    (used-var-list body)))))
                 (newbody (alpha-subst var newvar body)))
                (LAM newvar type
                     (subst-expression value name newbody)))
        (LAM var type (subst-expression value name body))))

     ((APP fun arg)
      (APP (subst-expression value name fun)
           (subst-expression value name arg)))

     ((IFELSE cond case1 case2)
      (IFELSE (subst-expression value name cond)
              (subst-expression value name case1)
              (subst-expression value name case2)))

     ((VAR !name) value)

     (& expr)))


(defthm expression-p-subst-expression
  (implies (and (expression-p val)
                (expression-p expr))
           (expression-p (subst-expression val name expr))))

(verify-guards subst-expression)


(defthm product-type-subst-expression
  (implies (not (var-p expr))
           (equal (product-type (subst-expression val name expr))
                  (product-type expr))))


(in-theory (disable subst-expression))



;; Value-p: expr is a good value, not requiring further evaluation.
(defun value-p (expr)
  (declare (xargs :guard (expression-p expr)))
  (pattern-match expr
    ((TRUE) t)
    ((FALSE) t)
    ((LAM & & &) t)))

;;----------------------------------------------------------------------------
;; valid-evaluation
;; This checks whether an evaluation derivation correctly shows that x1
;; evaluates to x2.
;;----------------------------------------------------------------------------
(defun valid-evaluation (x1 x2 deriv)
  (declare (xargs :guard (and (expression-p x1)
                              (expression-p x2)
                              (eval-deriv-p deriv))))
  (pattern-match deriv
    ((E-APP1 subder)
     (pattern-match-list (x1 x2)
       (((APP f1 a) (APP f2 a))
        (declare (ignore a))
        (valid-evaluation f1 f2 subder))))

    ((E-APP2 subder)
     (pattern-match-list (x1 x2)
       (((APP f a1) (APP f a2))
        (and (value-p f)
             (valid-evaluation a1 a2 subder)))))

    ((E-AppAbs)
     (pattern-match x1
       ((APP (LAM x & body) v)
        (and (value-p v)
             (equal (subst-expression v x body)
                    x2)))))

    ((E-IFCOND subder)
     (pattern-match-list (x1 x2)
       (((IFELSE cond1 case1 case2) (IFELSE cond2 case1 case2))
        (declare (ignore case1 case2))
        (valid-evaluation cond1 cond2 subder))))

    ((E-IFTRUE)
     (pattern-matches-list (x1 x2)
       ((IFELSE (TRUE) case1 &) case1)))

    ((E-IFFALSE)
     (pattern-matches-list (x1 x2)
       ((IFELSE (FALSE) & case2) case2)))))



(defthm valid-evaluation-examples
  (and
   (valid-evaluation
    '(APP (APP (LAM (VN x 0) (BOOL)
                    (LAM (VN y 0) (BOOL)
                         (IFELSE (IFELSE (VAR (VN x 0))
                                         (VAR (VN x 0))
                                         (VAR (VN y 0)))
                                 (FALSE)
                                 (TRUE))))
               (FALSE))
          (TRUE))
    '(APP (LAM (VN y 0) (BOOL)
               (IFELSE (IFELSE (FALSE)
                               (FALSE)
                               (VAR (VN y 0)))
                       (FALSE)
                       (TRUE)))
          (TRUE))
    '(E-APP1 (E-AppAbs)))
   (valid-evaluation
    '(APP (LAM (VN y 0) (BOOL)
               (IFELSE (IFELSE (FALSE)
                               (FALSE)
                               (VAR (VN y 0)))
                       (FALSE)
                       (TRUE)))
          (TRUE))
    '(IFELSE (IFELSE (FALSE)
                     (FALSE)
                     (TRUE))
             (FALSE)
             (TRUE))
    '(E-AppAbs))
   (valid-evaluation
    '(IFELSE (IFELSE (FALSE)
                     (FALSE)
                     (TRUE))
             (FALSE)
             (TRUE))
    '(IFELSE (TRUE) (FALSE) (TRUE))
    '(E-IFCOND (E-IFFALSE)))
   (valid-evaluation
    '(IFELSE (TRUE) (FALSE) (TRUE))
    '(FALSE)
    '(E-IFTRUE)))
  :rule-classes nil)



;;----------------------------------------------------------------------------
;; valid-typing
;; Checks that a typing derivation correctly shows that expression term is of
;; type type in context env.
;;----------------------------------------------------------------------------

(defun valid-typing (env term type deriv)
  (declare (xargs :guard (and (type-deriv-p deriv)
                              (environment-p env)
                              (expression-p term)
                              (stype-p type))))

  (pattern-match deriv
    ((T-TRUE)
     (and (equal term (TRUE))
          (equal type (BOOL))))

    ((T-FALSE)
     (and (equal term (FALSE))
          (equal type (BOOL))))

    ((T-VAR)
     (and (VAR-p term)
          (let ((assoc (assoc-equal (VAR-name term) env)))
            (and assoc
                 (equal type (cdr assoc))))))

    ((T-ABS bodyderiv)
     (pattern-match-list (term type)
       (((LAM x domain body) (FUN domain range))
        (valid-typing (cons (cons x domain) env)
                      body range bodyderiv))))

    ((T-APP argtype funderiv argderiv)
     (pattern-match term
       ((APP fun arg)
        (and (valid-typing env fun (FUN argtype type) funderiv)
             (valid-typing env arg argtype argderiv)))))

    ((T-IF condderiv case1deriv case2deriv)
     (pattern-match term
       ((IFELSE cond case1 case2)
        (and (valid-typing env cond (BOOL) condderiv)
             (valid-typing env case1 type case1deriv)
             (valid-typing env case2 type case2deriv)))))))



(defthm valid-typing-test
  (valid-typing nil
                '(LAM (VN x 0)
                      (BOOL)
                      (IFELSE (VAR (VN x 0)) (FALSE) (TRUE)))
                '(FUN (BOOL) (BOOL))
                '(T-ABS (T-IF (T-VAR) (T-FALSE) (T-TRUE))))
  :rule-classes nil)





;; PROGRESS --

;; We provide a function progress-deriv which, given a non-value term
;; with a valid type derivation, produces a valid evaluation
;; derivation together with a new term that is the result of the
;; evaluation.  The progress theorem then proves that this derivation
;; is valid.

(defun progress-deriv-expr (term type deriv)
  (declare (xargs :guard (and (expression-p term)
                              (stype-p type)
                              (type-deriv-p deriv)
                              (valid-typing nil term type deriv))))
  (pattern-match-list (deriv term)
    (((T-APP argtype funderiv argderiv)
      (APP fun arg))
     (if (value-p fun)
         (if (value-p arg)
             (pattern-match fun
               ((LAM x & body)
                (mv (E-AppAbs)
                    (subst-expression arg x body)))
               (& (mv nil nil)))
           (mv-let (argeval newarg)
                   (progress-deriv-expr arg argtype argderiv)
                   (if argeval
                       (mv (E-App2 argeval) (APP fun newarg))
                     (mv nil nil))))
       (mv-let (funeval newfun)
               (progress-deriv-expr fun (FUN argtype type) funderiv)
               (if funeval
                   (mv (E-App1 funeval) (APP newfun arg))
                 (mv nil nil)))))

    (((T-IF condderiv & &)
      (IFELSE cond case1 case2))
     (if (value-p cond)
         (if (equal cond (TRUE))
             (mv (E-IFTRUE) case1)
           (mv (E-IFFALSE) case2))
       (mv-let (condeval newcond)
               (progress-deriv-expr cond (BOOL) condderiv)
               (if condeval
                   (mv (E-IFCOND condeval)
                       (IFELSE newcond case1 case2))
                 (mv nil nil)))))

    (& (mv nil nil))))


(defun next-expr (term type deriv)
  (mv-let (evder newexp)
    (progress-deriv-expr term type deriv)
    (declare (ignore evder))
    newexp))

(defun progress-deriv (term type deriv)
  (mv-let (evder newexp)
    (progress-deriv-expr term type deriv)
    (declare (ignore newexp))
    evder))

(defthm progress
  (implies
   (and (valid-typing nil term type deriv)
        (not (value-p term)))
   (valid-evaluation term
                     (next-expr term type deriv)
                     (progress-deriv term type deriv)))
  :hints (("Goal" :induct (progress-deriv-expr term type deriv)))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(in-theory (disable progress-deriv next-expr))




;; Permutation

;; If env1 |- term : type by deriv and (env-same-bindings env1 env2)
;; then env2 |- term : type by
;; (permutation-deriv env1 env2 term type deriv).

;; env-same-bindings says that for each bound variable in env1,
;; looking it up in env1 yields the same result as looking it up in
;; env2.  In the abstract sense this is only permutation, though with
;; the alist representation of environments it also shows that
;; redundant bindings don't matter.

;; The same derivation proves env1 |- term : type as env2 |- term : type,
;; but using this function instead allows us to signal the theorem
;; prover to use the correct instantiation of the permutation lemma.
;; If we did not use this function then env1 would be a free variable
;; and it's unlikely that the theorem prover would instantiate it correctly.
(defun permutation-deriv (env1 deriv)
  (declare (xargs :guard t)
           (ignore env1))
  deriv)

(defthm permutation
  (implies (force-and (valid-typing env1 term type deriv)
                      (env-same-bindings env1 env2))
           (valid-typing env2 term type
                         (permutation-deriv env1 deriv)))
  :hints (("Goal"
           :induct (and (valid-typing env1 term type deriv)
                        (valid-typing env2 term type deriv))))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(defthm permutation-deriv-type
  (implies (type-deriv-p deriv)
           (type-deriv-p (permutation-deriv env deriv))))

(defthm permutation-deriv-measure
  (= (acl2-count (permutation-deriv env deriv))
     (acl2-count deriv)))

(in-theory (disable permutation-deriv))



;; Weakening:

;; The traditional weakening lemma is a little broader, covering
;; variables not free in a term.  But it turns out our permutation
;; lemma covers that case; if the variable with the binding being
;; inserted is bound then the environment with the variable bound
;; twice becomes a "permutation" of the original environment where it
;; was only bound once.
(defun weakening-deriv (env1 k v suffix deriv)
  (declare (ignore env1 k v suffix)
           (xargs :guard t))
  deriv)

(defthm weakening
  (implies (force-and (valid-typing env1 term type deriv)
                      (not (is-used-in var term))
                      (is-suffix suffix env1)
                      (equal env2 (insert-assoc var t2 suffix env1)))
           (valid-typing env2 term type
                         (weakening-deriv env1 var t2 suffix deriv)))
  :hints (("Goal"
           :induct (and (valid-typing env1 term type deriv)
                        (valid-typing env2 term type deriv))))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(defthm weakening-deriv-measure
  (= (acl2-count (weakening-deriv env1 k v suffix deriv))
     (acl2-count deriv)))

(defthm weakening-deriv-type
  (implies (type-deriv-p deriv)
           (type-deriv-p (weakening-deriv env1 k v suffix deriv))))

(in-theory (disable weakening-deriv))





;; Alpha substitution
;; The form of this one is a little strange.  The same type derivation
;; is still correct under an alpha substitution, but we have to
;; determine the correct from of an environment.  The following scheme
;; is what will work to prove substitution later:

;; - Some suffix of the environment may be unchanged, and we don't care
;; what is bound there.  This allows us to alpha-substitute into a
;; subterm where one of the substitution variables may already be
;; bound but are being re-bound immediately, which is actually the
;; case in which alpha substitution is used.

;; - If we're substituting v1 for v2, v1 MUST be bound in env before
;; the suffix, and v2 CANNOT be.

;; Those conditions are covered by (alpha-subst-env-okp v1 v2 suffix
;; env).  We also require that v2 not be used inside the term.  Since
;; v2 is just a fresh variable, it doesn't matter if we restrict it to
;; be unused instead of unfree, and it makes the proof easier.

(defun alpha-subst-deriv (suff env orig oldvar newvar deriv)
  (declare (ignore suff env orig oldvar newvar)
           (xargs :guard t))
  deriv)


(defthm alpha-subst-ok
  (implies (force-and (valid-typing env term type deriv)
                      (not (is-used-in var2 term))
                      (alpha-subst-env-okp var1 var2 suff env)
                      (equal env2 (env-subst-up-to var1 var2 suff env)))
           (valid-typing env2
                         (alpha-subst var1 var2 term)
                         type (alpha-subst-deriv suff env term var1 var2
                                                 deriv)))
  :hints (("Goal" :in-theory (enable alpha-subst)))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))


(defthm alpha-subst-deriv-measure
  (= (acl2-count (alpha-subst-deriv suff env term v1 v2 d))
     (acl2-count d)))

(defthm alpha-subst-type-deriv
  (implies (type-deriv-p deriv)
           (type-deriv-p (alpha-subst-deriv suff env orig var1 var2 deriv))))

(in-theory (disable alpha-subst-deriv))

;; If env |- val : valtype by val-deriv and
;; (cons (cons var valtype) env) |- term : term-type by term-deriv
;; then env |- (subst-expression val var term) : term-type
;; by the result of this function.


(defun substitution-deriv (env var val valtype val-deriv
                               term term-type term-deriv)
  (declare (xargs :guard (and (environment-p env)
                              (varname-p var)
                              (expression-p val)
                              (stype-p valtype)
                              (type-deriv-p val-deriv)
                              (expression-p term)
                              (stype-p term-type)
                              (type-deriv-p term-deriv))
                  :measure (acl2-count term-deriv)))
  (pattern-match term-deriv
    ((T-TRUE) (T-TRUE))
    ((T-FALSE) (T-FALSE))
    ((T-IF condder case1der case2der)
     (pattern-match term
       ((IFELSE cond case1 case2)
        (T-IF (substitution-deriv env var val valtype val-deriv
                                  cond (BOOL) condder)
              (substitution-deriv env var val valtype val-deriv
                                  case1 term-type case1der)
              (substitution-deriv env var val valtype val-deriv
                                  case2 term-type case2der)))))
    ((T-APP argtype funder argder)
     (pattern-match term
       ((APP fun arg)
        (T-APP argtype
               (substitution-deriv env var val valtype val-deriv
                                   fun (FUN argtype term-type) funder)
               (substitution-deriv env var val valtype val-deriv
                                   arg argtype argder)))))

    ((T-VAR)
     (pattern-match term
       ((VAR !var)
        val-deriv)
       ((VAR &)
        term-deriv)))

    ((T-ABS bodyder)
     (pattern-match term
       ((LAM !var dom &)
        (T-ABS (permutation-deriv
                (list* (cons var dom) (cons var valtype) env)
                bodyder)))
       ((LAM v dom body)
        (pattern-match term-type
          ((FUN !dom ran)
           (if (is-used-in v val)
               (let ((newvar (unique-varname
                              v (cons var
                                      (append (used-var-list val)
                                              (used-var-list body))))))
                 (T-ABS
                  (substitution-deriv
                   (cons (cons newvar dom) env)
                   var val valtype
                   (weakening-deriv
                    env newvar dom env val-deriv)
                   (alpha-subst v newvar body)
                   ran
                   ;; body-der says env,v:dom|-body:ran
                   ;; need env,newvar:dom|-(alpha-subst newvar v body):ran
                   (alpha-subst-deriv
                    env
                    (list* (cons var valtype) (cons v dom) env)
                    body v newvar
                    (permutation-deriv
                     (list* (cons v dom) (cons var valtype) env)
                     bodyder)))))

             ;; val-deriv: env |- val : valtype
             ;; bodyder: (cons (cons v dom) (cons (cons var valtype) env))
             ;;              |- body : ran

             (T-ABS
              (substitution-deriv
               (cons (cons v dom) env)
               var val valtype
               (weakening-deriv
                env v dom env val-deriv)
               body ran
               (permutation-deriv
                (list* (cons v dom) (cons var valtype) env)
                bodyder)))))))))))




(defthm substitution
  (implies (force-and (valid-typing env val vtype vderiv)
                      (valid-typing (cons (cons var vtype) env)
                                    term ttype tderiv))
           (valid-typing
            env (subst-expression val var term) ttype
            (substitution-deriv env var val vtype vderiv term ttype tderiv)))
  :hints (("Goal" :in-theory (enable subst-expression))
          ("Subgoal *1/22" :in-theory (enable is-used-in-used-var-list))
          ("Subgoal *1/21" :in-theory (enable is-used-in-used-var-list)))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(in-theory (disable substitution-deriv))


;; If env |- term : type by type-deriv and term -> term2 by eval-deriv,
;; then this function returns a derivation that env |- term2 : type.
(defun preservation-deriv (env term type type-deriv eval-deriv)
  (declare (xargs :guard (and (environment-p env)
                              (expression-p term)
                              (stype-p type)
                              (type-deriv-p type-deriv)
                              (eval-deriv-p eval-deriv))))
  (pattern-match eval-deriv
    ((E-APP1 eval-subder)
     (pattern-match-list (term type-deriv)
       (((APP f1 &) (T-APP argtype funderiv argderiv))
        (T-APP argtype
               (preservation-deriv
                env f1 (FUN argtype type) funderiv eval-subder)
               argderiv))))

    ((E-APP2 eval-subder)
     (pattern-match-list (term type-deriv)
       (((APP & a1) (T-APP argtype funderiv argderiv))
        (T-APP argtype
               funderiv
               (preservation-deriv
                env a1 argtype argderiv eval-subder)))))

    ((E-AppAbs)
     (pattern-match-list (term type-deriv)
       (((APP (LAM x dom body) arg) (T-APP dom (T-ABS bodyderiv) argderiv))
        (substitution-deriv
         env x arg dom argderiv body type bodyderiv))))

    ((E-IFCOND eval-subder)
     (pattern-match-list (term type-deriv)
       (((IFELSE cond1 & &)
         (T-IF condderiv case1deriv case2deriv))
        (T-IF (preservation-deriv
                 env cond1 (BOOL) condderiv eval-subder)
                case1deriv
                case2deriv))))

    ((E-IFTRUE)
     (pattern-match type-deriv
       ((T-IF & case1 &) case1)))

    ((E-IFFALSE)
      (pattern-match type-deriv
       ((T-IF & & case2) case2)))))


(defthm preservation
  (implies
   (and (valid-typing env term type type-deriv)
        (valid-evaluation term term2 eval-deriv))
   (valid-typing
    env term2 type
    (preservation-deriv
     env term type type-deriv eval-deriv)))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(in-theory (disable preservation-deriv))