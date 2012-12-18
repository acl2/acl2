

(in-package "GL")

(defstub bfr-mode () t)
(defun bfr-aig () (declare (xargs :guard t)) t)
(defun bfr-bdd () (declare (xargs :guard t)) nil)


(defmacro bfr-case (&key aig bdd)
  `(if (bfr-mode)
       ,aig ,bdd))

;; (defmacro bfr-event (&key aig bdd)
;;   `(make-event
;;     (if *experimental-aig-mode*
;;         ',aig ',bdd)))

(include-book "centaur/ubdds/lite" :dir :system)
(include-book "../aig/witness")

(local (in-theory (enable booleanp)))

(defun bfr-p (x)
  (declare (xargs :guard t)
           (ignorable x))
  (mbe :logic 
       (bfr-case :bdd (acl2::ubddp x) :aig t)
       :exec (or (booleanp x)
                 (bfr-case :bdd (acl2::ubddp x) :aig t))))

(defthm bfr-p-booleanp
  (booleanp (bfr-p x))
  :rule-classes :type-prescription)


(defthmd bfr-p-of-boolean
  (implies (booleanp x) (bfr-p x))
  :hints (("goal" :in-theory (enable bfr-p acl2::ubddp))))

(defun bfr-fix (x)
  (declare (xargs :guard t))
  (mbe :logic
       (bfr-case :bdd (acl2::ubdd-fix x) :aig x)
       :exec
       (if (booleanp x)
           x
         (bfr-case :bdd (acl2::ubdd-fix x) :aig x))))

(defthm bfr-p-bfr-fix
  (bfr-p (bfr-fix x)))

(defthm bfr-fix-when-bfr-p
  (implies (bfr-p x)
           (equal (bfr-fix x) x)))


(defun bfr-equiv (a b)
  (equal (bfr-fix a) (bfr-fix b)))

(defequiv bfr-equiv)

(defthm bfr-fix-bfr-equiv
  (bfr-equiv (bfr-fix x) x))

(defmacro bfrfix (x)
  `(mbe :logic (bfr-fix ,x) :exec ,x))

(defun bfr-fix-bindings (vars)
  (if (atom vars)
      nil
    (cons `(,(car vars) (bfrfix ,(car vars)))
          (bfr-fix-bindings (cdr vars)))))

(defmacro bfr-fix-vars (vars body)
  `(let ,(bfr-fix-bindings vars)
     (declare (ignorable . ,vars))
     ,body))
     

(defun bfr-eval (x env)
  (declare (xargs :guard (bfr-p x)))
  (mbe :logic
       (bfr-case :bdd (acl2::eval-bdd x env)
                 :aig (acl2::aig-eval x env))
       :exec
       (if (booleanp x)
           x
         (bfr-case :bdd (acl2::eval-bdd x env)
                   :aig (acl2::aig-eval x env)))))

(defthmd bfr-eval-of-bfr-fix
  (equal (bfr-eval (bfr-fix x) env)
         (bfr-eval x env))
  :hints (("goal" :use acl2::eval-bdd-ubdd-fix
           :in-theory (disable acl2::eval-bdd-ubdd-fix))))

(defcong bfr-equiv equal (bfr-eval x env) 1
  :hints (("goal" :use ((:instance bfr-eval-of-bfr-fix)
                        (:instance bfr-eval-of-bfr-fix
                                   (x x-equiv)))
           :in-theory (disable bfr-eval bfr-fix))))

(defun bfr-not (x)
  (declare (xargs :guard (bfr-p x)))
  (mbe :logic
       (bfr-case :bdd (acl2::q-not (bfrfix x))
                 :aig (acl2::aig-not (bfrfix x)))
       :exec
       (if (booleanp x)
           (not x)
         (bfr-case :bdd (acl2::q-not (bfrfix x))
                   :aig (acl2::aig-not (bfrfix x))))))

(defthm bfr-p-bfr-not
  (bfr-p (bfr-not x)))

(local (acl2::add-bdd-fn-pat acl2::ubdd-fix))

(defthm bfr-eval-bfr-not
  (equal (bfr-eval (bfr-not x) env)
         (not (bfr-eval x env)))
  :hints (("goal" :in-theory (enable booleanp))
          (acl2::bdd-reasoning)
          (acl2::aig-reasoning)))


(defcong bfr-equiv equal (bfr-not x) 1)

(in-theory (disable bfr-not))


(defun bfr-binary-and (x y)
  (declare (xargs :guard (and (bfr-p x) (bfr-p y))))
  (mbe :logic 
       (bfr-case :bdd (acl2::q-binary-and (bfrfix x) (bfrfix y))
                 :aig (acl2::aig-and (bfrfix x) (bfrfix y)))
       :exec
       (if (and (booleanp x) (booleanp y))
           (and x y)
         (bfr-case :bdd (acl2::q-binary-and (bfrfix x) (bfrfix y))
                   :aig (acl2::aig-and (bfrfix x) (bfrfix y))))))

(defthm bfr-p-bfr-binary-and
  (bfr-p (bfr-binary-and x y)))

(defthm bfr-eval-bfr-binary-and
  (equal (bfr-eval (bfr-binary-and x y) env)
         (and (bfr-eval x env)
              (bfr-eval y env)))
  :hints (("goal" :in-theory (enable booleanp))
          (acl2::bdd-reasoning)
          (acl2::aig-reasoning)))


(defthm bfr-and-of-nil
  (and (equal (bfr-binary-and nil y) nil)
       (equal (bfr-binary-and x nil) nil))
  :hints(("Goal" :in-theory (enable acl2::aig-and))))



(defcong bfr-equiv equal (bfr-binary-and a b) 1)

(defcong bfr-equiv equal (bfr-binary-and a b) 2)

(in-theory (disable bfr-binary-and))


(defun bfr-and-macro-logic-part (args)
  ;; Generates the :logic part for a bfr-and MBE call.
  (declare (xargs :mode :program))
  (cond ((atom args) 
         t)
        ((atom (cdr args)) 
         (car args))
        (t
         `(bfr-binary-and ,(car args) ,(bfr-and-macro-logic-part (cdr args))))))

(defun bfr-and-macro-exec-part (args)
  ;; Generates the :exec part for a bfr-and MBE call.
  (declare (xargs :mode :program))
  (cond ((atom args) 
         t)
        ((atom (cdr args)) 
         (car args))
        (t 
         `(let ((bfr-and-x-do-not-use-elsewhere ,(car args)))
            (and bfr-and-x-do-not-use-elsewhere
                 (bfr-binary-and
                  bfr-and-x-do-not-use-elsewhere
                  (check-vars-not-free
                   (bfr-and-x-do-not-use-elsewhere)
                   ,(bfr-and-macro-exec-part (cdr args)))))))))

(defmacro bfr-and (&rest args)
  `(mbe :logic ,(bfr-and-macro-logic-part args)
        :exec  ,(bfr-and-macro-exec-part  args)))





(defun bfr-ite-fn (x y z)
  (declare (xargs :guard (and (bfr-p x) (bfr-p y) (bfr-p z))))
  (bfr-fix-vars
   (x y z)
   (mbe :logic
        (bfr-case :bdd (acl2::q-ite x y z)
                  :aig (cond ((eq x t) y)
                             ((eq x nil) z)
                             (t (acl2::aig-ite x y z))))
        :exec
        (if (and (booleanp x) (booleanp y) (booleanp z))
            (if x y z)
          (bfr-case :bdd (acl2::q-ite x y z)
                    :aig (cond ((eq x t) y)
                               ((eq x nil) z)
                               (t (acl2::aig-ite x y z))))))))

(defthm bfr-p-bfr-ite-fn
  (bfr-p (bfr-ite-fn x y z)))

(defthm bfr-eval-bfr-ite-fn
  (equal (bfr-eval (bfr-ite-fn x y z) env)
         (if (bfr-eval x env)
             (bfr-eval y env)
           (bfr-eval z env)))
  :hints (("goal" :in-theory (enable booleanp))
          (acl2::bdd-reasoning)
          (acl2::aig-reasoning)))

(defthm bfr-ite-fn-bools
  (and (equal (bfr-ite-fn t y z) (bfr-fix y))
       (equal (bfr-ite-fn nil y z) (bfr-fix z))))


(defcong bfr-equiv equal (bfr-ite-fn x y z) 1)
(defcong bfr-equiv equal (bfr-ite-fn x y z) 2)
(defcong bfr-equiv equal (bfr-ite-fn x y z) 3)

(in-theory (disable bfr-ite-fn))


(defmacro bfr-ite (x y z)
  (cond ((and (or (quotep y) (atom y))
              (or (quotep z) (atom z)))
         `(bfr-ite-fn ,x ,y ,z))
        (t 
         `(mbe :logic (bfr-ite-fn ,x ,y ,z)
               :exec (let ((bfr-ite-x-do-not-use-elsewhere ,x))
                       (cond
                        ((eq bfr-ite-x-do-not-use-elsewhere nil) (bfrfix ,z))
                        ((eq bfr-ite-x-do-not-use-elsewhere t) (bfrfix ,y))
                        (t
                         (bfr-ite-fn bfr-ite-x-do-not-use-elsewhere
                                     ,y ,z))))))))


(defun bfr-binary-or (x y)
  (declare (xargs :guard (and (bfr-p x) (bfr-p y))))
  (mbe :logic
       (bfr-case :bdd (acl2::q-or (bfrfix x) (bfrfix y))
                 :aig (acl2::aig-or (bfrfix x) (bfrfix y)))
       :exec
       (if (and (booleanp x) (booleanp y))
           (or x y)
         (bfr-case :bdd (acl2::q-or (bfrfix x) (bfrfix y))
                   :aig (acl2::aig-or (bfrfix x) (bfrfix y))))))

(defthm bfr-p-bfr-binary-or
  (bfr-p (bfr-binary-or x y)))

(defthm bfr-eval-bfr-binary-or
  (equal (bfr-eval (bfr-binary-or x y) env)
         (or (bfr-eval x env)
             (bfr-eval y env)))
  :hints (("goal" :in-theory (enable booleanp))
          (acl2::bdd-reasoning)
          (acl2::aig-reasoning)))

(defthm bfr-or-of-t
  (and (equal (bfr-binary-or t y) t)
       (equal (bfr-binary-or y t) t))
  :hints(("Goal" :in-theory (enable acl2::aig-or
                                    acl2::aig-and
                                    acl2::aig-not))))

(defcong bfr-equiv equal (bfr-binary-or x y) 1)
(defcong bfr-equiv equal (bfr-binary-or x y) 2)

(in-theory (disable bfr-binary-or))



(defun bfr-or-macro-logic-part (args)
  (declare (xargs :mode :program))
  (cond ((atom args) 
         nil)
        ((atom (cdr args)) 
         (car args))
        (t
         `(bfr-binary-or ,(car args) ,(bfr-or-macro-logic-part (cdr args))))))

(defun bfr-or-macro-exec-part (args)
  (declare (xargs :mode :program))
  (cond ((atom args) 
         nil)
        ((atom (cdr args)) 
         (car args))
        (t 
         `(let ((bfr-or-x-do-not-use-elsewhere ,(car args)))
            ;; We could be slightly more permissive and just check
            ;; for any non-nil atom here.  But it's probably faster
            ;; to check equality with t and we probably don't care
            ;; about performance on non-ubddp bdds?
            (if (eq t bfr-or-x-do-not-use-elsewhere)
                t
              (bfr-binary-or
               bfr-or-x-do-not-use-elsewhere
               (check-vars-not-free
                (bfr-or-x-do-not-use-elsewhere)
                ,(bfr-or-macro-exec-part (cdr args)))))))))

(defmacro bfr-or (&rest args)
  `(mbe :logic ,(bfr-or-macro-logic-part args)
        :exec  ,(bfr-or-macro-exec-part  args)))




(defun bfr-xor (x y)
  (declare (xargs :guard (and (bfr-p x) (bfr-p y))))
  (mbe :logic
       (bfr-case :bdd (acl2::q-xor (bfrfix x) (bfrfix y))
                 :aig (acl2::aig-xor (bfrfix x) (bfrfix y)))
       :exec
       (if (and (booleanp x) (booleanp y))
           (xor x y)
         (bfr-case :bdd (acl2::q-xor (bfrfix x) (bfrfix y))
                   :aig (acl2::aig-xor (bfrfix x) (bfrfix y))))))

(defthm bfr-p-bfr-xor
  (bfr-p (bfr-xor x y)))

(defthm bfr-eval-bfr-xor
  (equal (bfr-eval (bfr-xor x y) env)
         (xor (bfr-eval x env)
              (bfr-eval y env)))
  :hints (("goal" :in-theory (enable booleanp))
          (acl2::bdd-reasoning)
          (acl2::aig-reasoning)))

(defcong bfr-equiv equal (bfr-xor x y) 1
  :hints(("Goal" :in-theory (enable booleanp))))
(defcong bfr-equiv equal (bfr-xor x y) 2
  :hints(("Goal" :in-theory (enable booleanp))))

(in-theory (disable bfr-xor))



(defun bfr-iff (x y)
  (declare (xargs :guard (and (bfr-p x) (bfr-p y))))
  (mbe :logic
       (bfr-case :bdd (acl2::q-iff (bfrfix x) (bfrfix y))
                 :aig (acl2::aig-iff (bfrfix x) (bfrfix y)))
       :exec
       (if (and (booleanp x) (booleanp y))
           (iff x y)
         (bfr-case :bdd (acl2::q-iff (bfrfix x) (bfrfix y))
                   :aig (acl2::aig-iff (bfrfix x) (bfrfix y))))))

(defthm bfr-p-bfr-iff
  (bfr-p (bfr-iff x y)))

(defthm bfr-eval-bfr-iff
  (equal (bfr-eval (bfr-iff x y) env)
         (iff (bfr-eval x env)
              (bfr-eval y env)))
  :hints (("goal" :in-theory (enable booleanp))
          (acl2::bdd-reasoning)
          (acl2::aig-reasoning)))


(defcong bfr-equiv equal (bfr-iff x y) 1
  :hints(("Goal" :in-theory (enable booleanp))))
(defcong bfr-equiv equal (bfr-iff x y) 2
  :hints(("Goal" :in-theory (enable booleanp))))

(in-theory (disable bfr-iff))


(defthm bfr-eval-consts
  (and (equal (bfr-eval t env) t)
       (equal (bfr-eval nil env) nil)))



(in-theory (disable bfr-eval bfr-fix bfr-p
                    (:type-prescription bfr-p)))


(defun bfr-var (n)
  (declare (xargs :guard (natp n)))
  (let ((n (lnfix n)))
    (bfr-case :bdd (acl2::qv n)
              :aig n)))

(defthm bfr-p-bfr-var
  (bfr-p (bfr-var n))
  :hints(("Goal" :in-theory (enable bfr-p))))

(in-theory (disable bfr-var (bfr-var)))


(defun  bfr-lookup (n env)
  (declare (xargs :guard (natp n)))
  (let ((n (lnfix n)))
    (bfr-case :bdd (and (acl2::with-guard-checking nil (ec-call (nth n env))) t)
              :aig (let ((look (hons-get n env)))
                     (if look
                         (and (cdr look) t)
                       t)))))

(defthm bfr-eval-bfr-var
  (equal (bfr-eval (bfr-var n) env)
         (bfr-lookup n env))
  :hints(("Goal" :in-theory (enable bfr-lookup bfr-eval bfr-var
                                    acl2::eval-bdd))))

(in-theory (disable bfr-lookup (bfr-lookup)))


(defun bfr-set-var (n val env)
  (declare (xargs :guard (natp n)))
  (let ((n (lnfix n)))
    (bfr-case :bdd (acl2::with-guard-checking
                    nil
                    (ec-call (update-nth n (and val t) env)))
              :aig (hons-acons n (and val t) env))))

(defthm bfr-lookup-bfr-set-var
  (equal (bfr-lookup n (bfr-set-var m val env))
         (if (equal (nfix n) (nfix m))
             (and val t)
           (bfr-lookup n env)))
  :hints(("Goal" :in-theory (e/d (bfr-lookup bfr-set-var)
                                 (update-nth nth)))))

(in-theory (disable bfr-set-var (bfr-set-var)))



;;++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
;; BFR reasoning clause processor
;;++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

(include-book "clause-processors/term-patterns" :dir :system)
(include-book "clause-processors/join-thms" :dir :system)



(defmacro bfr-patterns ()
  '(acl2::get-term-patterns bfr))

(defmacro set-bfr-patterns (val)
  `(acl2::set-term-patterns bfr ,val))

(defmacro add-bfr-pat (val)
  `(acl2::add-term-pattern bfr ,val))

(defmacro add-bfr-pats (&rest val)
  `(acl2::add-term-patterns bfr . ,val))

(defmacro add-bfr-fn-pat (val)
  `(acl2::add-fn-term-pattern bfr ,val))

(defmacro add-bfr-fn-pats (&rest val)
  `(acl2::add-fn-term-patterns bfr . ,val))

(set-bfr-patterns nil)

(add-bfr-fn-pats
 bfr-binary-and bfr-not bfr-binary-or bfr-xor bfr-iff bfr-ite-fn
 bfr-fix)

(add-bfr-pats 't 'nil)

(defun bfr-termp (x bfr-terms pats)
  (or (member-equal x bfr-terms)
      (acl2::match-term-pattern x pats)))



(defmacro bfr-eval-patterns ()
  '(acl2::get-term-patterns bfr-eval))

(defmacro set-bfr-eval-patterns (val)
  `(acl2::set-term-patterns bfr-eval ,val))

(defmacro add-bfr-eval-pat (val)
  `(acl2::add-term-pattern bfr-eval ,val))

(defmacro add-bfr-eval-pats (&rest val)
  `(acl2::add-term-patterns bfr-eval . ,val))

(set-bfr-eval-patterns nil)

(add-bfr-eval-pats (bfr-eval & env))


(defevaluator bfr-cp-ev bfr-cp-evl
  ((bfr-eval a b) (equal a b) (not a)
   (implies a b)
   (if a b c)))

(acl2::def-join-thms bfr-cp-ev)



(mutual-recursion
 (defun collect-bfr-eval-vals (term patterns)
   (cond ((atom term) nil)
         ((eq (car term) 'quote) nil)
         (t (let ((match (acl2::match-term-pattern term patterns)))
              (if match
                  (list (cdr (assoc 'env match)))
                (collect-bfr-eval-vals-list (cdr term) patterns))))))
 (defun collect-bfr-eval-vals-list (clause patterns)
   (if (atom clause)
       nil
     (union-equal (collect-bfr-eval-vals (car clause) patterns)
                  (collect-bfr-eval-vals-list (cdr clause) patterns)))))
 

(include-book "tools/flag" :dir :system)
(flag::make-flag collect-bfr-eval-vals-flag collect-bfr-eval-vals
                 :flag-mapping ((collect-bfr-eval-vals . term)
                                (collect-bfr-eval-vals-list . list)))

(defthm pseudo-term-listp-union-equal
  (implies (and (pseudo-term-listp x) (pseudo-term-listp y))
           (pseudo-term-listp (union-equal x y))))

(defthm-collect-bfr-eval-vals-flag pseudo-term-listp-collect-bfr-eval-vals
  (term (implies (pseudo-termp term)
                 (pseudo-term-listp (collect-bfr-eval-vals term patterns))))
  (list (implies (pseudo-term-listp clause)
                 (pseudo-term-listp (collect-bfr-eval-vals-list clause patterns))))
  :hints (("goal" :induct (collect-bfr-eval-vals-flag flag term clause patterns))))


(defun bfr-eval-vals (clause patterns)
  (let ((collect (collect-bfr-eval-vals-list clause patterns)))
    (or collect '(arbitrary-vals))))

(defthm bfr-eval-vals-pseudo-term-listp
  (implies (pseudo-term-listp clause)
           (pseudo-term-listp (bfr-eval-vals clause patterns))))

(in-theory (disable bfr-eval-vals))

(defun instantiate-bfr-evals (a b vals)
  (if (atom vals)
      nil
    (cons `(not (equal (bfr-eval ,a ,(car vals))
                       (bfr-eval ,b ,(car vals))))
          (instantiate-bfr-evals a b (cdr vals)))))

(defthm instantiate-bfr-evals-correct
  (implies (and ;;(pseudo-termp x)
                ;;(pseudo-termp y)
                ;;(alistp a)
                (equal (bfr-cp-ev x a)
                       (bfr-cp-ev y a)))
           (not (bfr-cp-ev (disjoin (instantiate-bfr-evals x y vals)) a)))
  :hints (("goal" :induct (instantiate-bfr-evals a b vals))))

(defthm pseudo-term-listp-instantiate-bfr-evals
  (implies (and (pseudo-term-listp vals)
                (pseudo-termp a)
                (pseudo-termp b))
           (pseudo-term-listp (instantiate-bfr-evals a b vals))))

(in-theory (disable instantiate-bfr-evals))

(defun instantiate-equals-with-bfr-evals (clause vals bfr-terms patterns)
  (if (atom clause)
      nil
    (let* ((rst-clause (instantiate-equals-with-bfr-evals
                        (cdr clause) vals bfr-terms patterns))
           (lit (car clause)))
      (mv-let (a b)
        (case-match lit
          (('not ('equal a b))
           (mv a b))
          (a (mv a ''nil))
          (& (mv nil nil)))
        (if (and (bfr-termp a bfr-terms patterns)
                 (bfr-termp b bfr-terms patterns))
            (cons (disjoin (instantiate-bfr-evals a b vals))
                  rst-clause)
          (cons lit rst-clause))))))

(defthm instantiate-equals-with-bfr-evals-correct
  (implies (and ;;(pseudo-term-listp clause)
                ;;(alistp a)
                (bfr-cp-ev (disjoin (instantiate-equals-with-bfr-evals
                                     clause vals bfr-terms patterns))
                           a))
           (bfr-cp-ev (disjoin clause) a))
  :hints (("goal" :induct (len clause)
           :in-theory (disable equal-of-booleans-rewrite
                               bfr-termp
                               (:type-prescription bfr-termp)
                               instantiate-equals-with-bfr-evals
                               (:type-prescription member-equal)
                               (:type-prescription acl2::match-term-pattern))
           :expand ((instantiate-equals-with-bfr-evals
                     clause vals bfr-terms patterns)))))



(defthm pseudo-term-listp-instantiate-equals-with-bfr-evals
  (implies (and (pseudo-term-listp clause)
                (pseudo-term-listp vals))
           (pseudo-term-listp (instantiate-equals-with-bfr-evals
                               clause vals bfr-terms patterns)))
  :hints (("goal" :induct (len clause)
           :in-theory (disable equal-of-booleans-rewrite
                               bfr-termp
                               (:type-prescription bfr-termp)
                               instantiate-equals-with-bfr-evals
                               (:type-prescription member-equal)
                               (:type-prescription acl2::match-term-pattern))
           :expand ((instantiate-equals-with-bfr-evals
                     clause vals bfr-terms patterns)
                    (instantiate-equals-with-bfr-evals
                     nil vals bfr-terms patterns)))))


(defun bfr-eval-cp (clause hints)
  (let* ((bfr-terms (car hints))
         (patterns (cadr hints))
         (eval-patterns (caddr hints))
         (vals (bfr-eval-vals clause eval-patterns))
         (clause (instantiate-equals-with-bfr-evals
                  clause vals bfr-terms patterns)))
    (list clause)))

(in-theory (disable instantiate-equals-with-bfr-evals
                    collect-bfr-eval-vals-list))

(defthm bfr-eval-cp-correct
  (implies (and (pseudo-term-listp clause)
                (alistp a)
                (bfr-cp-ev (conjoin-clauses
                            (bfr-eval-cp clause hints))
                           a))
           (bfr-cp-ev (disjoin clause) a))
  :rule-classes :clause-processor)

(defmacro bfr-reasoning (&key or-hint)
  `(if stable-under-simplificationp
       (er-progn 
        ;; This just lets us collect the clauses on which this hint is used.
        ,'(assign bfr-eval-cp-clauses
                  (cons clause
                        (and (boundp-global
                              'bfr-eval-cp-clauses state)
                             (@ bfr-eval-cp-clauses))))
        (let ((bfr-patterns (bfr-patterns))
              (bfr-eval-patterns (bfr-eval-patterns)))
          ,(let ((cphint '`(:clause-processor
                            (bfr-eval-cp
                             clause
                             (list nil ',bfr-patterns
                                   ',bfr-eval-patterns)))))
             `(value ,(if or-hint
                          ``(:or (,,cphint
                                 (:no-thanks t)))
                        cphint)))))
     (value nil)))
    

(defmacro bfr-reasoning-mode (flg)
  (if flg
      '(add-default-hints '((bfr-reasoning)))
    '(remove-default-hints '((bfr-reasoning)))))







(table prove-congruence-theory-table
       nil '((bfr-equiv bfr-fix-when-bfr-p
                        bfr-p-bfr-fix)) :clear)

(defmacro prove-congruence (equiv1 equiv2 fncall argnum
                                   &key fix theory)
  (let* ((var (nth argnum fncall))
         (var-equiv (intern-in-package-of-symbol
                     (coerce (acl2::packn1 (list var '-equiv))
                             'string)
                     (if (equal (symbol-package-name equiv1)
                                *main-lisp-package-name*)
                         (pkg-witness "ACL2")
                       equiv1)))
         (fncall2 (update-nth argnum
                              (list fix var)
                              fncall)))
    `(encapsulate nil
       (local (defthm local-lemma-for-prove-congruence
                (equal ,fncall2
                       ,fncall)
                :hints (("goal" :in-theory ,theory
                         :expand (,fncall ,fncall2)))
                :rule-classes nil))
       (defcong ,equiv1 ,equiv2 ,fncall ,argnum
         :hints (("goal" :use ((:instance local-lemma-for-prove-congruence)
                               (:instance local-lemma-for-prove-congruence
                                          (,var ,var-equiv)))))))))

(defun prove-congruences-fn (n equivs fncall world)
  (declare (xargs :mode :program))
  (if (atom equivs)
      nil
    (if (car equivs)
        (let ((fix (caadr (body (car equivs) nil world)))
              (theory (cdr (assoc (car equivs)
                                  (table-alist 'prove-congruence-theory-table world)))))
          ;; pull out FOO from (equal (foo x) (foo y))
          (cons `(prove-congruence ,(car equivs) equal
                                   ,fncall ,n
                                   :fix ,fix
                                   :theory ',theory)
                (prove-congruences-fn (1+ n) (cdr equivs) fncall world)))
      (prove-congruences-fn (1+ n) (cdr equivs) fncall world))))

(defmacro prove-congruences (equivs fn)
  `(make-event
    (cons 'progn
          (prove-congruences-fn 1 ',equivs
                                (cons ',fn
                                      (fgetprop ',fn 'formals nil (w state)))
                                (w state)))))


