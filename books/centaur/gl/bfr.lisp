

(in-package "GL")
(include-book "centaur/misc/universal-equiv" :dir :system)
(include-book "centaur/misc/arith-equivs" :dir :system)

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
(include-book "centaur/ubdds/param" :dir :system)
(include-book "../aig/witness")
(include-book "../aig/misc")

(local (in-theory (enable booleanp)))

;; (defun bfr-p (x)
;;   (declare (xargs :guard t)
;;            (ignorable x))
;;   (mbe :logic 
;;        (bfr-case :bdd (acl2::ubddp x) :aig t)
;;        :exec (or (booleanp x)
;;                  (bfr-case :bdd (acl2::ubddp x) :aig t))))

;; (defthm bfr-p-booleanp
;;   (booleanp (bfr-p x))
;;   :rule-classes :type-prescription)


;; (defthmd bfr-p-of-boolean
;;   (implies (booleanp x) (bfr-p x))
;;   :hints (("goal" :in-theory (enable bfr-p acl2::ubddp))))

;; (defun bfr-fix (x)
;;   (declare (xargs :guard t))
;;   (mbe :logic
;;        (bfr-case :bdd (acl2::ubdd-fix x) :aig x)
;;        :exec
;;        (if (booleanp x)
;;            x
;;          (bfr-case :bdd (acl2::ubdd-fix x) :aig x))))

;; (defthm bfr-p-bfr-fix
;;   (bfr-p (bfr-fix x)))

;; (defthm bfr-fix-when-bfr-p
;;   (implies (bfr-p x)
;;            (equal (bfr-fix x) x)))


;; (defun bfr-equiv (a b)
;;   (equal (bfr-fix a) (bfr-fix b)))

;; (defequiv bfr-equiv)

;; (defthm bfr-fix-bfr-equiv
;;   (bfr-equiv (bfr-fix x) x))

;; (defmacro bfrfix (x)
;;   `(mbe :logic (bfr-fix ,x) :exec ,x))

;; (defun bfr-fix-bindings (vars)
;;   (if (atom vars)
;;       nil
;;     (cons `(,(car vars) (bfrfix ,(car vars)))
;;           (bfr-fix-bindings (cdr vars)))))

;; (defmacro bfr-fix-vars (vars body)
;;   `(let ,(bfr-fix-bindings vars)
;;      (declare (ignorable . ,vars))
;;      ,body))
     

(defun bfr-eval (x env)
  (declare (xargs :guard t))
  (mbe :logic
       (bfr-case :bdd (acl2::eval-bdd x env)
                 :aig (acl2::aig-eval x env))
       :exec
       (if (booleanp x)
           x
         (bfr-case :bdd (acl2::eval-bdd x env)
                   :aig (acl2::aig-eval x env)))))

;; (defthmd bfr-eval-of-bfr-fix
;;   (equal (bfr-eval (bfr-fix x) env)
;;          (bfr-eval x env))
;;   :hints (("goal" :use acl2::eval-bdd-ubdd-fix
;;            :in-theory (disable acl2::eval-bdd-ubdd-fix))))

;; (defcong bfr-equiv equal (bfr-eval x env) 1
;;   :hints (("goal" :use ((:instance bfr-eval-of-bfr-fix)
;;                         (:instance bfr-eval-of-bfr-fix
;;                                    (x x-equiv)))
;;            :in-theory (disable bfr-eval bfr-fix))))

(defun bfr-not (x)
  (declare (xargs :guard t))
  (mbe :logic
       (bfr-case :bdd (acl2::q-not x)
                 :aig (acl2::aig-not x))
       :exec
       (if (booleanp x)
           (not x)
         (bfr-case :bdd (acl2::q-not x)
                   :aig (acl2::aig-not x)))))

;; (defthm bfr-p-bfr-not
;;   (bfr-p (bfr-not x)))

;; (local (acl2::add-bdd-fn-pat acl2::ubdd-fix))

(defthm bfr-eval-bfr-not
  (equal (bfr-eval (bfr-not x) env)
         (not (bfr-eval x env)))
  :hints (("goal" :in-theory (enable booleanp))))

;;(defcong bfr-equiv bfr-equiv (bfr-not x) 1)

(in-theory (disable bfr-not))


(defun bfr-binary-and (x y)
  (declare (xargs :guard t))
  (mbe :logic 
       (bfr-case :bdd (acl2::q-binary-and x y)
                 :aig (acl2::aig-and x y))
       :exec
       (cond ((not x) nil)
             ((not y) nil)
             ((and (eq x t) (eq y t)) t)
             (t (bfr-case :bdd (acl2::q-binary-and x y)
                          :aig (acl2::aig-and x y))))))

;; (defthm bfr-p-bfr-binary-and
;;   (bfr-p (bfr-binary-and x y)))

(defthm bfr-eval-bfr-binary-and
  (equal (bfr-eval (bfr-binary-and x y) env)
         (and (bfr-eval x env)
              (bfr-eval y env)))
  :hints (("goal" :in-theory (e/d (booleanp) ((force))))))

(defthm bfr-and-of-nil
  (and (equal (bfr-binary-and nil y) nil)
       (equal (bfr-binary-and x nil) nil))
  :hints(("Goal" :in-theory (enable acl2::aig-and))))



;; (defcong bfr-equiv equal (bfr-binary-and a b) 1)

;; (defcong bfr-equiv equal (bfr-binary-and a b) 2)

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
  (declare (xargs :guard t))
  (mbe :logic
       (bfr-case :bdd (acl2::q-ite x y z)
                 :aig (cond ((eq x t) y)
                            ((eq x nil) z)
                            (t (acl2::aig-ite x y z))))
       :exec
       (if (booleanp x)
           (if x y z)
         (bfr-case :bdd (acl2::q-ite x y z)
                   :aig (cond ((eq x t) y)
                              ((eq x nil) z)
                              (t (acl2::aig-ite x y z)))))))

;; (defthm bfr-p-bfr-ite-fn
;;   (bfr-p (bfr-ite-fn x y z)))

(defthm bfr-eval-bfr-ite-fn
  (equal (bfr-eval (bfr-ite-fn x y z) env)
         (if (bfr-eval x env)
             (bfr-eval y env)
           (bfr-eval z env)))
  :hints (("goal" :in-theory (enable booleanp))))

(defthm bfr-ite-fn-bools
  (and (equal (bfr-ite-fn t y z) y)
       (equal (bfr-ite-fn nil y z) z)))


;; (defcong bfr-equiv equal (bfr-ite-fn x y z) 1)
;; (defcong bfr-equiv equal (bfr-ite-fn x y z) 2)
;; (defcong bfr-equiv equal (bfr-ite-fn x y z) 3)

(in-theory (disable bfr-ite-fn))


(defmacro bfr-ite (x y z)
  (cond ((and (or (quotep y) (atom y))
              (or (quotep z) (atom z)))
         `(bfr-ite-fn ,x ,y ,z))
        (t 
         `(mbe :logic (bfr-ite-fn ,x ,y ,z)
               :exec (let ((bfr-ite-x-do-not-use-elsewhere ,x))
                       (cond
                        ((eq bfr-ite-x-do-not-use-elsewhere nil) ,z)
                        ((eq bfr-ite-x-do-not-use-elsewhere t) ,y)
                        (t
                         (bfr-ite-fn bfr-ite-x-do-not-use-elsewhere
                                     ,y ,z))))))))


(defun bfr-binary-or (x y)
  (declare (xargs :guard t))
  (mbe :logic
       (bfr-case :bdd (acl2::q-or x y)
                 :aig (acl2::aig-or x y))
       :exec
       (if (and (booleanp x) (booleanp y))
           (or x y)
         (bfr-case :bdd (acl2::q-or x y)
                   :aig (acl2::aig-or x y)))))

;; (defthm bfr-p-bfr-binary-or
;;   (bfr-p (bfr-binary-or x y)))

(defthm bfr-eval-bfr-binary-or
  (equal (bfr-eval (bfr-binary-or x y) env)
         (or (bfr-eval x env)
             (bfr-eval y env)))
  :hints (("goal" :in-theory (e/d (booleanp) ((force))))))

(defthm bfr-or-of-t
  (and (equal (bfr-binary-or t y) t)
       (equal (bfr-binary-or y t) t))
  :hints(("Goal" :in-theory (enable acl2::aig-or
                                    acl2::aig-and
                                    acl2::aig-not))))

;; (defcong bfr-equiv equal (bfr-binary-or x y) 1)
;; (defcong bfr-equiv equal (bfr-binary-or x y) 2)

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
  (declare (xargs :guard t))
  (mbe :logic
       (bfr-case :bdd (acl2::q-xor x y)
                 :aig (acl2::aig-xor x y))
       :exec
       (if (and (booleanp x) (booleanp y))
           (xor x y)
         (bfr-case :bdd (acl2::q-xor x y)
                   :aig (acl2::aig-xor x y)))))

;; (defthm bfr-p-bfr-xor
;;   (bfr-p (bfr-xor x y)))

(defthm bfr-eval-bfr-xor
  (equal (bfr-eval (bfr-xor x y) env)
         (xor (bfr-eval x env)
              (bfr-eval y env)))
  :hints (("goal" :in-theory (e/d (booleanp) ((force))))))

;; (defcong bfr-equiv equal (bfr-xor x y) 1
;;   :hints(("Goal" :in-theory (enable booleanp))))
;; (defcong bfr-equiv equal (bfr-xor x y) 2
;;   :hints(("Goal" :in-theory (enable booleanp))))

(in-theory (disable bfr-xor))



(defun bfr-iff (x y)
  (declare (xargs :guard t))
  (mbe :logic
       (bfr-case :bdd (acl2::q-iff x y)
                 :aig (acl2::aig-iff x y))
       :exec
       (if (and (booleanp x) (booleanp y))
           (iff x y)
         (bfr-case :bdd (acl2::q-iff x y)
                   :aig (acl2::aig-iff x y)))))

;; (defthm bfr-p-bfr-iff
;;   (bfr-p (bfr-iff x y)))

(defthm bfr-eval-bfr-iff
  (equal (bfr-eval (bfr-iff x y) env)
         (iff (bfr-eval x env)
              (bfr-eval y env)))
  :hints (("goal" :in-theory (e/d (booleanp) ((force))))))


;; (defcong bfr-equiv equal (bfr-iff x y) 1
;;   :hints(("Goal" :in-theory (enable booleanp))))
;; (defcong bfr-equiv equal (bfr-iff x y) 2
;;   :hints(("Goal" :in-theory (enable booleanp))))

(in-theory (disable bfr-iff))


(defthm bfr-eval-consts
  (and (equal (bfr-eval t env) t)
       (equal (bfr-eval nil env) nil)))



;; (in-theory (disable bfr-eval bfr-fix bfr-p
;;                     (:type-prescription bfr-p)))


(defun bfr-var (n)
  (declare (xargs :guard (natp n)))
  (let ((n (lnfix n)))
    (bfr-case :bdd (acl2::qv n)
              :aig n)))

;; (defthm bfr-p-bfr-var
;;   (bfr-p (bfr-var n))
;;   :hints(("Goal" :in-theory (enable bfr-p))))

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

(in-theory (disable bfr-set-var (bfr-set-var) bfr-eval))


(defcong acl2::nat-equiv equal (bfr-var n) 1
  :hints(("Goal" :in-theory (enable bfr-var))))

(defcong acl2::nat-equiv equal (bfr-lookup n env) 1
  :hints(("Goal" :in-theory (enable bfr-lookup))))

(defcong acl2::nat-equiv equal (bfr-set-var n val env) 1
  :hints(("Goal" :in-theory (enable bfr-set-var))))




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



(acl2::def-universal-equiv
 bfr-equiv
 :qvars (env)
 :equiv-terms ((equal (bfr-eval acl2::x env))))

(defcong bfr-equiv equal (bfr-eval x env) 1
  :hints(("Goal" :in-theory (e/d (bfr-equiv-necc)))))

(defcong bfr-equiv bfr-equiv (bfr-not x) 1
  :hints ((and stable-under-simplificationp
               `(:expand (,(car (last clause)))))))

(defcong bfr-equiv bfr-equiv (bfr-and x y) 1
  :hints ((and stable-under-simplificationp
               `(:expand (,(car (last clause)))))))

(defcong bfr-equiv bfr-equiv (bfr-and x y) 2
  :hints ((and stable-under-simplificationp
               `(:expand (,(car (last clause)))))))

(defcong bfr-equiv bfr-equiv (bfr-or x y) 1
  :hints ((and stable-under-simplificationp
               `(:expand (,(car (last clause)))))))

(defcong bfr-equiv bfr-equiv (bfr-or x y) 2
  :hints ((and stable-under-simplificationp
               `(:expand (,(car (last clause)))))))

(defcong bfr-equiv bfr-equiv (bfr-xor x y) 1
  :hints ((and stable-under-simplificationp
               `(:expand (,(car (last clause)))))))

(defcong bfr-equiv bfr-equiv (bfr-xor x y) 2
  :hints ((and stable-under-simplificationp
               `(:expand (,(car (last clause)))))))

(defcong bfr-equiv bfr-equiv (bfr-iff x y) 1
  :hints ((and stable-under-simplificationp
               `(:expand (,(car (last clause)))))))

(defcong bfr-equiv bfr-equiv (bfr-iff x y) 2
  :hints ((and stable-under-simplificationp
               `(:expand (,(car (last clause)))))))

(defcong bfr-equiv bfr-equiv (bfr-ite x y z) 1
  :hints ((and stable-under-simplificationp
               `(:expand (,(car (last clause)))))))

(defcong bfr-equiv bfr-equiv (bfr-ite x y z) 2
  :hints ((and stable-under-simplificationp
               `(:expand (,(car (last clause)))))))

(defcong bfr-equiv bfr-equiv (bfr-ite x y z) 3
  :hints ((and stable-under-simplificationp
               `(:expand (,(car (last clause)))))))



(defun bfr-to-param-space (p x)
  (declare (xargs :guard t)
           (ignorable p))
  (bfr-case :bdd (acl2::to-param-space p x)
            :aig (acl2::aig-restrict
                  x (acl2::aig-extract-iterated-assigns-alist p 10))))

(defun bfr-to-param-space-weak (p x)
  (declare (xargs :guard t)
           (ignorable p))
  (bfr-case :bdd (acl2::to-param-space p x)
            :aig x))

(defun bfr-from-param-space (p x)
  (declare (xargs :guard t)
           (ignorable p))
  (bfr-case :bdd (acl2::from-param-space p x)
            :aig x))


(defun bfr-param-env (p env)
  (declare (xargs :guard t)
           (ignorable p))
  (bfr-case :bdd (acl2::param-env p env)
            :aig env))

(defthmd bfr-eval-to-param-space
  (implies (bfr-eval p env)
           (equal (bfr-eval (bfr-to-param-space p x)
                            (bfr-param-env p env))
                  (bfr-eval x env)))
  :hints(("Goal" :in-theory (e/d* (bfr-eval
                                   bfr-to-param-space
                                   acl2::param-env-to-param-space)))))

(defthm bfr-eval-to-param-space-weak
  (implies (bfr-eval p env)
           (equal (bfr-eval (bfr-to-param-space-weak p x)
                            (bfr-param-env p env))
                  (bfr-eval x env)))
  :hints(("Goal" :in-theory (e/d* (bfr-eval
                                   bfr-to-param-space-weak
                                   acl2::param-env-to-param-space)))))


(defthm bfr-eval-from-param-space
  (implies (bfr-eval p env)
           (equal (bfr-eval (bfr-from-param-space p x)
                            env)
                  (bfr-eval x (bfr-param-env p env))))
  :hints(("Goal" :in-theory (e/d* (bfr-eval bfr-param-env
                                   bfr-from-param-space
                                   acl2::param-env-to-param-space)))))



(defun bfr-unparam-env (p env)
  (declare (xargs :guard t))
  (bfr-case :bdd (acl2::unparam-env p env)
            :aig (append (acl2::aig-extract-iterated-assigns-alist p 10)
                         env)))

(defthm bfr-eval-to-param-space-with-unparam-env
  (equal (bfr-eval (bfr-to-param-space p x) env)
         (bfr-eval x (bfr-unparam-env p env)))
  :hints (("goal" :do-not-induct t
           :in-theory (enable bfr-eval
                              acl2::unparam-env-to-param-space)))
  :otf-flg t)

(local (defthm aig-eval-of-extract-iterated-assigns-self
         (implies (acl2::aig-eval x env)
                  (equal (acl2::aig-eval x
                                         (append
                                          (acl2::aig-extract-iterated-assigns-alist
                                           x n)
                                          env))
                         t))))

(defthm bfr-eval-to-param-space-weak-with-unparam-env
  (implies (not (bfr-eval x (bfr-unparam-env x env)))
           (not (bfr-eval (bfr-to-param-space-weak x x) env)))
  :hints(("Goal" :in-theory (e/d (bfr-eval bfr-to-param-space-weak
                                           acl2::unparam-env-to-param-space
                                           bfr-unparam-env)
                                 (acl2::eval-bdd acl2::aig-eval)))))



(defthm bfr-unparam-env-of-param-env
  (implies (bfr-eval p env)
           (equal (bfr-eval x (bfr-unparam-env p (bfr-param-env p env)))
                  (bfr-eval x env)))
  :hints(("Goal" :in-theory (enable bfr-eval))))

(defthm bfr-param-env-of-unparam-env-of-param-env
  (implies (bfr-eval p env)
           (equal (bfr-eval x (bfr-param-env
                               p
                               (bfr-unparam-env
                                p
                                (bfr-param-env p env))))
                  (bfr-eval x (bfr-param-env p env))))
  :hints(("Goal" :in-theory (disable bfr-param-env bfr-unparam-env
                                     bfr-from-param-space)
          :use ((:instance bfr-eval-from-param-space
                 (env (bfr-unparam-env p (bfr-param-env p env))))))))

(defthm bfr-lookup-of-unparam-env-of-param-env
  (implies (bfr-eval p env)
           (equal (bfr-lookup x (bfr-unparam-env p (bfr-param-env p env)))
                  (bfr-lookup x env)))
  :hints(("Goal" :use ((:instance bfr-unparam-env-of-param-env
                        (x (bfr-var x))))
          :in-theory (disable bfr-unparam-env-of-param-env))))

(in-theory (disable bfr-to-param-space
                    bfr-to-param-space-weak
                    bfr-from-param-space
                    bfr-unparam-env
                    bfr-param-env))


(defun-sk bfr-depends-on (k x)
  (exists (env v)
          (not (equal (bfr-eval x (bfr-set-var k v env))
                      (bfr-eval x env)))))

(in-theory (disable bfr-depends-on
                    bfr-depends-on-suff))

(defthm bfr-eval-of-set-non-dep
  (implies (not (bfr-depends-on k x))
           (equal (bfr-eval x (bfr-set-var k v env))
                  (bfr-eval x env)))
  :hints(("Goal" :use bfr-depends-on-suff)))

(defthm bfr-depends-on-of-bfr-var
  (equal (bfr-depends-on m (bfr-var n))
         (equal (nfix m) (nfix n)))
  :hints(("Goal" :in-theory (disable nfix))
         (and stable-under-simplificationp
              (if (eq (caar (last clause)) 'not)
                  '(:expand ((bfr-depends-on m (bfr-var n))))
                '(:use ((:instance bfr-depends-on-suff
                         (k m) (x (bfr-var n))
                         (v (not (bfr-lookup n env))))))))))


(defthm no-new-deps-of-bfr-not
  (implies (not (bfr-depends-on k x))
           (not (bfr-depends-on k (bfr-not x))))
  :hints(("Goal" :expand ((bfr-depends-on k (bfr-not x))))))

(defthm no-new-deps-of-bfr-and
  (implies (and (not (bfr-depends-on k x))
                (not (bfr-depends-on k y)))
           (not (bfr-depends-on k (bfr-binary-and x y))))
  :hints (("Goal" :expand ((bfr-depends-on k (bfr-binary-and x y))))))

(defthm no-new-deps-of-bfr-or
  (implies (and (not (bfr-depends-on k x))
                (not (bfr-depends-on k y)))
           (not (bfr-depends-on k (bfr-binary-or x y))))
  :hints (("goal" :expand ((bfr-depends-on k (bfr-binary-or x y))))))

(defthm no-new-deps-of-bfr-xor
  (implies (and (not (bfr-depends-on k x))
                (not (bfr-depends-on k y)))
           (not (bfr-depends-on k (bfr-xor x y))))
  :hints (("goal" :expand ((bfr-depends-on k (bfr-xor x y))))))

(defthm no-new-deps-of-bfr-iff
  (implies (and (not (bfr-depends-on k x))
                (not (bfr-depends-on k y)))
           (not (bfr-depends-on k (bfr-iff x y))))
  :hints (("goal" :expand ((bfr-depends-on k (bfr-iff x y))))))

(defthm no-new-deps-of-bfr-ite
  (implies (and (not (bfr-depends-on k x))
                (not (bfr-depends-on k y))
                (not (bfr-depends-on k z)))
           (not (bfr-depends-on k (bfr-ite-fn x y z))))
  :hints (("goal" :expand ((bfr-depends-on k (bfr-ite-fn x y z))))))

(defthm no-deps-of-bfr-constants
  (and (not (bfr-depends-on k t))
       (not (bfr-depends-on k nil)))
  :hints (("goal" :expand ((bfr-depends-on k nil)
                           (bfr-depends-on k t)))))



(defun-sk pbfr-depends-on (k p x)
  (exists (env v)
          (and (bfr-eval p env)
               (bfr-eval p (bfr-set-var k v env))
               (not (equal (bfr-eval x (bfr-param-env p (bfr-set-var k v env)))
                           (bfr-eval x (bfr-param-env p env)))))))

(in-theory (disable pbfr-depends-on pbfr-depends-on-suff))

(defthm pbfr-eval-of-set-non-dep
  (implies (and (not (pbfr-depends-on k p x))
                (bfr-eval p env)
                (bfr-eval p (bfr-set-var k v env)))
           (equal (bfr-eval x (bfr-param-env p (bfr-set-var k v env)))
                  (bfr-eval x (bfr-param-env p env))))
  :hints (("goal" :use pbfr-depends-on-suff)))

(defthm pbfr-depends-on-of-bfr-var
  (implies (and (not (bfr-depends-on m p))
                (bfr-eval p env))
           (equal (pbfr-depends-on m p (bfr-to-param-space p (bfr-var n)))
                  (equal (nfix m) (nfix n))))
  :hints(("Goal" :in-theory (disable nfix))
         (and stable-under-simplificationp
              (if (eq (caar (last clause)) 'not)
                  '(:expand ((pbfr-depends-on m p (bfr-to-param-space p (bfr-var n)))))
                '(:use ((:instance pbfr-depends-on-suff
                         (k m) (x (bfr-to-param-space p (bfr-var n)))
                         (v (not (bfr-lookup n env)))))
                  :in-theory (disable pbfr-eval-of-set-non-dep nfix))))))

(defthm pbfr-depends-on-of-bfr-var-weak
  (implies (and (not (bfr-depends-on m p))
                (bfr-eval p env))
           (equal (pbfr-depends-on m p (bfr-to-param-space-weak p (bfr-var n)))
                  (equal (nfix m) (nfix n))))
  :hints(("Goal" :in-theory (disable nfix))
         (and stable-under-simplificationp
              (if (eq (caar (last clause)) 'not)
                  '(:expand ((pbfr-depends-on m p (bfr-to-param-space-weak p (bfr-var n)))))
                '(:use ((:instance pbfr-depends-on-suff
                         (k m) (x (bfr-to-param-space-weak p (bfr-var n)))
                         (v (not (bfr-lookup n env)))))
                  :in-theory (disable pbfr-eval-of-set-non-dep nfix))))))

(defthm pbfr-depends-on-of-constants
  (and (not (pbfr-depends-on k p t))
       (not (pbfr-depends-on k p nil)))
  :hints (("goal" :expand ((pbfr-depends-on k p t)
                           (pbfr-depends-on k p nil)))))

(defthm no-new-deps-of-pbfr-not
  (implies (not (pbfr-depends-on k p x))
           (not (pbfr-depends-on k p (bfr-not x))))
  :hints(("Goal" :expand ((pbfr-depends-on k p (bfr-not x))))))


(defthm no-new-deps-of-pbfr-and
  (implies (and (not (pbfr-depends-on k p x))
                (not (pbfr-depends-on k p y)))
           (not (pbfr-depends-on k p (bfr-binary-and x y))))
  :hints (("Goal" :expand ((pbfr-depends-on k p (bfr-binary-and x y))))))

(defthm no-new-deps-of-pbfr-or
  (implies (and (not (pbfr-depends-on k p x))
                (not (pbfr-depends-on k p y)))
           (not (pbfr-depends-on k p (bfr-binary-or x y))))
  :hints (("goal" :expand ((pbfr-depends-on k p (bfr-binary-or x y))))))

(defthm no-new-deps-of-pbfr-xor
  (implies (and (not (pbfr-depends-on k p x))
                (not (pbfr-depends-on k p y)))
           (not (pbfr-depends-on k p (bfr-xor x y))))
  :hints (("goal" :expand ((pbfr-depends-on k p (bfr-xor x y))))))

(defthm no-new-deps-of-pbfr-iff
  (implies (and (not (pbfr-depends-on k p x))
                (not (pbfr-depends-on k p y)))
           (not (pbfr-depends-on k p (bfr-iff x y))))
  :hints (("goal" :expand ((pbfr-depends-on k p (bfr-iff x y))))))

(defthm no-new-deps-of-pbfr-ite
  (implies (and (not (pbfr-depends-on k p x))
                (not (pbfr-depends-on k p y))
                (not (pbfr-depends-on k p z)))
           (not (pbfr-depends-on k p (bfr-ite-fn x y z))))
  :hints (("goal" :expand ((pbfr-depends-on k p (bfr-ite-fn x y z))))))

(defthm pbfr-depends-on-when-booleanp
  (implies (booleanp y)
           (not (pbfr-depends-on k p y)))
  :hints(("Goal" :in-theory (enable booleanp)))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))









;; (defund ubdd-deps-to-nat-list (n deps)
;;   (declare (xargs :guard (natp n)))
;;   (if (atom deps)
;;       nil
;;     (if (car deps)
;;         (cons n (ubdd-deps-to-nat-list (+ 1 n) (cdr deps)))
;;       (ubdd-deps-to-nat-list (+ 1 n) (cdr deps)))))


;; (encapsulate nil
;;   (local (include-book "arithmetic/top-with-meta" :dir :system))
;;   (defthm member-of-ubdd-deps-to-nat-list
;;     (implies (integerp n)
;;              (iff (member m (ubdd-deps-to-nat-list n deps))
;;                   (and (integerp m)
;;                        (<= n m)
;;                        (nth (- m n) deps))))
;;     :hints (("goal" :induct (ubdd-deps-to-nat-list n deps)
;;              :in-theory (enable ubdd-deps-to-nat-list natp posp)))))


;; (defun bfr-deps (x)
;;   (declare (xargs :guard t))
;;   (bfr-case :bdd (ubdd-deps-to-nat-list 0 (acl2::ubdd-deps x))
;;             :aig (acl2::aig-vars x)))

;; (local (defthm aig-eval-acons-when-not-in-vars
;;          (implies (not (member k (acl2::aig-vars x)))
;;                   (equal (acl2::aig-eval x (cons (cons k v) env))
;;                          (acl2::aig-eval x env)))))

;; (defund bfr-depends-on (k x)
;;   (declare (xargs :guard (natp k)))
;;   (consp (member (lnfix k) (bfr-deps x))))

;; (local (defthm consp-member
;;          (iff (consp (member k x))
;;               (member k x))))

;; (defthm bfr-eval-of-set-non-dep
;;   (implies (not (bfr-depends-on k x))
;;            (equal (bfr-eval x (bfr-set-var k v env))
;;                   (bfr-eval x env)))
;;   :hints(("Goal" :in-theory (e/d (bfr-eval
;;                                   bfr-set-var
;;                                   bfr-depends-on)
;;                                  (update-nth)))))

;; (defthm bfr-depends-on-of-bfr-var
;;   (equal (bfr-depends-on m (bfr-var n))
;;          (equal (nfix m) (nfix n)))
;;   :hints(("Goal" :in-theory (e/d (bfr-depends-on bfr-var)
;;                                  ((bfr-deps))))))

;; (local
;;  #!acl2
;;  (progn
;;    (defthm aig-vars-of-aig-not
;;      (equal (aig-vars (aig-not x))
;;             (aig-vars x))
;;      :hints(("Goal" :in-theory (enable aig-not))))

;;    (defthm aig-vars-of-aig-and
;;      (implies (and (not (member v (aig-vars x)))
;;                    (not (member v (aig-vars y))))
;;               (not (member v (aig-vars (aig-and x y)))))
;;      :hints(("Goal" :in-theory (enable aig-and))))

;;    (defthm aig-vars-of-aig-or
;;      (implies (and (not (member v (aig-vars x)))
;;                    (not (member v (aig-vars y))))
;;               (not (member v (aig-vars (aig-or x y)))))
;;      :hints(("Goal" :in-theory (enable aig-or))))

;;    (defthm aig-vars-of-aig-xor
;;      (implies (and (not (member v (aig-vars x)))
;;                    (not (member v (aig-vars y))))
;;               (not (member v (aig-vars (aig-xor x y)))))
;;      :hints(("Goal" :in-theory (enable aig-xor))))

;;    (defthm aig-vars-of-aig-iff
;;      (implies (and (not (member v (aig-vars x)))
;;                    (not (member v (aig-vars y))))
;;               (not (member v (aig-vars (aig-iff x y)))))
;;      :hints(("Goal" :in-theory (enable aig-iff))))

;;    (defthm aig-vars-of-aig-ite
;;      (implies (and (not (member v (aig-vars x)))
;;                    (not (member v (aig-vars y)))
;;                    (not (member v (aig-vars z))))
;;               (not (member v (aig-vars (aig-ite x y z)))))
;;      :hints(("Goal" :in-theory (enable aig-ite))))))

;; (defthm no-new-deps-of-bfr-not
;;   (implies (not (bfr-depends-on k x))
;;            (not (bfr-depends-on k (bfr-not x))))
;;   :hints(("Goal" :in-theory (e/d (bfr-depends-on bfr-not)
;;                                  (nth)))))

;; (defthm no-new-deps-of-bfr-and
;;   (implies (and (not (bfr-depends-on k x))
;;                 (not (bfr-depends-on k y)))
;;            (not (bfr-depends-on k (bfr-binary-and x y))))
;;   :hints(("Goal" :in-theory (e/d (bfr-depends-on bfr-binary-and)
;;                                  (nth)))))

;; (defthm no-new-deps-of-bfr-or
;;   (implies (and (not (bfr-depends-on k x))
;;                 (not (bfr-depends-on k y)))
;;            (not (bfr-depends-on k (bfr-binary-or x y))))
;;   :hints(("Goal" :in-theory (e/d (bfr-depends-on bfr-binary-or)
;;                                  (nth)))))

;; (defthm no-new-deps-of-bfr-xor
;;   (implies (and (not (bfr-depends-on k x))
;;                 (not (bfr-depends-on k y)))
;;            (not (bfr-depends-on k (bfr-xor x y))))
;;   :hints(("Goal" :in-theory (e/d (bfr-depends-on bfr-xor)
;;                                  (nth)))))

;; (defthm no-new-deps-of-bfr-iff
;;   (implies (and (not (bfr-depends-on k x))
;;                 (not (bfr-depends-on k y)))
;;            (not (bfr-depends-on k (bfr-iff x y))))
;;   :hints(("Goal" :in-theory (e/d (bfr-depends-on bfr-iff)
;;                                  (nth)))))

;; (defthm no-new-deps-of-bfr-ite
;;   (implies (and (not (bfr-depends-on k x))
;;                 (not (bfr-depends-on k y))
;;                 (not (bfr-depends-on k z)))
;;            (not (bfr-depends-on k (bfr-ite-fn x y z))))
;;   :hints(("Goal" :in-theory (e/d (bfr-depends-on bfr-ite-fn)
;;                                  (nth)))))

;; (defthm no-deps-of-bfr-constants
;;   (and (not (bfr-depends-on k t))
;;        (not (bfr-depends-on k nil)))
;;   :hints(("Goal" :in-theory (e/d (bfr-depends-on) ((bfr-deps))))))






;; (table prove-congruence-theory-table
;;        nil '((bfr-equiv bfr-fix-when-bfr-p
;;                         bfr-p-bfr-fix)) :clear)

;; (defmacro prove-congruence (equiv1 equiv2 fncall argnum
;;                                    &key fix theory)
;;   (let* ((var (nth argnum fncall))
;;          (var-equiv (intern-in-package-of-symbol
;;                      (coerce (acl2::packn1 (list var '-equiv))
;;                              'string)
;;                      (if (equal (symbol-package-name equiv1)
;;                                 *main-lisp-package-name*)
;;                          (pkg-witness "ACL2")
;;                        equiv1)))
;;          (fncall2 (update-nth argnum
;;                               (list fix var)
;;                               fncall)))
;;     `(encapsulate nil
;;        (local (defthm local-lemma-for-prove-congruence
;;                 (equal ,fncall2
;;                        ,fncall)
;;                 :hints (("goal" :in-theory ,theory
;;                          :expand (,fncall ,fncall2)))
;;                 :rule-classes nil))
;;        (defcong ,equiv1 ,equiv2 ,fncall ,argnum
;;          :hints (("goal" :use ((:instance local-lemma-for-prove-congruence)
;;                                (:instance local-lemma-for-prove-congruence
;;                                           (,var ,var-equiv)))))))))

;; (defun prove-congruences-fn (n equivs fncall world)
;;   (declare (xargs :mode :program))
;;   (if (atom equivs)
;;       nil
;;     (if (car equivs)
;;         (let ((fix (caadr (body (car equivs) nil world)))
;;               (theory (cdr (assoc (car equivs)
;;                                   (table-alist 'prove-congruence-theory-table world)))))
;;           ;; pull out FOO from (equal (foo x) (foo y))
;;           (cons `(prove-congruence ,(car equivs) equal
;;                                    ,fncall ,n
;;                                    :fix ,fix
;;                                    :theory ',theory)
;;                 (prove-congruences-fn (1+ n) (cdr equivs) fncall world)))
;;       (prove-congruences-fn (1+ n) (cdr equivs) fncall world))))

;; (defmacro prove-congruences (equivs fn)
;;   `(make-event
;;     (cons 'progn
;;           (prove-congruences-fn 1 ',equivs
;;                                 (cons ',fn
;;                                       (fgetprop ',fn 'formals nil (w state)))
;;                                 (w state)))))






;; Could just be done on trees but this makes the proofs easier (?)
;; This returns one plus the maximum natural number present -- this way it's
;; similar to the BDD lib's MAX-DEPTH.
;; (defund aig-max-nat (x)
;;   (declare (xargs :guard t))
;;   (cond ((natp x) (+ 1 x))
;;         ((atom x) 0)
;;         ((not (cdr x)) (aig-max-nat (car x)))
;;         (t (max (aig-max-nat (car x))
;;                 (aig-max-nat (cdr x))))))

;; (local
;;  (progn
;;    (defthm aig-eval-of-acons-max-nat
;;      (implies (and (<= (aig-max-nat x) var)
;;                    (natp var))
;;               (equal (acl2::aig-eval x (cons (cons var val) env))
;;                      (acl2::aig-eval x env)))
;;      :hints(("Goal" :in-theory (enable acl2::aig-eval aig-max-nat))))

;;    (defthm aig-max-nat-of-aig-not
;;      (equal (aig-max-nat (acl2::aig-not x))
;;             (aig-max-nat x))
;;      :hints(("Goal" :in-theory (enable acl2::aig-not aig-max-nat))))

;;    ;; (defthm aig-max-nat-of-aig-and
;;    ;;   (<= (aig-max-nat (acl2::aig-and x y)) (max (aig-max-nat x)
;;    ;;                                              (aig-max-nat y)))
;;    ;;   :hints(("Goal" :in-theory (enable acl2::aig-and aig-max-nat)))
;;    ;;   :rule-classes (:rewrite :linear))

;;    (defthm gte-aig-max-nat-of-and
;;      (implies (and (<= (aig-max-nat x) n)
;;                    (<= (aig-max-nat y) n))
;;               (<= (aig-max-nat (acl2::aig-and x y)) n))
;;      :hints(("Goal" :in-theory (enable acl2::aig-and aig-max-nat)))
;;      :rule-classes (:rewrite
;;                     (:linear :match-free :all)))

;;    ;; (defthm aig-max-nat-of-aig-or
;;    ;;   (<= (aig-max-nat (acl2::aig-or x y)) (max (aig-max-nat x)
;;    ;;                                             (aig-max-nat y)))
;;    ;;   :hints(("Goal" :in-theory (e/d (acl2::aig-or aig-max-nat))))
;;    ;;   :rule-classes (:rewrite :linear))

;;    (defthm gte-aig-max-nat-of-or
;;      (implies (and (<= (aig-max-nat x) n)
;;                    (<= (aig-max-nat y) n))
;;               (<= (aig-max-nat (acl2::aig-or x y)) n))
;;      :hints(("Goal" :in-theory (enable acl2::aig-or aig-max-nat)))
;;      :rule-classes (:rewrite
;;                     (:linear :match-free :all)))


;;    ;; (defthm aig-max-nat-of-aig-xor
;;    ;;   (<= (aig-max-nat (acl2::aig-xor x y)) (max (aig-max-nat x)
;;    ;;                                              (aig-max-nat y)))
;;    ;;   :hints(("Goal" :in-theory (enable acl2::aig-xor aig-max-nat)
;;    ;;           :do-not-induct t))
;;    ;;   :rule-classes (:rewrite :linear))

;;    (defthm gte-aig-max-nat-of-xor
;;      (implies (and (<= (aig-max-nat x) n)
;;                    (<= (aig-max-nat y) n))
;;               (<= (aig-max-nat (acl2::aig-xor x y)) n))
;;      :hints(("Goal" :in-theory (enable acl2::aig-xor aig-max-nat)))
;;      :rule-classes (:rewrite
;;                     (:linear :match-free :all)))

;;    (defthm gte-aig-max-nat-of-iff
;;      (implies (and (<= (aig-max-nat x) n)
;;                    (<= (aig-max-nat y) n))
;;               (<= (aig-max-nat (acl2::aig-iff x y)) n))
;;      :hints(("Goal" :in-theory (enable acl2::aig-iff aig-max-nat)))
;;      :rule-classes (:rewrite
;;                     (:linear :match-free :all)))

;;    (defthm gte-aig-max-nat-of-ite
;;      (implies (and (<= (aig-max-nat x) n)
;;                    (<= (aig-max-nat y) n)
;;                    (<= (aig-max-nat z) n))
;;               (<= (aig-max-nat (acl2::aig-ite x y z)) n))
;;      :hints(("Goal" :in-theory (enable acl2::aig-ite aig-max-nat)))
;;      :rule-classes (:rewrite
;;                     (:linear :match-free :all)))))


;; (memoize 'aig-max-nat :condition '(and (consp x) (cdr x)))

;; (local
;;  (progn
;;    (defun ind (x n env)
;;          (if (zp n)
;;              x
;;            (if (car env)
;;                (ind (car x) (1- n) (cdr env))
;;              (ind (cdr x) (1- n) (cdr env)))))

;;    (defthm eval-bdd-of-update-past-max-depth
;;      (implies (<= (max-depth x) (nfix n))
;;               (equal (acl2::eval-bdd x (update-nth n v env))
;;                      (acl2::eval-bdd x env)))
;;      :hints(("Goal" :expand ((:free (env) (acl2::eval-bdd x env))
;;                              (max-depth x)
;;                              (update-nth n v env))
;;              :induct (ind x n env))))))

;; (defund bfr-max-nat-var (x)
;;   (declare (xargs :guard t))
;;   (bfr-case :bdd (max-depth x)
;;             :aig (aig-max-nat x)))

;; (local (in-theory (enable bfr-max-nat-var)))


;; (defthm bfr-eval-of-bfr-set-var-past-max-nat
;;   (implies (and (<= (bfr-max-nat-var x) var)
;;                 (natp var))
;;            (equal (bfr-eval x (bfr-set-var var val env))
;;                   (bfr-eval x env)))
;;   :hints(("Goal" :in-theory (enable bfr-set-var bfr-eval))))



;; (local
;;  (progn
;;    (include-book "arithmetic/top-with-meta" :dir :system)

;;    (defthm max-plus
;;      (equal (max (+ n x) (+ n y))
;;             (+ n (max x y))))

;;    (defthm max-assoc
;;      (equal (max (max a b) c)
;;             (max a (max b c))))

;;    (defthm max-commute
;;      (implies (and (rationalp a) (rationalp b))
;;               (equal (max a b)
;;                      (max b a)))
;;      :rule-classes ((:rewrite :loop-stopper ((a b max)))))

;;    (defthm max-commute-2
;;      (implies (and (rationalp a) (rationalp b))
;;               (equal (max a (max b c))
;;                      (max b (max a c))))
;;      :rule-classes ((:rewrite :loop-stopper ((a b max)))))

;;    (defthm max-id
;;      (equal (max x x) x))

;;    (defthm max-id-2
;;      (equal (max x (max x y)) (max x y)))

;;    (defthm gt-max-implies
;;      (equal (< (max a b) c)
;;             (and (< a c)
;;                  (< b c))))
   
;;    (defthm lt-max-implies
;;      (equal (< c (max a b))
;;             (or (< c a)
;;                 (< c b))))

;;    (defthm gt-max-plus-1-implies
;;      (equal (< (+ 1 (max a b)) c)
;;             (and (< (+ 1 a) c)
;;                  (< (+ 1 b) c))))

;;    (defthm lt-max-plus-1-implies
;;      (equal (< c (+ 1 (max a b)))
;;             (or (< c (+ 1 a))
;;                 (< c (+ 1 b)))))

;;    (defun max-depth2-ind (x y n)
;;      (declare (xargs :measure (+ (acl2-count x) (acl2-count y))))
;;      (if (and (atom x) (atom y))
;;          n
;;        (list (max-depth2-ind (car x) (car y) (1- n))
;;              (max-depth2-ind (cdr x) (cdr y) (1- n)))))

;;    (defthm max-depth-of-q-not
;;      (equal (max-depth (acl2::q-not x))
;;             (max-depth x))
;;      :hints(("Goal" :in-theory (enable acl2::q-not max-depth))))

;;    (defthm max-depth-of-q-and
;;      (implies (and (<= (max-depth x) n)
;;                    (<= (max-depth y) n))
;;               (<= (max-depth (acl2::q-and x y)) n))
;;      :hints(("Goal" :in-theory (e/d (max-depth)
;;                                     ((force) max))
;;              :induct (max-depth2-ind x y n)
;;              :expand ((acl2::q-and x y))))
;;      :rule-classes (:rewrite
;;                     (:linear :match-free :all)))

;;    (defthm max-depth-of-q-or
;;      (implies (and (<= (max-depth x) n)
;;                    (<= (max-depth y) n))
;;               (<= (max-depth (acl2::q-or x y)) n))
;;      :hints(("Goal" :in-theory (e/d (max-depth)
;;                                     ((force) max))
;;              :induct (max-depth2-ind x y n)
;;              :expand ((acl2::q-or x y))))
;;      :rule-classes (:rewrite
;;                     (:linear :match-free :all)))

;;    (defthm max-depth-of-q-xor
;;      (implies (and (<= (max-depth x) n)
;;                    (<= (max-depth y) n))
;;               (<= (max-depth (acl2::q-xor x y)) n))
;;      :hints(("Goal" :in-theory (e/d (max-depth)
;;                                     ((force) max))
;;              :induct (max-depth2-ind x y n)
;;              :expand ((acl2::q-binary-xor x y))))
;;      :rule-classes (:rewrite
;;                     (:linear :match-free :all)))

;;    (defthm max-depth-of-q-iff
;;      (implies (and (<= (max-depth x) n)
;;                    (<= (max-depth y) n))
;;               (<= (max-depth (acl2::q-iff x y)) n))
;;      :hints(("Goal" :in-theory (e/d (max-depth)
;;                                     ((force) max))
;;              :induct (max-depth2-ind x y n)
;;              :expand ((acl2::q-binary-iff x y))))
;;      :rule-classes (:rewrite
;;                     (:linear :match-free :all)))))

;; (local
;;  (progn

;;    (defun replace-if-equal (x y v)
;;      (if (equal x y) v y))

;;    (defthm q-ite-redef
;;      (equal (acl2::q-ite-fn x y z)
;;             (COND
;;              ((NULL X) Z)
;;              ((ATOM X) Y)
;;              (T
;;               (LET
;;                ((Y (replace-if-equal x y t))
;;                 (Z (replace-if-equal x z nil)))
;;                (COND
;;                 ((HONS-EQUAL Y Z) Y)
;;                 ((AND (EQ Y T) (EQ Z NIL)) X)
;;                 ((AND (EQ Y NIL) (EQ Z T))
;;                  (ACL2::Q-NOT X))
;;                 (T (ACL2::QCONS (ACL2::Q-ITE-FN (CAR X)
;;                                                 (ACL2::QCAR Y)
;;                                                 (ACL2::QCAR Z))
;;                                 (ACL2::Q-ITE-FN (CDR X)
;;                                                 (ACL2::QCDR Y)
;;                                                 (ACL2::QCDR Z)))))))))
;;      :hints(("Goal" :in-theory (e/d () ((force)))))
;;      :rule-classes ((:definition :clique (acl2::q-ite-fn)
;;                      :controller-alist ((acl2::q-ite-fn t nil nil)))))

;;    (defun max-depth3-ind (x y z n)
;;      (if (atom x)
;;          (list y z n)
;;        (list (max-depth3-ind (car x)
;;                              (acl2::qcar (replace-if-equal x y t))
;;                              (acl2::qcar (replace-if-equal x z nil))
;;                              (1- n))
;;              (max-depth3-ind (cdr x)
;;                              (acl2::qcdr (replace-if-equal x y t))
;;                              (acl2::qcdr (replace-if-equal x z nil))
;;                              (1- n)))))

;;    (defthm max-depth-of-qcar-replace-strong
;;      (implies (and (consp y) (not (consp a)))
;;               (< (max-depth (acl2::qcar (replace-if-equal x y a))) (max-depth y)))
;;      :hints (("goal" :expand ((max-depth y)
;;                               (max-depth a))))
;;      :rule-classes :linear)

;;    (defthm max-depth-of-qcdr-replace-strong
;;      (implies (and (consp y) (not (consp a)))
;;               (< (max-depth (acl2::qcdr (replace-if-equal x y a))) (max-depth y)))
;;      :hints (("goal" :expand ((max-depth y)
;;                               (max-depth a))))
;;      :rule-classes :linear)

;;    (defthm max-depth-of-qcar-replace-weak
;;      (implies (not (consp a))
;;               (<= (max-depth (acl2::qcar (replace-if-equal x y a))) (max-depth y)))
;;      :hints (("goal" :expand ((max-depth y)
;;                               (max-depth a))))
;;      :rule-classes :linear)

;;    (defthm max-depth-of-qcdr-replace-weak
;;      (implies (not (consp a))
;;               (<= (max-depth (acl2::qcdr (replace-if-equal x y a))) (max-depth y)))
;;      :hints (("goal" :expand ((max-depth y)
;;                               (max-depth a))))
;;      :rule-classes :linear)

;;    (defthm max-depth-of-qcar-replace-atom
;;      (implies (and (not (consp y)) (not (consp a)))
;;               (equal (max-depth (acl2::qcar (replace-if-equal x y a))) 0))
;;      :hints (("goal" :expand ((max-depth y)
;;                               (max-depth a)))))

;;    (defthm max-depth-of-qcdr-replace-atom
;;      (implies (and (not (consp y)) (not (consp a)))
;;               (equal (max-depth (acl2::qcdr (replace-if-equal x y a))) 0))
;;      :hints (("goal" :expand ((max-depth y)
;;                               (max-depth a)))))

;;    ;; (defthm max-depth-of-qcdr-strong
;;    ;;   (implies (consp x)
;;    ;;            (< (max-depth (acl2::qcdr x)) (max-depth x)))
;;    ;;   :hints (("goal" :expand ((max-depth x))))
;;    ;;   :rule-classes :linear)

;;    ;; (defthm max-depth-of-qcdr-atom
;;    ;;   (implies (not (consp x))
;;    ;;            (equal (max-depth (acl2::qcdr x)) 0))
;;    ;;   :hints (("goal" :expand ((max-depth x)))))

;;    (defthm max-depth-of-replace-if-equal
;;      (implies (not (consp a))
;;               (<= (max-depth (replace-if-equal x y a)) (max-depth y)))
;;      :hints (("goal" :expand ((max-depth a))))
;;      :rule-classes :linear)

;;    (local (in-theory (disable replace-if-equal acl2::qcar acl2::qcdr)))

;;    (defthm max-depth-of-qcons
;;      (implies (and (<= (max-depth x) (+ -1 n))
;;                    (<= (max-depth y) (+ -1 n)))
;;               (<= (max-depth (acl2::qcons x y)) n))
;;      :hints(("Goal" :in-theory (enable acl2::qcons max-depth)))
;;      :rule-classes ((:linear :trigger-terms ((max-depth (acl2::qcons x y)))
;;                      :match-free :all)))
         

;;    ;; (local (defthm qcar/cdr-when-consp
;;    ;;          (implies (consp x)
;;    ;;                   (and (equal (acl2::qcar x) (car x))
;;    ;;                        (equal (acl2::qcdr x) (cdr x))))
;;    ;;          :rule-classes ((:rewrite :backchain-limit-lst 0))))
;;    ;; (local (defthm qcar/cdr-when-atom
;;    ;;          (implies (not (consp x))
;;    ;;                   (and (equal (acl2::qcar x) x)
;;    ;;                        (equal (acl2::qcdr x) x)))
;;    ;;          :rule-classes ((:rewrite :backchain-limit-lst 0))))

;;    (defthm max-depth-of-q-ite
;;      (implies (and (<= (max-depth x) n)
;;                    (<= (max-depth y) n)
;;                    (<= (max-depth z) n))
;;               (<= (max-depth (acl2::q-ite-fn x y z)) n))
;;      :hints(("Goal" :in-theory (e/d (max-depth)
;;                                     ((force) max acl2::qcar acl2::qcdr acl2::qcons))
;;              :induct (max-depth3-ind x y z n)
;;              :expand ((acl2::q-ite-fn x y z)))
;;             (and stable-under-simplificationp
;;                  '(:cases ((consp y))))
;;             (and stable-under-simplificationp
;;                  '(:cases ((consp z)))))
;;      :rule-classes ((:rewrite)
;;                     (:linear :match-free :all)))))

;; (defthm bfr-max-nat-var-of-bfr-not
;;   (equal (bfr-max-nat-var (bfr-not x))
;;          (bfr-max-nat-var x))
;;   :hints(("Goal" :in-theory (enable bfr-max-nat-var bfr-not))))

;; (defthm bfr-max-nat-var-of-bfr-and
;;   (implies (and (<= (bfr-max-nat-var x) n)
;;                 (<= (bfr-max-nat-var y) n))
;;            (<= (bfr-max-nat-var (bfr-binary-and x y)) n))
;;   :hints(("Goal" :in-theory (e/d (bfr-max-nat-var bfr-binary-and)
;;                                  (max gt-max-implies gt-max-plus-1-implies))))
;;   :rule-classes ((:rewrite)
;;                  (:linear :match-free :all)))

;; (defthm bfr-max-nat-var-of-bfr-or
;;   (implies (and (<= (bfr-max-nat-var x) n)
;;                 (<= (bfr-max-nat-var y) n))
;;            (<= (bfr-max-nat-var (bfr-binary-or x y)) n))
;;   :hints(("Goal" :in-theory (e/d (bfr-max-nat-var bfr-binary-or)
;;                                  (max gt-max-implies gt-max-plus-1-implies))))
;;   :rule-classes ((:rewrite)
;;                  (:linear :match-free :all)))

;; (defthm bfr-max-nat-var-of-bfr-xor
;;   (implies (and (<= (bfr-max-nat-var x) n)
;;                 (<= (bfr-max-nat-var y) n))
;;            (<= (bfr-max-nat-var (bfr-xor x y)) n))
;;   :hints(("Goal" :in-theory (e/d (bfr-max-nat-var bfr-xor)
;;                                  (max gt-max-implies gt-max-plus-1-implies))))
;;   :rule-classes ((:rewrite)
;;                  (:linear :match-free :all)))

;; (defthm bfr-max-nat-var-of-bfr-iff
;;   (implies (and (<= (bfr-max-nat-var x) n)
;;                 (<= (bfr-max-nat-var y) n))
;;            (<= (bfr-max-nat-var (bfr-iff x y)) n))
;;   :hints(("Goal" :in-theory (e/d (bfr-max-nat-var bfr-iff)
;;                                  (max gt-max-implies gt-max-plus-1-implies))))
;;   :rule-classes (:rewrite
;;                  (:linear :match-free :all)))

;; (defthm bfr-max-nat-var-of-bfr-ite
;;   (implies (and (<= (bfr-max-nat-var x) n)
;;                 (<= (bfr-max-nat-var y) n)
;;                 (<= (bfr-max-nat-var z) n))
;;            (<= (bfr-max-nat-var (bfr-ite-fn x y z)) n))
;;   :hints(("Goal" :in-theory (e/d (bfr-max-nat-var bfr-ite-fn)
;;                                  (max gt-max-implies gt-max-plus-1-implies))))
;;   :rule-classes ((:rewrite)
;;                  (:linear :match-free :all)))

;; (defthm bfr-max-nat-var-of-consts
;;   (and (equal (bfr-max-nat-var nil) 0)
;;        (equal (bfr-max-nat-var t) 0))
;;   :hints(("Goal" :in-theory (e/d (bfr-max-nat-var)
;;                                  ((bfr-max-nat-var))))))
   

