
(in-package "ACL2")

(include-book "misc/hons-help2" :dir :system)
(include-book "base")

(include-book "clause-processors/term-patterns" :dir :system)
(include-book "clause-processors/join-thms" :dir :system)


(defmacro aig-patterns ()
  '(get-term-patterns aig))

(defmacro set-aig-patterns (val)
  `(set-term-patterns aig ,val))

(defmacro add-aig-pat (val)
  `(add-term-pattern aig ,val))

(defmacro add-aig-pats (&rest val)
  `(add-term-patterns aig . ,val))

(defmacro add-aig-fn-pat (val)
  `(add-fn-term-pattern aig ,val))

(defmacro add-aig-fn-pats (&rest val)
  `(add-fn-term-patterns aig . ,val))

(set-aig-patterns nil)

(add-aig-fn-pats
 aig-and aig-not aig-or aig-xor aig-iff aig-ite aig-restrict)

(add-aig-pats 't 'nil)

(defun aig-termp (x aig-terms pats)
  (or (member-equal x aig-terms)
      (match-term-pattern x pats)))



(defevaluator aig-cp-ev aig-cp-evl
  ((aig-eval a b) (equal a b) (not a)
   (implies a b)
   (if a b c)))

(def-join-thms aig-cp-ev)





(mutual-recursion
 (defun collect-aig-eval-vals (term)
   (cond ((atom term) nil)
         ((eq (car term) 'quote) nil)
         ((member-eq (car term)
                     '(aig-eval
                       aig-eval-pat
                       aig-eval-list
                       aig-eval-alist
                       faig-eval-pat
                       faig-eval-list
                       faig-eval-alist))
          (and (eql (len term) 3)
               (list (nth 2 term))))
         (t (collect-aig-eval-vals-list (cdr term)))))
 (defun collect-aig-eval-vals-list (clause)
   (if (atom clause)
       nil
     (union-equal (collect-aig-eval-vals (car clause))
                  (collect-aig-eval-vals-list (cdr clause))))))
 

(include-book "tools/flag" :dir :system)        
(flag::make-flag collect-aig-eval-vals-flag collect-aig-eval-vals
                 :flag-mapping ((collect-aig-eval-vals . term)
                                (collect-aig-eval-vals-list . list)))

(defthm pseudo-term-listp-union-equal
  (implies (and (pseudo-term-listp x) (pseudo-term-listp y))
           (pseudo-term-listp (union-equal x y))))

(defthm-collect-aig-eval-vals-flag pseudo-term-listp-collect-aig-eval-vals
  (term (implies (pseudo-termp term)
                 (pseudo-term-listp (collect-aig-eval-vals term))))
  (list (implies (pseudo-term-listp clause)
                 (pseudo-term-listp (collect-aig-eval-vals-list clause))))
  :hints (("goal" :induct (collect-aig-eval-vals-flag flag term clause))
          ("Subgoal *1/6" :expand (collect-aig-eval-vals-list clause))))


(defun aig-eval-vals (clause)
  (let ((collect (collect-aig-eval-vals-list clause)))
    (or collect '(arbitrary-vals))))

(defthm aig-eval-vals-pseudo-term-listp
  (implies (pseudo-term-listp clause)
           (pseudo-term-listp (aig-eval-vals clause))))

(in-theory (disable aig-eval-vals))

(defun instantiate-aig-evals (a b vals)
  (if (atom vals)
      nil
    (cons `(not (equal (aig-eval ,a ,(car vals))
                       (aig-eval ,b ,(car vals))))
          (instantiate-aig-evals a b (cdr vals)))))

(defthm instantiate-aig-evals-correct
  (implies (and ;;(pseudo-termp x)
                ;;(pseudo-termp y)
                ;;(alistp a)
                (equal (aig-cp-ev x a)
                       (aig-cp-ev y a)))
           (not (aig-cp-ev (disjoin (instantiate-aig-evals x y vals)) a)))
  :hints (("goal" :induct (instantiate-aig-evals a b vals))))

(defthm pseudo-term-listp-instantiate-aig-evals
  (implies (and (pseudo-term-listp vals)
                (pseudo-termp a)
                (pseudo-termp b))
           (pseudo-term-listp (instantiate-aig-evals a b vals))))

(in-theory (disable instantiate-aig-evals))

(defun instantiate-equals-with-aig-evals (clause vals aig-terms patterns)
  (if (atom clause)
      nil
    (let* ((rst-clause (instantiate-equals-with-aig-evals
                        (cdr clause) vals aig-terms patterns))
           (lit (car clause)))
      (mv-let (a b)
        (case-match lit
          (('not ('equal a b))
           (mv a b))
          (a (mv a ''nil))
          (& (mv nil nil)))
        (if (and (aig-termp a aig-terms patterns)
                 (aig-termp b aig-terms patterns))
            (cons (disjoin (instantiate-aig-evals a b vals))
                  rst-clause)
          (cons lit rst-clause))))))

(defthm instantiate-equals-with-aig-evals-correct
  (implies (and ;;(pseudo-term-listp clause)
                ;;(alistp a)
                (aig-cp-ev (disjoin (instantiate-equals-with-aig-evals
                                     clause vals aig-terms patterns))
                           a))
           (aig-cp-ev (disjoin clause) a))
  :hints (("goal" :induct (instantiate-equals-with-aig-evals
                           clause vals aig-terms patterns))))



(defthm pseudo-term-listp-instantiate-equals-with-aig-evals
  (implies (and (pseudo-term-listp clause)
                (pseudo-term-listp vals))
           (pseudo-term-listp (instantiate-equals-with-aig-evals
                               clause vals aig-terms patterns))))


(defun aig-eval-cp (clause hints)
  (let* ((aig-terms (car hints))
         (patterns (cadr hints))
         (vals (aig-eval-vals clause))
         (clause (instantiate-equals-with-aig-evals
                  clause vals aig-terms patterns)))
    (list clause)))

(in-theory (disable instantiate-equals-with-aig-evals
                    collect-aig-eval-vals-list))

(defthm aig-eval-cp-correct
  (implies (and (pseudo-term-listp clause)
                (alistp a)
                (aig-cp-ev (conjoin-clauses
                            (aig-eval-cp clause hints))
                           a))
           (aig-cp-ev (disjoin clause) a))
  :rule-classes :clause-processor)

(defmacro aig-reasoning (&key or-hint)
  (declare (ignorable or-hint))
  `(if stable-under-simplificationp
       (er-progn 
        ;; This just lets us collect the clauses on which this hint is used.
        (assign aig-eval-cp-clauses
                (cons clause
                      (and (boundp-global
                            'aig-eval-cp-clauses state)
                           (@ aig-eval-cp-clauses))))
        (let ((cphint `(:clause-processor
                        (aig-eval-cp clause (list nil ',(get-term-patterns aig))))))
          (value ,(if or-hint
                      '`(:or ,cphint (:no-thanks t))
                    'cphint))))
     (value nil)))
    
