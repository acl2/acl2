; UBDD Library
; Copyright (C) 2008-2011 Warren Hunt and Bob Boyer
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.
; Significantly revised in 2008 by Jared Davis and Sol Swords.
; Now maintained by Centaur Technology.
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/

(in-package "ACL2")

(set-inhibit-warnings "theory")
(defun is-prefix (x y)
  (or (atom x)
      (and (equal (car x) (car y))
           (is-prefix (cdr x) (cdr y)))))

(defun subgoal-of (goal id)
  (declare (xargs :mode :program))
  (let ((goal (parse-clause-id goal)))
    (and (is-prefix (car goal) (car id))
         (or (not (equal (car goal) (car id)))
             (and (is-prefix (cadr goal) (cadr id))
                  (or (not (equal (cadr goal) (cadr id)))
                      (< (cddr goal) (cddr id))))))))



(include-book "extra-operations")
(include-book "misc/hons-help2" :dir :system)
(include-book "clause-processors/term-patterns" :dir :system)
(include-book "clause-processors/use-by-hint" :dir :system)
(include-book "tools/mv-nth" :dir :system)

;; bdd-diff-witness: given two different BDDs, finds a variable assignment
;; that makes their evaulations unequal.
(defund bdd-diff-witness (a b)
  (declare (xargs :measure (+ (acl2-count a) (acl2-count b))
                  :guard t))
  (if (and (atom a) (atom b))
      nil
    (if (hqual (qcdr a) (qcdr b))
        (cons t (bdd-diff-witness (qcar a) (qcar b)))
      (cons nil (bdd-diff-witness (qcdr a) (qcdr b))))))

(in-theory (disable (bdd-diff-witness) (:type-prescription bdd-diff-witness)))


;; BDD-DIFF-WITNESS always produces a variable assignment which
;; differentiates two BDDs, if they are different:
(defthm eval-bdd-diff-witness
  (implies (and (ubddp a)
                (ubddp b)
                (not (equal a b)))
           (not (equal (eval-bdd a (bdd-diff-witness a b))
                       (eval-bdd b (bdd-diff-witness a b)))))
  :hints (("goal" :in-theory (enable eval-bdd ubddp bdd-diff-witness)
           :induct (bdd-diff-witness a b))))

(defthm eval-bdd-diff-witness-corr
  (implies (and (ubddp a)
                (ubddp b)
                (not (equal a b)))
           (equal (eval-bdd a (bdd-diff-witness a b))
                  (not (eval-bdd b (bdd-diff-witness a b)))))
  :hints (("goal" :use ((:instance eval-bdd-diff-witness))
           :in-theory (e/d (bdd-diff-witness) (eval-bdd-diff-witness)))))



;; Simple pattern language for recognizing BDD terms:
;; pat ::== & | atom | (quote x) | (sym {pat}) | (sym {pat} . &)
;; & matches anything, atom matches its own quotation,
;; (quote x) matches (quote x).

(defmacro bdd-patterns ()
  '(get-term-patterns bdd))

(defmacro set-bdd-patterns (val)
  `(set-term-patterns bdd ,val))

(defmacro add-bdd-pat (val)
  `(add-term-pattern bdd ,val))

(defmacro add-bdd-pats (&rest val)
  `(add-term-patterns bdd . ,val))

(defmacro add-bdd-fn-pat (val)
  `(add-fn-term-pattern bdd ,val))

(defmacro add-bdd-fn-pats (&rest val)
  `(add-fn-term-patterns bdd . ,val))

(set-bdd-patterns nil)

(add-bdd-fn-pats
 q-ite-fn q-not q-binary-and q-binary-or q-binary-xor q-binary-iff qv qvar-n
 q-implies-fn)

(add-bdd-pats 't 'nil)


(defun bdd-termp (x ubddp-terms patterns)
  (or (member-equal x ubddp-terms)
      (match-term-pattern x patterns)))



;; (mutual-recursion
;;  (defun collect-bdd-diff-witnesses-term (x acc)
;;    (if (atom x)
;;        acc
;;      (let ((acc (if (and (eq (car x) 'bdd-diff-witness)
;;                          (not (member-equal x acc)))
;;                     (cons x acc)
;;                   acc)))
;;        (collect-bdd-diff-witnesses-list (cdr x) acc))))
;;  (defun collect-bdd-diff-witnesses-list (x acc)
;;    (if (atom x)
;;        acc
;;      (collect-bdd-diff-witnesses-term
;;       (car x)
;;       (collect-bdd-diff-witnesses-list (cdr x) acc)))))


(include-book "clause-processors/generalize" :dir :system)



(defevaluator bdd-cp-ev bdd-cp-evl
  ((bdd-diff-witness a b) (eval-bdd a b) (equal a b) (not a)
   (ubddp a)
   (equal x y)
   (use-these-hints x)
   (implies a b)
   (if a b c)))

(def-join-thms bdd-cp-ev)



(defun not-equal-hyps-to-eval-bdds (clause ubddp-terms patterns)
  (if (atom clause)
      (mv nil nil)
    (mv-let (rst-clause witnesses)
      (not-equal-hyps-to-eval-bdds (cdr clause) ubddp-terms patterns)
      (let ((lit (car clause)))
        (mv-let (a b ok)
          (case-match lit
            (('equal a b)
             (mv a b t))
            (('not a) (mv a ''nil t))
            (& (mv nil nil nil)))
          (if (and ok
                   (bdd-termp a ubddp-terms patterns)
                   (bdd-termp b ubddp-terms patterns))
              (mv (cons ;; `(not (eval-bdd (q-binary-xor ,a ,b)
                   ;;                                         (q-sat (q-binary-xor ,a ,b))))
                   `(not (implies (if (ubddp ,a) (ubddp ,b) 'nil)
                                  (not (equal (eval-bdd ,a (bdd-diff-witness ,a ,b))
                                              (eval-bdd ,b (bdd-diff-witness ,a ,b))))))
                   rst-clause)
                  (cons `(bdd-diff-witness ,a ,b) witnesses))
            (mv (cons lit rst-clause)
                witnesses)))))))

(defthm pseudo-term-listp-not-equal-hyps
  (implies (pseudo-term-listp clause)
           (pseudo-term-listp (mv-nth 0 (not-equal-hyps-to-eval-bdds
                                    clause ubddp-terms patterns)))))

(in-theory (disable bdd-termp))


(encapsulate
 nil
 (local (in-theory (disable default-car default-cdr
                            equal-of-booleans-rewrite
                            len length (:type-prescription booleanp))))

 (defthm not-equal-hyps-to-eval-bdds-correct
   (implies (and ;;(pseudo-term-listp clause)
             ;;(alistp a)
             (bdd-cp-ev (disjoin (mv-nth 0 (not-equal-hyps-to-eval-bdds
                                            clause ubddp-terms patterns))) a))
            (bdd-cp-ev (disjoin clause) a))
   :hints (("goal" :induct (not-equal-hyps-to-eval-bdds clause ubddp-terms
                                                        patterns))
           (and (subgoal-of "subgoal *1/" id)
                '(:in-theory
                  (disable not-equal-hyps-to-eval-bdds
                           eval-bdd-of-q-xor)
                  :expand ((not-equal-hyps-to-eval-bdds clause ubddp-terms
                                                        patterns)
                           (not-equal-hyps-to-eval-bdds nil ubddp-terms
                                                        patterns)))))))


;; ;; The hint consists of (list ubddp-terms patterns), where ubddp-terms is a list
;; ;; of terms that will be considered BDDs (it should be provable that they are
;; ;; each ubddp.)
;; (defun not-equal-hyps-to-eval-bdds-cp (clause hint)
;;   (mv-let (new-clause ubddp-hyps)
;;     (not-equal-hyps-to-eval-bdds clause (car hint) (cadr hint))
;;     (list new-clause
;;           (cons (conjoin ubddp-hyps) clause))))

;; (defthm not-equal-hyps-to-eval-bdds-cp-correct
;;   (implies (and (pseudo-term-listp clause)
;;                 (alistp a)
;;                 (bdd-cp-ev (conjoin-clauses (not-equal-hyps-to-eval-bdds-cp
;;                                              clause hint))
;;                            a))
;;            (bdd-cp-ev (disjoin clause) a))
;;   :hints (("goal" :use ((:instance not-equal-hyps-to-eval-bdds-correct
;;                                    (patterns (cadr hint))
;;                                    (ubddp-terms (car hint))))
;;            :in-theory (disable not-equal-hyps-to-eval-bdds-correct)))
;;   :rule-classes :clause-processor)



(mutual-recursion
 (defun collect-eval-bdd-vals (term)
   (cond ((atom term) nil)
         ((eq (car term) 'quote) nil)
         ((member-eq (car term) '(eval-bdd eval-bdd-list))
          (and (eql (len term) 3)
               (list (nth 2 term))))
         (t (collect-eval-bdd-vals-list (cdr term)))))
 (defun collect-eval-bdd-vals-list (clause)
   (if (atom clause)
       nil
     (union-equal (collect-eval-bdd-vals (car clause))
                  (collect-eval-bdd-vals-list (cdr clause))))))


(include-book "tools/flag" :dir :system)
(flag::make-flag collect-eval-bdd-vals-flag collect-eval-bdd-vals
                 :flag-mapping ((collect-eval-bdd-vals term)
                                (collect-eval-bdd-vals-list list)))

(defthm pseudo-term-listp-union-equal
  (implies (and (pseudo-term-listp x) (pseudo-term-listp y))
           (pseudo-term-listp (union-equal x y))))

(defthm-collect-eval-bdd-vals-flag pseudo-term-listp-collect-eval-bdd-vals
  (term (implies (pseudo-termp term)
                 (pseudo-term-listp (collect-eval-bdd-vals term))))
  (list (implies (pseudo-term-listp clause)
                 (pseudo-term-listp (collect-eval-bdd-vals-list clause))))
  :hints (("goal" :induct (collect-eval-bdd-vals-flag flag term clause))
          ("Subgoal *1/6" :expand (collect-eval-bdd-vals-list clause))))


(defun eval-bdd-vals (clause)
  (let ((collect (collect-eval-bdd-vals-list clause)))
    (or collect '(arbitrary-vals))))

(defthm eval-bdd-vals-pseudo-term-listp
  (implies (pseudo-term-listp clause)
           (pseudo-term-listp (eval-bdd-vals clause))))

(in-theory (disable eval-bdd-vals))

(defun instantiate-eval-bdds (a b vals)
  (if (atom vals)
      nil
    (cons `(not (equal (eval-bdd ,a ,(car vals))
                       (eval-bdd ,b ,(car vals))))
          (instantiate-eval-bdds a b (cdr vals)))))

(defthm instantiate-eval-bdds-correct
  (implies (and ;;(pseudo-termp x)
                ;;(pseudo-termp y)
                ;;(alistp a)
                (equal (bdd-cp-ev x a)
                       (bdd-cp-ev y a)))
           (not (bdd-cp-ev (disjoin (instantiate-eval-bdds x y vals)) a)))
  :hints (("goal" :induct (instantiate-eval-bdds a b vals))))

(defthm pseudo-term-listp-instantiate-eval-bdds
  (implies (and (pseudo-term-listp vals)
                (pseudo-termp a)
                (pseudo-termp b))
           (pseudo-term-listp (instantiate-eval-bdds a b vals))))

(in-theory (disable instantiate-eval-bdds))

(defun instantiate-equals-with-eval-bdds (clause vals ubddp-terms patterns)
  (if (atom clause)
      nil
    (let* ((rst-clause (instantiate-equals-with-eval-bdds
                        (cdr clause) vals ubddp-terms patterns))
           (lit (car clause)))
      (mv-let (a b)
        (case-match lit
          (('not ('equal a b))
           (mv a b))
          (a (mv a ''nil))
          (& (mv nil nil)))
        (if (and (bdd-termp a ubddp-terms patterns)
                 (bdd-termp b ubddp-terms patterns))
            (cons (disjoin (instantiate-eval-bdds a b vals))
                  rst-clause)
          (cons lit rst-clause))))))

(defthm instantiate-equals-with-eval-bdds-correct
  (implies (and ;;(pseudo-term-listp clause)
                ;;(alistp a)
                (bdd-cp-ev (disjoin (instantiate-equals-with-eval-bdds
                                     clause vals ubddp-terms patterns))
                           a))
           (bdd-cp-ev (disjoin clause) a))
  :hints (("goal" :induct (instantiate-equals-with-eval-bdds
                           clause vals ubddp-terms patterns))))



(defthm pseudo-term-listp-instantiate-equals-with-eval-bdds
  (implies (and (pseudo-term-listp clause)
                (pseudo-term-listp vals))
           (pseudo-term-listp (instantiate-equals-with-eval-bdds
                               clause vals ubddp-terms patterns))))


;; hints are: ubddp-terms, patterns
(defun eval-bdd-cp (clause hints)
  (let* ((ubddp-terms (car hints))
         (patterns (cadr hints))
         (given-witnesses (caddr hints)))
    (mv-let (new-clause witnesses)
      (if given-witnesses
          (mv clause given-witnesses)
        (not-equal-hyps-to-eval-bdds clause ubddp-terms patterns))
      (let* ((vals (eval-bdd-vals new-clause))
             (new-clause (instantiate-equals-with-eval-bdds
                          new-clause vals ubddp-terms patterns)))
        (if given-witnesses
            (list new-clause)
          (let* ((symbols (make-n-vars (len witnesses) 'bdd-vals 0
                                       (simple-term-vars-lst new-clause)))
                 (alist (pairlis$ witnesses symbols)))
            (list (replace-subterms-list new-clause alist))))))))

(in-theory (disable instantiate-equals-with-eval-bdds
                    collect-eval-bdd-vals-list
                    not-equal-hyps-to-eval-bdds
                    replace-subterms-list))


(defun replace-alist-to-bindings-bdd (alist bindings)
  (if (atom alist)
      nil
    (cons (cons (cdar alist) (bdd-cp-ev (caar alist) bindings))
          (replace-alist-to-bindings-bdd (cdr alist) bindings))))




(defthm disjoin-replace-subterms-list-bdd
  (implies (and (not (intersectp-equal (strip-cdrs alist)
                                       (simple-term-vars-lst x)))
                (symbol-listp (strip-cdrs alist))
                (not (member-equal nil (strip-cdrs alist)))
                (no-duplicatesp-equal (strip-cdrs alist))
                (pseudo-term-listp x))
           (iff (bdd-cp-ev (disjoin (replace-subterms-list x alist))
                             (append (replace-alist-to-bindings-bdd alist env)
                                     env))
                  (bdd-cp-ev (disjoin x) env)))
  :hints (("goal" :in-theory (enable bdd-cp-ev-constraint-0)
           :use ((:functional-instance
                  disjoin-replace-subterms-list
                  (gen-eval bdd-cp-ev)
                  (gen-eval-lst bdd-cp-evl)
                  (replace-alist-to-bindings
                   replace-alist-to-bindings-bdd))))))

(defun alist-for-eval-bdd-cp (clause hints a)
  (let* ((ubddp-terms (car hints))
         (patterns (cadr hints))
         (given-witnesses (caddr hints)))
    (mv-let (new-clause witnesses)
      (if given-witnesses
          (mv clause given-witnesses)
        (not-equal-hyps-to-eval-bdds clause ubddp-terms patterns))
      (let* ((vals (eval-bdd-vals new-clause))
             (new-clause (instantiate-equals-with-eval-bdds
                          new-clause vals ubddp-terms patterns)))
        (if given-witnesses
            a
          (let* ((symbols (make-n-vars (len witnesses) 'bdd-vals 0
                                       (simple-term-vars-lst new-clause)))
                 (alist (pairlis$ witnesses symbols)))
            (append (replace-alist-to-bindings-bdd alist a) a)))))))

(defthm strip-cdrs-pairlis$
  (implies (and (equal (len a) (len b))
                (symbol-listp b))
           (equal (strip-cdrs (pairlis$ a b))
                  b)))

(defthm eval-bdd-cp-correct
  (implies (and (pseudo-term-listp clause)
                (alistp a)
                (bdd-cp-ev (conjoin-clauses
                            (eval-bdd-cp clause hints))
                           (alist-for-eval-bdd-cp clause hints a)))
           (bdd-cp-ev (disjoin clause) a))
  :hints ((let ((new-clause '(mv-nth 0 (not-equal-hyps-to-eval-bdds
                                        clause (car hints) (cadr hints)))))
            `(:use ((:instance not-equal-hyps-to-eval-bdds-correct
                               (ubddp-terms (car hints))
                               (patterns (cadr hints)))
                    (:instance instantiate-equals-with-eval-bdds-correct
                               (clause ,new-clause)
                               (ubddp-terms (car hints))
                               (vals (eval-bdd-vals ,new-clause))
                               (patterns (cadr hints)))
                    (:instance instantiate-equals-with-eval-bdds-correct
                               (clause clause)
                               (ubddp-terms (car hints))
                               (vals (eval-bdd-vals clause))
                               (patterns (cadr hints))))
                   :in-theory (disable not-equal-hyps-to-eval-bdds-correct
                                       instantiate-equals-with-eval-bdds-correct)
                   :do-not-induct t)))
  :rule-classes :clause-processor
  :otf-flg t)




(defun find-ubddp-terms (clause)
  (if (atom clause)
      nil
    (let ((lit (car clause))
          (rst (find-ubddp-terms (cdr clause))))
      (case-match lit
        (('not ('ubddp x))
         (cons x rst))
        (& rst)))))



(defun eval-bdd-cp-hint (clause patterns)
  `(:clause-processor (eval-bdd-cp clause (list ',(find-ubddp-terms clause)
                                                ',patterns))))


;; computed hint to use this clause processor when stable under
;; simplification.  If or-hint is t, alternatively provide no hint.
;; (defmacro bdd-reasoning (&key or-hint)
;;   `(if stable-under-simplificationp
;;        (er-progn
;;         ;; This just lets us collect the clauses on which this hint is used.
;;         ,'(assign eval-bdd-cp-clauses
;;                   (cons clause
;;                         (and (boundp-global
;;                               'eval-bdd-cp-clauses state)
;;                              (@ eval-bdd-cp-clauses))))
;;         ,(let ((cphint '(eval-bdd-cp-hint clause (bdd-patterns))))
;;            `(value ,(if or-hint
;;                         ``(:or (,,cphint
;;                                 (:no-thanks t)))
;;                       cphint))))
;;      (value nil)))

(defmacro bdd-reasoning (&key or-hint)
  `(and stable-under-simplificationp
        ,(let ((cphint '(eval-bdd-cp-hint clause (bdd-patterns))))
           (if or-hint
               ``(:or (,,cphint
                       (:no-thanks t)))
             cphint))))

(defmacro eval-bdd-cp-default-hint ()
  `(and stable-under-simplificationp
        (let* ((rcnst (access prove-spec-var pspv :rewrite-constant))
               (ens   (access rewrite-constant rcnst
                              :current-enabled-structure)))
          (enabled-numep (fnume '(:definition eval-bdd-cp-hint) world)
                         ens))
        (bdd-reasoning :or-hint t)))


(def-ruleset q-witness-mode-rules '((:definition eval-bdd-cp-hint)))

(add-default-hints!
 '((eval-bdd-cp-default-hint)))

(in-theory (disable eval-bdd-cp-hint))


;;   `(:or ((:clause-processor (eval-bdd-cp clause (list ',(find-ubddp-terms clause)
;;                                                       ',(bdd-patterns))))
;;          (:null nil))))









(local
 (defsection q-witness-tests

   (in-theory (enable eval-bdd-cp-hint))

   (defthm ex1
     (implies (and (ubddp a) (ubddp b) (ubddp c)
                   (not (q-ite a b c)))
              (not (q-and (q-implies a b)
                          (q-implies (q-not a) c))))
     :rule-classes nil)


   (defthm ex2
     (implies (and (ubddp a) (ubddp b) (ubddp c)
                   (not (q-and (q-implies a b) (q-implies (q-not a) c))))
              (not (q-ite a b c)))
     :rule-classes nil)
   ;;      :hints ((and stable-under-simplificationp
   ;;                   (eval-bdd-cp-hint clause (bdd-patterns)))))


   (defthm ex3
     (implies (and (ubddp x) (ubddp hyp)
                   (equal (let ((and (q-and x hyp)))
                            (if and (if (hqual and hyp) t x) nil))
                          x)
                   (not (equal hyp nil)))
              (equal (eq x t)
                     (not (q-and (q-not x) hyp))))
     :rule-classes nil)
   ;;      :hints ((and stable-under-simplificationp
   ;;                   (eval-bdd-cp-hint clause (bdd-patterns)))))


   (defthm ex4
     (implies (and (ubddp c) (ubddp hyp) hyp
                   (equal (let ((and (q-and c hyp)))
                            (if and (if (hqual and hyp) t c) nil))
                          c))
              (equal (eq (let ((and (q-and (q-not c) hyp)))
                           (if and (if (hqual and hyp) t (q-not c)) nil))
                         nil)
                     (eq c t)))
     :rule-classes nil)))
