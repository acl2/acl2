
;; invariants.lisp
;; by Sol Swords

;; Consider a situation where you have a recursive function (foo x y z) for
;; which a useful invariant is (foo-guard x y z).  It may be the case that many
;; inductive proofs involving foo use foo-guard as a hyp.  In this case, for
;; every induction hypothesis it is necessary to prove (foo-guard
;; substituted-args).  This book introduces a macro which proves such
;; invariants.

;; Invocation:

;; (prove-invariants foo ((foo . (invariant-fn x y z))) :hints (("goal" ...)))

;; Takes the guard as the invariant:
;; (prove-guard-invariants foo :hints (("goal" ...)))


;; for a mutually recursive clique (foo bar baz):
;; (prove-invariants foo    ;; any member of the clique
;;                   ((foo . (foo-inv x y))
;;                    (bar . (bar-inv a b))
;;                    (baz . (baz-inv m n o p)))
;;                   :hints (("goal" ...)))

;; (prove-guard-invariant foo     ;; any member of the clique
;;                        :hints (("Goal" ...)))


(in-package "ACL2")

(program)
(set-state-ok t)
(include-book "bash")



(defun get-clique-members (fn world)
  (or (getprop fn 'recursivep nil 'current-acl2-world world)
      (er hard 'get-clique-members "Expected ~s0 to be in a mutually-recursive nest.~%")))

(defun get-formals (fn world)
  (getprop fn 'formals nil 'current-acl2-world world))

(defun get-body (fn latest-def world)
  ;; If latest-def is nil (the default for make-flag), this gets the original,
  ;; normalized or non-normalized body based on what the user typed for the
  ;; :normalize xarg.  The use of "last" skips past any other :definition rules
  ;; that have been added since then.
  (let* ((bodies (getprop fn 'def-bodies nil 'current-acl2-world world))
         (body (if latest-def
                   (car bodies)
                 (car (last bodies)))))
    (if (access def-body body :hyp)
        (er hard 'get-body
            "Attempt to call get-body on a body with a non-nil hypothesis, ~x0"
            (access def-body body :hyp))
      (if (not (eq (access def-body body :equiv)
                   'equal))
          (er hard 'get-body
              "Attempt to call get-body for an equivalence relation other ~
               than equal, ~x0"
              (access def-body body :equiv))
        (access def-body body :concl)))))


(defun inv-build-lemma-from-context (concl hyps context)
  (cond ((atom context)
         `(implies (and . ,hyps) ,concl))
        ((eq (caar context) :hyp)
         (inv-build-lemma-from-context concl (cons (cadar context) hyps)
                                       (cdr context)))
        ((eq (caar context) :lambda)
         (let ((formals (cadar context))
               (actuals (caddar context)))
           (inv-build-lemma-from-context
            `((lambda ,formals
                (declare (ignorable . ,formals))
                (implies (and . ,hyps) ,concl))
              . ,actuals)
            nil (cdr context))))
        (t (er hard 'inv-build-lemma-from-context
               "Malformed context element: ~x0~%" (car context)))))

(defun inv-clause-to-theorem (clause)
  `(implies (and . ,(dumb-negate-lit-lst (butlast clause 1)))
            ,(car (last clause))))

(defun inv-clauses-to-theorems (clauses)
  (if (atom clauses)
      nil
    (cons (inv-clause-to-theorem (car clauses))
          (inv-clauses-to-theorems (cdr clauses)))))

(defun inv-to-theorems (term hints state)
  (er-let* ((clauses (simplify-with-prover term hints 'inv-to-theorems state)))
           (value (inv-clauses-to-theorems clauses))))


(mutual-recursion
 ;; Fn-alist consists of pairs (fn . invariant) where invariant is some term.
 ;; This function collects clauses like
 ;; (implies (and (top-fn-invariant a b c) other-hyps)
 ;;               (called-fn-invariant (f a b) (g c a) ...))
 (defun gather-invariant-reqs (x context fn-alist hints state acc)
   (cond ((or (atom x) (eq (car x) 'quote)) (value acc))
         ((eq (car x) 'if)
          (er-let* ((acc (gather-invariant-reqs
                          (cadr x) context fn-alist hints state
                          acc))
                    (acc (gather-invariant-reqs
                          (caddr x) (cons `(:hyp ,(cadr x)) context) fn-alist
                          hints state acc)))
                   (gather-invariant-reqs
                    (cadddr x) (cons `(:hyp (not ,(cadr x))) context) fn-alist
                    hints state acc)))
         ((symbolp (car x))
          (let* ((lookup (assoc-eq (car x) fn-alist)))
            (er-let* ((acc
                       (if lookup
                           (let* ((formals (get-formals (car x) (w state)))
                                  (concl (cdr lookup))
                                  (context
                                   (cons `(:lambda ,formals ,(cdr x)) context))
                                  (lemma-raw (inv-build-lemma-from-context concl nil
                                                                           context)))
                             (er-let* ((lemmas (inv-to-theorems
                                                lemma-raw
                                                (or hints
                                                    '(("goal" :in-theory
                                                       (theory 'minimal-theory))))
                                                state)))
                                      (value (append lemmas acc))))
                         (value acc))))
                     (gather-invariant-reqs-list (cdr x) context fn-alist hints
                                                 state acc))))
         (t ;; lambda
          (let ((formals (cadar x))
                (actuals (cdr x))
                (body (caddar x)))
            (er-let* ((acc (gather-invariant-reqs
                            body (cons `(:lambda ,formals ,actuals) context)
                            fn-alist hints state acc)))
                     (gather-invariant-reqs-list actuals context fn-alist hints
                                                 state
                                                 acc))))))

 (defun gather-invariant-reqs-list (x context fn-alist hints state acc)
   (if (atom x)
       (value acc)
     (er-let* ((acc (gather-invariant-reqs-list
                     (cdr x) context fn-alist hints state acc)))
              (gather-invariant-reqs (car x) context fn-alist hints state acc)))))


(defun calls-make-concls (calls fn-alist state)
  (if (atom calls)
      nil
    (let* ((fn (caar calls))
           (args (cdar calls))
           (formals (get-formals (caar calls) (w state)))
           (inv (cdr (assoc-eq fn fn-alist))))
      (cons `((lambda ,formals ,inv)
              . ,args)
            (calls-make-concls (cdr calls) fn-alist state)))))



(defun gather-invariant-reqs-from-induction (induction fn-alist req hints state)
  (if (atom induction)
      (value nil)
    (er-let* ((reqs (gather-invariant-reqs-from-induction
                     (cdr induction) fn-alist req hints state)))
             (let* ((tests (cons req (access tests-and-calls (car induction) :tests)))
                    (calls (access tests-and-calls (car induction) :calls))
                    (concls (calls-make-concls calls fn-alist state))
                    (lemma-raw `(implies (and . ,tests)
                                         (and . ,concls))))
               (er-let* ((lemmas (inv-to-theorems
                                  lemma-raw
                                  (or hints
                                      '(("goal" :in-theory (theory
                                                            'minimal-theory))))
                                  state)))
                        (value (append lemmas reqs)))))))





(defun clique-invariant-alist (clique world)
  (if (atom clique)
      nil
    (let ((guard (getprop (car clique) 'guard t 'current-acl2-world world)))
      (cons (cons (car clique) guard)
            (clique-invariant-alist (cdr clique) world)))))

(defun name-and-number-lemmas (lemmas fn other-args n)
  (if (atom lemmas)
      (mv nil nil)
    (let ((name (intern-in-package-of-symbol
                     (concatenate
                      'string
                      (symbol-name fn)
                      "-INVARIANT-"
                      (coerce (explode-atom n 10) 'string)) fn)))
      (mv-let (rest-names rest-thms)
        (name-and-number-lemmas (cdr lemmas) fn other-args (1+ n))
        (mv (cons name rest-names)
            (cons `(defthm ,name
                     ,(car lemmas)
                     . ,other-args)
                  rest-thms))))))

(defun get-induction (fn world)
  (getprop fn 'induction-machine nil 'current-acl2-world world))

(defun gather-invariant-lemmas (alist full-alist simpl-hints use-induction
                                      other-args state)
  (if (atom alist)
      (mv nil nil state)
    (er-let* ((lemmas (if use-induction
                          (gather-invariant-reqs-from-induction
                           (get-induction (caar alist) (w state))
                           full-alist (cdar alist) simpl-hints state)
                        (gather-invariant-reqs
                         (get-body (caar alist) nil (w state))
                         (list `(:hyp ,(cdar alist)))
                         full-alist simpl-hints state nil))))
             (mv-let (rest-names rest-thms state)
               (gather-invariant-lemmas (cdr alist) full-alist simpl-hints
                                        use-induction other-args state)
               (mv-let (names thms)
                 (name-and-number-lemmas lemmas (caar alist) other-args 0)
                 (mv (append names rest-names)
                     (append thms rest-thms)
                     state))))))

(defun remove-these-keywords (keys args)
  (if (or (atom args) (atom (cdr args)))
      args
    (if (member-eq (car args) keys)
        (remove-these-keywords keys (cddr args))
      (list* (car args) (cadr args) (remove-these-keywords keys (cddr args))))))

(defun remove-numbered-entries (nums lst n)
  (if (atom lst)
      nil
    (if (member n nums)
        (remove-numbered-entries nums (cdr lst) (1+ n))
      (cons (car lst) (remove-numbered-entries nums (cdr lst) (1+ n))))))


(defun prove-invariants-fn (clique-member alist args state)
  (let* ((world (w state))
         (fns (get-clique-members clique-member world))
         (simplify-hints (cadr (assoc-keyword :simplify-hints args)))
         (omit (cadr (assoc-keyword :omit args)))
         (use-induction (cadr (assoc-keyword :use-induction args)))
         (other-args (remove-these-keywords
                      '(:simplify-hints :omit :use-induction) args))
         (alist (or alist (clique-invariant-alist fns world)))
         (theory-name (intern-in-package-of-symbol
                       (concatenate
                        'string
                        (symbol-name clique-member)
                        "-INVARIANTS")
                       clique-member)))
    (mv-let (names lemmas state)
      (gather-invariant-lemmas alist alist simplify-hints use-induction
                               other-args state)
      (let ((names (remove-numbered-entries omit names 0))
            (lemmas (remove-numbered-entries omit lemmas 0)))
        (value `(encapsulate
                 nil
                 ,@lemmas
                 (deftheory ,theory-name ',names)))))))
(defmacro prove-guard-invariants (fn &rest args)
  `(make-event (prove-invariants-fn ',fn nil ',args state)))

(defmacro prove-invariants (fn alist &rest args)
  `(make-event (prove-invariants-fn ',fn ',alist ',args state)))

