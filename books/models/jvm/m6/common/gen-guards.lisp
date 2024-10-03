(in-package "ACL2")
(include-book "misc/file-io" :dir :system)
(program)

(set-state-ok t)
(defun guard-thm-fn (name args state)

; This is adapted from ACL2 source function guard-clauses-for-fn.

 (let* ((ens (ens state))
        (wrld (w state))
        (newvar ; Matt K. mod; see ACL2 source function guard-clauses-for-fn1
         (genvar (cond ((symbolp name) name)
                       ((lambda-formals name) (car (lambda-formals name)))
                       (t 'APPLY$))
                 "NEWV"
                 nil
                 (all-vars!-of-fn name wrld))))
   (mv-let
     (normal-guard ttree)
; Matt K. mod: Update normalize call.
     (normalize (guard name nil wrld)
                t ; iff-flg
                nil ; type-alist
                ens wrld nil
                (backchain-limit wrld :ts))
     (mv-let
       (cl-set ttree)
; Matt K. mod: Update guard-clauses-for-body call.
       (guard-clauses-for-body (clausify (dumb-negate-lit normal-guard)
                                         nil t wrld)
                               (getprop name 'unnormalized-body
                                        '(:error "See GUARD-CLAUSES-FOR-FN.")
                                        'current-acl2-world wrld)
                               nil ; debug-info
                               nil ; stobj-optp
                               ens
                               wrld
                               nil ; safe-mode
                               nil ; gc-off
                               ttree
                               newvar)
       (declare (ignore ttree))
       (let ((guard-thm-name
              (intern-in-package-of-symbol
               (concatenate 'string (symbol-name name) "$GUARD-THM")
               name))
             (guard-op-name
              (intern-in-package-of-symbol
               (concatenate 'string (symbol-name name) "-GUARD")
               name)))
         `(defthm ,guard-thm-name
            ,(conjoin (prettyify-clause-lst cl-set nil wrld))
            :rule-classes ((:forward-chaining
                            :trigger-terms
                            ((,guard-op-name ,@args))))))))))


(defun defpredicate-fn (name args rest)
 `(progn (defun ,name ,args ,@rest)
         (defthm ,(intern-in-package-of-symbol
                   (concatenate 'string (symbol-name name) "$FORWARD")
                   name)
           (implies (,name ,@args)
                    ,(car (last rest)))
           :hints (("Goal"
                    :in-theory
                    (union-theories (theory 'ground-zero)
                                    '(,name))))
           :rule-classes :forward-chaining)))

(defmacro defpredicate (name args &rest rest)
 (defpredicate-fn name args rest))

(defmacro guard-thm (&rest args)
 `(value-triple ',args))

(defun guard-forms (forms acc state)
 (cond ((endp forms)
        (reverse acc))
       (t (guard-forms (cdr forms)
                       (let ((form (car forms)))
                         (if (and (consp form)
                                  (eq (car form) 'guard-thm))
                             (cons (guard-thm-fn (cadr form)
                                                 (cddr form)
                                                 state)
                                   acc)
                           acc))
                       state))))

(defun write-guards-fn (infile outfile state)
 (let ((ctx 'write-guards))
   (er-let* ((forms (read-list infile ctx state)))
            (let ((pkg-form (car forms)))
              (if (and (consp pkg-form)
                       (eq (car pkg-form) 'in-package)
                       (eql (length pkg-form) 2)
                       (equal (cadr pkg-form)
                              (current-package state)))
                  (write-list (guard-forms forms (list pkg-form) state)
                              outfile ctx state)
                (er soft 'write-guards
                    "Need to be in the package matching the first form of ~
                     ~x0,which should be an IN-PACKAGE form."
                    infile))))))

(defmacro write-guards (infile outfile)
 `(write-guards-fn ,infile ,outfile state))
