; Copyright (C) 2016, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)

(program)
(set-state-ok t)

(include-book "tools/remove-hyps" :dir :system) ; for event-steps
(include-book "kestrel/system/world-queries" :dir :system) ; for ruler-extenders

(defun not-none (r)

; Coerces :none to nil.

  (and (not (eq r :none))
       r))

(mutual-recursion

(defun possible-ruler-extenders (fns term)

; Normally returns a list of possible ruler-extenders, where term is a subterm
; of the body of a definition of one of the functions in fns, defined together
; with mutual-recursion.  However, return :none if there is a call in term of
; some function in fns but there are no ruler-extenders.

  (cond
   ((variablep term) nil)
   ((fquotep term) nil)
   ((eq (ffn-symb term) 'if)
    (let* ((r1 (possible-ruler-extenders fns (fargn term 1)))
           (r2 (possible-ruler-extenders fns (fargn term 2)))
           (r3 (possible-ruler-extenders fns (fargn term 3))))
      (and (or r1 r2 r3)
           (or (union$ (and r1
                            (cons 'if (not-none r1)))
                       (not-none r2)
                       (not-none r3)
                       :test 'eq)
               :none))))
   (t (let ((rs (possible-ruler-extenders-lst fns (fargs term))))
        (cond (rs (add-to-set-eq (if (flambdap (ffn-symb term))
                                     :lambdas
                                   (ffn-symb term))
                                 (not-none rs)))
              ((member-eq (ffn-symb term) fns)
               :none)
              (t nil))))))

(defun possible-ruler-extenders-lst (fns termlist)
  (cond ((endp termlist) nil)
        ((endp (cdr termlist))
         (possible-ruler-extenders fns (car termlist)))
        (t (let ((r1 (possible-ruler-extenders fns (car termlist)))
                 (r2 (possible-ruler-extenders-lst fns (cdr termlist))))
             (and (or r1 r2)
                  (or (union-eq (not-none r1)
                                (not-none r2))
                      :none))))))
)

(defun init-ruler-extenders (fn ruler-extenders term)
  (let ((re (possible-ruler-extenders (list fn) term)))
    (if (eq ruler-extenders :all)
        re
      (intersection-eq re ruler-extenders))))

(defconst *default-def-types*

; We expect some variant of defun here: (defxxx name args (decls/strings)* body).

  '(defun defund))

(defun minimal-ruler-extenders-steps (steps)
; This is quite arbitrary, but has worked well for remove-hyps.
  (+ 1000 (* 3 steps)))

(defun add-ruler-extenders (form ruler-extenders)
  (case-match form
    ((defxxx name formals . rest)
     `(,defxxx ,name ,formals
        (declare (xargs :ruler-extenders ,ruler-extenders))
        ,@rest))
    (& (er hard 'replace-ruler-extenders
           "Unexpected form: ~x0"
           form))))

(defun strip-ruler-extenders (form)
  (case-match form
    ((defxxx name formals . rest)
     `(,defxxx ,name ,formals
        ,@(strip-dcls '(:ruler-extenders) (butlast rest 1))
        ,(car (last rest))))
    (& (er hard 'replace-ruler-extenders
           "Unexpected form: ~x0"
           form))))

(defun minimal-ruler-extenders (form ruler-extenders steps acc verbose-p state)
  (cond
   ((endp ruler-extenders) (value (reverse acc)))
   (t (let ((form2 `(with-prover-step-limit
                     ,steps
                     ,(add-ruler-extenders
                       form
                       (append (cdr ruler-extenders) acc)))))
        (er-let* ((success (event-steps form2 verbose-p nil state)))
          (minimal-ruler-extenders form
                                   (cdr ruler-extenders)
                                   steps
                                   (if success
                                       acc
                                     (cons (car ruler-extenders) acc))
                                   verbose-p
                                   state))))))

(defmacro minimize-ruler-extenders (form &key verbose-p)
  `(make-event
    (let* ((verbose-p ,verbose-p)
           (def-types *default-def-types*)
           (form ',form)
           (form0 (strip-ruler-extenders form))
           (ctx 'minimize-ruler-extenders))
      (cond
       ((not (and (consp form)
                  (true-listp form)
                  (member-eq (car form) def-types)))
        (er soft ctx
            "Illegal call of ~x0 on form:~|~x1~|The form must be a true-list ~
             that is a call of ~v2."
            'minimal-ruler-extenders form def-types))
       (t
        (assert$
         (symbolp (cadr form)) ; name
         (er-let* ((ruler-extenders-p
                    (value (member-eq :ruler-extenders
                                      (dcl-fields (butlast (nthcdr 3 form) 1)))))
                   (steps
                    (event-steps (if ruler-extenders-p
                                     form
                                   (add-ruler-extenders form0 :all))
                                 verbose-p
                                 `((f-put-global 'minimal-r-e-body
                                                 (body ',(cadr form)
                                                       nil
                                                       (w state))
                                                 state)
                                   (f-put-global
                                    'minimal-r-e-ruler-extenders
                                    (ruler-extenders ',(cadr form)
                                                     (w state))
                                    state))
                                 state)))
           (cond
            ((null steps)
             (er soft ctx
                 "Original defun failed!"))
            (t (er-let* ((ruler-extenders
                          (minimal-ruler-extenders
                           form0
                           (init-ruler-extenders (cadr form)
                                                 (f-get-global
                                                  'minimal-r-e-ruler-extenders
                                                  state)
                                                 (f-get-global
                                                  'minimal-r-e-body
                                                  state))
                           (minimal-ruler-extenders-steps steps)
                           nil
                           verbose-p
                           state)))
                 (value (add-ruler-extenders form ruler-extenders))))))))))))

; Example:

(local
 (encapsulate
   ()
   (minimize-ruler-extenders
    (defun foo (x)
      (car (if (endp x)
               x
             (cons (foo (cdr x))
                   (evens (if (consp (cdr x))
                              (foo (cddr x))
                            nil)))))))
   (assert-event (equal (ruler-extenders 'foo (w state))
                        '(car)))))

; TO DO: Improve this documentation.

(defxdoc minimize-ruler-extenders
  :parents (kestrel-system-utilities system-utilities)
  :short "Minimize the ruler-extenders necessary to admit a definition"
  :long "<p>Example:</p>

 @({
 (minimize-ruler-extenders
  (defun foo (x)
    (car (if (endp x)
             x
           (cons (foo (cdr x))
                 (evens (if (consp (cdr x))
                            (foo (cddr x))
                          nil)))))))
 })

 <p>In the example above, a minimal set of @(see ruler-extenders) &mdash; in
 fact, THE minimal set &mdash; is the set @('{car}').  So the definition that is
 actually submitted, successfully, to ACL2 is obtained by making that
 explicit:</p>

 @({
 ACL2 !>:pe foo
  L         2:x(MINIMIZE-RULER-EXTENDERS (DEFUN FOO # ...))
               \
 >L             (DEFUN FOO (X)
                       (DECLARE (XARGS :RULER-EXTENDERS (CAR)))
                       (CAR (IF (ENDP X)
                                X
                                (CONS (FOO (CDR X))
                                      (EVENS (IF (CONSP (CDR X))
                                                 (FOO (CDDR X))
                                                 NIL))))))
 ACL2 !>
 })

 <p>The input form must be a call of @(tsee defun) or @(tsee defund).  If that
 form specifies @(':ruler-extenders lst'), then ACL2 will look for a minimal
 subsequence of @('lst') that can serve as the ruler-extenders.  Otherwise,
 ACL2 will start by additing an @(tsee xargs) declaration, @(':ruler-extenders
 lst'), where @('lst') contains every plausible ruler-extender, and then will
 try to find a minimal subsequence of @('lst').</p>")
