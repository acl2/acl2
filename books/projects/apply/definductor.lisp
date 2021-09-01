; Copyright (C) 2020, Regents of the University of Texas
; Written by Matt Kaufmann and J Moore
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Many thanks to ForrestHunt, Inc. for supporting the preponderance of this
; work, and for permission to include it here.

; This book provides a preliminary attempt at the definductor utility, which
; attempts to create an inductive hint function to associate with a
; loop$-recursive function.  At the moment we can only handle functions whose
; recursive loop$s all target a measured variable or cdr-nests of measured
; variables.  We can handle AS loop$s over such variables.  But we cannot
; handle functions containing recursive loop$s like

; (loop$ for e in (target x) collect ...)

; even when x is a measured variable.  Nor can we handle ON loop$s or
; FROM/TO/BY loop$s because their targets are (TAILS ...) and (FROM-TO-BY ...)
; expressions.  But it is a start!

(in-package "ACL2")

(program)

(defun car/cdr-nestp (cdr-only-flg term mvars)

; If term is a car/cdr nest around an element of mvars (which is a list of
; variable symbols), return the variable; else, nil.  If cdr-only-flg is t we
; insist that term be a cdr-nest (no cars allowed).

  (cond
   ((variablep term)
    (if (member-eq term mvars)
        term
        nil))
   ((fquotep term) nil)
   ((or (and (not cdr-only-flg) (eq (ffn-symb term) 'car))
        (eq (ffn-symb term) 'cdr))
    (car/cdr-nestp cdr-only-flg (fargn term 1) mvars))
   (t nil)))

(defun glue-terms (terms term)
  (cond
   ((endp terms) term)
   ((or (member-equal (car terms) (cdr terms))
        (equal (car terms) term))
    (glue-terms (cdr terms) term))
   (t `(return-last 'progn
                    ,(mark-loop$-recursion-nugget (car terms))
                    ,(glue-terms (cdr terms) term)))))

(defun nugget-fn-call-actuals1 (op targets)

; Op is either CAR, CDR, or NIL.  Targets is a list of k resolved loop$
; targets, each being a car/cdr-nest around a variable.  Let the ith element of
; targets be ti and let its variable be vi.  We form the substitution ((v1
; . (op t1)) ... (vk . (op tk))), except when op is NIL (op ti) is just ti.
; Note that we have no guarantee that this is actually a substitution: some vi
; may be bound twice.  But when treated as a substitution, only the first
; binding matters.

  (cond
   ((endp targets) nil)
   (t (cons (cons (car (all-vars (car targets)))
                  (if op
                      (list op (car targets))
                      (car targets)))
            (nugget-fn-call-actuals1 op (cdr targets))))))

(defun nugget-fn-call-actuals (formals op targets)

; Suppose formals is '(A B X Y Z), op is CAR, and targets is ((CDR X) (CDR (CAR
; Z))).  Then this function would return (A B (CAR (CDR X)) Y (CAR (CDR (CAR
; Z)))).

  (sublis-var-lst (nugget-fn-call-actuals1 op targets)
                  formals))

(mutual-recursion

(defun car-cdr-cons-rewriter (term)

; Term is a term and we simplify it by applying (car (cons x y)) = x and (cdr
; (cons x y)) = y.  We also apply (car atom) = (cdr atom) = nil.  We apply no
; other rules.  We do not anticipate term containing lambda applications
; (because they will have been expanded).  So if term does contain lambda
; applications they're treated just like conventional function calls.

  (cond
   ((variablep term) term)
   ((fquotep term) term)
   ((eq (ffn-symb term) 'car)
    (let ((arg (car-cdr-cons-rewriter (fargn term 1))))
      (cond
       ((variablep arg) term)
       ((fquotep arg)
        (let ((evg (unquote arg)))
          (cond ((atom evg) *nil*)
                (t (kwote (car evg))))))
       ((eq (ffn-symb arg) 'cons)
        (fargn arg 1))
       (t term))))
   ((eq (ffn-symb term) 'cdr)
    (let ((arg (car-cdr-cons-rewriter (fargn term 1))))
      (cond
       ((variablep arg) term)
       ((fquotep arg)
        (let ((evg (unquote arg)))
          (cond ((atom evg) *nil*)
                (t (kwote (cdr evg))))))
       ((eq (ffn-symb arg) 'cons)
        (fargn arg 2))
       (t term))))
   (t (fcons-term (ffn-symb term)
                  (car-cdr-cons-rewriter-list (fargs term))))))

(defun car-cdr-cons-rewriter-list (terms)
  (cond
   ((endp terms) nil)
   (t (cons (car-cdr-cons-rewriter (car terms))
            (car-cdr-cons-rewriter-list (cdr terms)))))))

(defun car/cdr-nestsp (cdr-only-flg terms mvars)
  (cond
   ((endp terms) t)
   (t (and (car/cdr-nestp cdr-only-flg (car terms) mvars)
           (car/cdr-nestsp cdr-only-flg (cdr terms) mvars)))))

(defun leftmost-innermost (term)
  (cond
   ((variablep term) term)
   ((or (fquotep term)
        (null (fargs term)))
    term)
   (t (leftmost-innermost (fargn term 1)))))

(defun leftmost-innermost-lst (terms)
  (cond
   ((endp terms) nil)
   (t (cons (leftmost-innermost (car terms))
            (leftmost-innermost-lst (cdr terms))))))

(defun variablesp (lst)
  (cond ((endp lst) t)
        (t (and (variablep (car lst))
                (variablesp (cdr lst))))))

(defun true-cons-nestp (term)
  (cond
   ((variablep term) nil)
   ((fquotep term) (equal term *nil*))
   (t (and (eq (ffn-symb term) 'CONS)
           (true-cons-nestp (fargn term 2))))))

(defun strip-true-cons-nest (term)
  (cond
   ((variablep term) nil) ; can't happen
   ((fquotep term) nil)
   (t (cons (fargn term 1)
            (strip-true-cons-nest (fargn term 2))))))

(defun conjoined-consps (terms)
  (cond ((endp terms) *t*)
        (t `(IF (CONSP ,(car terms))
                ,(conjoined-consps (cdr terms))
                'NIL))))

(defun consed-cars (terms)
  (cond ((endp terms) *nil*)
        (t `(CONS (CAR ,(car terms))
                  ,(consed-cars (cdr terms))))))

(defun variablep-lst (lst)
  (cond ((endp lst) t)
        (t (and (variablep (car lst))
                (variablep-lst (cdr lst))))))



; Invariant about mvars and alist: In this code, mvars starts out as the list
; of measured formals when we start to analyze the body of a function, and
; alist is nil.  As we dive into loop$s we extend mvars with the iterative
; variable(s) of the loop$, provided the target is a cdr-nest around an element
; of mvars.  We also extend alist by pairing the iterative variable with the
; CAR of the target, except we first ``resolve'' the target by applying the
; alist to it.  Thus, the alist always maps iterative variables in mvars to the
; car/cdr-nests denoting the first value the iterative variable takes on,
; expressed entirely in terms of the original formals.  Thus, if at the
; top-level of a fn's body, where the (original) mvars is just the list (x),
; then we get to alpha in (loop$ for e in (cdr x) collect alpha), mvars is (e
; x) and alist is ((e . (car (cdr x)))).  If alpha is (loop$ for d in (cdr (cdr
; e)) collect beta), then when we see beta mvars is (d e x) and alist is ((d
; . (car (cdr (cdr (car (cdr x)))))) (e . (car (cdr x)))).

(defun nugget (fn formals mvars alist term)

; We return (mv erp nugget), where erp is either a msg or nil.  Nugget is
; relevant only when erp is nil and is nil or the nugget for term.  When nugget
; is non-nil it means term is a recursive loop$ scion call satisfying various
; conditions on its target.  When erp is non-nil it is a message that completes
; the sentence ``No inductor for fn can be generated because ''.

  (let ((style (loop$-scion-style (ffn-symb term) *loop$-keyword-info*)))
    (cond
     ((eq style :plain)
      (case-match term
        ((& ('quote ('lambda (e) body)) target) ; which scion doesn't matter!
         (cond
          ((not (loop$-recursion-ffnnamep fn body))
           (mv nil nil))
          (t (let ((resolved-target (sublis-var alist target)))
               (cond
                ((car/cdr-nestp t target mvars)

; Target is a cdr-nest of an mvar, and alist maps mvars to car/cdr-nests of
; measured formals, so resolved-target is a car/cdr-nest around a measured
; formal and below we call that formal the resolved-var.

                 (let* ((resolved-var (leftmost-innermost resolved-target)))
                   (mv nil
                       `(if (consp ,resolved-var)
                            ,(glue-terms
                              `(,(if (ffnnamep fn body)
                                     (car-cdr-cons-rewriter
                                      (expand-all-lambdas
                                       `((lambda (,e) ,body)
                                         (car ,resolved-var))))
                                     `(,fn ,@(nugget-fn-call-actuals
                                              formals
                                              'car
                                              (list resolved-var))))
; add the short-cut instance if req'd
                                ,@(if (variablep resolved-target)
                                      nil
                                      `((,fn ,@(nugget-fn-call-actuals
                                                formals
                                                nil
                                                (list resolved-target))))))
                              `(,fn ,@(nugget-fn-call-actuals
                                       formals
                                       'cdr
                                       (list resolved-var))))
                            'nil))))
                (t (mv (msg "it contains a loop$ over the non-inductible target ~
                           ~x0."
                            target)
                       nil)))))))
        (& (mv nil nil))))
     ((eq style :fancy)
      (case-match term
        ((scion ('QUOTE ('LAMBDA (gvars ivars) body)) gactuals target)
         (cond
          ((not (loop$-recursion-ffnnamep fn body))
           (mv nil nil))
          ((not (and (nvariablep target)
                     (not (fquotep target))
                     (eq (ffn-symb target) 'LOOP$-AS)
                     (true-cons-nestp (fargn target 1))))
           (mv (msg "it uses the fancy loop$ scion ~x0 to map over a target, ~
                     ~x1, that we cannot destructure.  We expect the target ~
                     to be (LOOP$-AS (LIST t1 ... tn))."
                    scion
                    target)
               nil))
          (t
           (let* ((targets (strip-true-cons-nest (fargn target 1)))
                  (resolved-targets (sublis-var-lst alist targets)))
             (cond
              ((car/cdr-nestsp t targets mvars)

; Targets is list of cdr-nests, each on an mvar, and alist maps mvars to
; car/cdr-nests of measured formals, so resolved-targets is a list of
; car/cdr-nest around a measured formal and below we call those formals the
; resolved-vars.  They must all be distinct.

               (let* ((resolved-vars (leftmost-innermost-lst resolved-targets)))
                 (cond
                  ((not (no-duplicatesp resolved-vars))
                   (mv (msg "it calls the fancy loop$ scion ~x0 on a list of ~
                             targets that share measured formals ~x1."
                            scion
                            target)
                       nil))
                  (t
                   (mv nil
                       `(if ,(conjoined-consps resolved-vars)
                            ,(glue-terms
                              `(,(if (ffnnamep fn body)
                                     (car-cdr-cons-rewriter
                                      (expand-all-lambdas
                                       `((lambda (,gvars ,ivars) ,body)
                                         ,gactuals
                                         ,(consed-cars resolved-vars))))
                                     `(,fn ,@(nugget-fn-call-actuals
                                              formals
                                              'car
                                              resolved-vars)))
; add the short-cut instance if req'd
                                ,@(if (variablep-lst resolved-targets)
                                      nil
                                      `((,fn ,@(nugget-fn-call-actuals
                                                formals
                                                nil
                                                resolved-targets)))))
                              `(,fn ,@(nugget-fn-call-actuals
                                       formals
                                       'cdr
                                       resolved-vars)))
                            'nil))))))
              (t (mv (msg "it contains a loop$ over the non-inductible target ~
                           ~x0."
                          target)
                     nil)))))))
        (& (mv nil nil))))
     (t (mv nil nil)))))

(mutual-recursion

(defun generate-loop$-scion-nuggets (fn formals mvars alist term)

; We explore the fn-recursive loop$ scion calls in term and generate nugget for
; each one that we can.  We return (mv erp nuggets), where erp is a msg or nil and
; nuggets (relevant only if erp is nil) is the list of nuggets, which may be nil even
; if there are loop$ recursive calls because we can't see a way to generate a
; nugget.  Mvars is initially a list of the formals of fn that are somehow
; measured but is extended as we dive into certain loop$ scion calls that
; target car/cdr-nests of mvars.  We have no guarantee that the measure of fn
; decreases under a car/cdr nest!  But at least we can hope!  Admitting the
; inductor function will prove that the measure decreases.  Alist is an alist
; pairing iteration variables with their actual targets, where targets are
; expressed entirely in terms of formals of fn.  So, for example, if v is an
; mvar and alist is initially nil and term is

;  (sum$ '(lambda (e) (sum$ '(lambda (d) (fn d)) (cddr e))) (car v))

; then when we see (fn d), d is bound in alist to (cddr (car v)), which means d
; is taking on values over that target.

  (cond
   ((variablep term)
    (mv nil nil))
   ((fquotep term)
    (mv nil nil))
   ((lambda-applicationp term)
    (generate-loop$-scion-nuggets
     fn formals mvars
     alist
     (sublis-var (pairlis$ (lambda-formals (ffn-symb term))
                           (fargs term))
                 (lambda-body (ffn-symb term)))))
   (t (mv-let (erp nugget)
        (nugget fn formals mvars alist term)
        (cond
         (erp (mv erp nil))
         (nugget

; Term is a recursive loop$ scion call (because we only generate nuggets for
; such terms).  We have generated a nugget for term, which means its target was
; a (possibly empty) car/cdr nest around an mvar.  But that might included
; targets like (cdr (cdr evar)) where evar is not among mvars but is the
; iteration variable of a superior loop$ and is being iterated over a cdr-nest
; of an mvar.  E.g., evar may be mapped to (cdr (cdr x)) in alist, where x is
; an mvar.  We need to try to generate nuggets from term's body and for term's
; fargs.  (Right now, term is guaranteed to be a :plain scion call so there are
; no non-quoted fargs other than the target itself.)  During these recursions
; we consider evar (the variable in target) to be an mvar.

; But we need to re-consider when term can be :fancy.

          (let* ((obj (unquote (fargn term 1)))
                 (target (fargn term 2))
                 (ivar (car (lambda-object-formals obj)))

; Whenever we add a var to mvars we must also bind that var in alist to the CAR
; of the target/alist.  Thus, alist always maps mvars (except the original
; formals) to car/cdr-nests around original formals, and every element of mvars
; is measured or a car/cdr component of a measured var.

                 (mvars1 (add-to-set-eq ivar mvars))
                 (alist1 (cons (cons ivar `(car ,(sublis-var alist target)))
                               alist))
                 (body (lambda-object-body obj)))
            (mv-let (erp nuggets-from-body)
              (generate-loop$-scion-nuggets fn formals mvars1 alist1 body)
              (cond
               (erp (mv erp nil))
               (t (mv-let (erp nuggets-from-target)
                    (generate-loop$-scion-nuggets
                     fn formals mvars alist target)
                    (cond
                     (erp (mv erp nil))
                     (t
                      (mv nil
                          (add-to-set-equal
                           nugget
                           (union-equal nuggets-from-body
                                        nuggets-from-target)))))))))))
         (t (generate-loop$-scion-nuggets-list fn formals mvars alist
                                               (fargs term))))))))

 (defun generate-loop$-scion-nuggets-list (fn formals mvars alist terms)
   (cond
    ((endp terms) (mv nil nil))
    (t (mv-let (erp nuggets1)
         (generate-loop$-scion-nuggets
          fn formals mvars alist (car terms))
         (cond
          (erp (mv erp nil))
          (t (mv-let (erp nuggets2)
               (generate-loop$-scion-nuggets-list
                fn formals mvars alist (cdr terms))
               (cond
                (erp (mv erp nil))
                (t (mv nil
                       (union-equal nuggets1 nuggets2)))))))))))
 )

(defun get-loop$-scion-default-quoted-lambda-object (scion alist)
  (cond
   ((endp alist) *nil*)
   ((eq scion (cadr (car alist)))
; A :plain loop$ scion call.
    (case (car (car alist))
      (sum ''(LAMBDA (E) (DECLARE (IGNORE E)) '0))
      (always ''(LAMBDA (E) (DECLARE (IGNORE E)) 'T))
      (thereis ''(LAMBDA (E) (DECLARE (IGNORE E)) 'NIL))
      (collect ''(LAMBDA (E) (DECLARE (IGNORE E)) 'NIL))
      (append ''(LAMBDA (E) (DECLARE (IGNORE E)) 'NIL))

; If it is not one of the above then it is an until$ or when$ and we just pick
; *nil* as the default.

      (otherwise ''(LAMBDA (E) (DECLARE (IGNORE E)) 'NIL))))
   ((eq scion (caddr (car alist)))
; A :fancy loop$ scion call.
    (case (car (car alist))
      (sum ''(LAMBDA (LOOP$-GVARS LOOP$-IVARS)
                     (DECLARE (IGNORE LOOP$-GVARS LOOP$-IVARS))
                     '0))
      (always ''(LAMBDA (LOOP$-GVARS LOOP$-IVARS)
                        (DECLARE (IGNORE LOOP$-GVARS LOOP$-IVARS))
                        'T))
      (thereis ''(LAMBDA (LOOP$-GVARS LOOP$-IVARS)
                         (DECLARE (IGNORE LOOP$-GVARS LOOP$-IVARS))
                         'NIL))
      (collect ''(LAMBDA (LOOP$-GVARS LOOP$-IVARS)
                         (DECLARE (IGNORE LOOP$-GVARS LOOP$-IVARS))
                         'NIL))
      (append ''(LAMBDA (LOOP$-GVARS LOOP$-IVARS)
                        (DECLARE (IGNORE LOOP$-GVARS LOOP$-IVARS))
                        'NIL))
      (otherwise ''(LAMBDA (LOOP$-GVARS LOOP$-IVARS)
                           (DECLARE (IGNORE LOOP$-GVARS LOOP$-IVARS))
                           'NIL))))
   (t (get-loop$-scion-default-quoted-lambda-object scion (cdr alist)))))

(mutual-recursion

(defun rename-fn-and-replace-loop$-lambda-objs (new-fn old-fn term)
  (cond
   ((variablep term) term)
   ((fquotep term) term)
   ((lambda-applicationp term)
    (cons-term (make-lambda (lambda-formals (ffn-symb term))
                            (rename-fn-and-replace-loop$-lambda-objs
                             new-fn
                             old-fn
                             (lambda-body (ffn-symb term))))
               (rename-fn-and-replace-loop$-lambda-objs-list
                new-fn old-fn
                (fargs term))))
   ((eq (ffn-symb term) old-fn)
    (cons-term new-fn
               (rename-fn-and-replace-loop$-lambda-objs-list
                new-fn old-fn
                (fargs term))))
   ((and (loop$-scion-style (ffn-symb term) *loop$-keyword-info*)
         (quotep (fargn term 1))
         (consp (unquote (fargn term 1)))
         (eq (car (unquote (fargn term 1))) 'lambda))

; We don't actually know whether this loop$ scion call is :plain or :fancy or
; even whether its lambda object contains a recursive call.  We don't care!  We
; just replace the lambda object by a non-recursive one of the ``right'' type
; and signature.  This way we preserve the other arguments, which might involve
; clear recursive calls (not ones buried inside of quoted lambdas).  Of course,
; it could happen that the lambda object we're replacing has clear recursive
; calls.  But they wouldn't contribute to a subsequent induction analysis since
; the current induction machine machinery does not look into quoted objects.

    (cons-term (ffn-symb term)
               (cons (get-loop$-scion-default-quoted-lambda-object
                      (ffn-symb term)
                      *loop$-keyword-info*)
                     (rename-fn-and-replace-loop$-lambda-objs-list
                      new-fn old-fn
                      (cdr (fargs term))))))
   (t (cons-term (ffn-symb term)
                 (rename-fn-and-replace-loop$-lambda-objs-list
                  new-fn old-fn
                  (fargs term))))))

(defun rename-fn-and-replace-loop$-lambda-objs-list (new-fn old-fn terms)
  (cond
   ((endp terms) nil)
   (t (cons (rename-fn-and-replace-loop$-lambda-objs new-fn old-fn
                                                     (car terms))
            (rename-fn-and-replace-loop$-lambda-objs-list new-fn old-fn
                                                          (cdr terms))))))

)

(defun make-inductor-defun-and-rule
  (fn inductor-fn measure rel ruler-extenders hints wrld)

; Fn is the name of an already admitted loop$-recursive function, inductor-fn
; is nil or the name we are to use for the generated loop$ recursive induction
; function (aka the ``inductor'') for fn.  Measure, rel, ruler-extenders, and
; hints are user-supplied xargs settings of the inductor's defun.  We assume fn
; is a loop$-recursive function symbol, inductor-fn is a symbol (possibly nil),
; and measure is a fully translated term.  We don't inspect rel,
; ruler-extenders, or hints and just paste them into the defun we generate, so
; they are error-checked by the execution of that defun.  We return an
; encapsulate event defining the inductor and the associated rule linking it to
; fn, or else nil, meaning no inductor function can be generated by current
; heuristics.

  (let* ((inductor-fn1 (or inductor-fn
                           (packn (list fn '-inductor))))
         (formals (formals fn wrld))
         (body (remove-guard-holders (body fn nil wrld) wrld))
         (jst (getpropc fn 'justification nil wrld))
         (measure1 (or measure
                       (access justification jst :measure)))
         (rel1 (or rel
                   (access justification jst :rel)))
         (ruler-extenders1 (or ruler-extenders
                               (access justification jst :ruler-extenders)))
         (mvars (all-vars measure1)))
    (mv-let (erp nuggets)
      (generate-loop$-scion-nuggets fn formals mvars nil body)
      (cond
       (erp (mv erp nil))
       (t (let* ((body1
                  (if nuggets
                      (rename-fn-and-replace-loop$-lambda-objs-list
                       inductor-fn1 fn
                       (glue-terms nuggets body))
                      *nil*))
                 (ignores (set-difference-eq formals (all-vars body1)))
                 (rule-name (packn (list fn '-induction-rule))))
            (cond
             (nuggets
              (mv nil
                  `(encapsulate
                     nil
                     (defun$ ,inductor-fn1 ,formals
                       (declare (xargs :mode :logic
                                       :measure ,measure1
                                       :well-founded-relation ,rel1
                                       :ruler-extenders ,ruler-extenders1
                                       ,@(if hints
                                             `(:hints ,hints)
                                             nil))
                                ,@(if ignores
                                      `(ignore ,@ignores)
                                      nil))
                       ,body1)
                     (defthm ,rule-name t
                       :rule-classes ((:induction
                                       :pattern (,fn ,@formals)
                                       :scheme (,inductor-fn1 ,@formals)))))))
             (t (mv (msg "there are no recursive loop$s in it.")
                    nil)))))))))

(set-state-ok t)

(defun definductor-fn1 (fn inductor-fn measure well-founded-relation
                           ruler-extenders hints state)
  (let ((wrld (w state)))
    (cond
     ((or (not (symbolp fn))
          (not (getpropc fn 'loop$-recursion nil wrld)))
      (er soft 'definductor
          "The first argument to definductor must be the name of a previously ~
         defined loop$-recursive function and ~x0 is not."
          fn))
     ((not (symbolp inductor-fn))
      (er soft 'definductor
          "The second argument to definductor must be nil or the name you ~
         choose to give to the inductor function generated for ~x0 but ~x1 is ~
         not a symbol."
          fn inductor-fn))
     (t (er-let*
            ((measures (if measure
                           (translate-measures (list measure) t 'definductor
                                               wrld state)
                           (value '(nil)))))
          (let* ((tmeasure (car measures))) ; translated measure
            (mv-let (erp encap)
              (make-inductor-defun-and-rule
               fn inductor-fn tmeasure well-founded-relation ruler-extenders
               hints wrld)
              (cond
               (erp (er soft 'definductor
                        "We cannot construct an inductor for ~x0 because ~@1"
                        fn erp))
               (t (value encap))))))))))

(defun definductor-fn (fn inductor-fn measure well-founded-relation
                          ruler-extenders hints)
  (declare (xargs :mode :logic :guard t)) ; for execution speed in safe-mode
  `(definductor-fn1 ',fn
     ',inductor-fn
     ',measure
     ',well-founded-relation
     ',ruler-extenders
     ',hints
     state))

(defmacro definductor (fn &key inductor-fn measure well-founded-relation
                          ruler-extenders hints)
  `(with-output
     :off
; *valid-output-names* except for error
     (warning warning! observation prove proof-builder event history summary
              proof-tree)
     :stack :push
     :gag-mode nil
     (make-event
      (with-output
        :stack :pop
        ,(definductor-fn fn inductor-fn measure well-founded-relation
           ruler-extenders hints))
      :on-behalf-of :quiet!
; See note below.
      :check-expansion t)))
