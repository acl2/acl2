; (ld '((include-book "defsys-utilities") . "defsys.lisp") :ld-pre-eval-print t)

; (include-book "defsys-utilities")
; (certify-book "defsys" 1)

; Defsys -- a Verifying Mini-Compiler for M1
; J Strother Moore
; March, 2012

; This file provides the defsys utility.  It takes a list of ``modules,''
; compiles them into M1 code, defines the appropriate clocks and semantic
; functions, and proves that the code is correct.  Here is an example that
; illustrates what a ``module'' is and how the code is described in a
; high-level source language akin to ACL2 except using IFEQ.

; Every system is configured so that when starting from 0 it calls the MAIN
; module using the arguments on the stack.  It then halts.  Note that a module
; may return multiple values (see MOD2-FLOOR2) and note how that module is
; called in the :code for MAIN: It is passed to RECOMBINE which treats
; MOD2-FLOOR2 as having supplied 2 of its arguments.  (RECOMBINE needs 3 args
; but is given 2 actual expressions in MAIN.)

; Defsys also supports ``ghost variables.''  These are variables need to insure
; termination of the corresponding ACL2 functions.  The provisions for ghost
; variables are very hackish, designed with one example in mind: the situation
; when the top level routine in a system doesn't always terminate and MAIN
; calls it.  Ghost variables allow the additional keywords :ghost-formals,
; :ghost-base-test, :ghost-base-value and :ghost-decr.  These are,
; respectively, a list of variables, a test leading to forced termination, the
; result in the case of forced termination, and a list of ``decrement''
; expressions to be appended to every recursive call of fn.  We assume that
; (nth 0 ghost-base-value) is 0 when forced termination occurs.

; Basically a function like

; (defun fn (vars)
;   body)

; with those additional keyword specifiers becomes:

; (defun fn (vars ,@ghost-formals)
;   (if ,ghost-base-test
;       ,ghost-base-value
;       body'))

; where body' is body with all calls of fn given the additional final arguments
; listed in ghost-decr.  For a relatively simple example of a use of ghost
; variables, see low-seven.lisp.

#|
(defsys t
  (mod2-floor2 :formals (x a)
               :input (and (natp x) (natp a))
               :output (mv (mod x 2) (+ a (floor x 2)))
               :code (ifeq x (mv 0 a) (ifeq (- x 1) (mv 1 a) (mod2-floor2 (- x 2) (+ a 1))))
               :post-events nil)
  (recombine :formals (m q y)
             :input (and (natp m)(natp q)(natp y))
             :output (+ m (* y q))
             :code (+ m (* y q)))
  (lessp :formals (x y)
         :input (and (natp x)
                     (natp y))
         :output (if (< x y) 1 0)
         :code (ifeq y
                     0
                     (ifeq x
                           1
                           (lessp (- x 1) (- y 1)))))
  (mod :formals (x y)
       :input (and (natp x)
                   (natp y)
                   (not (equal y 0)))
       :output (mod x y)
       :code (ifeq (lessp x y)
                   (mod (- x y) y)
                   x))
  (floor :formals (x y a)
         :input (and (natp x)
                     (natp y)
                     (not (equal y 0))
                     (natp a))
         :output (+ a (floor x y))
         :code (ifeq (lessp x y)
                     (floor (- x y) y (+ a 1))
                     a))
  (main :formals (x y a)
        :input (and (natp x)
                    (natp y)
                    (not (equal y 0))
                    (natp a))
        :output (+ (* 10000 (+ (mod x y) (* y (floor x y)))) a)
        :code (+ (* 10000 (+ (mod x y) (* y (floor x y 0))))
                 (recombine (mod2-floor2 a 0) 2))))

(acl2::pe 'm1-psi)

(defthm m1-psi-thm
  (implies (and (natp x)
                (natp y)
                (not (equal y 0))
                (natp a))
           (let ((sf (m1-psi x y a)))
             (and (equal (next-inst sf) '(HALT))
                  (equal (top (stack sf)) (+ (* 10000 x) a))))))

(clk+ 2 (main-clock nil 231 7 456))

(next-inst (m1-psi 231 7 456))
; = (HALT)
(top (stack (m1-psi 231 7 456)))
; = 2310456

QED!

|#

(in-package "M1")
(acl2::program)

; -----------------------------------------------------------------

(defun pack (lst)
  (declare (xargs :mode :program))
  (intern-in-package-of-symbol
   (coerce (acl2::packn1 lst)
           'string)
   'm1))


; (defmacro trace$ (&rest args) `(acl2::trace$ ,@args))
; (defmacro untrace$ (&rest args) `(acl2::untrace$ ,@args))

; -----------------------------------------------------------------

(acl2::set-irrelevant-formals-ok t)

(defun rev1 (x a)
  (if (endp x)
      a
      (rev1 (cdr x) (cons (car x) a))))

(defun all-but-last (x)
  (declare (xargs :mode :logic))
  (if (endp x)
      nil
      (if (endp (cdr x))
          nil
          (cons (car x) (all-but-last (cdr x))))))



(defun nv (fn var vars)
  (let ((temp (member-equal var vars)))
    (cond (temp
; if a-reg were not 0, we'd have to add it to this number:
           (- (len vars) (len temp)))
          (t (er hard 'defsys
                 "While compiling ~x0 we encountered an undeclared variable ~
                  ~x1.  The locals of ~x0 are ~x2."
                 fn var vars)))))

; When we ILOAD a series of regs, we go from base up.  When we ISTORE a
; series of regs, we go down to base.

(defun ILOAD-series (base n)
; (ILOAD-series 7 2) ==> ((ILOAD 7) (ILOAD 8))
  (cond ((zp n) nil)
        (t (cons `(ILOAD ,base)
                 (ILOAD-series (+ 1 base) (- n 1))))))

(defun ISTORE-series (base n)
  (cond ((zp n) nil)
        (t (cons `(ISTORE ,(+ base n -1))
                 (ISTORE-series base (- n 1))))))

(defun save-regs (n max-a-regs)
  `((ISTORE ,(* 2 max-a-regs))
    ,@(ISTORE-series max-a-regs n)
    ,@(ILOAD-series 0 n)
    (ILOAD ,(* 2 max-a-regs))
    ,@(ILOAD-series max-a-regs n)
    ,@(ISTORE-series 0 n)))

; Let mvn below be the ;output-arity of the module.  We save the mvn results
; temporarily into the B regs while we restore the pushed A regs.  We know that
; at the end of this the ret pc is in the return pc register 2max-a-regs.

(defun restore-regs (mvn n max-a-regs)
  `(,@(ISTORE-series max-a-regs mvn)
    (ISTORE ,(* 2 max-a-regs))
    ,@(ISTORE-series 0 n)
    ,@(ILOAD-series max-a-regs mvn)))

(defun icount (acode)

; Given a segment of acode generated by compiler-expr count how many
; instructions will be in it after it is assembled and linked.  We know the
; compiler does not lay down labels and it doesn't generate RETs.  So the only
; pseudo-instructions in acode are CALLs.

  (cond ((endp acode) 0)
        ((and (consp (car acode))
              (eq (op-code (car acode)) 'CALL))
         (+ 2 (icount (cdr acode))))
        ((and (consp (car acode))
              (member (op-code (car acode))
                      '(iload istore iconst iadd isub imul ifeq goto call)))
         (+ (if (eq (op-code (car acode)) 'CALL)
                2
                1)
            (icount (cdr acode))))
        (t
         (er hard 'icount
             "Acode encountered an illegal instruction, label, or pseudo-instruction, ~x0."
             (car acode)))))

; We are about to implement a compiler from simple recursive functions to M1.
; We will then implement a clock compiler to produce the corresponding
; clock function.  To implement the clock compiler we must know the
; return pc to which which each CALL returns.  That return pc affects the
; clock for the CALL since the amount of time taken in the RET from that
; call is a function of that return pc.

; But the clock compiler is not looking at the compiled code where the CALL
; really is.  It is looking at the high level language expression that was
; compiled.  So how can the clock compiler determine the return pc for each
; call?  We solve this problem by ``annotating'' the input definitions before
; we begin compiling.  The annotation changes every function call (fn a1
; ... an) into (fn id a1' ... an'), where id is a unique object associated with
; this occurrence of this expression and the ai' are the recursively annotated
; subexpressions.

; The compiler generates annotated call statements, (CALL FOO id).
; Add-return-labels, the function that adds return pc labels after each CALL,
; builds a table associating the ids with the labels generated.  The linker
; then builds a table associating labels with pcs.  So when the clock
; compiler crawls over the annotated expressions to create the clocks it can
; look at the id of the expression, get the corresponding label, and then the
; corresponding return pc.

(mutual-recursion
 (defun annotate-expr (x id)
   (cond ((atom x) x)
         ((eq (car x) 'quote) x)
         (t (cons (car x) (cons id (annotate-expr-lst (cdr x) 0 id))))))
 (defun annotate-expr-lst (x i id)
   (cond ((endp x) nil)
         (t (cons (annotate-expr (car x) (cons i id))
                  (annotate-expr-lst (cdr x) (+ i 1) id))))))

(mutual-recursion
 (defun strip-annotations-expr (x)
   (cond ((atom x) x)
         ((eq (car x) 'quote) x)
         (t (cons (car x) (strip-annotations-expr-lst (cdr (cdr x)))))))

 (defun strip-annotations-expr-lst (x)
   (cond ((endp x) nil)
         (t (cons (strip-annotations-expr (car x))
                  (strip-annotations-expr-lst (cdr x)))))))

; We handle tail recursive functions only.  We can properly compile full-blown
; recursions and also properly compile ``sometimes tail-recursive'' functions
; (which, like mc-flatten, contain both full-blown recursion and
; tail-recursion).  But our clock compiler and the basic proof strategy do
; not work for such functions.

(mutual-recursion
 (defun recursions-okp (mode fn expr)

; We support two modes, :tail and :none.  The former checks that the only
; recursions in expr are tail-recursive.  The latter checks that there are no
; recursions in expr.

   (cond ((atom expr) t)
         ((eq (car expr) 'quote) t)
         ((eq (car expr) 'IF)
          (er hard 'compile-expr
              "The compiler does not support IF.  Use IFEQ."))
         ((eq (car expr) 'IFEQ)
          (and (recursions-okp :none fn (nth 1 expr))
               (recursions-okp mode fn (nth 2 expr))
               (recursions-okp mode fn (nth 3 expr))))
         ((eq (car expr) fn)
          (if (eq mode :none)
              nil
              (recursions-okp-lst :none fn (cdr expr))))
         (t (recursions-okp-lst :none fn (cdr expr)))))
 (defun recursions-okp-lst (mode fn lst)
   (cond ((endp lst) t)
         (t (and (recursions-okp mode fn (car lst))
                 (recursions-okp-lst mode fn (cdr lst)))))))

(mutual-recursion
 (defun chk-input-output-arity (expr amodules)

; Amodules is the list of modules annotated so far.  Each module has a :formals
; and an :output-arity field.  We confirm that every call of every function in
; the annotated expression has the right number of arguments.  If so, we return
; its output arity.  If not, we cause a hard error.

   (cond
    ((atom expr) 1)
    ((eq (car expr) 'quote) 1)
    ((eq (car expr) 'MV)
     (chk-input-output-arity-lst (cddr expr) amodules))
    ((eq (car expr) 'IFEQ)
     (let ((test-output
            (chk-input-output-arity (nth 2 expr) amodules))
           (then-output
            (chk-input-output-arity (nth 3 expr) amodules))
           (else-output
            (chk-input-output-arity (nth 4 expr) amodules)))
       (cond
        ((not (equal test-output 1))
         (er hard 'defsys
             "The test of an IFEQ must return 1 result but the test of ~x0 ~
              returns ~x1."
             expr test-output))
        ((equal then-output else-output)
         then-output)
        (t (er hard 'defsys
               "Both branches of an IFEQ must return the same number of ~
                results, but in ~x0 the THEN branch returns ~x1 and the ELSE ~
                branch returns ~x2."
               expr then-output else-output)))))
    (t
     (let ((fn (car expr))
           (expected-inputs
            (if (member (car expr) '(+ - *))
                2
                (if (assoc-equal (car expr) amodules)
                    (len (cadr (assoc-keyword :formals
                                              (cdr (assoc-equal (car expr) amodules)))))
                    nil)))
           (expected-outputs
            (if (member (car expr) '(+ - *))
                1
                (if (assoc-equal (car expr) amodules)
                    (cadr (assoc-keyword :output-arity
                                         (cdr (assoc-equal (car expr) amodules))))
                    nil))))
       (cond
        ((equal expected-inputs nil)
         (er hard 'defsys "Unknown function ~x0" fn))
        (t (let ((actual-inputs
                  (chk-input-output-arity-lst (cddr expr) amodules)))
             (cond ((equal actual-inputs expected-inputs)
                    expected-outputs)
                   (t (er hard 'defsys
                          "The function ~x0 expects ~x1 inputs but is ~
                            supplied ~x2 inputs in the annotated expression ~
                            ~x3."
                          fn expected-inputs actual-inputs expr))))))))))
 (defun chk-input-output-arity-lst (expr-lst amodules)
   (cond ((endp expr-lst) 0)
         (t (+ (chk-input-output-arity (car expr-lst) amodules)
               (chk-input-output-arity-lst (cdr expr-lst) amodules))))))



; A module is a program name, fn, followed by a keyword alist containing, at
; most, the keys

; :formals -- list of formal parameters
; :dcls -- nil or a DECLARE form to admit recursive fns
; :input -- hypotheses about the formals (essentially a guard)
; :output -- logical expression equal to the value left on the stack [see note]
; :output-arity -- a natp constant, e.g., 1 or 3
; :code -- source code from which we obtain M1 code by compilation

; Note: If :output-arity is not specified and :output begins with MV,
; :output-arity defaults to the number elements described by :output.  Things
; should work when :output is an MV expression and :output-arity is omitted.
; But if :output is some other expression, e.g., (my-algorithm x y), then you
; have to tell defsys how many results are laid down by the code.  Of course,
; there can be all sorts of discrepancies ... :output may describe 2 values,
; :output-arity may specify 3, and the code may sometimes produce 2, 3, or 4!
; But to verify, they'd all better agree.  This system cannot handle varying
; output arities because the restore-regs code has to know how many values to
; save.

(defun annotate-module (module id)
  (let ((legal-keys '(:formals :dcls :input :output
                               :output-arity :code
                               :ghost-formals
                               :ghost-base-test :ghost-base-value
                               :ghost-decr)))
    (cond
     ((and (consp module)
           (symbolp (car module))
           (acl2::keyword-value-listp (cdr module))
           (acl2::subsetp (acl2::evens (cdr module)) legal-keys))
      (let* ((fn (car module))
             (expr (cadr (assoc-keyword :code (cdr module))))
             (output-arity
              (if (assoc-keyword :output-arity (cdr module))
                  (cadr (assoc-keyword :output-arity (cdr module)))
                  (if (and (consp (cadr (assoc-keyword :output (cdr module))))
                           (or (eq (car (cadr (assoc-keyword :output (cdr module))))
                                   'MV)
                               (eq (car (cadr (assoc-keyword :output (cdr module))))
                                   'acl2::MV)))
                      (len (cdr (cadr (assoc-keyword :output (cdr module)))))
                      1))))
        (cond
         ((member 's (cadr (assoc-keyword :formals (cdr module))))
          (er hard 'defsys
              "It is illegal for a module like ~x0 to use S as a formal ~
               parameter because that variable name is used in certain of our ~
               proof-support functions."
              fn))
         ((not (recursions-okp :tail fn expr))
          (er hard 'defsys
              "We only support tail-recursion and the module defining ~x0 is ~
               not tail-recursive."
              fn))
         ((not (assoc-keyword :formals (cdr module)))
          (er hard 'defsys
              "You did not provide :FORMALS for ~x0."
              fn))
         ((not (assoc-keyword :code (cdr module)))
          (er hard 'defsys
              "You did not provide :CODE for ~x0."
              fn))
         ((not (natp output-arity))
          (er hard 'defsys
              "When an :output-arity is supplied it must be a natural number ~
               and the :output-arity for ~x0 is not."
              fn))
         ((and (> output-arity 1)
               (not (equal (cadr (assoc-keyword :input (cdr module))) t))
               (not (and
                     (consp (cadr (assoc-keyword :ghost-base-value (cdr module))))
                     (or (equal (car (cadr (assoc-keyword :ghost-base-value (cdr module))))
                                'mv)
                         (equal (car (cadr (assoc-keyword :ghost-base-value (cdr module))))
                                'acl2::mv))
                     (equal (len (cdr (cadr (assoc-keyword :ghost-base-value (cdr module)))))
                            output-arity))))
          (er hard 'defsys
              "When the :output-arity is greater than 1 you must supply a ~
               :ghost-base-value, which must be an MV form of the appropriate ~
               arity.  These rules are violated for ~x0 where the ~
               :output-arity is ~x1 but :ghost-base-value is ~x2."
              fn output-arity (cadr (assoc-keyword :ghost-base-value (cdr module)))))
         ((and (or (assoc-keyword :ghost-base-test (cdr module))
                   (assoc-keyword :ghost-decr (cdr module)))
               (not (assoc-keyword :ghost-formals (cdr module))))
          (er hard 'defsys
              "When you supply either a :ghost-base-test or a :ghost-decr, ~
               you must supply :ghost-formals but you did not in ~x0."
              fn))
         ((and (or (assoc-keyword :ghost-base-test (cdr module))
                   (assoc-keyword :ghost-decr (cdr module)))
               (not (and (assoc-keyword :ghost-base-test (cdr module))
                         (assoc-keyword :ghost-base-value (cdr module))
                         (assoc-keyword :ghost-decr (cdr module)))))
          (er hard 'defsys
              "When you supply either a :ghost-base-test or
               or a :ghost-decr, you must supply both of them and a ~
               :ghost-base-value as well.  You did not in ~x0."
              fn))

         ((and (and (assoc-keyword :ghost-formals (cdr module))
                    (assoc-keyword :ghost-base-value (cdr module)))
               (not (and (or (equal (car (cadr (assoc-keyword :ghost-base-value (cdr module)))) 'mv)
                             (equal (car (cadr (assoc-keyword :ghost-base-value (cdr module)))) 'acl2::mv))
                         (equal 0 (cadr (cadr (assoc-keyword :ghost-base-value (cdr module))))))))
          (er hard 'defsys
              "When :ghost-formals and a :ghost-base-value are supplied, the ~
               :ghost-base-value must be an MV form with first result 0 but ~
               in ~x0 the form is ~x1."
              fn
              (cadr (assoc-keyword :ghost-base-value (cdr module)))))
         (t
          (list (car module)
                :formals (cadr (assoc-keyword :formals (cdr module)))
                :dcls (cadr (assoc-keyword :dcls (cdr module)))
                :input (or (cadr (assoc-keyword :input (cdr module))) t)
                :output (or (cadr (assoc-keyword :output (cdr module)))
                            :NONE)
                :output-arity output-arity
                :code (annotate-expr expr id)
                :ghost-formals (cadr (assoc-keyword :ghost-formals (cdr module)))
                :ghost-base-test (cadr (assoc-keyword :ghost-base-test (cdr module)))
                :ghost-base-value (cadr (assoc-keyword :ghost-base-value (cdr module)))
                :ghost-decr (cadr (assoc-keyword :ghost-decr (cdr module))))))))
     (t (er hard 'defsys
            "Bad DEFSYS syntax for module ~x0.  Each element must be of the form (symbol ~
             :key1 val1 ... :keyn valn) where the only legal :keyi are ~&1."
            (car module)
            legal-keys)))))


(defun annotate-modules (modules i id ans max-a-regs)
  (cond ((endp modules)
         (mv (rev1 ans nil) max-a-regs))
        (t (let* ((amod (annotate-module (car modules) (cons i id)))
                  (ans1 (cons amod ans)))
             (acl2::prog2$
              (chk-input-output-arity
               (cadr (assoc-keyword :code (cdr amod)))
               ans1)
              (annotate-modules (cdr modules) (+ 1 i) id
                                ans1
                                (max max-a-regs
                                     (max (len (cadr (assoc-keyword :formals (cdr amod))))
                                          (cadr (assoc-keyword :output-arity (cdr amod)))))))))))

(mutual-recursion
 (defun compile-expr (fn loop vars expr max-a-regs)

; expr is an annotated code expression: every fn call is of the form (fn id a1
; ... an) instead of (fn a1 ... an).  By the way: this compiler handles
; recursions just fine, including ``sometimes tail-recursive'' functions like
; mc-flatten with some tail-recursive calls and some full-blown recursive
; calls.  However, the clock compiler doesn't handle sometimes tail-recursive
; functions properly.

   (cond ((atom expr)
          (cond ((symbolp expr)
                 `((ILOAD ,(nv fn expr vars))))
                (t `((ICONST ,expr)))))
         ((eq (car expr) 'quote)
          `((ICONST ,(cadr expr))))
         ((member (car expr) '(+ - *))
          `(,@(compile-expr nil nil vars (nth 2 expr) max-a-regs)
            ,@(compile-expr nil nil vars (nth 3 expr) max-a-regs)
            ,(case (car expr)
               (+ '(IADD))
               (- '(ISUB))
               (otherwise '(IMUL)))))
         ((eq (car expr) 'MV)
          (compile-expr-lst nil loop vars (cdr (cdr expr)) max-a-regs))
         ((eq (car expr) 'IF)
          (er hard 'compile-expr
              "The compiler does not support IF.  Use IFEQ."))
         ((eq (car expr) 'IFEQ)
          (let ((a (nth 2 expr))
                (b (nth 3 expr))
                (c (nth 4 expr)))
            (let* ((test (compile-expr nil nil vars a max-a-regs))
                   (then (compile-expr fn loop vars b max-a-regs))
                   (else (compile-expr fn loop vars c max-a-regs))
                   (last-else-inst (car (last else))))
              (if (and (consp last-else-inst)
                       (eq (car last-else-inst) 'GOTO))
                  `(,@test
                    (IFEQ ,(+ (icount else) 1))
                    ,@else
                    ,@then)
                  `(,@test
                    (IFEQ ,(+ (icount else) 2))
                    ,@else
                    (GOTO ,(+ (icount then) 1))
                    ,@then)))))
         (t (append
             (compile-expr-lst nil loop vars (cdr (cdr expr)) max-a-regs)
             (if (eq (car expr) fn)
                 (append (ISTORE-series 0 (len vars))
                         `((GOTO ,loop)))
                 `((CALL ,(car expr) ,(cadr expr))))))))

 (defun compile-expr-lst (fn loop vars expr-lst max-a-regs)
   (declare (xargs :mode :program))
   (cond ((endp expr-lst) nil)
         (t (append (compile-expr fn loop vars (car expr-lst) max-a-regs)
                    (compile-expr-lst fn loop vars (cdr expr-lst) max-a-regs))))))

(defun compile-module (module max-a-regs)
  (let* ((fn (car module))
         (vars (cadr (assoc-keyword :formals (cdr module))))
         (n (len vars))
         (body (cadr (assoc-keyword :code (cdr module))))
         (fn-loop (pack (list fn "-LOOP")))
         (fn-exit (pack (list fn "-EXIT"))))
    `(,fn
      ,@(save-regs n max-a-regs)
      ,fn-loop
      ,@(compile-expr fn fn-loop vars body max-a-regs)
      ,fn-exit
      ,@(restore-regs (cadr (assoc-keyword :output-arity (cdr module)))
                      n max-a-regs)
      (RET ,fn))))

(defun algorithm-name (fn)
  (pack (list '! fn)))

(defun nth-series (n base max)
  (cond ((>= n max) nil)
        (t (cons `(nth ,n ,base)
                 (nth-series (+ 1 n) base max)))))

(defun mv-nth-series (n base max)
  (cond ((>= n max) nil)
        (t (cons `(mv-nth ,n (mv-list ,max ,base))
                 (mv-nth-series (+ 1 n) base max)))))

(mutual-recursion
 (defun algorithm-expr (fn expr amodule-lst)

; Expr is an annotated expression and we strip the annotations out as we also
; change the names of all the non-primitives from names such as FLOOR and MOD
; to !FLOOR and !MOD, and convert the IFEQs to IFs.  Fn is either nil or a
; function name.  When non-nil, fn is the name of a function we are defining
; and expr was (originally) its body.  In the case that fn is non-nil and has
; ghostly attributes, we put them into calls of fn.  Note that we don't know
; how to make sense of calls of functions with ghostly attributes except at the
; very top-level.  If, for example, foo has a ghost formal k and foo is called
; in bar, which has no ghost formal, then what do we use for the x argument in
; the call of foo from bar?  We simply return an ill-formed term in which foo
; is called with an insufficient nubmer of arguments.

   (cond ((atom expr) expr)
         ((eq (car expr) 'IFEQ)
          `(IF (EQUAL ,(algorithm-expr fn (nth 2 expr) amodule-lst)
                      0)
               ,(algorithm-expr fn (nth 3 expr) amodule-lst)
               ,(algorithm-expr fn (nth 4 expr) amodule-lst)))
         (t
          (let ((ghost-formals
                 (cadr
                  (assoc-keyword :ghost-formals
                                 (cdr (assoc-equal (car expr)
                                                   amodule-lst)))))
                (ghost-decr
                 (if (equal (car expr) fn) ; if fn is nil this fails
                     (cadr
                      (assoc-keyword :ghost-decr
                                     (cdr (assoc-equal fn
                                                       amodule-lst))))
                     nil))
                (!fn (if (member (car expr) '(+ - * mv acl2::mv))
                         (car expr)
                         (algorithm-name (car expr))))
                (args (algorithm-expr-lst fn (cdr (cdr  expr)) amodule-lst)))
            (cons !fn
                  (cond
                   ((and (eq (car expr) fn) ghost-decr)
                    (append args ghost-decr))
                   (ghost-formals
                    (append args ghost-formals))
                   (t args)))))))

 (defun algorithm-expr-lst (fn expr-lst amodule-lst)
   (cond
    ((endp expr-lst) nil)
    (t (let* ((x (car expr-lst))
              (arg (algorithm-expr fn x amodule-lst))
              (output-arity
               (cond ((and (consp x)
                           (not (eq (car x) 'quote))
                           (assoc-equal (car x) amodule-lst))
                      (cadr (assoc-keyword :output-arity
                                           (cdr (assoc-equal (car x)
                                                             amodule-lst)))))
                     (t 1)))
              (rest (algorithm-expr-lst fn (cdr expr-lst) amodule-lst)))
         (cond
          ((equal output-arity 1)
           (cons arg rest))
          (t (append (mv-nth-series 0 arg output-arity) rest))))))))

(defun add-return-labels (code i rcode id-to-label-table)

; Every CALL must be followed by a label.  In addition, every call is currently
; annotated with a unique id that associates it with the corresponding function
; call in the original high-level expression.  We add a unique label after each
; CALL and we build a table associating the unique ids of each call to the
; label generated.  We do all this in a second pass, rather than as part of
; compilation, because it is easier to guarantee that all the labels are
; distinct.

  (cond ((endp code)
         (mv (rev1 rcode nil)
                   id-to-label-table))
        ((and (consp (car code))
              (eq (op-code (car code)) 'CALL))
         (let ((id (nth 2 (car code)))
               (label (pack (list 'ret-pc- i '-from-call- (arg1 (car code))))))
           (add-return-labels (cdr code)
                              (+ 1 i)
                              (rev1 `(,(car code)
                                      ,label)
                                    rcode)
                              (cons (cons id label) id-to-label-table))))
        (t (add-return-labels (cdr code)
                              i
                              (cons (car code) rcode)
                              id-to-label-table))))

(defun compile-module-lst (lst rcode max-a-regs)
  (cond ((endp lst)
         (add-return-labels (rev1 rcode '(NON-TERMINATING
                                          (GOTO NON-TERMINATING)
                                          ILLEGAL-FINAL-PC
                                          (GOTO ILLEGAL-FINAL-PC)))
                            0
                            nil
                            nil))
        (t (compile-module-lst (cdr lst)
                               (rev1 (compile-module (car lst) max-a-regs)
                                     rcode)
                               max-a-regs))))


(defun compile-system (top-level-code module-lst max-a-regs)
; module-lst is annotated.
  (compile-module-lst module-lst
                      (rev1 top-level-code nil)
                      max-a-regs))

(defun expand-CALL (inst ret-label rcode)
  (rev1 `((ICONST ,ret-label)
          (GOTO ,(arg1 inst)))
        rcode))

(defun expand-ret-lst (targets rcode max-a-regs)
  (cond ((endp targets)
         (rev1 '((GOTO NON-TERMINATING))
               rcode))
        ((endp (cdr targets))
         (rev1 `((GOTO ,(car targets)))
               rcode))
        (t (expand-ret-lst
            (cdr targets)
            (rev1 `((ILOAD ,(* 2 max-a-regs))
                    (ICONST ,(car targets))
                    (ISUB)
                    (IFEQ ,(car targets)))
                  rcode)
            max-a-regs))))

(defun expand-RET (inst alist rcode max-a-regs)
  (expand-ret-lst (cdr (assoc (arg1 inst) alist))
                  rcode
                  max-a-regs))

; The alist below maps subrs to the return labels from all their callers.

(defun assemble (code alist rcode max-a-regs)
  (cond ((endp code)
         (rev1 rcode nil))
        ((atom (car code))
         (assemble (cdr code)
                   alist
                   (cons (car code) rcode)
                   max-a-regs))
        ((eq (op-code (car code)) 'CALL)
         (assemble (cdr code)
                   alist
                   (expand-CALL (car code) (cadr code) rcode)
                   max-a-regs))
        ((eq (op-code (car code)) 'RET)
         (assemble (cdr code)
                   alist
                   (expand-RET (car code) alist rcode max-a-regs)
                   max-a-regs))
        (t (assemble (cdr code)
                     alist
                     (cons (car code) rcode)
                     max-a-regs))))

(defun label-table (code pc alist)
  (cond ((endp code) alist)
        ((atom (car code))
         (label-table (cdr code)
                      pc
                      (cons (cons (car code) pc) alist)))
        (t (label-table (cdr code)
                        (+ 1 pc)
                        alist))))

(defun assoc-or-report (instr tablename key alist)
  (let ((ans (assoc key alist)))
    (if ans
        ans
        (er hard 'link
            "While linking the instruction ~x0 no entry was found in ~x1 for ~x2.  The ~
             value of ~x1 is ~X34."
            instr tablename key alist nil))))

(defun link (code pc label-table rcode)
  (cond ((endp code)
         (rev1 rcode nil))
        ((atom (car code))
         (link (cdr code) pc label-table rcode))
        ((eq (op-code (car code)) 'ICONST)
; We permit an ICONST instruction to use a label as data and replace the
; label by the corresponding pc.

         (link (cdr code)
                (+ 1 pc)
                label-table
                (cons (if (integerp (arg1 (car code)))
                          (car code)
                          (list 'ICONST
                                (cdr (assoc-or-report (car code)
                                                      'label-table
                                                      (arg1 (car code))
                                                      label-table))))
                      rcode)))
        ((member (op-code (car code)) '(GOTO IFEQ))

; We permit GOTO and IFEQ to use label names and replace them with the correct
; relative jump distances.  However, if the arg given is a number, we leave it
; in place.

         (link (cdr code)
                (+ 1 pc)
                label-table
                (cons (if (integerp (arg1 (car code)))
                          (car code)
                          (list (op-code (car code))
                                (- (cdr (assoc-or-report (car code)
                                                         'label-table
                                                         (arg1 (car code))
                                                         label-table))
                                   pc)))
                      rcode)))
        ((member (op-code (car code)) '(ILOAD ISTORE IADD ISUB IMUL HALT))

; All other M1 instructions are left as-is.

         (link (cdr code)
                (+ 1 pc)
                label-table
                (cons (car code) rcode)))
        (t (er hard 'link
               "Unrecognized instruction or pseudo-instruction, ~x0."
               (car code)))))

(defun defconst-lst (alist)
  (cond ((endp alist) nil)
        (t (cons `(defconst ,(pack (list '* (caar alist) '*))
                    ,(cdr (car alist)))
                 (defconst-lst (cdr alist))))))

(defun switch-table (code alist)
  (cond ((endp code) alist)
        ((and (consp (car code))
              (eq (op-code (car code)) 'CALL))
         (let* ((subr (arg1 (car code)))
                (ret-label (cadr code))
                (temp (assoc subr alist))
                (new-targets (add-to-set-equal ret-label (cdr temp))))
           (switch-table (cdr code)
                         (put-assoc-equal subr new-targets alist))))
        (t (switch-table (cdr code) alist))))

; Now we develop a compiler for clock functions.  The worst aspect of this
; process is a hack I call the :STOP hack.  Recall that the then branch of an
; IF is generally followed by a GOTO that skips over the else branch.  So the
; clock for a then branch is generated by getting the clock for the code
; and adding one TICK after it.  But this tick is not added if the last
; instruction in the then branch is a GOTO.  However, now consider the code for
; (if a (if b c d) e) and suppose c is a tail-recursive call compiled to a
; GOTO.  Then the clock for c is correctly handled (no extra TICK) but the
; clock for (if b c d) is not because we would add a TICK -- but that TICK
; is not needed on every path through the code, just some paths.  We handle
; this by putting the keyword :STOP into the clock when we see a
; tail-recursive GOTO.  Then, we generate clocks like (clk+ (clk+
; 11 (clk+ (foo-clock x) :STOP)) 1) like: (clk+ 11
; (clk+ (foo-clock x) (clk+ :STOP 1))) which we just truncate at the
; :STOP.  Thus, the extra TICK is added only on those branches not ending in a
; tail-recursive GOTO.  But to make this work we have to normalize ifs and
; associate the clk+s.

(defun normalize-clk+-ifs (x)
  (cond ((atom x) x)
        ((eq (car x) 'quote) x)
        ((eq (car x) 'IF)
         `(IF ,(nth 1 x)
              ,(normalize-clk+-ifs (nth 2 x))
              ,(normalize-clk+-ifs (nth 3 x))))
        ((eq (car x) 'clk+)
         (let ((x1 (normalize-clk+-ifs (nth 1 x)))
               (x2 (normalize-clk+-ifs (nth 2 x))))
           (cond
            ((and (consp x1)
                  (eq (car x1) 'IF))
             `(IF ,(nth 1 x1)
                  ,(normalize-clk+-ifs `(clk+ ,(nth 2 x1) ,x2))
                  ,(normalize-clk+-ifs `(clk+ ,(nth 3 x1) ,x2))))
            ((and (consp x2)
                  (eq (car x2) 'IF))
             `(IF ,(nth 1 x2)
                  ,(normalize-clk+-ifs `(clk+ ,x1 ,(nth 2 x2)))
                  ,(normalize-clk+-ifs `(clk+ ,x1 ,(nth 3 x2)))))
            (t `(clk+ ,x1 ,x2)))))
        (t x)))

(defun flatten-clk+-expr (x)
  (cond ((and (consp x)
              (eq (car x) 'clk+))
         (append (flatten-clk+-expr (nth 1 x))
                 (flatten-clk+-expr (nth 2 x))))
        (t (list x))))

(defun truncate-to-stop (x)
  (cond ((endp x) nil)
        ((eq (car x) :STOP) nil)
        (t (cons (car x) (truncate-to-stop (cdr x))))))

(defun combine-adjacent-natp-clocks (lst)
  (cond ((endp lst) nil)
        ((endp (cdr lst)) lst)
        (t (let ((x1 (car lst))
                 (lst1 (combine-adjacent-natp-clocks (cdr lst))))
             (cond
              ((and (natp x1)
                    (natp (car lst1)))
               (cons (+ x1 (car lst1))
                     (cdr lst1)))
              (t (cons x1 lst1)))))))

(defun make-clk+-nest (lst)
  (if (endp lst)
      0
      (if (endp (cdr lst))
          (car lst)
          `(clk+ ,(car lst)
                 ,(make-clk+-nest (cdr lst))))))

(defun associate-clk+s (x)
  (cond ((atom x) x)
        ((eq (car x) 'quote) x)
        ((eq (car x) 'clk+)
         (make-clk+-nest
          (combine-adjacent-natp-clocks
           (truncate-to-stop (flatten-clk+-expr x)))))
        ((eq (car x) 'if)
         `(if ,(nth 1 x)
              ,(associate-clk+s (nth 2 x))
              ,(associate-clk+s (nth 3 x))))
        (t x)))

(defun combine-clocks (lst1 lst2)

; Each of the args is a list of clock expressions that will ultimately be
; combined.  For example, lst1 might be '((foo-clock x) 5) and lst2 might be
; '(3).  We ``concatentate'', combining explicit clocks (if any) on the last
; element of lst1 and first of lst2.  So we combine the two examples above to
; '((foo-clock x) 8).  Eventually we'll build a right-associated clk+ nest from
; this list.

  (let ((x1 (car (last lst1)))
        (x2 (car lst2)))
    (cond
     ((and (natp x1)
           (natp x2))
      (append (all-but-last lst1)
              (cons (+ x1 x2)
                    (cdr lst2))))
     (t (append lst1 lst2)))))

(mutual-recursion
 (defun compile-clock-expr (fn loop vars expr amodule-lst)
; Expr is an annotated expression.
   (cond ((atom expr)
          '(1))   ; ILOAD or ICONST
         ((eq (car expr) 'quote)
          '(1))   ; ICONST
         ((member (car expr) '(+ - *))
          (combine-clocks
           (compile-clock-expr nil nil vars (nth 2 expr) amodule-lst)
           (combine-clocks
            (compile-clock-expr nil nil vars (nth 3 expr) amodule-lst)
            '(1)))) ; IADD, ISUB, IMUL
         ((eq (car expr) 'MV)
          (compile-clock-expr-lst nil loop vars (cdr (cdr expr)) amodule-lst))
         ((eq (car expr) 'IF)
          (er hard 'compile-clock-expr
              "The clock compiler does not support IF.  Use IFEQ."))
         ((eq (car expr) 'IFEQ)
          (let ((a (nth 2 expr))
                (b (nth 3 expr))
                (c (nth 4 expr)))
            (let* ((test-clock (compile-clock-expr nil nil vars a amodule-lst))
                   (then-clock (compile-clock-expr fn loop vars b amodule-lst))
                   (else-clock (compile-clock-expr fn loop vars c amodule-lst)))

; I have debated whether the first arg to algorithm-expr below should be fn or
; nil.  I will supply nil and that means that we won't supply ghost args if we
; see a call of fn.  But I don't expect a call of fn in the test of a tail
; recursive definition of fn!

              `((IF (EQUAL ,(algorithm-expr nil a amodule-lst) 0)
                    ,(make-clk+-nest
                      (combine-clocks
                       test-clock
                       (combine-clocks
                        '(1) ; IFEQ
                        then-clock)))
                    ,(make-clk+-nest
                      (combine-clocks
                       test-clock
                       (combine-clocks
                        '(1) ; IFEQ
                        (if (and (consp c)
                                 (eq (car c) fn))
                            else-clock
                            (combine-clocks
                             else-clock
                             '(1)))))))))))  ; (GOTO skip-around-then)
         (t (combine-clocks
             (compile-clock-expr-lst nil loop vars (cdr (cdr expr)) amodule-lst)
             (cond
              ((eq (car expr) fn)
               `(,(+ 1 (len (ISTORE-series 0 (len vars))))
                 (,(pack (list loop '-CLOCK))
                  ,@(algorithm-expr-lst nil (cdr (cdr expr)) amodule-lst)
                  ,@(cadr (assoc-keyword :ghost-decr
                                         (cdr (assoc-equal fn amodule-lst)))))
; Note the :STOP hack marker, indicating that the preceding is a tail-recursive jump.
; This prevents any subsequent clock from being appended to this branch.
                 :STOP))
              (t
               `(2
                 (,(pack (list (car expr) '-CLOCK))
                  ',(cadr expr) ; id
                  ,@(algorithm-expr-lst fn (cdr (cdr expr)) amodule-lst)
                  ,@(cadr (assoc-keyword :ghost-formals
                                         (cdr (assoc-equal (car expr) amodule-lst))))))))))))

 (defun compile-clock-expr-lst (fn loop vars expr-lst amodule-lst)
   (declare (xargs :mode :program))
   (cond ((endp expr-lst) nil)
         (t (combine-clocks
             (compile-clock-expr fn loop vars (car expr-lst) amodule-lst)
             (compile-clock-expr-lst fn loop vars (cdr expr-lst) amodule-lst))))))

; Now we develop the code to extract from a recursive clock function the
; part of the clock that drives the code once around the loop.

(mutual-recursion
 (defun calledp (fn x)
   (cond ((atom x) nil)
         ((eq (car x) 'quote) nil)
         ((eq fn (car x)) t)
         (t (calledp-lst fn (cdr x)))))
 (defun calledp-lst (fn lst)
   (cond ((endp lst) nil)
         (t (or (calledp fn (car lst))
                (calledp-lst fn (cdr lst)))))))


(defun generate-induction-hint-expr (fn hfn vars expr a)

; Fn is the name of a recursive clock function, like FACT-LOOP-CLOCK, and
; expr is its body.  We dive through expr and gut it, replacing all base-case
; exits by (list ,@vars s) and all clk+ nests containing calls of fn, e.g., (clk+ a
; (clk+ b (clk+ c (fn ...)))) by (hfn ... (m1 s (clk+ a (clk+ b c)))).  We assume (and
; check later) that every call of fn is the last argument of some clk+ nest
; output.  We check that by only looking for and replacing such calls and then
; finally confirm that the result has no calls of fn.

  (cond ((atom expr) `(list ,@vars s))
        ((eq (car expr) 'quote) `(list ,@vars s))
        ((eq (car expr) 'IF)
         `(IF ,(nth 1 expr)
              ,(generate-induction-hint-expr fn hfn vars (nth 2 expr) a)
              ,(generate-induction-hint-expr fn hfn vars (nth 3 expr) a)))
        ((eq (car expr) fn)
         `(,hfn ,@(cdr expr) ,(if a
                                  `(m1 s ,(make-clk+-nest (rev1 a nil)))
                                  's)))
        ((eq (car expr) 'clk+)
         (generate-induction-hint-expr fn hfn vars (nth 2 expr)
                                       (cons (nth 1 expr) a)))
        ((calledp fn expr)
         (er hard 'defsys
             "It was thought impossible for a clock function, specifically ~
              ~x0, to be called recursively in its body except as the deepest ~
              argument of CLK+ nests in output branches of top-level IFs, but ~
              it is called in ~x1."
             fn expr))
        (t `(list ,@vars s))))

(defun make-push-nest (lst stack)
  (cond ((endp lst) stack)
        (t (make-push-nest (cdr lst) `(push ,(car lst) ,stack)))))


(defun make-acl2-body (ghost-base-test ghost-base-value hyps body)
  (let ((body1 (if (eq hyps t)
                   body
                   `(if ,hyps ,body ,ghost-base-value))))
    (if ghost-base-test
        `(if ,ghost-base-test
             ,ghost-base-value
             ,body1)
        body1)))

; The following function generates two or three functions depending on whether
; the module is iterative.  If it has a loop in it, we generate three
; functions: the loop clock, the top-level clock (including entry and
; exit costs), and the induction hint.  If it does not have a loop, we just
; generate the ``loop'' clock (even though it is not a loop, it is the core
; of the module) and the top-level clock.

(defun repeat (e n)
  (if (zp n)
      nil
      (cons e (repeat e (- n 1)))))

(defun defun-clock-and-hint-fns (module max-a-regs amodule-lst)
  (let* ((fn (car module))
         (loop (pack (list fn '-loop)))
         (vars (cadr (assoc-keyword :formals (cdr module))))
         (ghost-formals (cadr (assoc-keyword :ghost-formals (cdr module))))
         (vars-and-ghosts (append vars ghost-formals))
         (ghost-base-test (cadr (assoc-keyword :ghost-base-test (cdr module))))
         (dcls (cadr (assoc-keyword :dcls (cdr module))))
         (hyps (cadr (assoc-keyword :input (cdr module))))
         (output-arity (cadr (assoc-keyword :output-arity (cdr module))))
         (expr (cadr (assoc-keyword :code (cdr module))))
         (loop-clock-list (compile-clock-expr fn loop vars expr amodule-lst))
         (loop-clock (pack (list loop '-clock)))
         (loop-clock-body
          (associate-clk+s
           (normalize-clk+-ifs
            (make-clk+-nest loop-clock-list))))
         (clock (pack (list fn '-clock)))
         (clock-body (if ghost-formals
                         `(if (equal (mv-nth 0 (mv-list ,output-arity
                                                        (,(algorithm-name fn) ,@vars-and-ghosts)))
                                     0)
                              (clk+ ,(len (save-regs (len vars) max-a-regs))
                                    (,loop-clock ,@vars-and-ghosts))
                              (clk+ ,(len (save-regs (len vars) max-a-regs))
                                    (clk+ (,loop-clock ,@vars-and-ghosts)
                                          (clk+ ,(len (restore-regs output-arity
                                                                    (len vars)
                                                                    max-a-regs))
                                                (exit-clock ',fn ret-pc)))))
                         `(clk+ ,(len (save-regs (len vars) max-a-regs))
                                (clk+ (,loop-clock ,@vars-and-ghosts)
                                      (clk+ ,(len (restore-regs output-arity
                                                                (len vars)
                                                                max-a-regs))
                                            (exit-clock ',fn ret-pc))))))
         (hint (pack (list loop '-induction-hint)))
         (hint-body (if (calledp loop-clock loop-clock-body)
                        (generate-induction-hint-expr loop-clock hint vars loop-clock-body nil)
                        :NON-RECURSIVE)))
    (cond ((and (not (eq hint-body :NON-RECURSIVE))
                (calledp loop-clock hint-body))
           (er hard 'defsys
               "In the process of defining the hint function ~x0 we gutted ~
                the body of the corresponding clock function, ~x1, and ~
                replaced all the recursive calls at the end of output CLK+ ~
                nests by recursive calls of the ~x0.  But the original ~
                clock function name, ~x0, still occurs in the purported ~
                induction hint function body, ~x1, contrary to what we ~
                thought was possible!"
               hint fn hint-body))
          (t
           `(
             (defun ,loop-clock ,vars-and-ghosts
               ,@dcls
; Clock fns return nil on forced termination, so I ignore ghost-base-value below.
               ,(make-acl2-body ghost-base-test 0 hyps loop-clock-body))
             (defun ,clock (ret-pc ,@vars-and-ghosts)
               ,clock-body)

             ,@(if (eq fn 'MAIN)
                   `((defun m1-psi (,@vars-and-ghosts)
                       (m1 (make-state 0
                                       ',(repeat 0 (+ (* 2 max-a-regs) 1))
                                       ,(make-push-nest vars nil)
                                       (psi))
                           (clk+ 2
                                 (main-clock nil ,@vars-and-ghosts)))))
                   nil)

             ,@(cond ((not (eq hint-body :NON-RECURSIVE))
                      `((defun ,hint (,@vars-and-ghosts s)
                          ,@dcls
; Hint functions return nil on forced termination, so I ignore ghost-base-value below.
                          ,(make-acl2-body ghost-base-test nil hyps hint-body))))
                     (t nil)))))))

(defun defun-algorithm (module amodule-lst)
  (let* ((fn (car module))
         (ghost-formals (cadr (assoc-keyword :ghost-formals (cdr module))))
         (ghost-base-test (cadr (assoc-keyword :ghost-base-test (cdr module))))
         (ghost-base-value (cadr (assoc-keyword :ghost-base-value (cdr module))))
         (vars-and-ghosts
          (append (cadr (assoc-keyword :formals (cdr module)))
                  ghost-formals))
         (dcls (cadr (assoc-keyword :dcls (cdr module))))
         (hyps (cadr (assoc-keyword :input (cdr module))))
         (body (cadr (assoc-keyword :code (cdr module))))
         (!fn (algorithm-name fn))
         (!body (algorithm-expr fn body amodule-lst)))
    (mv `(defun ,!fn ,vars-and-ghosts ,@dcls
           ,(make-acl2-body ghost-base-test ghost-base-value hyps !body))
        (calledp !fn !body))))

(defun make-equal-var-top-pop-stack (vars stack)
  (cond ((endp vars) nil)
        (t (cons `(equal ,(car vars) (top ,stack))
                 (make-equal-var-top-pop-stack (cdr vars) `(pop ,stack))))))

(defun nth-i-locals-lst (n max-a-regs)
  (nth-series n '(locals s) max-a-regs))

(defun push-lst (nthfn n expr stack)
  (cond ((zp n) stack)
        (t `(push (,nthfn ,(- n 1) ,expr)
                  ,(push-lst nthfn (- n 1) expr stack)))))

(mutual-recursion
 (defun ghost-calls (expr amodule-lst)

; We return the list of all modules with ghost formals that are called in expr.

   (cond ((atom expr) nil)
         ((eq (car expr) 'quote) nil)
         ((cadr (assoc-keyword :ghost-formals
                               (cdr (assoc-equal (car expr) amodule-lst))))
          (cons (car expr)
                (ghost-calls-lst (cddr expr) amodule-lst)))
         (t (ghost-calls-lst (cddr expr) amodule-lst))))
 (defun ghost-calls-lst (lst amodule-lst)
   (cond ((endp lst) nil)
         (t (append (ghost-calls (car lst) amodule-lst)
                    (ghost-calls-lst (cdr lst) amodule-lst))))))


(defun verification-events-for-module (module ans max-a-regs amodule-lst)
  (let* ((fn (car module))
         (vars (cadr (assoc-keyword :formals (cdr module))))
         (ghost-formals (cadr (assoc-keyword :ghost-formals (cdr module))))
         (vars-and-ghosts (append vars ghost-formals))
         (hyps (cadr (assoc-keyword :input (cdr module))))
         (rhs (cadr (assoc-keyword :output (cdr module))))
         (output-arity (cadr (assoc-keyword :output-arity (cdr module))))
         (expr (cadr (assoc-keyword :code (cdr module))))
         (ghost-calls (ghost-calls expr amodule-lst))
         (ghost-call (car ghost-calls)))

; If module contains a ghost call (a call to a module with ghost formals) then
; either the only ghost calls are to the module itself (i.e., this is the
; module introducing nontermination), or else the module should be MAIN, there
; is only one ghost call, and MAIN has the same ghost formals as the ghost
; calling module.

    (acl2::prog2$
     (if
      (or (not ghost-calls)
          (acl2::subsetp ghost-calls (list fn))
          (and (equal fn 'MAIN)
               (equal ghost-calls (list ghost-call))
               (equal
                (cadr
                 (assoc-keyword :ghost-formals (cdr module)))
                (cadr
                 (assoc-keyword :ghost-formals
                                (cdr (assoc-equal ghost-call
                                                  amodule-lst)))))))
      nil
      (acl2::cw
       "The module named ~x0 calls ~x1 and the called module has ghost ~
        formals.  (Presumably ~x1 does not necessarily terminate and thus ~
        thus ~x0 won't either.)  How are the ghost formals for ~x1 passed ~
        down to its clock function in the clock function for ~x0?  I ~
        have a really draconian convention:  I allow this only if the calling ~
        module is MAIN, the only ghostly call MAIN makes is to ~x1, and MAIN ~
        has identical ghost formals.  Under these circumstances I pass MAIN's ~
        ghosts down to ~x1.  However, these draconian restrictions are not ~
        met in this system.  I wasn't motivated to figure out what is really ~
        needed in such general cases as this.  I suspect this defsys will ~
        fail!  However, if you :TRANS1 it and replay the workable part to get ~
        to the first nonsensical event, perhaps you can see how to patch up ~
        the remaining events."
       fn ghost-call))
     (mv-let
      (alg-def recursivep)
      (defun-algorithm module amodule-lst)
      (rev1
       `(,alg-def

         ,@(defun-clock-and-hint-fns module max-a-regs amodule-lst)

         (defun ,(pack (list fn '-loop-final-locals)) (,@vars-and-ghosts s)
           (locals (m1 s (,(pack (list fn '-loop-clock)) ,@vars-and-ghosts))))

;         (defthm ,(pack (list 'true-listp- fn '-loop-final-locals))
;           (implies (acl2::true-listp (locals s))
;                    (acl2::true-listp (,(pack (list fn '-loop-final-locals)) ,@vars-and-ghosts s))))

         (defthm ,(pack (list 'len- fn '-loop-final-locals))
           (<= (len (locals s))
               (len (,(pack (list fn '-loop-final-locals)) ,@vars-and-ghosts s)))
           :rule-classes :linear)

         ,@(if (and (eq fn 'MAIN)
                    ghost-calls)

; Given our draconian restriction that MAIN is the only module that can call a
; module with ghost formals, we know that ghost-call is the name of the called
; module, that ghost-call's correctness theorem splits on whether ghost-call
; terminates and that in the event that it does not, m1 hangs at
; ghost-call's loop.  In this case, we handle MAIN differently than for normal
; always-terminating MAINs.  In particular, we splice in a definition for MAIN's
; final (still non-terminal) stack and then use it in the correcness results.

               `((defun main-loop-final-stack (,@vars-and-ghosts s)
                   (stack (m1 s (main-loop-clock ,@vars-and-ghosts)))))
               nil)

         (defthm ,(pack (list fn '-loop-is- (algorithm-name fn)))
           (implies
            (and (ready-at ,(pack (list '* fn '-loop*)) (list ,@vars) 0 s)
                 ,@(if (equal hyps t) nil (list hyps)))
            (equal
             (m1 s (,(pack (list fn '-loop-clock)) ,@vars-and-ghosts))
             ,(let ((terminal-state
                     `(make-state
                       ,(pack (list '* fn '-exit*))
                       ,(if (equal (len vars) max-a-regs)
                            `(,(pack (list fn '-loop-final-locals)) ,@vars-and-ghosts s)
                            `(update-nth* ,(len vars)
                                          (list ,@(nth-i-locals-lst (len vars) max-a-regs))
                                          (,(pack (list fn '-loop-final-locals))
                                           ,@vars-and-ghosts s)))
                       ,(if (equal output-arity 1)
                            `(push (,(algorithm-name fn) ,@vars-and-ghosts) (stack s))
                            (push-lst 'mv-nth
                                      output-arity
                                      `(,(algorithm-name fn) ,@vars-and-ghosts)
                                      '(stack s)))
                       (psi))))
                (if ghost-formals
                    (if (and (eq fn 'MAIN)
                             ghost-calls)

                        `(if (equal (mv-nth 0 (mv-list ,output-arity (!MAIN ,@vars-and-ghosts))) 0)

; Note that if MAIN hangs, it hangs at ghost-call's loop, not *MAIN-LOOP*.
; Note also that we disavow any knowledge of the stack at that point, although
; with some care we could reconstruct it: it is (stack s) with MAIN's locals
; and return pc popped off, then (len vars) of (LOCALS s) pushed, then the
; return pc pushed, then k locals of that state pushed, where k is the number
; of vars of ghost-calls, and then the return pc back to MAIN.  But I do not
; think we care about the stack of an infinitely looping state, since we'll
; never pop back into it.

                             (make-state ,(pack (list '* ghost-call '-loop*))
                                         (main-loop-final-locals ,@vars-and-ghosts s)
                                         (main-loop-final-stack ,@vars-and-ghosts s)
                                         (psi))
                             ,terminal-state)
                        `(if (equal (mv-nth 0 (mv-list ,output-arity
                                                       (,(algorithm-name fn) ,@vars-and-ghosts)))
                                    0)
                             (make-state ,(pack (list '* fn '-loop*))
                                         (,(pack (list fn '-loop-final-locals)) ,@vars-and-ghosts s)
                                         (stack s)
                                         (psi))
                             ,terminal-state))
                    terminal-state))))
           :hints (("Goal"
                    ,@(if recursivep
                          `(:induct (,(pack (list fn '-loop-induction-hint)) ,@vars-and-ghosts s))
                          `(:do-not-induct t)))))

         (in-theory (disable ,(pack (list fn '-loop-clock))
                             ,(pack (list fn '-loop-final-locals))
                             ,@(if (and (eq fn 'MAIN)
                                        ghost-calls)
                                   '(MAIN-LOOP-FINAL-STACK)
                                   nil)))

         (defun ,(pack (list fn '-final-locals)) (call-id ,@vars-and-ghosts s)
           (locals (m1 s (,(pack (list fn '-clock)) call-id ,@vars-and-ghosts))))

;         (defthm ,(pack (list 'true-listp- fn '-final-locals))
;           (implies (acl2::true-listp (locals s))
;                    (acl2::true-listp (,(pack (list fn '-final-locals)) call-id ,@vars-and-ghosts s))))

         (defthm ,(pack (list 'len- fn '-final-locals))
           (<= (len (locals s))
               (len (,(pack (list fn '-final-locals)) call-id ,@vars-and-ghosts s)))
           :rule-classes :linear)

; We do an analogous treatment for the top-level MAIN theorem if it has a ghost call in it.

         ,@(if (and (eq fn 'MAIN)
                    ghost-calls)
               `((defun main-final-stack (call-id ,@vars-and-ghosts s)
                   (stack (m1 s (main-clock call-id ,@vars-and-ghosts)))))
               nil)

; We force the READY-AT and the requirements on call-id.  The idea is that if
; the theorem fails to apply at a place where the fn code is clocked, it is
; because of elementary programming mistakes having to do with pushing the
; right arguments.

         (defthm ,(pack (list fn '-is- (algorithm-name fn)))
           (implies
            (and (acl2::force
                  (ready-at ,(pack (list '* fn '*))
                            (locals s)
                            ,(+ 1 (len vars))
                            s))
                 (acl2::force
                  (member (cdr (assoc call-id *id-to-label-table*))
                          (cdr (assoc ',fn *switch-table*))))
                 (acl2::force
                  (equal (top (stack s)) (final-pc ',fn call-id)))
                 ,@(make-equal-var-top-pop-stack (rev1 vars nil) '(pop (stack s)))
                 ,@(if (equal hyps t) nil `(,hyps)))
            (equal
             (m1 s (,(pack (list fn '-clock)) call-id ,@vars-and-ghosts))
             ,(let ((terminal-state
                     `(make-state (top (stack s))
                                  (update-nth* 0
                                               (list ,@(nth-i-locals-lst 0 max-a-regs))
                                               (,(pack (list fn '-final-locals))
                                                call-id ,@vars-and-ghosts s))
                                  ,(if (equal output-arity 1)
                                       `(push (,(algorithm-name fn) ,@vars-and-ghosts)
                                              (popn ,(+ 1 (len vars)) (stack s)))
                                       (push-lst 'mv-nth
                                                 output-arity
                                                 `(,(algorithm-name fn) ,@vars-and-ghosts)
                                                 `(popn ,(+ 1 (len vars)) (stack s))))
                                  (psi))))
                (if ghost-formals
                    (if (and (eq fn 'main)
                             ghost-calls)
                        `(if (equal (mv-nth 0 (mv-list ,output-arity
                                                       (!MAIN ,@vars-and-ghosts)))
                                    0)
                             (make-state ,(pack (list '* ghost-call '-loop*))
                                         (,(pack (list fn '-final-locals)) call-id ,@vars-and-ghosts s)
                                         (main-final-stack call-id ,@vars-and-ghosts s)
                                         (psi))
                             ,terminal-state)
                        `(if (equal (mv-nth 0 (mv-list ,output-arity
                                                       (,(algorithm-name fn) ,@vars-and-ghosts)))
                                    0)
                             (make-state ,(pack (list '* fn '-loop*))
                                         (,(pack (list fn '-final-locals)) call-id ,@vars-and-ghosts s)
                                         (push (final-pc ',fn call-id)
                                               ,(push-lst 'nth
                                                          (len vars)
                                                          '(locals s)
                                                          `(popn ,(+ 1 (len vars)) (stack s))))
                                         (psi))
                             ,terminal-state))
                    terminal-state))))

           :hints (("Goal" :do-not-induct t)))

         (in-theory (disable ,(pack (list fn '-clock))
                             ,(pack (list fn '-final-locals))
                             ,@(if (and (eq fn 'MAIN)
                                        ghost-calls)
                                   `(main-final-stack)
                                   nil)))

         ,@(if (eq rhs :NONE)
               nil
               `((defthm ,(pack (list (algorithm-name fn) '-spec))
                   ,(let ((concl `(equal (,(pack (list (algorithm-name fn))) ,@vars-and-ghosts)
                                         ,rhs)))
                      (if (equal hyps t)
                          concl
                          `(implies ,hyps ,concl)))))))
       ans)))))


(defun verification-events-for-modules (amod-lst ans max-a-regs amodule-lst)
; amod-lst is a tail of amodule-lst, the full list of annotated modules.
  (cond ((endp amod-lst) (rev1 ans nil))
        (t (verification-events-for-modules
            (cdr amod-lst)
            (verification-events-for-module (car amod-lst) ans max-a-regs amodule-lst)
            max-a-regs amodule-lst))))

; Before we execute the events created by defsys we give the user a chance to
; elaborate them.

; We develop a utility that allows us to edit a list of events ``off line.''
; The utility takes a list of events and a list of commands and carries out the
; commands.  We do not expand macros in the event list, nor do we look inside
; of encapsulates.  Each edit command is of the form (ev-type ev-name place x),
; where

; ev-type = DEFTHM, place = :before, :after, :hints, or :rule-classes
; ev-type = DEFUN, place =  :before, :after, or :xargs

; When place is :before or :after, x is assumed to be a list of events and is
; spliced in before or after the one identified.

; When place is :hints, :xargs, or :rule-classes, x is a legal value for that
; and replaces the value given (or is added as the value if none is present).

; Errors are caused if a command is not used.

#|
(edit-event-lst
 '((defun foo (x) (+ 1 x))
   (defun bar (x y) (declare (ignore x)) (declare (type integerp y)) (+ 1 y))
   (defun mum1 (x y) (declare (ignore x)) (declare (xargs :measure (m x))) (declare (type integerp y)) (+ 1 y))
   (defun mum2 (x y) (declare (ignore x) (xargs :measure (m x)) (type integerp y)) (+ 1 y))
   (defthm lem1 (equal rhs lhs))
   (defthm lem2 (equal rhs lhs) :rule-classes :rewrite)
   (defthm lem3 (equal rhs lhs) :rule-classes :rewrite :hints (("Goal" :do-not-induct t)))
   (defthm lem4 (equal rhs lhs) :hints (("Goal" :do-not-induct t))  :rule-classes :rewrite :otf-flg t))
 '((defthm lem1 :before (a b c))
   (defthm lem1 :before (d e f))
   (defthm lem3 :hints (("Goal" a b c)))
   (defthm lem1 :after (u v w))
   (defthm lem1 :after (x y z))
   (defun mum2 :xargs (u v w))
   ;(defun mum2 :guard-hints (a b c)) ; <--- illegal edit command
   ))
|#

(defun relevant-edit-commands (ev-type ev-name commands relevant-cmds leftover-cmds)

; We return (mv relevant-cmds leftover-cmds), where relevant-cmds are all the
; commands in commands that identify the event with the given type and name and
; leftover-commands are the other commands.

  (cond
   ((endp commands)
    (mv (rev1 relevant-cmds nil) (rev1 leftover-cmds nil)))
   ((and (eq ev-type (nth 0 (car commands)))
         (eq ev-name (nth 1 (car commands))))
    (relevant-edit-commands ev-type ev-name (cdr commands)
                            (cons (car commands) relevant-cmds)
                            leftover-cmds))
   (t
    (relevant-edit-commands ev-type ev-name (cdr commands)
                            relevant-cmds
                            (cons (car commands) leftover-cmds)))))

(defun replace-keyword-arg (key val lst)
  (cond ((endp lst)
         (list :key val))
        ((eq key (car lst))
         (list* key val (cdr (cdr lst))))
        (t (list* (car lst) (car (cdr lst))
                  (replace-keyword-arg key val (cdr (cdr lst)))))))

(defun edit-hints (event x)
  (let ((name (nth 1 event))
        (term (nth 2 event))
        (alist (cdr (cdr (cdr event)))))
    `(DEFTHM ,name ,term
       ,@(if (assoc-keyword :hints alist)
             (replace-keyword-arg :hints x alist)
             `(:hints ,x ,@alist)))))

(defun edit-rule-classes (event x)
  (let ((name (nth 1 event))
        (term (nth 2 event))
        (alist (cdr (cdr (cdr event)))))
    `(DEFTHM ,name ,term
       ,@(if (assoc-keyword :rule-classes alist)
             (replace-keyword-arg :rule-classes x alist)
             `(:rule-classes ,x ,@alist)))))

(defun replace-xargs (dcls x)
  (cond ((endp dcls) `((DECLARE (XARGS ,@x))))
        ((and (eq (car (car dcls)) 'DECLARE)
              (assoc 'XARGS (cdr (car dcls))))
         (cons (cons 'DECLARE
                     (put-assoc-equal 'XARGS x (cdr (car dcls))))
               (cdr dcls)))
        (t (cons (car dcls)
                 (replace-xargs (cdr dcls) x)))))

(defun edit-xargs (event x)
  (let ((name (nth 1 event))
        (vars (nth 2 event))
        (dcls (all-but-last (cdr (cdr (cdr event)))))
        (body (nth (- (len event) 1) event)))
    `(DEFUN ,name ,vars
       ,@(replace-xargs dcls x)
       ,body)))

(defun do-edit-command (cmd event before-events after-events)
  (let ((ev-type (nth 0 cmd))
        (place (nth 2 cmd))
        (x (nth 3 cmd)))
    (case place
      (:before
       (mv (append before-events x) event after-events))
      (:after
       (mv before-events event (append after-events x)))
      (:hints
       (cond
        ((eq ev-type 'defthm)
         (mv before-events (edit-hints event x) after-events))
        (t (mv nil
               (er hard 'defsys
                   "The event editor cannot handle a :hints edit command ~
                    except on DEFTHM events.  So ~x0 is an illegal edit ~
                    command."
               cmd)
               nil))))
      (:rule-classes
       (cond
        ((eq ev-type 'defthm)
         (mv before-events (edit-rule-classes event x) after-events))
        (t (mv nil
               (er hard 'defsys
                   "The event editor cannot handle a :rule-classes edit ~
                    command except on DEFTHM events.  So ~x0 is an illegal ~
                    edit command."
               cmd)
               nil))))
      (:xargs
       (cond
        ((eq ev-type 'defun)
         (mv before-events (edit-xargs event x) after-events))
        (t (mv nil
               (er hard 'defsys
                   "The event editor cannot handle an :xargs edit command ~
                    except on DEFUN events.  So ~x0 is an illegal edit ~
                    command."
               cmd)
               nil))))
      (otherwise
       (mv nil
           (er hard 'defsys
               "The event editor cannot handle the command ~x0.  Legal ~
                commands are (DEFTHM name :HINTS x), (DEFTHM name ~
                :RULE-CLASSES x), (DEFUN name :XARGS x), (ev-type name ~
                :BEFORE x), or (ev-type name :AFTER x)."
           cmd)
           nil)))))

(defun do-edit-commands (cmds event before-events after-events)
  (cond
   ((endp cmds)
    (mv before-events event after-events))
   (t (mv-let (new-before-events new-event new-after-events)
              (do-edit-command (car cmds) event before-events after-events)
              (do-edit-commands (cdr cmds)
                                new-event new-before-events new-after-events)))))

(defun edit-event-lst (events commands)
  (cond
   ((endp events)
    (cond (commands
           (er hard 'xdefsys
               "The following commands were not used, ~x0."
               commands))
          (t nil)))
   ((and (consp (car events))
         (consp (cdr (car events)))
         (symbolp (cadr (car events))))
    (mv-let (relevant-cmds leftover-cmds)
            (relevant-edit-commands (car (car events))
                                    (cadr (car events))
                                    commands nil nil)

            (mv-let (before-events new-event after-events)
                    (do-edit-commands relevant-cmds (car events) nil nil)
                    (append before-events
                            (cons new-event
                                  (append after-events
                                          (edit-event-lst (cdr events) leftover-cmds)))))))
   (t (cons (car events)
            (edit-event-lst (cdr events) commands)))))

(defmacro defsys (acl2::&key ld-flg modules edit-commands)
  (mv-let
   (amodule-lst max-a-regs)
   (annotate-modules modules 0 nil nil 0)
   (mv-let
    (ccode id-to-label-table)
    (compile-system '((CALL MAIN) (HALT))
                    amodule-lst max-a-regs)

; This system will require a total of 2*max-a-regs + 1 locals.  The first max-var
; of them, locals 0, ..., max-var-1, are called the ``A registers''.  The next
; max-var of them, namely max-var, max-var+1, ..., 2max-var-1, are the ``B
; registers''.  The last, 2max-var, is the return-pc register.  The A registers
; are used to hold the locals of the active module.  The B registers are used
; merely to implement the basic operations of CALL and RET.  (To enter a module
; with n locals, we pop n items off the stack and store them in the B
; registers.  Then we push the relevant A registers to protect them.  Then we
; move the B registers to the A registers for use by the module's code.
; Exiting upon RET is the symmetric operation.)

    (let* ((switch-table (switch-table ccode nil))
           (acode (assemble ccode switch-table nil max-a-regs))
           (label-table (label-table acode 0 nil))
           (event-lst
            `((defconst *amodule-lst* ',amodule-lst)
              (defconst *max-a-regs* ,max-a-regs)
              (defconst *ccode* ',ccode)
              (defconst *acode* ',acode)
              (defconst *psi* ',(link acode 0 label-table nil))
              (defun psi () *psi*)
              (defthm next-inst-psi
                (implies (acl2::syntaxp (acl2::quotep i))
                         (equal (nth i (psi)) (nth i *psi*))))
              (in-theory (disable psi (:executable-counterpart psi)))
              (defconst *id-to-label-table* ',id-to-label-table)
              (defconst *switch-table* ',switch-table)
              (defconst *label-table* ',label-table)
              ,@(defconst-lst label-table)

; The code above generates the M1 byte code and our tables.  Now we work on the
; verification events for each successive module.  The following function is
; used in all the top-level clock functions, to compute the time to exit a
; call with a given id.  From id we get the corresponding return pc label and
; then compute where that label occurs in list of return targets considered.
; If you look at expand-ret you see that jumpting to the first pc in lst takes
; 4 instructions, the next 8, etc., until you get to the last pc in lst, which
; takes just 1 more instruction than the previous label took.

              (defun exit-clock (fn id)
                (let* ((exit (cdr (assoc id *id-to-label-table*)))
                       (lst (cdr (assoc fn *switch-table*)))
                       (tail (member-equal exit lst)))
                  (cond ((or (endp tail)
                             (endp (cdr tail)))
                         (+ 1 (* 4 (nfix (- (len lst) 1)))))
                        (t (* 4 (+ 1 (nfix (- (len lst) (len tail)))))))))

; This is used in the code correctness theorems and returns the final pc given
; the called routine and the id of the call.

              (defun final-pc (fn id)
                (cond ((assoc-equal id *id-to-label-table*)
                       (let* ((label (cdr (assoc-equal id *id-to-label-table*))))
                         (cond ((member label (cdr (assoc fn *switch-table*)))
                                (cdr (assoc label *label-table*)))
                               (t *illegal-final-pc*))))
                      (t *illegal-final-pc*)))

              (defun ready-at (pc local-names d s)
                (and (acl2::true-listp s)
                     (equal (len s) 4)
                     (equal (pc s) pc)
;(acl2::true-listp (locals s))
                     (<= ,(+ (* 2 max-a-regs) 1) (len (locals s)))
                     (name-locals local-names (locals s) 0)
                     (<= d (len (stack s)))
                     (equal (program s) (psi))))

              ,@(verification-events-for-modules amodule-lst nil
                                                 max-a-regs amodule-lst)

              ))
           (elaborated-event-lst
            (edit-event-lst event-lst edit-commands))
           (final-event-lst
            `((defconst *defsys-events*
                ',event-lst)
              (defconst *elaborated-defsys-events*
                ',elaborated-event-lst)
              ,@elaborated-event-lst)))
      (if ld-flg
          `(ld ',final-event-lst :ld-pre-eval-print t)
          `(encapsulate nil ,@final-event-lst))))))


