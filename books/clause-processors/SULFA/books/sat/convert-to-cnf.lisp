
;; What I'm up to:
;; Seperating top-vars from the rest:
;; modify pop-traversal-var and push-traversal-var (push-top-traversal-var)
;; (push-defined-traversal-var)
;; use proper version of push for task at hand
;; modify un-fn to always create top-traversal-var (sometimes another one
;; as well).
;; Fix completed-var-list usage

;; Todo (critical):


;; Todo (non-critical): use bfix accessor
;;                      clean up todo-entry
;;                      consider changing args to remove-functions
;;                      clean up comments
;;                      look for useless functions
;; ... rename all things named todo-list, or at least make the naming consistent!
;; ... rename non-list arguments to ground arguments
;; ... delete list axiom include book and makefile entry
;;    value.  Also allow 'not through as an accessor
;; ... update bfix comments to reflect change to eq-nil
;; ... use stack methodology for "pop"ed tail-rec funcs
;; ...optimize (eq val nil) by allowing 'not as a remove-functions return
;; ... change atoms-alist to atom-alist
;; ... ensure that I've tested all the wierd cases involving list axioms
;; ... consider removing accessor tests when "simplified"
;; ... consider optimizing ifs with constant true or false branches.
;; ... rename i-expr-to-f-expr
;; ... consider avoiding the creation of multiple variables to represent
;;     the same eq-const, s.a. (eq x '(1 2 3)).
;; ... make use of the new constant checker in the local-clause-optimizer
;; ... simplify the get-eq-f-expr, create-eq-const-var, etc.  Just use
;;     get-eq-f-expr for everything?
;; ... consider removing the "-const" functions.  They are a minor optimization
;;     that increases the chance of bugs.  Nevermind, I think.  If a merge the
;;     functions I'll need to make the f-expr and the const functions mutually
;;     recursive.
;; ... add section explaining terminology of f-expr and i-expr
;; ... Thoughts on code cleanup:
;;     --- simplify comments and functions to, as much as possible, take in the
;;         following inputs: SULFA expressions, intermediate expressions,
;;         and final expressions.  These can be denoted S0, S2, ... SN, I0, I1,
;;         ... IN, F0, ... FN, with variables in lower-case.
;; ... Make get-eq-f-expr tail-recursive
;; ... rename create-eq-var, since it doesn't necessarily create a var.
;; ... consider whether new-top-i-var, add-new-todo, and new-i-var should
;;     have a better abstraction.
;; ... use raw and real ce-vali functions so that it looks like I have an array
;;     of Booleans.
;; ... consider optimizing compare-cons-lists, if possible
;; ... move the neq into its own file, write an essay on how it works and
;;     generalize the "temporary" variable idea and see if I can use it for
;;     consp as well.
;; ... Add a variable to sat that states whether the SAT procedure
;;     succeeded (either proved it or found a real counter-example).
;;     Use with make-event to create a nice regression-test.
;; ... Rename deconstruct-sat-stobj
;; ... Consider making the arrays non-resizable
;; ... consider reordering the arguments to add-cnf-disjunct-implication

;; Some terminology:
;; i-variable:  An "intermediate" variable representing an ACL2 object and
;;              denoted by a positive integer.  Variables in the original
;;              ACL2 expression are turned into i-variables, along with
;;              a number of variables created during the conversion process.
;;
;; f-variable:  A "final" variable representing a Boolean and denoted by
;;              a positive integer.  An f-variable always corresponds to
;;              a Boolean i-expression---either (equal <i-var> (quote ...))
;;              or (consp <i-var>).
;;
;; i-expression:  A well-formed expression formed from i-variables.  An
;;                i-expression has the following grammer:
;; <i-expr> ::= <i-var> | <const-expr> | (cons <i-expr> <i-expr>) |
;;              (equal <i-expr> <i-expr>) | <consp-expr>
;; <consp-expr> ::= (consp <i-var>)
;; <const-expr> ::= (quote <ACL2-constant>)

;; f-expression:  A well-formed expression formed from f-variables.  An
;;                f-expression has the following grammer:
;; <f-expr> ::= t | nil | <f-var> | <negated-f-var>

;; Where <f-var> is a positive integer denoting an f-variables and <negated-f-var>
;; is a negative integerp, denoting the negation of an f-variable.  The
;; symbols t and nil represent true and false respectively.

(in-package "SAT")
(program)
(set-state-ok t)

(include-book "sat-setup")
(include-book "local-clause-simp")
(include-book "neq-implication")

(defun lookup-ufe-list (fn not-found-val $sat)
  (declare (xargs :stobjs $sat))
  (getprop fn 'ufe-list not-found-val 'un-fn-world (un-fn-world $sat)))

(defun set-ufe-list (fn val $sat)
  (declare (xargs :stobjs $sat))
  (update-un-fn-world (putprop fn 'ufe-list val (un-fn-world $sat))
                      $sat))

;; Add the unique keys in key-list to alist.
(defun add-to-alist (key-list val-list alist)
  (if (endp key-list)
      alist
    (add-to-alist (cdr key-list)
                  (cdr val-list)
                  (cons (cons (car key-list)
                              (car val-list))
                        alist))))


;; Make an alist with only constant values in it.
(defun add-vals-to-alist (key-list val-list alist)
  (cond
   ((endp key-list)
    alist)
   ((constp (car val-list))
    (add-vals-to-alist (cdr key-list)
                       (cdr val-list)
                       (cons (cons (car key-list)
                                   (unquote (car val-list)))
                             alist)))
   (t
    (add-vals-to-alist (cdr key-list)
                       (cdr val-list)
                       alist))))

;; An ACL2 Todo Entry Represents a variable that has
;; been created to represent an ACL2 expression, but has
;; not yet been turned into CNF clauses, or even into
;; i-expressions.

;; It is a tree structure:
;; '((accessor-list . expr) . ((cnf-lits . alist) . (rec-fn-list . ord)))
;;
;; I'm using a compact structure to conserve memory and
;; speed up access & updating.
;;
;; Representing the clause:
;; (or (equal var expr''') cnf-lits)
;;
;; Where expr' is expr with the accessors in
;; accessor-list, a list of cars, cdrs, and
;; a consp, added to it with the first element
;; in accessor-list becoming the inner-most accessor
;; in expr'
;;
;; Expr'' is expr under the alist substitution.
;;
;; Expr''' is expr'' with any calls to functions
;; in rec-fn-list with an ordinal not less than ord
;; replaced with 'nil.
;;
;; Here we associate an ordinal with a function call
;; by mapping the arguments of the function call
;; to the formals of the function in the
;; termination justifying measure and
;; evaluating (the arguments that map to formals
;; in the measure are constant).  Such an ordinal
;; is expected to decrease on recursive calls.  If it
;; fails to decrease, we replace it with 'nil (its
;; value doesn't matter---as proven during termination
;; justification).

;; '((accessor-list . expr) . ((cnf-lits . alist) . (rec-fn-list . ord)))
(defun ate-accessor-list (at-entry)
  (car (car at-entry)))

(defun ate-expr (at-entry)
  (cdr (car at-entry)))

(defun ate-cnf-lits (at-entry)
  (car (car (cdr at-entry))))

(defun ate-alist (at-entry)
  (cdr (car (cdr at-entry))))

(defun ate-rec-fn-list (at-entry)
  (car (cdr (cdr at-entry))))

(defun ate-ord (at-entry)
  (cdr (cdr (cdr at-entry))))

;; '((accessor-list . (var . expr)) . ((cnf-lits . alist) . (rec-fn-list . ord)))
(defun make-acl2-todo-entry (accessor-list expr cnf-lits alist rec-fn-list ord)
  `((,accessor-list . ,expr) . ((,cnf-lits . ,alist) . (,rec-fn-list . ,ord))))

;; Create an intermediate variable that possibly represents
;; the top level of a cons structure (and therefore could have
;; relevant non-constant equalities.
(defun new-top-i-var ($sat)
  (declare (xargs :stobjs $sat))
  (mv-let
   (new-var $sat)
   (++i-var $sat)
   (let (($sat (push-top-traversal-var new-var $sat)))
     (mv new-var $sat))))

(defun new-defined-i-var ($sat)
  (declare (xargs :stobjs $sat))
  (mv-let
   (new-var $sat)
   (++i-var $sat)
   (let (($sat (push-defined-traversal-var new-var $sat)))
     (mv new-var $sat))))

(defconst *empty-at-entry*
  (make-acl2-todo-entry nil nil nil nil nil nil))

(defun ate-update-accessor-list (accessor-list at-entry)
  `((,accessor-list . ,(cdr (car at-entry))) . ,(cdr at-entry)))

(defun ate-update-expr (expr at-entry)
  `((,(car (car at-entry)) . ,expr) . ,(cdr at-entry)))

(defun ate-update-alist (alist at-entry)
  `(,(car at-entry)
    .
    ((,(car (car (cdr at-entry))) . ,alist) . ,(cdr (cdr at-entry)))))

(defun ate-update-cnf-lits (cnf-lits at-entry)
  `(,(car at-entry)
    .
    ((,cnf-lits . ,(cdr (car (cdr at-entry)))) . ,(cdr (cdr at-entry)))))

(defun ate-add-lit (lit at-entry)
  (ate-update-cnf-lits (cons lit (ate-cnf-lits at-entry)) at-entry))

(defun ate-add-accessor (acc at-entry)
  (ate-update-accessor-list (cons acc (ate-accessor-list at-entry))
                           at-entry))

(defun ate-pop-accessor (at-entry)
  (let ((accessor-list (ate-accessor-list at-entry)))
    (mv (car accessor-list)
        (ate-update-accessor-list (cdr accessor-list) at-entry))))

(defun ate-update-recursion (rec-fn-list ord at-entry)
  `(,(car at-entry)
    .
    (,(car (cdr at-entry)) . (,rec-fn-list . ,ord))))

;;(defun te-remove-accessors (at-entry)
;;  (ate-update-accessor-list nil at-entry))

(defun get-justifying-ord (fn args state)
  (let* ((justif (fn-justification fn state))
         (alist (add-vals-to-alist (fn-formals fn state)
                                   args
                                   nil)))
    (mv-let
     (erp val state)
     (simple-translate-and-eval (acl2::access acl2::justification justif
                                              :measure)
                                alist
                                nil
                                "SAT internal evaluator"
                                "get-justifying-ord"
                                (w state)
                                state

; Matt K.: I added the argument aok=nil for v4-0.  Thus, attachments are
; disallowed.  That's the conservative thing to do, and my guess is that it's
; the necessary thing to do, at least in this case (less sure about the other
; two below); but if necessary, this decision could be revisited.

                                nil)
     (if erp
         (mv (er hard 'get-justifying-ord
                 "Error evaluating ordinal~%")
             state)
       (mv (cdr val) state)))))

;; Return t if the function call (fn args) is irrelevant,
;; since it i a recursive call and its ordinal is greater than
;; or equal to the ordinal of its enclosing function.
(defun irrelevant-recursionp (fn args at-entry state)
  (let ((rec-fn-list (ate-rec-fn-list at-entry)))
    (if (and (not (consp fn))
             (member-eq fn rec-fn-list))
        (mv-let
         (inner-ord state)
         (get-justifying-ord fn args state)
         (if (o< inner-ord (ate-ord at-entry))
             (mv nil state)
           (mv t state)))
      (mv nil state))))

(defun update-recursion (fn args at-entry state)
  (if (consp fn)
      (mv at-entry state)
    (let ((recursivep-prop (getprop fn
                                    'acl2::recursivep
                                    nil
                                    'acl2::current-acl2-world
                                    (w state))))
      (cond
       ((not recursivep-prop)
        (mv at-entry state))
       ((atom recursivep-prop)
        (mv-let
         (ord state)
         (get-justifying-ord fn args state)
         (mv (ate-update-recursion (list fn)
                                  ord
                                  at-entry)
             state)))
       (t
        ;; fn is a member of a mutually-recursive set
        ;; given by recursivep-prop.
        (mv-let
         (ord state)
         (get-justifying-ord fn args state)
         (mv (ate-update-recursion recursivep-prop
                                  ord
                                  at-entry)
             state)))))))

;; I-todo-entries represent an ACL2 expression that
;; has been converted into an I-expression, but not
;; yet into CNF clauses
;; (<cnf-lits> . <expr>)

(defun make-i-expr-todo-entry (expr cnf-lits)
  (cons cnf-lits expr))

(defun iete-expr (i-todo-entry)
  (cdr i-todo-entry))

(defun iete-cnf-lits (i-todo-entry)
  (car i-todo-entry))

;; Cons-todo-entries represent a CONS that may have been
;; partially converted into CNF clauses.

;; A cet-entry is actually an address, so that we can
;; update it without returning it.  The address points
;; to a structure with the following form:
;; ((<car-t-struct> . <cdr-t-struct>) . <cnf-lits>)

;; Note that cet-entries are never deleted, so no garbage
;; collection is needed!!!

(defun new-cete ($sat)
  (declare (xargs :stobjs $sat))
  (let* ((cet-addr (num-cete $sat))
         ($sat (update-num-cete (1+ cet-addr) $sat))
         (cet-size (cet-entry-length $sat)))
    (cond
     ((< cet-addr cet-size)
      (mv cet-addr $sat))
     (t
      (let (($sat (resize-cet-entry (* 2 cet-size) $sat)))
        (mv cet-addr $sat))))))

(defun make-cons-expr-todo-entry (car-t-struct cdr-t-struct cnf-lits $sat)
  (declare (xargs :stobjs $sat))
  (mv-let
   (cet-addr $sat)
   (new-cete $sat)
   (let (($sat (update-cet-entryi cet-addr
                                  `((,car-t-struct . ,cdr-t-struct) . ,cnf-lits)
                                  $sat)))
     (mv cet-addr $sat))))


(defun cete-car (cet-entry $sat)
  (declare (xargs :stobjs $sat))
  (caar (cet-entryi cet-entry $sat)))

(defun cete-cdr (cet-entry $sat)
  (declare (xargs :stobjs $sat))
  (cdar (cet-entryi cet-entry $sat)))

(defun cete-cnf-lits (cet-entry $sat)
  (declare (xargs :stobjs $sat))
  (cdr (cet-entryi cet-entry $sat)))

(defun cete-update-car-cdr (cete-car cete-cdr cet-entry $sat)
  (declare (xargs :stobjs $sat))
  (update-cet-entryi cet-entry
                     `((,cete-car . ,cete-cdr) .
                       ,(cdr (cet-entryi cet-entry $sat)))
                     $sat))

;; A todo-struct represents an ACL2 expression that has been partially
;; converted into i-expressions.
;; (<ate-list> . (<cete-list> . <iete-list>))

(defun make-todo-struct (ate-list cete-list iete-list)
  `(,ate-list . (,cete-list . ,iete-list)))

(defconst *empty-todo-struct* `(nil . (nil . nil)))

(defun ts-ate-list (t-struct)
  (car t-struct))

(defun ts-cete-list (t-struct)
  (cadr t-struct))

(defun ts-iete-list (t-struct)
  (cddr t-struct))

(defun ts-update-ate-list (ate-list t-struct)
  `(,ate-list . ,(cdr t-struct)))

(defun ts-update-cete-list (cete-list t-struct)
  `(,(car t-struct) . (,cete-list . ,(cddr t-struct))))

(defun ts-update-iete-list (iete-list t-struct)
  `(,(car t-struct) . (,(cadr t-struct) . ,iete-list)))

(defun ts-emptyp (t-struct)
  (and (atom (ts-ate-list t-struct))
       (atom (ts-cete-list t-struct))
       (atom (ts-iete-list t-struct))))

(defun ts-add-at-entry (at-entry t-struct)
  (ts-update-ate-list (cons at-entry (ts-ate-list t-struct)) t-struct))

(defun ts-add-cet-entry (car-t-struct cdr-t-struct cnf-lits t-struct $sat)
  (declare (xargs :stobjs $sat))
  (mv-let
   (cet-entry $sat)
   (make-cons-expr-todo-entry car-t-struct cdr-t-struct cnf-lits $sat)
   (mv (ts-update-cete-list (cons cet-entry (ts-cete-list t-struct))
                            t-struct)
       $sat)))

;; Candidate for tail-recursive optimization!
(defun ts-add-ite-entry (expr cnf-lits t-struct $sat)
  (declare (xargs :stobjs $sat))
  (cond
   ((and (consp expr) (eq 'cons (car expr)))
    ;; Break up cons into cet-entries
    (let* ((car-expr (cadr expr))
           (cdr-expr (caddr expr))
           (ts-car (make-todo-struct nil nil nil))
           (ts-cdr (make-todo-struct nil nil nil)))
      (mv-let
       (ts-car $sat)
       (ts-add-ite-entry car-expr cnf-lits ts-car $sat)
       (mv-let
        (ts-cdr $sat)
        (ts-add-ite-entry cdr-expr cnf-lits ts-cdr $sat)
        (ts-add-cet-entry ts-car ts-cdr cnf-lits t-struct $sat)))))
   (t
    (mv (ts-update-iete-list (cons (make-i-expr-todo-entry expr cnf-lits)
                                   (ts-iete-list t-struct))
                             t-struct)
        $sat))))

;; An uninterpreted-function-entry is used to store information
;; about each call to an uninterpreted function.  Currently:
;; (<i-var> . <arg-list>)
;; Where i-var is the intermediate variable representing the
;; call and arg-list is a list of intermediate expressions
;; representing the arguments to the call.

(defun make-uninterpreted-function-entry (top-var defined-var arg-list)
  (cons (cons top-var defined-var) arg-list))

(defun ufe-top-var (uf-entry)
  (caar uf-entry))

(defun ufe-defined-var (uf-entry)
  (cdar uf-entry))

(defun ufe-arg-list (uf-entry)
  (cdr uf-entry))

;; Create a new intermediate variable to represent
;; the expression "expr".

(defun new-i-variable (expr at-entry $sat)
  (declare (xargs :stobjs $sat))
  (mv-let
   (var $sat)
   (new-defined-i-var $sat)
   (let* ((at-entry (ate-update-expr expr at-entry))
          (at-entry (ate-update-cnf-lits nil at-entry))
          ($sat (update-todo-structi var
                                     (make-todo-struct (list at-entry) nil nil)
                                     $sat)))
     (mv var $sat))))

(defun assoc-eql (key alist)
  (cond
   ((endp alist)
    nil)
   ((eql key (caar alist))
    (car alist))
   (t
    (assoc-eql key (cdr alist)))))

;; I could add the accessors and run tran-eval,
;; but my guess is that there is more overhead in that
;; then just using this interpreter.
(defun eval-const-accessors (accessor-list val)
  (cond
   ((endp accessor-list)
    val)
   ((eq (car accessor-list) 'consp)
    (eval-const-accessors (cdr accessor-list) (consp val)))
   ((eq (car accessor-list) 'car)
    (eval-const-accessors (cdr accessor-list) (logical-car val)))
   ((eq (car accessor-list) 'cdr)
    (eval-const-accessors (cdr accessor-list) (logical-cdr val)))
   (t
    (er hard 'eval-const-accessors
        "Unknown accessor ~x0~%"
        (car accessor-list)))))

(defun add-var-accessors (acc-list var $sat)
    (declare (xargs :stobjs $sat))
  (cond
   ((endp acc-list)
    (mv var $sat))

   ((eq 'car (car acc-list))
    (mv-let
     (var $sat)
     (get-car-var var $sat)
     (add-var-accessors (cdr acc-list) var $sat)))

   ((eq 'cdr (car acc-list))
    (mv-let
     (var $sat)
     (get-cdr-var var $sat)
     (add-var-accessors (cdr acc-list) var $sat)))

   ((eq 'consp (car acc-list))
    (mv `(consp ,var) $sat))

   (t
    (mv (er hard 'add-var-accessors
            "Bad accessor list: ~x0~%"
            acc-list)
        $sat))))

;; Take a simple-expr and return a new simple-expr,
;; taking accessors into account.

(defun add-accessors (acc-list expr $sat)
  (declare (xargs :stobjs $sat))
  (cond
   ((atom expr)
    (add-var-accessors acc-list expr $sat))

   ((eq (car expr) 'cons)
    (cond
     ((endp acc-list)
      (mv expr $sat))
     ((eq 'car (car acc-list))
      (add-accessors (cdr acc-list)
                     (cadr expr)
                     $sat))
     ((eq 'cdr (car acc-list))
      (add-accessors (cdr acc-list)
                     (caddr expr)
                     $sat))
     ((eq 'consp (car acc-list))
      (mv '(quote t) $sat))
     (t
      (mv (er hard 'add-accessors
              "Unknown accessor ~x0~%"
              (car acc-list))
          $sat))))

   ((or (eq (car expr) 'consp)
        (eq (car expr) 'equal))
    (if (endp acc-list)
        (mv expr $sat)
      (mv '(quote nil) $sat)))

   ((quotep expr)
    (mv `(quote ,(eval-const-accessors acc-list (unquote expr)))
        $sat))

   (t
    (mv (er hard 'add-accessors
            "Expected a simple expression, but got ~x0~%"
            expr)
        $sat))))


;; Convert an intermediate expression into a final expression representing
;; whether it is non-nil.  Note that an intermediate expression has the
;; following Grammar:

;;<i-expr> ::= <i-var> | <const-expr> | (cons <i-expr> <i-expr>) | (equal <i-expr> <i-expr>) | <consp-expr>
;;<consp-expr> ::= (consp <i-var>)
;;<const-expr> ::= (quote <ACL2-constant>)

;; In the following function, we methodically go through each of the 10 cases
;; implied by the above grammar.

(mutual-recursion
(defun eq-i-expr-to-f-expr (i0 i1 $sat)
  (declare (xargs :stobjs $sat))
  (cond
   ((atom i0)
    (cond
     ((atom i1)
      (create-eq-var i0 i1 $sat))
     ((quotep i1)
      (if (atom (unquote i1))
          (create-atom-var i0 (unquote i1) $sat)
        (let ((car-i1 `(quote ,(car (unquote i1))))
              (cdr-i1 `(quote ,(cdr (unquote i1)))))
          ;; Break up non-atomic constants
          (mv-let
           (car-i0 $sat)
           (get-car-var i0 $sat)
           (mv-let
            (cdr-i0 $sat)
            (get-cdr-var i0 $sat)
             (mv-let
              (new-i-var $sat)
              (new-i-variable `(if (i-expression (consp ,i0))
                                   (if (i-expression (equal ,car-i0 ,car-i1))
                                       (i-expression (equal ,cdr-i0 ,cdr-i1))
                                     (quote nil))
                                 (quote nil))
                              *empty-at-entry*
                              $sat)
              (i-expr-to-f-expr new-i-var $sat)))))))
     ((eq 'cons (car i1))
      (let ((car-i1 (cadr i1))
            (cdr-i1 (caddr i1)))
        (mv-let
         (car-i0 $sat)
         (get-car-var i0 $sat)
         (mv-let
          (cdr-i0 $sat)
          (get-cdr-var i0 $sat)
          (mv-let
           (new-i-var $sat)
           (new-i-variable `(if (i-expression (consp ,i0))
                                (if (i-expression (equal ,car-i0 ,car-i1))
                                    (i-expression (equal ,cdr-i0 ,cdr-i1))
                                  (quote nil))
                              (quote nil))
                           *empty-at-entry*
                           $sat)
           (i-expr-to-f-expr new-i-var $sat))))))
     ((or (eq 'equal (car i1))
          (eq 'consp (car i1)))
      (mv-let
       (new-i-var $sat)
       (new-i-variable `(if (i-expression ,i1)
                            (i-expression (equal ,i0 (quote t)))
                          (i-expression (equal ,i0 (quote nil))))
                       *empty-at-entry*
                       $sat)
       (i-expr-to-f-expr new-i-var $sat)))
     (t
      (mv (er hard 'eq-i-expr-to-f-expr
              "Illegal expression encountered, presumably output by remove-functions: ~x0"
              `(equal ,i0 ,i1))
          $sat))))

   ((atom i1)
    ;; Flip it so it matches the above case.
    (eq-i-expr-to-f-expr i1 i0 $sat))

   ((quotep i0)
    (cond
     ((quotep i1)
      (if (equal (unquote i0) (unquote i1))
          (mv *f-true* $sat)
        (mv *f-false* $sat)))

     ((eq 'cons (car i1))
      (cond
       ((atom (unquote i0))
        (mv *f-false* $sat))
       (t
        (let ((car-i0 `(quote ,(car (unquote i0))))
              (cdr-i0 `(quote ,(cdr (unquote i0))))
              (car-i1 (cadr i1))
              (cdr-i1 (caddr i1)))
          (mv-let
           (new-i-var $sat)
           (new-i-variable `(if (i-expression (equal ,car-i0 ,car-i1))
                                (i-expression (equal ,cdr-i0 ,cdr-i1))
                              (quote nil))
                           *empty-at-entry*
                           $sat)
           (i-expr-to-f-expr new-i-var $sat))))))

     ((eq 'equal (car i1))
      (cond
       ((equal (unquote i0) t)
        ;; We can reduce (eq (eq i0 i1) t) to (eq i0 i1)
        (eq-i-expr-to-f-expr (cadr i0) (caddr i0) $sat))
       ((equal (unquote i0) nil)
        ;; We can reduce (eq (eq i0 i1) nil) to (not (eq i0 i1))
        (mv-let
         (consp-var $sat)
         (eq-i-expr-to-f-expr (cadr i0) (caddr i1) $sat)
         (mv (negate-f-expr consp-var) $sat)))
       (t
        ;; Otherwise this equality can never be true
        (mv *f-false* $sat))))

     ((eq 'consp (car i1))
      (cond
       ((equal (unquote i0) t)
        ;; When i0=(consp x), we can reduce (eq i0 t) to i0
        (i-expr-to-f-expr i0 $sat))
       ((equal (unquote i0) nil)
        ;; We can reduce (eq (consp i0) nil) to (not (consp i0))
        (mv-let
         (consp-var $sat)
         (i-expr-to-f-expr i0 $sat)
         (mv (negate-f-expr consp-var) $sat)))
       (t
        ;; Otherwise this equality can never be true
        (mv *f-false* $sat))))
     (t
      (mv (er hard 'eq-i-expr-to-f-expr
              "Illegal expression encountered, presumably output by remove-functions: ~x0"
              `(equal ,i0 ,i1))
          $sat))))

   ((quotep i1)
    (eq-i-expr-to-f-expr i1 i0 $sat))

   ((eq 'cons (car i0))
    (cond
     ((eq 'cons (car i1))
      (let ((car-i0 (cadr i0))
            (cdr-i0 (caddr i0))
            (car-i1 (cadr i1))
            (cdr-i1 (caddr i1)))
        (mv-let
         (new-i-var $sat)
         (new-i-variable `(if (i-expression (equal ,car-i0 ,car-i1))
                              (i-expression (equal ,cdr-i0 ,cdr-i1))
                            (quote nil))
                         *empty-at-entry*
                         $sat)
         (i-expr-to-f-expr new-i-var $sat))))

     ((or (eq 'equal (car i1))
          (eq 'consp (car i1)))
      (mv *f-false* $sat))
     (t
      (mv (er hard 'eq-i-expr-to-f-expr
              "Illegal expression encountered, presumably output by remove-functions: ~x0"
              `(equal ,i0 ,i1))
          $sat))))

   ((eq 'cons (car i1))
    (eq-i-expr-to-f-expr i1 i0 $sat))

   ((or (eq 'equal (car i0))
        (eq 'consp (car i0)))
    (cond
     ((or (eq 'equal (car i1))
          (eq 'consp (car i1)))
      (mv-let
       (new-i-var $sat)
       (new-i-variable `(if (i-expression ,i0)
                            (i-expression ,i1)
                          (if (i-expression ,i1)
                              (quote nil)
                            (quote t)))
                       *empty-at-entry*
                       $sat)
       (i-expr-to-f-expr new-i-var $sat)))
     (t
      (mv (er hard 'eq-i-expr-to-f-expr
              "Illegal expression encountered, presumably output by remove-functions: ~x0"
              `(equal ,i0 ,i1))
          $sat))))

   (t
    (mv (er hard 'eq-i-expr-to-f-expr
            "Illegal expression encountered, presumably output by remove-functions: ~x0"
            `(equal ,i0 ,i1))
        $sat))))

(defun i-expr-to-f-expr (expr $sat)
  (declare (xargs :stobjs $sat))
  (cond
   ((atom expr)
    (mv-let
     (eq-nil-var $sat)
     (create-eq-nil-var expr $sat)
     (mv (negate-f-expr eq-nil-var) $sat)))

   ((eq (car expr) 'consp)
    (create-consp-var (cadr expr) $sat))

   ((quotep expr)
    (if (unquote expr)
        (mv *f-true* $sat)
      (mv *f-false* $sat)))

   ((eq (car expr) 'cons)
    (mv *f-true* $sat))

   ((eq (car expr) 'equal)
    (eq-i-expr-to-f-expr (cadr expr) (caddr expr) $sat))

   (t (mv (er hard 'i-expr-to-f-expr
              "Unexpected boolean expression ~x0~%"
              expr)
          $sat))))
)

;; Essay on uninterpreted functions:

;; We keep a sorted list of uninterpreted functions, which we
;; break into a prior-list and a post-list, for calls
;; traversed before and after a new one.

;; If the prior-list is non-nil, we mark that another traversal
;; is needed.

;; Let the current i-var be i1, with arg list a1_0 a1_1 ... a1_N

;; For each prior i-var i0, we add:
;; a1_0 = a0_0 /\ a1_1 = a0_1 /\ ... a1_N = a0_N
;; ->
;; i0 = i1

;; To the let expression for i0.

;; For each post i-var i2, we add:
;; a1_0 = a2_0 /\ a1_1 = a2_1 /\ ... a2_N = a2_N
;; ->
;; i1 = i2

;; To the let expression for i2.

(defun un-fn-add-iet-entry (iet-entry t-struct $sat)
  (declare (xargs :stobjs $sat))
  (let* ((t-struct (ts-update-iete-list
                    (cons iet-entry (ts-iete-list t-struct))
                    t-struct)))
    (mv t-struct $sat)))

;; Add iet-entry to var's todo-struct.
(defun un-fn-add-iet-entry-var (var iet-entry $sat)
  (declare (xargs :stobjs $sat))
  (let* ((t-struct (todo-structi var $sat)))
    (mv-let
     (t-struct $sat)
     (un-fn-add-iet-entry iet-entry t-struct $sat)
     (update-todo-structi var t-struct $sat))))

(defun add-new-uf-entry1 (var ufe-list acc $sat)
  (declare (xargs :stobjs $sat))
  (cond
   ((endp ufe-list)
    (mv acc ufe-list))
   ((traversed-prior-top var (ufe-defined-var (car ufe-list)) $sat)
    (mv acc ufe-list))
   (t
    (add-new-uf-entry1 var
                       (cdr ufe-list)
                       (cons (car ufe-list) acc)
                       $sat))))

(defun add-un-fn (fn $sat)
  (declare (xargs :stobjs $sat))
  (cond
   ((member-eq fn (un-fn-list $sat))
    $sat)
   (t
    (update-un-fn-list (cons fn (un-fn-list $sat)) $sat))))

(defun add-new-uf-entry (ufe-new fn $sat)
  (declare (xargs :stobjs $sat))
  (let* ((ufe-list (lookup-ufe-list fn nil $sat)))
    (mv-let
     (rev-prior-list post-list)
     (add-new-uf-entry1 (ufe-defined-var ufe-new) ufe-list nil $sat)
     (let* (($sat (add-un-fn fn $sat))
            ($sat (set-ufe-list
                   fn
                   (revappend rev-prior-list (cons ufe-new post-list))
                   $sat)))
       (mv (revappend rev-prior-list nil) post-list $sat)))))

(defun new-un-func-cnf-lits (arg-list0 arg-list1 cnf-lits $sat)
  (declare (xargs :stobjs $sat))
  (cond
   ((endp arg-list0)
    (mv cnf-lits $sat))
   (t
    (mv-let
     (eq-a0-a1 $sat)
     (eq-i-expr-to-f-expr (car arg-list0) (car arg-list1) $sat)
     (new-un-func-cnf-lits (cdr arg-list0) (cdr arg-list1)
                           (cons (negate-f-expr eq-a0-a1) cnf-lits)
                           $sat)))))

(defun new-un-func-prior-list (prior-list ufe-new $sat)
  (declare (xargs :stobjs $sat))
  (cond
   ((endp prior-list)
    $sat)
   (t
    (mv-let
     (cnf-lits $sat)
     (new-un-func-cnf-lits (ufe-arg-list (car prior-list))
                           (ufe-arg-list ufe-new)
                           nil $sat)
     (let* ((iet-entry (make-i-expr-todo-entry (ufe-top-var ufe-new) cnf-lits))
            ($sat (un-fn-add-iet-entry-var (ufe-defined-var (car prior-list)) iet-entry
                                           $sat))
            ;;!! Note: The following is (hopefully) a temporary fix. The
            ;;   variable shouldn't be considered relevant so much as
            ;;   containing a new i-expression that needs to be traversed.
            ;;   All new i-expressions should be traversed, regardless of
            ;;   whether said variable is "relevant".  For now I can't
            ;;   do this the right way because we don't have a concept
            ;;   of new i-expressions.
            ($sat (mark-ivar-relevant (ufe-defined-var (car prior-list)) $sat)))
       (new-un-func-prior-list (cdr prior-list) ufe-new $sat))))))

(defun new-un-func-post-list (post-list ufe-new t-struct $sat)
  (declare (xargs :stobjs $sat))
  (cond
   ((endp post-list)
    (mv t-struct $sat))
   (t
    (mv-let
     (cnf-lits $sat)
     (new-un-func-cnf-lits (ufe-arg-list (car post-list))
                           (ufe-arg-list ufe-new)
                           nil $sat)
     (let ((iet-entry (make-i-expr-todo-entry (ufe-top-var (car post-list))
                                              cnf-lits)))
       (mv-let
        (t-struct $sat)
        (un-fn-add-iet-entry iet-entry t-struct $sat)
        (new-un-func-post-list (cdr post-list) ufe-new t-struct $sat)))))))

;; new-un-funct handles a new uninterpreted function
;; call to the function fn.  The uninterpreted function
;; entry ufe-new includes the i-variable this
;; new call is associated with and the uninterpreted
;; function call's arg-list.  The ate-list is the
;; ate-list for the i-variable associated with this
;; call, which we may add on to.

;; !! Note: We can do better than this!  Two new variables
;; are certainly unnecessary.  However, I'm just trying to get
;; something working.  If you really want fast uninterpretted functions,
;; consider using a preprocessing step before calling SULFA.
(defun new-un-func (fn args $sat)
  (declare (xargs :stobjs $sat))
  (mv-let
   (defined-var $sat)
   (new-defined-i-var $sat)
   (mv-let
    (top-var $sat)
    (new-top-i-var $sat)
    (let* ((uf-entry (make-uninterpreted-function-entry top-var defined-var args))
           (iet-entry (make-i-expr-todo-entry top-var nil))
           (t-struct (make-todo-struct nil nil (list iet-entry))))
      (mv-let
       (prior-list post-list $sat)
       (add-new-uf-entry uf-entry fn $sat)
       (let* (($sat (if prior-list
                        (update-need-more-traversals t $sat)
                      $sat))
              ($sat (new-un-func-prior-list prior-list
                                            uf-entry
                                            $sat)))
         (mv-let
          (t-struct $sat)
          (new-un-func-post-list post-list
                                 uf-entry
                                 t-struct
                                 $sat)
          (let* (($sat (update-todo-structi defined-var t-struct $sat)))
            (mv defined-var $sat)))))))))

(mutual-recursion

;; The following definition is one of the meat functions of our algorithm:
;; it adds entries to the todo list in order to simplify
;; an expr until it contains only list primitives.
;;
;; It takes in four inputs:
;; 1) expr: The expression we are currently simplifying
;; 2) at-entry: The at-entry that originally created this expression.
;;                It includes an alist under which the expression should be
;;                substituted, information about what function calls would be
;;                considered recursive calls and the ordinal that such calls
;;                must be smaller than, and a list of unary list accessor
;;                functions outside the current expr.
;; 3) $sat: The $sat state data structure
;; 4) state: The acl2 state
;;
;; It produces four outputs:
;; 1) expr: The simplified expression.
;; 2) accessors: A list of list accessors (car, cdr, and consp), in reverse
;;               order, that enclose expr.
;; 3) $sat: The updated $sat state.
;; 4) state: The updated ACL2 state.

;; Note: We could break up at-entry into its components.
;; I'm not sure if that would speed things up significantly
;; or not, so for now I'm just leaving it in its list structure
;; format.

;; Note: Candidate for tail-recursive optimization
;;       To make this function really fast, we could implement
;;       I-expressions as an array, rather than a List constant.
;;       If their implemented as an array, remove functions could
;;       SET the i-expression, rather than return it.
(defun remove-functions (expr at-entry $sat state)
  (declare (xargs :stobjs $sat))
  (cond
   ((atom expr)
    ;; expr is a variable---look it up in the alist
    (mv-let
     (expr $sat)
     (add-accessors (ate-accessor-list at-entry)
                    (cdr (assoc-eql expr (ate-alist at-entry)))
                    $sat)
     (mv expr $sat state)))

   ((quotep expr)
    ;; expr is a constant---return it
       (mv `(quote ,(eval-const-accessors (ate-accessor-list at-entry)
                                          (unquote expr)))
           $sat
           state))

   ((eq 'if (car expr))
    ;; expr is an if---either simplify it or create a variable for it
    (let ((cond-expr (cadr expr))
          (true-br (caddr expr))
          (false-br (cadddr expr)))
      (mv-let
       (cond-expr $sat state)
       (remove-functions cond-expr
                         (ate-update-accessor-list nil at-entry)
                         $sat
                         state)
       (cond
        ((or (atom cond-expr)
             (equal (car cond-expr) 'consp)
             (equal (car cond-expr) 'equal))
         ;; We don't know what the condition is---create a variable
         ;; to represent the current mess and add to the todo list
         (mv-let
          (new-var $sat)
          (new-i-variable `(if (i-expression ,cond-expr) ,true-br ,false-br)
                          at-entry
                          $sat)
          (mv new-var $sat state)))
        ((or (and (quotep cond-expr) (unquote cond-expr))
             (eq (car cond-expr) 'cons))
         ;; The condition is true
         (remove-functions true-br at-entry $sat state))
        ((and (quotep cond-expr) (not (unquote cond-expr)))
         ;; The condition is false
         (remove-functions false-br at-entry $sat state))
        (t
         (mv (er hard 'remove-functions
                 "Error: The if condition was not what we were expecting:~x0~%"
                 cond-expr)
             $sat
             state))))))

   ((or (eq 'car (car expr))
        (eq 'cdr (car expr)))
    ;; Expr is a list accessor, add it to the accessor list
    (remove-functions (cadr expr)
                      (ate-add-accessor (car expr) at-entry)
                      $sat
                      state))

   ((eq 'consp (car expr))
    ;; expr is a consp---
    ;; Note that we consider consp an accessor, but it better be
    ;; at the top-level (car (consp x))=nil, (consp (consp x))=nil.
    ;; (bfix (consp x)) = (consp x)
    (let ((accessor-list (ate-accessor-list at-entry)))
      (cond
       ((endp accessor-list)
        (remove-functions (cadr expr)
                          (ate-update-accessor-list '(consp)
                                                   at-entry)
                          $sat
                          state))
       (t
        (mv '(quote nil) $sat state)))))

   ((eq 'cons (car expr))
    ;; Expr is a cons, try to simplify it using the accessor
    ;; list.  If that doesn't work, simplify the leaves and
    ;; cons them together.
    (mv-let
     (acc at-entry)
     (ate-pop-accessor at-entry)
     (cond
      ((eq acc 'car)
       (remove-functions (cadr expr)
                         at-entry
                         $sat
                         state))
      ((eq acc 'cdr)
       (remove-functions (caddr expr)
                         at-entry
                         $sat
                         state))
      ((eq acc 'consp)
       (mv '(quote t) $sat state))
      ((eq acc nil)
       (mv-let
        (car-expr $sat state)
        (remove-functions (cadr expr)
                          at-entry
                          $sat
                          state)
        (mv-let
         (cdr-expr $sat state)
         (remove-functions (caddr expr)
                           at-entry
                           $sat
                           state)
         (cond
          ((and (constp car-expr)
                (constp cdr-expr))
           (mv `(quote ,(cons (unquote car-expr) (unquote cdr-expr)))
               $sat
               state))
          (t
           (mv `(cons ,car-expr ,cdr-expr)
               $sat
               state))))))
      (t
       (mv (er hard 'remove-functions "Unrecognized accessor:~x0~%" acc)
           $sat
           state)))))

   ((eq 'equal (car expr))
    ;; expr is an equal
    (let ((accessor-list (ate-accessor-list at-entry)))
      (cond
       ((consp accessor-list)
        ;; (car (equal x y)), (cdr (equal x y)), and (consp (equal x y)) are
        ;; all nil
        (mv '(quote nil) $sat state))
       (t
        (mv-let
         (lhs-expr $sat state)
         (remove-functions (cadr expr) at-entry $sat state)
         (mv-let
          (rhs-expr $sat state)
          (remove-functions (caddr expr) at-entry $sat state)
          (mv `(equal ,lhs-expr ,rhs-expr) $sat state)))))))

   ((eq 'i-expression (car expr))
    ;; A special symbol (protected by the SAT package) denoting that
    ;; its argument is already a simplified i-expression
    (mv (cadr expr) $sat state))

   (t
    ;; expr is a call to an unknown primitive or a user-defined
    ;; function.  If it's constant---evaluate!  If it's an irrelevant
    ;; recursive call, remove it!  Otherwise, open it.
    (mv-let
     (constp new-args $sat state)
     (remove-functions-list t
                            (cdr expr)
                            (ate-update-accessor-list nil at-entry)
                            nil
                            $sat
                            state)
     (cond
      ((uninterpreted-fnp (car expr) $sat state)
       (mv-let
        (var $sat)
        (new-un-func (car expr) new-args $sat)
        (mv-let
         (expr $sat)
         (add-accessors (ate-accessor-list at-entry) var $sat)
         (mv expr $sat state))))
      (constp
       (mv-let
        (erp val state)
        (simple-translate-and-eval (cons (car expr) new-args)
                                   nil
                                   nil
                                   "SAT internal evaluator"
                                   "remove-functions"
                                   (w state)
                                   state
                                   nil) ; see comment above about aok
        (if erp
            (mv (er hard
                    'remove-functions
                    "Unable to evaluate expression: ~x0~%"
                    (cons (car expr) new-args))
                $sat
                state)
          (mv `(quote ,(eval-const-accessors (ate-accessor-list at-entry)
                                             (cdr val)))
              $sat
              state))))
      (t
       (mv-let
        (irrelevantp state)
        (irrelevant-recursionp (car expr)
                               new-args
                               at-entry
                               state)
        (cond
         (irrelevantp
          ;; An irrelevant recursive call
          (mv '(quote nil) $sat state))

         (t
          ;; open up the user-defined function
          (let ((at-entry (ate-update-alist (add-to-alist (fn-formals (car expr) state)
                                                           new-args
                                                           nil)
                                             at-entry)))
            (mv-let
             (at-entry state)
             (update-recursion (car expr) new-args at-entry state)
             ;; open up the user-defined function
             (remove-functions (fn-body (car expr) state)
                               at-entry
                               $sat
                               state))))))))))))

(defun remove-functions-list (constp expr-list at-entry ans $sat state)
  (declare (xargs :stobjs $sat))
  (if (endp expr-list)
      (mv constp (reverse ans) $sat state)
    (mv-let
     (expr $sat state)
     (remove-functions (car expr-list) at-entry $sat state)
     (remove-functions-list (and constp (constp expr))
                            (cdr expr-list)
                            at-entry
                            (cons expr ans)
                            $sat
                            state))))
)

;; Add to the clause list:
;; (iff lhs rhs-const) \/ cnf-lits
;; Where rhs-const is a constant value and lhs is an f-var.
(defun add-cnf-iff-const (lhs rhs-const cnf-lits $sat state)
  (declare (xargs :stobjs $sat))
  (cond
   (rhs-const
    (add-cnf-clause (cons lhs cnf-lits) $sat state))
   (t
    (add-cnf-clause (cons (negate-f-expr lhs) cnf-lits) $sat state))))

;; Add (iff lhs-var rhs-var) \/ cnf-lits
;; Where lhs-var and rhs-var are both valid f-vars
(defun add-cnf-iff (lhs-var rhs-var cnf-lits $sat state)
  (declare (xargs :stobjs $sat))
  (mv-let
   ($sat state)
   (add-cnf-clause (list* lhs-var (negate-f-expr rhs-var) cnf-lits)
                   $sat state)
   (add-cnf-clause (list* (negate-f-expr lhs-var) rhs-var cnf-lits)
                   $sat state)))

;; Each of the entries in the atoms-alist represents
;; (eq x a) for some atomic constant a.  Here we
;; create clauses representing either (eq x a) \/ cnf-lits
;; or (not (eq x a) \/ cnf-lits depending on whether (eq x const-val)
;; is (eq x a).
(defun add-cnf-eq-atoms-const (atoms-alist const-val cnf-lits $sat state)
  (declare (xargs :stobjs $sat))
  (if (endp atoms-alist)
      (mv $sat state)
    (mv-let
     ($sat state)
     (add-cnf-iff-const (cdr (car atoms-alist))
                        (equal (car (car atoms-alist)) const-val)
                        cnf-lits
                        $sat
                        state)
     (add-cnf-eq-atoms-const (cdr atoms-alist)
                             const-val
                             cnf-lits
                             $sat
                             state))))

;; This function sets (not (eq x a)) \/ cnf-lits for all (eq x a)
;; represented in atoms-alist.
(defun add-cnf-eq-atoms-off (atoms-alist cnf-lits $sat state)
  (declare (xargs :stobjs $sat))
  (add-cnf-eq-atoms-const atoms-alist (cons nil nil) cnf-lits $sat state))

;; Here cnf-lits -> (eq x f-var).  Since f-var is a Boolean, this
;; translates to either cnf-lits -> (iff (eq x a) f-var),
;; cnf-lits -> (iff (not (eq x a)) f-var), cnf-lits -> (not (eq x a)) depending
;; on whether a is t, nil, or a non-Boolean.

(defun add-cnf-eq-atom-f-var (a eq-x-a-var f-var cnf-lits $sat state)
  (declare (xargs :stobjs $sat))
  (cond
   ((eq a nil)
    (add-cnf-iff (negate-f-expr eq-x-a-var) f-var cnf-lits $sat state))
   ((eq a t)
    (add-cnf-iff eq-x-a-var f-var cnf-lits $sat state))
   (t
    (add-cnf-iff-const eq-x-a-var nil cnf-lits $sat state))))

(defun add-cnf-eq-atoms-f-var (atoms-alist f-var cnf-lits $sat state)
  (declare (xargs :stobjs $sat))
  (if (endp atoms-alist)
      (mv $sat state)
    (mv-let
     ($sat state)
     (add-cnf-eq-atom-f-var (car (car atoms-alist))
                            (cdr (car atoms-alist))
                            f-var
                            cnf-lits
                            $sat
                            state)
     (add-cnf-eq-atoms-f-var (cdr atoms-alist)
                             f-var
                             cnf-lits
                             $sat
                             state))))

;; Now we have to convert the clause cnf-lits->(eq x y) into
;; a number of clauses involving the relevant (eq x a) atoms.  For
;; each of these we add the clause cnf-lits->(iff (eq x a) (eq y a)),
;; adding (eq y a) if it isn't already present.
(defun add-cnf-eq-atoms-i-var (atoms-alist rhs-var cnf-lits $sat state)
  (declare (xargs :stobjs $sat))
  (if (endp atoms-alist)
      (mv $sat state)
    (let ((a (car (car atoms-alist)))
          (eq-x-a (cdr (car atoms-alist))))
      (mv-let
       (eq-y-a $sat)
       (create-atom-var rhs-var a $sat)
       (mv-let
        ($sat state)
        (add-cnf-iff eq-x-a eq-y-a cnf-lits $sat state)
        (add-cnf-eq-atoms-i-var (cdr atoms-alist) rhs-var cnf-lits $sat state))))))

;; (eq x a)
;; =>
;; Given (eq x y) is relevant:
;; (iff (eq x y) (eq y a))
(defun add-cnf-eq-alist-const (eq-alist a cnf-lits $sat state)
  (declare (xargs :stobjs $sat))
  (if (endp eq-alist)
      (mv $sat state)
    (let ((y (caar eq-alist))
          (eq-x-y (cdar eq-alist)))
      (mv-let
       (eq-y-a $sat)
       (eq-i-expr-to-f-expr y `(quote ,a) $sat)
       (mv-let
        ($sat state)
        (add-cnf-iff eq-x-y eq-y-a cnf-lits $sat state)
        (add-cnf-eq-alist-const (cdr eq-alist) a cnf-lits $sat state))))))

(defun add-cnf-const-i1-push (lhs-var const-val todo-list)
  (if (not (valid-varp lhs-var))
      todo-list
    (cons (cons lhs-var const-val)
          todo-list)))

(mutual-recursion
(defun add-cnf-const-i1-pop (cnf-lits todo-list $sat state)
  (declare (xargs :stobjs $sat))
  (if (endp todo-list)
      (mv $sat state)
    (let* (;; Pop entry off todo-list
           (var-todo (car todo-list))
           (todo-list (cdr todo-list))

           ;; Get the current lhs and rhs constant
           (lhs-var (car var-todo))
           (const-val (cdr var-todo)))
      (add-cnf-const-i1 lhs-var const-val cnf-lits todo-list $sat state))))

(defun add-cnf-const-i1 (lhs-var const-val cnf-lits todo-list $sat state)
  (declare (xargs :stobjs $sat))
  ;;(let ((eq-f-var (lookup-atom-var lhs-var const-val $sat)))
  ;;  (cond
  ;;   ((valid-varp eq-f-var)
  ;;    ;; We have a variable representing (eq lhs-var cosnt-val)
  ;;    (mv-let
  ;;     ($sat state)
  ;;     (add-cnf-clause (cons eq-f-var cnf-lits) $sat state)
  ;;     (add-cnf-const-i1-pop cnf-lits todo-list $sat state)))
  ;;   (t
      (let* ( ;; Break each side up into bfix, consp, car, & cdr.
             (atoms-lhs (atoms-alist-vari lhs-var $sat))
             (eq-alist-lhs (eq-alist-vari lhs-var $sat)))
        (mv-let
         ($sat state)
         (add-cnf-eq-alist-const eq-alist-lhs const-val cnf-lits $sat state)
         (mv-let
          ($sat state)
          (add-cnf-eq-atoms-const atoms-lhs const-val cnf-lits $sat state)
          (cond
           ((consp const-val)
            (let* ((consp-lhs (consp-vari lhs-var $sat))
                   (car-lhs (car-vari lhs-var $sat))
                   (cdr-lhs (cdr-vari lhs-var $sat))
                   (todo-list (add-cnf-const-i1-push car-lhs
                                                     (logical-car const-val)
                                                     todo-list))
                   (todo-list (add-cnf-const-i1-push cdr-lhs
                                                     (logical-cdr const-val)
                                                     todo-list)))
              (mv-let
               ($sat state)
               (if (valid-varp consp-lhs)
                   (add-cnf-clause (cons consp-lhs cnf-lits) $sat state)
                 (mv $sat state))
               (add-cnf-const-i1-pop cnf-lits todo-list $sat state))))
           (t
            (add-cnf-const-not-consp lhs-var cnf-lits todo-list $sat state)))))))

;; Add clauses resulting from the fact that lhs-var is not a consp.  If
;; consp is relevant, it's just one clause.  Otherwise, we need to traverse
;; down the list structure.
(defun add-cnf-const-not-consp (lhs-var cnf-lits todo-list $sat state)
  (declare (xargs :stobjs $sat))
  (let ((consp-lhs (consp-vari lhs-var $sat)))
    (cond
     ((valid-varp consp-lhs)
      (mv-let
       ($sat state)
       (add-cnf-clause (cons (negate-f-expr consp-lhs) cnf-lits) $sat state)
       (let* ((car-lhs (car-vari lhs-var $sat))
              (cdr-lhs (cdr-vari lhs-var $sat))
              (todo-list (add-cnf-const-i1-push car-lhs
                                                nil
                                                todo-list))
              (todo-list (add-cnf-const-i1-push cdr-lhs
                                                nil
                                                todo-list)))
         (add-cnf-const-i1-pop cnf-lits todo-list $sat state))))
     (t
      (let* ((car-lhs (car-vari lhs-var $sat))
             (cdr-lhs (cdr-vari lhs-var $sat))
             (todo-list (add-cnf-const-i1-push car-lhs
                                               nil
                                               todo-list))
             (todo-list (add-cnf-const-i1-push cdr-lhs
                                               nil
                                               todo-list)))
        (add-cnf-const-i1-pop cnf-lits todo-list $sat state))))))

)

;; Add CNF clauses to represent the expression
;; lhs-var = const-val \/ cnf-lits
;; Where const-val is a constant value (i.e. unquoted constant).

(defun add-cnf-eq-i-var-const (lhs-var const-val cnf-lits $sat state)
  (declare (xargs :stobjs $sat))
  (add-cnf-const-i1 lhs-var const-val cnf-lits nil $sat state))

;; Add (bfix lhs-var) = (bfix rhs-var) \/ cnf-lits, if
;; (bfix lhs-var) is relevant.
;; (defun add-cnf-eq-eq-nil (lhs-var rhs-var cnf-lits $sat state)
;;   (declare (xargs :stobjs $sat))
;;   (let ((eq-nil-lhs (eq-nil-vari lhs-var $sat)))
;;     (if (valid-varp eq-nil-lhs)
;;         (mv-let
;;          (eq-nil-rhs $sat)
;;          (create-eq-nil-var rhs-var $sat)
;;          (add-cnf-iff eq-nil-lhs eq-nil-rhs cnf-lits $sat state))
;;       (mv $sat state))))

;; Add (consp lhs-var) = (consp rhs-var) \/ cnf-lits, if
;; (consp lhs-var) is relevant.
(defun add-cnf-eq-consp (lhs-var rhs-var cnf-lits $sat state)
  (declare (xargs :stobjs $sat))
  (let ((consp-lhs (consp-vari lhs-var $sat)))
    (if (valid-varp consp-lhs)
        (mv-let
         (consp-rhs $sat)
         (create-consp-var rhs-var $sat)
         (add-cnf-iff consp-lhs consp-rhs cnf-lits $sat state))
      (mv $sat state))))

;; Why add car-lhs if car is irrelevant???
(defun add-car-var (lhs-var rhs-var var-expr-list $sat)
  (declare (xargs :stobjs $sat))
  (let ((car-lhs (car-vari lhs-var $sat)))
    (if (valid-varp car-lhs)
        (mv-let
         (car-rhs $sat)
         (get-car-var rhs-var $sat)
         (mv (cons (cons car-lhs car-rhs) var-expr-list) $sat))
      (mv var-expr-list $sat))))

(defun add-cdr-var (lhs-var rhs-var var-expr-list $sat)
  (declare (xargs :stobjs $sat))
  (let ((cdr-lhs (cdr-vari lhs-var $sat)))
    (if (valid-varp cdr-lhs)
        (mv-let
         (cdr-rhs $sat)
         (get-cdr-var rhs-var $sat)
         (mv (cons (cons cdr-lhs cdr-rhs) var-expr-list) $sat))
      (mv var-expr-list $sat))))

;; f-expr represents a Boolean, such as (consp y).  Here we
;; add the relevant clauses for something like:
;; (eq x (consp y))
;; =>
;; Given (eq x a) is a relevant equality:
;; (consp y) -> (iff (eq x a) (eq a t))
;; (not (consp y)) -> (iff (eq x a) (eq a nil))
(defun add-cnf-eq-alist-f-var (eq-alist f-expr cnf-lits $sat state)
  (declare (xargs :stobjs $sat))
  (if (endp eq-alist)
      (mv $sat state)
    (let ((a (caar eq-alist))
          (eq-x-a (cdar eq-alist)))
      (mv-let
       (eq-a-t $sat)
       (eq-i-expr-to-f-expr a '(quote t) $sat)
       (mv-let
        (eq-a-nil $sat)
        (eq-i-expr-to-f-expr a '(quote nil) $sat)
        (mv-let
         ($sat state)
         (add-cnf-iff eq-x-a
                      eq-a-t
                      (cons (negate-f-expr f-expr) cnf-lits)
                      $sat
                      state)
         (mv-let
          ($sat state)
          (add-cnf-iff eq-x-a
                       eq-a-nil
                       (cons f-expr cnf-lits)
                       $sat
                       state)
          (add-cnf-eq-alist-f-var (cdr eq-alist)
                                  f-expr
                                  cnf-lits
                                  $sat
                                  state))))))))

;; lhs = (consp rhs) \/ cnf-lits
;; That means that we need (bfix lhs) = (consp rhs),
;; (consp lhs) = 'nil, (car lhs) = 'nil, and (car rhs) = 'nil.
;; (defun add-cnf-bfix-consp (lhs-var rhs-var cnf-lits $sat state)
;;   (declare (xargs :stobjs $sat))
;;   (mv-let
;;    ($sat state)
;;    (add-bfix-consp-clause lhs-var rhs-var cnf-lits $sat state)
;;    (mv-let
;;     ($sat state)
;;     (add-cnf-const (consp-vari lhs-var $sat) nil cnf-lits $sat state)
;;     (let* ((car-lhs (car-vari lhs-var $sat))
;;            (cdr-lhs (cdr-vari lhs-var $sat))

;;            (todo-list (if (not (valid-varp car-lhs)) nil
;;                              (list (cons car-lhs nil))))
;;            (todo-list (if (not (valid-varp cdr-lhs)) todo-list
;;                              (cons (cons cdr-lhs nil) todo-list))))
;;       (add-cnf-const-i1-pop cnf-lits todo-list $sat state)))))

;; lhs = f-var \/ cnf-lits
;; Where f-var is a final variable representing a Boolean.
;;
;; That means that we need (bfix lhs) = f-var,
;; (consp lhs) = 'nil, (car lhs) = 'nil, and (car rhs) = 'nil.
(defun add-cnf-eq-i-var-f-var (lhs-var f-var cnf-lits $sat state)
  (declare (xargs :stobjs $sat))
  (let ((atoms-alist (atoms-alist-vari lhs-var $sat))
        (eq-alist (eq-alist-vari lhs-var $sat)))
    (mv-let
     ($sat state)
     (add-cnf-eq-atoms-f-var atoms-alist f-var cnf-lits $sat state)
     (mv-let
      ($sat state)
      (add-cnf-eq-alist-f-var eq-alist f-var cnf-lits $sat state)
      (add-cnf-const-not-consp lhs-var cnf-lits nil $sat state)))))

;; (defun get-leaf-eq-list-push (eq-y-var rhs-expr todo-list)
;;   (cons (cons eq-y-var rhs-expr) todo-list))

;; (mutual-recursion
;; (defun get-leaf-eq-list-pop (todo-list leaf-eq-list $sat)
;;   (declare (xargs :stobjs $sat))
;;   (if (endp todo-list)
;;       (mv leaf-eq-list $sat)
;;     (get-leaf-eq-list (caar todo-list)
;;                       (cdar todo-list)
;;                       (cdr todo-list)
;;                       leaf-eq-list $sat)))

;; (defun get-leaf-eq-list (eq-y-var rhs-expr todo-list leaf-eq-list $sat)
;;   (declare (xargs :stobjs $sat))
;;   (cond
;;    ((and (consp rhs-expr) (eq 'cons (car rhs-expr)))
;;     (mv-let
;;      (car-var $sat)
;;      (get-car-var eq-y-var $sat)
;;      (mv-let
;;       (cdr-var $sat)
;;       (get-cdr-var eq-y-var $sat)
;;       (let* ((car-rhs-expr (cadr rhs-expr))
;;              (cdr-rhs-expr (caddr rhs-expr))
;;              (todo-list (get-leaf-eq-list-push car-var car-rhs-expr todo-list)))
;;         (get-leaf-eq-list cdr-var
;;                           cdr-rhs-expr
;;                           todo-list
;;                           leaf-eq-list
;;                           $sat)))))
;;    ((and (constp rhs-expr) (consp (unquote rhs-expr)))
;;     (mv-let
;;      (car-var $sat)
;;      (get-car-var eq-y-var $sat)
;;      (mv-let
;;       (cdr-var $sat)
;;       (get-cdr-var eq-y-var $sat)
;;       (let* ((car-rhs-expr `(quote ,(car (unquote rhs-expr))))
;;              (cdr-rhs-expr `(quote ,(cdr (unquote rhs-expr))))
;;              (todo-list (get-leaf-eq-list-push car-var car-rhs-expr todo-list)))
;;         (get-leaf-eq-list cdr-var
;;                           cdr-rhs-expr
;;                           todo-list
;;                           leaf-eq-list
;;                           $sat)))))
;;    (t
;;     (mv-let
;;      (eq-y-rhs-f-var $sat)
;;      (eq-i-expr-to-f-expr eq-y-var rhs-expr $sat)
;;      (get-leaf-eq-list-pop todo-list (cons eq-y-rhs-f-var leaf-eq-list) $sat)))))
;; )

;; Add the clause:
;; (eq x y) \/ (not (eq (car y) a)) \/ (not (eq (cdr y) b)) \/ c
;; (defun add-cons-implications-1 (leaf-eq-list cnf-lits $sat state)
;;   (declare (xargs :stobjs $sat))
;;   (if (endp leaf-eq-list)
;;       (add-cnf-clause cnf-lits $sat state)
;;     (add-cons-implications-1 (cdr leaf-eq-list)
;;                              (cons (negate-f-expr (car leaf-eq-list)) cnf-lits)
;;                              $sat
;;                              state)))

;; ;; Add the clauses:
;; ;;  (not (eq x y)) \/ (eq (car y) a) \/ c
;; ;;  (not (eq x y)) \/ (eq (car y) b) \/ c
;; (defun add-cons-implications-2 (leaf-eq-list cnf-lits $sat state)
;;   (declare (xargs :stobjs $sat))
;;   (if (endp leaf-eq-list)
;;       (mv $sat state)
;;     (mv-let
;;      ($sat state)
;;      (add-cnf-clause (cons (car leaf-eq-list) cnf-lits) $sat state)
;;      (add-cons-implications-2 (cdr leaf-eq-list) cnf-lits $sat state))))

;; (defun add-cons-implications (eq-x-y leaf-eq-list cnf-lits $sat state)
;;   (declare (xargs :stobjs $sat))
;;   (mv-let
;;    ($sat state)
;;    (add-cons-implications-1 leaf-eq-list (cons eq-x-y cnf-lits) $sat state)
;;    (add-cons-implications-2 leaf-eq-list (cons (negate-f-expr eq-x-y) cnf-lits) $sat state)))

;; (or (equal x (cons a b)) c)
;; =>
;;  (eq x y) \/ (not (eq (car y) a)) \/ (not (eq (cdr y) b)) \/ c
;;  (not (eq x y)) \/ (eq (car y) a) \/ c
;;  (not (eq x y)) \/ (eq (car y) b) \/ c

;; (defun add-cnf-eq-x-cons-a-b (eq-alist rhs-expr cnf-lits $sat state)
;;   (declare (xargs :stobjs $sat))
;;   (cond
;;    ((endp eq-alist)
;;     (mv $sat state))
;;    (t
;;     (mv-let
;;      (leaf-eq-list $sat)
;;      (get-leaf-eq-list (car (car eq-alist)) rhs-expr nil nil $sat)
;;      (mv-let
;;       ($sat state)
;;       (add-cons-implications (cdr (car eq-alist))
;;                              leaf-eq-list
;;                              cnf-lits
;;                              $sat
;;                              state)
;;       (add-cnf-eq-x-cons-a-b (cdr eq-alist) rhs-expr cnf-lits $sat state))))))

;; Given an intermediate clause:
;; (eq x y) \/ cnf-lits
;; for each equality (eq x a) add:
;; (eq x a) <-> (eq y a) \/ cnf-lits
(defun add-cnf-nc-eq-i-var (eq-alist rhs-var cnf-lits $sat state)
  (declare (xargs :stobjs $sat))
  (if (endp eq-alist)
      (mv $sat state)
    (let ((a (caar eq-alist))
          (eq-x-a (cdar eq-alist)))
      (mv-let
       (eq-y-a $sat)
       (eq-i-expr-to-f-expr a rhs-var $sat)
       (mv-let
        ($sat state)
        (add-cnf-iff eq-x-a eq-y-a cnf-lits $sat state)
        (add-cnf-nc-eq-i-var (cdr eq-alist)
                             rhs-var
                             cnf-lits
                             $sat
                             state))))))

;; Add CNF clauses to represent the expression
;; lhs-var = rhs-expr \/ cnf-lits
;; rhs-expr can contain calls of cons, i-vars, and constants.

;; The var-expr-list holds (lhs . rhs) pairs that also need to
;; be dealt with.

(mutual-recursion
(defun add-cnf-eq1-pop (cnf-lits var-expr-list $sat state)
  (declare (xargs :stobjs $sat))
  (if (endp var-expr-list)
      (mv $sat state)
    (let* ((var-expr (car var-expr-list))
           (var-expr-list (cdr var-expr-list))
           (lhs-var (car var-expr))
           (rhs-expr (cdr var-expr)))
      (add-cnf-eq1 lhs-var rhs-expr cnf-lits var-expr-list $sat state))))

(defun add-cnf-eq1 (lhs-var rhs-expr cnf-lits var-expr-list $sat state)
  (declare (xargs :stobjs $sat))
  (cond
   ((atom rhs-expr)
    ;;(let ((eq-f-var (lookup-eq-var lhs-var rhs-expr $sat)))
    ;;  (cond
    ;;   ((valid-varp eq-f-var)
    ;;    ;; We have a variable representing (eq lhs-var rhs-expr)
    ;;    (mv-let
    ;;     ($sat state)
    ;;     (add-cnf-clause (cons eq-f-var cnf-lits) $sat state)
    ;;     (add-cnf-eq1-pop cnf-lits var-expr-list $sat state)))
    ;;   (t
        (mv-let
         ($sat state)
         (add-cnf-eq-atoms-i-var (atoms-alist-vari lhs-var $sat)
                                 rhs-expr
                                 cnf-lits
                                 $sat
                                 state)
         (mv-let
          ($sat state)
          (add-cnf-nc-eq-i-var (eq-alist-vari lhs-var $sat)
                               rhs-expr
                               cnf-lits
                               $sat
                               state)
          (mv-let
           ($sat state)
           (add-cnf-eq-consp lhs-var rhs-expr cnf-lits $sat state)
           (mv-let
            (var-expr-list $sat)
            (add-car-var lhs-var rhs-expr var-expr-list $sat)
            (mv-let
             (var-expr-list $sat)
             (add-cdr-var lhs-var rhs-expr var-expr-list $sat)
             (add-cnf-eq1-pop cnf-lits var-expr-list $sat state)))))))

   ((quotep rhs-expr)
    (mv-let
     ($sat state)
     (add-cnf-eq-i-var-const lhs-var (unquote rhs-expr) cnf-lits $sat state)
     (add-cnf-eq1-pop cnf-lits var-expr-list $sat state)))

   ((eq 'consp (car rhs-expr))
      (if (not (valid-Booleanp lhs-var $sat))
          ;; If there's no valid Boolean, then all we need to
          ;; state is that lhs-var is not a consp.
          (add-cnf-const-not-consp lhs-var
                                   cnf-lits
                                   nil
                                   $sat
                                   state)
        (mv-let
         (rhs-f-var $sat)
         (create-consp-var (cadr rhs-expr) $sat)
         (add-cnf-eq-i-var-f-var lhs-var
                                 rhs-f-var
                                 cnf-lits
                                 $sat
                                 state))))

   ((eq (car rhs-expr) 'equal)
    (if (and (not (valid-Booleanp lhs-var $sat))
             (not (eq-alist-vari lhs-var $sat)))
        ;; We don't need to look at the right hand side, to know
        ;; it's a Boolean atom.
        (add-cnf-eq-i-var-f-var lhs-var
                                0
                                cnf-lits
                                $sat
                                state)
      (mv-let
       (rhs-f-expr $sat)
       (i-expr-to-f-expr rhs-expr $sat)
       (cond
        ((constp rhs-f-expr)
         (add-cnf-eq-i-var-const lhs-var
                                 (unquote rhs-f-expr)
                                 cnf-lits
                                 $sat
                                 state))
        (t
         (add-cnf-eq-i-var-f-var lhs-var
                                 rhs-f-expr
                                 cnf-lits
                                 $sat
                                 state))))))

   ;; I plan on making this case impossible!!!
   ;; This case is now impossible, since we break up
   ;; conses in ts-add-iete-entry!
   ;; ((eq (car rhs-expr) 'cons)
;;     (let* ((atoms-lhs (atoms-alist-vari lhs-var $sat))
;;            (eq-alist (eq-alist-vari lhs-var $sat))

;;            (consp-lhs (consp-vari lhs-var $sat))
;;            (car-lhs (car-vari lhs-var $sat))
;;            (cdr-lhs (cdr-vari lhs-var $sat))

;;            (car-rhs (cadr rhs-expr))
;;            (cdr-rhs (caddr rhs-expr))

;;            (var-expr-list (if (not (valid-varp car-lhs)) var-expr-list
;;                             (cons (cons car-lhs car-rhs) var-expr-list)))
;;            (var-expr-list (if (not (valid-varp cdr-lhs)) var-expr-list
;;                             (cons (cons cdr-lhs cdr-rhs) var-expr-list))))
;;       (mv-let
;;        ($sat state)
;;        (add-cnf-eq-x-cons-a-b eq-alist rhs-expr cnf-lits $sat state)
;;        (mv-let
;;         ($sat state)
;;         (add-cnf-eq-atoms-off atoms-lhs cnf-lits $sat state)
;;         (mv-let
;;          ($sat state)
;;          (if (valid-varp consp-lhs)
;;              (add-cnf-iff-const consp-lhs t cnf-lits $sat state)
;;            (mv $sat state))
;; (add-cnf-eq1-pop cnf-lits var-expr-list $sat state))))))

   (t
    (prog2$ (er hard 'add-cnf-list-expr1
                "Unrecognized function symbol:~x0~%"
                (car rhs-expr))
            (mv $sat state)))))
)

(defun add-cnf-eq-i-var-i-expr (lhs-var rhs-expr cnf-lits $sat state)
  (declare (xargs :stobjs $sat))
   (add-cnf-eq1 lhs-var rhs-expr cnf-lits nil $sat state))

(mutual-recursion
(defun todo-to-cnf-pop (ate-list t-struct $sat state)
  (declare (xargs :stobjs $sat))
  (if (endp ate-list)
      (mv t-struct $sat state)
    (todo-to-cnf (car ate-list)
                 (cdr ate-list)
                 t-struct
                 $sat
                 state)))

(defun todo-to-cnf (at-entry ate-list t-struct $sat state)
  (declare (xargs :stobjs $sat))
  (cond
   ((atom (ate-expr at-entry))
    (mv-let
     (expr $sat)
     (add-accessors (ate-accessor-list at-entry)
                    (cdr (assoc-eql (ate-expr at-entry) (ate-alist at-entry)))
                    $sat)
     (mv-let
      (t-struct $sat)
      (ts-add-ite-entry expr (ate-cnf-lits at-entry) t-struct $sat)
      (todo-to-cnf-pop ate-list t-struct $sat state))))
   (t
    (let ((fn (car (ate-expr at-entry)))
          (args (cdr (ate-expr at-entry))))
      (cond
       ((eq 'i-expression fn)
        (mv-let
         (expr $sat)
         (add-accessors (ate-accessor-list at-entry)
                        (car args)
                        $sat)
         (mv-let
          (t-struct $sat)
          (ts-add-ite-entry expr (ate-cnf-lits at-entry) t-struct $sat)
          (todo-to-cnf-pop ate-list t-struct $sat state))))
       ((eq 'quote fn)
        (let ((val (eval-const-accessors (ate-accessor-list at-entry)
                                         (car args))))
         (mv-let
          (t-struct $sat)
          (ts-add-ite-entry `(quote ,val) (ate-cnf-lits at-entry) t-struct $sat)
          (todo-to-cnf-pop ate-list t-struct $sat state))))
       ((eq 'if fn)
        (let ((cond-expr (car args))
              (true-br (cadr args))
              (false-br (caddr args)))
          (mv-let
           (cond-expr $sat state)
           (remove-functions cond-expr
                             (ate-update-accessor-list nil at-entry)
                             $sat
                             state)
           (mv-let
            (cond-f-var $sat)
            (i-expr-to-f-expr cond-expr $sat)
            (cond
             ((eq cond-f-var *f-true*)
              ;; The condition is true
              (todo-to-cnf (ate-update-expr true-br at-entry)
                           ate-list
                           t-struct
                           $sat
                           state))
             ((eq cond-f-var *f-false*)
              ;; The condition is false
              (todo-to-cnf (ate-update-expr false-br at-entry)
                           ate-list
                           t-struct
                           $sat
                           state))
             (t (let* ((true-br-entry (ate-add-lit (negate-f-expr cond-f-var)
                                                  (ate-update-expr true-br at-entry)))
                       (ate-list (cons true-br-entry ate-list))
                       (false-br-entry (ate-add-lit cond-f-var
                                                   (ate-update-expr false-br at-entry))))
                  (todo-to-cnf false-br-entry
                               ate-list
                               t-struct
                               $sat
                               state))))))))

       ((or (eq 'car fn)
            (eq 'cdr fn))
        ;; Expr is a list accessor, add it to the accessor list
        (todo-to-cnf (ate-update-expr (car args) (ate-add-accessor fn at-entry))
                     ate-list
                     t-struct
                     $sat
                     state))

       ((eq 'consp fn)
        ;; expr is a consp---
        ;; Note that we consider consp an accessor, but it better be
        ;; at the top-level (car (consp x))=nil, (consp (consp x))=nil.
        ;; (bfix (consp x)) = (consp x)
        (let ((accessor-list (ate-accessor-list at-entry)))
          (cond
           ((endp accessor-list)
            (todo-to-cnf (ate-update-expr (car args)
                                         (ate-update-accessor-list '(consp)
                                                                  at-entry))
                         ate-list
                         t-struct
                         $sat
                         state))
           (t
            (mv-let
             (t-struct $sat)
             (ts-add-ite-entry '(quote nil) (ate-cnf-lits at-entry) t-struct $sat)
             (todo-to-cnf-pop ate-list t-struct $sat state))))))

       ((eq 'cons fn)
        ;; Expr is a cons, try to simplify it using the accessor
        ;; list.  If that doesn't work, simplify the leaves and
        ;; cons them together.
        (let ((car-expr (car args))
              (cdr-expr (cadr args)))
          (mv-let
           (acc at-entry)
           (ate-pop-accessor at-entry)
           (cond
            ((eq acc 'car)
             (todo-to-cnf (ate-update-expr car-expr at-entry)
                          ate-list
                          t-struct
                          $sat
                          state))
            ((eq acc 'cdr)
             (todo-to-cnf (ate-update-expr cdr-expr at-entry)
                          ate-list
                          t-struct
                          $sat
                          state))
            ((eq acc 'consp)
             (mv-let
              (t-struct $sat)
              (ts-add-ite-entry '(quote t) (ate-cnf-lits at-entry) t-struct $sat)
              (todo-to-cnf-pop ate-list t-struct $sat state)))
            ((eq acc nil)
             (let* ((ate-car (ate-update-expr car-expr at-entry))
                    (ate-cdr (ate-update-expr cdr-expr at-entry))
                    (car-t-struct (make-todo-struct (list ate-car) nil nil))
                    (cdr-t-struct (make-todo-struct (list ate-cdr) nil nil)))
               (mv-let
                (t-struct $sat)
                (ts-add-cet-entry car-t-struct
                                  cdr-t-struct
                                  (ate-cnf-lits at-entry)
                                  t-struct
                                  $sat)
                (todo-to-cnf-pop ate-list t-struct $sat state))))
            (t
             (prog2$
              (er hard 'todo-to-cnf "Unrecognized accessor:~x0~%" acc)
              (mv t-struct $sat state)))))))

       ((eq 'equal fn)
        ;; expr is an equal
        (let* ((accessor-list (ate-accessor-list at-entry)))
          (cond
           ((consp accessor-list)
            ;; (car (equal x y)), (cdr (equal x y)), and (consp (equal x y)) are
            ;; all nil
            (mv-let
             (t-struct $sat)
             (ts-add-ite-entry '(quote nil) (ate-cnf-lits at-entry) t-struct $sat)
             (todo-to-cnf-pop ate-list t-struct $sat state)))
           (t
            (mv-let
             (expr $sat state)
             (remove-functions (ate-expr at-entry) at-entry $sat state)
             (mv-let
              (t-struct $sat)
              (ts-add-ite-entry expr (ate-cnf-lits at-entry) t-struct $sat)
              (todo-to-cnf-pop ate-list t-struct $sat state)))))))

       (t
        ;; expr is a call to an unknown primitive or a user-defined
        ;; function.  If it's constant---evaluate!  If it's an irrelevant
        ;; recursive call, remove it!  Otherwise, open it.
        (mv-let
         (constp args $sat state)
         (remove-functions-list t
                                args
                                (ate-update-accessor-list nil at-entry)
                                nil
                                $sat
                                state)
         (cond
          ((uninterpreted-fnp fn $sat state)
           (mv-let
            (var $sat)
            (new-un-func fn args $sat)
            (mv-let
             (expr $sat)
             (add-accessors (ate-accessor-list at-entry) var $sat)
             (mv-let
              (t-struct $sat)
              (ts-add-ite-entry expr (ate-cnf-lits at-entry) t-struct $sat)
              (todo-to-cnf-pop ate-list t-struct $sat state)))))
          (constp
           (mv-let
            (erp val state)
            (simple-translate-and-eval (cons fn args)
                                       nil
                                       nil
                                       "SAT internal evaluator"
                                       "remove-functions?"
                                       (w state)
                                       state
                                       nil) ; see comment above about aok
            (if erp
                (prog2$
                 (er hard
                     'todo-to-cnf
                     "Unable to evaluate expression: ~x0~%"
                     (cons fn args))
                 (mv t-struct $sat state))
              (mv-let
               (t-struct $sat)
               (ts-add-ite-entry `(quote ,(eval-const-accessors (ate-accessor-list at-entry)
                                                                (cdr val)))
                                 (ate-cnf-lits at-entry)
                                 t-struct
                                 $sat)
               (todo-to-cnf-pop ate-list t-struct $sat state)))))

          (t
           (mv-let
            (irrelevantp state)
            (irrelevant-recursionp fn
                                   args
                                   at-entry
                                   state)
            (cond
             (irrelevantp
              ;; An irrelevant recursive call
              (todo-to-cnf-pop ate-list t-struct $sat state))
             (t
              ;; open up the user-defined function
              (let ((at-entry (ate-update-alist (add-to-alist (fn-formals fn state)
                                                               args
                                                               nil)
                                                 at-entry)))
                (mv-let
                 (at-entry state)
                 (update-recursion fn args at-entry state)
                 ;; open up the user-defined function
                 (todo-to-cnf (ate-update-expr (fn-body fn state)
                                               at-entry)
                              ate-list
                              t-struct
                              $sat
                              state)))))))))))))))
)

(defun eq-todo-to-cnf-eq-alist1 (i0 $sat state)
  (declare (xargs :stobjs $sat))
  (mv-let
   (i1 eq-i0-i1 $sat)
   (pop-eq-alist-entry i0 $sat)
   (cond
    ((not (valid-varp i1))
     (mv $sat state))
    (t
     (mv-let
      ($sat state)
      (make-neq-cnf i0 i1 eq-i0-i1 $sat state)
      (mv-let
       ($sat state)
       (add-cnf-eq-i-var-i-expr i0 i1 (list (negate-f-expr eq-i0-i1)) $sat state)
       (eq-todo-to-cnf-eq-alist1 i0 $sat state)))))))

(defun eq-todo-to-cnf-eq-alist (i0 $sat state)
  (declare (xargs :stobjs $sat))
  (let ((eq-alist (eq-alist-vari i0 $sat)))
    (mv-let
     ($sat state)
     (eq-todo-to-cnf-eq-alist1 i0 $sat state)
     (let (($sat (update-eq-alist-vari i0 eq-alist $sat)))
       (mv $sat state)))))

(defun eq-todo-to-cnf-atoms-alist (i0 $sat state)
  (declare (xargs :stobjs $sat))
  (mv-let
   (a eq-i0-a $sat)
   (pop-eq-atom-entry i0 $sat)
   (cond
    ((not (valid-varp eq-i0-a))
     (mv $sat state))
    (t
     (mv-let
      ($sat state)
      (add-cnf-eq-i-var-const i0 a (list (negate-f-expr eq-i0-a)) $sat state)
      (eq-todo-to-cnf-atoms-alist i0 $sat state))))))

(defun eq-todo-to-cnf-consp (i0 $sat state)
  (declare (xargs :stobjs $sat))
  (let ((consp-i0 (consp-vari i0 $sat)))
    (cond
     ((not (valid-varp consp-i0))
      (mv $sat state))
     (t
      (let* ((car-i0 (car-vari i0 $sat))
             (cdr-i0 (cdr-vari i0 $sat))
             (todo-list (add-cnf-const-i1-push car-i0 nil nil))
             (todo-list (add-cnf-const-i1-push cdr-i0 nil todo-list)))
        (add-cnf-const-i1-pop (list consp-i0) todo-list $sat state))))))

;; Handle new equality traversal
(defun eq-todo-to-cnf (top var $sat state)
  (declare (xargs :stobjs $sat))
  (cond
   ((not (valid-varp var))
    ;;(or (not (valid-varp var))
    ;;    (irrelevant-ivarp var $sat))
    (mv $sat state))
   ((not top)
    ;; We can rely on the definitions to filter down leaves
    (mv $sat state))
   (t
    ;; First we traverse the root, then the cdr, then the car
    ;; ---not quite what we say we do in traverse-prior!
    ;; This should be fixed!!!
    ;; Also, I may need to mess with my counter-example generation
    ;; algorithm, since it also needs to use the correct order.
    (let ((eq-alist (eq-alist-vari var $sat))
          (atoms-alist (atoms-alist-vari var $sat)))
      (mv-let
       ($sat state)
       (eq-todo-to-cnf-eq-alist var $sat state)
       (mv-let
        ($sat state)
        (eq-todo-to-cnf-atoms-alist var $sat state)
        (mv-let
         ($sat state)
         (eq-todo-to-cnf-consp var $sat state)
         (let* (($sat (update-eq-alist-vari var eq-alist $sat))
                ($sat (update-atoms-alist-vari var atoms-alist $sat)))
           (mv-let
            ($sat state)
            (eq-todo-to-cnf top (cdr-vari var $sat) $sat state)
            (mv-let
             ($sat state)
             (eq-todo-to-cnf top (car-vari var $sat) $sat state)
             (mv $sat state)))))))))))

(defun iete-list-to-cnf (lhs-var iete-list $sat state)
  (declare (xargs :stobjs $sat))
  (cond
   ((endp iete-list)
    (mv $sat state))
   (t
    (mv-let
     ($sat state)
     (add-cnf-eq-i-var-i-expr lhs-var
                              (iete-expr (car iete-list))
                              (iete-cnf-lits (car iete-list))
                              $sat
                              state)
     (iete-list-to-cnf lhs-var (cdr iete-list) $sat state)))))

;; For (equal i0 (cons i1 i2)):

;; -------------------------------------------------------------------------------------
;; Move to neq-implication.lisp ???

(defun compute-cete-eq-disj-iet-entry (i0 iet-entry $sat state)
  (declare (xargs :stobjs $sat))
  (let ((expr (iete-expr iet-entry))
        (cnf-lits (iete-cnf-lits iet-entry)))
    (mv-let
     (eq-i0-expr $sat)
     (eq-i-expr-to-f-expr i0 expr $sat)
     (let* ((conj (conj-from-cnf-lits cnf-lits))
            (conj (add-conjunct eq-i0-expr conj)))
       (mv (singleton-disjunct conj) $sat state)))))

(defun compute-cete-eq-disj-iete-list (i0 iete-list ans $sat state)
  (declare (xargs :stobjs $sat))
  (cond
   ((endp iete-list)
    (mv ans $sat state))
   (t
    (mv-let
     (iete-disj $sat state)
     (compute-cete-eq-disj-iet-entry i0 (car iete-list) $sat state)
     (compute-cete-eq-disj-iete-list i0
                                     (cdr iete-list)
                                     (merge-or iete-disj ans)
                                     $sat
                                     state)))))

(mutual-recursion
(defun compute-cete-eq-disj-cete-list (i0 cete-list ans $sat state)
  (declare (xargs :stobjs $sat))
  (cond
   ((endp cete-list)
    (mv ans $sat state))
   (t
    (mv-let
     (cete-disj $sat state)
     (compute-cete-eq-disj i0 (car cete-list) $sat state)
     (compute-cete-eq-disj-cete-list i0
                                     (cdr cete-list)
                                     (merge-or cete-disj ans)
                                     $sat
                                     state)))))

(defun compute-cete-eq-disj-t-struct (i0 t-struct $sat state)
  (declare (xargs :stobjs $sat))
  (mv-let
   (iete-disj $sat state)
   (compute-cete-eq-disj-iete-list i0
                                   (ts-iete-list t-struct)
                                   (empty-disjunct)
                                   $sat
                                   state)
   (compute-cete-eq-disj-cete-list i0 (ts-cete-list t-struct) iete-disj $sat state)))

;; Compute a DNF expression that implies (eq i0 (cons i1 i2), where
;; (cons i1 i2) is the expression represented by cet-entry.
(defun compute-cete-eq-disj (i0 cet-entry $sat state)
  (declare (xargs :stobjs $sat))
  (mv-let
   (car-i0 $sat)
   (get-car-var i0 $sat)
   (mv-let
    (cdr-i0 $sat)
    (get-cdr-var i0 $sat)
    (mv-let
     (consp-i0 $sat)
     (create-consp-var i0 $sat)
     (mv-let
      (car-disj $sat state)
      (compute-cete-eq-disj-t-struct car-i0 (cete-car cet-entry $sat) $sat state)
      (mv-let
       (cdr-disj $sat state)
       (compute-cete-eq-disj-t-struct cdr-i0 (cete-cdr cet-entry $sat) $sat state)
       (mv-let
        (disj $sat state)
        (merge-and (singleton-disjunct (singleton-conjunct consp-i0))
                   car-disj
                   $sat
                   state)
        (merge-and disj cdr-disj $sat state))))))))
)

;; Add that (eq (car i0) i1) /\ (eq (cdr i0) i2) /\ (consp i0) -> eq-i0-cons-i1-i2
(defun cete-neq-implication (i0 eq-i0-cons-i1-i2 cet-entry $sat state)
  (declare (xargs :stobjs $sat))
  (mv-let
   (disj $sat state)
   (compute-cete-eq-disj i0 cet-entry $sat state)
   (add-cnf-disjunct-implication eq-i0-cons-i1-i2 disj $sat state)))

;; -------------------------------------------------------------------------------------

(defun cete-eq-implication-iete-list (i0 y0 iete-list $sat state)
  (declare (xargs :stobjs $sat))
  (cond
   ((endp iete-list)
    (mv $sat state))
   (t
    (let* ((iet-entry (car iete-list))
           (i-expr (iete-expr iet-entry))
           (cnf-lits (iete-cnf-lits iet-entry)))
      (mv-let
       (eq-i0-i1 $sat)
       (eq-i-expr-to-f-expr i0 i-expr $sat)
       (mv-let
        ($sat state)
        (add-cnf-clause (list* eq-i0-i1 (negate-f-expr y0) cnf-lits) $sat state)
        (cete-eq-implication-iete-list i0 y0 (cdr iete-list) $sat state)))))))

(mutual-recursion
(defun cete-eq-implication-cete-list (i0 y0 cete-list $sat state)
  (declare (xargs :stobjs $sat))
  (cond
   ((endp cete-list)
    (mv $sat state))
   (t
    (mv-let
     ($sat state)
     (cete-eq-implication i0 y0 (car cete-list) $sat state)
     (cete-eq-implication-cete-list i0 y0 (cdr cete-list) $sat state)))))

;; Adding that y0 -> (eq i0 i1) for all i1 represented in the
;; t-struct.
(defun cete-eq-implication (i0 y0 cet-entry $sat state)
  (declare (xargs :stobjs $sat))
  (let* ((cete-car (cete-car cet-entry $sat))
         (cete-cdr (cete-cdr cet-entry $sat))
         (cnf-lits (cete-cnf-lits cet-entry $sat))

         (iete-list-car (ts-iete-list cete-car))
         (iete-list-cdr (ts-iete-list cete-cdr))
         (cete-list-car (ts-cete-list cete-car))
         (cete-list-cdr (ts-cete-list cete-cdr)))
    (mv-let
     (consp-var $sat)
     (create-consp-var i0 $sat)
     (mv-let
      ($sat state)
      (add-cnf-clause (list* consp-var (negate-f-expr y0) cnf-lits) $sat state)
      (mv-let
       (car-i0 $sat)
       (get-car-var i0 $sat)
       (mv-let
        (cdr-i0 $sat)
        (get-cdr-var i0 $sat)
        (mv-let
         ($sat state)
         (cete-eq-implication-iete-list car-i0 y0 iete-list-car $sat state)
         (mv-let
          ($sat state)
          (cete-eq-implication-cete-list car-i0 y0 cete-list-car $sat state)
          (mv-let
           ($sat state)
           (cete-eq-implication-iete-list cdr-i0 y0 iete-list-cdr $sat state)
           (cete-eq-implication-cete-list cdr-i0 y0 cete-list-cdr $sat state))))))))))
)

(mutual-recursion
;; Note: Candidate for tail-recursive optimization
(defun simplify-all-cete-list (cete-list $sat state)
  (declare (xargs :stobjs $sat))
  (cond
   ((endp cete-list)
    (mv $sat state))
   (t
    (let* ((cet-entry (car cete-list))
           (car-t-struct (cete-car cet-entry $sat))
           (cdr-t-struct (cete-cdr cet-entry $sat)))
      (mv-let
       (car-t-struct $sat state)
       (simplify-all-acl2-expressions car-t-struct $sat state)
       (mv-let
        (cdr-t-struct $sat state)
        (simplify-all-acl2-expressions cdr-t-struct $sat state)
        (let* (($sat (cete-update-car-cdr car-t-struct
                                          cdr-t-struct
                                          cet-entry
                                          $sat)))
          (simplify-all-cete-list (cdr cete-list)
                                  $sat
                                  state))))))))

(defun simplify-all-acl2-expressions (t-struct $sat state)
  (declare (xargs :stobjs $sat))
  (let* ((ate-list (ts-ate-list t-struct))
         (t-struct (ts-update-ate-list nil t-struct)))
    (mv-let
     (t-struct $sat state)
     (todo-to-cnf-pop ate-list t-struct $sat state)
     (mv-let
      ($sat state)
      (simplify-all-cete-list (ts-cete-list t-struct) $sat state)
      (mv t-struct $sat state)))))

(defun cete-eq-implications (eq-alist cet-entry $sat state)
  (declare (xargs :stobjs $sat))
  (cond
   ((endp eq-alist)
    (mv $sat state))
   (t
    (let ((i0 (caar eq-alist))
          (eq-i0-cons-i1-i2 (cdar eq-alist)))
      (mv-let
       ($sat state)
       (cete-eq-implication i0 eq-i0-cons-i1-i2 cet-entry $sat state)
      (mv-let
       ($sat state)
       (cete-neq-implication i0 eq-i0-cons-i1-i2 cet-entry $sat state)
       (cete-eq-implications (cdr eq-alist)
                             cet-entry
                             $sat
                             state)))))))

;; Note: Candidate for tail-recursive optimization
(defun cet-entry-to-cnf (lhs-var cet-entry $sat state)
  (declare (xargs :stobjs $sat))
  (let* ((car-t-struct (cete-car cet-entry $sat))
         (cdr-t-struct (cete-cdr cet-entry $sat))

         (cnf-lits (cete-cnf-lits cet-entry $sat))
         (atoms-lhs (atoms-alist-vari lhs-var $sat))

         (consp-lhs (consp-vari lhs-var $sat))
         (car-lhs (car-vari lhs-var $sat))
         (cdr-lhs (cdr-vari lhs-var $sat)))
    (mv-let
     ($sat state)
     (add-cnf-eq-atoms-off atoms-lhs cnf-lits $sat state)
     (mv-let
      ($sat state)
      (if (valid-varp consp-lhs)
          (add-cnf-iff-const consp-lhs t cnf-lits $sat state)
        (mv $sat state))
      (mv-let
       (car-t-struct $sat state)
       (traverse-var nil car-lhs car-t-struct $sat state)
       (mv-let
        (cdr-t-struct $sat state)
        (traverse-var nil cdr-lhs cdr-t-struct $sat state)
        (mv-let
         (cet-entry $sat)
         (make-cons-expr-todo-entry car-t-struct cdr-t-struct cnf-lits $sat)
         (declare (ignore cet-entry))
         (mv $sat state))))))))

(defun cete-list-to-cnf (lhs-var cete-list $sat state)
  (declare (xargs :stobjs $sat))
  (cond
   ((endp cete-list)
    (mv $sat state))
   (t
    (mv-let
     ($sat state)
     (cet-entry-to-cnf lhs-var (car cete-list) $sat state)
     (cete-list-to-cnf lhs-var
                       (cdr cete-list)
                       $sat
                       state)))))

(defun cete-list-eq-implications (eq-alist cete-list $sat state)
  (declare (xargs :stobjs $sat))
  (cond
   ((endp cete-list)
    (mv $sat state))
   (t
    (mv-let
     ($sat state)
     (cete-eq-implications eq-alist (car cete-list) $sat state)
     (cete-list-eq-implications eq-alist (cdr cete-list) $sat state)))))

(defun cons-eq-implications (eq-alist t-struct $sat state)
  (declare (xargs :stobjs $sat))
  (cond
   ((endp eq-alist)
    (mv t-struct $sat state))
   (t
    (mv-let
     (t-struct $sat state)
     (simplify-all-acl2-expressions t-struct $sat state)
     (mv-let
      ($sat state)
      (cete-list-eq-implications eq-alist (ts-cete-list t-struct) $sat state)
      (mv t-struct $sat state))))))

(defun traverse-var (top var t-struct $sat state)
  (declare (xargs :stobjs $sat))
  (cond
   ((not (valid-varp var))
    (mv t-struct $sat state))
   (t
    ;; Note that it's important for eq-todo-to-cnf to
    ;; occur first since (eq (cdr i0) (car i0)) might
    ;; add relevant entries to (car i0).  It's similarly
    ;; important that in the iete-list we don't ever see
    ;; (car i0) when traversing (cdr i0)!

    ;; I really ought to clean up this mess by stictly traversing
    ;; the cdr, then the car, then the top level, keeping
    ;; track of higher-level eq-alists as I go....
    (mv-let
     ($sat state)
     (eq-todo-to-cnf top var $sat state)
     (let* ((ate-list (ts-ate-list t-struct))
            (t-struct (ts-update-ate-list nil t-struct)))
       (mv-let
        (t-struct $sat state)
        (todo-to-cnf-pop ate-list t-struct $sat state)
        (mv-let
         ($sat state)
         (iete-list-to-cnf var (ts-iete-list t-struct) $sat state)
         (mv-let
          ($sat state)
          (cete-list-to-cnf var (ts-cete-list t-struct) $sat state)
          (mv-let
           (t-struct $sat state)
           (cons-eq-implications (eq-alist-vari var $sat) t-struct $sat state)
           (mv t-struct $sat state))))))))))
)

;; Before traversing a variable we add some extra consp-var
;; entries that might be needed.
;; Note: Candidate for tail-recursive optimization!!
(defun add-extra-consp-vars (var need-consp-var $sat)
  (declare (xargs :stobjs $sat))
  (cond
   ((not (valid-varp var))
    $sat)
   (need-consp-var
    (mv-let
     (consp-var $sat)
     (create-consp-var var $sat)
     (declare (ignore consp-var))
     (let (($sat (add-extra-consp-vars (car-vari var $sat) t $sat)))
       (add-extra-consp-vars (cdr-vari var $sat) t $sat))))
   ;;((irrelevant-ivarp var $sat)
   ;; $sat)
   ((eq nil (eq-alist-vari var $sat))
    (let (($sat (add-extra-consp-vars (car-vari var $sat) nil $sat)))
      (add-extra-consp-vars (cdr-vari var $sat) nil $sat)))
   ((or (valid-varp (car-vari var $sat))
        (valid-varp (car-vari var $sat)))
    (mv-let
     (consp-var $sat)
     (create-consp-var var $sat)
     (declare (ignore consp-var))
     (let (($sat (add-extra-consp-vars (car-vari var $sat) t $sat)))
       (add-extra-consp-vars (cdr-vari var $sat) t $sat))))
   (t
    $sat)))

(defun traverse-vars ($sat state)
  (declare (xargs :stobjs $sat))
  (mv-let
   (top var $sat)
   (pop-traversal-var $sat)
   (cond
    ((not (valid-varp var))
     (mv $sat state))
    ((irrelevant-ivarp var $sat)
     (traverse-vars $sat state))
    (t
     (let (($sat (add-extra-consp-vars var nil $sat)))
       (mv-let
        (t-struct $sat state)
        (traverse-var top var (todo-structi var $sat) $sat state)
        (let* (($sat (mark-ivar-irrelevant var $sat))
               ($sat (update-todo-structi var t-struct $sat)))
          (traverse-vars $sat state))))))))

(defun push-defined-list-onto-stack (var-list $sat)
  (declare (xargs :stobjs $sat))
  (cond
   ((endp var-list)
    $sat)
   (t
    (let (($sat (push-defined-traversal-var (car var-list) $sat)))
      (push-defined-list-onto-stack (cdr var-list) $sat)))))

(defun push-top-list-onto-stack (var-list $sat)
  (declare (xargs :stobjs $sat))
  (cond
   ((endp var-list)
    $sat)
   (t
    (let (($sat (push-top-traversal-var (car var-list) $sat)))
      (push-top-list-onto-stack (cdr var-list) $sat)))))

(defun convert-to-cnf ($sat state)
  (declare (xargs :stobjs $sat))
  (cond
   ((not (need-more-traversals $sat))
    (mv $sat state))
   (t
    (let* (($sat (update-need-more-traversals nil $sat))
           ($sat (update-completed-var-list nil $sat))
           ($sat (update-top-completed-var-list nil $sat))
           ($sat (update-traversal-number 0 $sat)))
      (mv-let
       ($sat state)
       (traverse-vars $sat state)
       ;; Once we've completed the traversal, we recreate the stack
       ;; so that others can push entries safely onto the top.
       ;;
       ;; Note that the completed list will remain a list of
       ;; variables seen in the last traversal until another
       ;; traversal begins.
       (let* ((completed-var-list (completed-var-list $sat))
              (top-completed-var-list (top-completed-var-list $sat))

              ($sat (update-var-stack nil $sat))
              ($sat (update-top-var-stack nil $sat))
              ($sat (update-stack-number 0 $sat))

              ($sat (push-defined-list-onto-stack completed-var-list $sat))
              ($sat (push-top-list-onto-stack top-completed-var-list $sat)))

         (convert-to-cnf $sat state)))))))

