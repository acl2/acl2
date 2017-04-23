
;; Ordering:  Currently the ordering I use is based on when a variable
;; is created.  This ordering doesn't work in the presence of a (ideal)
;; hash-table optimization however.  The only ordering I've come up with
;; so far that would work is to give precedence to a variable with an
;; older function symbol, with ties going to the second oldest function
;; symbol, and so on with precedence to variables with more functions.
;;
;; I can also create an ordering where any expression that calls input
;; x2 is bigger than one that just uses x1 and x0, etc.  Then I order
;; the variables created from expressions of x2 in a similar manner, giving
;; precedence to newer functions.  The problem with this ordering is
;; it's really difficult to keep track of.  If I use a number, then
;; every time I insert a new expression (say one shows up involving just x1),
;; I need to add 1 to all greater expressions.  If I had a good way
;; of comparing real numbers, I could do it, but that's not really
;; a solution.  I guess you could number a new expression as half
;; way in between it and the next number, then occasionally fix the
;; whole mess.

;; Todo:
;; 1) get everything working except convert-to-cnf
;; 2) call the local clause simplifier!

;; The SAT-based decision procedure for SULFA

;; !! Maybe I should remove the output.sexpr file after reading it.

(in-package "SAT")

(program)
(set-state-ok t)

(include-book "sulfa-dir-const")
(include-book "user-entry-data-structure")
(include-book "convert-to-cnf")
(include-book "check-output")
(include-book "recognizer")
;;(include-book "../external/external")

;; ---------------- Problem Phase ---------------------
;; The SAT problem goes through a number of phases and
;; most user functions can only be legally used in certain
;; phases.  If a function is called when it is in an
;; illegal phase, an error message is generated.

;; These are the phases
;; (and corresponding problem-stack-depth #):
;;
;; 0: No SAT problem
;; 1: New SAT problem
;; 2: Expression(s) added
;; 3: "SAT" solution available
;; 4: Satisfying instance generated
;; 5: Satisfying instance exploration
;; 6: Satisfying instance exploration, current value set

;; Currently I use the numbers directly to perform the
;; legality checking---rather than creating functions with
;; good names to check or update phase numbers.

;; ----------------------------------------------------

(defconst *input-filename* "input.sexpr")
(defconst *output-filename* "output.sexpr")
(defconst *temp-dir* "sat-temp-files")

(defun full-sat-script-name ()
  (concat *sulfa-dir* "/scripts/sexpr-sat-solver"))

(defun full-input-filename ()
  (concat *temp-dir* "/" *input-filename*))

(defun full-output-filename ()
  (concat *temp-dir* "/" *output-filename*))

(defun solver-concat-args (lst)
  (if (consp lst)
      (if (consp (cdr lst))
	  (list 'concatenate
                ''string
                " "
                (list 'concatenate
                      ''string
                      (car lst)
                      (solver-concat-args (cdr lst))))
	(list 'concatenate
              ''string
              " "
              (car lst)))
    nil))

(defttag acl2::SAT)

(encapsulate
 ()

 (defun solver-sys-call-fn (arg-str state)
   (sys-call* *perl*
              (list* (full-sat-script-name)
                     "-dir"
                     *temp-dir*
                     *input-filename*
                     arg-str)
              state))

 (defmacro solver-sys-call (&rest args)
   `(solver-sys-call-fn (list . ,args) state))

 (defmacro rm-output-file () ; Matt K. mod in the spirit of pre-4-2017 behavior
   '(mv-let (erp val state)
      (sys-call+ "rm" (list "-f" (full-output-filename)) state)
      (declare (ignore erp val))
      state))
 )

(defun read-alist (acc channel state)
  (mv-let
   (eof obj state)
   (read-object channel state)
   (if eof
       (mv acc channel state)
     (read-alist (cons obj acc) channel state))))

(defun read-sat-file (filename state)
  (mv-let
   (channel state)
   (open-input-channel filename :object state)
   (if (not channel)
       (mv (er hard 'read-sat-file "SAT solver produced no output~%")
           "unknown"
           state)
     (mv-let
      (alist channel state)
      (read-alist nil channel state)
      (let* ((state (close-input-channel channel state))
             (sat-entry (assoc-eq 'acl2::sat alist))
             (unsat-entry (assoc-eq 'acl2::unsat alist))
             (time-entry (assoc-eq 'acl2::time alist))
             (time (if time-entry (cadr time-entry) "unknown")))
        (cond
         (sat-entry
          (mv sat-entry time state))
         (unsat-entry
          (mv unsat-entry time state))
         (t
          (mv (er hard 'read-sat-file "SAT solver produced no answer~%")
              "unknown"
              state))))))))

(defun run-sat-solver (num-vars num-clauses $sat state)
  (declare (xargs :stobjs $sat))
  (mv-let (erp val state)
    (prog2$
     (print-msg 1
                (msg "Calling SAT solver.  Num-vars: ~x0, Num-clauses: ~x1 ~%"
                     num-vars num-clauses)
                $sat)
     (solver-sys-call "--solve"
                      (num-to-str num-vars)
                      (num-to-str num-clauses)
                      *output-filename*))
    (declare (ignore erp val)) ; Matt K. comment: this conforms with behavior pre-4-2017
    (prog2$
     (print-msg 2 (msg "Reading solver's output~%") $sat)
     (mv-let
       (sat-output time state)
       (read-sat-file (full-output-filename) state)
       (pprogn
        (rm-output-file)
        (prog2$
         (print-msg 1 (msg "Time spent by SAT solver: ~s0~%" time) $sat)
         (mv sat-output state)))))))

;; Look up an input-variable's i-var in the
;; input-alist, or create one if none exists.
(defun get-input-i-var (input-var $sat)
  (declare (xargs :stobjs $sat))
  (let* ((var-entry (assoc-eq input-var (input-alist $sat))))
    (cond
     (var-entry
      (mv (cdr var-entry) $sat))
     (t
      (mv-let
       (i-var $sat)
       (new-top-i-var $sat)
       (let (($sat (add-input-alist-entry input-var i-var $sat)))
         (mv i-var $sat)))))))

(mutual-recursion
;; Candidate for tail-recursive optimization!
(defun add-free-variables-expr-list (bound-vars expr-list $sat)
  (declare (xargs :stobjs $sat))
  (cond
   ((endp expr-list)
    $sat)
   (t
    (let (($sat (add-free-variables bound-vars (car expr-list) $sat)))
      (add-free-variables-expr-list bound-vars (cdr expr-list) $sat)))))

;; Add the free variables in expr into the input alist.
(defun add-free-variables (bound-vars expr $sat)
  (declare (xargs :stobjs $sat))
  (cond
   ((atom expr)
    (if (or (member expr bound-vars)
            (assoc-eq expr (input-alist $sat)))
        $sat
      (mv-let
       (i-var $sat)
       (new-top-i-var $sat)
       (add-input-alist-entry expr i-var $sat))))
   ((consp (car expr))
    ;; ((lambda <formals> <body>) <args>)
    (let* ((formals (cadr (car expr)))
           (body (caddr (car expr)))
           (args (cdr expr))
           ($sat (add-free-variables (append formals bound-vars)
                                     body
                                     $sat)))
      (add-free-variables-expr-list bound-vars args $sat)))
   ((quotep expr)
    $sat)
   (t
    (add-free-variables-expr-list bound-vars (cdr expr) $sat))))
)

;; Add a new ACL2 expression "expr" to the SAT conjunction.
;; If sat-solve later returns satisfiable then there exists an instance
;; to the free variable that satisfies this "expr" along with the
;; rest of the SAT problem.  If "negate" is non-nil then the negation
;; of "expr" must be satisfied rather than the expression itself.
;; For example, to determine whether (implies (and a b) (or c d)) is
;; valid one could use the sequence:

;; (sat-add-expr nil a $sat state)
;; (sat-add-expr nil b $sat state)
;; (sat-add-expr t c $sat state)
;; (sat-add-expr t d $sat state)
;; (sat-solve $sat state)

;; Now we're asking the question is there an instance such that
;; a and b, but not c or d?  If there is then this instance is
;; a counter-example to (implies (and a b) (or c d)).  Otherwise,
;; (implies (and a b) (or c d)) is valid.

(defun add-expr-ivar-alist (negate expr alist $sat state)
  (declare (xargs :stobjs $sat))
  (let* (($sat (update-need-more-traversals t $sat))
         (t-struct (make-acl2-todo-entry nil expr nil alist nil nil)))
    (mv-let
     (expr $sat state)
     (remove-functions expr t-struct $sat state)
     (mv-let
      (f-expr $sat)
      (i-expr-to-f-expr expr $sat)
      (if negate
          ;; We need to assert that the input is false.
          (mv-let
           ($sat state)
           (add-cnf-clause `(,(negate-f-expr f-expr)) $sat state)
           (mv $sat state))
        ;; We need to assert that the input is true.
        (mv-let
         ($sat state)
         (add-cnf-clause `(,f-expr) $sat state)
         (mv $sat state)))))))

(defun acl2::sat-add-expr (negate expr $sat state)
  (declare (xargs :stobjs $sat))
  (mv-let
   (in-SULFA sat-package-symbols $sat)
   (SULFA-exprp expr $sat state)
   (cond
    (sat-package-symbols
     (mv (er hard 'acl2::sat-add-expr
             "Expression not in SULFA---SAT package symbols ~
              are prohibited")
         $sat state))
    ((not in-SULFA)
     (mv (er hard 'acl2::sat-add-expr
             "Expression is not in SULFA")
         $sat state))
    ((equal (problem-stack-depth $sat) 0)
     (mv (er hard 'acl2::sat-add-expr
             "ERROR: No current sat problem")
         $sat state))
    ((<= 5 (problem-stack-depth $sat))
     (mv (er hard 'acl2::sat-add-expr
             "ERROR: This operation is illegal during exploration of a ~
                satisfying instance")
         $sat state))
    (t
     (let* (($sat (update-problem-stack-depth 2 $sat))
            ($sat (add-free-variables nil expr $sat)))
       (mv-let
        ($sat state)
        (add-expr-ivar-alist negate expr (input-alist $sat) $sat state)
        (mv nil $sat state)))))))

(defun acl2::sat-un-fn-condition-val (un-fn-entry $sat state)
  (declare (xargs :stobjs $sat)
           (ignore un-fn-entry))
  (cond
   ((<= (problem-stack-depth $sat) 3)
    (mv (er hard 'acl2::sat-un-fn-condition-val
            "ERROR: No satisfying instance available~%")
        t $sat state))
   (t
    ;; At the moment all un-fn conditions are emtpy (i.e. true)
    (mv nil t $sat state))))

(defun acl2::sat-un-fn-fn (un-fn-entry $sat state)
  (declare (xargs :stobjs $sat))
  (mv nil (uufe-fn un-fn-entry) $sat state))

(defun acl2::sat-un-fn-val (un-fn-entry $sat state)
  (declare (xargs :stobjs $sat))
  (cond
   ((<= (problem-stack-depth $sat) 3)
    (mv (er hard 'acl2::sat-un-fn-val
            "ERROR: No satisfying instance available~%")
           'sat::unknown $sat state))
   (t
    (let* ((val (ce-i-var-vali (uufe-lhs un-fn-entry) $sat)))
      (cond
       ((ce-val-unknownp val)
        (mv nil 'sat::unknown $sat state))
       (t
        (mv nil val $sat state)))))))

(defun acl2::sat-un-fn-arg-entry-list (un-fn-entry $sat state)
  (declare (xargs :stobjs $sat))
  (mv nil (uufe-args un-fn-entry) $sat state))

(defun acl2::sat-arg-entry-val (un-fn-entry $sat state)
  (declare (xargs :stobjs $sat))
  (cond
   ((<= (problem-stack-depth $sat) 3)
    (mv (er hard 'acl2::sat-arg-entry-val
            "ERROR: No satisfying instance available~%")
        'sat::unknown $sat state))
   (t
    (let* ((val (eval-i-expr (uae-i-expr un-fn-entry) $sat)))
      (cond
       ((ce-val-unknownp val)
        (mv nil 'sat::unknown $sat state))
       (t
        (mv nil val $sat state)))))))

(defun acl2::sat-var-entry (var $sat state)
  (declare (xargs :stobjs $sat))
  (cond
   ((equal (problem-stack-depth $sat) 0)
    (mv (er hard 'acl2::sat-var-entry
            "ERROR: No SAT problem~%")
        (invalid-user-entry) $sat state))
   (t
    (mv-let
     (ivar $sat)
     (get-input-i-var var $sat)
     (mv nil (make-user-var-entry var ivar) $sat state)))))

(defun sat-un-fn-entry-list1 (fn ufe-list acc)
  (cond
   ((endp ufe-list)
    acc)
   (t
    (let ((uuf-entry (make-user-un-fn-entry fn (car ufe-list))))
      (sat-un-fn-entry-list1 fn
                             (cdr ufe-list)
                             (cons uuf-entry acc))))))

(defun user-un-fn-entry-list (fn $sat)
  (declare (xargs :stobjs $sat))
  ;; First get the internal un-fn-entry list, then turn it
  ;; into the "user" version.
  (let ((ufe-list (lookup-ufe-list fn nil $sat)))
    (sat-un-fn-entry-list1 fn ufe-list nil)))

(defun acl2::sat-un-fn-entry-list (fn $sat state)
  (declare (xargs :stobjs $sat))
  (cond
   ((equal (problem-stack-depth $sat) 0)
    (mv (er hard 'acl2::sat-un-fn-entry-list
            "ERROR: No sat problem")
        nil $sat state))
   (t
    (mv nil (user-un-fn-entry-list fn $sat) $sat state))))

(defun acl2::sat-un-fn-list ($sat state)
  (declare (xargs :stobjs $sat))
  (mv nil (un-fn-list $sat) $sat state))

(defun make-ivar-alist (user-alist acc $sat)
  (declare (xargs :stobjs $sat))
  (cond
   ((endp user-alist)
    (mv acc $sat))
   (t
    (let ((key (caar user-alist))
          (val (cdar user-alist)))
      (make-ivar-alist (cdr user-alist)
                       (cons (cons key (user-entry-i-expr val)) acc)
                       $sat)))))

;; sat-add-expr-alist function is a more general version of
;; sat-add-expr.  Every free
;; veriable in the ACL2 expression "expr" must occur as a key in the
;; alist "alist".  The value of the alist entry can be either a variable
;; (representing a variable in the SAT problem), a uninterpreted
;; function entry (given by sat-un-fn-entry-list), or an argument
;; entry (given by sat-si-un-fn-arg-entry-list).  The idea is that
;; this function can be used to refine a formula in which the uninterpreted
;; functions are a means of abstraction.

(defun acl2::sat-add-expr-alist (negate expr alist $sat state)
  (declare (xargs :stobjs $sat))
  (mv-let
   (in-SULFA sat-package-symbols $sat)
   (SULFA-exprp expr $sat state)
   (cond
    (sat-package-symbols
     (mv (er hard 'acl2::sat-add-expr-alist
             "Expression not in SULFA---SAT package symbols ~
              are prohibited")
         $sat state))
    ((not in-SULFA)
     (mv (er hard 'acl2::sat-add-expr-alist
             "Expression is not in SULFA")
         $sat state))
    ((equal (problem-stack-depth $sat) 0)
     (mv (er hard 'acl2::sat-add-expr-alist
             "ERROR: No current sat problem")
         $sat state))
    ((<= 5 (problem-stack-depth $sat))
     (mv (er hard 'acl2::sat-add-expr-alist
             "ERROR: This operation is illegal during exploration of a ~
              satisfying instance")
         $sat state))
    (t
     (let (($sat (update-problem-stack-depth 2 $sat)))
       (mv-let
        (ivar-alist $sat)
        (make-ivar-alist alist nil $sat)
        (mv-let
         ($sat state)
         (add-expr-ivar-alist negate expr ivar-alist $sat state)
         (mv nil $sat state))))))))


(defun open-temp-sat-file ($sat state)
  (declare (xargs :stobjs $sat))
  (mv-let
   ($sat state)
   (zero-sat-input-channel $sat state)
   (mv-let
    (channel state)
    (open-output-channel! (full-input-filename) :character state)
    (let* (($sat (update-sat-input-channel channel $sat)))
      (mv $sat state)))))

(defun close-temp-sat-file ($sat state)
  (declare (xargs :stobjs $sat))
  (let* ((state (close-output-channel (sat-input-channel $sat)
                                      state))
         ($sat (update-sat-input-channel nil $sat)))
    (mv $sat state)))

(defun ordered-entry-list-list (un-fn-list acc $sat)
  (declare (xargs :stobjs $sat))
  (cond
   ((endp un-fn-list)
    acc)
   (t
    (ordered-entry-list-list (cdr un-fn-list)
                             (cons (user-un-fn-entry-list (car un-fn-list)
                                                          $sat)
                                   acc)
                             $sat))))

(defun max-traversal-entry1 (i entry-list-list i-max curr-max $sat)
  (declare (xargs :stobjs $sat))
  (cond
   ((endp entry-list-list)
    (mv i-max curr-max))
   ((endp (car entry-list-list))
    (max-traversal-entry1 (1+ i) (cdr entry-list-list)
                          i-max curr-max $sat))
   ((not (valid-user-entryp curr-max))
    (let ((entry (caar entry-list-list)))
    (max-traversal-entry1 (1+ i) (cdr entry-list-list)
                          i entry $sat)))
   (t
    (let ((i0 (user-entry-i-var curr-max))
          (i1 (user-entry-i-var (caar entry-list-list))))
      (cond
       ((traversed-prior-top i0 i1 $sat)
        (max-traversal-entry1 (1+ i)
                             (cdr entry-list-list)
                             i
                             (caar entry-list-list)
                             $sat))
       (t
        (max-traversal-entry1 (1+ i)
                             (cdr entry-list-list)
                             i-max
                             curr-max
                             $sat)))))))

(defun max-traversal-entry (entry-list-list $sat)
  (declare (xargs :stobjs $sat))
  (max-traversal-entry1 0 entry-list-list (invalid-user-entry) -1 $sat))

;; Remove the ith car from entry-list-list.
(defun rem-ith-car (i entry-list-list acc)
  (cond
   ((zp i)
    (revappend acc (cons (cdr (car entry-list-list))
                         (cdr entry-list-list))))
   (t
    (rem-ith-car (1- i) (cdr entry-list-list)
                 (cons (car entry-list-list) acc)))))

(defun merge-entry-lists (entry-list-list acc $sat)
  (declare (xargs :stobjs $sat))
  (mv-let
   (i entry)
   (max-traversal-entry entry-list-list $sat)
   (cond
    ((valid-user-entryp entry)
     (merge-entry-lists (rem-ith-car i entry-list-list acc)
                        (cons entry acc)
                        $sat))
    (t
     (revappend acc nil)))))

(defun generate-up-to-ivar (i0 $sat)
  (declare (xargs :stobjs $sat))
  (let ((var-list (explore-var-list $sat)))
    (cond
     ((eq nil var-list)
      $sat)
     ((equal i0 (car var-list))
      (let (($sat (update-explore-var-list (cdr var-list) $sat)))
        ;; It's up to the user to provide the value for this variable!
        $sat))
     (t
      (mv-let
       (val $sat)
       (ce-var (car var-list) $sat)
       (declare (ignore val))
       (let (($sat (update-explore-var-list (cdr var-list) $sat)))
         (generate-up-to-ivar i0 $sat)))))))

(defun exploration-list-emptyp ($sat)
  (declare (xargs :stobjs $sat))
  (eq nil (curr-ord-entry-list $sat)))

(defun current-exploration-entry ($sat)
  (declare (xargs :stobjs $sat))
  (car (curr-ord-entry-list $sat)))

(defun generate-up-to-curr-entry ($sat)
  (declare (xargs :stobjs $sat))
  (cond
   ((exploration-list-emptyp $sat)
    (generate-up-to-ivar 0 $sat))
   (t
    (let* ((entry (current-exploration-entry $sat))
           (i0 (user-entry-i-var entry)))
      (generate-up-to-ivar i0 $sat)))))

(defun create-exploration-list ($sat)
  (declare (xargs :stobjs $sat))
  (let* ((un-fn-list (un-fn-list $sat))
         (ordered-input-list (full-uve-list $sat))
         (ordered-entry-list-list (ordered-entry-list-list un-fn-list
                                                           (list ordered-input-list)
                                                           $sat))
         (ordered-entry-list (merge-entry-lists ordered-entry-list-list nil $sat))
         ($sat (update-curr-ord-entry-list ordered-entry-list $sat))
         ($sat (update-saved-ord-entry-list ordered-entry-list $sat))
         ($sat (update-explore-var-list (top-completed-var-list $sat) $sat)))
    $sat))

(defun restart-exploration-list ($sat)
  (declare (xargs :stobjs $sat))
  (let* ((ordered-entry-list (saved-ord-entry-list $sat))
         ($sat (update-curr-ord-entry-list ordered-entry-list $sat))
         ($sat (update-saved-ord-entry-list ordered-entry-list $sat))
         ($sat (update-exploration-val-list nil $sat))
         ($sat (update-explore-var-list (top-completed-var-list $sat) $sat)))
     $sat))

(defun next-exploration-entry ($sat)
  (declare (xargs :stobjs $sat))
  (let ((ord-entry-list (curr-ord-entry-list $sat)))
    (update-curr-ord-entry-list (cdr ord-entry-list) $sat)))

(defun exploration-ground-atoms (atoms-alist val $sat state)
  (declare (xargs :stobjs $sat))
  (cond
   ((endp atoms-alist)
    (mv $sat state))
   ((equal val (caar atoms-alist))
    (mv-let
     ($sat state)
     (add-cnf-clause (list (cdar atoms-alist)) $sat state)
     (exploration-ground-atoms (cdr atoms-alist) val $sat state)))
   (t
    (mv-let
     ($sat state)
     (add-cnf-clause (list (negate-f-expr (cdar atoms-alist))) $sat state)
     (exploration-ground-atoms (cdr atoms-alist) val $sat state)))))

(defun exploration-ground-eq-alist (eq-alist val $sat state)
  (declare (xargs :stobjs $sat))
  (cond
   ((endp eq-alist)
    (mv $sat state))
   ((equal val (ce-i-var-vali (caar eq-alist) $sat))
    (mv-let
     ($sat state)
     (add-cnf-clause (list (cdar eq-alist)) $sat state)
     (exploration-ground-eq-alist (cdr eq-alist) val $sat state)))
   (t
    (mv-let
     ($sat state)
     (add-cnf-clause (list (negate-f-expr (cdar eq-alist))) $sat state)
     (exploration-ground-eq-alist (cdr eq-alist) val $sat state)))))

(defun exploration-ground-consp (consp-f-var val $sat state)
  (declare (xargs :stobjs $sat))
  (cond
   ((not (valid-varp consp-f-var))
    (mv $sat state))
   ((consp val)
    (add-cnf-clause (list consp-f-var) $sat state))
   (t
    (add-cnf-clause (list (negate-f-expr consp-f-var)) $sat state))))

;; Candidate for tail-recursive optimization!
(defun exploration-ground-i-var (i0 val $sat state)
  (declare (xargs :stobjs $sat))
  (cond
   ((not (valid-varp i0))
    (mv $sat state))
   (t
    (let* ((i0-atoms (atoms-alist-vari i0 $sat))
           (i0-eq-alist (eq-alist-vari i0 $sat))
           (i0-consp (consp-vari i0 $sat))
           (i0-car (car-vari i0 $sat))
           (i0-cdr (cdr-vari i0 $sat))
           (val-car (logical-car val))
           (val-cdr (logical-cdr val)))
    (mv-let
     ($sat state)
     (exploration-ground-atoms i0-atoms val $sat state)
     (mv-let
      ($sat state)
      (exploration-ground-eq-alist i0-eq-alist val $sat state)
      (mv-let
       ($sat state)
       (exploration-ground-consp i0-consp val $sat state)
       (mv-let
        ($sat state)
        (exploration-ground-i-var i0-car val-car $sat state)
        (exploration-ground-i-var i0-cdr val-cdr $sat state)))))))))

(defun exploration-ground-iete-list (iete-list val $sat state)
  (declare (xargs :stobjs $sat))
  (cond
   ((endp iete-list)
    (mv $sat state))
   ((equal (eval-i-expr (iete-expr (car iete-list)) $sat)
           val)
    ;; This clause is satisfied by its defining literal
    (exploration-ground-iete-list (cdr iete-list) val $sat state))
   (t
    ;; This clause must be satisfied through its other literals
    (mv-let
     ($sat state)
     (add-cnf-clause (iete-cnf-lits (car iete-list)) $sat state)
     (exploration-ground-iete-list (cdr iete-list) val $sat state)))))

(defun set-exploration-val1 (i0 val $sat state)
  (declare (xargs :stobjs $sat))
  (let* ((t-struct (todo-structi i0 $sat))
         (iete-list (ts-iete-list t-struct)))
    (mv-let
     ($sat state)
     (exploration-ground-iete-list iete-list val $sat state)
     (exploration-ground-i-var i0 val $sat state))))

(defun set-exploration-val (entry val $sat state)
  (declare (xargs :stobjs $sat))
  (set-exploration-val1 (user-entry-i-var entry) val $sat state))

(defun remove-exploration-list ($sat)
  (declare (xargs :stobjs $sat))
  (let* (($sat (update-curr-ord-entry-list nil $sat))
         ($sat (update-saved-ord-entry-list nil $sat))
         ($sat (update-exploration-val-list nil $sat)))
    $sat))

(defun rerun-exploration-list1 (entry-list val-list $sat state)
  (declare (xargs :stobjs $sat))
  (cond
   ((endp val-list)
    (mv $sat state))
   (t
    (mv-let
     ($sat state)
     (set-exploration-val (car entry-list) (car val-list) $sat state)
     (rerun-exploration-list1 (cdr entry-list) (cdr val-list) $sat state)))))

(defun rerun-exploration-list ($sat state)
  (declare (xargs :stobjs $sat))
  (rerun-exploration-list1 (saved-ord-entry-list $sat)
                           (revappend (exploration-val-list $sat) nil)
                           $sat state))

(defun add-un-fn-val (entry return-val $sat)
  (declare (xargs :stobjs $sat))
  (cond
   ((uuf-entryp entry)
    (let* ((fn (uufe-fn entry))
           (arg-vals (uufe-arg-vals entry $sat))
           (un-fn-alist (lookup-un-fn-vals fn nil $sat))
           (un-fn-alist (cons (cons arg-vals return-val) un-fn-alist))
           ($sat (set-un-fn-vals fn un-fn-alist $sat)))
      $sat))
   (t $sat)))

(defun add-exploration-val (entry val $sat)
  (declare (xargs :stobjs $sat))
  (let* ((exploration-val-list (exploration-val-list $sat))
         (exploration-val-list (cons val exploration-val-list))
         ($sat (update-exploration-val-list exploration-val-list $sat))
         ($sat (add-un-fn-val entry val $sat)))
    $sat))

(defun remove-un-fn-val (entry $sat)
  (declare (xargs :stobjs $sat))
  (cond
   ((uuf-entryp entry)
    (let* ((fn (uufe-fn entry))
           (un-fn-alist (lookup-un-fn-vals fn nil $sat))
           (un-fn-alist (cdr un-fn-alist))
           ($sat (set-un-fn-vals fn un-fn-alist $sat)))
      $sat))
   (t $sat)))

(defun remove-exploration-val (entry $sat)
  (declare (xargs :stobjs $sat))
  (let* ((exploration-val-list (exploration-val-list $sat))
         ($sat (update-exploration-val-list (cdr exploration-val-list) $sat))
         ($sat (remove-un-fn-val entry $sat)))
    $sat))

(defmacro with-solver-sys-call (arg form)
  `(mv-let (erp-with-solver-sys-call val-with-solver-sys-call state)
     (solver-sys-call ,arg)
     (declare (ignore val-with-solver-sys-call))
     (prog2$ (and erp-with-solver-sys-call
                  (er hard! 'solver-sys-call
                      "Sys-call+ returned non-zero error status from:~|~x0"
                      '(solver-sys-call ,arg)))
             ,form)))

(defun acl2::sat-instance-exploration-begin ($sat state)
  (declare (xargs :stobjs $sat))
  (cond
   ((or (equal (problem-stack-depth $sat) 3)
        (equal (problem-stack-depth $sat) 4))
    (with-solver-sys-call
     "--push"
     (let* (($sat (update-problem-stack-depth 5 $sat))
            ($sat (create-exploration-list $sat))
            ($sat (update-num-f-clauses-pre-explore (num-f-clauses $sat) $sat))
            ($sat (generate-up-to-curr-entry $sat)))
       (mv nil $sat state))))
   ((<= 5 (problem-stack-depth $sat))
    ;; We're restarting the current exploration
    (let (($sat (restart-exploration-list $sat)))
      (with-solver-sys-call
       "--pop"
       (let (($sat (update-num-f-clauses (num-f-clauses-pre-explore $sat) $sat)))
         (with-solver-sys-call
          "--push"
          (let* (($sat (generate-up-to-curr-entry $sat))
                 ($sat (update-problem-stack-depth 5 $sat)))
            (mv nil $sat state)))))))
   (t
    (mv (er hard 'acl2::sat-instance-exploration-begin
            "ERROR: This operation is only legal after sat-solve ~
             returns \"sat\"~%")
        $sat state))))

(defun acl2::sat-ie-emptyp ($sat state)
  (declare (xargs :stobjs $sat))
  (cond
   ((< (problem-stack-depth $sat) 5)
    (mv (er hard 'acl2::sat-ie-emptyp
            "ERROR: Not in SAT exploration phase~%")
        t $sat state))
   (t
    (mv nil (exploration-list-emptyp $sat) $sat state))))

(defun acl2::sat-ie-current-entry ($sat state)
  (declare (xargs :stobjs $sat))
  (cond
   ((< (problem-stack-depth $sat) 5)
    (mv (er hard 'acl2::sat-ie-current-entry
            "ERROR: Not in SAT exploration phase~%")
        nil $sat state))
   ((exploration-list-emptyp $sat)
    (mv (er hard 'acl2::sat-ie-current-entry
            "ERROR: Exploration list is empty~%")
        nil $sat state))
   (t
    (mv nil (current-exploration-entry $sat) $sat state))))

(defun acl2::sat-ie-current-entry-type ($sat state)
  (declare (xargs :stobjs $sat))
  (cond
   ((< (problem-stack-depth $sat) 5)
    (mv (er hard 'acl2::sat-ie-current-entry
            "ERROR: Not in SAT exploration phase~%")
        nil $sat state))
   ((exploration-list-emptyp $sat)
    (mv (er hard 'acl2::sat-ie-current-entry
            "ERROR: Exploration list is empty~%")
        nil $sat state))
   (t
    (let ((entry (current-exploration-entry $sat)))
      (cond
       ((uuf-entryp entry)
        (mv nil 'acl2::uninterpreted-function $sat state))
       (t
        (mv nil 'acl2::variable $sat state)))))))

(defun acl2::sat-ie-current-expr ($sat state)
  (declare (xargs :stobjs $sat))
  (cond
   ((< (problem-stack-depth $sat) 5)
    (mv (er hard 'acl2::sat-ie-current-expr
            "ERROR: Not in SAT exploration phase~%")
        nil $sat state))
   ((exploration-list-emptyp $sat)
    (mv (er hard 'acl2::sat-ie-current-expr
            "ERROR: Exploration list is empty~%")
        nil $sat state))
   (t
    (let ((entry (current-exploration-entry $sat)))
      (mv nil (simplify-entry entry $sat) $sat state)))))

(defun acl2::sat-ie-find-val ($sat state)
  (declare (xargs :stobjs $sat))
  (cond
   ((< (problem-stack-depth $sat) 5)
    (mv (er hard 'acl2::sat-ie-find-val
            "ERROR: Not in SAT exploration phase~%")
        'acl2::unknown $sat state))
   ((exploration-list-emptyp $sat)
    (mv (er hard 'acl2::sat-ie-find-val
            "ERROR: Exploration list is empty~%")
        'acl2::unknown $sat state))
   (t
    (let ((entry (current-exploration-entry $sat)))
      (mv-let
       (val $sat)
       (ce-var (user-entry-i-var entry) $sat)
       (mv nil val $sat state))))))

(defun acl2::sat-ie-unique-id ($sat state)
  (declare (xargs :stobjs $sat))
  (cond
   ((< (problem-stack-depth $sat) 5)
    (mv (er hard 'acl2::sat-ie-find-val
            "ERROR: Not in SAT exploration phase~%")
        'acl2::unknown $sat state))
   ((exploration-list-emptyp $sat)
    (mv (er hard 'acl2::sat-ie-find-val
            "ERROR: Exploration list is empty~%")
        'acl2::unknown $sat state))
   (t
    (let ((entry (current-exploration-entry $sat)))
      (mv nil (user-entry-i-var entry) $sat state)))))

(defun acl2::sat-ie-check ($sat state)
  (declare (xargs :stobjs $sat))
  (cond
   ((< (problem-stack-depth $sat) 5)
    (mv (er hard 'acl2::sat-ie-check
            "ERROR: Only available during instance exploration~%")
        'acl2::unknown $sat state))
   (t
    (mv-let
     ($sat state)
     (close-temp-sat-file $sat state)
     (mv-let
      (sat-output state)
      (run-sat-solver (num-f-vars $sat) (num-f-clauses $sat) $sat state)
      (mv-let
       ($sat state)
       (open-temp-sat-file $sat state)
       (cond
        ((unsatp sat-output)
         (mv nil 'acl2::unsat $sat state))
        (t
         (let (($sat (add-ce-vals 1 (sat-inst-list sat-output) $sat)))
           (mv nil 'acl2::sat $sat state))))))))))

(defun acl2::sat-ie-set! (val $sat state)
  (declare (xargs :stobjs $sat))
  (cond
   ((< (problem-stack-depth $sat) 5)
    (mv (er hard 'acl2::sat-ie-set!
            "ERROR: Not in SAT exploration phase~%")
        $sat state))
   ((exploration-list-emptyp $sat)
    (mv (er hard 'acl2::sat-ie-set!
            "ERROR: Exploration list empty~%")
        $sat state))
   ((equal (problem-stack-depth $sat) 6)
    (let* ((entry (current-exploration-entry $sat))
           ($sat (remove-exploration-val entry $sat)))
      (with-solver-sys-call
       "--pop"
       (let (($sat (update-num-f-clauses (num-f-clauses-pre-explore $sat) $sat)))
         (with-solver-sys-call
          "--push"
          (let (($sat (update-problem-stack-depth 5 $sat)))
            (mv-let
              ($sat state)
              (rerun-exploration-list $sat state)
              (acl2::sat-ie-set! val $sat state))))))))
   (t
    (let* ((entry (current-exploration-entry $sat)))
      (mv-let
       ($sat state)
       (set-exploration-val entry val $sat state)
       (let* (($sat (add-exploration-val entry val $sat))
              ($sat (update-problem-stack-depth 6 $sat)))
         (mv-let
          (val $sat)
          (add-new-ce-val (user-entry-i-var entry) val $sat)
          (declare (ignore val))
          (mv nil $sat state))))))))

(defun acl2::sat-ie-next ($sat state)
  (declare (xargs :stobjs $sat))
  (cond
   ((< (problem-stack-depth $sat) 5)
    (mv (er hard 'acl2::sat-ie-next
            "ERROR: Not in SAT exploration phase~%")
        $sat state))
   ((equal (problem-stack-depth $sat) 5)
    (mv (er hard 'acl2::sat-ie-next
            "ERROR: No value set for current variable~%")
        $sat state))
   ((exploration-list-emptyp $sat)
    (mv (er hard 'acl2::sat-ie-next
            "ERROR: Exploration list is empty~%")
        $sat state))
   (t
    (let* (($sat (next-exploration-entry $sat))
           ($sat (update-problem-stack-depth 5 $sat))
           ($sat (generate-up-to-curr-entry $sat)))
      (mv nil $sat state)))))

(defun acl2::sat-ie-set (val $sat state)
  (declare (xargs :stobjs $sat))
  (mv-let
   (erp $sat state)
   (acl2::sat-ie-set! val $sat state)
   (declare (ignore erp))
   (acl2::sat-ie-check $sat state)))

(defun acl2::sat-instance-exploration-end ($sat state)
  (declare (xargs :stobjs $sat))
  (cond
   ((<= 5 (problem-stack-depth $sat))
    (with-solver-sys-call
     "--pop"
     (let* (($sat (update-num-f-clauses (num-f-clauses-pre-explore $sat) $sat))
            ($sat (update-problem-stack-depth 3 $sat))
            ($sat (remove-exploration-list $sat)))
       (mv nil $sat state))))
   (t
    (mv (er hard 'acl2::sat-instance-exploration-end
            "ERROR: No exploration to end~%")
        $sat state))))

(defun acl2::sat-update-external-value (val $sat)
  (declare (xargs :stobjs $sat))
  (update-external-value val $sat))

(defun acl2::sat-external-value ($sat)
  (declare (xargs :stobjs $sat))
  (external-value $sat))

(defun acl2::sat-solve ($sat state)
  (declare (xargs :stobjs $sat))
  (cond
   ((equal (problem-stack-depth $sat) 0)
    (mv (er hard 'acl2::sat-solve
            "ERROR: No problem to solve~%")
        'acl2::unknown $sat state))
   ((<= 5 (problem-stack-depth $sat))
    (mv (er hard 'acl2::sat-solve
            "ERROR: End SAT exploration first!~%")
        'acl2::unknown $sat state))
   (t
    (mv-let
     ($sat state)
     (convert-to-cnf $sat state)
     (mv-let
      ($sat state)
      (close-temp-sat-file $sat state)
      (mv-let
       (sat-output state)
       (run-sat-solver (num-f-vars $sat) (num-f-clauses $sat) $sat state)
       (mv-let
        ($sat state)
        (open-temp-sat-file $sat state)
        (cond
         ((unsatp sat-output)
          (let (($sat (update-problem-stack-depth 2 $sat)))
            (mv nil 'acl2::unsat $sat state)))
         (t
          (let* (($sat (update-problem-stack-depth 3 $sat))
                 ($sat (zero-ce-vals $sat))
                 ($sat (construct-ce-vals $sat))
                 ($sat (add-ce-vals 1 (sat-inst-list sat-output) $sat)))
            (mv nil 'acl2::sat $sat state)))))))))))

(defun acl2::sat-in-SULFA (expr $sat state)
  (declare (xargs :stobjs $sat))
  (mv-let
   (in-SULFA sat-package-symbols $sat)
   (SULFA-exprp expr $sat state)
   (mv nil in-SULFA sat-package-symbols $sat state)))

(defun acl2::sat-mark-uninterpreted (fn $sat state)
  (declare (xargs :stobjs $sat))
  (cond
   ((equal (problem-stack-depth $sat) 1)
    (let* (($sat (update-NLA-table nil $sat))
           ($sat (set-un-fn-mark fn t $sat)))
      (mv nil $sat state)))
   (t
    (mv (er hard 'acl2::sat-mark-uninterpreted
            "ERROR: Mark-uninterpreted only legal just after begining a new ~
             problem")
        $sat state))))

(defun acl2::sat-unmark-uninterpreted (fn $sat state)
  (declare (xargs :stobjs $sat))
  (cond
   ((equal (problem-stack-depth $sat) 1)
    (let* (($sat (update-NLA-table nil $sat))
           ($sat (set-un-fn-mark fn nil $sat)))
      (mv nil $sat state)))
   (t
    (mv (er hard 'acl2::sat-unmark-uninterpreted
            "ERROR: Unmark-uninterpreted only legal just after beginning a new ~
             problem")
        $sat state))))

(defun acl2::sat-generate-satisfying-instance ($sat state)
  (declare (xargs :stobjs $sat))
  (cond
   ((equal (problem-stack-depth $sat) 3)
    (let* (($sat (update-problem-stack-depth 4 $sat))
           ($sat (ce-var-list (top-completed-var-list $sat) $sat))
           ($sat (add-ce-un-fn-vals (un-fn-list $sat) $sat)))
      (mv nil $sat state)))
   (t
    (mv (er hard 'acl2::sat-generate-satisfying-instance
            "ERROR: No satifiable solution to generate~%")
        $sat state))))

(defun acl2::sat-si-input-alist ($sat state)
  (declare (xargs :stobjs $sat))
  (cond
   ((<= (problem-stack-depth $sat) 3)
    (mv (er hard 'acl2::sat-si-input-alist
            "ERROR: No satisfying instance~%")
        nil $sat state))
   (t
    (mv nil
        (get-ce-alist (rev-append (input-alist $sat) nil) nil $sat)
        $sat state))))

(defun acl2::sat-si-un-fn-alist (fn $sat state)
  (declare (xargs :stobjs $sat))
  (cond
   ((<= (problem-stack-depth $sat) 3)
    (mv (er hard 'acl2::sat-si-un-fn-alist
            "ERROR: No satisfying instance~%")
        nil $sat state))
   (t
    (mv nil (lookup-un-fn-vals fn nil $sat) $sat state))))

;; Remove all data from the current problem so that we can start a new one.
;; This function must be called before calling ANY other functions.
(defun acl2::sat-new-problem ($sat state)
  (declare (xargs :stobjs $sat))
  (cond
   ((<= 5 (problem-stack-depth $sat))
    (mv (er hard 'acl2::sat-new-problem
            "ERROR: This operation is illegal during exploration of a ~
             satisfying instance~%")
        $sat state))
   (t
    (mv-let
     ($sat state)
     (zero-sat-stobj $sat state)
     (let* (($sat (construct-sat-stobj $sat))
            ($sat (update-problem-stack-depth 1 $sat)))
       (with-solver-sys-call
        "--new-problem"
        (mv-let
          ($sat state)
          (open-temp-sat-file $sat state)
          (mv nil $sat state))))))))

(defun acl2::sat-new-problem! ($sat state)
  (declare (xargs :stobjs $sat))
  (cond
   ((< (problem-stack-depth $sat) 5)
    (mv-let
     ($sat state)
     (zero-sat-stobj! $sat state)
     (let* (($sat (construct-sat-stobj $sat))
            ($sat (update-problem-stack-depth 1 $sat)))
       (with-solver-sys-call
        "--new-problem"
        (mv-let
          ($sat state)
          (open-temp-sat-file $sat state)
          (mv nil $sat state))))))
   (t
    (mv-let
     (erp $sat state)
     (acl2::sat-instance-exploration-end $sat state)
     (declare (ignore erp))
     (acl2::sat-new-problem! $sat state)))))


(defun acl2::sat-end-problem ($sat state)
  (declare (xargs :stobjs $sat))
  (cond
   ((<= 5 (problem-stack-depth $sat))
    (mv (er hard 'acl2::sat-end-problem
            "ERROR: This operation is illegal during exploration of a ~
             satisfying instance~%")
        $sat state))
   (t
    (mv-let
     ($sat state)
     (zero-sat-stobj $sat state)
     (let (($sat (update-problem-stack-depth 0 $sat)))
       (with-solver-sys-call
        "--end-problem"
        (mv nil $sat state)))))))

(defun acl2::sat-end-problem! ($sat state)
  (declare (xargs :stobjs $sat))
  (cond
   ((< (problem-stack-depth $sat) 5)
    (mv-let
      ($sat state)
      (zero-sat-stobj! $sat state)
      (let (($sat (update-problem-stack-depth 0 $sat)))
        (with-solver-sys-call
         "--end-problem"
         (mv nil $sat state)))))
   (t
    (mv-let
     (erp $sat state)
     (acl2::sat-instance-exploration-end $sat state)
     (declare (ignore erp))
     (acl2::sat-end-problem! $sat state)))))

(defun acl2::sat-set-verbosity (x $sat state)
  (declare (xargs :stobjs $sat))
  (cond
   ((or (not (integerp x)) (< x 0) (< 4 x))
    (mv (er hard 'acl2::sat-set-verbosity
            "ERROR: Invalid verbosity level.  Verbosity level ~
         ranges from 0 (min output) to 4 (max output)~%")
        $sat state))
   (t
    (let (($sat (update-verbosity x $sat)))
      (mv nil $sat state)))))

(defun make-gf-list (formals NLA)
  (cond
   ((endp formals)
    nil)
   (t
    (cons (car NLA) (make-gf-list (cdr formals) (cdr NLA))))))

;; Get the ground formals of function fn
(defun acl2::sat-ground-formals (fn $sat state)
  (declare (xargs :stobjs $sat))
  (let ((formals (fn-formals fn state)))
    (mv-let
     (soln sat-symbols $sat)
     (SULFA-exprp (cons fn formals) $sat state)
     (declare (ignore soln sat-symbols))
     (let ((NLA (lookup-NLA fn 'not-found $sat)))
       (if (eq 'not-found NLA)
           (mv (er hard 'acl2::sat-ground-formals
                   "ERROR: No function ~x0 ~%")
               nil $sat state)
         (mv nil (make-gf-list formals NLA) $sat state))))))
