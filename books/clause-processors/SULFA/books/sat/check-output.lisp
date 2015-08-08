
;; check-output.lisp: This file checks the output of the
;; SAT solver to determine whether it found the formula
;; to be satisfyiable or unsatisfiable.  If a satisfying
;; instance is found it finds and prints an ACL2
;; counter-example.

(in-package "SAT")
(program)
(set-state-ok t)

(include-book "convert-to-cnf")
(include-book "recognizer")

(defun lookup-un-fn-vals (fn not-found-val $sat)
  (declare (xargs :stobjs $sat))
  (getprop fn 'un-fn-vals not-found-val 'un-fn-world (un-fn-world $sat)))

(defun set-un-fn-vals (fn val $sat)
  (declare (xargs :stobjs $sat))
  (update-un-fn-world (putprop fn 'un-fn-vals val (un-fn-world $sat))
                      $sat))

;; I'm using symbol-name below to protect
;; against any package name issues
(defun unsatp (sat-output)
  (and (consp sat-output)
       (equal (symbol-name (car sat-output))
              (symbol-name 'unsat))))

(defun sat-inst-list (sat-output)
  (if (not (and (consp sat-output)
                (equal (symbol-name (car sat-output))
                       (symbol-name 'sat))))
      (er hard 'sat-inst-list "No satisfying instance found~%")
    (cdr sat-output)))

(defun known-consp (var $sat)
  (declare (xargs :stobjs $sat))
  (let ((consp-var (consp-vari var $sat)))
    (if (valid-varp consp-var)
        (mv t (equal (ce-vali consp-var $sat) 1))
      (mv nil nil))))

(defun known-eq-atom1 (atom-alist non-nil non-t $sat)
  (declare (xargs :stobjs $sat))
  (cond
   ((endp atom-alist)
    (mv nil nil non-nil non-t))
   ((equal (ce-vali (cdr (car atom-alist)) $sat) 1)
    (mv t (car (car atom-alist)) nil nil))
   ((eq (car (car atom-alist)) nil)
    (known-eq-atom1 (cdr atom-alist) t non-t $sat))
   ((eq (car (car atom-alist)) t)
    (known-eq-atom1 (cdr atom-alist) non-nil t $sat))
   (t
    (known-eq-atom1 (cdr atom-alist) non-nil non-t $sat))))

;; Traverses the list of atoms that
;; var could equal and returns the four tuple:
;; (mv eq-atom atom-val non-nil non-t)
;;
;; Where eq-atom is t if one of the (eq var a)
;; entries is true.
;; In this case, atom-val is a.
;;
;; Otherwise, if there is a (eq var nil) that
;; is false then non-nil is true and if there
;; is a (eq var t) that is false then non-t
;; is true.
(defun known-eq-atom (var non-nil non-t $sat)
  (declare (xargs :stobjs $sat))
  (known-eq-atom1 (atoms-alist-vari var $sat)
                  non-nil
                  non-t
                  $sat))

(defun add-new-ce-val1 (var val todo-list $sat)
  (declare (xargs :stobjs $sat))
  (cond
   ((not (valid-varp var))
    (cond
     ((endp todo-list)
      $sat)
     (t
      (add-new-ce-val1 (caar todo-list) (cdar todo-list)
                       (cdr todo-list) $sat))))
   (t
    (let (($sat (update-ce-i-var-vali var val $sat)))
      (add-new-ce-val1 (car-vari var $sat) (logical-car val)
                       (cons (cons (cdr-vari var $sat) (logical-cdr val))
                             todo-list)
                       $sat)))))

;; Add that the variable "var" is equal to "val" in the
;; counter-example.  I think I can remove the quote!!!
;; However, having it there allows us to distinguish between
;; having no value for a variable and having the nil value.
;; Of course, we could use a Boolean array for that.
(defun add-new-ce-val (var val $sat)
  (declare (xargs :stobjs $sat))
  (let (($sat (add-new-ce-val1 var val nil $sat)))
    (mv val $sat)))

;; Look through the eq-alist for an entry
;; (eq x a) s.t. a already has a value and
;; (eq x a) is true.  In that case the value
;; of x should be set to the value of a.
(defun known-eq-val1 (eq-alist non-nil non-t non-cons-list $sat)
  (declare (xargs :stobjs $sat))
  (cond
   ((endp eq-alist)
    (mv nil nil non-nil non-t non-cons-list))
   (t
    (let* ((a (caar eq-alist))
           (eq-x-a (cdar eq-alist))
           (a-val (ce-i-var-vali a $sat))
           (eq-x-a-val (equal (ce-vali eq-x-a $sat) 1)))
      (cond
       ((ce-val-unknownp a-val)
        (mv (er hard 'known-eq-val1
                "Unknown value for previous variable in counter-example generation")
            nil nil nil nil))
       (eq-x-a-val
        (mv t
            a-val
            (not (eq a-val nil))
            (not (eq a-val t))
            non-cons-list))
       ((eq a-val nil)
        (known-eq-val1 (cdr eq-alist) t non-t non-cons-list $sat))
       ((eq a-val t)
        (known-eq-val1 (cdr eq-alist) non-nil t non-cons-list $sat))
       ((consp a-val)
        (known-eq-val1 (cdr eq-alist)
                       non-nil
                       non-t
                       (cons a-val non-cons-list)
                       $sat))
       (t
        (known-eq-val1 (cdr eq-alist) non-nil non-t non-cons-list $sat)))))))

(defun known-eq-val (var non-nil non-t non-cons-list $sat)
  (declare (xargs :stobjs $sat))
  (let ((eq-alist (eq-alist-vari var $sat)))
    (known-eq-val1 eq-alist non-nil non-t non-cons-list $sat)))

(defun car-non-cons-list (non-cons-list car-non-nil car-non-t car-non-cons-list)
  (cond
   ((endp non-cons-list)
    (mv car-non-nil car-non-t car-non-cons-list))
   ((eq (caar non-cons-list) nil)
    (car-non-cons-list (cdr non-cons-list) t car-non-t car-non-cons-list))
   ((eq (caar non-cons-list) t)
    (car-non-cons-list (cdr non-cons-list) car-non-nil t car-non-cons-list))
   ((consp (caar non-cons-list))
    (car-non-cons-list (cdr non-cons-list)
                         car-non-nil
                         car-non-t
                         (cons (caar non-cons-list) car-non-cons-list)))
   (t
    (car-non-cons-list (cdr non-cons-list) car-non-nil car-non-t car-non-cons-list))))

(defun cdr-non-cons-list (non-cons-list cdr-non-nil cdr-non-t cdr-non-cons-list)
  (cond
   ((endp non-cons-list)
    (mv cdr-non-nil cdr-non-t cdr-non-cons-list))
   ((eq (cdar non-cons-list) nil)
    (cdr-non-cons-list (cdr non-cons-list) t cdr-non-t cdr-non-cons-list))
   ((eq (cdar non-cons-list) t)
    (cdr-non-cons-list (cdr non-cons-list) cdr-non-nil t cdr-non-cons-list))
   ((consp (cdar non-cons-list))
    (cdr-non-cons-list (cdr non-cons-list)
                         cdr-non-nil
                         cdr-non-t
                         (cons (cdar non-cons-list) cdr-non-cons-list)))
   (t
    (cdr-non-cons-list (cdr non-cons-list) cdr-non-nil cdr-non-t cdr-non-cons-list))))

(defun ce-var-check (var non-nil non-t non-cons-const $sat)
  (declare (xargs :stobjs $sat))
  (if (not (valid-varp var))
      (mv nil nil nil nil non-nil non-t non-cons-const)
    (mv-let
     (eq-atom atom-val non-nil non-t)
     (known-eq-atom var non-nil non-t $sat)
     (mv-let
      (consp-known consp-val)
      (known-consp var $sat)
      (mv-let
       (eq-val-known eq-val non-nil non-t non-cons-const)
       (known-eq-val var non-nil non-t non-cons-const $sat)
       (cond
        (eq-atom
         (mv t atom-val consp-known consp-val non-nil non-t non-cons-const))
        (eq-val-known
         (mv t eq-val consp-known consp-val non-nil non-t non-cons-const))
        (t
         (mv nil nil consp-known consp-val non-nil non-t non-cons-const))))))))

;; Evaluate the intermediate expression i-expr, under
;; the current satisfying instance.
(defun eval-i-expr (i-expr $sat)
  (declare (xargs :stobjs $sat))
  (cond
   ((atom i-expr)
    (ce-i-var-vali i-expr $sat))
   ((quotep i-expr)
    (unquote i-expr))
   ((eq (car i-expr) 'consp)
    (ce-val-consp (eval-i-expr (cadr i-expr) $sat)))
   ((eq (car i-expr) 'cons)
    (ce-val-cons (eval-i-expr (cadr i-expr) $sat)
                 (eval-i-expr (caddr i-expr) $sat)))
   ((eq (car i-expr) 'equal)
    (ce-val-equal (eval-i-expr (cadr i-expr) $sat)
                  (eval-i-expr (caddr i-expr) $sat)))
   (t
    (er hard 'eval-i-expr
        "Invalid i-expression: ~x0~%"
        i-expr))))

;; Determine whether an f-expr is true in the
;; current counter-example.
(defun ce-true-f-exprp (f-expr $sat)
  (declare (xargs :stobjs $sat))
  (cond
   ((eq 't f-expr)
    t)
   ((eq 'nil f-expr)
    nil)
   ((< 0 f-expr)
    (eq (ce-vali f-expr $sat) 1))
   (t
    (eq (ce-vali (- f-expr) $sat) 0))))

;; Return true if all of the literals in cnf-lits
;; are false (meaning that the last literal must be true).
(defun ce-cnf-lits-unsatp (cnf-lits $sat)
  (declare (xargs :stobjs $sat))
  (cond
   ((endp cnf-lits)
    t)
   ((ce-true-f-exprp (car cnf-lits) $sat)
    nil)
   (t
    (ce-cnf-lits-unsatp (cdr cnf-lits) $sat))))

(defun ce-var-iete-list (iete-list $sat)
  (declare (xargs :stobjs $sat))
  (cond
   ((endp iete-list)
    (mv nil nil))
   ((ce-cnf-lits-unsatp (iete-cnf-lits (car iete-list)) $sat)
    (mv t (eval-i-expr (iete-expr (car iete-list)) $sat)))
   (t
    (ce-var-iete-list (cdr iete-list) $sat))))

(defun ce-var-cete-list (cete-list $sat)
  (declare (xargs :stobjs $sat))
  (cond
   ((endp cete-list)
    (mv nil nil nil))
   ((ce-cnf-lits-unsatp (cete-cnf-lits (car cete-list) $sat) $sat)
    (mv t (cete-car (car cete-list) $sat) (cete-cdr (car cete-list) $sat)))
   (t
    (ce-var-cete-list (cdr cete-list) $sat))))

;; Note: the non-cons-const argument is a list of cons structures
;; we know var is NOT equal to.
(defun ce-var1 (var t-struct non-nil non-t non-cons-const $sat)
  (declare (xargs :stobjs $sat))
  (cond
   (t-struct
    (mv-let
     (known-val val)
     (ce-var-iete-list (ts-iete-list t-struct) $sat)
     (cond
      (known-val
       (add-new-ce-val var val $sat))
      (t
       (mv-let
        (known-cons car-t-struct cdr-t-struct)
        (ce-var-cete-list (ts-cete-list t-struct) $sat)
        (cond
         (known-cons
          (mv-let
           (car-val $sat)
           (ce-var1 (car-vari var $sat) car-t-struct non-nil non-t
                    non-cons-const $sat)
           (mv-let
            (cdr-val $sat)
            (ce-var1 (cdr-vari var $sat) cdr-t-struct non-nil non-t
                     non-cons-const $sat)
            (add-new-ce-val var (cons car-val cdr-val) $sat))))
         (t
          (ce-var1 var nil non-nil non-t non-cons-const $sat))))))))
   (t
    (mv-let
     (known-val val consp-known consp-val non-nil non-t non-cons-const)
     (ce-var-check var non-nil non-t non-cons-const $sat)
     (cond
      (known-val
       (add-new-ce-val var val $sat))
      ((or (and consp-known consp-val)
           (and (not consp-known)
                (or (valid-varp (car-vari var $sat))
                    (valid-varp (cdr-vari var $sat)))))
       (mv-let
        (car-non-nil car-non-t car-non-cons-list)
        (car-non-cons-list non-cons-const nil nil nil)
        (mv-let
         (cdr-non-nil cdr-non-t cdr-non-cons-list)
         (cdr-non-cons-list non-cons-const nil nil nil)
         ;; We need to be consistent with the ordering used in
         ;; compare-cons-structure, so that an rhs value is always
         ;; built before an lhs value.  To do this, we just
         ;; need to make sure we go down the car first.
         (mv-let
          (car-val $sat)
          (ce-var1 (car-vari var $sat)
                   nil
                   car-non-nil
                   car-non-t
                   car-non-cons-list
                   $sat)
          (mv-let
           (cdr-val $sat)
           (ce-var1 (cdr-vari var $sat)
                    nil
                    cdr-non-nil
                    cdr-non-t
                    cdr-non-cons-list
                    $sat)
           (add-new-ce-val var (cons car-val cdr-val) $sat))))))
      ((not non-nil)
       (add-new-ce-val var nil $sat))
      ((not non-t)
       (add-new-ce-val var t $sat))
      ;; At this point we can't use nil or t.  We can use any
      ;; symbol that doesn't occur in the atom list, but to make
      ;; our life easy we pick a symbol that has never been used
      ;; in the counter-example, nor will it ever be used again.
      (t
       (mv-let
        (unused-num $sat)
        (get-unused-number $sat)
        (add-new-ce-val var
                        (intern-in-package-of-symbol
                         (concat "X" (num-to-str unused-num))
                         'X)
                        $sat))))))))

;; Find the counter-example value of a given variable.
;; The philosophy here is to choose a cons if the
;; car and cdr are relevant, otherwise choose nil, unless
;; it has to be true.

(defun ce-var (var $sat)
  (declare (xargs :stobjs $sat))
  (ce-var1 var (todo-structi var $sat) nil nil nil $sat))

(defun ce-var-list (var-list $sat)
  (declare (xargs :stobjs $sat))
  (cond
   ((endp var-list)
    $sat)
   (t
    (mv-let
     (val $sat)
     (ce-var (car var-list) $sat)
     (declare (ignore val))
     (ce-var-list (cdr var-list) $sat)))))

(defun get-ce-alist (input-alist ans $sat)
  (declare (xargs :stobjs $sat))
  (if (endp input-alist)
      ans
    (let* ((entry (car input-alist))
           (input (car entry))
           (var (cdr entry))
           (val (ce-i-var-vali var $sat)))
      (get-ce-alist (cdr input-alist) (cons (cons input val) ans) $sat))))

(defun btoi (x) (if x 1 0))

(defun add-ce-vals (n inst-list $sat)
  (declare (xargs :stobjs $sat))
  (if (endp inst-list)
      $sat
    (let* (($sat (update-ce-vali n (btoi (car inst-list)) $sat)))
      (add-ce-vals (1+ n) (cdr inst-list) $sat))))

(defun ce-list-i-expr-vals (i-expr-list acc $sat)
  (declare (xargs :stobjs $sat))
  (cond
   ((endp i-expr-list)
    (revappend acc nil))
   (t
    (ce-list-i-expr-vals (cdr i-expr-list)
                         (cons (eval-i-expr (car i-expr-list) $sat)
                               acc)
                         $sat))))

(defun ce-un-fn-val-alist (ufe-list acc $sat)
  (declare (xargs :stobjs $sat))
  (cond
   ((endp ufe-list)
    acc)
   (t
    (let ((arg-vals (ce-list-i-expr-vals (ufe-arg-list (car ufe-list)) nil
                                         $sat)))
      (cond
       ((assoc-equal arg-vals acc)
        ;; We already have this entry
        (ce-un-fn-val-alist (cdr ufe-list) acc $sat))
       (t
        ;; We don't have this entry yet so we should look it up.
        (let ((call-val (ce-i-var-vali (ufe-top-var (car ufe-list)) $sat)))
          (ce-un-fn-val-alist (cdr ufe-list)
                              (cons (cons arg-vals call-val)
                                    acc)
                              $sat))))))))

(defun add-ce-un-fn-vals (un-fn-list $sat)
  (declare (xargs :stobjs $sat))
  (cond
   ((endp un-fn-list)
    $sat)
   (t
    (let* ((fn (car un-fn-list))
           (ufe-list (lookup-ufe-list fn nil $sat))
           (ce-un-fn-val-alist (ce-un-fn-val-alist ufe-list nil $sat))
           ($sat (set-un-fn-vals fn ce-un-fn-val-alist $sat)))
      (add-ce-un-fn-vals (cdr un-fn-list) $sat)))))

#|
(defun gen-ce (sat-output $sat)
  (declare (xargs :stobjs $sat))
  (prog2$
   (cw "Generating counter-example~%")
   (let* (($sat (resize-ce-val 0 $sat))
          ($sat (resize-ce-i-var-val 0 $sat))
          ($sat (resize-ce-val *max-vars* $sat))
          ($sat (resize-ce-i-var-val *max-vars* $sat))
          ($sat (add-ce-vals 1 (sat-inst-list sat-output) $sat))
          ($sat (ce-var-list (completed-var-list $sat) 0 $sat))
          ($sat (add-ce-un-fn-vals (un-fn-list $sat) $sat))
          (ce-alist (get-ce-alist (rev-append (input-alist $sat) nil) nil $sat)))
     (mv ce-alist $sat))))
|# ;|

#|
(mutual-recursion
(defun run-ce-expr-list (expr-list ce-alist acc $sat state)
  (declare (xargs :stobjs $sat))
  (cond
   ((endp expr-list)
    (mv (revappend acc nil) $sat state))
   (t
    (mv-let
     (err car-val $sat state)
     (run-ce-expr (car expr-list) ce-alist $sat state)
     (declare (ignore err))
     (run-ce-expr-list (cdr expr-list) ce-alist
                       (cons car-val acc) $sat state)))))

;; Run the counter-example on an expression, looking up
;; uninterpreted function values from the un-fn-world as
;; needed.  Note expr must be a translated expression---no
;; macros or unquoted constants please!

;; Also this function assumes that the world has been
;; already updated with the executable information on each
;; function---as the recognizer and run-ce does!
(defun run-ce-expr (expr ce-alist $sat state)
  (declare (xargs :stobjs $sat))
  (cond
   ((atom expr)
    ;; The first value just exists to keep this from
    ;; being an event tuple.
    (mv 'no-error (cdr (assoc-equal expr ce-alist)) $sat state))
   ((quotep expr)
    (mv 'no-error (unquote expr) $sat state))
   (t
    (let* ((fn (car expr))
           (exec-info (lookup-executable fn 'not-found $sat)))
      (cond
       ((eq exec-info 'not-found)
        ;; We must not have used the recognizer on this
        ;; expression.
        (let* ((fn-list (needed-fn-expr expr nil nil $sat))
               ($sat (add-mem-entries fn-list $sat state)))
          ;; It won't happen again
          (run-ce-expr expr ce-alist $sat state)))
       (t
        (mv-let
         (arg-vals $sat state)
         (run-ce-expr-list (cdr expr) ce-alist nil $sat state)
         (cond
          ((ce-val-unknown-listp arg-vals)
           ;; If one of the arguments is an unknown value, then
           ;; we return unknown.
           (mv nil 'sat::unknown $sat state))
          (exec-info
           (let ((arg-vals (quote-list arg-vals nil)))
             (mv-let
              (erp val state)
              (simple-translate-and-eval (cons (car expr) arg-vals)
                                         nil
                                         nil ;;'($sat)
                                         "Counter-example check"
                                         "run-ce"
                                         (w state)
                                         state)
              (if erp
                  (mv (er hard 'run-ce "Unable to run counter-example~%")
                      nil $sat state)
                (mv 'no-error (cdr val) $sat state)))))
          ((uninterpreted-fnp fn $sat state)
           (let* ((un-fn-val-alist (lookup-un-fn-vals fn nil $sat))
                  (val-entry (assoc-equal arg-vals un-fn-val-alist)))
             (if val-entry
                 (mv 'no-error (cdr val-entry) $sat state)
               (mv (er hard 'run-ce-expr
                       "The unterpreted function ~x0 has no entry for the ~
                        argument list ~x1~%"
                       fn arg-vals)
                   nil $sat state))))
          (t
           (run-ce-expr (fn-body fn state)
                        (add-to-alist (fn-formals fn state) arg-vals nil)
                        $sat state))))))))))
)

;; Return t if the input-clause disjunction has any non-nil
;; literal expressions.
(defun run-ce (input-clause ce-alist $sat state)
  (declare (xargs :stobjs $sat))
  (cond
   ((endp input-clause)
    (mv 'no-error nil $sat state))
   (t
    (mv-let
     (err val $sat state)
     (run-ce-expr (car input-clause) ce-alist $sat state)
     (declare (ignore err))
     (if val
         (mv 'no-error t $sat state)
       (run-ce (cdr input-clause) ce-alist $sat state))))))

(set-irrelevant-formals-ok t)
(defun print-ce-ins (ce-alist)
  (if (endp ce-alist)
      nil
    (let* ((entry (car ce-alist))
           (input-var (car entry))
           (val (cdr entry)))
      (prog2$
       (cw "~x0: ~x1~%" input-var val)
       (print-ce-ins (cdr ce-alist))))))

(defun print-ce-un-fn (fn un-fn-val-alist)
  (cond
   ((endp un-fn-val-alist)
    nil)
   (t
    (let ((arg-vals (quote-list (caar un-fn-val-alist) nil))
          (call-val (cdar un-fn-val-alist)))
      (prog2$
       (cw "~x0: ~x1~%" (cons fn arg-vals) call-val)
       (print-ce-un-fn fn (cdr un-fn-val-alist)))))))

(defun print-ce-un-fn-list (un-fn-list $sat)
  (declare (xargs :stobjs $sat))
  (cond
   ((endp un-fn-list)
    nil)
   (t
    (let* ((fn (car un-fn-list))
           (un-fn-val-alist (lookup-un-fn-vals fn nil $sat))
           (val (print-ce-un-fn fn un-fn-val-alist)))
      (declare (ignore val))
      (print-ce-un-fn-list (cdr un-fn-list) $sat)))))

(defun print-ce (ce-alist $sat)
  (declare (xargs :stobjs $sat))
  (let* ((val1 (print-ce-ins ce-alist))
         (val2 (print-ce-un-fn-list (un-fn-list $sat) $sat)))
    (declare (ignore val1 val2))
    nil))
(set-irrelevant-formals-ok nil)
|# ;|