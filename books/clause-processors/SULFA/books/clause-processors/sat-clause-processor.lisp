
(in-package "ACL2")

(include-book "../sat/sat" :ttags (sat))

(set-state-ok t)
(program)

(defun sat-cl-property-status ($sat)
  (declare (xargs :stobjs $sat))
  (car (sat-external-value $sat)))

(defun sat-cl-update-property-status (val $sat)
  (declare (xargs :stobjs $sat))
  (sat-update-external-value
   (list* val (cdr (sat-external-value $sat)))
   $sat))

(defun sat-cl-marked-un-fns ($sat)
  (declare (xargs :stobjs $sat))
  (cadr (sat-external-value $sat)))

(defun sat-cl-update-marked-un-fns (val $sat)
  (declare (xargs :stobjs $sat))
  (sat-update-external-value
   (list* (car (sat-external-value $sat)) val
          (cddr (sat-external-value $sat)))
   $sat))

(defun sat-cl-ce-alist ($sat)
  (declare (xargs :stobjs $sat))
  (caddr (sat-external-value $sat)))

(defun sat-cl-update-ce-alist (val $sat)
  (declare (xargs :stobjs $sat))
  (sat-update-external-value
   (list* (car (sat-external-value $sat))
          (cadr (sat-external-value $sat))
          val
          (cdddr (sat-external-value $sat)))
   $sat))

;; ---------------------------------------------------
;; A macro to help with running counter-examples
;; ---------------------------------------------------

;; If you want to see what (f (g x)) evaluates
;; to under the current counterexample, type
;; (sat-cl-ce (f (g x)))

;; Note: It doesn't currently work with uninterpreted
;; functions.

(defmacro sat-cl-ce (expr)
  `(mv-let
    (erp val state)
    (simple-translate-and-eval (quote ,expr)
                               (sat-cl-ce-alist $sat)
                               nil
                               "User create ce"
                               "sat-cl-ce"
                               (w state)
                               state

; Matt K.: I added the argument aok=nil for v4-0.  Thus, attachments are
; disallowed.  That's the conservative thing to do, but I don't know if it's
; necessary here (probably is for the next call below of
; simple-translate-and-eval, though).  This decision could be revisited if
; there is interest.

                               nil)
    (mv erp (cdr val) state)))

;; ---------------------------------------------------

(defun sat-cl-get-un-fn-val (x ans)
  (cond
   ((atom x)
    (mv (revappend ans nil) x))
   (t
    (sat-cl-get-un-fn-val (cdr x)
                          (cons (car x) ans)))))

(defun sat-cl-add-un-fn (fn fn-alist alist)
  (cond
   ((endp fn-alist)
    alist)
   (t
    (let ((args (car (car fn-alist)))
          (return-val (cdr (car fn-alist))))
      (sat-cl-add-un-fn fn (cdr fn-alist)
                        (cons (cons (cons fn args) return-val)
                              alist))))))

(defun sat-cl-add-un-fn-list (fn-list alist $sat state)
  (declare (xargs :stobjs $sat))
  (cond
   ((endp fn-list)
    (mv alist $sat state))
   (t
    (mv-let
     (erp un-fn-alist $sat state)
     (sat-si-un-fn-alist (car fn-list) $sat state)
     (declare (ignore erp))
     (sat-cl-add-un-fn-list (cdr fn-list)
                            (sat-cl-add-un-fn (car fn-list)
                                              un-fn-alist
                                              alist)
                            $sat state)))))

(defun sat-cl-update-current-ce ($sat state)
  (declare (xargs :stobjs $sat))
  (mv-let
   (erp fn-list $sat state)
   (sat-un-fn-list $sat state)
   (declare (ignore erp))
   (mv-let
    (erp alist $sat state)
    (sat-si-input-alist $sat state)
    (declare (ignore erp))
    (mv-let
     (alist $sat state)
     (sat-cl-add-un-fn-list fn-list alist $sat state)
     (let (($sat (sat-cl-update-ce-alist alist $sat)))
       (mv $sat state))))))

(defun sat-cl-print-alist (alist)
  (cond
   ((endp alist)
    nil)
   (t
    (prog2$
     (cw "~x0: ~x1~%" (caar alist) (cdar alist))
     (sat-cl-print-alist (cdr alist))))))

(defun sat-cl-print-ce ($sat)
  (declare (xargs :stobjs $sat))
  (sat-cl-print-alist (sat-cl-ce-alist $sat)))

(defun sat-cl-update-and-print-ce ($sat state)
  (declare (xargs :stobjs $sat))
  (mv-let
   ($sat state)
   (sat-cl-update-current-ce $sat state)
   (prog2$
    (sat-cl-print-ce $sat)
    (mv $sat state))))

(defun sat-cl-add-input-literal-list (input-lit-list $sat state)
  (declare (xargs :stobjs $sat))
  (cond
   ((endp input-lit-list)
    (mv $sat state))
   (t
    (mv-let
     (erp $sat state)
     (sat-add-expr t (car input-lit-list) $sat state)
     (declare (ignore erp))
     (sat-cl-add-input-literal-list (cdr input-lit-list)
                                 $sat
                                 state)))))

(defun sat-cl-clause-in-SULFA (clause $sat state)
  (declare (xargs :stobjs $sat))
  (cond
   ((endp clause)
    (mv t nil $sat state))
   (t
    (mv-let
     (erp in-SULFA sat-package-symbols $sat state)
     (sat-in-SULFA (car clause) $sat state)
     (declare (ignore erp))
     (cond
      (sat-package-symbols
       (mv nil t $sat state))
      ((not in-SULFA)
       (mv nil nil $sat state))
      (t
       (sat-cl-clause-in-SULFA (cdr clause) $sat state)))))))

(defun sat-cl-handle-un-fn-markers1 (un-fn-list $sat state)
  (declare (xargs :stobjs $sat))
  (cond
   ((endp un-fn-list)
    (mv $sat state))
   (t
    (mv-let
     (erp $sat state)
     (sat-mark-uninterpreted (car un-fn-list) $sat state)
     (declare (ignore erp))
     (sat-cl-handle-un-fn-markers1 (cdr un-fn-list) $sat state)))))

(defun sat-cl-start (marked-un-fn-list $sat state)
  (declare (xargs :stobjs $sat))
  (let* ((prev-un-fn-list (sat-cl-marked-un-fns $sat)))
    (cond
     ((and (not marked-un-fn-list) (not prev-un-fn-list))
      (mv-let
       (erp $sat state)
       (sat-new-problem $sat state)
       (declare (ignore erp))
       (mv $sat state)))
     ((not marked-un-fn-list)
      (let (($sat (sat-cl-update-marked-un-fns nil $sat)))
        (mv-let
         (erp $sat state)
         (sat-new-problem! $sat state)
         (declare (ignore erp))
         (mv $sat state))))
     ((equal prev-un-fn-list marked-un-fn-list)
      (mv-let
       (erp $sat state)
       (sat-new-problem $sat state)
       (declare (ignore erp))
       (mv $sat state)))
     (t
      (let (($sat (sat-cl-update-marked-un-fns marked-un-fn-list $sat)))
        (mv-let
         (erp $sat state)
         (sat-new-problem! $sat state)
         (declare (ignore erp))
         (sat-cl-handle-un-fn-markers1 marked-un-fn-list $sat state)))))))

(defun sat-cl-run-clause (input-clause ce-alist state)
  (cond
   ((endp input-clause)
    (mv nil state))
   (t
    (mv-let
     (erp eval-output state)
     (simple-translate-and-eval (car input-clause)
                                ce-alist
                                nil ;;'($sat)
                                "Counter-example check"
                                "run-ce"
                                (w state)
                                state
                                nil) ; see comment about aok above
     (cond
      (erp
       (mv (er hard 'sat-cl-run-clause
               "Counter example check failed.  Perhaps the formula is not ~
                executable.")
           state))
      ((cdr eval-output)
       (mv t state))
      (t
       (sat-cl-run-clause (cdr input-clause) ce-alist state)))))))

(defun sat1 (input-clause marked-un-fn-list check-ce $sat state)
  (declare (xargs :stobjs $sat))
  (let* (($sat (sat-cl-update-property-status 'acl2::unknown $sat)))
    (mv-let
     ($sat state)
     (sat-cl-start marked-un-fn-list $sat state)
     (mv-let
      (in-SULFA sat-package-symbols $sat state)
      (sat-cl-clause-in-SULFA input-clause $sat state)
      (cond
       (sat-package-symbols
        (mv (cons "ERROR: This formula contains symbols in the SAT package, ~
                   but the SAT package is reserved for internal use.~%"
                  nil)
            nil
            $sat
            state))
       ((not in-SULFA)
        (mv (cons "ERROR: This formula is not in ~
                   the decidable Subclass of Unrollable List Formulas in ACL2 (SULFA)~%"
                  nil)
            nil
            $sat
            state))
       (t
        (prog2$
         (cw "The expression is in the decidable ~
              Subclass of Unrollable List Formulas in ACL2 (SULFA).~%")
         (mv-let
          ($sat state)
          (sat-cl-add-input-literal-list input-clause $sat state)
          (mv-let
           (erp soln $sat state)
           (sat-solve $sat state)
           (declare (ignore erp))
           (cond
            ((eq 'unsat soln)
             (mv-let
              (erp $sat state)
              (sat-end-problem $sat state)
              (declare (ignore erp))
              (let* (($sat (sat-cl-update-property-status 'acl2::valid $sat)))
                (prog2$
                 (cw "The SAT solver found no satisfying instance (to the negated formula); ~
                       therefore, the original formula is valid~%")
                 (mv nil '() $sat state)))))
            (t
             (prog2$
              (cw "Generating counter-example:~%")
              (mv-let
               (erp $sat state)
               (sat-generate-satisfying-instance $sat state)
               (declare (ignore erp))
               (mv-let
                ($sat state)
                (sat-cl-update-and-print-ce $sat state)
                (mv-let
                 (erp ce-alist $sat state)
                 (sat-si-input-alist $sat state)
                 (declare (ignore erp))
                 (mv-let
                  (erp $sat state)
                  (sat-end-problem $sat state)
                  (declare (ignore erp))
                  (cond
                   (check-ce
                    (prog2$
                     (cw "Checking counter-example.~%")
                     (mv-let
                      (ce-val state)
                      (sat-cl-run-clause input-clause ce-alist state)
                      (cond
                       (ce-val
                        (prog2$
                         (cw "The formula evaluated to true, so the counter example ~
                            is SPURIOUS.~%")
                         (mv (cons "The SAT-based procedure failed to verify ~
                                     the formula~%"
                                   nil)
                             nil
                             $sat
                             state)))
                       (t
                        (let* (($sat (sat-cl-update-property-status 'acl2::invalid $sat)))
                          (prog2$
                           (cw "The formula evaluated to false, so the ~
                                 counter example is real.~%")
                           (mv (cons "The SAT-based procedure failed to ~
                                       verify the formula~%"
                                     nil)
                               nil
                               $sat
                               state))))))))
                   (marked-un-fn-list
                    (prog2$
                     (cw "Counter-example checking is currently off and ~
                           some abstraction was used.  Therefore, we do not ~
                           know if the counter example is real.~%")
                     (mv (cons "The SAT-based procedure failed to verify ~
                                 the formula~%"
                               nil)
                         nil
                         $sat
                         state)))
                   (t
                    (let* (($sat (sat-cl-update-property-status 'acl2::invalid $sat)))
                      (prog2$
                       (cw "Counter-example checking is currently off, but ~
                           no abstraction was used.  Therefore the ~
                           counter example must be real.~%")
                       (mv (cons "The SAT-based SULFA solver failed to verify ~
                                   the formula~%"
                                 nil)
                           nil
                           $sat
                           state)))))))))))))))))))))

(defun sat-cl-lookup-hint-val (key default sat-hint)
  (let* ((entry (member key sat-hint)))
    (cond
     ((and entry (not (consp (cdr entry))))
      (let ((val (er hard 'sat-cl'start
                     "ERROR: ~s0 requires a value~%"
                     key)))
        (declare (ignore val))
        default))
     (entry
      (cadr entry))
     (t
      default))))

(defun sat (input-clause sat-hint $sat state)
  (declare (xargs :stobjs $sat))
  (sat1 input-clause
        (sat-cl-lookup-hint-val ':uninterpreted-functions 'nil sat-hint)
        (sat-cl-lookup-hint-val ':check-counter-example 't sat-hint)
        $sat
        state))

(define-trusted-clause-processor
  sat
  nil
  :ttag sat-cl)

