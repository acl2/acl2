
(IN-PACKAGE "ACL2")

(include-book "bv-lib" :skip-proofs-okp t :ttags (sat sat-cl))
(include-book "redundancy-removal" :ttags (sat sat-cl smt))
(include-book "misc/expander" :dir :system)
(include-book "../clause-processors/sym-str")

(set-state-ok t)
(program)

(defun make-hyp-axiom-name (hyp-number)
  (symbol-from-str-num "SMT-HYP-AXIOM-"
                       hyp-number))

;; I don't use symsim directly, since I don't want to translate the formula

(defun smt-symsim (expr hyps hints state)
  (mv-let
   (erp tuples-lst state)
   (tool-fn expr hyps t 'iff state hints 'try nil nil t 'smt-symsim)
   (cond
    (erp
     (mv expr state))
    (t
     (mv (caddr (car tuples-lst)) state)))))

#| ;; A more safe version of smt-symsim (doesn't rely on the internal function tool-fn
(defun smt-symsim (expr hints state)
  (mv-let
   (erp symsim-ans state)
   (symsim-fn expr nil hints 'try 'nil 'nil (w state) state)
   (cond
    (erp
     (mv-let
      (erp expr state)
      (translate term t t t 'top-level (w state) state)
      (declare (ignore erp))
      (mv expr state)))
    (t
     (let ((expr (caddr (car symsim-ans))))
       (mv expr state))))))
|# ;|

;;(smt-symsim expr hints state))))))

(defun smt-rewrite-hyp (expr formula raw-bv-theory-name state)
  (mv-let
   (erp expr state)
   (translate expr t t t 'top-level (w state) state)
   (cond
    (erp
     (mv (er hard 'smt-rewrite-hyp "ERROR: Unable to translate SMT expression: ~
                               ~x0~%"
             expr)
         formula
         state))
    (t
     (mv-let
      (expr state)
      (smt-symsim expr nil nil state)
      (cond
       ((quotep expr)
        (mv expr formula state))
       ((quotep formula)
        (mv-let
          (expr state)
          (smt-symsim expr
                      nil
                      `(("Goal" :in-theory (theory (quote ,raw-bv-theory-name))))
                      state)
          (mv expr formula state)))
       (t
        (mv-let
         (formula state)
         (smt-symsim formula (list expr) nil state)
         (mv-let
          (expr state)
          (smt-symsim expr
                      nil
                      `(("Goal" :in-theory (theory (quote ,raw-bv-theory-name))))
                      state)
          (mv expr formula state))))))))))

(defun smt-rewrite-hyp-list (hyp-list formula raw-bv-theory-name acc state)
  (cond
   ((endp hyp-list)
    (mv nil acc formula state))
   (t
    (mv-let
     (expr formula state)
     (smt-rewrite-hyp (car hyp-list) formula raw-bv-theory-name state)
     (cond
      ((and (quotep formula) (not (unquote formula)))
       ;; We've reduced the formula to true
       (mv t nil nil state))
      ((quotep expr)
       (cond
        ((unquote expr)
         ;; We've reduced a literal to false, so we don't need it
         (smt-rewrite-hyp-list (cdr hyp-list) formula raw-bv-theory-name
                               acc state))
        (t
         ;; We've reduced a literal to true, so the clause is true
         (mv t nil nil state))))
      (t
       (smt-rewrite-hyp-list (cdr hyp-list)
                             formula
                             raw-bv-theory-name
                             (cons expr acc)
                             state)))))))

(defun smt-rewrite (hyp-list formula raw-bv-theory-name state)
  (mv-let
   (erp formula state)
   (translate formula t t t 'top-level (w state) state)
   (cond
    (erp
     (mv nil
         (er hard 'smt-rewrite "ERROR: Unable to translate SMT expression: ~
                               ~x0~%"
             formula)
         state))
    (t
     (mv-let
      (formula state)
      (smt-symsim formula nil nil state)
      (cond
       ((and (quotep formula) (not (unquote formula)))
        (mv t nil state))
       (t
        (mv-let
         (soln hyp-list formula state)
         (smt-rewrite-hyp-list hyp-list formula raw-bv-theory-name nil state)
         (cond
          (soln
           (mv t nil state))
          ((quotep formula)
           (mv nil hyp-list state))
          (t
           (mv-let
            (formula state)
            (smt-symsim formula
                        nil
                        `(("Goal" :in-theory (theory (quote ,raw-bv-theory-name))))
                        state)
            (mv nil (cons formula hyp-list) state))))))))))))


(defun smt-sat-add-hyp-list (hyp-list $sat $sat-plus state)
  (declare (xargs :stobjs ($sat $sat-plus)))
  (cond
   ((endp hyp-list)
    (mv $sat $sat-plus state))
   (t
    (mv-let
     ($sat $sat-plus state)
     (smt-sat-add-expr (car hyp-list) $sat $sat-plus state)
     (smt-sat-add-hyp-list (cdr hyp-list) $sat $sat-plus state)))))

(defun smt-solve1 (hyp-list formula raw-bv-theory-name $sat $sat-plus state)
  (declare (xargs :stobjs ($sat $sat-plus)))
  (mv-let
   (solved hyp-list state)
   (time$ (smt-rewrite hyp-list formula raw-bv-theory-name state))
   (cond
    (solved
     ;; If it's solved that means a hypothesis simplified to false.
     (mv 'unsat $sat $sat-plus state))
    (t
     ;; Otherwise, use the SAT solver
     (time$
      (mv-let
       ($sat $sat-plus state)
       (smt-sat-add-hyp-list hyp-list $sat $sat-plus state)
       (mv-let
        (erp soln $sat state)
        (smt-sat-solve $sat state)
        (declare (ignore erp))
        (mv soln $sat $sat-plus state))))))))

(defun smt-solve (hyp-list formula extrafuns raw-bv-theory-name $sat $sat-plus
                           state)
  (declare (xargs :stobjs ($sat $sat-plus)))
  (let* (($sat-plus (zero-sat-plus-stobj $sat-plus))
         ($sat-plus (construct-sat-plus-stobj $sat-plus))
         ($sat-plus (add-extra-fn-list extrafuns $sat-plus)))
  (mv-let
   (erp $sat state)
   (sat-new-problem $sat state)
   (declare (ignore erp))
   (mv-let
    (ans $sat $sat-plus state)
    (smt-solve1 hyp-list formula raw-bv-theory-name $sat $sat-plus state)
    (mv-let
     (erp $sat state)
     (sat-end-problem $sat state)
     (declare (ignore erp))
     (mv ans $sat $sat-plus state))))))

(defun write-msg (str file-name $sat $sat-plus state)
  (declare (xargs :stobjs ($sat $sat-plus)))
  (mv-let
   (channel state)
   (open-output-channel file-name :character state)
   (let* ((state (fms! "~s0~%" (list (cons #\0 str)) channel state nil))
          (state (close-output-channel channel state)))
     (mv $sat $sat-plus state))))

(defun smt-check-fn (hyp-list formula extrafuns raw-bv-theory-name expected-ans msg-file $sat $sat-plus state)
  (declare (xargs :stobjs ($sat $sat-plus)))
  (mv-let
   (ans $sat $sat-plus state)
   (smt-solve hyp-list formula extrafuns raw-bv-theory-name $sat $sat-plus state)
   (cond
    ((and (not (equal ans 'sat)) (not (equal ans 'unsat)))
     (write-msg "INTERNAL ERROR" msg-file $sat $sat-plus state))
    ((and (equal ans 'sat)
          (equal expected-ans 'unsat))
     (write-msg "SAT---ERROR: Expected unsat"
                msg-file $sat $sat-plus state))
    ((and (equal ans 'sat)
          (equal expected-ans 'sat))
     (write-msg "SAT---as expected."
                msg-file $sat $sat-plus state))
    ((and (equal ans 'sat)
          (equal expected-ans 'unknown))
     (write-msg "SAT"
                msg-file $sat $sat-plus state))
    ((equal ans 'sat)
     (write-msg "SAT---ERROR: Unrecognized expectation"
                msg-file $sat $sat-plus state))
    ((equal expected-ans 'unsat)
     (write-msg "UNSAT---as expected."
                msg-file $sat $sat-plus state))
    ((equal expected-ans 'sat)
     (write-msg "UNSAT---ERROR: Expected sat."
                msg-file $sat $sat-plus state))
    ((equal expected-ans 'unknown)
     (write-msg "UNSAT"
                msg-file $sat $sat-plus state))
    (t
     (write-msg "UNSAT---ERROR: Unrecognized expectation"
                msg-file $sat $sat-plus state)))))

(defmacro smt-check (hyp-list formula extrafuns raw-bv-theory-name expected-ans msg-file)
  `(smt-check-fn (quote ,hyp-list)
                 (quote ,formula)
                 (quote ,extrafuns)
                 (quote ,raw-bv-theory-name)
                 (quote ,expected-ans)
                 ,msg-file
                 $sat $sat-plus state))

