
;; In this section I implement a simple simplifier
;; for a Boolean CNF clause list---duplicate literals 
;; within a clause are deleted and clauses with a 
;; literal and its negation are removed.
;;
;; Some SAT solvers require these simplifications 
;; be performed before the CNF formula is passed to
;; them.

(in-package "SAT")
(program)
(set-state-ok t)

(include-book "sat-setup")

;; Returns the negation of an f-expression.
(defun negate-f-expr (f0) 
  (cond
   ((integerp f0)
    (- f0))
   ((eq f0 *f-false*)
    *f-true*)
   ((eq f0 *f-true*)
    *f-false*)
   (t
    (er hard 'negate-f-expr
        "Invalid f-expression:~x0~%"
        f0))))

(defun remove-lit (lit $sat)
  (declare (xargs :stobjs $sat))
  (if (posp lit)
      (update-pos-vari lit
                       0
                       $sat)
    (update-neg-vari (- lit)
                     0
                     $sat)))

(defun remove-old (clause $sat)
  (declare (xargs :stobjs $sat))
  (if (endp clause)
      $sat
    (let (($sat (remove-lit (car clause) $sat)))
      (remove-old (cdr clause) $sat))))

(defun add-lit (lit $sat)
  (declare (xargs :stobjs $sat))
  (if (posp lit)
      (update-pos-vari lit
                       1
                       $sat)
    (update-neg-vari (- lit)
                     1
                     $sat)))

(defun oposite-lit (lit $sat)
  (declare (xargs :stobjs $sat))
  (if (posp lit)
      (equal 1 (neg-vari lit $sat))
    (equal 1 (pos-vari (- lit) $sat))))

(defun duplicate-lit (lit $sat)
  (declare (xargs :stobjs $sat))
  (if (posp lit)
      (equal 1 (pos-vari lit $sat))
    (equal 1 (neg-vari (- lit) $sat))))

;; Perform Local Clause Optimizations---remove
;; duplicate literals and clauses with oposing
;; literals.
(defun local-clause-opt (clause ans $sat)
  (declare (xargs :stobjs $sat))
  (cond 
   ((endp clause)
    (let (($sat (remove-old ans $sat)))
      (mv nil ans $sat)))
   ((not (integerp (car clause)))
    (cond 
     ((eq *f-false* (car clause))
      (local-clause-opt (cdr clause) ans $sat))
     ((eq *f-true* (car clause))
      (let (($sat (remove-old ans $sat)))
        (mv t nil $sat)))
     (t
      (mv (er hard 'local-clause-opt
              "Illegal f-expression: ~x0~%"
              (car clause))
          ans
          $sat))))
   ((duplicate-lit (car clause) $sat)
    (local-clause-opt (cdr clause) ans $sat))
   ((oposite-lit (car clause) $sat)
    (let (($sat (remove-old ans $sat)))
      (mv t nil $sat)))
   (t 
    (let (($sat (add-lit (car clause) $sat)))
      (local-clause-opt
       (cdr clause)
       (cons (car clause) ans)
       $sat)))))

;; Add a clause to the SAT input channel
(defun add-cnf-clause (clause $sat state)
  (declare (xargs :stobjs $sat))
  (mv-let 
   (always-true clause $sat)
   (local-clause-opt clause nil $sat)
   (cond 
    (always-true
     (mv $sat state))
    (clause
     (let* (($sat (update-num-f-clauses (1+ (num-f-clauses $sat)) $sat))
            (state (print-object$-ser clause nil (sat-input-channel $sat)
                                      state)))
       (mv $sat state)))
    (t 
     ;; At this point we have reduced the clause to false!
     ;; Therefore the formula is unsatisfiable.  We'll let
     ;; the SAT solver figure this out though.
     (mv-let
      (f-var $sat)
      (++f-var $sat)
      (let* (($sat (update-num-f-clauses (+ 2 (num-f-clauses $sat)) $sat))
             (state (print-object$-ser (list f-var)
                                       nil
                                       (sat-input-channel $sat)
                                       state))
             (state (print-object$-ser (list (- f-var))
                                       nil
                                       (sat-input-channel $sat)
                                       state)))
        (mv $sat state)))))))
