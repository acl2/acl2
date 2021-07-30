
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

; Added by Matt K. 10/20/2013: With the soundness bug fix committed today, we
; get a failure when certifying
; books/clause-processors/SULFA/books/sat-tests/benchmark.lisp, because
; guard-checking is, in essence, being coerced to :none or :all so that *1*
; functions are called all the way down to stobj updaters with non-trivial
; guards.  The following function, sat::add-cnf-clause, calls updater
; sat::update-num-f-clauses, so has this coerced behavior, as do functions all
; the way up the call stack to acl2::sat.  Because the *1* function for
; sat::add-cnf-clause is being called with guard-checking treated as :all or
; :none, the *1* function is being called for print-object$-ser, and that leads
; to a guard violation because (judging from the channel's name) there is an
; attempt to write to an input channel.  I'm working around this problem by
; introducing the following :program mode wrapper for print-object$-ser.  Note
; that with one obscure exception (32-bit-integer-stack), fields of the state
; do not get this special guard-coercion treatment; so the workaround is
; successful.  Of course, it might be better to provide a "real" fix, to avoid
; writing to an input channel; but I'm not inclined to put in the effort, since
; I don't know the details of this work.

; Matt K. mod, 7/2021: print-object$-ser is now print-object$-fn.
(defun print-object$-fn-wrapper (x serialize-character channel state)
  (print-object$-fn x serialize-character channel state))

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
            (state (print-object$-fn-wrapper clause nil (sat-input-channel $sat)
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
             (state (print-object$-fn-wrapper (list f-var)
                                              nil
                                              (sat-input-channel $sat)
                                              state))
             (state (print-object$-fn-wrapper (list (- f-var))
                                              nil
                                              (sat-input-channel $sat)
                                              state)))
        (mv $sat state)))))))
