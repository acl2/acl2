(in-package "HELP")

(include-book "recommendations")
(include-book "kestrel/utilities/print-levels" :dir :system)
(include-book "std/util/bstar" :dir :system)
(include-book "kestrel/hints/casesx" :dir :system)
(include-book "kestrel/lists-light/firstn-def" :dir :system)
(include-book "kestrel/utilities/rational-printing" :dir :system)

(defun term-is-booleanp (term ens wrld)
  (declare (xargs :mode :program))
  (mv-let (type-set val)
    (acl2::type-set term nil nil
              nil ; type-alist
              ens wrld nil nil nil)
    (declare (ignore val))
    (acl2::ts-subsetp type-set acl2::*ts-boolean*)))
;; Example (term-is-booleanp '(not x) (ens state) (w state))

;; for now, we only choose one argument of the EQUALS.  splitting on both seems unnecessary?
(defun equated-boolean-terms-in-lit (lit ens wrld)
  (declare (xargs :mode :program))
  (let (;; strip a not:
        (lit (if (and (consp lit) (eq 'not (acl2::ffn-symb lit)))
                 (cadr lit)
               lit)))
    (if (not (and (consp lit) (eq 'equal (acl2::ffn-symb lit))))
        nil
      (let ((arg1 (acl2::fargn lit 1))
            (arg2 (acl2::fargn lit 2)))
        (if (and (term-is-booleanp arg1 ens wrld)
                 (not (quotep arg1)))
            (list arg1)
          (if (and (term-is-booleanp arg2 ens wrld)
                   (not (quotep arg2)))
              (list arg2)
            nil))))))

(defun equated-boolean-terms-in-clause (clause ens wrld)
  (declare (xargs :mode :program))
  (if (endp clause)
      nil
    (append (equated-boolean-terms-in-lit (first clause) ens wrld)
            (equated-boolean-terms-in-clause (rest clause) ens wrld))))

(defun equated-boolean-terms-in-clauses (clauses ens wrld)
  (declare (xargs :mode :program))
  (if (endp clauses)
      nil
    (union-equal (equated-boolean-terms-in-clause (first clauses) ens wrld)
                 (equated-boolean-terms-in-clauses (rest clauses) ens wrld))))

;; todo: look at checkpoints and goal
;; todo: perhaps do something different if there is an induction happening?
(defun make-cases-recs (translated-theorem-body
                        checkpoint-clauses-top
                        checkpoint-clauses-non-top
                        num-recs
                        print
                        state)
  (declare (xargs :guard (and (pseudo-termp translated-theorem-body)
                              (acl2::pseudo-term-list-listp checkpoint-clauses-top)
                              (acl2::pseudo-term-list-listp checkpoint-clauses-non-top)
                              (natp num-recs)
                              (acl2::print-levelp print))
                  :stobjs state
                  :mode :program ; because this ultimately calls type-set
                  ))
  (declare (ignore translated-theorem-body)) ; todo: would it be good to use this?
  (b* ((wrld (w state))
       (- (and (acl2::print-level-at-least-tp print)
               (cw "Making ~x0 :cases recommendations: " ; the line is ended below when we print the time
                   num-recs)))
       ;; For now, just suggest cases when we have a boolean term equated to something else:
       ;; TODO: Also look at the goal (handle implies, etc.):
       (equated-boolean-terms-in-top-checkpoints (equated-boolean-terms-in-clauses checkpoint-clauses-top (acl2::ens state) wrld))
       (equated-boolean-terms-in-non-top-checkpoints (equated-boolean-terms-in-clauses checkpoint-clauses-non-top (acl2::ens state) wrld))
       (top-recs
        (if equated-boolean-terms-in-top-checkpoints
            (list (make-rec (concatenate 'string "cases" "0" ;(acl2::nat-to-string 0)
                                         )
                            :add-cases-hint
                        ;; todo: can we do better (e.g., only splitting on one thing in each equality)?
                            (acl2::all-case-combinations equated-boolean-terms-in-top-checkpoints)
                            5 ; confidence percentage (quite high) TODO: allow unknown?  TODO: Allow this to depend on the number of cases?
                            nil
                            ))
          ;; Don't make any recommendations:
          nil))
       ;; TODO: These hints really should be put onto inductive subgoals:
       (non-top-recs
        (if equated-boolean-terms-in-non-top-checkpoints
            (list (make-rec (concatenate 'string "cases" "0" ;(acl2::nat-to-string 0)
                                         )
                            :add-cases-hint
                            ;; todo: can we do better (e.g., only splitting on one thing in each equality)?
                            (acl2::all-case-combinations equated-boolean-terms-in-non-top-checkpoints)
                            5 ; confidence percentage (quite high) TODO: allow unknown?  TODO: Allow this to depend on the number of cases?
                            nil
                            ))
          ;; Don't make any recommendations:
          nil))
       ;; todo: how to choose when we can't return them all?:
       (recs (acl2::firstn num-recs (append top-recs non-top-recs))))
    (mv nil recs state)))
