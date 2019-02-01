(in-package "PROOF-CHECKER-ARRAY")

(include-book "mv-nth")
(include-book "ternary")
(include-book "literal")
(include-book "unique")
(include-book "sets")
(include-book "assignment")
(include-book "clause")
(include-book "all-literals")
(include-book "evaluator")

(include-book "std/util/bstar" :dir :system)


;; ===================================================================
;; ========================= IS-UNIT-CLAUSE ==========================

(defun is-unit-clause (clause assignment)
  (declare (xargs :guard (and (clausep clause)
                              (assignmentp assignment))))
  (cond
   ((atom clause) nil)
   ((truep (evaluate-literal (car clause) assignment)) nil)
   ((undefp (evaluate-literal (car clause) assignment))
    (if (falsep (evaluate-clause (cdr clause) assignment))
        (car clause)
      nil))
   ((falsep (evaluate-literal (car clause) assignment))
    (is-unit-clause (cdr clause) assignment))
   (t nil)))


(defthm literalp-is-unit-clause
  (implies (and (clausep clause)
                (is-unit-clause clause assignment))
           (literalp (is-unit-clause clause assignment))))

(defthm member-is-unit-clause-clause
  (implies (is-unit-clause clause assignment)
           (member (is-unit-clause clause assignment)
                   clause)))

(defthm not-member-is-unit-clause-assignment
  (implies (is-unit-clause clause assignment)
           (not (member (is-unit-clause clause assignment)
                        assignment))))

(defthm not-member-negate-is-unit-clause-assignment
  (implies (is-unit-clause clause assignment)
           (not (member (negate (is-unit-clause clause assignment))
                        assignment))))

(defthm member-is-unit-clause-all-literals
  (implies (and (is-unit-clause clause assignment)
                (member clause formula))
           (member (is-unit-clause clause assignment)
                   (all-literals formula)))
  :hints (("Goal"
           :use ((:instance member-is-unit-clause-clause)
                 (:instance member-all-literals
                            (literal (is-unit-clause clause assignment)))))))


(defthm is-unit-clause-implies-undefp-evaluate-clause
  (implies (is-unit-clause clause assignment)
           (undefp (evaluate-clause clause assignment))))



;; ===================================================================
;; ======================== FIND-UNIT-CLAUSE =========================

(defun find-unit-clause (formula assignment)
  (declare (xargs :guard (and (formulap formula)
                              (assignmentp assignment))))
  (b*
   (((when (atom formula)) (mv nil nil))
    (clause (car formula))
    (rest-of-formula (cdr formula))
    (unit-literal (is-unit-clause clause assignment))
    ((when unit-literal) (mv unit-literal clause)))
   (find-unit-clause rest-of-formula assignment)))




(defthm literalp-mv-nth-0-find-unit-clause
  (implies (and (formulap formula)
                (mv-nth 0 (find-unit-clause formula assignment)))
           (literalp (mv-nth 0 (find-unit-clause formula assignment)))))

(defthm clausep-mv-nth-1-find-unit-clause
  (implies (and (formulap formula)
                (mv-nth 0 (find-unit-clause formula assignment)))
           (clausep (mv-nth 1 (find-unit-clause formula assignment)))))

(defthm not-member-mv-nth-0-find-unit-clause-assignment
  (implies (mv-nth 0 (find-unit-clause formula assignment))
           (not (member (mv-nth 0 (find-unit-clause formula assignment))
                        assignment))))

(defthm not-member-negate-mv-nth-0-find-unit-clause-assignment
  (implies (mv-nth 0 (find-unit-clause formula assignment))
           (not (member (negate (mv-nth 0 (find-unit-clause formula
                                                            assignment)))
                        assignment))))

(defthm member-mv-nth-0-find-unit-clause-mv-nth-1-find-unit-clause
  (implies (mv-nth 0 (find-unit-clause formula assignment))
           (member (mv-nth 0 (find-unit-clause formula assignment))
                   (mv-nth 1 (find-unit-clause formula assignment)))))

(defthm member-mv-nth-1-find-unit-clause-formula
  (implies (mv-nth 0 (find-unit-clause formula assignment))
           (member (mv-nth 1 (find-unit-clause formula assignment))
                   formula)))

(defthm member-mv-nth-0-find-unit-clause-all-literals
  (implies (mv-nth 0 (find-unit-clause formula assignment))
           (member (mv-nth 0 (find-unit-clause formula assignment))
                   (all-literals formula)))
  :hints (("Goal"
           :use ((:instance member-mv-nth-0-find-unit-clause-mv-nth-1-find-unit-clause)
                 (:instance member-mv-nth-1-find-unit-clause-formula)
                 (:instance member-all-literals
                            (literal (mv-nth 0 (find-unit-clause formula assignment)))
                            (clause (mv-nth 1 (find-unit-clause formula assignment))))))))


