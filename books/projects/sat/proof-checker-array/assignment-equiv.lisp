(in-package "PROOF-CHECKER-ARRAY")

(include-book "assignment-st")

;; (defun project1 (i st)
;;   (declare (xargs :guard (and (assignment-stp st)
;;                               (or (field-offsetp i *stack* *s* st)
;;                                   (equal i -1)))
;;                   :stobjs (st)
;;                   :measure (nfix (1+ i))))
;;   (if (not (mbt (and (assignment-stp st)
;;                      (or (field-offsetp i *stack* *s* st)
;;                          (equal i -1)))))
;;       nil
;;     (if (equal i -1)
;;         nil
;;       (cons (fread *stack* i *s* st)
;;             (project1 (1- i) st)))))


(defun project1 (i f start st)
  (declare (xargs :guard (and (farrayp start st)
                              (fieldp f start st)
                              (or (field-offsetp i f start st)
                                  (equal i -1)))
                  :stobjs (st)
                  :measure (nfix (1+ i))))
  (if (not (mbt (and (farrayp start st)
                     (fieldp f start st)
                     (or (field-offsetp i f start st)
                         (equal i -1)))))
      nil
    (if (equal i -1)
        nil
      (cons (fread f i start st)
            (project1 (1- i) f start st)))))




(defun project (st)
  (declare (xargs :guard (assignment-stp st)
                  :stobjs (st)))
  (project1 (1- (fread *stack-end* 0 *s* st)) *stack* *s* st))



;; (defthm stack-memberp-implies-member-project1
;;   (implies (and (assignment-stp st)
;;                 (literalp lit)
;;                 ;; (lit-in-rangep lit st)
;;                 (field-offsetp i *stack* *s* st)
;;                 (stack-memberp lit i st))
;;                 ;; (assignedp lit st))
;;            (member lit (project1 i st)))
;;   :hints (("Goal"
;;            :induct (project1 i st) )))
;;           ;;  :in-theory (disable assignedp stack-memberp)) ))
;;           ;; ("Subgoal *1/2.1'"
;;           ;;  :in-theory (disable assignedp stack-memberp assignedp-implies-stack-memberp)
;;           ;;  :use ((:instance assignedp-implies-stack-memberp)))))


;; (defthm assignedp-implies-member-project
;;   (implies (and (assignment-stp st)
;;                 (literalp lit)
;;                 (lit-in-rangep lit st)
;;                 ;; (field-offsetp i *stack* *s* st)
;;                 ;; (stack-memberp lit i st))
;;                 (assignedp lit st))
;;            (member lit (project st)))
;;   :hints (("Goal"
;;            :do-not-induct t
;;            :in-theory (disable assignedp stack-memberp
;;                                assignedp-implies-stack-memberp
;;                                stack-memberp-implies-member-project1)
;;            :use ((:instance assignedp-implies-stack-memberp)
;;                  (:instance stack-memberp-implies-member-project1
;;                             (i (1- (fread 2 0 0 st))))))
;;           ("Goal'''"
;;            :in-theory (enable field-offsetp))))

;; (defthm stack-memberp-implies-equal-fread-lookup-1
;;   (implies (and (lookup-correspondsp i 1--se st)
;;                 (literalp lit)
;;                 (<= i lit)
;;                 (< lit (flength *lookup* *s* st))
;;                 (stack-memberp lit 1--se st))
;;            (equal (fread *lookup* lit *s* st) 1))
;;   :hints (("Goal"
;;            :induct (lookup-correspondsp i 1--se st))))

;; (defthm stack-memberp-implies-assignedp
;;   (implies (and (assignment-stp st)
;;                 (literalp lit)
;;                 (lit-in-rangep lit st)
;;                 (stack-memberp lit (1- (fread *stack-end* 0 *s* st)) st))
;;            (assignedp lit st))
;;   :hints (("Goal"
;;            :in-theory (disable lookup-correspondsp)
;;            :use ((:instance equal-fread-lookup-1-implies-stack-memberp
;;                             (i 0)
;;                             (1--se (1- (fread *stack-end* 0 *s* st))))))))


;; (defthm member-project-implies-assignedp
;;   (implies (and (assignment-stp st)
;;                 (literalp lit)
;;                 (lit-in-rangep lit st)
;;                 ;; (field-offsetp i *stack* *s* st)
;;                 ;; (stack-memberp lit i st))
;;                 (member lit (project st)))
;;            (assignedp lit st))
;;   :hints (("Goal"
;;            :do-not-induct t
;;            :in-theory (disable assignedp stack-memberp
;;                                assignedp-implies-stack-memberp
;;                                stack-memberp-implies-member-project1
;;                                assignedp-implies-stack-memberp)
;;            :use ((:instance assignedp-implies-stack-memberp)
;;                  (:instance stack-memberp-implies-member-project1
;;                             (i (1- (fread 2 0 0 st)))))) ))





;; ===================================================================

;; (in-theory (disable assignment-stp-assign-lit))

;; *num-vars*  1
;; *stack-end* 2
;; *stack*     3
;; *lookup*    4

;; (skip-proofs
;;  (defthm assignment-stp-assign-lit-2
;;    (implies (and (assignment-stp st)
;;                  (literalp lit)
;;                  (lit-in-rangep lit st)
;;                  ;; (not (stack-fullp st))
;;                  ;; (not (stack-memberp lit (fread *stack-end* 0 *s* st) st))
;;                  ;; (not (stack-memberp (negate lit) (fread *stack-end* 0 *s* st) st))
;;                  )
;;             (assignment-stp (assign-lit lit st)))))


;; (skip-proofs
;;  (defthm assignment-stp-unassign-one
;;    (implies (and (assignment-stp st))
;;                  ;(not (stack-emptyp ...)))
;;             (assignment-stp (unassign-one st)))))

;; (skip-proofs
;;  (defthm assignment-stp-unassign-all
;;    (implies (and (assignment-stp st))
;;             (assignment-stp (unassign-all (fread *stack-end* 0 *s* st) st)))))

;; ===================================================================

(include-book "supplemental/assignment")

;; (in-theory (disable lookup-corresponds-with-stackp))



;; ===================================================================

(defthm field-memberp-implies-member-project1
  (implies (and ;; (farrayp start st)
                ;; (fieldp f start st)
                ;; (field-offsetp i f start st)
                (field-memberp e i 0 f start st))
           (member e (project1 i f start st))))


(defthm member-project1-implies-field-memberp
  (implies (and ;; (farrayp start st)
                ;; (fieldp f start st)
                ;; (field-offsetp i f start st)
                (sb60p e)
                (member e (project1 i f start st)))
           (field-memberp e i 0 f start st)))

(defthm iff-field-memberp-member-project1
  (implies (and ;; (farrayp start st)
                ;; (fieldp f start st)
                ;; (field-offsetp i f start st)
                (sb60p e))
           (iff (field-memberp e i 0 f start st)
                (member e (project1 i f start st)))))


(defthm iff-field-memberp-member-project
  (implies (and ;; (farrayp start st)
                ;; (fieldp f start st)
                ;; (field-offsetp i f start st)
                (sb60p e))
           (iff (field-memberp e
                               (1- (fread *stack-end* 0 *s* st))
                               0 *stack* *s* st)
                (member e (project st)))))


;; ===================================================================

(defthm literalp-fread-*stack*
  (implies (and (stack-contains-literalsp j st)
                (field-offsetp i *stack* *s* st)
                (<= i j))
           (literalp (fread *stack* i *s* st))))

(defthm literal-listp-project1
  (implies (and (assignment-stp st)
                (field-offsetp i *stack* *s* st)
                (< i (fread *stack-end* 0 *s* st)))
           (literal-listp (project1 i *stack* *s* st))))

(defthm literal-listp-project
  (implies (assignment-stp st)
           (literal-listp (project st)))
  :hints (("Goal" :use ((:instance literal-listp-project1
                                   (i (1- (fread *stack-end* 0 *s* st))))))))

;; ===================================================================

(defthm stack-uniquep-implies-not-field-memberp
  (implies (and (stack-uniquep j st)
                (field-offsetp i *stack* *s* st)
                (<= i j))
           (not (field-memberp (fread *stack* i *s* st)
                               (1- i) 0 *stack* *s* st)))
  :hints (("Goal" :in-theory (enable stack-uniquep))))

(defthm stack-uniquep-implies-not-member-project1
  (implies (and (stack-uniquep j st)
                (field-offsetp i *stack* *s* st)
                (<= i j))
           (not (member (fread *stack* i *s* st)
                        (project1 (1- i) *stack* *s* st))))
  :hints (("Goal" :in-theory (enable stack-uniquep))))


(defthm unique-literalsp-project1
  (implies (stack-uniquep j st)
           (unique-literalsp (project1 j *stack* *s* st)))
  :hints (("Goal" :in-theory (enable stack-uniquep))))

(defthm unique-literalsp-project
  (implies (assignment-stp st)
           (unique-literalsp (project st))))

;; ===================================================================

;; (defthm sb60p-negate
;;   (implies (literalp lit)
;;            (sb60p (negate lit)))
;;   :hints (("Goal" :use ((:instance literalp-negate (x lit))
;;                         (:instance literalp-implies-sb60p)))))


(in-theory (enable stack-not-conflictingp))

(defthm stack-not-conflictingp-implies-not-field-memberp-negate
  (implies (and (stack-not-conflictingp j st)
                (field-offsetp i *stack* *s* st)
                (<= i j))
           (not (field-memberp (negate (fread *stack* i *s* st))
                               (1- i) 0 *stack* *s* st)))
  :hints (("Goal" :in-theory (disable iff-field-memberp-member-project1))))



(defthm stack-not-conflictingp-implies-not-member-negate-project1
  (implies (and (stack-not-conflictingp j st)
                (field-offsetp i *stack* *s* st)
                (<= i j))
           (not (member (negate (fread *stack* i *s* st))
                        (project1 (1- i) *stack* *s* st)))))

(defthm no-conflicting-literalsp-project1
  (implies (stack-not-conflictingp j st)
           (no-conflicting-literalsp (project1 j *stack* *s* st))))

(defthm no-conflicting-literalsp-project
  (implies (assignment-stp st)
           (no-conflicting-literalsp (project st))))

(in-theory (disable stack-not-conflictingp))

;; ===================================================================

(defthm assignmentp-project1
  (implies (and (assignment-stp st)
                ;; (field-offsetp i *stack* *s* st)
                (< i (fread *stack-end* 0 *s* st)))
           (assignmentp (project1 i *stack* *s* st))))

(defthm assignmentp-project
  (implies (assignment-stp st)
           (assignmentp (project st))))
 
;; ===================================================================



(defthm assignedp-implies-member-project
  (implies (and (assignment-stp st)
                (literalp lit)
                (lit-in-rangep lit st)
                (assignedp lit st))
           (member-equal lit (project st)))
  :hints (("Goal" :use ((:instance assignedp-implies-field-memberp-*stack*)
                        (:instance iff-field-memberp-member-project
                                   (e lit))))))


(defthm field-memberp-*stack*-implies-equal-fread-lookup-1
  (implies (and (stack-corresponds-with-lookup-p j st)
                (field-memberp lit
                               j
                               0 *stack* *s* st)
                ;; (field-offsetp lit *lookup* *s* st)
                ;; (<= i lit)
                )
           (equal (fread *lookup* lit *s* st) 1))
  :hints (("Goal" :in-theory (disable iff-field-memberp-member-project1))))

(defthm member-project-implies-assignedp
  (implies (and (assignment-stp st)
                (literalp lit)
                (lit-in-rangep lit st)
                (member-equal lit (project st)))
           (assignedp lit st)))


(defthm iff-assignedp-member-project
  (implies (and (assignment-stp st)
                (literalp lit)
                (lit-in-rangep lit st))
           (iff (assignedp lit st)
                (member-equal lit (project st))))
  :hints (("Goal" :in-theory (disable assignedp project assignment-stp))))

;; ===================================================================


(defthm assign-lit-cons-project1
  (implies (and (assignment-stp st)
                (literalp lit)
                (lit-in-rangep lit st)
                (< i (fread *stack-end* 0 *s* st)))
           (equal (project1 i *stack* *s* (assign-lit lit st))
                  (project1 i *stack* *s* st))))

(defthm assign-lit-cons-project
  (implies (and (assignment-stp st)
                (literalp lit)
                (lit-in-rangep lit st))
           (equal (project (assign-lit lit st))
                  (cons lit (project st))))
  :hints (("Goal'''"
           :use ((:instance assign-lit-cons-project1
                            (i (1- (fread *stack-end* 0 *s* st))))))))
  ;; :hints (("Goal" :in-theory (disable assign-lit))))


;; ===================================================================



(defthm unassign-one-cdr-project1
  (implies (and (assignment-stp st)
                (not (equal (fread *stack-end* 0 *s* st) 0))
                (< i (1- (fread *stack-end* 0 *s* st)))
                ;; (field-offsetp i *stack* *s* st)
                ;; (sb60p (1- (fread *stack-end* 0 *s* st)))
                )
           (equal (project1 i *stack* *s* (unassign-one st))
                  (project1 i *stack* *s* st)))
  :hints (("Goal" :in-theory (enable unassign-one))))

;; (defthm unassign-one-cdr-project1
;;   (implies (and (assignment-stp st)
;;                 (not (equal (fread *stack-end* 0 *s* st) 0))
;;                 (<= i (1- (fread *stack-end* 0 *s* st)))
;;                 (field-offsetp i *stack* *s* st)
;;                 )
;;            (equal (project1 (1- i) *stack* *s* (unassign-one st))
;;                   (cdr (project1 i *stack* *s* st)))))

(defthm unassign-one-cdr-project
  (implies (and (assignment-stp st)
                (not (equal (fread *stack-end* 0 *s* st) 0))
                ;; (sb60p (1- (fread *stack-end* 0 *s* st)))
                )
           (equal (project (unassign-one st))
                  (cdr (project st))))
  :hints (("Goal"
           :use ((:instance unassign-one-cdr-project1
                            (i (+ -1 -1 (fread *stack-end* 0 *s* st)))) ))))


;; ===================================================================

(defthm fread-*stack-end*-unassign-all
  (implies (and (assignment-stp st)
                (field-offsetp i *stack* *s* st)
                (equal i (fread *stack-end* 0 *s* st)))
           (equal (fread *stack-end* 0 *s* (unassign-all i st))
                  0))
  :hints (("Goal"
           :in-theory (disable unassign-one)
           :induct (unassign-all i st))))

(defthm fread-*stack-end*-unassign-all-*stack-end*
  (implies (and (assignment-stp st)
                (field-offsetp i *stack* *s* st)
                (<= i (fread *stack-end* 0 *s* st)))
           (equal (fread *stack-end* 0 *s* (unassign-all (fread *stack-end* 0
                                                                *s* st) st))
                  0))
  :hints (("Goal" :in-theory (disable unassign-one))))

(defthm project-unassign-all
  (implies (and (assignment-stp st))
           (equal (project (unassign-all (fread *stack-end* 0 *s* st) st))
                  nil))
  :hints (("Goal" :in-theory (disable unassign-one))))



;; ===================================================================

;; (skip-proofs
;;  (defthm assignedp-member-project
;;    (implies (and (assignment-stp st)
;;                  (literalp lit)
;;                  (lit-in-rangep lit st))
;;             (iff (assignedp lit st)
;;                  (member-equal lit (project st))))))

;; (skip-proofs
;;  (defthm assign-lit-cons-project
;;    (implies (and (assignment-stp st)
;;                  (literalp lit)
;;                  (lit-in-rangep lit st))
;;             (equal (project (assign-lit lit st))
;;                    (cons lit (project st))))))

;; (skip-proofs
;;  (defthm unassign-one-cdr-project
;;    (implies (and (assignment-stp st)
;;                  )
;;             (equal (project (unassign-one st))
;;                    (cdr (project st))))))


;; (skip-proofs
;;  (defthm unassign-all-equal-project-nil
;;    (implies (and (assignment-stp st)
;;                  )
;;             (equal (project (unassign-all (fread *stack-end* 0 *s* st) st))
;;                    nil))))

;; ===================================================================

;; (include-book "supplemental/ternary")

;; ===================================================================


(encapsulate
 ()
 (local (include-book "arithmetic-5/top" :dir :system))

 (defthm assignment-stp-evenp-len
   (implies (assignment-stp st)
            (evenp (flength *lookup* *s* st)))))

(defthm lit-in-range-negate
  (implies (and (assignment-stp st)
                (literalp lit)
                (lit-in-rangep lit st))
           (lit-in-rangep (negate lit) st))
  :otf-flg t
  :hints (("Goal"
           :in-theory (enable field-offsetp))))


;; (defthm lit-in-range-negate-2
;;   (implies (and (assignment-stp st)
;;                 (literalp lit)
;;                 (lit-in-rangep (negate lit) st))
;;            (lit-in-rangep lit st))
;;   :otf-flg t
;;   :hints (("Goal"
;;            :in-theory (enable field-offsetp))))


;; ===================================================================



;; (skip-proofs
;;  (defthm lit-in-rangep-negate
;;    (implies (and (assignment-stp st)
;;                  (literalp lit)
;;                  (lit-in-rangep lit st))
;;             (lit-in-rangep (negate lit) st))))

;; ===================================================================


(in-theory (disable assignment-stp
                    assign-lit
                    assignedp
                    unassign-one
                    lit-in-rangep
                    unassign-all
                    project))


(include-book "rat-checker-new")

(defun evaluate-literal-st (lit st)
  (declare (xargs :guard (and (assignment-stp st)
                              (literalp lit)
                              (lit-in-rangep lit st))
                  :stobjs (st)))
  (cond
   ((assignedp lit st) (true))
   ((assignedp (negate lit) st) (false))
   (t (undef))))

(defthm evaluate-literal-equiv
  (implies (and (assignment-stp st)
                (literalp lit)
                (lit-in-rangep lit st))
           (equal (evaluate-literal-st lit st)
                  (evaluate-literal lit (project st)))))

;; ===================================================================

(defun clause-in-rangep (clause st)
  (declare (xargs :guard (and (assignment-stp st)
                              (clausep clause))
                  :stobjs (st)))
  (if (atom clause)
      t
    (and (lit-in-rangep (car clause) st)
         (clause-in-rangep (cdr clause) st))))


(defun formula-in-rangep (formula st)
  (declare (xargs :guard (and (assignment-stp st)
                              (formulap formula))
                  :stobjs (st)))
  (if (atom formula)
      t
    (and (clause-in-rangep (car formula) st)
         (formula-in-rangep (cdr formula) st))))

(defun evaluate-clause-st (clause st)
  (declare (xargs :guard (and (assignment-stp st)
                              (clausep clause)
                              (clause-in-rangep clause st))
                  :stobjs (st)))
  (if (atom clause)
      (false)
    (let* ((literal (car clause))
           (literal-value (evaluate-literal-st literal st)))
      (if (truep literal-value)
          (true)
        (let* ((remaining-clause (cdr clause))
               (remaining-clause-value (evaluate-clause-st remaining-clause
                                                           st)))
          (cond
           ((truep remaining-clause-value) (true))
           ((undefp literal-value) (undef))
           (t remaining-clause-value)))))))

(defthm evaluate-clause-equiv
  (implies (and (assignment-stp st)
                (clausep clause)
                (clause-in-rangep clause st))
           (equal (evaluate-clause-st clause st)
                  (evaluate-clause clause (project st)))))


(defun evaluate-formula-st (formula st)
  (declare (xargs :guard (and (assignment-stp st)
                              (formulap formula)
                              (formula-in-rangep formula st))
                  :stobjs (st)))
  (if (atom formula)
      (true)
    (let* ((clause (car formula))
           (clause-value (evaluate-clause-st clause st)))
      (if (falsep clause-value)
          (false)
        (let* ((remaining-formula (cdr formula))
               (remaining-formula-value (evaluate-formula-st remaining-formula
                                                             st)))
          (cond
           ((falsep remaining-formula-value) (false))
           ((undefp clause-value) (undef))
           (t remaining-formula-value)))))))

(defthm evaluate-formula-equiv
  (implies (and (assignment-stp st)
                (formulap formula)
                (formula-in-rangep formula st))
           (equal (evaluate-formula-st formula st)
                  (evaluate-formula formula (project st)))))
;; ===================================================================

(defun is-unit-clause-st (clause st)
  (declare (xargs :guard (and (assignment-stp st)
                              (clausep clause)
                              (clause-in-rangep clause st))
                  :stobjs (st)))
  (cond
   ((atom clause) nil)
   ((truep (evaluate-literal-st (car clause) st)) nil)
   ((undefp (evaluate-literal-st (car clause) st))
    (if (falsep (evaluate-clause-st (cdr clause) st))
        (car clause)
      nil))
   ((falsep (evaluate-literal-st (car clause) st))
    (is-unit-clause-st (cdr clause) st))
   (t nil)))


(defthm is-unit-clause-equiv
  (implies (and (assignment-stp st)
                (clausep clause)
                (clause-in-rangep clause st))
           (equal (is-unit-clause-st clause st)
                  (is-unit-clause clause (project st)))))



(defun find-unit-clause-st (formula st)
  (declare (xargs :guard (and (assignment-stp st)
                              (formulap formula)
                              (formula-in-rangep formula st))
                  :stobjs (st)))
  (b*
   (((when (atom formula)) (mv nil nil))
    (clause (car formula))
    (rest-of-formula (cdr formula))
    (unit-literal (is-unit-clause-st clause st))
    ((when unit-literal) (mv unit-literal clause)))
   (find-unit-clause-st rest-of-formula st)))


(defthm find-unit-clause-equiv
  (implies (and (assignment-stp st)
                (formulap formula)
                (formula-in-rangep formula st))
           (equal (find-unit-clause-st formula st)
                  (find-unit-clause formula (project st)))))


;; ===================================================================



(defun num-undef-st (formula st)
  (declare (xargs :guard (and (assignment-stp st)
                              (formulap formula)
                              (formula-in-rangep formula st))
                  :stobjs (st)))
  (if (atom formula)
      0
    (if (undefp (evaluate-clause-st (car formula) st))
        (1+ (num-undef-st (cdr formula) st))
      (num-undef-st (cdr formula) st))))

(defthm num-undef-equiv
  (implies (and (assignment-stp st)
                (formulap formula)
                (formula-in-rangep formula st))
           (equal (num-undef-st formula st)
                  (num-undef formula (project st)))))

;; ===================================================================

(defthm clause-in-rangep-member
  (implies (and (clause-in-rangep clause st)
                (member lit clause)
                (assignment-stp st))
           (lit-in-rangep lit st)))

(defthm formula-in-rangep-member
  (implies (and (formula-in-rangep formula st)
                (member clause formula)
                (assignment-stp st))
           (clause-in-rangep clause st)))

(defthm lit-in-rangep-mv-nth-0-find-unit-clause-project
  (implies (and (assignment-stp st)
                (formulap formula)
                (formula-in-rangep formula st)
                (mv-nth 0 (find-unit-clause formula (project st))))
           (lit-in-rangep (mv-nth 0 (find-unit-clause formula (project st)))
                          st)))

(defthm literalp-mv-nth-0-find-unit-clause-project
  (implies (and (assignment-stp st)
                (formulap formula)
                (formula-in-rangep formula st)
                (mv-nth 0 (find-unit-clause formula (project st))))
           (literalp (mv-nth 0 (find-unit-clause formula (project st))))))

(defthm lit-in-rangep-assign-lit
  (implies (and (assignment-stp st)
                (literalp lit)
                (lit-in-rangep lit st)
                (literalp lit2)
                (lit-in-rangep lit2 st))
           (lit-in-rangep lit (assign-lit lit2 st)))
  :hints (("Goal"
           :in-theory (enable lit-in-rangep assign-lit assignment-stp))))

(defthm clause-in-rangep-assign-lit
  (implies (and (assignment-stp st)
                (clausep clause)
                (clause-in-rangep clause st)
                (literalp lit)
                (lit-in-rangep lit st))
           (clause-in-rangep clause (assign-lit lit st))))

(defthm formula-in-rangep-assign-lit
  (implies (and (assignment-stp st)
                (formulap formula)
                (formula-in-rangep formula st)
                (literalp lit)
                (lit-in-rangep lit st))
           (formula-in-rangep formula (assign-lit lit st))))

(defthm num-undef-measure
  (implies (and (assignment-stp st)
                (formulap formula)
                (formula-in-rangep formula st)
                (mv-nth 0 (find-unit-clause formula (project st))))
           (< (num-undef formula
                         (project (assign-lit (mv-nth 0 (find-unit-clause
                                                         formula
                                                         (project st)))
                                              st)))
              (num-undef formula (project st)))) )

;; ===================================================================


(defthm sb60p-is-unit-clause
  (implies (and (clausep clause)
                (assignmentp assignment)
                (is-unit-clause clause assignment))
           (sb60p (is-unit-clause clause assignment))))

(defthm sb60p-mv-nth-0-find-unit-clause
  (implies (and (formulap formula)
                (assignmentp assignment)
                (mv-nth 0
                          (find-unit-clause formula assignment)))
           (sb60p (mv-nth 0
                          (find-unit-clause formula assignment)))))

(defthm assignment-stp-assign-lit-mv-nth-0-find-unit-clause
  (implies
   (and (formula-in-rangep formula st)
        (formulap formula)
        (assignment-stp st)
        ;; (stp st)
        (mv-nth 0
                (find-unit-clause formula (project st))))
   (assignment-stp (assign-lit (mv-nth 0
                                       (find-unit-clause formula (project st)))
                               st)))
  :otf-flg t
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (lit-in-rangep)
                           (assignment-stp-assign-lit
                            lit-in-rangep-mv-nth-0-find-unit-clause-project
                            IFF-FIELD-MEMBERP-MEMBER-PROJECT1))
           :use ((:instance assignment-stp-assign-lit
                            (lit (mv-nth 0 (find-unit-clause formula
                                                             (project st)))))
                 (:instance lit-in-rangep-mv-nth-0-find-unit-clause-project)))
          ("Goal'4'"
           :use ((:instance iff-field-memberp-member-project
                            (e (mv-nth 0 (find-unit-clause
                                          formula
                                          (project st)))))))))

(defun unit-propagation-st (formula st)
  (declare (xargs :guard (and (assignment-stp st)
                              (formulap formula)
                              (formula-in-rangep formula st))
                  :verify-guards nil
                  :stobjs (st)
                  :measure (num-undef formula (project st))))
  (if (not (mbt (and (assignment-stp st)
                     (formulap formula)
                     (formula-in-rangep formula st))))
      st
    (mv-let (unit-literal unit-clause)
            (find-unit-clause-st formula st)
            (declare (ignorable unit-clause))
            (if (not unit-literal)
                st
              (let ((st (assign-lit unit-literal st)))
                (unit-propagation-st formula st))))))

;; (skip-proofs (verify-guards unit-propagation-st))

(defthm assignment-stp-unit-propagation-st
  (implies (and (assignment-stp st)
                (formulap formula)
                (formula-in-rangep formula st))
           (assignment-stp (unit-propagation-st formula st))))

(verify-guards unit-propagation-st)

(defthm unit-propagation-equiv
  (implies (and (assignment-stp st)
                (formulap formula)
                (formula-in-rangep formula st))
           (equal (project (unit-propagation-st formula st))
                  (unit-propagation formula (project st)))))




;; ===================================================================

;; (i-am-here)

;; (negate-clause '(1 2 3)) = '(-1 -2 -3)

;; (clause-to-assignment '(1 2 3) st)
;; st = (clause-to-assignment '(2 3) st), (assign-lit -1 st) (push -1)
;; st = (clause-to-assignment '(3) st), (assign-lit -2 st) (push -2)

;; bottom -3 -2 -1 top

;; (equal (project (clause-to-assignment clause st))
;;        (reverse (negate-clause clause)))


(defun clause-agrees-with-stackp (clause st)
  (declare (xargs :guard (and (assignment-stp st)
                              (clausep clause)
                              (clause-in-rangep clause st))
                  :guard-hints (("Goal"
                                 :in-theory (enable assignment-stp)))
                  :stobjs (st)))
  (if (atom clause)
      t
    (and (not (field-memberp (car clause)
                             (1- (fread *stack-end* 0 *s* st))
                             0
                             *stack*
                             *s*
                             st))
         (not (field-memberp (negate (car clause))
                             (1- (fread *stack-end* 0 *s* st))
                             0
                             *stack*
                             *s*
                             st))
         (clause-agrees-with-stackp (cdr clause) st))))



(defthm fread-*stack*-at-*stack-end*-assign-lit
  (implies (and (farrayp *s* st)
                (fieldp *stack-end* *s* st)
                (fieldp *stack* *s* st)
                (fieldp *lookup* *s* st)
                (field-offsetp (fread *stack-end* 0 *s* st) *stack* *s* st)
                (field-offsetp lit *lookup* *s* st))
           (equal (fread *stack*
                         (fread *stack-end* 0 *s* st)
                         *s* (assign-lit lit st))
                  lit))
  :hints (("Goal" :in-theory (enable assign-lit))))


(defthm field-memberp-1--*stack-end*-assign-lit
  (implies (and (farrayp *s* st)
                (fieldp *stack-end* *s* st)
                (fieldp *stack* *s* st)
                (fieldp *lookup* *s* st)
                (field-offsetp (fread *stack-end* 0 *s* st) *stack* *s* st)
                (field-offsetp lit *lookup* *s* st))
           (equal (field-memberp lit2
                                 (1- (fread *stack-end* 0 *s* st))
                                 0 *stack* *s* (assign-lit lit st))
                  (field-memberp lit2
                                 (1- (fread *stack-end* 0 *s* st))
                                 0 *stack* *s* st)))
  :hints (("Goal" :in-theory (enable assign-lit))))




(defthm not-field-memberp-fread-assign-lit-assign-lit
  (implies (and (not (field-memberp lit2
                                    ;;(1- i)
                                    (+ -1 (fread 2 0 0 st))
                                    0 3 0 st))
                (not (equal lit lit2))
                ;; (not (equal (negate lit) lit2))
                ;; (<= 0 i)
                ;; (field-offsetp i *stack* *s* st)
                (farrayp *s* st)
                (fieldp *stack-end* *s* st)
                (field-offsetp (fread *stack-end* 0 *s* st) *stack* *s* st)
                (field-offsetp lit *lookup* *s* st)
                (fieldp *lookup* *s* st)
                (fieldp *stack* *s* st)
                (literalp lit)
                ;; (literalp lit2)
                ;; (stack-contains-literalsp (1- (fread *stack-end* 0 *s* st)) st)
                )
           (not (field-memberp lit2
                               ;;i
                               (+ -1 (fread 2 0 0 (assign-lit lit st)))
                               0 3 0 (assign-lit lit st))))
  :hints (("Goal" :in-theory (disable IFF-FIELD-MEMBERP-MEMBER-PROJECT1
                                      FIELD-MEMBERP-IMPLIES-MEMBER-PROJECT1
                                      IFF-FIELD-MEMBERP-MEMBER-PROJECT)) ))
          ;; ("Subgoal 2'"
          ;;  :use ((:instance field-offsetp-assign-lit
          ;;                   (offset i))))))





(defthm clause-agrees-with-stackp-assign-lit
  (implies (and (clause-agrees-with-stackp clause st)
                (not (member lit clause))
                (not (member (negate lit) clause))
                (literalp lit)
                ;; (clause-in-rangep clause st)
                (lit-in-rangep lit st)
                (assignment-stp st)
                ;; (not (field-memberp lit
                ;;                     (1- (fread *stack-end* 0 *s* st))
                ;;                     0 *stack* *s* st))
                ;; (not (field-memberp (negate lit)
                ;;                     (1- (fread *stack-end* 0 *s* st))
                ;;                     0 *stack* *s* st))
                )
           (clause-agrees-with-stackp clause (assign-lit lit st)))
  :hints (("Goal"
           :in-theory (e/d (assignment-stp lit-in-rangep)
                           (IFF-FIELD-MEMBERP-MEMBER-PROJECT
                            IFF-FIELD-MEMBERP-MEMBER-PROJECT1
                            FIELD-MEMBERP-IMPLIES-MEMBER-PROJECT1)))
          ("Subgoal *1/3.2'"
           :use ((:instance fread-*stack*-at-*stack-end*-assign-lit)))))



;; ===================================================================

(defun clause-to-assignment (clause st)
  (declare (xargs :guard (and (assignment-stp st)
                              (clausep clause)
                              (clause-in-rangep clause st)
                              (clause-agrees-with-stackp clause st))
                              ;; (or (equal clause nil)
                              ;;     (NOT (FIELD-MEMBERP (car clause)
                              ;;                     (1- (FREAD *STACK-END* 0 *S* ST))
                              ;;                     0 *STACK* *S* ST)))
                              ;; (or (equal clause nil)
                              ;;     (NOT (FIELD-MEMBERP (negate (car clause))
                              ;;                         (1- (FREAD *STACK-END* 0 *S* ST))
                              ;;                         0 *STACK* *S* ST))))
                  :verify-guards nil
                  :stobjs (st)))
  (if (atom clause)
      st
    (let* (
           (st (assign-lit (negate (car clause)) st))
           (st (clause-to-assignment (cdr clause) st))
           )
      st)))


(defthm field-offsetp-negate-lit-*lookup*
  (implies (and (assignment-stp st)
                (literalp lit)
                (field-offsetp lit *lookup* *s* st))
           (field-offsetp (negate lit) *lookup* *s* st))
  :hints (("Goal" :in-theory (enable assignment-stp) )))

;; (defun clause-to-assignment-helper (clause st)
;;   (declare (xargs :guard (and (assignment-stp st)
;;                               (clausep clause)
;;                               (clause-in-rangep clause st)
;;                               )
;;                   :stobjs (st)))
;;   (let* ((st (unassign-all st))
;;          (st (clause-to-assignment clause st)))
;;     st))

(verify-guards
 clause-to-assignment
 ;:otf-flg t
 :hints (("Goal"
          :in-theory (enable lit-in-rangep)
          ;:do-not-induct t
          ) ))
         ;; ("Subgoal 3.3"
         ;;  :use ((:instance assignment-stp-assign-lit
         ;;                   (lit (negate (car clause))))))
         ;; ("Subgoal 3.3'''"
         ;;  :use ((:instance field-offsetp-negate-lit-*lookup* ;fjfjfjf
         ;;                   (lit (car clause)))))))
         ;; ("Subgoal 13'"
         ;;  :in-theory (enable assignment-stp))
         ;; ("Subgoal 12'"
         ;;  :in-theory (enable assignment-stp))
         ;; ("Subgoal 11'"
         ;;  :in-theory (enable assignment-stp))
         ;; ("Subgoal 10'"
         ;;  :in-theory (enable assignment-stp))
         ;; ("Subgoal 9'"
         ;;  :in-theory (enable assignment-stp))
         ;; ("Subgoal 8'"
         ;;  :in-theory (enable assignment-stp))
         ;; ("Subgoal 7'"
         ;;  :in-theory (enable assignment-stp))
         ;; ("Subgoal 6'"
         ;;  :in-theory (enable assignment-stp))
         ;; ("Subgoal 5'"
         ;;  :in-theory (enable assignment-stp)) ))
         ;; ("Subgoal 1.4"
         ;;  :use ((:inst
         ;; ("Subgoal 3.4.19"
         ;;  :in-theory (enable farrayp))))

;; (defthm farrayp-clause-to-assignment
;;   (implies (and (assignment-stp st)
;;                 (clausep clause)
;;                 (clause-in-rangep clause st))
;;            (farrayp *s* (clause-to-assignment clause st)))
;;   :hints (("Goal" :in-theory (enable assignment-stp))))



;; (defthm field-offsetp-clause-to-assignment
;;   (implies (and (assignment-stp st)
;;                 (assignment-stp (clause-to-assignment (cdr clause) st))
;;                 (consp clause)
;;                 (clausep clause)
;;                 (clause-in-rangep clause st)
;;                 (clause-agrees-with-stackp clause st)
;;                 (field-offsetp i *lookup* *s* st))
;;            (field-offsetp i *lookup* *s* (clause-to-assignment clause st))) )
;;   :hints (("Goal" :in-theory (enable assignment-stp)) ))


;; (defthm assignment-stp-implies-field-offsetp-assign-lit
;;   (implies (and (assignment-stp st)
;;                 (field-offsetp lit *lookup* *s* st)
;;                 (literalp lit))
;;            (equal (field-offsetp offset *lookup* *s* (assign-lit lit st))
;;                   (field-offsetp offset *lookup* *s* st)))
;;   :hints (("Goal" :in-theory (enable assignment-stp))))


;; (defthm assignment-stp-implies-field-offsetp-assign-lit-2222
;;   (implies (and (assignment-stp st)
;;                 ;; (assignment-stp (clause-to-assignment
;;                 ;;                                       clause st))
;;                 (clausep clause)
;;                 (clause-in-rangep clause st)
;;                 (clause-agrees-with-stackp clause st)
;;                 (field-offsetp offset *lookup* *s* st))
;;            (field-offsetp offset *lookup* *s* (clause-to-assignment clause st)))
;;   :hints (("Goal" :in-theory (enable lit-in-rangep)
;;            :induct (clause-to-assignment clause st))
;;           ("Subgoal *1/2.2'"
;;            ;:in-theory (disable fjfjfjf)
;;            :use ((:instance lit-in-range-negate
;;                             (lit 

;;           ("Subgoal *1/7'''"
;;            :expand (clause-to-assignment clause st))))


;; (defthm farrayp-assign-lit-inverse
;;   (implies (and 
;;                 (fieldp *stack-end* *s* st)
;;                 (fieldp *stack* *s* st)
;;                 (fieldp *lookup* *s* st)
;;                 (field-offsetp (fread *stack-end* 0 *s* st) *stack* *s* st)
;;                 (field-offsetp lit *lookup* *s* st)
;;                 (literalp lit)
;;                 (farrayp *s* (assign-lit lit st)))
;;            (farrayp *s* st))
;;   :hints (("Goal" :in-theory (enable assign-lit))))

;; (defthm assignment-stp-assign-lit-inverse
;;   (implies (and 
;;                 (literalp lit)
;;                 ;; (field-offsetp (fread *stack-end* 0 *s* st) *stack* *s* st)
;;                 ;; (field-offsetp (1+ (fread *stack-end* 0 *s* st)) *stack* *s* st)
;;                 (field-offsetp lit *lookup* *s* st)
;;                 ;(lit-in-rangep lit st)
;;                 ;(not (stack-fullp st))
;;                 (not (field-memberp lit (1- (fread *stack-end* 0 *s* st)) 0
;;                                     *stack* *s* st))
;;                 (not (field-memberp (negate lit) (1- (fread *stack-end* 0 *s*
;;                                                             st)) 0 *stack* *s*
;;                                                             st))
;;                 (assignment-stp (assign-lit lit st))
;;                 )
;;            (assignment-stp st) )
;;   :hints (("Goal" :in-theory (enable assignment-stp))))


;; (skip-proofs
(defthm assignment-stp-clause-to-assignment
  (implies (and (assignment-stp st)
                (clausep clause)
                (clause-in-rangep clause st)
                (clause-agrees-with-stackp clause st))
           (assignment-stp (clause-to-assignment clause st)))
  :otf-flg t
  :hints (("Goal"
           :induct (clause-to-assignment clause st))
           ;; :in-theory (e/d (lit-in-rangep)
           ;;                 (assignment-stp-assign-lit
           ;;                  ;; lit-in-rangep-mv-nth-0-find-unit-clause-project
           ;;                  IFF-FIELD-MEMBERP-MEMBER-PROJECT1
           ;;                  IFF-FIELD-MEMBERP-MEMBER-PROJECT
           ;;                  ;; lit-in-range-negate
           ;;                  ))
           ;; )
          ("Subgoal *1/2.3'"
           :in-theory (enable lit-in-rangep)
           :use ((:instance assignment-stp-assign-lit
                            (lit (negate (car clause))) )))))
          ;; ("Subgoal *1/2.3"
          ;;  :use ((:instance lit-in-range-negate
          ;;                   (lit (car clause))
          ;;                   (st (clause-to-assignment (cdr clause) st))) ))))
          ;;        (:instance lit-in-rangep-clause-to-assignment
          ;;                   (lit (car clause))
          ;;                   (clause (cdr clause)))))))
                             
;; (defthm fread-*num-vars*-assign-lit
;;   (implies (and (assignment-stp st)
;;                 (literalp lit)
;;                 (lit-in-rangep lit st))
;;            (equal (fread *num-vars* 0 *s* (assign-lit lit st))
;;                   (fread *num-vars* 0 *s* st)))
;;   :hints (("Goal" :in-theory (enable assign-lit assignment-stp))))


;; (defthm fread-clause-to-assignment
;;   (implies (and (assignment-stp (clause-to-assignment clause st))
;;                 (assignment-stp st)
;;                 (clausep clause)
;;                 (clause-in-rangep clause st)
;;                 (consp clause))
;;            (assignment-stp (clause-to-assignment (cdr clause) st))))
;; :in-theory (enable assignment-stp assign-lit))))

;; (defthm fread-clause-to-assignment
;;   (implies (and (assignment-stp st)
;;                 (assignment-stp (clause-to-assignment clause st))
;;                 (clausep clause)
;;                 (clause-in-rangep clause st))
;;            (equal (fread *num-vars* 0 *s* (clause-to-assignment clause st))
;;                   (fread *num-vars* 0 *s* st)))
;;   :hints (("Subgoal *1/7''"
;;            :use ((:instance fread-*num-vars*-assign-lit
;;                             (lit (negate (car clause)))
;;                             (st (clause-to-assignment (cdr clause) st)))))))

;; (defthm lit-in-rangep-diff-st
;;   (implies (and (assignment-stp st1)
;;                 (assignment-stp st2)
;;                 (literalp lit)
;;                 (lit-in-rangep lit st1)
;;                 (equal (fread *num-vars* 0 *s* st1)
;;                        (fread *num-vars* 0 *s* st2)))
;;            (lit-in-rangep lit st2))
;;   :hints (("Goal"
;;            :in-theory (enable lit-in-rangep))))

;; (skip-proofs 
;;  (defthm assignment-stp-clause-to-assignment
;;    (implies (and (assignment-stp st)
;;                  (clausep clause)
;;                  (clause-in-rangep clause st))
;;             (assignment-stp (clause-to-assignment clause st)))))
  ;; :hints (("Goal"
  ;;          :induct (clause-to-assignment clause st))
  ;;         ("Subgoal *1/2''"
  ;;          :use ((:instance assignment-stp-assign-lit-2
  ;;                           (lit (negate (car clause)))
  ;;                           (st (clause-to-assignment (cdr clause) st)))))
  ;;         ("Subgoal *1/2'5'"
  ;;          :use ((:instance lit-in-rangep-diff-st
  ;;                           (lit (negate (car clause)))
  ;;                           (st1 st)
  ;;                           (st2 (clause-to-assignment (cdr clause) st)))))
  ;;         ))

;; (skip-proofs 
(defthm lit-in-rangep-clause-to-assignment
  (implies (and (assignment-stp st)
                (clausep clause)
                (clause-in-rangep clause st)
                (clause-agrees-with-stackp clause st)
                (literalp lit)
                (lit-in-rangep lit st))
           (lit-in-rangep lit (clause-to-assignment clause st)))
  :hints (("Goal"
           :in-theory (enable lit-in-rangep)
           :induct (clause-to-assignment clause st))
          ("Subgoal *1/2.2'"
           :in-theory (enable assignment-stp)
           :use ((:instance field-offsetp-assign-lit
                            (offset lit)
                            (f *lookup*)
                            (lit (negate (car clause)))))) ))


(defthm clause-in-rangep-clause-to-assignment
  (implies (and (assignment-stp st)
                (clausep clause)
                (clause-in-rangep clause st)
                (clause-agrees-with-stackp clause st))
           (clause-in-rangep clause (clause-to-assignment clause st)))
  :hints (("Goal"
           :in-theory (enable lit-in-rangep)
           :induct (clause-to-assignment clause st))))


(defthm formula-in-rangep-clause-to-assignment
  (implies (and (assignment-stp st)
                (formulap formula)
                (formula-in-rangep formula st)
                (clausep clause)
                (clause-in-rangep clause st)
                (clause-agrees-with-stackp clause st))
           (formula-in-rangep formula (clause-to-assignment clause st))) )


;; (skip-proofs
;; (verify-guards clause-to-assignment))

;; (skip-proofs
;;  (verify-guards unassign-one))

;; (skip-proofs
;;  (verify-guards unassign-all))




(defthm field-offsetp-unassign-all
  (implies (and (assignment-stp st)
                ;(equal (fread *stack-end* 0 *s* st) i)
                (field-offsetp offset *lookup* *s* st))
           (field-offsetp offset *lookup* *s* (unassign-all i st)))
  :hints (("Goal"
           :in-theory (enable unassign-all assignment-stp)
           :induct (unassign-all i st))))


(defthm lit-in-rangep-unassign-all
  (implies (and (assignment-stp st)
                (literalp lit)
                (lit-in-rangep lit st))
           (lit-in-rangep lit (unassign-all (fread *stack-end* 0 *s* st) st)))
  :hints (("Goal" :in-theory (enable assignment-stp lit-in-rangep))))

(defthm clause-in-rangep-unassign-all
  (implies (and (assignment-stp st)
                (clausep clause)
                (clause-in-rangep clause st))
           (clause-in-rangep clause (unassign-all (fread *stack-end* 0 *s* st) st))))

(defthm formula-in-rangep-unassign-all
  (implies (and (assignment-stp st)
                (formulap formula)
                (formula-in-rangep formula st))
           (formula-in-rangep formula (unassign-all (fread *stack-end* 0 *s* st) st))))




(defthm formula-in-rangep-unit-propagation
  (implies (and (assignment-stp st)
                (formulap formula)
                (formula-in-rangep formula st))
           (formula-in-rangep formula (unit-propagation-st formula st))))


(defthm clause-agrees-with-stackp-unassign-all
  (implies (and (assignment-stp st)
                (clausep clause)
                (clause-in-rangep clause st))
           (clause-agrees-with-stackp clause
                                      (unassign-all (fread *stack-end* 0 *s* st) st))))


(defun ATp-st (formula clause st)
  (declare (xargs :guard (and (assignment-stp st)
                              (formulap formula)
                              (formula-in-rangep formula st)
                              (clausep clause)
                              (clause-in-rangep clause st))
                  :guard-hints (("Goal"
                                 :do-not-induct t
                                 :in-theory (e/d (assignment-stp) ()))
                                ("Subgoal 1.4"
                                 :use ((:instance
                                        clause-in-rangep-unassign-all)))
                                ("Subgoal 1.3"
                                 :use ((:instance
                                        formula-in-rangep-clause-to-assignment
                                        (st (unassign-all (fread *stack-end* 0
                                                                 *s* st) st)))
                                       (:instance
                                        formula-in-rangep-unassign-all)
                                       (:instance
                                        clause-in-rangep-unassign-all)
                                       (:instance
                                        clause-agrees-with-stackp-unassign-all)))
                                ("Subgoal 1.2"
                                 :use ((:instance
                                        clause-agrees-with-stackp-unassign-all))))
                  :stobjs (st)))
  (let* ((st (unassign-all (fread *stack-end* 0 *s* st) st))
         (st (clause-to-assignment clause st))
         (st (unit-propagation-st formula st)))
    (mv (falsep (evaluate-formula-st formula st))
        st)))

(defthm append-revappend-cons
  (equal (append (revappend x y)
                 (cons a b))
         (append (revappend x (append y (list a)))
                 b)))

(defthm negate-clause-equiv-1
  (implies (and (assignment-stp st)
                (clausep clause)
                (clause-in-rangep clause st)
                (clause-agrees-with-stackp clause st))
           (equal (project (clause-to-assignment clause st))
                  (append (revappend (negate-clause clause) nil)
                          (project st))))
  :hints (("Goal"
           :in-theory (enable lit-in-rangep)
           :induct (clause-to-assignment clause st))))
  ;; :hints (("Subgoal *1/7'''" :use ((:instance assign-lit-cons-project
  ;;                           (lit (negate (car clause)))
  ;;                           (st (clause-to-assignment (cdr clause) st))) )) ))

(defthm append-nil-2
  (implies (true-listp x)
           (equal (append x nil) x)))

(defthm true-listp-revappend
  (implies (and (true-listp x)
                (true-listp y))
           (true-listp (revappend x y))))
           ;; (equal (append x nil) x)))

(defthm negate-clause-equiv
  (implies (and (assignment-stp st)
                (clausep clause)
                (clause-in-rangep clause st))
           (equal (project (clause-to-assignment
                            clause
                            (unassign-all (fread *stack-end* 0 *s* st) st)))
                  (revappend (negate-clause clause) nil))))

(defthm ATp-equiv
  (implies (and (assignment-stp st)
                (formulap formula)
                (formula-in-rangep formula st)
                (clausep clause)
                (clause-in-rangep clause st))
           (equal (mv-nth 0 (ATp-st formula clause st))
                  (ATp formula clause))))


;; ===================================================================

(defun clause-list-in-rangep (clause-list st)
  (declare (xargs :guard (and (assignment-stp st)
                              (clause-listp clause-list))
                  :stobjs (st)))
  (if (atom clause-list)
      t
    (and (clause-in-rangep (car clause-list) st)
         (clause-list-in-rangep (cdr clause-list) st))))


(defthm clause-in-rangep-union
  (implies (and (clause-in-rangep c1 st)
                (clause-in-rangep c2 st))
           (clause-in-rangep (union c1 c2) st)))

(defthm clause-in-rangep-remove-literal
  (implies (and (clause-in-rangep clause st))
           (clause-in-rangep (remove-literal lit clause) st)))

(defthm clause-in-rangep-resolution
  (implies (and (clause-in-rangep c1 st)
                (clause-in-rangep c2 st))
           (clause-in-rangep (resolution lit c1 c2) st)))


(defthm lit-in-rangep-unit-propagation-st
  (implies (and (assignment-stp st)
                (literalp lit)
                (lit-in-rangep lit st)
                (formulap formula)
                (formula-in-rangep formula st))
           (lit-in-rangep lit (unit-propagation-st formula st))))

(defthm clause-in-rangep-unit-propagation-st
  (implies (and (assignment-stp st)
                (clausep clause)
                (clause-in-rangep clause st)
                (formulap formula)
                (formula-in-rangep formula st))
           (clause-in-rangep clause (unit-propagation-st formula st))))

(defthm clause-list-in-rangep-unit-propagation-st
  (implies (and (assignment-stp st)
                (clause-listp clause-list)
                (clause-list-in-rangep clause-list st)
                (formulap formula)
                (formula-in-rangep formula st))
           (clause-list-in-rangep clause-list (unit-propagation-st formula st))))

(defthm formula-in-rangep-unit-propagation-st
  (implies (and (assignment-stp st)
                (formulap formula1)
                (formula-in-rangep formula1 st)
                (formulap formula2)
                (formula-in-rangep formula2 st))
           (formula-in-rangep formula1 (unit-propagation-st formula2 st))))


(defthm clause-in-rangep-clause-to-assignment-2
  (implies (and (assignment-stp st)
                (clausep clause)
                (clause-in-rangep clause st)
                (clausep clause2)
                (clause-in-rangep clause2 st)
                (clause-agrees-with-stackp clause2 st))
           (clause-in-rangep clause (clause-to-assignment clause2 st))))


(defthm clause-list-in-rangep-assign-lit
  (implies (and (assignment-stp st)
                (clause-listp clause-list)
                (clause-list-in-rangep clause-list st)
                (literalp lit)
                (lit-in-rangep lit st))
           (clause-list-in-rangep clause-list (assign-lit lit st))))

(defthm clause-list-in-rangep-clause-to-assignment
  (implies (and (assignment-stp st)
                (clause-listp clause-list)
                (clause-list-in-rangep clause-list st)
                (clausep clause)
                (clause-in-rangep clause st)
                (clause-agrees-with-stackp clause st))
           (clause-list-in-rangep clause-list (clause-to-assignment clause st))))

(defthm clause-list-in-rangep-unassign-all
  (implies (and (assignment-stp st)
                (clause-listp clause-list)
                (clause-list-in-rangep clause-list st))
           (clause-list-in-rangep clause-list (unassign-all (fread *stack-end*
                                                                   0 *s* st) st))))



(in-theory (disable resolution clausep))

(defun RATp1-st (clause-list formula clause literal st)
  (declare (xargs :guard (and (assignment-stp st)
                              (clause-listp clause-list)
                              (clause-list-in-rangep clause-list st)
                              (formulap formula)
                              (formula-in-rangep formula st)
                              (clausep clause)
                              (clause-in-rangep clause st)
                              (literalp literal)
                              (lit-in-rangep literal st))
                  :stobjs (st)))
  (if (atom clause-list)
      (mv t st)
    (if (not (member (negate literal) (car clause-list)))
        (RATp1-st (cdr clause-list) formula clause literal st)
      (let ((resolvent (resolution literal clause (car clause-list))))
       (if (tautologyp resolvent)
           (RATp1-st (cdr clause-list) formula clause literal st)
         (mv-let (is-atp st)
                 (ATp-st formula resolvent st)
                 (if is-atp
                     (RATp1-st (cdr clause-list) formula clause literal st)
                   (mv nil st))))))))

;; (defthm mv-nth-0-atp-st-diff-st
;;   (implies (and (assignment-stp st1)
;;                 (assignment-stp st2)
;;                 (formulap formula)
;;                 (formula-in-rangep formula st1)
;;                 (formula-in-rangep formula st2)
;;                 (clausep clause)
;;                 (clause-in-rangep clause st1)
;;                 (clause-in-rangep clause st2)
;;                 )
;;            (equal (mv-nth 0 (atp-st formula clause st1))
;;                   (mv-nth 0 (atp-st formula clause st2))))
;;   :rule-classes nil)

;; (defthm unassign-all-diff-st
;;   (implies (and (assignment-stp st1)
;;                 (assignment-stp st2)
;;                 (equal 0 (fread *stack-end* 0 *s* st1))
;;                 (equal 0 (fread *stack-end* 0 *s* st2))
;;                 (equal (fread *num-vars* 0 *s* st1)
;;                        (fread *num-vars* 0 *s* st2))
;;                 (not (equal st1 st2))
;;   :hints (("Goal" :in-theory (enable assignment-stp)))
;;   :rule-classes nil)

;; (defthm unassign-all-diff-st
;;   (implies (and (assignment-stp st1)
;;                 (assignment-stp st2)
;;                 (equal i (fread *stack-end* 0 *s* st1))
;;                 (hide (equal j (fread *stack-end* 0 *s* st2)))
;;                 (equal (fread *num-vars* 0 *s* st1)
;;                        (fread *num-vars* 0 *s* st2)))
;;            (equal (unassign-all i st1)
;;                   (unassign-all j st2)))
;;   :hints (("Goal"
;;            :in-theory (enable assignment-stp unassign-all)
;;            :induct (unassign-all i st1)
;;            )
;;           ("Subgoal *1/2''"
;;            :expand (hide (equal j (fread *stack-end* 0 *s* st2)))
;;            :induct (unassign-all j st2))))
                
;; (defthm mv-nth-1-atp-st-diff-st
;;   (implies (and (assignment-stp st1)
;;                 (assignment-stp st2)
;;                 (formulap formula)
;;                 (formula-in-rangep formula st1)
;;                 (formula-in-rangep formula st2)
;;                 (clausep clause)
;;                 (clause-in-rangep clause st1)
;;                 (clause-in-rangep clause st2)
;;                 )
;;            (equal (project (mv-nth 1 (atp-st formula clause st1)))
;;                   (project (mv-nth 1 (atp-st formula clause st2))))
;;   :rule-classes nil)


;; ;; (skip-proofs)
;; (defthm mv-nth-0-ratp1-st-diff-st
;;   (implies (and (assignment-stp st1)
;;                 (assignment-stp st2)
;;                 (clause-listp clause-list)
;;                 (clause-list-in-rangep clause-list st1)
;;                 (clause-list-in-rangep clause-list st2)
;;                 (formulap formula)
;;                 (formula-in-rangep formula st1)
;;                 (formula-in-rangep formula st2)
;;                 (clausep clause)
;;                 (clause-in-rangep clause st1)
;;                 (clause-in-rangep clause st2)
;;                 (literalp lit)
;;                 (lit-in-rangep lit st1)
;;                 (lit-in-rangep lit st2)
;;                 )
;;            (equal (mv-nth 0 (ratp1-st clause-list formula clause lit st1))
;;                   (mv-nth 0 (ratp1-st clause-list formula clause lit st2))))
;;   :hints (("Goal"
;;            :in-theory (disable atp-st atp-equiv))
;;           ("Subgoal *1/18'''"
;;            :expand (ratp1-st clause-list formula clause lit st1)
;;            :use ((:instance mv-nth-0-atp-st-diff-st
;;                             (clause (resolution lit clause (car
;;                                                             clause-list))))))
;;           ("Subgoal *1/17''"
;;            ;:expand (ratp1-st clause-list formula clause lit st1)
;;            :use ((:instance mv-nth-0-atp-st-diff-st
;;                             (clause (resolution lit clause (car
;;                                                             clause-list))))))
;;           )
;;   :rule-classes nil)


(defthm assignment-stp-mv-nth-1-atp-st
  (implies (and (assignment-stp st)
                (formulap formula)
                (formula-in-rangep formula st)
                (clausep clause)
                (clause-in-rangep clause st))
           (assignment-stp (mv-nth 1 (ATp-st formula clause st)))))

(defthm clause-in-rangep-mv-nth-1-atp-st
  (implies (and (assignment-stp st)
                (formulap formula)
                (formula-in-rangep formula st)
                (clausep clause)
                (clause-in-rangep clause st)
                (clausep clause2)
                (clause-in-rangep clause2 st))
           (clause-in-rangep clause2 (mv-nth 1 (atp-st formula clause st)))))

(defthm lit-in-rangep-mv-nth-1-atp-st
  (implies (and (assignment-stp st)
                (formulap formula)
                (formula-in-rangep formula st)
                (clausep clause)
                (clause-in-rangep clause st)
                (literalp lit)
                (lit-in-rangep lit st))
           (lit-in-rangep lit (mv-nth 1 (atp-st formula clause st)))))

(defthm clause-list-in-rangep-mv-nth-1-atp-st
  (implies (and (assignment-stp st)
                (formulap formula)
                (formula-in-rangep formula st)
                (clausep clause)
                (clause-in-rangep clause st)
                (clause-listp clause-list)
                (clause-list-in-rangep clause-list st))
           (clause-list-in-rangep clause-list (mv-nth 1 (atp-st formula clause st)))))

(defthm formula-in-rangep-mv-nth-1-atp-st
  (implies (and (assignment-stp st)
                (formulap formula)
                (formula-in-rangep formula st)
                (clausep clause)
                (clause-in-rangep clause st)
                (formulap formula2)
                (formula-in-rangep formula2 st))
           (formula-in-rangep formula2 (mv-nth 1 (atp-st formula clause st)))))

(defthm RATp1-equiv
  (implies (and (assignment-stp st)
                (clause-listp clause-list)
                (clause-list-in-rangep clause-list st)
                (formulap formula)
                (formula-in-rangep formula st)
                (clausep clause)
                (clause-in-rangep clause st)
                (literalp literal)
                (lit-in-rangep literal st))
           (equal (mv-nth 0 (RATp1-st clause-list formula clause literal st))
                  (RATp1 clause-list formula clause literal)))
  :otf-flg t
  :hints (("Goal"
           :in-theory (disable atp atp-st)
           :induct (ratp1-st clause-list formula clause literal st)) ))
          ;; ("Subgoal *1/10''"
          ;;  :expand (ratp1-st clause-list formula clause literal st)) ))
          ;; ("Subgoal *1/10'''"
          ;;  :use ((:instance mv-nth-0-ratp1-st-diff-st
          ;;                   (clause-list (cdr clause-list))
          ;;                   (lit literal)
          ;;                   (st2 st)
          ;;                   (st1 (mv-nth 1 (atp-st formula
          ;;                                          (resolution literal clause
          ;;                                                      (car clause-list)) st))))))
          ;; ))

(defun RATp-st (formula clause literal st)
  (declare (xargs :guard (and (assignment-stp st)
                              (formulap formula)
                              (formula-in-rangep formula st)
                              (clausep clause)
                              (clause-in-rangep clause st)
                              (literalp literal)
                              (lit-in-rangep literal st))
                  :stobjs (st)))
  (RATp1-st formula formula clause literal st))

(defthm formulap-implies-clause-listp
  (implies (formulap formula)
           (clause-listp formula)))

(defthm formula-in-rangep-implies-clause-list-in-rangep
  (implies (formula-in-rangep formula st)
           (clause-list-in-rangep formula st)))

(defthm RATp-equiv
  (implies (and (assignment-stp st)
                (formulap formula)
                (formula-in-rangep formula st)
                (clausep clause)
                (clause-in-rangep clause st)
                (literalp literal)
                (lit-in-rangep literal st))
           (equal (mv-nth 0 (RATp-st formula clause literal st))
                  (RATp formula clause literal))) )


(defun verify-clause-st (clause formula st)
  (declare (xargs :guard (and (assignment-stp st)
                              (formulap formula)
                              (formula-in-rangep formula st)
                              (clausep clause)
                              (clause-in-rangep clause st))
                  :stobjs (st)))
  (mv-let (is-atp st)
          (ATp-st formula clause st)
          (if is-atp
              (mv t st)
            (if (atom clause)
                (mv nil st)
              (RATp-st formula clause (car clause) st)))))


(defthm verify-clause-st-equiv
  (implies (and (assignment-stp st)
                (clausep clause)
                (clause-in-rangep clause st)
                (formulap formula)
                (formula-in-rangep formula st))
           (equal (mv-nth 0 (verify-clause-st clause formula st))
                  (verify-clause clause formula))) )

;; (i-am-here)

;; ===================================================================

(defthm assignment-stp-mv-nth-1-ratp1-st
  (implies (and (assignment-stp st)
                (clause-listp clause-list)
                (clause-list-in-rangep clause-list st)
                (formulap formula)
                (formula-in-rangep formula st)
                (clausep clause)
                (clause-in-rangep clause st)
                (literalp literal)
                (lit-in-rangep literal st))
           (assignment-stp (mv-nth 1 (ratp1-st clause-list formula clause
                                               literal st))))
  :hints (("Goal" :induct (ratp1-st clause-list formula clause literal st))))

(defthm lit-in-rangep-mv-nth-1-ratp1-st
  (implies (and (assignment-stp st)
                (clause-listp clause-list)
                (clause-list-in-rangep clause-list st)
                (formulap formula)
                (formula-in-rangep formula st)
                (clausep clause)
                (clause-in-rangep clause st)
                (literalp literal)
                (lit-in-rangep literal st)
                (literalp literal2)
                (lit-in-rangep literal2 st))
           (lit-in-rangep literal2 (mv-nth 1 (ratp1-st clause-list formula
                                                       clause literal st))))
  :hints (("Goal" :induct (ratp1-st clause-list formula clause literal st))))

(defthm clause-in-rangep-mv-nth-1-ratp1-st
  (implies (and (assignment-stp st)
                (clause-listp clause-list)
                (clause-list-in-rangep clause-list st)
                (formulap formula)
                (formula-in-rangep formula st)
                (clausep clause)
                (clause-in-rangep clause st)
                (literalp literal)
                (lit-in-rangep literal st)
                (clausep clause2)
                (clause-in-rangep clause2 st))
           (clause-in-rangep clause2 (mv-nth 1 (ratp1-st clause-list formula
                                                         clause literal st)))))


(defthm clause-list-in-rangep-mv-nth-1-ratp1-st
  (implies (and (assignment-stp st)
                (clause-listp clause-list)
                (clause-list-in-rangep clause-list st)
                (formulap formula)
                (formula-in-rangep formula st)
                (clausep clause)
                (clause-in-rangep clause st)
                (literalp literal)
                (lit-in-rangep literal st)
                (clause-listp clause-list2)
                (clause-list-in-rangep clause-list2 st))
           (clause-list-in-rangep clause-list2 (mv-nth 1 (ratp1-st clause-list
                                                                   formula clause literal st)))))

(defthm formula-in-rangep-mv-nth-1-ratp1-st
  (implies (and (assignment-stp st)
                (clause-listp clause-list)
                (clause-list-in-rangep clause-list st)
                (formulap formula)
                (formula-in-rangep formula st)
                (clausep clause)
                (clause-in-rangep clause st)
                (literalp literal)
                (lit-in-rangep literal st)
                (formulap formula2)
                (formula-in-rangep formula2 st))
           (formula-in-rangep formula2 (mv-nth 1 (ratp1-st clause-list formula
                                                           clause literal st)))))

;; ===================================================================

(defthm assignment-stp-mv-nth-1-ratp-st
  (implies (and (assignment-stp st)
                (formulap formula)
                (formula-in-rangep formula st)
                (clausep clause)
                (clause-in-rangep clause st)
                (literalp literal)
                (lit-in-rangep literal st))
           (assignment-stp (mv-nth 1 (ratp-st formula clause literal st)))))


(defthm lit-in-rangep-mv-nth-1-ratp-st
  (implies (and (assignment-stp st)
                (formulap formula)
                (formula-in-rangep formula st)
                (clausep clause)
                (clause-in-rangep clause st)
                (literalp literal)
                (lit-in-rangep literal st)
                (literalp literal2)
                (lit-in-rangep literal2 st))
           (lit-in-rangep literal2 (mv-nth 1 (ratp-st formula clause literal
                                                      st)))))


(defthm clause-in-rangep-mv-nth-1-ratp-st
  (implies (and (assignment-stp st)
                (formulap formula)
                (formula-in-rangep formula st)
                (clausep clause)
                (clause-in-rangep clause st)
                (literalp literal)
                (lit-in-rangep literal st)
                (clausep clause2)
                (clause-in-rangep clause2 st))
           (clause-in-rangep clause2 (mv-nth 1 (ratp-st formula clause literal st)))))


(defthm clause-list-in-rangep-mv-nth-1-ratp-st
  (implies (and (assignment-stp st)
                (formulap formula)
                (formula-in-rangep formula st)
                (clausep clause)
                (clause-in-rangep clause st)
                (literalp literal)
                (lit-in-rangep literal st)
                (clause-listp clause-list)
                (clause-list-in-rangep clause-list st))
           (clause-list-in-rangep clause-list (mv-nth 1 (ratp-st formula clause
                                                                 literal st)))))

(defthm formula-in-rangep-mv-nth-1-ratp-st
  (implies (and (assignment-stp st)
                (formulap formula)
                (formula-in-rangep formula st)
                (clausep clause)
                (clause-in-rangep clause st)
                (literalp literal)
                (lit-in-rangep literal st)
                (formulap formula2)
                (formula-in-rangep formula2 st))
           (formula-in-rangep formula2 (mv-nth 1 (ratp-st formula clause literal st)))))

;; ===================================================================

(in-theory (disable ratp-st))

(defthm assignment-stp-mv-nth-1-verify-clause-st
  (implies (and (assignment-stp st)
                (formulap formula)
                (formula-in-rangep formula st)
                (clausep clause)
                (clause-in-rangep clause st))
           (assignment-stp (mv-nth 1 (verify-clause-st clause formula st)))))


(defthm lit-in-rangep-mv-nth-1-verify-clause-st
  (implies (and (assignment-stp st)
                (formulap formula)
                (formula-in-rangep formula st)
                (clausep clause)
                (clause-in-rangep clause st)
                (literalp literal)
                (lit-in-rangep literal st))
           (lit-in-rangep literal (mv-nth 1 (verify-clause-st clause formula
                                                              st)))))



(defthm clause-in-rangep-mv-nth-1-verify-clause-st
  (implies (and (assignment-stp st)
                (formulap formula)
                (formula-in-rangep formula st)
                (clausep clause)
                (clause-in-rangep clause st)
                (clausep clause2)
                (clause-in-rangep clause2 st))
           (clause-in-rangep clause2 (mv-nth 1 (verify-clause-st clause formula st)))))


(defthm clause-list-in-rangep-mv-nth-1-verify-clause-st
  (implies (and (assignment-stp st)
                (formulap formula)
                (formula-in-rangep formula st)
                (clausep clause)
                (clause-in-rangep clause st)
                (clause-listp clause-list)
                (clause-list-in-rangep clause-list st))
           (clause-list-in-rangep clause-list (mv-nth 1 (verify-clause-st
                                                         clause formula st)))))

(defthm formula-in-rangep-mv-nth-1-verify-clause-st
  (implies (and (assignment-stp st)
                (formulap formula)
                (formula-in-rangep formula st)
                (clausep clause)
                (clause-in-rangep clause st)
                (formulap formula2)
                (formula-in-rangep formula2 st))
           (formula-in-rangep formula2 (mv-nth 1 (verify-clause-st clause
                                                                   formula st)))))



;; ===================================================================

(in-theory (disable verify-clause-st))

(defun verify-proof-st (clause-list formula st)
  (declare (xargs :guard (and (assignment-stp st)
                              (clause-listp clause-list)
                              (clause-list-in-rangep clause-list st)
                              (formulap formula)
                              (formula-in-rangep formula st))
                  :stobjs (st)))
  (if (atom clause-list)
      (mv t st)
    (mv-let (vc st)
            (verify-clause-st (car clause-list) formula st)
            (if (not vc)
                (mv nil st)
              (verify-proof-st (cdr clause-list)
                               (cons (car clause-list) formula)
                               st)))))

(defthm verify-proof-st-equiv
  (implies (and (assignment-stp st)
                (clause-listp clause-list)
                (clause-list-in-rangep clause-list st)
                (formulap formula)
                (formula-in-rangep formula st))
           (equal (mv-nth 0 (verify-proof-st clause-list formula st))
                  (verify-proof clause-list formula)))
  :hints (("Goal" :induct (verify-proof-st clause-list formula st))))

;; ===================================================================


(defun proofp-st (proof formula st)
  (declare (xargs :guard (and (assignment-stp st)
                              (formulap formula)
                              (formula-in-rangep formula st))
                  :stobjs (st)))
  (if (not (clause-listp proof))
      (mv nil st)
    (if (not (clause-list-in-rangep proof st))
        (mv nil st)
      (verify-proof-st proof formula st))))

(defthm proofp-st-equiv
  (implies (and (assignment-stp st)
                (clause-listp proof)
                (clause-list-in-rangep proof st)
                (formulap formula)
                (formula-in-rangep formula st))
           (equal (mv-nth 0 (proofp-st proof formula st))
                  (proofp proof formula))))

(defun refutationp-st (proof formula st)
  (declare (xargs :guard (and (assignment-stp st)
                              (formulap formula)
                              (formula-in-rangep formula st)
                              (true-listp proof))
                  :stobjs (st)))
  (if (not (member *empty-clause* proof))
      (mv nil st)
    (proofp-st proof formula st)))

(defthm refutationp-st-equiv
  (implies (and (assignment-stp st)
                (clause-listp proof)
                (clause-list-in-rangep proof st)
                (formulap formula)
                (formula-in-rangep formula st)
                (member *empty-clause* proof))
           (iff (mv-nth 0 (refutationp-st proof formula st))
                (refutationp proof formula))))


(defthm exists-solution-implies-not-refutationp-st
  (implies (and (assignment-stp st)
                (formulap formula)
                (formula-in-rangep formula st)
                (clause-listp clause-list)
                (clause-list-in-rangep clause-list st)
                (exists-solution formula))
           (not (mv-nth 0 (refutationp-st clause-list formula st)))))


(defthm exists-solution-implies-not-refutationp-st-contrapositive
  (implies (and (assignment-stp st)
                (formulap formula)
                (formula-in-rangep formula st)
                (clause-listp clause-list)
                (clause-list-in-rangep clause-list st)
                (mv-nth 0 (refutationp-st clause-list formula st)))
           (not (exists-solution formula))))

(defthm main-theorem
  (implies (and (formulap formula)
                (refutationp clause-list formula))
           (not (exists-solution formula))))








































;; ===================================================================
;; ===================================================================
;; ===================================================================

;; (defconst *st-4-empty*
;;   '(4  ;  0 - num-fields
;;     6  ;  1 - num-vars offset
;;     7  ;  2 - stack-end offset
;;     8  ;  3 - stack offset
;;     13 ;  4 - lookup offset
;;     23 ;  5 - end offset
;;     4  ;  6 - 0 - num-vars
;;     0  ;  7 - 0 - stack-end
;;     0  ;  8 - 0 - stack bottom
;;     0  ;  9 - 1
;;     0  ; 10 - 2
;;     0  ; 11 - 3
;;     0  ; 12 - 4 - padding
;;     0  ; 13 - 0 - lookup
;;     0  ; 14 - 1
;;     0  ; 15 - 2
;;     0  ; 16 - 3
;;     0  ; 17 - 4
;;     0  ; 18 - 5
;;     0  ; 19 - 6
;;     0  ; 20 - 7
;;     0  ; 21 - 8
;;     0  ; 22 - 9
;;     0  ; 23 - end
;;     ))
