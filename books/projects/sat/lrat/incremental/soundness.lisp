; Copyright (C) 2017, Regents of the University of Texas
; Marijn Heule, Warren A. Hunt, Jr., and Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; See ../README.

(in-package "LRAT")

(include-book "incremental")

(deflabel soundness-start)

(in-theory (theory 'ground-zero))

(defthm ordered-formula-p-forward-to-true-listp
  (implies (ordered-formula-p formula)
           (true-listp formula))
  :hints (("Goal" :in-theory (enable ordered-formula-p)))
  :rule-classes :forward-chaining)

(defun proved-formula (cnf-file clrat-file chunk-size debug incomplete-okp ctx
                                state)
  (declare (xargs :stobjs state
                  :guard-hints
                  (("Goal" :in-theory (enable incl-valid-proofp$-top
                                              acl2::error1-logic)))))
  (mv-let (erp val/formula state)
    (incl-valid-proofp$-top cnf-file clrat-file
                            incomplete-okp
                            chunk-size debug ctx state)
    (value (and (null erp)
                (consp val/formula)
                (eq (car val/formula) t)

; The formula returned by incl-valid-proofp$-top is in reverse order.  We
; prefer to return a formula that we expect to agree with the formula
; represented in the input cnf-file.

                (reverse (cdr val/formula))))))

(in-theory (disable reverse))

(encapsulate
  ()
  (local (include-book "soundness-main"))
  (set-enforce-redundancy t)
  (defthm soundness-main
    (implies
     (and (equal (car (incl-valid-proofp$-top-rec formula
                                                  clrat-file posn chunk-size
                                                  clrat-file-length
                                                  old-suffix debug max-var a$ ctx
                                                  state))
                 :complete)
          (formula-p formula)
          (a$p a$)
          (equal (a$ptr a$) 0)
          (integerp max-var)
          (<= (formula-max-var formula 0) max-var))
     (not (satisfiable formula)))))

(defthm a$p-initial-a$
  (a$p (resize-a$arr 2 (create-a$)))
  :hints (("Goal" :in-theory (current-theory 'soundness-start))))

(defthm a$ptr-initial-a$
  (equal (a$ptr (resize-a$arr 2 (create-a$)))
         0)
  :hints (("Goal" :in-theory (current-theory 'soundness-start))))


(defthm soundness-helper-1
  (implies
   (and (formula-p formula)
        (posp clrat-file-length)
        (equal (car (incl-valid-proofp$-top-rec formula
                                                clrat-file 0 chunk-size
                                                clrat-file-length
                                                "" debug
                                                (formula-max-var formula 0)
                                                (resize-a$arr 2 (create-a$))
                                                ctx state))
               :complete))
   (not (satisfiable formula)))
  :hints (("Goal" :in-theory (enable natp-formula-max-var))))

(encapsulate ; Prove satisfiable-reverse.
  ()

  (local
   (progn ; Prove hons-assoc-equal-reverse.

     (defthm hons-assoc-equal-revappend-lemma-1
       (implies (and (ordered-formula-p1 formula i)
                     (natp i)
                     (natp j)
                     (<= i j))
                (equal (hons-assoc-equal j (revappend formula acc))
                       (hons-assoc-equal j acc)))
       :hints (("Goal"
                :in-theory (enable ordered-formula-p1))))

     (defthm hons-assoc-equal-revappend-lemma-2
       (implies (and (ordered-formula-p1 formula i)
                     (natp i)
                     (natp j)
                     (<= i j))
                (equal (hons-assoc-equal j formula)
                       nil))
       :hints (("Goal"
                :in-theory (enable ordered-formula-p1))))

     (defthm hons-assoc-equal-revappend
       (implies (ordered-formula-p1 formula start)
                (equal (hons-assoc-equal index (revappend formula acc))
                       (or (hons-assoc-equal index formula)
                           (hons-assoc-equal index acc))))
       :hints (("Goal"
                :in-theory (enable ordered-formula-p1))))

     (defthm hons-assoc-equal-reverse
       (implies (ordered-formula-p formula)
                (equal (hons-assoc-equal index (reverse formula))
                       (hons-assoc-equal index formula)))
       :hints (("Goal" :in-theory (enable reverse ordered-formula-p))))))

  (local
   (defthm solution-p-reverse-implies-solution-p
     (implies (and (ordered-formula-p formula)
                   (solution-p assignment (reverse formula)))
              (solution-p assignment formula))
     :hints (("Goal"
              :in-theory (enable formula-truep-necc solution-p)
              :restrict ((formula-truep-necc
                          ((index (formula-truep-witness formula assignment)))))
              :expand ((formula-truep formula assignment))))))

  (defthm satisfiable-reverse
    (implies (and (ordered-formula-p formula)
                  (not (satisfiable formula)))
             (not (satisfiable (reverse formula))))
    :hints (("Goal"
             :in-theory (enable satisfiable-suff)
             :restrict ((satisfiable-suff
                         ((assignment (satisfiable-witness (reverse formula))))))
             :expand ((satisfiable (reverse formula)))))))

(defthm soundness-helper-2
  (implies (mv-let (erp val/formula state)
             (incl-valid-proofp$-top cnf-file clrat-file nil
                                     chunk-size debug ctx state)
             (declare (ignore state))
             (and (not erp)
                  (equal formula (reverse (cdr val/formula)))
                  (car val/formula)))
           (not (satisfiable formula)))
  :hints (("Goal"
           :in-theory (enable incl-valid-proofp$-top
                              acl2::error1-logic
                              incl-valid-proofp$-top-aux
                              ordered-formula-p-implies-formula-p))))

(defthm soundness
  (let ((formula (mv-nth 1
                         (proved-formula cnf-file clrat-file chunk-size debug
                                         nil ; incomplete-okp
                                         ctx state))))
    (implies formula
             (not (satisfiable formula))))
  :hints (("Goal" :restrict ((soundness-helper-2
                              ((state state)
                               (ctx ctx)
                               (debug debug)
                               (chunk-size chunk-size)
                               (clrat-file clrat-file)
                               (cnf-file cnf-file)))))))
