; Copyright (C) 2017, Regents of the University of Texas
; Marijn Heule, Warren A. Hunt, Jr., and Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; See cube.lisp.

(in-package "LRAT")

(include-book "cube")

; A small theory:
(include-book "../incremental/soundness")

; Add in useful lemmas:
(include-book "verify-for-cube-soundness-lemmas")

(defthm formula-p-revappend
  (implies (and (formula-p x)
                (formula-p y))
           (formula-p (revappend x y)))
  :hints (("Goal" :in-theory (enable formula-p))))

(defthm negate-cube-negate-cube
  (implies (literal-listp cube)
           (equal (negate-cube (negate-cube cube))
                  cube))
  :hints (("Goal" :in-theory (enable negate-cube literal-listp literalp))))

(defthm lemma-1
  (a$p (resize-a$arr 2 (hide (create-a$))))
  :hints (("Goal"
           :expand ((:free (x) (hide x)))
           :in-theory '((a$p)
                        (resize-a$arr)
                        create-a$
                        (make-list-ac)))))

(defthm lemma-2
  (equal (a$ptr (resize-a$arr 2 (hide (create-a$))))
         0)
  :hints (("Goal"
           :expand ((:free (x) (hide x)))
           :in-theory '((a$ptr)
                        (resize-a$arr)
                        create-a$
                        (make-list-ac)))))

(defun-sk formula-equiv (x y)
  (forall index
          (equal (hons-assoc-equal index x)
                 (hons-assoc-equal index y)))
  :rewrite :direct)

(in-theory (disable formula-equiv))

(defthm formula-equiv-preserves-satisfiable-1
  (implies (and (formula-equiv f1 f2)
                (formula-p f2)
                (clause-or-assignment-p assignment)
                (formula-truep f1 assignment))
           (formula-truep f2 assignment))
  :hints (("Goal"
           :expand ((formula-truep f2 assignment))
           :in-theory (enable formula-truep-necc)
           :restrict ((formula-truep-necc
                       ((index (formula-truep-witness f2 assignment))))))))

(defthm formula-equiv-preserves-satisfiable
  (implies (and (formula-p f2)
                (satisfiable f1)
                (formula-equiv f1 f2))
           (satisfiable f2))
  :hints (("Goal"
           :in-theory (enable solution-p)
           :use ((:instance satisfiable-suff
                            (assignment (satisfiable-witness f1))
                            (formula f2)))
           :expand ((satisfiable f1)))))

(defthm no-duplicatesp-equal-strip-cars-revappend
  (iff (no-duplicatesp-equal (strip-cars (revappend x Y)))
       (and (no-duplicatesp-equal (strip-cars x))
            (no-duplicatesp-equal (strip-cars y))
            (not (intersectp-equal (strip-cars x)
                                   (strip-cars y)))))
  :hints (("Goal"
           :induct (revappend x y)
           :in-theory (enable intersectp-equal-cons-2))))

(defthm ordered-formula-p1-implies-not-member-equal
  (implies (and (ordered-formula-p1 formula index)
                (>= j index))
           (not (member-equal j (strip-cars formula))))
  :hints (("Goal" :in-theory (enable ordered-formula-p1))))

(defthm ordered-formula-p1-implies-no-duplicatesp-equal
  (implies (ordered-formula-p1 formula index)
           (no-duplicatesp-equal (strip-cars formula)))
  :hints (("Goal" :in-theory (enable ordered-formula-p1))))

(defthm ordered-formula-p-implies-no-duplicatesp-equal-strip-cars
  (implies (ordered-formula-p formula)
           (no-duplicatesp-equal (strip-cars formula)))
  :hints (("Goal" :in-theory (enable ordered-formula-p)))
  :otf-flg t)

(defthm soundness-main-alt
  (implies
   (and (satisfiable formula)
        (formula-p formula)
        (a$p a$)
        (equal (a$ptr a$) 0)
        (integerp max-var)
        (<= (formula-max-var formula 0) max-var))
   (not (equal (car (incl-valid-proofp$-top-rec formula
                                                clrat-file posn chunk-size
                                                clrat-file-length
                                                old-suffix debug max-var a$ ctx
                                                state))
               :complete)))
	       :hints (("Goal" :by soundness-main)))

(defthm verify-for-cube-soundness-main
  (mv-let (ign formula/clause state)
    (verify-for-cube cnf-file clrat-file cube-file chunk-size debug ctx state)
    (declare (ignore ign state)) ; not mentioned below
    (implies formula/clause      ; no error
             (let ((formula (car formula/clause))
                   (clause (cdr formula/clause)))
               (and (clausep clause)
                    (ordered-formula-p formula)
                    (not (satisfiable (extend-formula-with-cube
                                       formula
; Clauses and cubes have the same format, so the following isn't really a type
; error.
                                       (negate-cube clause))))))))
  :hints
  (("Goal"
    :in-theory
    (union-theories
     '(verify-for-cube cube-valid-proofp$-top acl2::error1-logic clausep
                       conflicting-literalsp-negate-cube
                       unique-literalsp-negate-cube
                       ordered-formula-p
                       ordered-formula-p-implies-formula-p
                       formula-p-revappend
                       negate-cube-negate-cube
                       incl-valid-proofp$-top-aux
                       soundness-main-alt
                       natp-formula-max-var
                       lemma-1 lemma-2
                       formula-p-extend-formula-with-cube
                       formula-equiv-preserves-satisfiable
                       no-duplicatesp-equal-strip-cars-revappend
                       ordered-formula-p-implies-no-duplicatesp-equal-strip-cars
                       )
     (union-theories (executable-counterpart-theory :here)
                     (set-difference-equal (theory 'ground-zero)
                                           '(no-duplicatesp-equal))))))
  :rule-classes nil)
