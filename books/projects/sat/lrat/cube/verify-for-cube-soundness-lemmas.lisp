; Copyright (C) 2017, Regents of the University of Texas
; Marijn Heule, Warren A. Hunt, Jr., and Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; See cube.lisp.

; Originally, our development of verify-for-cube-soundness.lisp included some
; rather general lemmas.  We initially created the present book by moving those
; lemmas, along with some supporting definitions, into this book, so that they
; could be reused in development of the book
; verify-for-cube-soundness-main.lisp.

(in-package "LRAT")

(include-book "cube")

(defun falsify-clause (clause assignment)
  (cond ((atom clause) assignment)
        ((equal (evaluate-literal (car clause) assignment) 0)
         (falsify-clause (cdr clause)
                         (cons (negate (car clause)) assignment)))
        (t (falsify-clause (cdr clause) assignment))))

; Start proof of evaluate-clause-falsify-clause

(defthm falsify-clause-preserves-member
  (implies (member-equal lit assignment)
           (member-equal lit (falsify-clause clause assignment))))

(defthm member-falsify-clause
  (implies (and (literalp lit)
                (clause-or-assignment-p clause)
                (member-equal lit clause)
                (not (member-equal lit assignment)))
           (member-equal (negate lit)
                         (falsify-clause clause assignment))))

(defthm not-member-falsify-clause-1-1
  (implies (and (literalp lit)
                (clause-or-assignment-p clause))
           (implies (member-equal lit
                                  (falsify-clause clause assignment))
                    (or (member-equal (- lit) clause)
                        (member-equal lit assignment))))
  :rule-classes nil)

(defthm conflicting-literals-p-suff
  (implies (and (not (conflicting-literalsp clause))
                (literalp lit)
                (member lit clause))
           (not (member (negate lit) clause))))

(defthm not-member-falsify-clause-1
  (implies (and (literalp lit)
                (clause-or-assignment-p clause)
                (member-equal lit clause))
           (implies (member-equal lit
                                  (falsify-clause clause assignment))
                    (member-equal lit assignment)))
  :hints (("Goal"
           :use not-member-falsify-clause-1-1
           :do-not-induct t))
  :rule-classes nil)

(defthm not-member-falsify-clause
  (implies (and (literalp lit)
                (clause-or-assignment-p clause)
                (member-equal lit clause))
           (iff (member-equal lit
                              (falsify-clause clause assignment))
                (member-equal lit assignment)))
  :hints (("Goal" :use (not-member-falsify-clause-1
                        falsify-clause-preserves-member))))

(defthm evaluate-clause-falsify-clause
  (implies (and (subsetp-equal clause1 clause2)
                (clause-or-assignment-p clause1)
                (clause-or-assignment-p clause2)
                (not (equal (evaluate-clause clause1 assignment)
                            t)))
           (equal (evaluate-clause clause1 (falsify-clause clause2 assignment))
                  nil)))

(encapsulate
  ()
  (local (include-book "../list-based/truth-monotone"))
  (defthm truth-monotone
    (implies (and (subsetp-equal a1 a2)
                  (equal (formula-truep formula a1) t))
             (equal (formula-truep formula a2) t)))
  (defthm truth-monotone-alt
    (implies (and (formula-truep formula a1)
                  (subsetp-equal a1 a2))
             (equal (formula-truep formula a2) t))))

; Start proof of cube-soundness-2.

(defthm literal-listp-falsify-clause
  (implies (and (literal-listp clause)
                (literal-listp assignment))
           (literal-listp (falsify-clause clause assignment))))

(defthm unique-literalsp-falsify-clause
  (implies (unique-literalsp assignment)
           (unique-literalsp (falsify-clause clause assignment))))

(defthm not-conflicting-literalsp-falsify-clause
  (implies (and (literal-listp clause)
                (not (conflicting-literalsp assignment)))
           (not (conflicting-literalsp (falsify-clause clause assignment)))))

(defthm cons-preserves-subsetp
  (implies (subsetp-equal x y)
           (subsetp-equal x (cons a y))))

(defthm subsetp-x-x
  (subsetp-equal x x))

(defthm subset-equal-falsify-clause
  (subsetp-equal assignment
                 (falsify-clause clause assignment)))

(defun cube-to-formula (cube next-index)

; This variant of extend-formula-with-cube1 is useful for reasoning, below.

  (cond ((endp cube) nil)
        (t (acons next-index
                  (list (car cube))
                  (cube-to-formula
                   (cdr cube)
                   (1+ next-index))))))

(defthm extend-formula-with-cube1-rewrite
  (implies (and (clause-or-assignment-p cube)
                (posp next-index))
           (equal (extend-formula-with-cube1 formula cube next-index)
                  (revappend (cube-to-formula cube next-index) formula))))

(defthm hons-assoc-equal-revappend-1-1
  (implies (and (consp pair)
                (not (member-equal (car pair) (strip-cars x1)))
                (not (member-equal (car pair) (strip-cars x2))))
           (equal (hons-assoc-equal (car pair)
                                    (revappend x1 (append x2 (cons pair y))))
                  pair))
  :hints (("Goal" :induct (revappend x1 x2)))
  :rule-classes nil)

(defthm hons-assoc-equal-revappend-1
  (implies (and (consp pair)
                (not (member-equal (car pair) (strip-cars x))))
           (equal (hons-assoc-equal (car pair)
                                    (revappend x (cons pair y)))
                  pair))
  :hints (("Goal" :use (:instance hons-assoc-equal-revappend-1-1
                                  (x1 x) (x2 nil)))))

(defthm hons-assoc-equal-revappend
  (implies (no-duplicatesp (strip-cars x))
           (equal (hons-assoc-equal i (revappend x y))
                  (or (hons-assoc-equal i x)
                      (hons-assoc-equal i y)))))

(defthm hons-assoc-equal-cube-to-formula-implies-large-index
  (implies (and (natp next-index)
                (hons-assoc-equal i (cube-to-formula cube next-index)))
           (and (natp i)
                (>= i next-index)))
  :rule-classes nil)

(defthm hons-assoc-equal-formula-implies-small-index
  (implies (and (ordered-formula-p formula)
                (hons-assoc-equal i formula))
           (and (natp i)
                (<= i (formula-max-index formula))))
  :hints (("Goal" :in-theory (enable ordered-formula-p)))
  :rule-classes nil)

(defthm hons-assoc-equal-formula-implies-not-hons-assoc-equal-cube-to-formula
  (implies (and (ordered-formula-p formula)
                (hons-assoc-equal i formula))
           (not (hons-assoc-equal
                 i
                 (cube-to-formula cube
                                  (+ 1 (formula-max-index formula))))))
  :otf-flg t
  :hints (("Goal"
           :do-not-induct t
           :in-theory (disable ordered-formula-p-implies-formula-p)
           :use
           ((:instance hons-assoc-equal-cube-to-formula-implies-large-index
                       (next-index (+ 1 (formula-max-index formula))))
            hons-assoc-equal-formula-implies-small-index
            ordered-formula-p-implies-formula-p))))

(defthm no-duplicatesp-strip-cars-cube-to-formula-1
  (implies (< i j)
           (not (member-equal i (strip-cars (cube-to-formula cube j))))))

(defthm no-duplicatesp-strip-cars-cube-to-formula
  (implies (natp j)
           (no-duplicatesp-equal
            (strip-cars (cube-to-formula cube j)))))

(local (defthm ordered-formula-p-implies-formula-p-forward
         (implies (ordered-formula-p formula)
                  (formula-p formula))
         :rule-classes :forward-chaining))

(local (in-theory (disable ordered-formula-p-implies-formula-p)))

(in-theory (disable formula-max-index))

(defthm hons-assoc-equal-extend-formula-with-cube-1
  (implies (and (ordered-formula-p formula)
                (clause-or-assignment-p cube)
                (hons-assoc-equal i formula))
           (equal (hons-assoc-equal i
                                    (extend-formula-with-cube formula cube))
                  (hons-assoc-equal i formula)))
  :hints (("Goal" :in-theory (enable extend-formula-with-cube)))
  :rule-classes nil)

(defthm hons-assoc-equal-cube-to-formula-implies-member-equal
  (implies (and (literal-listp cube)
                (hons-assoc-equal i
                                  (cube-to-formula cube j)))
           (member-equal
            (cadr (hons-assoc-equal i (cube-to-formula cube j)))
            cube)))

(defthm not-cddr-hons-assoc-equal-cube-to-formula
  (not (cddr (hons-assoc-equal i (cube-to-formula cube j)))))

(defthm consp-cdr-hons-assoc-equal-cube-to-formula
  (implies (hons-assoc-equal i (cube-to-formula cube j))
           (consp (cdr (hons-assoc-equal i (cube-to-formula cube j))))))

(defthm hons-assoc-equal-extend-formula-with-cube-2
  (let ((pair (hons-assoc-equal i
                                (extend-formula-with-cube formula cube))))
    (implies (and (formula-p formula)
                  (clause-or-assignment-p cube)
                  pair
                  (not (hons-assoc-equal i formula)))
             (let ((clause (cdr pair)))
               (and (consp clause)
                    (null (cdr clause))
                    (member-equal (car clause) cube)))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (enable extend-formula-with-cube)))
  :otf-flg t
  :rule-classes nil)

(defthm literal-listp-negate-cube
  (implies (literal-listp x)
           (literal-listp (negate-cube x))))

(defthm member-equal-negate-cube
  (implies (literal-listp x)
           (iff (member-equal lit (negate-cube x))
                (member-equal (negate lit) x))))

(defthm conflicting-literalsp-negate-cube
  (implies (literal-listp x)
           (iff (conflicting-literalsp (negate-cube x))
                (conflicting-literalsp x))))

(defthm unique-literalsp-negate-cube
  (implies (literal-listp x)
           (equal (unique-literalsp (negate-cube x))
                  (unique-literalsp x))))

(defthm member-negate-implies-member-assignment
  (implies (and (equal (evaluate-clause clause assignment)
                       nil)
                (clause-or-assignment-p clause)
                (force (literalp lit))
                (member-equal (negate lit) clause))
           (member-equal lit assignment)))

(defthm formula-truep-extend-formula-with-cube

; There is lots of induction under forcing rounds; maybe a little work could
; eliminate that.

  (implies
   (and (ordered-formula-p formula)
        (clause-or-assignment-p clause)
        (clause-or-assignment-p assignment))
   (implies (and (formula-truep formula assignment)
                 (equal (evaluate-clause clause assignment)
                        nil))
            (formula-truep (extend-formula-with-cube formula
                                                     (negate-cube clause))
                           assignment)))
  :hints (("Goal"
           :use
           ((:instance
             hons-assoc-equal-extend-formula-with-cube-1
             (i (formula-truep-witness
                 (extend-formula-with-cube formula (negate-cube clause))
                 assignment))
             (cube (negate-cube clause)))
            (:instance
             hons-assoc-equal-extend-formula-with-cube-2
             (i (formula-truep-witness
                 (extend-formula-with-cube formula (negate-cube clause))
                 assignment))
             (cube (negate-cube clause))))
           :expand ((formula-truep
                     (extend-formula-with-cube formula (negate-cube clause))
                     assignment))
           :restrict ((formula-truep-necc
                       ((index
                         (formula-truep-witness
                          (extend-formula-with-cube formula (negate-cube clause))
                          assignment))))
                      (member-negate-implies-member-assignment
                       ((clause clause)))))))

