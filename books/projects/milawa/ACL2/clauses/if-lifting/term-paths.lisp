; Milawa - A Reflective Theorem Prover
; Copyright (C) 2005-2009 Kookamara LLC
;
; Contact:
;
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759, USA
;   http://www.kookamara.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Jared Davis <jared@kookamara.com>

(in-package "MILAWA")
(include-book "term-tests")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)



;; (clause.term-paths x)
;;
;; We walk down the term and create lists of all the if expressions we
;; encounter along the way.  I.e., these paths show you each set of choices you
;; would need to make in order to get to every tip of a term.

(defund clause.flag-term-paths (flag x)
  (declare (xargs :guard (if (equal flag 'term)
                             (logic.termp x)
                           (logic.term-listp x))))
  (if (equal flag 'term)
      (cond ((logic.constantp x) nil)
            ((logic.variablep x) nil)
            ((logic.functionp x)
             (let ((name (logic.function-name x))
                   (args (logic.function-args x)))
               (if (and (equal name 'if)
                        (equal (len args) 3))
                   (let ((paths (app (clause.flag-term-paths 'term (first args))
                                     (app (clause.flag-term-paths 'term (second args))
                                          (clause.flag-term-paths 'term (third args))))))
                     (if paths
                         (multicons (first args) paths)
                       (list (list (first args)))))
                 (clause.flag-term-paths 'list (logic.function-args x)))))
            ((logic.lambdap x)
             (clause.flag-term-paths 'list (logic.lambda-actuals x)))
            (t nil))
    (if (consp x)
        (app (clause.flag-term-paths 'term (car x))
             (clause.flag-term-paths 'list (cdr x)))
      nil)))

(defund clause.term-paths (x)
  (declare (xargs :guard (logic.termp x)))
  (clause.flag-term-paths 'term x))

(defund clause.term-paths-list (x)
  (declare (xargs :guard (logic.term-listp x)))
  (clause.flag-term-paths 'list x))

(defthmd definition-of-clause.term-paths
  (equal (clause.term-paths x)
         (cond ((logic.constantp x) nil)
               ((logic.variablep x) nil)
               ((logic.functionp x)
                (let ((name (logic.function-name x))
                      (args (logic.function-args x)))
                  (if (and (equal name 'if)
                           (equal (len args) 3))
                      (let ((paths (app (clause.term-paths (first args))
                                        (app (clause.term-paths (second args))
                                             (clause.term-paths (third args))))))
                        (if paths
                            (multicons (first args) paths)
                          (list (list (first args)))))
                    (clause.term-paths-list (logic.function-args x)))))
               ((logic.lambdap x)
                (clause.term-paths-list (logic.lambda-actuals x)))
               (t nil)))
  :rule-classes :definition
  :hints(("Goal" :in-theory (enable clause.term-paths
                                    clause.flag-term-paths
                                    clause.term-paths-list))))

(defthmd definition-of-clause.term-paths-list
  (equal (clause.term-paths-list x)
         (if (consp x)
             (app (clause.term-paths (car x))
                  (clause.term-paths-list (cdr x)))
           nil))
  :rule-classes :definition
  :hints(("Goal" :in-theory (enable clause.term-paths
                                    clause.flag-term-paths
                                    clause.term-paths-list))))

(defthm clause.flag-term-paths-of-term-removal
  (equal (clause.flag-term-paths 'term x)
         (clause.term-paths x))
  :hints(("Goal" :in-theory (enable clause.term-paths))))

(defthm clause.flag-term-paths-of-list-removal
  (equal (clause.flag-term-paths 'list x)
         (clause.term-paths-list x))
  :hints(("Goal" :in-theory (enable clause.term-paths-list))))

(ACL2::theory-invariant (not (ACL2::active-runep '(:definition clause.term-paths))))
(ACL2::theory-invariant (not (ACL2::active-runep '(:definition clause.term-paths-list))))
(ACL2::theory-invariant (not (ACL2::active-runep '(:definition clause.flag-term-paths))))

(defthm clause.term-paths-when-logic.constantp
  (implies (logic.constantp x)
           (equal (clause.term-paths x)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :in-theory (enable definition-of-clause.term-paths))))

(defthm clause.term-paths-when-logic.variablep
  (implies (logic.variablep x)
           (equal (clause.term-paths x)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :in-theory (enable definition-of-clause.term-paths))))

(defthm clause.term-paths-when-non-if-logic.functionp
  (implies (and (not (equal 'if (logic.function-name x)))
                (logic.functionp x))
           (equal (clause.term-paths x)
                  (clause.term-paths-list (logic.function-args x))))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :in-theory (enable definition-of-clause.term-paths))))

(defthm clause.term-paths-when-bad-args-logic.functionp
  (implies (and (not (equal 3 (len (logic.function-args x))))
                (logic.functionp x))
           (equal (clause.term-paths x)
                  (clause.term-paths-list (logic.function-args x))))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :in-theory (enable definition-of-clause.term-paths))))

(defthm clause.term-paths-when-if-logic.functionp
  (implies (and (equal 'if (logic.function-name x))
                (equal 3 (len (logic.function-args x)))
                (logic.functionp x))
           (equal (clause.term-paths x)
                  (let ((paths (app (clause.term-paths (first (logic.function-args x)))
                                    (app (clause.term-paths (second (logic.function-args x)))
                                         (clause.term-paths (third (logic.function-args x)))))))
                    (if paths
                        (multicons (first (logic.function-args x)) paths)
                      (list (list (first (logic.function-args x))))))))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :in-theory (enable definition-of-clause.term-paths))))

(defthm clause.term-paths-when-logic.lambdap
  (implies (logic.lambdap x)
           (equal (clause.term-paths x)
                  (clause.term-paths-list (logic.lambda-actuals x))))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :in-theory (enable definition-of-clause.term-paths))))

(defthm clause.term-paths-when-degenerate
  (implies (and (not (logic.variablep x))
                (not (logic.constantp x))
                (not (logic.functionp x))
                (not (logic.lambdap x)))
           (equal (clause.term-paths x)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :in-theory (enable definition-of-clause.term-paths))))

(defthm clause.term-paths-list-when-not-consp
  (implies (not (consp x))
           (equal (clause.term-paths-list x)
                  nil))
  :hints(("Goal" :in-theory (enable definition-of-clause.term-paths-list))))

(defthm clause.term-paths-list-of-cons
  (equal (clause.term-paths-list (cons a x))
         (app (clause.term-paths a)
              (clause.term-paths-list x)))
  :hints(("Goal" :in-theory (enable definition-of-clause.term-paths-list))))

(defthm clause.term-paths-list-when-len-three
  (implies (equal (len x) 3)
           (equal (clause.term-paths-list x)
                  (app (clause.term-paths (first x))
                       (app (clause.term-paths (second x))
                            (clause.term-paths (third x)))))))

(defthms-flag
  :thms ((term clause.term-paths-when-clause.simple-termp
               (implies (clause.simple-termp x)
                        (equal (clause.term-paths x)
                               nil)))
         (t clause.term-paths-list-when-clause.simple-term-listp
            (implies (clause.simple-term-listp x)
                     (equal (clause.term-paths-list x)
                            nil))))
  :hints (("Goal" :induct (clause.simple-term-induction flag x))))

(defthms-flag
  :thms ((term forcing-logic.term-list-listp-of-clause.term-paths
               (implies (force (logic.termp x))
                        (equal (logic.term-list-listp (clause.term-paths x))
                               t)))
         (t forcing-logic.term-list-listp-of-clause.term-paths-list
            (implies (force (logic.term-listp x))
                     (equal (logic.term-list-listp (clause.term-paths-list x))
                            t))))
  :hints (("Goal" :induct (clause.simple-term-induction flag x))))

(defthms-flag
  :thms ((term forcing-consp-of-clause.term-paths
               (implies (force (logic.termp x))
                        (equal (consp (clause.term-paths x))
                               (not (clause.simple-termp x)))))
         (t forcing-consp-of-clause.term-paths-list
            (implies (force (logic.term-listp x))
                     (equal (consp (clause.term-paths-list x))
                            (not (clause.simple-term-listp x))))))
  :hints (("Goal" :induct (clause.simple-term-induction flag x))))

(defthm disjoint-from-nonep-of-clause.term-paths-when-memberp
  (implies (and (disjoint-from-nonep domain (clause.term-paths-list x))
                (memberp a x))
           (equal (disjoint-from-nonep domain (clause.term-paths a))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthms-flag
  :thms ((term disjoint-from-nonep-of-clause.simple-tests-and-clause.term-paths
               (implies (force (logic.termp x))
                        (equal (disjoint-from-nonep (clause.simple-tests x) (clause.term-paths x))
                               t)))
         (t disjoint-from-nonep-of-clause.simple-tests-list-and-clause.term-paths-list
            (implies (force (logic.term-listp x))
                     (equal (disjoint-from-nonep (clause.simple-tests-list x)
                                                 (clause.term-paths-list x))
                            t))))
  :hints (("Goal" :induct (clause.simple-term-induction flag x))))

