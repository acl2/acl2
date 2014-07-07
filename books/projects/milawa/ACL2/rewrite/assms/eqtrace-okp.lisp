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
(include-book "primary-eqtrace")
(include-book "secondary-eqtrace")
(include-book "transitivity-eqtraces")
(include-book "weakening-eqtrace")
(include-book "direct-iff-eqtrace")
(include-book "negative-iff-eqtrace")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)



(defund rw.eqtrace-step-okp (x box)
  (declare (xargs :guard (and (rw.eqtracep x)
                              (rw.hypboxp box))))
  (let ((method (rw.eqtrace->method x)))
    (cond ((equal method 'primary)      (rw.primary-eqtrace-okp x box))
          ((equal method 'secondary)    (rw.secondary-eqtrace-okp x box))
          ((equal method 'trans1)       (rw.trans1-eqtrace-okp x))
          ((equal method 'trans2)       (rw.trans2-eqtrace-okp x))
          ((equal method 'trans3)       (rw.trans3-eqtrace-okp x))
          ((equal method 'weakening)    (rw.weakening-eqtrace-okp x))
          ((equal method 'direct-iff)   (rw.direct-iff-eqtrace-okp x box))
          ((equal method 'negative-iff) (rw.negative-iff-eqtrace-okp x box))
          (t nil))))

(defthm booleanp-of-rw.eqtrace-step-okp
  (equal (booleanp (rw.eqtrace-step-okp x box))
         t)
  :hints(("Goal" :in-theory (enable rw.eqtrace-step-okp))))



(defun rw.flag-eqtrace-okp (flag x box)
  (declare (xargs :guard (if (equal flag 'trace)
                             (and (rw.eqtracep x)
                                  (rw.hypboxp box))
                           (and (equal flag 'list)
                                (rw.eqtrace-listp x)
                                (rw.hypboxp box)))
                  :measure (two-nats-measure (rank x) (if (equal flag 'trace) 1 0))))
  (if (equal flag 'trace)
      (and (rw.eqtrace-step-okp x box)
           (rw.flag-eqtrace-okp 'list (rw.eqtrace->subtraces x) box))
    (if (consp x)
        (and (rw.flag-eqtrace-okp 'trace (car x) box)
             (rw.flag-eqtrace-okp 'list (cdr x) box))
      t)))

(definlined rw.eqtrace-okp (x box)
  (declare (xargs :guard (and (rw.eqtracep x)
                              (rw.hypboxp box))))
  (rw.flag-eqtrace-okp 'trace x box))

(definlined rw.eqtrace-list-okp (x box)
  (declare (xargs :guard (and (rw.eqtrace-listp x)
                              (rw.hypboxp box))))
  (rw.flag-eqtrace-okp 'list x box))

(defthmd definition-of-rw.eqtrace-okp
  (equal (rw.eqtrace-okp x box)
         (and (rw.eqtrace-step-okp x box)
              (rw.eqtrace-list-okp (rw.eqtrace->subtraces x) box)))
  :rule-classes :definition
  :hints(("Goal" :in-theory (enable rw.eqtrace-okp rw.eqtrace-list-okp))))

(defthmd definition-of-rw.eqtrace-list-okp
  (equal (rw.eqtrace-list-okp x box)
         (if (consp x)
             (and (rw.eqtrace-okp (car x) box)
                  (rw.eqtrace-list-okp (cdr x) box))
           t))
  :rule-classes :definition
  :hints(("Goal" :in-theory (enable rw.eqtrace-okp rw.eqtrace-list-okp))))

(defthm rw.flag-eqtrace-okp-of-trace
  (equal (rw.flag-eqtrace-okp 'trace x box)
         (rw.eqtrace-okp x box))
  :hints(("Goal" :in-theory (enable rw.eqtrace-okp))))

(defthm rw.flag-eqtrace-okp-of-list
  (equal (rw.flag-eqtrace-okp 'list x box)
         (rw.eqtrace-list-okp x box))
  :hints(("Goal" :in-theory (enable rw.eqtrace-list-okp))))

(ACL2::theory-invariant (not (ACL2::active-runep '(:definition rw.eqtrace-okp))))
(ACL2::theory-invariant (not (ACL2::active-runep '(:definition rw.eqtrace-list-okp))))

(defthms-flag
  :thms ((trace booleanp-of-rw.eqtrace-okp
                (equal (booleanp (rw.eqtrace-okp x box))
                       t))
         (t booleanp-of-rw.eqtrace-list-okp
            (equal (booleanp (rw.eqtrace-list-okp x box))
                   t)))
  :hints (("Goal"
           :induct (rw.flag-eqtrace-okp flag x box)
           :in-theory (enable definition-of-rw.eqtrace-okp
                              definition-of-rw.eqtrace-list-okp))))

(defthm rw.eqtrace-list-okp-when-not-consp
  (implies (not (consp x))
           (equal (rw.eqtrace-list-okp x box)
                  t))
  :hints(("Goal" :in-theory (enable definition-of-rw.eqtrace-list-okp))))

(defthm rw.eqtrace-list-okp-of-cons
  (equal (rw.eqtrace-list-okp (cons a x) box)
         (and (rw.eqtrace-okp a box)
              (rw.eqtrace-list-okp x box)))
  :hints(("Goal" :in-theory (enable definition-of-rw.eqtrace-list-okp))))

(defthm rw.eqtrace-step-okp-of-nil
  (equal (rw.eqtrace-step-okp nil box)
         nil)
  :hints(("Goal" :in-theory (enable rw.eqtrace-step-okp))))

(defthm rw.eqtrace-okp-of-nil
  (equal (rw.eqtrace-okp nil box)
         nil)
  :hints(("Goal" :in-theory (enable definition-of-rw.eqtrace-okp))))

(deflist rw.eqtrace-list-okp (x box)
  (rw.eqtrace-okp x box)
  :elementp-of-nil nil
  :already-definedp t)

(defthm forcing-rw.eqtrace-list-okp-of-rw.eqtrace-subtraces
  (implies (force (rw.eqtrace-okp x box))
           (equal (rw.eqtrace-list-okp (rw.eqtrace->subtraces x) box)
                  t))
  :hints(("Goal" :in-theory (enable definition-of-rw.eqtrace-okp))))


(defthm rw.primary-eqtrace-okp-when-empty-box
  (implies (and (not (rw.hypbox->left box))
                (not (rw.hypbox->right box)))
           (equal (rw.primary-eqtrace-okp x box)
                  nil))
  :hints(("Goal" :in-theory (enable rw.primary-eqtrace-okp))))

(defthm rw.secondary-eqtrace-okp-when-empty-box
  (implies (and (not (rw.hypbox->left box))
                (not (rw.hypbox->right box)))
           (equal (rw.secondary-eqtrace-okp x box)
                  nil))
  :hints(("Goal" :in-theory (enable rw.secondary-eqtrace-okp))))



(defthms-flag
  :shared-hyp (and (not (rw.hypbox->left box))
                   (not (rw.hypbox->right box)))
  :thms ((trace rw.eqtrace-okp-when-empty-box
                (equal (rw.eqtrace-okp x box)
                       nil))
         (t rw.eqtrace-list-okp-when-empty-box
            (equal (rw.eqtrace-list-okp x box)
                   (not (consp x)))))
  :hints(("Goal"
          :induct (rw.flag-eqtrace-okp flag x box)
          :in-theory (enable definition-of-rw.eqtrace-okp
                             rw.eqtrace-step-okp
                             rw.trans1-eqtrace-okp
                             rw.trans2-eqtrace-okp
                             rw.trans3-eqtrace-okp
                             rw.weakening-eqtrace-okp
                             rw.direct-iff-eqtrace-okp
                             rw.negative-iff-eqtrace-okp
                             ))))


(encapsulate
 ()
 (local (in-theory (e/d (definition-of-rw.eqtrace-okp
                          rw.eqtrace-step-okp)
                        (forcing-rw.eqtrace-list-okp-of-rw.eqtrace-subtraces))))

 (defthm forcing-rw.eqtrace-okp-of-rw.primary-eqtrace
   (implies (force (and (rw.primary-eqtrace okp nhyp)
                        (or (memberp nhyp (rw.hypbox->left box))
                            (memberp nhyp (rw.hypbox->right box)))))
            (equal (rw.eqtrace-okp (rw.primary-eqtrace okp nhyp) box)
                   t)))

 (defthm forcing-rw.eqtrace-okp-of-rw.secondary-eqtrace
   (implies (force (and (rw.secondary-eqtrace okp nhyp)
                        (rw.hypboxp box)
                        (or (memberp nhyp (rw.hypbox->left box))
                            (memberp nhyp (rw.hypbox->right box)))))
            (equal (rw.eqtrace-okp (rw.secondary-eqtrace okp nhyp) box)
                   t)))

 (defthm forcing-rw.eqtrace-okp-of-rw.trans1-eqtrace
   (implies (force (and (rw.eqtrace-okp x box)
                        (rw.eqtrace-okp y box)
                        (equal (rw.eqtrace->rhs x) (rw.eqtrace->lhs y))
                        (implies (not iffp)
                                 (and (not (rw.eqtrace->iffp x))
                                      (not (rw.eqtrace->iffp y))))))
            (equal (rw.eqtrace-okp (rw.trans1-eqtrace iffp x y) box)
                   t)))

 (defthm forcing-rw.eqtrace-okp-of-rw.trans2-eqtrace
   (implies (force (and (rw.eqtrace-okp x box)
                        (rw.eqtrace-okp y box)
                        (equal (rw.eqtrace->lhs x) (rw.eqtrace->lhs y))
                        (implies (not iffp)
                                 (and (not (rw.eqtrace->iffp x))
                                      (not (rw.eqtrace->iffp y))))))
            (equal (rw.eqtrace-okp (rw.trans2-eqtrace iffp x y) box)
                   t)))

 (defthm forcing-rw.eqtrace-okp-of-rw.trans3-eqtrace
   (implies (force (and (rw.eqtrace-okp x box)
                        (rw.eqtrace-okp y box)
                        (equal (rw.eqtrace->rhs x) (rw.eqtrace->rhs y))
                        (implies (not iffp)
                                 (and (not (rw.eqtrace->iffp x))
                                      (not (rw.eqtrace->iffp y))))))
            (equal (rw.eqtrace-okp (rw.trans3-eqtrace iffp x y) box)
                   t)))

 (defthm forcing-rw.eqtrace-okp-of-rw.weakening-eqtrace
   (implies (force (and (rw.eqtrace-okp x box)
                        (rw.eqtracep x)))
            (equal (rw.eqtrace-okp (rw.weakening-eqtrace x) box)
                   t)))

 (defthm forcing-rw.eqtrace-okp-of-rw.direct-iff-eqtrace
   (implies (force (and (rw.direct-iff-eqtrace okp nhyp)
                        (or (memberp nhyp (rw.hypbox->left box))
                            (memberp nhyp (rw.hypbox->right box)))))
            (equal (rw.eqtrace-okp (rw.direct-iff-eqtrace okp nhyp) box)
                   t)))

 (defthm forcing-rw.eqtrace-okp-of-rw.negative-iff-eqtrace
   (implies (force (and (rw.negative-iff-eqtrace okp nhyp)
                        (rw.hypboxp box)
                        (or (memberp nhyp (rw.hypbox->left box))
                            (memberp nhyp (rw.hypbox->right box)))))
            (equal (rw.eqtrace-okp (rw.negative-iff-eqtrace okp nhyp) box)
                   t))))





(defund rw.eqtrace-formula (x box)
  (declare (xargs :guard (and (rw.eqtracep x)
                              (rw.hypboxp box)
                              (rw.eqtrace-okp x box))))
  (logic.por (rw.hypbox-formula box)
             (logic.pequal (logic.function (if (rw.eqtrace->iffp x) 'iff 'equal)
                                           (list (rw.eqtrace->lhs x)
                                                 (rw.eqtrace->rhs x)))
                           ''t)))

(defthm forcing-logic.formulap-of-rw.eqtrace-formula
  (implies (and (rw.eqtracep x)
                (rw.hypboxp box)
                (rw.eqtrace-okp x box))
           (equal (logic.formulap (rw.eqtrace-formula x box))
                  t))
  :hints(("Goal" :in-theory (enable rw.eqtrace-formula))))

(defthm forcing-logic.formula-atblp-of-rw.eqtrace-formula
  (implies (and (rw.eqtrace-atblp x atbl)
                (rw.hypboxp box)
                (rw.hypbox-atblp box atbl)
                (rw.eqtrace-okp x box)
                (equal (cdr (lookup 'iff atbl)) 2)
                (equal (cdr (lookup 'equal atbl)) 2))
           (equal (logic.formula-atblp (rw.eqtrace-formula x box) atbl)
                  t))
  :hints(("Goal" :in-theory (enable rw.eqtrace-formula))))

(defprojection
  :list (rw.eqtrace-formula-list x box)
  :element (rw.eqtrace-formula x box)
  :guard (and (rw.eqtrace-listp x)
              (rw.hypboxp box)
              (rw.eqtrace-list-okp x box)))

(defthm forcing-logic.formula-listp-of-rw.eqtrace-formula-list
  (implies (and (rw.eqtrace-listp x)
                (rw.hypboxp box)
                (rw.eqtrace-list-okp x box))
           (equal (logic.formula-listp (rw.eqtrace-formula-list x box))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm forcing-logic.formula-list-atblp-of-rw.eqtrace-formula
  (implies (and (rw.eqtrace-list-atblp x atbl)
                (rw.hypboxp box)
                (rw.hypbox-atblp box atbl)
                (rw.eqtrace-list-okp x box)
                (equal (cdr (lookup 'iff atbl)) 2)
                (equal (cdr (lookup 'equal atbl)) 2))
           (equal (logic.formula-list-atblp (rw.eqtrace-formula-list x box) atbl)
                  t))
  :hints(("Goal" :in-theory (enable rw.eqtrace-formula-list))))

