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
(include-book "basic-recognizers")
(include-book "urewrite-recognizers")
(include-book "crewrite-recognizers")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


(defund rw.trace-step-okp (x defs)
  (declare (xargs :guard (and (rw.tracep x)
                              (definition-listp defs))))
  (let ((method (rw.trace->method x)))
    (cond ((equal method 'fail)                          (rw.fail-tracep x))
          ((equal method 'transitivity)                  (rw.transitivity-tracep x))
          ((equal method 'equiv-by-args)                 (rw.equiv-by-args-tracep x))
          ((equal method 'lambda-equiv-by-args)          (rw.lambda-equiv-by-args-tracep x))
          ((equal method 'beta-reduction)                (rw.beta-reduction-tracep x))
          ((equal method 'ground)                        (rw.ground-tracep x defs))
          ((equal method 'if-specialcase-nil)            (rw.if-specialcase-nil-tracep x))
          ((equal method 'if-specialcase-t)              (rw.if-specialcase-t-tracep x))
          ((equal method 'not)                           (rw.not-tracep x))
          ((equal method 'negative-if)                   (rw.negative-if-tracep x))
          ;; ---
          ((equal method 'urewrite-if-specialcase-same)  (rw.urewrite-if-specialcase-same-tracep x))
          ((equal method 'urewrite-if-generalcase)       (rw.urewrite-if-generalcase-tracep x))
          ((equal method 'urewrite-rule)                 (rw.urewrite-rule-tracep x))
          ;; ---
          ((equal method 'crewrite-if-specialcase-same)  (rw.crewrite-if-specialcase-same-tracep x))
          ((equal method 'crewrite-if-generalcase)       (rw.crewrite-if-generalcase-tracep x))
          ((equal method 'crewrite-rule)                 (rw.crewrite-rule-tracep x))
          ((equal method 'assumptions)                   (rw.assumptions-tracep x))
          ((equal method 'force)                         (rw.force-tracep x))
          ((equal method 'weakening)                     (rw.weakening-tracep x))
          (t nil))))

(defund rw.trace-step-env-okp (x defs thms atbl)
  (declare (xargs :guard (and (rw.tracep x)
                              (definition-listp defs)
                              (rw.trace-step-okp x defs)
                              (logic.formula-listp thms)
                              (logic.arity-tablep atbl))
                  :guard-hints (("Goal" :in-theory (enable rw.trace-step-okp))))
           (ignore defs))
  (let ((method (rw.trace->method x)))
    (cond ((equal method 'urewrite-rule)  (rw.urewrite-rule-trace-env-okp x thms atbl))
          ((equal method 'crewrite-rule)  (rw.crewrite-rule-trace-env-okp x thms atbl))
          (t t))))

(defthm booleanp-of-rw.trace-step-okp
  (equal (booleanp (rw.trace-step-okp x defs))
         t)
  :hints(("Goal" :in-theory (enable rw.trace-step-okp))))

(defthm booleanp-of-rw.trace-step-env-okp
  (equal (booleanp (rw.trace-step-env-okp x defs thms atbl))
         t)
  :hints(("Goal" :in-theory (enable rw.trace-step-env-okp))))



(defund rw.flag-trace-okp (flag x defs)
  (declare (xargs :guard (and (if (equal flag 'term)
                                  (rw.tracep x)
                                (rw.trace-listp x))
                              (definition-listp defs))
                  :measure (two-nats-measure (rank x) (if (equal flag 'term) 1 0))))
  (if (equal flag 'term)
      (and (rw.trace-step-okp x defs)
           (rw.flag-trace-okp 'list (rw.trace->subtraces x) defs))
    (if (consp x)
        (and (rw.flag-trace-okp 'term (car x) defs)
             (rw.flag-trace-okp 'list (cdr x) defs))
      t)))

(definlined rw.trace-okp (x defs)
  (declare (xargs :guard (and (rw.tracep x)
                              (definition-listp defs))))
  (rw.flag-trace-okp 'term x defs))

(definlined rw.trace-list-okp (x defs)
  (declare (xargs :guard (and (rw.trace-listp x)
                              (definition-listp defs))))
  (rw.flag-trace-okp 'list x defs))

(defthmd definition-of-rw.trace-okp
  (equal (rw.trace-okp x defs)
         (and (rw.trace-step-okp x defs)
              (rw.trace-list-okp (rw.trace->subtraces x) defs)))
  :rule-classes :definition
  :hints(("Goal" :in-theory (enable rw.trace-okp
                                    rw.trace-list-okp
                                    rw.flag-trace-okp))))

(defthmd definition-of-rw.trace-list-okp
  (equal (rw.trace-list-okp x defs)
         (if (consp x)
             (and (rw.trace-okp (car x) defs)
                  (rw.trace-list-okp (cdr x) defs))
           t))
  :rule-classes :definition
  :hints(("Goal" :in-theory (enable rw.trace-okp
                                    rw.trace-list-okp
                                    rw.flag-trace-okp))))


(ACL2::theory-invariant (not (ACL2::active-runep '(:definition rw.trace-okp))))
(ACL2::theory-invariant (not (ACL2::active-runep '(:definition rw.trace-list-okp))))

(defthm rw.trace-step-okp-of-nil
  (equal (rw.trace-step-okp nil defs)
         nil)
  :hints(("Goal" :in-theory (enable rw.trace-step-okp))))

(defthm rw.trace-okp-of-nil
  (equal (rw.trace-okp nil defs)
         nil)
  :hints(("Goal" :in-theory (enable definition-of-rw.trace-okp))))

(defthm rw.trace-list-okp-when-not-consp
  (implies (not (consp x))
           (equal (rw.trace-list-okp x defs)
                  t))
  :hints(("Goal" :in-theory (enable definition-of-rw.trace-list-okp))))

(defthm rw.trace-list-okp-of-cons
  (equal (rw.trace-list-okp (cons a x) defs)
         (and (rw.trace-okp a defs)
              (rw.trace-list-okp x defs)))
  :hints(("Goal" :in-theory (enable definition-of-rw.trace-list-okp))))

(defthms-flag
  :thms ((term booleanp-of-rw.trace-okp
               (equal (booleanp (rw.trace-okp x defs))
                      t))
         (t booleanp-of-rw.trace-list-okp
            (equal (booleanp (rw.trace-list-okp x defs))
                   t)))
  :hints(("Goal"
          :in-theory (enable definition-of-rw.trace-okp)
          :induct (rw.trace-induction flag x))))

(deflist rw.trace-list-okp (x defs)
  (rw.trace-okp x defs)
  :elementp-of-nil nil
  :already-definedp t)

(defthm rw.trace-step-okp-when-rw.trace-okp
  (implies (rw.trace-okp x defs)
           (equal (rw.trace-step-okp x defs)
                  t))
  :hints(("Goal" :in-theory (enable definition-of-rw.trace-okp))))

(defthm rw.trace-list-okp-of-rw.trace->subtraces-when-rw.trace-okp
  (implies (rw.trace-okp x defs)
           (equal (rw.trace-list-okp (rw.trace->subtraces x) defs)
                  t))
  :hints(("Goal" :in-theory (enable definition-of-rw.trace-okp))))





(defund rw.flag-trace-env-okp (flag x defs thms atbl)
  (declare (xargs :guard (and (definition-listp defs)
                              (if (equal flag 'term)
                                  (and (rw.tracep x)
                                       (rw.trace-okp x defs))
                                (and (rw.trace-listp x)
                                     (rw.trace-list-okp x defs)))
                              (logic.formula-listp thms)
                              (logic.arity-tablep atbl))
                  :measure (two-nats-measure (rank x) (if (equal flag 'term) 1 0))))
  (if (equal flag 'term)
      (and (rw.trace-step-env-okp x defs thms atbl)
           (rw.flag-trace-env-okp 'list (rw.trace->subtraces x) defs thms atbl))
    (if (consp x)
        (and (rw.flag-trace-env-okp 'term (car x) defs thms atbl)
             (rw.flag-trace-env-okp 'list (cdr x) defs thms atbl))
      t)))

(definlined rw.trace-env-okp (x defs thms atbl)
  (declare (xargs :guard (and (rw.tracep x)
                              (definition-listp defs)
                              (rw.trace-okp x defs)
                              (logic.formula-listp thms)
                              (logic.arity-tablep atbl))))
  (rw.flag-trace-env-okp 'term x defs thms atbl))

(definlined rw.trace-list-env-okp (x defs thms atbl)
  (declare (xargs :guard (and (rw.trace-listp x)
                              (definition-listp defs)
                              (rw.trace-list-okp x defs)
                              (logic.formula-listp thms)
                              (logic.arity-tablep atbl))
; Removed after v7-2 by Matt K. since the definition is non-recursive:
;                 :measure (two-nats-measure (rank x) 0)
                  ))
  (rw.flag-trace-env-okp 'list x defs thms atbl))

(defthmd definition-of-rw.trace-env-okp
  (equal (rw.trace-env-okp x defs thms atbl)
         (and (rw.trace-step-env-okp x defs thms atbl)
              (rw.trace-list-env-okp (rw.trace->subtraces x) defs thms atbl)))
  :rule-classes :definition
  :hints(("Goal" :in-theory (enable rw.flag-trace-env-okp
                                    rw.trace-env-okp
                                    rw.trace-list-env-okp))))

(defthmd definition-of-rw.trace-list-env-okp
  (equal (rw.trace-list-env-okp x defs thms atbl)
         (if (consp x)
             (and (rw.trace-env-okp (car x) defs thms atbl)
                  (rw.trace-list-env-okp (cdr x) defs thms atbl))
           t))
  :rule-classes :definition
  :hints(("Goal" :in-theory (enable rw.flag-trace-env-okp
                                    rw.trace-env-okp
                                    rw.trace-list-env-okp))))

(ACL2::theory-invariant (not (ACL2::active-runep '(:definition rw.trace-env-okp))))
(ACL2::theory-invariant (not (ACL2::active-runep '(:definition rw.trace-list-env-okp))))

(defthm rw.trace-list-env-okp-when-not-consp
  (implies (not (consp x))
           (equal (rw.trace-list-env-okp x defs thms atbl)
                  t))
  :hints(("Goal" :in-theory (enable definition-of-rw.trace-list-env-okp))))

(defthm rw.trace-list-env-okp-of-cons
  (equal (rw.trace-list-env-okp (cons a x) defs thms atbl)
         (and (rw.trace-env-okp a defs thms atbl)
              (rw.trace-list-env-okp x defs thms atbl)))
  :hints(("Goal" :in-theory (enable definition-of-rw.trace-list-env-okp))))

(defthms-flag
  :thms ((term booleanp-of-rw.trace-env-okp
                (equal (booleanp (rw.trace-env-okp x defs thms atbl))
                       t))
         (t booleanp-of-rw.trace-list-env-okp
            (equal (booleanp (rw.trace-list-env-okp x defs thms atbl))
                   t)))
  :hints (("Goal"
           :in-theory (enable definition-of-rw.trace-env-okp)
           :induct (rw.trace-induction flag x))))

(defthm rw.trace-step-env-okp-of-nil
  (equal (rw.trace-step-env-okp nil defs thms atbl)
         t)
  :hints(("Goal" :in-theory (enable rw.trace-step-env-okp))))

(defthm rw.trace-env-okp-of-nil
  (equal (rw.trace-env-okp nil defs thms atbl)
         t)
  :hints(("Goal" :in-theory (enable definition-of-rw.trace-env-okp))))

(deflist rw.trace-list-env-okp (x defs thms atbl)
  (rw.trace-env-okp x defs thms atbl)
  :elementp-of-nil t
  :already-definedp t)

(defthm rw.trace-step-env-okp-when-rw.trace-env-okp
  (implies (rw.trace-env-okp x defs thms atbl)
           (equal (rw.trace-step-env-okp x defs thms atbl)
                  t))
  :hints(("Goal" :in-theory (enable definition-of-rw.trace-env-okp))))

(defthm rw.trace-list-env-okp-of-rw.trace->subtraces-when-rw.trace-env-okp
  (implies (rw.trace-env-okp x defs thms atbl)
           (equal (rw.trace-list-env-okp (rw.trace->subtraces x) defs thms atbl)
                  t))
  :hints(("Goal" :in-theory (enable definition-of-rw.trace-env-okp))))

