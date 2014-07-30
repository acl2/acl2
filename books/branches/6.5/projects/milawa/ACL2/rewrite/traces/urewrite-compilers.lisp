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
(include-book "trace-okp")
(include-book "urewrite-if-lemmas")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)

(local (in-theory (enable rw.trace-conclusion-formula rw.trace-formula)))


(defund rw.compile-urewrite-if-specialcase-same-trace (x proofs)
  (declare (xargs :guard (and (rw.tracep x)
                              (rw.urewrite-if-specialcase-same-tracep x)
                              (logic.appeal-listp proofs)
                              (equal (logic.strip-conclusions proofs) (rw.trace-list-formulas (rw.trace->subtraces x))))
                  :verify-guards nil))
  (let* ((lhs (rw.trace->lhs x))   ;; (if a b c)
         (a   (first (logic.function-args lhs)))
         ;; This is sort of goofy.  Basically, our builder function is set up to handle assumptions
         ;; for the conditional rewriter.  But we don't use assumptions, so we need to fake having an
         ;; assumption about the condition.
         (test-proof (build.iff-reflexivity a))
         (then-proof (build.expansion (logic.pnot (logic.pequal (logic.function 'not (list a)) ''nil))
                                      (first proofs)))
         (else-proof (build.expansion (logic.pnot (logic.pequal a ''nil))
                                      (second proofs))))
    (if (rw.trace->iffp x)
        (rw.iff-of-if-x-y-y-bldr test-proof then-proof else-proof)
      (rw.equal-of-if-x-y-y-bldr test-proof then-proof else-proof))))

(defobligations rw.compile-urewrite-if-specialcase-same-trace
  (build.iff-reflexivity
   build.expansion
   rw.iff-of-if-x-y-y-bldr
   rw.equal-of-if-x-y-y-bldr))

(encapsulate
 ()
 (local (in-theory (enable rw.urewrite-if-specialcase-same-tracep rw.compile-urewrite-if-specialcase-same-trace)))

 (verify-guards rw.compile-urewrite-if-specialcase-same-trace)

 (defthm rw.compile-urewrite-if-specialcase-same-trace-under-iff
   (iff (rw.compile-urewrite-if-specialcase-same-trace x proofs)
        t)
   :hints(("Goal" :in-theory (disable (:executable-counterpart ACL2::force)))))

 (defthm logic.appealp-of-rw.compile-urewrite-if-specialcase-same-trace
   (implies (force (and (rw.urewrite-if-specialcase-same-tracep x)
                        (rw.tracep x)
                        (logic.appeal-listp proofs)
                        (equal (logic.strip-conclusions proofs) (rw.trace-list-formulas (rw.trace->subtraces x)))))
            (equal (logic.appealp (rw.compile-urewrite-if-specialcase-same-trace x proofs))
                   t)))

 (defthm logic.conclusion-of-rw.compile-urewrite-if-specialcase-same-trace
   (implies (force (and (rw.urewrite-if-specialcase-same-tracep x)
                        (rw.tracep x)
                        (logic.appeal-listp proofs)
                        (equal (logic.strip-conclusions proofs) (rw.trace-list-formulas (rw.trace->subtraces x)))))
            (equal (logic.conclusion (rw.compile-urewrite-if-specialcase-same-trace x proofs))
                   (rw.trace-formula x)))
   :rule-classes ((:rewrite :backchain-limit-lst 0)))

 (defthm@ logic.proofp-of-rw.compile-urewrite-if-specialcase-same-trace
   (implies (force (and (rw.urewrite-if-specialcase-same-tracep x)
                        (rw.tracep x)
                        (logic.appeal-listp proofs)
                        (equal (logic.strip-conclusions proofs) (rw.trace-list-formulas (rw.trace->subtraces x)))
                        ;; ---
                        (rw.trace-atblp x atbl)
                        (logic.proof-listp proofs axioms thms atbl)
                        (equal (cdr (lookup 'iff atbl)) 2)
                        (equal (cdr (lookup 'not atbl)) 1)
                        (@obligations rw.compile-urewrite-if-specialcase-same-trace)))
            (equal (logic.proofp (rw.compile-urewrite-if-specialcase-same-trace x proofs) axioms thms atbl)
                   t))))




(defund rw.compile-urewrite-if-generalcase-trace (x proofs)
  (declare (xargs :guard (and (rw.tracep x)
                              (rw.urewrite-if-generalcase-tracep x)
                              (logic.appeal-listp proofs)
                              (equal (logic.strip-conclusions proofs) (rw.trace-list-formulas (rw.trace->subtraces x))))
                  :verify-guards nil))
  (let* ((rhs        (rw.trace->rhs x))  ;; (if a2 b2 c2)
         (a2         (first (logic.function-args rhs)))
         (test-proof (first proofs))
         (then-proof (build.expansion (logic.pnot (logic.pequal (logic.function 'not (list a2)) ''nil))
                                      (second proofs)))
         (else-proof (build.expansion (logic.pnot (logic.pequal a2 ''nil))
                                      (third proofs))))
    (if (rw.trace->iffp x)
        (rw.iff-implies-iff-if-bldr test-proof then-proof else-proof)
      (rw.iff-implies-equal-if-bldr test-proof then-proof else-proof))))

(defobligations rw.compile-urewrite-if-generalcase-trace
  (build.expansion
   rw.iff-implies-iff-if-bldr
   rw.iff-implies-equal-if-bldr))

(encapsulate
 ()
 (local (in-theory (enable rw.urewrite-if-generalcase-tracep rw.compile-urewrite-if-generalcase-trace)))

 (verify-guards rw.compile-urewrite-if-generalcase-trace)

 (defthm rw.compile-urewrite-if-generalcase-trace-under-iff
   (iff (rw.compile-urewrite-if-generalcase-trace x proofs)
        t)
   :hints(("Goal" :in-theory (disable (:executable-counterpart ACL2::force)))))

 (defthm logic.appealp-of-rw.compile-urewrite-if-generalcase-trace
   (implies (force (and (rw.urewrite-if-generalcase-tracep x)
                        (rw.tracep x)
                        (logic.appeal-listp proofs)
                        (equal (logic.strip-conclusions proofs) (rw.trace-list-formulas (rw.trace->subtraces x)))))
            (equal (logic.appealp (rw.compile-urewrite-if-generalcase-trace x proofs))
                   t)))

 (defthm logic.conclusion-of-rw.compile-urewrite-if-generalcase-trace
   (implies (force (and (rw.urewrite-if-generalcase-tracep x)
                        (rw.tracep x)
                        (logic.appeal-listp proofs)
                        (equal (logic.strip-conclusions proofs) (rw.trace-list-formulas (rw.trace->subtraces x)))))
            (equal (logic.conclusion (rw.compile-urewrite-if-generalcase-trace x proofs))
                   (rw.trace-formula x)))
   :rule-classes ((:rewrite :backchain-limit-lst 0)))

 (defthm@ logic.proofp-of-rw.compile-urewrite-if-generalcase-trace
   (implies (force (and (rw.urewrite-if-generalcase-tracep x)
                        (rw.tracep x)
                        (logic.appeal-listp proofs)
                        (equal (logic.strip-conclusions proofs) (rw.trace-list-formulas (rw.trace->subtraces x)))
                        ;; ---
                        (rw.trace-atblp x atbl)
                        (logic.proof-listp proofs axioms thms atbl)
                        (equal (cdr (lookup 'not atbl)) 1)
                        (@obligations rw.compile-urewrite-if-generalcase-trace)))
            (equal (logic.proofp (rw.compile-urewrite-if-generalcase-trace x proofs) axioms thms atbl)
                   t))))



(defund@ rw.compile-urewrite-rule-trace (x)
  (declare (xargs :guard (and (rw.tracep x)
                              (rw.urewrite-rule-tracep x))
                  :verify-guards nil))
  (let* ((hypbox (rw.trace->hypbox x))
         (iffp   (rw.trace->iffp x))
         (extras (rw.trace->extras x))
         (rule   (first extras))
         (sigma  (second extras)))
    (let ((main-proof
           (cond ((and iffp (equal (rw.rule->equiv rule) 'equal))
                  ;; The rule uses equal, but we just want iff.
                  (@derive ((!= (equal rule-lhs rule-rhs) nil)  (build.theorem (clause.clause-formula (rw.rule-clause rule))))
                           ((= (equal rule-lhs rule-rhs) t)     (build.equal-t-from-not-nil @-))
                           ((= (equal lhs rhs) t)               (build.instantiation @- sigma))
                           ((= (iff lhs rhs) t)                 (build.iff-from-equal @-))))
                 (iffp
                  ;; The rule uses iff and we want iff.
                  (@derive ((!= (iff rule-lhs rule-rhs) nil)    (build.theorem (clause.clause-formula (rw.rule-clause rule))))
                           ((= (iff rule-lhs rule-rhs) t)       (build.iff-t-from-not-nil @-))
                           ((= (iff lhs rhs) t)                 (build.instantiation @- sigma))))
                 (t
                  ;; The rule uses equal and we want equal.
                  (@derive ((!= (equal rule-lhs rule-rhs) nil)  (build.theorem (clause.clause-formula (rw.rule-clause rule))))
                           ((= (equal rule-lhs rule-rhs) t)     (build.equal-t-from-not-nil @-))
                           ((= (equal lhs rhs) t)               (build.instantiation @- sigma)))))))
      (if (and (not (rw.hypbox->left hypbox))
               (not (rw.hypbox->right hypbox)))
          main-proof
        (build.expansion (rw.hypbox-formula hypbox) main-proof)))))

(defobligations rw.compile-urewrite-rule-trace
  (build.expansion
   build.instantiation
   build.iff-from-equal
   build.equal-t-from-not-nil
   build.iff-t-from-not-nil))

(encapsulate
 ()
 (local (in-theory (enable logic.term-formula
                           rw.rule-env-okp
                           rw.urewrite-rule-tracep
                           rw.urewrite-rule-trace-env-okp
                           rw.compile-urewrite-rule-trace)))

 (verify-guards rw.compile-urewrite-rule-trace)

 (defthm rw.compile-urewrite-rule-trace-under-iff
   (iff (rw.compile-urewrite-rule-trace x)
        t)
   :hints(("Goal" :in-theory (disable (:executable-counterpart ACL2::force)))))

 (defthm forcing-logic.appealp-of-rw.compile-urewrite-rule-trace
   (implies (force (and (rw.urewrite-rule-tracep x)
                        (rw.tracep x)))
            (equal (logic.appealp (rw.compile-urewrite-rule-trace x))
                   t)))

 (defthm forcing-logic.conclusion-of-rw.compile-urewrite-rule-trace
   (implies (force (and (rw.urewrite-rule-tracep x)
                        (rw.tracep x)))
            (equal (logic.conclusion (rw.compile-urewrite-rule-trace x))
                   (rw.trace-formula x))))

 (defthm@ forcing-logic.proofp-of-rw.compile-urewrite-rule-trace
   (implies (force (and (rw.urewrite-rule-trace-env-okp x thms atbl)
                        (rw.urewrite-rule-tracep x)
                        (rw.tracep x)
                        ;; ---
                        (rw.trace-atblp x atbl)
                        (equal (cdr (lookup 'iff atbl)) 2)
                        (equal (cdr (lookup 'equal atbl)) 2)
                        (@obligations rw.compile-urewrite-rule-trace)))
            (equal (logic.proofp (rw.compile-urewrite-rule-trace x) axioms thms atbl)
                   t))))

