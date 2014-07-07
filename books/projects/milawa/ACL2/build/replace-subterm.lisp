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
(include-book "lambda")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)

(defun build.flag-replace-subterm (flag x old new proof)
  (declare (xargs :guard (and (if (equal flag 'term)
                                  (logic.termp x)
                                (and (equal flag 'list)
                                     (logic.term-listp x)))
                              (logic.termp old)
                              (logic.termp new)
                              (logic.appealp proof)
                              (equal (logic.conclusion proof) (logic.pequal old new)))
                  :verify-guards nil))
  (if (equal flag 'term)
      (cond ((equal x old)
             (logic.appeal-identity proof))
            ((logic.constantp x)
             (build.reflexivity x))
            ((logic.variablep x)
             (build.reflexivity x))
            ((logic.functionp x)
             (let* ((name       (logic.function-name x))
                    (args       (logic.function-args x))
                    (arg-proofs (build.flag-replace-subterm 'list args old new proof)))
               (build.pequal-by-args name arg-proofs)))
            ((logic.lambdap x)
             (let* ((formals       (logic.lambda-formals x))
                    (body          (logic.lambda-body x))
                    (actuals       (logic.lambda-actuals x))
                    (actual-proofs (build.flag-replace-subterm 'list actuals old new proof)))
               (build.lambda-pequal-by-args formals body actual-proofs)))
            ;; Sneaky twiddle for hypless iff theorem
            (t t))
    (if (consp x)
        (cons (build.flag-replace-subterm 'term (car x) old new proof)
              (build.flag-replace-subterm 'list (cdr x) old new proof))
      nil)))

(definlined build.replace-subterm (x old new proof)
  (declare (xargs :guard (and (logic.termp x)
                              (logic.termp old)
                              (logic.termp new)
                              (logic.appealp proof)
                              (equal (logic.conclusion proof) (logic.pequal old new)))
                  :verify-guards nil))
  (build.flag-replace-subterm 'term x old new proof))

(definlined build.replace-subterm-list (x old new proof)
  (declare (xargs :guard (and (logic.term-listp x)
                              (logic.termp old)
                              (logic.termp new)
                              (logic.appealp proof)
                              (equal (logic.conclusion proof) (logic.pequal old new)))
                  :verify-guards nil))
  (build.flag-replace-subterm 'list x old new proof))

(defobligations build.flag-replace-subterm
  (logic.appeal-identity
   build.reflexivity
   build.pequal-by-args
   build.lambda-pequal-by-args))

(defobligations build.replace-subterm
  (build.flag-replace-subterm))

(defobligations build.replace-subterm-list
  (build.flag-replace-subterm))

(defthmd definition-of-build.replace-subterm
  (equal (build.replace-subterm x old new proof)
         (cond ((equal x old)
                (logic.appeal-identity proof))
               ((logic.constantp x)
                (build.reflexivity x))
               ((logic.variablep x)
                (build.reflexivity x))
               ((logic.functionp x)
                (let* ((name       (logic.function-name x))
                       (args       (logic.function-args x))
                       (arg-proofs (build.replace-subterm-list args old new proof)))
                  (build.pequal-by-args name arg-proofs)))
               ((logic.lambdap x)
                (let* ((formals       (logic.lambda-formals x))
                       (body          (logic.lambda-body x))
                       (actuals       (logic.lambda-actuals x))
                       (actual-proofs (build.replace-subterm-list actuals old new proof)))
                  (build.lambda-pequal-by-args formals body actual-proofs)))
               ;; Sneaky twiddle for hypless iff theorem
               (t t)))
  :rule-classes :definition
  :hints(("Goal" :in-theory (enable build.replace-subterm build.replace-subterm-list))))

(defthmd definition-of-build.replace-subterm-list
  (equal (build.replace-subterm-list x old new proof)
         (if (consp x)
             (cons (build.replace-subterm (car x) old new proof)
                   (build.replace-subterm-list (cdr x) old new proof))
           nil))
  :rule-classes :definition
  :hints(("Goal" :in-theory (enable build.replace-subterm build.replace-subterm-list))))

(defthm build.flag-replace-subterm-of-term
  (equal (build.flag-replace-subterm 'term x old new proof)
         (build.replace-subterm x old new proof))
  :hints(("Goal" :in-theory (enable build.replace-subterm))))

(defthm build.flag-replace-subterm-of-list
  (equal (build.flag-replace-subterm 'list x old new proof)
         (build.replace-subterm-list x old new proof))
  :hints(("Goal" :in-theory (enable build.replace-subterm-list))))

(ACL2::theory-invariant (not (ACL2::active-runep '(:definition build.replace-subterm))))
(ACL2::theory-invariant (not (ACL2::active-runep '(:definition build.replace-subterm-list))))

(encapsulate
 ()
 (defthm build.replace-subterm-list-when-not-consp
   (implies (not (consp x))
            (equal (build.replace-subterm-list x old new proof)
                   nil))
   :hints(("Goal" :in-theory (enable definition-of-build.replace-subterm-list))))

 (defthm build.replace-subterm-list-of-cons
   (equal (build.replace-subterm-list (cons a x) old new proof)
          (cons (build.replace-subterm a old new proof)
                (build.replace-subterm-list x old new proof)))
   :hints(("Goal" :in-theory (enable definition-of-build.replace-subterm-list))))

 (defprojection
   :list (build.replace-subterm-list x old new proof)
   :element (build.replace-subterm x old new proof)
   :already-definedp t))

(encapsulate
 ()
 (local (defthm lemma
          (if (equal flag 'term)
              (implies (and (logic.termp x)
                            (logic.termp old)
                            (logic.termp new)
                            (logic.appealp proof)
                            (equal (logic.conclusion proof) (logic.pequal old new)))
                       (and (logic.appealp (build.replace-subterm x old new proof))
                            (equal (logic.conclusion (build.replace-subterm x old new proof))
                                   (logic.pequal x (logic.replace-subterm x old new)))))
            (implies (and (logic.term-listp x)
                          (logic.termp old)
                          (logic.termp new)
                          (logic.appealp proof)
                          (equal (logic.conclusion proof) (logic.pequal old new)))
                     (and (logic.appeal-listp (build.replace-subterm-list x old new proof))
                          (equal (logic.strip-conclusions (build.replace-subterm-list x old new proof))
                                 (logic.pequal-list x (logic.replace-subterm-list x old new))))))
          :rule-classes nil
          :hints(("Goal"
                  :expand ((build.replace-subterm x old new proof)
                           (build.replace-subterm old old new proof)
                           (logic.replace-subterm x old new)
                           (logic.replace-subterm old old new))
                  ;; :restrict ((forcing-lookup-of-logic.function-name ((atbl atbl))))
                  :induct (build.flag-replace-subterm flag x old new proof)))))

 (defthm forcing-logic.appealp-of-build.replace-subterm
   (implies (force (and (logic.termp x)
                        (logic.termp old)
                        (logic.termp new)
                        (logic.appealp proof)
                        (equal (logic.conclusion proof) (logic.pequal old new))))
            (equal (logic.appealp (build.replace-subterm x old new proof))
                   t))
   :hints(("Goal" :use ((:instance lemma (flag 'term))))))

 (defthm forcing-logic.conclusion-of-build.replace-subterm
   (implies (force (and (logic.termp x)
                        (logic.termp old)
                        (logic.termp new)
                        (logic.appealp proof)
                        (equal (logic.conclusion proof) (logic.pequal old new))))
            (equal (logic.conclusion (build.replace-subterm x old new proof))
                   (logic.pequal x (logic.replace-subterm x old new))))
   :rule-classes ((:rewrite :backchain-limit-lst 0))
   :hints(("Goal" :use ((:instance lemma (flag 'term))))))

 (defthm forcing-logic.appeal-listp-of-build.replace-subterm-list
   (implies (force (and (logic.term-listp x)
                        (logic.termp old)
                        (logic.termp new)
                        (logic.appealp proof)
                        (equal (logic.conclusion proof) (logic.pequal old new))))
            (equal (logic.appeal-listp (build.replace-subterm-list x old new proof))
                   t))
   :hints(("Goal" :use ((:instance lemma (flag 'list))))))

 (defthm forcing-logic.strip-conclusions-of-build.replace-subterm-list
   (implies (force (and (logic.term-listp x)
                        (logic.termp old)
                        (logic.termp new)
                        (logic.appealp proof)
                        (equal (logic.conclusion proof) (logic.pequal old new))))
            (equal (logic.strip-conclusions (build.replace-subterm-list x old new proof))
                   (logic.pequal-list x (logic.replace-subterm-list x old new))))
   :rule-classes ((:rewrite :backchain-limit-lst 0))
   :hints(("Goal" :use ((:instance lemma (flag 'list)))))))

(encapsulate
 ()
 (local (defthm@ lemma
          (if (equal flag 'term)
              (implies (and (logic.termp x)
                            (logic.termp old)
                            (logic.termp new)
                            (logic.appealp proof)
                            (equal (logic.conclusion proof) (logic.pequal old new))
                            ;; ---
                            (logic.term-atblp x atbl)
                            (logic.proofp proof axioms thms atbl)
                            (@obligations build.replace-subterm))
                       (logic.proofp (build.replace-subterm x old new proof) axioms thms atbl))
            (implies (and (logic.term-listp x)
                          (logic.termp old)
                          (logic.termp new)
                          (logic.appealp proof)
                          (equal (logic.conclusion proof) (logic.pequal old new))
                          ;; ---
                          (logic.term-list-atblp x atbl)
                          (logic.proofp proof axioms thms atbl)
                          (@obligations build.replace-subterm-list))
                     (logic.proof-listp (build.replace-subterm-list x old new proof) axioms thms atbl)))
          :rule-classes nil
          :hints(("Goal"
                  :expand ((build.replace-subterm x old new proof)
                           (build.replace-subterm old old new proof))
                  ;; :restrict ((forcing-lookup-of-logic.function-name ((atbl atbl))))
                  :induct (build.flag-replace-subterm flag x old new proof)))))

 (defthm@ forcing-logic.proofp-of-build.replace-subterm
   (implies (force (and (logic.termp x)
                        (logic.termp old)
                        (logic.termp new)
                        (logic.appealp proof)
                        (equal (logic.conclusion proof) (logic.pequal old new))
                        ;; ---
                        (logic.term-atblp x atbl)
                        (logic.proofp proof axioms thms atbl)
                        (@obligations build.replace-subterm)))
            (equal (logic.proofp (build.replace-subterm x old new proof) axioms thms atbl)
                   t))
   :hints(("Goal" :use ((:instance lemma (flag 'term))))))

 (defthm@ forcing-logic.proof-listp-of-build.replace-subterm-list
   (implies (force (and (logic.term-listp x)
                        (logic.termp old)
                        (logic.termp new)
                        (logic.appealp proof)
                        (equal (logic.conclusion proof) (logic.pequal old new))
                        ;; ---
                        (logic.term-list-atblp x atbl)
                        (logic.proofp proof axioms thms atbl)
                        (@obligations build.replace-subterm-list)))
            (equal (logic.proof-listp (build.replace-subterm-list x old new proof) axioms thms atbl)
                   t))
   :hints(("Goal" :use ((:instance lemma (flag 'list)))))))

(verify-guards build.flag-replace-subterm)
(verify-guards build.replace-subterm)
(verify-guards build.replace-subterm-list)






(defun build.flag-disjoined-replace-subterm (flag x old new proof)
  (declare (xargs :guard (and (if (equal flag 'term)
                                  (logic.termp x)
                                (and (equal flag 'list)
                                     (logic.term-listp x)))
                              (logic.termp old)
                              (logic.termp new)
                              (logic.appealp proof)
                              (equal (logic.fmtype (logic.conclusion proof)) 'por*)
                              (equal (logic.vrhs (logic.conclusion proof)) (logic.pequal old new)))
                  :verify-guards nil))
  (if (equal flag 'term)
      (cond ((equal x old)
             (logic.appeal-identity proof))
            ((logic.constantp x)
             (build.expansion (logic.vlhs (logic.conclusion proof))
                              (build.reflexivity x)))
            ((logic.variablep x)
             (build.expansion (logic.vlhs (logic.conclusion proof))
                              (build.reflexivity x)))
            ((logic.functionp x)
             (let* ((name       (logic.function-name x))
                    (args       (logic.function-args x))
                    (arg-proofs (build.flag-disjoined-replace-subterm 'list args old new proof)))
               (build.disjoined-pequal-by-args name (logic.vlhs (logic.conclusion proof)) arg-proofs)))
            ((logic.lambdap x)
             (let* ((formals       (logic.lambda-formals x))
                    (body          (logic.lambda-body x))
                    (actuals       (logic.lambda-actuals x))
                    (actual-proofs (build.flag-disjoined-replace-subterm 'list actuals old new proof)))
               (build.disjoined-lambda-pequal-by-args formals body (logic.vlhs (logic.conclusion proof)) actual-proofs)))
            ;; Sneaky twiddle for hypless iff theorem
            (t t))
    (if (consp x)
        (cons (build.flag-disjoined-replace-subterm 'term (car x) old new proof)
              (build.flag-disjoined-replace-subterm 'list (cdr x) old new proof))
      nil)))

(definlined build.disjoined-replace-subterm (x old new proof)
  (declare (xargs :guard (and (logic.termp x)
                              (logic.termp old)
                              (logic.termp new)
                              (logic.appealp proof)
                              (equal (logic.fmtype (logic.conclusion proof)) 'por*)
                              (equal (logic.vrhs (logic.conclusion proof)) (logic.pequal old new)))
                  :verify-guards nil))
  (build.flag-disjoined-replace-subterm 'term x old new proof))

(definlined build.disjoined-replace-subterm-list (x old new proof)
  (declare (xargs :guard (and (logic.term-listp x)
                              (logic.termp old)
                              (logic.termp new)
                              (logic.appealp proof)
                              (equal (logic.fmtype (logic.conclusion proof)) 'por*)
                              (equal (logic.vrhs (logic.conclusion proof)) (logic.pequal old new)))
                  :verify-guards nil))
  (build.flag-disjoined-replace-subterm 'list x old new proof))

(defobligations build.flag-disjoined-replace-subterm
  (logic.appeal-identity
   build.reflexivity
   build.expansion
   build.disjoined-pequal-by-args
   build.disjoined-lambda-pequal-by-args))

(defobligations build.disjoined-replace-subterm
  (build.flag-disjoined-replace-subterm))

(defobligations build.disjoined-replace-subterm-list
  (build.flag-disjoined-replace-subterm))

(defthmd definition-of-build.disjoined-replace-subterm
  (equal (build.disjoined-replace-subterm x old new proof)
         (cond ((equal x old)
                (logic.appeal-identity proof))
               ((logic.constantp x)
                (build.expansion (logic.vlhs (logic.conclusion proof))
                                 (build.reflexivity x)))
               ((logic.variablep x)
                (build.expansion (logic.vlhs (logic.conclusion proof))
                                 (build.reflexivity x)))
               ((logic.functionp x)
                (let* ((name       (logic.function-name x))
                       (args       (logic.function-args x))
                       (arg-proofs (build.disjoined-replace-subterm-list args old new proof)))
                  (build.disjoined-pequal-by-args name (logic.vlhs (logic.conclusion proof)) arg-proofs)))
               ((logic.lambdap x)
                (let* ((formals       (logic.lambda-formals x))
                       (body          (logic.lambda-body x))
                       (actuals       (logic.lambda-actuals x))
                       (actual-proofs (build.disjoined-replace-subterm-list actuals old new proof)))
                  (build.disjoined-lambda-pequal-by-args formals body (logic.vlhs (logic.conclusion proof)) actual-proofs)))
               ;; Sneaky twiddle for hypless iff theorem
               (t t)))
  :rule-classes :definition
  :hints(("Goal" :in-theory (enable build.disjoined-replace-subterm build.disjoined-replace-subterm-list))))

(defthmd definition-of-build.disjoined-replace-subterm-list
  (equal (build.disjoined-replace-subterm-list x old new proof)
         (if (consp x)
             (cons (build.disjoined-replace-subterm (car x) old new proof)
                   (build.disjoined-replace-subterm-list (cdr x) old new proof))
           nil))
  :rule-classes :definition
  :hints(("Goal" :in-theory (enable build.disjoined-replace-subterm build.disjoined-replace-subterm-list))))

(defthm build.flag-disjoined-replace-subterm-of-term
  (equal (build.flag-disjoined-replace-subterm 'term x old new proof)
         (build.disjoined-replace-subterm x old new proof))
  :hints(("Goal" :in-theory (enable build.disjoined-replace-subterm))))

(defthm build.flag-disjoined-replace-subterm-of-list
  (equal (build.flag-disjoined-replace-subterm 'list x old new proof)
         (build.disjoined-replace-subterm-list x old new proof))
  :hints(("Goal" :in-theory (enable build.disjoined-replace-subterm-list))))

(ACL2::theory-invariant (not (ACL2::active-runep '(:definition build.disjoined-replace-subterm))))
(ACL2::theory-invariant (not (ACL2::active-runep '(:definition build.disjoined-replace-subterm-list))))

(encapsulate
 ()
 (defthm build.disjoined-replace-subterm-list-when-not-consp
   (implies (not (consp x))
            (equal (build.disjoined-replace-subterm-list x old new proof)
                   nil))
   :hints(("Goal" :in-theory (enable definition-of-build.disjoined-replace-subterm-list))))

 (defthm build.disjoined-replace-subterm-list-of-cons
   (equal (build.disjoined-replace-subterm-list (cons a x) old new proof)
          (cons (build.disjoined-replace-subterm a old new proof)
                (build.disjoined-replace-subterm-list x old new proof)))
   :hints(("Goal" :in-theory (enable definition-of-build.disjoined-replace-subterm-list))))

 (defprojection
   :list (build.disjoined-replace-subterm-list x old new proof)
   :element (build.disjoined-replace-subterm x old new proof)
   :already-definedp t))

(encapsulate
 ()
 (local (defthm lemma
          (if (equal flag 'term)
              (implies (and (logic.termp x)
                            (logic.termp old)
                            (logic.termp new)
                            (logic.appealp proof)
                            (equal (logic.fmtype (logic.conclusion proof)) 'por*)
                            (equal (logic.vrhs (logic.conclusion proof)) (logic.pequal old new)))
                       (and (logic.appealp (build.disjoined-replace-subterm x old new proof))
                            (equal (logic.conclusion (build.disjoined-replace-subterm x old new proof))
                                   (logic.por (logic.vlhs (logic.conclusion proof))
                                              (logic.pequal x (logic.replace-subterm x old new))))))
            (implies (and (logic.term-listp x)
                          (logic.termp old)
                          (logic.termp new)
                          (logic.appealp proof)
                          (equal (logic.fmtype (logic.conclusion proof)) 'por*)
                          (equal (logic.vrhs (logic.conclusion proof)) (logic.pequal old new)))
                     (and (logic.appeal-listp (build.disjoined-replace-subterm-list x old new proof))
                          (equal (logic.strip-conclusions (build.disjoined-replace-subterm-list x old new proof))
                                 (logic.por-list (repeat (logic.vlhs (logic.conclusion proof)) (len x))
                                                 (logic.pequal-list x (logic.replace-subterm-list x old new)))))))
          :rule-classes nil
          :hints(("Goal"
                  :expand ((build.disjoined-replace-subterm x old new proof)
                           (build.disjoined-replace-subterm old old new proof)
                           (logic.replace-subterm x old new)
                           (logic.replace-subterm old old new))
                  ;; :restrict ((forcing-lookup-of-logic.function-name ((atbl atbl))))
                  :induct (build.flag-disjoined-replace-subterm flag x old new proof)))))

 (defthm forcing-logic.appealp-of-build.disjoined-replace-subterm
   (implies (force (and (logic.termp x)
                        (logic.termp old)
                        (logic.termp new)
                        (logic.appealp proof)
                        (equal (logic.fmtype (logic.conclusion proof)) 'por*)
                        (equal (logic.vrhs (logic.conclusion proof)) (logic.pequal old new))))
            (equal (logic.appealp (build.disjoined-replace-subterm x old new proof))
                   t))
   :hints(("Goal" :use ((:instance lemma (flag 'term))))))

 (defthm forcing-logic.conclusion-of-build.disjoined-replace-subterm
   (implies (force (and (logic.termp x)
                        (logic.termp old)
                        (logic.termp new)
                        (logic.appealp proof)
                        (equal (logic.fmtype (logic.conclusion proof)) 'por*)
                        (equal (logic.vrhs (logic.conclusion proof)) (logic.pequal old new))))
            (equal (logic.conclusion (build.disjoined-replace-subterm x old new proof))
                   (logic.por (logic.vlhs (logic.conclusion proof))
                              (logic.pequal x (logic.replace-subterm x old new)))))
   :rule-classes ((:rewrite :backchain-limit-lst 0))
   :hints(("Goal" :use ((:instance lemma (flag 'term))))))

 (defthm forcing-logic.appeal-listp-of-build.disjoined-replace-subterm-list
   (implies (force (and (logic.term-listp x)
                        (logic.termp old)
                        (logic.termp new)
                        (logic.appealp proof)
                        (equal (logic.fmtype (logic.conclusion proof)) 'por*)
                        (equal (logic.vrhs (logic.conclusion proof)) (logic.pequal old new))))
            (equal (logic.appeal-listp (build.disjoined-replace-subterm-list x old new proof))
                   t))
   :hints(("Goal" :use ((:instance lemma (flag 'list))))))

 (defthm forcing-logic.strip-conclusions-of-build.disjoined-replace-subterm-list
   (implies (force (and (logic.term-listp x)
                        (logic.termp old)
                        (logic.termp new)
                        (logic.appealp proof)
                        (equal (logic.fmtype (logic.conclusion proof)) 'por*)
                        (equal (logic.vrhs (logic.conclusion proof)) (logic.pequal old new))))
            (equal (logic.strip-conclusions (build.disjoined-replace-subterm-list x old new proof))
                   (logic.por-list (repeat (logic.vlhs (logic.conclusion proof)) (len x))
                                   (logic.pequal-list x (logic.replace-subterm-list x old new)))))
   :rule-classes ((:rewrite :backchain-limit-lst 0))
   :hints(("Goal" :use ((:instance lemma (flag 'list)))))))

(encapsulate
 ()
 (local (defthm@ lemma
          (if (equal flag 'term)
              (implies (and (logic.termp x)
                            (logic.termp old)
                            (logic.termp new)
                            (logic.appealp proof)
                            (equal (logic.fmtype (logic.conclusion proof)) 'por*)
                            (equal (logic.vrhs (logic.conclusion proof)) (logic.pequal old new))
                            ;; ---
                            (logic.term-atblp x atbl)
                            (logic.proofp proof axioms thms atbl)
                            (@obligations build.disjoined-replace-subterm))
                       (logic.proofp (build.disjoined-replace-subterm x old new proof) axioms thms atbl))
            (implies (and (logic.term-listp x)
                          (logic.termp old)
                          (logic.termp new)
                          (logic.appealp proof)
                          (equal (logic.fmtype (logic.conclusion proof)) 'por*)
                          (equal (logic.vrhs (logic.conclusion proof)) (logic.pequal old new))
                          ;; ---
                          (logic.term-list-atblp x atbl)
                          (logic.proofp proof axioms thms atbl)
                          (@obligations build.disjoined-replace-subterm-list))
                     (logic.proof-listp (build.disjoined-replace-subterm-list x old new proof) axioms thms atbl)))
          :rule-classes nil
          :hints(("Goal"
                  :expand ((build.disjoined-replace-subterm x old new proof)
                           (build.disjoined-replace-subterm old old new proof))
                  ;; :restrict ((forcing-lookup-of-logic.function-name ((atbl atbl))))
                  :induct (build.flag-disjoined-replace-subterm flag x old new proof)))))

 (defthm@ forcing-logic.proofp-of-build.disjoined-replace-subterm
   (implies (force (and (logic.termp x)
                        (logic.termp old)
                        (logic.termp new)
                        (logic.appealp proof)
                        (equal (logic.fmtype (logic.conclusion proof)) 'por*)
                        (equal (logic.vrhs (logic.conclusion proof)) (logic.pequal old new))
                        ;; ---
                        (logic.term-atblp x atbl)
                        (logic.proofp proof axioms thms atbl)
                        (@obligations build.disjoined-replace-subterm)))
            (equal (logic.proofp (build.disjoined-replace-subterm x old new proof) axioms thms atbl)
                   t))
   :hints(("Goal" :use ((:instance lemma (flag 'term))))))

 (defthm@ forcing-logic.proof-listp-of-build.disjoined-replace-subterm-list
   (implies (force (and (logic.term-listp x)
                        (logic.termp old)
                        (logic.termp new)
                        (logic.appealp proof)
                        (equal (logic.fmtype (logic.conclusion proof)) 'por*)
                        (equal (logic.vrhs (logic.conclusion proof)) (logic.pequal old new))
                        ;; ---
                        (logic.term-list-atblp x atbl)
                        (logic.proofp proof axioms thms atbl)
                        (@obligations build.disjoined-replace-subterm-list)))
            (equal (logic.proof-listp (build.disjoined-replace-subterm-list x old new proof) axioms thms atbl)
                   t))
   :hints(("Goal" :use ((:instance lemma (flag 'list)))))))

(verify-guards build.flag-disjoined-replace-subterm)
(verify-guards build.disjoined-replace-subterm)
(verify-guards build.disjoined-replace-subterm-list)


