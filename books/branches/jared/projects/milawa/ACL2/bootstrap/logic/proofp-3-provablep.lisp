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
(include-book "proofp-2")
(%interactive)

(%defchoose logic.provable-witness proof (x axioms thms atbl)
            (and (logic.appealp proof)
                 (logic.proofp proof axioms thms atbl)
                 (equal (logic.conclusion proof) x)))

(defun logic.provablep (x axioms thms atbl)
  ;; BOZO because we used defun-sk to introduce it, which is based on
  ;; ACL2::defun instead of MILAWA::defun, there's no syntax-defuns entry for
  ;; logic.provablep, So, we now add a redundant definition of logic.provablep
  ;; using MILAWA::defun, so that %autoadmit knows what its definition is.
  (declare (xargs :guard (and (logic.formulap x)
                              (logic.formula-listp axioms)
                              (logic.formula-listp thms)
                              (logic.arity-tablep atbl))))
  (let ((proof (logic.provable-witness x axioms thms atbl)))
       (and (logic.appealp proof)
            (logic.proofp proof axioms thms atbl)
            (equal (logic.conclusion proof) x))))

(%autoadmit logic.provablep)

(%autoprove logic.provablep-suff
            (%use (build.axiom (defchoose-axiom-for-logic.provable-witness)))
            (%enable default logic.provablep))

(%autoprove booleanp-of-logic.provablep
            (%enable default logic.provablep))

(%autoprove forcing-logic.appealp-of-logic.provable-witness
            (%enable default logic.provablep))

(%autoprove forcing-logic.proofp-of-logic.provable-witness
            (%enable default logic.provablep)
            (%disable default forcing-logic.appealp-of-logic.provable-witness))

(%autoprove forcing-logic.conclusion-of-logic.provable-witness
            (%enable default logic.provablep))

(%autoprove logic.formulap-when-logic.provablep
            (%disable default forcing-logic.formulap-of-logic.conclusion)
            (%use (%instance (%thm forcing-logic.formulap-of-logic.conclusion)
                             (x (logic.provable-witness x axioms thms atbl))))
            ;; This %split is important for some reason
            (%split))

(%autoprove logic.formula-atblp-when-logic.provablep
            (%use (%instance (%thm logic.formula-atblp-of-logic.conclusion-when-logic.proofp)
                             (x (logic.provable-witness x axioms thms atbl)))))

(%autoprove logic.provablep-when-not-consp
            (%disable default logic.formulap-when-not-consp)
            (%use (%instance (%thm logic.formulap-when-not-consp))))

(%autoprove forcing-logic.provablep-when-logic.proofp
            (%use (%instance (%thm logic.provablep-suff)
                             (proof x)
                             (x (logic.conclusion x)))))



(%deflist logic.provable-listp (x axioms thms atbl)
          (logic.provablep x axioms thms atbl))

(%autoprove logic.provablep-of-car-when-logic.provable-listp-free)

(%autoprove logic.provablep-of-second-when-logic.provable-listp)

(%autoprove forcing-logic.provable-listp-of-logic.strip-conclusions-when-logic.proof-listp
            (%cdr-induction x))

(%autoprove forcing-logic.provable-listp-of-logic.subproofs-when-logic.proofp
            (%restrict default definition-of-logic.proofp (equal x 'x)))

(%autoprove logic.formula-list-atblp-of-when-logic.provable-listp
            (%cdr-induction x))



(%defprojection :list (logic.provable-list-witness x axioms thms atbl)
                :element (logic.provable-witness x axioms thms atbl))

(%autoprove forcing-logic.appeal-listp-of-logic.provable-list-witness
            (%cdr-induction x))

(%autoprove force-logic.proof-listp-of-logic.provable-list-witness
            (%cdr-induction x))

(%autoprove forcing-logic.strip-conclusions-of-logic.provable-list-witness
            (%cdr-induction x))

(%autoprove logic.provablep-of-logic.conclusion-of-first-when-logic.provable-listp)
(%autoprove logic.provablep-of-logic.conclusion-of-second-when-logic.provable-listp)
(%autoprove logic.provablep-of-logic.conclusion-of-third-when-logic.provable-listp)
(%autoprove logic.provablep-of-logic.conclusion-of-fourth-when-logic.provable-listp)

