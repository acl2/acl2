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
(include-book "base-evaluator")
(include-book "substitute-formula")
(%interactive)


(%autoadmit logic.flag-appealp)
(%autoadmit logic.appealp)
(%autoadmit logic.appeal-listp)

(%autoadmit logic.appeal)
(%autoadmit logic.method)
(%autoadmit logic.conclusion)
(%autoadmit logic.subproofs)
(%autoadmit logic.extras)

(%autoprove definition-of-logic.appealp
            (%enable default logic.appealp logic.appeal-listp)
            (%restrict default logic.flag-appealp (equal x 'x)))

(%autoprove definition-of-logic.appeal-listp
            (%enable default logic.appealp logic.appeal-listp)
            (%restrict default logic.flag-appealp (equal x 'x)))

(defmacro %logic.appeal-induction (flag x)
  ;; weird that this has 'list instead of 'proof??
  `(%induct (two-nats-measure (rank ,x) (if (equal ,flag 'proof) '1 '0))
            ((equal ,flag 'proof)
             (((,x    (logic.subproofs ,x))
               (,flag 'list))))
            ((and (not (equal ,flag 'proof))
                  (consp ,x))
             (((,x    (car ,x))
               (,flag 'proof))
              ((,x    (cdr ,x))
               (,flag 'list))))
            ((and (not (equal ,flag 'proof))
                  (not (consp ,x)))
             nil)))

(defsection lemma-for-booleanp-of-logic.appealp
  (%prove (%rule lemma-for-booleanp-of-logic.appealp
                 :lhs (if (equal flag 'proof)
                          (booleanp (logic.appealp x))
                        (booleanp (logic.appeal-listp x)))
                 :rhs t))
  (%logic.appeal-induction flag x)
  (local (%restrict default definition-of-logic.appealp (equal x 'x)))
  (local (%restrict default definition-of-logic.appeal-listp (equal x 'x)))
  (local (%enable default logic.subproofs))
  (%auto)
  (%qed))

(%autoprove booleanp-of-logic.appealp
            (%use (%instance (%thm lemma-for-booleanp-of-logic.appealp) (flag 'proof))))

(%autoprove booleanp-of-logic.appeal-listp
            (%use (%instance (%thm lemma-for-booleanp-of-logic.appealp) (flag 'list))))

(%autoprove logic.appeal-listp-when-not-consp
            (%restrict default definition-of-logic.appeal-listp (equal x 'x)))

(%autoprove logic.appeal-listp-of-cons
            (%restrict default definition-of-logic.appeal-listp (equal x '(cons a x))))

(%deflist logic.appeal-listp (x)
          (logic.appealp x))


(%autoprove logic.appealp-of-nth-when-logic.appeal-listp)

(%autoprove logic.appealp-of-second-when-logic.appeal-listp)

(%autoprove forcing-logic.appeal-listp-of-firstn)

(%autoprove forcing-logic.appeal-listp-of-restn)



(%autoprove logic.method-of-logic.appeal
            (%enable default logic.appeal logic.method))

(%autoprove logic.conclusion-of-logic.appeal
            (%enable default logic.appeal logic.conclusion))

(%autoprove logic.subproofs-of-logic.appeal
            (%enable default logic.appeal logic.subproofs))

(%autoprove logic.extras-of-logic.appeal
            (%enable default logic.appeal logic.extras))

(%autoprove logic.appeal-under-iff
            (%enable default logic.appeal))

(%autoprove forcing-logic.appealp-of-logic.appeal
            (%enable default logic.appeal)
            (%restrict default definition-of-logic.appealp
                       (or (equal x '(CONS METHOD (CONS CONCLUSION 'NIL)))
                           (equal x '(CONS METHOD (CONS CONCLUSION (CONS SUBPROOFS 'NIL))))
                           (equal x '(CONS METHOD (CONS CONCLUSION (CONS SUBPROOFS (CONS EXTRAS 'NIL))))))))


(%autoprove forcing-symbolp-of-logic.method
            (%enable default logic.method)
            (%restrict default definition-of-logic.appealp (equal x 'x)))

(%autoprove forcing-logic.formulap-of-logic.conclusion
            (%enable default logic.conclusion)
            (%restrict default definition-of-logic.appealp (equal x 'x)))

(%autoprove forcing-true-listp-of-logic.subproofs
            (%enable default logic.subproofs)
            (%restrict default definition-of-logic.appealp (equal x 'x)))

(%autoprove forcing-logic.appeal-listp-of-logic.subproofs
            (%enable default logic.subproofs)
            (%restrict default definition-of-logic.appealp (equal x 'x)))


(%autoprove rank-of-logic.subproofs
            (%enable default logic.subproofs)
            (%restrict default definition-of-logic.appealp (equal x 'x)))

(%autoprove rank-of-logic.subproofs-weak
            (%enable default logic.subproofs))

(%autoprove rank-of-logic.subproofs-strong-via-consp
            (%enable default logic.subproofs))

(%autoprove rank-of-first-of-logic.subproofs
            (%disable default rank-of-logic.subproofs)
            (%use (%instance (%thm rank-of-logic.subproofs))))

(%autoprove rank-of-second-of-logic.subproofs
            (%disable default rank-of-logic.subproofs)
            (%use (%instance (%thm rank-of-logic.subproofs))))

