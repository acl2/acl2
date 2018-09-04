; GL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2008-2013 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
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
; Original author: Sol Swords <sswords@centtech.com>

(in-package "GL")
(include-book "eval-g-base")
(include-book "g-if")
;; (include-book "gify-clause-proc")
(include-book "general-object-thms")
(include-book "tools/def-functional-instance" :dir :system)

(set-ignore-ok t)


(defmacro def-eval-g-base-thm-instance (new-name orig-name &key (rule-classes 'nil rule-classes-p))
  `(acl2::def-functional-instance
     ,new-name ,orig-name
     ((generic-geval-ev eval-g-base-ev)
      (generic-geval-ev-lst eval-g-base-ev-lst)
      (generic-geval eval-g-base)
      (generic-geval-list eval-g-base-list))
     :hints ('(:in-theory (e/d* (eval-g-base-ev-of-fncall-args
                                 eval-g-base-apply-agrees-with-eval-g-base-ev)
                                (eval-g-base-apply))
               :expand ((:with eval-g-base (eval-g-base x env))
                        (eval-g-base-list x env))))
     . ,(and rule-classes-p `(:rule-classes ,rule-classes))))

(def-eval-g-base-thm-instance eval-g-base-alt-def generic-geval-alt-def
  :rule-classes ((:definition :clique (eval-g-base) :controller-alist ((eval-g-base t nil)))))

(in-theory (disable eval-g-base-alt-def eval-g-base))

(def-eval-g-base-thm-instance general-boolean-value-correct-for-eval-g-base general-boolean-value-correct)
(def-eval-g-base-thm-instance mk-g-boolean-correct-for-eval-g-base mk-g-boolean-correct)
(def-eval-g-base-thm-instance booleanp-of-geval-for-eval-g-base booleanp-of-geval)
(def-eval-g-base-thm-instance gtests-obj-correct-for-eval-g-base gtests-obj-correct)
(def-eval-g-base-thm-instance gtests-nonnil-correct-for-eval-g-base gtests-nonnil-correct)
(def-eval-g-base-thm-instance bfr-assume-of-gtests-possibly-true-for-eval-g-base bfr-assume-of-gtests-possibly-true)
(def-eval-g-base-thm-instance bfr-assume-of-gtests-possibly-false-for-eval-g-base bfr-assume-of-gtests-possibly-false)
(def-eval-g-base-thm-instance general-integer-bits-correct-for-eval-g-base general-integer-bits-correct)
(def-eval-g-base-thm-instance integerp-of-geval-for-eval-g-base integerp-of-geval)
(def-eval-g-base-thm-instance general-consp-correct-for-eval-g-base general-consp-correct)
(def-eval-g-base-thm-instance not-consp-implies-not-general-consp-for-eval-g-base not-consp-implies-not-general-consp
  :rule-classes :forward-chaining)
(def-eval-g-base-thm-instance consp-of-geval-for-eval-g-base consp-of-geval)

(def-eval-g-base-thm-instance general-consp-car-when-concretep-for-eval-g-base general-consp-car-when-concretep)
(def-eval-g-base-thm-instance general-consp-cdr-when-concretep-for-eval-g-base general-consp-car-when-concretep)

;; (local
;;  (progn

;;    ;; These should only be necessary to prove the meta rules for g-if.

(def-eval-g-base-thm-instance g-if-fn-correct-for-eval-g-base g-if-fn-correct)
(def-eval-g-base-thm-instance g-or-fn-correct-for-eval-g-base g-or-fn-correct)
(def-eval-g-base-thm-instance mk-g-ite-correct-for-eval-g-base mk-g-ite-correct)
(def-eval-g-base-thm-instance gobj-ite-merge-correct-for-eval-g-base gobj-ite-merge-correct)
(def-eval-g-base-thm-instance mk-g-bdd-ite-correct-for-eval-g-base mk-g-bdd-ite-correct)
(def-eval-g-base-thm-instance eval-g-base-g-apply generic-geval-g-apply)
(def-eval-g-base-thm-instance general-consp-car-correct-for-eval-g-base general-consp-car-correct)
(def-eval-g-base-thm-instance general-consp-cdr-correct-for-eval-g-base general-consp-cdr-correct)

(in-theory (disable general-consp-car-correct-for-eval-g-base
                    general-consp-cdr-correct-for-eval-g-base))

(def-eval-g-base-thm-instance eval-g-base-cons generic-geval-cons)
(def-eval-g-base-thm-instance eval-g-base-non-cons generic-geval-non-cons)

(in-theory (disable eval-g-base-non-cons))

;; (def-eval-g-base-thm-instance general-concrete-obj-when-consp-for-eval-g-base general-concrete-obj-when-consp)
(def-eval-g-base-thm-instance general-number-fix-correct-for-eval-g-base general-number-fix-correct)
(def-eval-g-base-thm-instance geval-when-general-concretep-of-number-fix-for-eval-g-base geval-when-general-concretep-of-number-fix)

(def-eval-g-base-thm-instance not-general-integerp-not-integerp-for-eval-g-base not-general-integerp-not-integerp)
(def-eval-g-base-thm-instance mk-g-integer-correct-for-eval-g-base mk-g-integer-correct)
(def-eval-g-base-thm-instance mk-g-concrete-correct-for-eval-g-base mk-g-concrete-correct)
(def-eval-g-base-thm-instance g-concrete-quote-correct-for-eval-g-base g-concrete-quote-correct)
(def-eval-g-base-thm-instance eval-g-base-of-gl-cons generic-geval-gl-cons)
(def-eval-g-base-thm-instance eval-g-base-list-of-gl-cons generic-geval-list-gl-cons)
(def-eval-g-base-thm-instance generic-geval-of-g-ite-branches-for-eval-g-base generic-geval-of-g-ite-branches)
(def-eval-g-base-thm-instance general-concrete-obj-correct-for-eval-g-base general-concrete-obj-correct)





;; (def-geval-meta eval-g-base evgb-ev evgb-ev-lst)
