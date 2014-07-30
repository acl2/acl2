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

(acl2::def-functional-instance
 eval-g-base-alt-def
 generic-geval-alt-def
 ((generic-geval-ev eval-g-base-ev)
  (generic-geval-ev-lst eval-g-base-ev-lst)
  (generic-geval eval-g-base)
  (generic-geval-list eval-g-base-list))
 :hints ('(:in-theory (e/d* (eval-g-base-ev-of-fncall-args
                             eval-g-base-apply-agrees-with-eval-g-base-ev)
                            (eval-g-base-apply))
           :expand ((eval-g-base x env)
                    (eval-g-base-list x env))))
         ;; :do-not-induct
         ;;   t
         ;;   :expand ((eval-g-base x env))))
 :rule-classes ((:definition :clique (eval-g-base))))


(acl2::def-functional-instance
 mk-g-boolean-correct-for-eval-g-base
 mk-g-boolean-correct
 ((generic-geval-ev eval-g-base-ev)
  (generic-geval-ev-lst eval-g-base-ev-lst)
  (generic-geval eval-g-base)
  (generic-geval-list eval-g-base-list)))



(acl2::def-functional-instance
 gtests-obj-correct-for-eval-g-base
 gtests-obj-correct
 ((generic-geval-ev eval-g-base-ev)
  (generic-geval-ev-lst eval-g-base-ev-lst)
  (generic-geval eval-g-base)
  (generic-geval-list eval-g-base-list)))

(acl2::def-functional-instance
 gtests-nonnil-correct-for-eval-g-base
 gtests-nonnil-correct
 ((generic-geval-ev eval-g-base-ev)
  (generic-geval-ev-lst eval-g-base-ev-lst)
  (generic-geval eval-g-base)
  (generic-geval-list eval-g-base-list)))

(acl2::def-functional-instance
 bfr-assume-of-gtests-possibly-true-for-eval-g-base
 bfr-assume-of-gtests-possibly-true
 ((generic-geval-ev eval-g-base-ev)
  (generic-geval-ev-lst eval-g-base-ev-lst)
  (generic-geval eval-g-base)
  (generic-geval-list eval-g-base-list)))

(acl2::def-functional-instance
 bfr-assume-of-gtests-possibly-false-for-eval-g-base
 bfr-assume-of-gtests-possibly-false
 ((generic-geval-ev eval-g-base-ev)
  (generic-geval-ev-lst eval-g-base-ev-lst)
  (generic-geval eval-g-base)
  (generic-geval-list eval-g-base-list)))

;; (local
;;  (progn

;;    ;; These should only be necessary to prove the meta rules for g-if.

(acl2::def-functional-instance
  g-if-fn-correct-for-eval-g-base
  g-if-fn-correct
  ((generic-geval-ev eval-g-base-ev)
   (generic-geval-ev-lst eval-g-base-ev-lst)
   (generic-geval eval-g-base)
   (generic-geval-list eval-g-base-list)))

(acl2::def-functional-instance
  g-or-fn-correct-for-eval-g-base
  g-or-fn-correct
  ((generic-geval-ev eval-g-base-ev)
   (generic-geval-ev-lst eval-g-base-ev-lst)
   (generic-geval eval-g-base)
   (generic-geval-list eval-g-base-list)))

(acl2::def-functional-instance
  mk-g-ite-correct-for-eval-g-base
  mk-g-ite-correct
  ((generic-geval-ev eval-g-base-ev)
   (generic-geval-ev-lst eval-g-base-ev-lst)
   (generic-geval eval-g-base)
   (generic-geval-list eval-g-base-list)))


(acl2::def-functional-instance
  gobj-ite-merge-correct-for-eval-g-base
  gobj-ite-merge-correct
  ((generic-geval-ev eval-g-base-ev)
   (generic-geval-ev-lst eval-g-base-ev-lst)
   (generic-geval eval-g-base)
   (generic-geval-list eval-g-base-list)))

(acl2::def-functional-instance
  mk-g-bdd-ite-correct-for-eval-g-base
  mk-g-bdd-ite-correct
  ((generic-geval-ev eval-g-base-ev)
   (generic-geval-ev-lst eval-g-base-ev-lst)
   (generic-geval eval-g-base)
   (generic-geval-list eval-g-base-list)))

(acl2::def-functional-instance
 eval-g-base-g-apply
 generic-geval-g-apply
 ((generic-geval-ev eval-g-base-ev)
  (generic-geval-ev-lst eval-g-base-ev-lst)
  (generic-geval eval-g-base)
  (generic-geval-list eval-g-base-list)))

(acl2::def-functional-instance
 general-consp-car-correct-for-eval-g-base
 general-consp-car-correct
 ((generic-geval-ev eval-g-base-ev)
  (generic-geval-ev-lst eval-g-base-ev-lst)
  (generic-geval eval-g-base)
  (generic-geval-list eval-g-base-list)))

(acl2::def-functional-instance
 general-consp-cdr-correct-for-eval-g-base
 general-consp-cdr-correct
 ((generic-geval-ev eval-g-base-ev)
  (generic-geval-ev-lst eval-g-base-ev-lst)
  (generic-geval eval-g-base)
  (generic-geval-list eval-g-base-list)))

(in-theory (disable general-consp-car-correct-for-eval-g-base
                    general-consp-cdr-correct-for-eval-g-base))

(acl2::def-functional-instance
 eval-g-base-cons
 generic-geval-cons
 ((generic-geval-ev eval-g-base-ev)
  (generic-geval-ev-lst eval-g-base-ev-lst)
  (generic-geval eval-g-base)
  (generic-geval-list eval-g-base-list)))

(acl2::def-functional-instance
 eval-g-base-non-cons
 generic-geval-non-cons
 ((generic-geval-ev eval-g-base-ev)
  (generic-geval-ev-lst eval-g-base-ev-lst)
  (generic-geval eval-g-base)
  (generic-geval-list eval-g-base-list)))

(in-theory (disable eval-g-base-non-cons))

;; (acl2::def-functional-instance
;;  eval-g-base-gobj-fix
;;  generic-geval-gobj-fix
;;  ((apply-stub eval-g-base-apply)
;;   (generic-geval-apply eval-g-base-apply)
;;   (generic-geval eval-g-base)

(acl2::def-functional-instance
 general-concrete-obj-when-consp-for-eval-g-base
 general-concrete-obj-when-consp
 ((generic-geval-ev eval-g-base-ev)
  (generic-geval-ev-lst eval-g-base-ev-lst)
  (generic-geval eval-g-base)
  (generic-geval-list eval-g-base-list)))

(acl2::def-functional-instance
 not-general-numberp-not-acl2-numberp-for-eval-g-base
 not-general-numberp-not-acl2-numberp
 ((generic-geval-ev eval-g-base-ev)
  (generic-geval-ev-lst eval-g-base-ev-lst)
  (generic-geval eval-g-base)
  (generic-geval-list eval-g-base-list)))

(acl2::def-functional-instance
 mk-g-number-correct-for-eval-g-base
 mk-g-number-correct
 ((generic-geval-ev eval-g-base-ev)
  (generic-geval-ev-lst eval-g-base-ev-lst)
  (generic-geval eval-g-base)
  (generic-geval-list eval-g-base-list)))

(acl2::def-functional-instance
 mk-g-concrete-correct-for-eval-g-base
 mk-g-concrete-correct
 ((generic-geval-ev eval-g-base-ev)
  (generic-geval-ev-lst eval-g-base-ev-lst)
  (generic-geval eval-g-base)
  (generic-geval-list eval-g-base-list)))

(acl2::def-functional-instance
 g-concrete-quote-correct-for-eval-g-base
 g-concrete-quote-correct
 ((generic-geval-ev eval-g-base-ev)
  (generic-geval-ev-lst eval-g-base-ev-lst)
  (generic-geval eval-g-base)
  (generic-geval-list eval-g-base-list)))

(acl2::def-functional-instance
 eval-g-base-of-gl-cons
 generic-geval-gl-cons
 ((generic-geval-ev eval-g-base-ev)
  (generic-geval-ev-lst eval-g-base-ev-lst)
  (generic-geval eval-g-base)
  (generic-geval-list eval-g-base-list)))

(acl2::def-functional-instance
 eval-g-base-list-of-gl-cons
 generic-geval-list-gl-cons
 ((generic-geval-ev eval-g-base-ev)
  (generic-geval-ev-lst eval-g-base-ev-lst)
  (generic-geval eval-g-base)
  (generic-geval-list eval-g-base-list)))





;; (def-geval-meta eval-g-base evgb-ev evgb-ev-lst)
