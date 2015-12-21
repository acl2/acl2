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
(include-book "evaluator-bldr")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


;; The magic-evaluator is very magical.
;;
;; It's like the generic-evaluator, except
;;   - You don't have to worry about how many steps it will take, and
;;   - It calls raw lisp eval under the hood so it runs much faster.
;;
;; Similarly, there is a magic-evaluator-bldr which doesn't need to take a
;; number of steps.
;;
;; There are some limitations to the magic.
;;   - You can only use the magic evaluator in conjunction with the
;;     tactic harness and only with
;;       (1) the currently defined functions, or
;;       (2) the currently defined syntactic functions (syndefs)
;;   - You can only use its builder with the currently defined functions.
;;
;; Attempting to break these rules will result in a hard error.

(encapsulate
 ()
 (set-verify-guards-eagerness 0)

 (defun-sk evaluable-termp (x defs)
   (acl2::exists n (generic-evaluator x defs n)))

 (set-verify-guards-eagerness 2))


(defund magic-evaluator (x defs)
  ;; This eventually gets replaced with a thin wrapper for common lisp "eval"
  (declare (xargs :guard (and (logic.termp x)
                              (logic.groundp x)
                              (definition-listp defs))))
  (ACL2::prog2$ (ACL2::cw "Warning: magic-evaluator has not yet been redefined!!~%")
                (generic-evaluator x defs (nfix (evaluable-termp-witness x defs)))))

(defthm forcing-logic.constantp-of-magic-evaluator
  (implies (force (and (magic-evaluator x defs)
                       (logic.termp x)
                       (definition-listp defs)))
           (logic.constantp (magic-evaluator x defs)))
  :hints(("Goal" :in-theory (enable magic-evaluator))))




(defund magic-evaluator-bldr (x defs)
  (declare (xargs :guard (and (logic.termp x)
                              (logic.groundp x)
                              (definition-listp defs)
                              (magic-evaluator x defs))
                  :guard-hints (("Goal" :in-theory (enable magic-evaluator)))))
  ;; This eventually gets replaced with a thing wrapper for an "unbounded"
  ;; version of the generic-evaluator-bldr.
  (ACL2::prog2$ (ACL2::cw "Warning: magic-evaluator-bldr has not yet been redefined!!~%")
                (generic-evaluator-bldr x defs (nfix (evaluable-termp-witness x defs)))))

(defobligations magic-evaluator-bldr
  (generic-evaluator-bldr))

(defthm forcing-logic.appealp-of-magic-evaluator-bldr
  (implies (force (and (magic-evaluator x defs)
                       (logic.termp x)
                       (definition-listp defs)))
           (equal (logic.appealp (magic-evaluator-bldr x defs))
                  t))
  :hints(("Goal" :in-theory (enable magic-evaluator magic-evaluator-bldr))))

(defthm forcing-logic.conclusion-of-magic-evaluator-bldr
  (implies (force (and (magic-evaluator x defs)
                       (logic.termp x)
                       (definition-listp defs)))
           (equal (logic.conclusion (magic-evaluator-bldr x defs))
                  (logic.pequal x (magic-evaluator x defs))))
  :hints(("Goal" :in-theory (enable magic-evaluator magic-evaluator-bldr))))

(defthm@ forcing-logic.proofp-of-magic-evaluator-bldr
  (implies (force (and (magic-evaluator x defs)
                       (logic.termp x)
                       (logic.term-atblp x atbl)
                       (definition-listp defs)
                       (logic.formula-list-atblp defs atbl)
                       (subsetp defs axioms)
                       (equal (cdr (lookup 'if atbl)) 3)
                       (equal (cdr (lookup 'equal atbl)) 2)
                       (@obligations generic-evaluator-bldr)))
           (equal (logic.proofp (magic-evaluator-bldr x defs) axioms thms atbl)
                  t))
  :hints(("Goal" :in-theory (enable magic-evaluator magic-evaluator-bldr))))

