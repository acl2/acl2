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
(include-book "worldp")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


(defund tactic.slow-world-arities (x)
  (declare (xargs :guard (tactic.worldp x)))
  (let* ((res (rw.slow-theory-map-arities (tactic.world->theories x)))
         (res (app (rw.slow-rule-list-arities (tactic.world->allrules x)) res))
         (res (app (logic.slow-formula-list-arities (tactic.world->defs x)) res)))
    res))

(defund tactic.world-arities (x acc)
  (declare (xargs :guard (and (tactic.worldp x)
                              (true-listp acc))))
  (let* ((acc (rw.theory-map-arities (tactic.world->theories x) acc))
         (acc (rw.rule-list-arities (tactic.world->allrules x) acc)))
    (logic.formula-list-arities (tactic.world->defs x) acc)))

(defthm true-listp-of-tactic.world-arities
  (implies (force (true-listp acc))
           (equal (true-listp (tactic.world-arities x acc))
                  t))
  :hints(("Goal" :in-theory (enable tactic.world-arities))))

(defthm tactic.world-arities-removal
  (implies (force (true-listp acc))
           (equal (tactic.world-arities x acc)
                  (app (tactic.slow-world-arities x) acc)))
  :hints(("Goal" :in-theory (enable tactic.world-arities
                                    tactic.slow-world-arities))))

(defthm tactic.slow-world-arities-correct
  (implies (force (tactic.worldp x))
           (equal (logic.arities-okp (tactic.slow-world-arities x) atbl)
                  (tactic.world-atblp x atbl)))
  :hints(("Goal"
          :expand ((tactic.slow-world-arities x)
                   (tactic.world-atblp x atbl))
          :in-theory (disable rw.rule-list-atblp-of-tactic.world->allrules
                              logic.formula-list-atblp-of-tactic.world->defs
                              rw.theory-list-atblp-of-range-of-tactic.world->theories))))



(defund tactic.slow-world-list-arities (x)
  (declare (xargs :guard (tactic.world-listp x)))
  (if (consp x)
      ;; Reverse order gives us a tail call in the fast version
      (app (tactic.slow-world-list-arities (cdr x))
           (tactic.slow-world-arities (car x)))
    nil))

(defund tactic.world-list-arities (x acc)
  (declare (xargs :guard (and (tactic.world-listp x)
                              (true-listp acc))))
  (if (consp x)
      (tactic.world-list-arities (cdr x)
                                 (tactic.world-arities (car x) acc))
    acc))

(defthm true-listp-of-tactic.world-list-arities
  (implies (force (true-listp acc))
           (equal (true-listp (tactic.world-list-arities x acc))
                  t))
  :hints(("Goal" :in-theory (enable tactic.world-list-arities))))

(defthm tactic.world-list-arities-removal
  (implies (force (true-listp acc))
           (equal (tactic.world-list-arities x acc)
                  (app (tactic.slow-world-list-arities x) acc)))
  :hints(("Goal" :in-theory (enable tactic.world-list-arities
                                    tactic.slow-world-list-arities))))

(defthm tactic.slow-world-list-arities-correct
  (implies (force (tactic.world-listp x))
           (equal (logic.arities-okp (tactic.slow-world-list-arities x) atbl)
                  (tactic.world-list-atblp x atbl)))
  :hints(("Goal"
          :induct (cdr-induction x)
          :expand ((tactic.world-list-atblp x atbl)
                   (tactic.slow-world-list-arities x)))))



;; One final twist is that if we are checking a list of worlds, it is most
;; common for the allrules and defs to be the same throughout all of the
;; worlds.  Rather than repeatedly collect from them, we see this situation and
;; avoid the redundant gathering.

(defund tactic.slow-world-partial-arities (x)
  (declare (xargs :guard (tactic.worldp x)))
  (rw.slow-theory-map-arities (tactic.world->theories x)))

(defund tactic.world-partial-arities (x acc)
  (declare (xargs :guard (and (tactic.worldp x)
                              (true-listp acc))))
  (rw.theory-map-arities (tactic.world->theories x) acc))

(defthm true-listp-of-tactic.world-partial-arities
  (implies (force (true-listp acc))
           (equal (true-listp (tactic.world-partial-arities x acc))
                  t))
  :hints(("Goal" :in-theory (enable tactic.world-partial-arities))))

(defthm tactic.world-partial-arities-removal
  (implies (force (true-listp acc))
           (equal (tactic.world-partial-arities x acc)
                  (app (tactic.slow-world-partial-arities x) acc)))
  :hints(("Goal" :in-theory (enable tactic.world-partial-arities
                                    tactic.slow-world-partial-arities))))

(defthm tactic.slow-world-partial-arities-correct
  (implies (force (and (tactic.worldp x)
                       (rw.rule-list-atblp (tactic.world->allrules x) atbl)
                       (logic.formula-list-atblp (tactic.world->defs x) atbl)))
           (equal (logic.arities-okp (tactic.slow-world-partial-arities x) atbl)
                  (tactic.world-atblp x atbl)))
  :hints(("Goal"
          :expand ((tactic.slow-world-partial-arities x)
                   (tactic.world-atblp x atbl))
          :in-theory (disable rw.rule-list-atblp-of-tactic.world->allrules
                              logic.formula-list-atblp-of-tactic.world->defs
                              rw.theory-list-atblp-of-range-of-tactic.world->theories))))



(defund tactic.slow-world-list-partial-arities (x)
  (declare (xargs :guard (tactic.world-listp x)))
  (if (consp x)
      ;; Reverse order gives us a tail call in the fast version
      (app (tactic.slow-world-list-partial-arities (cdr x))
           (tactic.slow-world-partial-arities (car x)))
    nil))

(defund tactic.world-list-partial-arities (x acc)
  (declare (xargs :guard (and (tactic.world-listp x)
                              (true-listp acc))))
  (if (consp x)
      (tactic.world-list-partial-arities (cdr x)
                                 (tactic.world-partial-arities (car x) acc))
    acc))

(defthm true-listp-of-tactic.world-list-partial-arities
  (implies (force (true-listp acc))
           (equal (true-listp (tactic.world-list-partial-arities x acc))
                  t))
  :hints(("Goal" :in-theory (enable tactic.world-list-partial-arities))))

(defthm tactic.world-list-partial-arities-removal
  (implies (force (true-listp acc))
           (equal (tactic.world-list-partial-arities x acc)
                  (app (tactic.slow-world-list-partial-arities x) acc)))
  :hints(("Goal" :in-theory (enable tactic.world-list-partial-arities
                                    tactic.slow-world-list-partial-arities))))



(defund tactic.world-list-compatiblep-hack (x)
  (declare (xargs :guard (tactic.world-listp x)))
  (if (consp x)
      (if (consp (cdr x))
          (and (equal (tactic.world->allrules (first x))
                      (tactic.world->allrules (second x)))
               (equal (tactic.world->defs (first x))
                      (tactic.world->defs (second x)))
               (tactic.world-list-compatiblep-hack (cdr x)))
        t)
    t))

(defthm tactic.slow-world-list-partial-arities-correct
  (implies (force (and (tactic.world-listp x)
                       (tactic.world-list-compatiblep-hack x)
                       (consp x)
                       (rw.rule-list-atblp (tactic.world->allrules (car x)) atbl)
                       (logic.formula-list-atblp (tactic.world->defs (car x)) atbl)))
           (equal (logic.arities-okp (tactic.slow-world-list-partial-arities x) atbl)
                  (tactic.world-list-atblp x atbl)))
  :hints(("Goal"
          :induct (cdr-induction x)
          :in-theory (e/d (tactic.world-list-compatiblep-hack
                           tactic.slow-world-list-partial-arities)
                          (LOGIC.FORMULA-LIST-ATBLP-OF-TACTIC.WORLD->DEFS
                           RW.RULE-LIST-ATBLP-OF-TACTIC.WORLD->ALLRULES)))))


;; All of this culminates in tactic.fast-world-list-atblp, which is pretty damn
;; wonderful.

(defund tactic.fast-world-list-atblp (x atbl)
  (declare (xargs :guard (and (tactic.world-listp x)
                              (logic.arity-tablep atbl))))
  (if (and (consp x)
           (tactic.world-list-compatiblep-hack x))
      (let* ((acc (rw.rule-list-arities (tactic.world->allrules (car x)) nil))
             (acc (logic.formula-list-arities (tactic.world->defs (car x)) acc))
             (acc (tactic.world-list-partial-arities x acc)))
        (logic.fast-arities-okp acc atbl))
    (ACL2::prog2$
     (ACL2::cw "Performance note: fast-world-atblp cannot use compatibility hack.~%")
     (logic.fast-arities-okp (tactic.world-list-arities x nil) atbl))))

(defthm tactic.fast-world-list-atblp-is-tactic.world-list-atblp
  (implies (force (and (tactic.world-listp x)
                       (mapp atbl)))
           (equal (tactic.fast-world-list-atblp x atbl)
                  (tactic.world-list-atblp x atbl)))
  :hints(("Goal"
          :in-theory (e/d (tactic.fast-world-list-atblp)
                          ((:executable-counterpart acl2::force))))))


;; Here are some performance comparisons, using level9/symmetry.

;; (defun tactic.world-list-atblp-wrapper (x atbl)   ;; to avoid guards
;;   (declare (xargs :mode :program))
;;   (tactic.world-list-atblp x atbl))

;; (defun tactic.fast-world-list-atblp-wrapper (x atbl)   ;; to avoid guards
;;   (declare (xargs :mode :program))
;;   (tactic.fast-world-list-atblp x atbl))

;; (acl2::time$
;;  ;; 7.3 seconds, 28 KB allocated
;;  (tactic.world-list-atblp-wrapper (repeat (tactic.harness->world (acl2::w acl2::state)) 1)
;;                                   (tactic.harness->atbl (acl2::w acl2::state))))

;; (acl2::time$
;;  ;; 20.7 seconds, 86 KB allocated
;;  (tactic.world-list-atblp-wrapper (repeat (tactic.harness->world (acl2::w acl2::state)) 3)
;;                                   (tactic.harness->atbl (acl2::w acl2::state))))

;; (acl2::time$
;;  ;; .36 seconds, 62 MB allocated
;;  (tactic.fast-world-list-atblp-wrapper (repeat (tactic.harness->world (acl2::w acl2::state)) 1)
;;                                        (tactic.harness->atbl (acl2::w acl2::state))))

;; (acl2::time$
;;  ;; .6 seconds, 105 MB allocated
;;  (tactic.fast-world-list-atblp-wrapper (repeat (tactic.harness->world (acl2::w acl2::state)) 3)
;;                                        (tactic.harness->atbl (acl2::w acl2::state))))

;; (acl2::time$
;;  ;; .74 seconds, 127 MB allocated
;;  (tactic.fast-world-list-atblp-wrapper (repeat (tactic.harness->world (acl2::w acl2::state)) 4)
;;                                        (tactic.harness->atbl (acl2::w acl2::state))))

;; (acl2::time$
;;  ;; 2.1 seconds, 376 MB allocated
;;  (tactic.fast-world-list-atblp-wrapper (repeat (tactic.harness->world (acl2::w acl2::state)) 15)
;;                                        (tactic.harness->atbl (acl2::w acl2::state))))







;; We now turn our attention to developing fast checks for the env-okp
;; functions.  Our approach is pretty much the same as for the arity table,
;; except it's a little easier because we don't need to develop any analogue of
;; logic.arities-okp or anything; it's just a matter of harvesting lists of
;; formulas and putting them into lists, which we'll then mergesort and do an
;; ordered comparison against to make sure they're all axioms and/or theorems.

;; We start with the rewrite rules.  We need to show that every rule in the
;; list of allrules and that all of the rules throughout our theories are
;; members of *thms*.  As with our atbl checks, we just accumulate the theorems
;; for all the rules.


;; We found it useful to break up tactic.world-env-okp into two functions,
;; one to check the axioms and one to check the theorems.

(defund tactic.world-thms-okp (x thms)
  (declare (xargs :guard (and (tactic.worldp x)
                              (logic.formula-listp thms))))
  (and (rw.theory-list-env-okp-of-range (tactic.world->theories x) thms)
       (rw.rule-list-env-okp (tactic.world->allrules x) thms)))

(defund tactic.world-axioms-okp (x axioms)
  (declare (xargs :guard (and (tactic.worldp x)
                              (logic.formula-listp axioms))))
  (subsetp (tactic.world->defs x) axioms))

(defthm booleanp-of-tactic.world-thms-okp
  (equal (booleanp (tactic.world-thms-okp x thms))
         t)
  :hints(("Goal" :in-theory (enable tactic.world-thms-okp))))

(defthm booleanp-of-tactic.world-axioms-okp
  (equal (booleanp (tactic.world-axioms-okp x thms))
         t)
  :hints(("Goal" :in-theory (enable tactic.world-axioms-okp))))

(deflist tactic.world-list-thms-okp (x thms)
  (tactic.world-thms-okp x thms)
  :guard (and (tactic.world-listp x)
              (logic.formula-listp thms)))

(deflist tactic.world-list-axioms-okp (x axioms)
  (tactic.world-axioms-okp x axioms)
  :guard (and (tactic.world-listp x)
              (logic.formula-listp axioms)))

(defthmd tactic.world-env-okp-redefinition
  (equal (tactic.world-env-okp x axioms thms)
         (and (tactic.world-thms-okp x thms)
              (tactic.world-axioms-okp x axioms)))
  :hints(("Goal" :in-theory (enable tactic.world-env-okp
                                    tactic.world-thms-okp
                                    tactic.world-axioms-okp))))

(defthmd tactic.world-list-env-okp-redefinition
  (equal (tactic.world-list-env-okp x axioms thms)
         (and (tactic.world-list-thms-okp x thms)
              (tactic.world-list-axioms-okp x axioms)))
  :hints(("Goal"
          :induct (cdr-induction x)
          :in-theory (enable tactic.world-env-okp-redefinition))))




(defund tactic.slow-world-thms (x)
  (declare (xargs :guard (tactic.worldp x)))
  (app (rw.slow-theory-map-thms (tactic.world->theories x))
       (rw.slow-rule-list-thms (tactic.world->allrules x))))

(defund tactic.world-thms (x acc)
  (declare (xargs :guard (and (tactic.worldp x)
                              (true-listp acc))))
  (let ((acc (rw.rule-list-thms (tactic.world->allrules x) acc)))
    (rw.theory-map-thms (tactic.world->theories x) acc)))

(defthm true-listp-of-tactic.world-thms
  (implies (force (true-listp acc))
           (true-listp (tactic.world-thms x acc)))
  :hints(("Goal" :in-theory (enable tactic.world-thms))))

(defthm tactic.world-thms-removal
  (implies (force (true-listp acc))
           (equal (tactic.world-thms x acc)
                  (app (tactic.slow-world-thms x)
                       acc)))
  :hints(("Goal" :in-theory (enable tactic.world-thms
                                    tactic.slow-world-thms))))

(defthm tactic.slow-world-thms-correct
  (equal (subsetp (tactic.slow-world-thms x) thms)
         (tactic.world-thms-okp x thms))
  :hints(("Goal"
          :in-theory (e/d (tactic.slow-world-thms
                           tactic.world-thms-okp)))))



(defund tactic.slow-world-list-thms (x)
  (declare (xargs :guard (tactic.world-listp x)))
  (if (consp x)
      (app (tactic.slow-world-list-thms (cdr x))
           (tactic.slow-world-thms (car x)))
    nil))

(defund tactic.world-list-thms (x acc)
  (declare (xargs :guard (and (tactic.world-listp x)
                              (true-listp acc))))
  (if (consp x)
      (tactic.world-list-thms (cdr x)
                              (tactic.world-thms (car x) acc))
    acc))

(defthm true-listp-of-tactic.world-list-thms
  (implies (force (true-listp acc))
           (true-listp (tactic.world-list-thms x acc)))
  :hints(("Goal" :in-theory (enable tactic.world-list-thms))))

(defthm tactic.world-list-thms-removal
  (implies (force (true-listp acc))
           (equal (tactic.world-list-thms x acc)
                  (app (tactic.slow-world-list-thms x)
                       acc)))
  :hints(("Goal" :in-theory (enable tactic.world-list-thms
                                    tactic.slow-world-list-thms))))

(defthm tactic.slow-world-list-thms-correct
  (equal (subsetp (tactic.slow-world-list-thms x) thms)
         (tactic.world-list-thms-okp x thms))
  :hints(("Goal"
          :in-theory (e/d (tactic.slow-world-list-thms
                           tactic.world-list-thms-okp)))))



(defund tactic.slow-world-partial-thms (x)
  (declare (xargs :guard (tactic.worldp x)))
  (rw.slow-theory-map-thms (tactic.world->theories x)))

(defund tactic.world-partial-thms (x acc)
  (declare (xargs :guard (and (tactic.worldp x)
                              (true-listp acc))))
  (rw.theory-map-thms (tactic.world->theories x) acc))

(defthm true-listp-of-tactic.world-partial-thms
  (implies (force (true-listp acc))
           (true-listp (tactic.world-partial-thms x acc)))
  :hints(("Goal" :in-theory (enable tactic.world-partial-thms))))

(defthm tactic.world-partial-thms-removal
  (implies (force (true-listp acc))
           (equal (tactic.world-partial-thms x acc)
                  (app (tactic.slow-world-partial-thms x)
                       acc)))
  :hints(("Goal" :in-theory (enable tactic.world-partial-thms
                                    tactic.slow-world-partial-thms))))

(defthm tactic.slow-world-partial-thms-correct
  (implies (subsetp (tactic.slow-world-partial-thms x) thms)
           (equal (tactic.world-thms-okp x thms)
                  (rw.rule-list-env-okp (tactic.world->allrules x) thms)))
  :hints(("Goal"
          :in-theory (e/d (tactic.slow-world-partial-thms
                           tactic.world-thms-okp)))))




(defund tactic.slow-world-list-partial-thms (x)
  (declare (xargs :guard (tactic.world-listp x)))
  (if (consp x)
      (app (tactic.slow-world-list-partial-thms (cdr x))
           (tactic.slow-world-partial-thms (car x)))
    nil))

(defund tactic.world-list-partial-thms (x acc)
  (declare (xargs :guard (and (tactic.world-listp x)
                              (true-listp acc))))
  (if (consp x)
      (tactic.world-list-partial-thms (cdr x)
                                      (tactic.world-partial-thms (car x) acc))
    acc))

(defthm true-listp-of-tactic.world-list-partial-thms
  (implies (force (true-listp acc))
           (true-listp (tactic.world-list-partial-thms x acc)))
  :hints(("Goal" :in-theory (enable tactic.world-list-partial-thms))))

(defthm tactic.world-list-partial-thms-removal
  (implies (force (true-listp acc))
           (equal (tactic.world-list-partial-thms x acc)
                  (app (tactic.slow-world-list-partial-thms x)
                       acc)))
  :hints(("Goal" :in-theory (enable tactic.world-list-partial-thms
                                    tactic.slow-world-list-partial-thms))))

(defthm tactic.slow-world-list-partial-thms-correct
  (implies (and (subsetp (tactic.slow-world-list-partial-thms x) thms)
                (force (tactic.world-list-compatiblep-hack x))
                (force (consp x)))
           (equal (tactic.world-list-thms-okp x thms)
                  (rw.rule-list-env-okp (tactic.world->allrules (car x)) thms)))
  :hints(("Goal"
          :in-theory (e/d (tactic.world-list-compatiblep-hack
                           tactic.slow-world-list-partial-thms
                           tactic.world-list-thms-okp)))))





(defund tactic.world-list-defs (x)
  (declare (xargs :guard (tactic.world-listp x)))
  (if (consp x)
      (revappend (tactic.world->defs (car x))
                 (tactic.world-list-defs (cdr x)))
    nil))

(defthm true-listp-of-tactic.world-list-defs
  (true-listp (tactic.world-list-defs x))
  :hints(("Goal" :in-theory (enable tactic.world-list-defs))))

(defthm tactic.world-list-defs-correct
  (equal (subsetp (tactic.world-list-defs x) axioms)
         (tactic.world-list-axioms-okp x axioms))
  :hints(("Goal"
          :in-theory (enable tactic.world-list-defs
                             tactic.world-list-axioms-okp
                             tactic.world-axioms-okp))))

(defthm tactic.world-list-partial-defs-correct
  (implies (and (tactic.world-list-compatiblep-hack x)
                (consp x))
           (equal (subsetp (tactic.world->defs (car x)) axioms)
                  (tactic.world-list-axioms-okp x axioms)))
  :hints(("Goal" :in-theory (enable tactic.world-axioms-okp
                                    tactic.world-list-axioms-okp
                                    tactic.world-list-compatiblep-hack))))



(defund tactic.fast-world-list-env-okp (x axioms thms)
  (declare (xargs :guard (and (tactic.world-listp x)
                              (logic.formula-listp axioms)
                              (logic.formula-listp thms))))
  (if (and (consp x)
           (tactic.world-list-compatiblep-hack x))
      (let* ((my-thms (tactic.world-list-partial-thms x nil))
             (my-thms (rw.rule-list-thms (tactic.world->allrules (car x)) my-thms))
             (my-defs (tactic.world->defs (car x))))
        (and (ordered-list-subsetp (mergesort my-thms) (mergesort thms))
             (ordered-list-subsetp (mergesort my-defs) (mergesort axioms))))
    (ACL2::prog2$
     (ACL2::cw "Performance note: fast-world-list-env-okp can't use compatibility hack.~%")
     (let* ((my-thms (tactic.world-list-thms x nil))
            (my-defs (tactic.world-list-defs x)))
       (and (ordered-list-subsetp (mergesort my-thms) (mergesort thms))
            (ordered-list-subsetp (mergesort my-defs) (mergesort axioms)))))))

(defthmd lemma-1-for-tactic.fast-world-list-env-okp-lemma
  (implies (TACTIC.WORLD-LIST-THMS-OKP X THMS)
           (SUBSETP (TACTIC.SLOW-WORLD-LIST-PARTIAL-THMS X) THMS))
  :hints(("Goal"
          :in-theory (enable tactic.world-list-thms-okp
                             tactic.world-thms-okp
                             TACTIC.SLOW-WORLD-LIST-PARTIAL-THMS
                             tactic.slow-world-partial-thms))))

(defthmd lemma-2-for-tactic.fast-world-list-env-okp-lemma
  (implies (tactic.world-list-thms-okp x thms)
           (rw.rule-list-env-okp (tactic.world->allrules (first x)) thms))
  :hints(("Goal"
          :in-theory (enable tactic.world-list-thms-okp
                             tactic.world-thms-okp))))

(defthmd tactic.fast-world-list-env-okp-lemma
  (equal (tactic.fast-world-list-env-okp x axioms thms)
         (and (tactic.world-list-axioms-okp x axioms)
              (tactic.world-list-thms-okp x thms)))
  :hints(("Goal"
          :in-theory (e/d (tactic.fast-world-list-env-okp
                           lemma-1-for-tactic.fast-world-list-env-okp-lemma
                           lemma-2-for-tactic.fast-world-list-env-okp-lemma
                           )))))

(defthm tactic.fast-world-list-env-okp-correct
  (equal (tactic.fast-world-list-env-okp x axioms thms)
         (tactic.world-list-env-okp x axioms thms))
  :hints(("Goal" :in-theory (enable tactic.fast-world-list-env-okp-lemma
                                    tactic.world-list-env-okp-redefinition))))




;; Here are some performance comparisons, using level9/symmetry.
;;
;; (defun tactic.world-list-env-okp-wrapper (x axioms thms)   ;; to avoid guards
;;   (declare (xargs :mode :program))
;;   (tactic.world-list-env-okp x axioms thms))
;;
;; (defun tactic.fast-world-list-env-okp-wrapper (x axioms thms)   ;; to avoid guards
;;   (declare (xargs :mode :program))
;;   (tactic.fast-world-list-env-okp x axioms thms))
;;
;; (acl2::time$
;;  ;; 41.3 seconds, 10 MB
;;  (tactic.world-list-env-okp-wrapper (repeat (tactic.harness->world (acl2::w acl2::state)) 1)
;;                                     (tactic.harness->axioms (acl2::w acl2::state))
;;                                     (tactic.harness->thms (acl2::w acl2::state))))
;;
;; (acl2::time$
;;  ;; 124 seconds, 30 MB
;;  (tactic.world-list-env-okp-wrapper (repeat (tactic.harness->world (acl2::w acl2::state)) 3)
;;                                     (tactic.harness->axioms (acl2::w acl2::state))
;;                                     (tactic.harness->thms (acl2::w acl2::state))))
;;
;; (acl2::time$
;;  ;; .41 seconds, 20 MB
;;  (tactic.fast-world-list-env-okp-wrapper (repeat (tactic.harness->world (acl2::w acl2::state)) 1)
;;                                          (tactic.harness->axioms (acl2::w acl2::state))
;;                                          (tactic.harness->thms (acl2::w acl2::state))))
;;
;; (acl2::time$
;;  ;; .68 seconds, 36 MB
;;  (tactic.fast-world-list-env-okp-wrapper (repeat (tactic.harness->world (acl2::w acl2::state)) 3)
;;                                          (tactic.harness->axioms (acl2::w acl2::state))
;;                                          (tactic.harness->thms (acl2::w acl2::state))))
;;
;; (acl2::time$
;;  ;; .81 seconds, 44 MB
;;  (tactic.fast-world-list-env-okp-wrapper (repeat (tactic.harness->world (acl2::w acl2::state)) 4)
;;                                          (tactic.harness->axioms (acl2::w acl2::state))
;;                                          (tactic.harness->thms (acl2::w acl2::state))))
;;
;; (acl2::time$
;;  ;; 2.2 seconds, 133 MB
;;  (tactic.fast-world-list-env-okp-wrapper (repeat (tactic.harness->world (acl2::w acl2::state)) 15)
;;                                          (tactic.harness->axioms (acl2::w acl2::state))
;;                                          (tactic.harness->thms (acl2::w acl2::state))))

