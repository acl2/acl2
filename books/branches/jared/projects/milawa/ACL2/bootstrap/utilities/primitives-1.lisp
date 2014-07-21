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
(include-book "prepare-for-bootstrapping")
(%interactive)


(%autoadmit nfix)
(%autoadmit <=)
(%autoadmit zp)
(%autoadmit min)
(%autoadmit max)
(%autoadmit max3)

(%enable default min max max3 <=)

(%autoadmit booleanp)




;; (ACL2::trace! (tactic.apply-strategy-step :entry (let* ((args acl2::arglist)
;;                                                         (step (first args))
;;                                                         (blimit (third args))
;;                                                         (rlimit (fourth args))
;;                                                         (rw-n (acl2::sixth args)))
;;                                                    (list step '<skelly> blimit rlimit '<control> rw-n))
;;                                           :exit (let* ((values acl2::values)
;;                                                        (result (car values)))
;;                                                   (if result
;;                                                       '<skelly-result>
;;                                                     'fail))))


;; (ACL2::trace! (tactic.auto-tac :entry (let* ((args acl2::arglist)
;;                                              (current-strat (second args))
;;                                              (global-strat (third args)))
;;                                         (list current-strat global-strat))
;;                                :exit '<result>))

(defsection equal-of-booleans-rewrite
  ;; I add a syntaxp restriction here.  If you just use %restrict later, you
  ;; can't disable equal-of-booleans-rewrite because our disabling code works
  ;; by the whole rule instead of by its name.  Maybe we should redo that,
  ;; since this is kind of retarded.
  (%prove (%rule equal-of-booleans-rewrite
                 :type inside
                 :hyps (list (%hyp (booleanp x) :limit 1)
                             (%hyp (booleanp y) :limit 1))
                 :lhs (equal x y)
                 :rhs (iff x y)
                 :syntax ((not (logic.term-< y x)))))
  (local (%enable default booleanp))
  (%auto)
  (%qed)
  (%enable default equal-of-booleans-rewrite))

(%autoprove booleanp-of-booleanp
            (%enable default booleanp))

(%autoprove booleanp-of-equal
            (%enable default booleanp))

(%autoprove booleanp-of-not
            (%use (build.axiom (definition-of-not))))

(%autoprove booleanp-of-iff)

(%autoprove booleanp-of-zp
            (%enable default zp))


;; Crewrite automatically converts (if x nil t) to (not x).  We now provide
;; rewrite rules to convert the other not-variants to (not x) as well.

(defsection equal-of-nil-one
  ;; No equivalent in ACL2
  (%prove (%rule equal-of-nil-one
                 :lhs (equal x nil)
                 :rhs (not x)))
  (%auto)
  (%qed)
  (%enable default equal-of-nil-one)
  (%raw-add-rule (%rule [outside]equal-of-nil-one
                        :type outside
                        :lhs (equal x nil)
                        :rhs (not x))))

(defsection equal-of-nil-two
  ;; No equivalent in ACL2
  (%prove (%rule equal-of-nil-two
                 :lhs (equal nil x)
                 :rhs (not x)))
  (%auto)
  (%qed)
  (%enable default equal-of-nil-two)
  (%raw-add-rule (%rule [outside]equal-of-nil-two
                        :type outside
                        :lhs (equal nil x)
                        :rhs (not x))))

(defsection iff-of-nil-one
  ;; No equivalent in ACL2
  (%prove (%rule iff-of-nil-one
                 :lhs (iff x nil)
                 :rhs (not x)))
  (%auto)
  (%qed)
  (%enable default iff-of-nil-one)
  (%raw-add-rule (%rule [outside]iff-of-nil-one
                        :type outside
                        :lhs (iff x nil)
                        :rhs (not x))))

(defsection iff-of-nil-two
  ;; No equivalent in ACL2
  (%prove (%rule iff-of-nil-two
                 :lhs (iff nil x)
                 :rhs (not x)))
  (%auto)
  (%qed)
  (%enable default iff-of-nil-two)
  (%raw-add-rule (%rule [outside]iff-of-nil-two
                        :type outside
                        :lhs (iff nil x)
                        :rhs (not x))))

(defsection iff-of-t-left
  ;; No equivalent in ACL2.  Useful when iff is disabled.
  (%prove (%rule iff-of-t-left
                 :equiv iff
                 :lhs (iff t x)
                 :rhs x))
  (%auto)
  (%qed)
  (%enable default iff-of-t-left)
  (%raw-add-rule (%rule [outside]iff-of-t-left
                        :type outside
                        :equiv iff
                        :lhs (iff t x)
                        :rhs x)))

(defsection iff-of-t-right
  ;; No equivalent in ACL2.  Useful when iff is disabled.
  (%prove (%rule iff-of-t-right
                 :equiv iff
                 :lhs (iff x t)
                 :rhs x))
  (%auto)
  (%qed)
  (%enable default iff-of-t-right)
  (%raw-add-rule (%rule [outside]iff-of-t-right
                        :type outside
                        :equiv iff
                        :lhs (iff x t)
                        :rhs x)))




;; Cons, Car, and Cdr.

(%autoprove booleanp-of-consp
            (%use (build.axiom (axiom-consp-nil-or-t))))

(%autoprove car-when-not-consp
            (%use (build.axiom (axiom-car-when-not-consp))))

(%autoprove cdr-when-not-consp
            (%use (build.axiom (axiom-cdr-when-not-consp))))

(%autoprove car-of-cons
            (%use (build.axiom (axiom-car-of-cons))))

(%autoprove cdr-of-cons
            (%use (build.axiom (axiom-cdr-of-cons))))

;; No equivalent of car-cdr-elim in Milawa.

(%autoprove cons-of-car-and-cdr
            (%use (build.axiom (axiom-cons-of-car-and-cdr))))

(%autoprove equal-of-cons-rewrite
            (%auto :strategy (cleanup split crewrite dist)))

(%autoprove booleanp-of-symbolp
            (%use (build.axiom (axiom-symbolp-nil-or-t))))

(%autoprove booleanp-of-symbol-<
            (%use (build.axiom (axiom-symbol-<-nil-or-t))))

(%autoprove irreflexivity-of-symbol-<
            (%use (build.axiom (axiom-irreflexivity-of-symbol-<))))

(%autoprove antisymmetry-of-symbol-<
            (%use (build.axiom (axiom-antisymmetry-of-symbol-<))))

(%autoprove transitivity-of-symbol-<
            (%use (build.axiom (axiom-transitivity-of-symbol-<))))

(%autoprove trichotomy-of-symbol-<
            (%use (build.axiom (axiom-trichotomy-of-symbol-<))))

(%autoprove symbol-<-completion-left
            (%use (build.axiom (axiom-symbol-<-completion-left))))

(%autoprove symbol-<-completion-right
            (%use (build.axiom (axiom-symbol-<-completion-right))))



;; Reasoning about Types.

(%autoprove booleanp-of-natp
            (%use (build.axiom (axiom-natp-nil-or-t))))

(%autoprove symbolp-when-natp-cheap
            (%use (build.axiom (axiom-disjoint-symbols-and-naturals))))

(%autoprove symbolp-when-consp-cheap
            (%use (build.axiom (axiom-disjoint-symbols-and-conses))))

(%autoprove consp-when-natp-cheap
            (%use (build.axiom (axiom-disjoint-naturals-and-conses))))

(%autoprove booleanp-when-natp-cheap
            (%enable default booleanp))

(%autoprove booleanp-when-consp-cheap
            (%enable default booleanp))

(%autoprove symbolp-when-booleanp-cheap
            (%enable default booleanp))

(defsection cons-under-iff
  ;; Not in utilities/primitives; somehow built into ACL2?
  (%prove (%rule cons-under-iff
                 :equiv iff
                 :lhs (cons x y)
                 :rhs t))
  (%use (build.theorem (theorem-cons-is-not-nil)))
  (%auto)
  (%qed)
  (%enable default cons-under-iff)
  (%raw-add-rule (%rule [outside]cons-under-iff
                        :type outside
                        :equiv iff
                        :lhs (cons x y)
                        :rhs t)))


;; The following rules have no equivalents in ACL2 because there they can be
;; handled with type reasoning.

(defsection equal-of-symbol-and-non-symbol-cheap
  ;; BOZO should we syntactically restrict this rule so that it only fires when x <= y,
  ;; in the term order, so that the symmetry rule fires first?
  (%prove (%rule equal-of-symbol-and-non-symbol-cheap
                 :hyps (list (%hyp (symbolp x) :limit 1)
                             (%hyp (not (symbolp y)) :limit 1))
                 :lhs (equal x y)
                 :rhs nil))
  (%auto)
  (%qed)
  (%enable default equal-of-symbol-and-non-symbol-cheap))

(defsection equal-of-non-symbol-and-symbol-cheap
  (%prove (%rule equal-of-non-symbol-and-symbol-cheap
                 :hyps (list (%hyp (not (symbolp x)) :limit 1)
                             (%hyp (symbolp y) :limit 1))
                 :lhs (equal x y)
                 :rhs nil))
  (%auto)
  (%qed)
  (%enable default equal-of-non-symbol-and-symbol-cheap))

(defsection equal-of-cons-and-non-cons-cheap
  (%prove (%rule equal-of-cons-and-non-cons-cheap
                 :hyps (list (%hyp (consp x) :limit 1)
                             (%hyp (not (consp y)) :limit 1))
                 :lhs (equal x y)
                 :rhs nil))
  (%auto)
  (%qed)
  (%enable default equal-of-cons-and-non-cons-cheap))

(defsection equal-of-non-cons-and-cons-cheap
  (%prove (%rule equal-of-non-cons-and-cons-cheap
                 :hyps (list (%hyp (not (consp x)) :limit 1)
                             (%hyp (consp y) :limit 1))
                 :lhs (equal x y)
                 :rhs nil))
  (%auto)
  (%qed)
  (%enable default equal-of-non-cons-and-cons-cheap))

(defsection equal-of-nat-and-non-nat-cheap
  (%prove (%rule equal-of-nat-and-non-nat-cheap
                 :hyps (list (%hyp (natp x) :limit 1)
                             (%hyp (not (natp y)) :limit 1))
                 :lhs (equal x y)
                 :rhs nil))
  (%auto)
  (%qed)
  (%enable default equal-of-nat-and-non-nat-cheap))

(defsection equal-of-non-nat-and-nat-cheap
  (%prove (%rule equal-of-non-nat-and-nat-cheap
                 :hyps (list (%hyp (not (natp x)) :limit 1)
                             (%hyp (natp y) :limit 1))
                 :lhs (equal x y)
                 :rhs nil))
  (%auto)
  (%qed)
  (%enable default equal-of-non-nat-and-nat-cheap))


(defsection car-when-symbolp-cheap
  ;; This isn't part of ACL2
  (%prove (%rule car-when-symbolp-cheap
                 :hyps (list (%hyp (symbolp x) :limit 0))
                 :lhs (car x)
                 :rhs nil))
  (%use (%instance (%thm car-when-not-consp)))
  (%auto)
  (%qed)
  (%enable default car-when-symbolp-cheap))



(defsection not-of-not-under-iff
  ;; This isn't part of ACL2.
  ;;
  ;; The conditional rewriter doesn't target not, but the unconditional
  ;; rewriter can use this rule so it's still useful.
  (%prove (%rule not-of-not-under-iff
                 :equiv iff
                 :lhs (not (not x))
                 :rhs x))
  (%auto)
  (%qed)
  (%enable default not-of-not-under-iff)
  (%raw-add-rule (%rule [outside]not-of-not-under-iff
                        :type outside
                        :equiv iff
                        :lhs (not (not x))
                        :rhs x)))



;; Rules about Implies.
;;
;; These rules are not found in ACL2.  And, you might wonder what they're doing
;; here, too, since we almost always leave implies enabled.  In some big proofs,
;; particularly mutually-recursive style ones with several implies, a useful
;; size reduction technique is to disable implies until late in the proof to
;; control case splitting.  When we do this, these rules let us simplify some
;; of the more trivial implies statements we run into.

(defsection implies-of-self
  (%prove (%rule implies-of-self
                 :lhs (implies x x)
                 :rhs t))
  (%auto)
  (%qed)
  (%enable default implies-of-self)
  (%raw-add-rule (%rule [outside]implies-of-self
                        :type outside
                        :lhs (implies x x)
                        :rhs t)))

(defsection implies-of-t-left
  (%prove (%rule implies-of-t-left
                 :equiv iff
                 :lhs (implies t x)
                 :rhs x))
  (%auto)
  (%qed)
  (%enable default implies-of-t-left)
  (%raw-add-rule (%rule [outside]implies-of-t-left
                        :type outside
                        :equiv iff
                        :lhs (implies t x)
                        :rhs x)))

(defsection implies-of-t-right
  (%prove (%rule implies-of-t-right
                 :lhs (implies x t)
                 :rhs t))
  (%auto)
  (%qed)
  (%enable default implies-of-t-right)
  (%raw-add-rule (%rule [outside]implies-of-t-right
                        :type outside
                        :lhs (implies x t)
                        :rhs t)))

(defsection implies-of-nil-left
  (%prove (%rule implies-of-nil-left
                 :lhs (implies nil x)
                 :rhs t))
  (%auto)
  (%qed)
  (%enable default implies-of-nil-left)
  (%raw-add-rule (%rule [outside]implies-of-nil-left
                        :type outside
                        :lhs (implies nil x)
                        :rhs t)))

(defsection implies-of-nil-right
  (%prove (%rule implies-of-nil-right
                 :lhs (implies x nil)
                 :rhs (not x)))
  (%auto)
  (%qed)
  (%enable default implies-of-nil-right)
  (%raw-add-rule (%rule [outside]implies-of-nil-right
                        :type outside
                        :lhs (implies x nil)
                        :rhs (not x))))

(defsection booleanp-of-implies
  (%prove (%rule booleanp-of-implies
                 :lhs (booleanp (implies x y))
                 :rhs t))
  (%auto)
  (%qed)
  (%enable default booleanp-of-implies)
  (%raw-add-rule (%rule [outside]booleanp-of-implies
                        :type outside
                        :lhs (booleanp (implies x y))
                        :rhs t)))



;; (ACL2::trace! (rw.cache-lookup :entry (let ((args ACL2::arglist))
;;                                         (list (first args)
;;                                               (second args)
;;                                               '<cache>))
;;                                :exit (let ((args ACL2::arglist)
;;                                            (vals ACL2::values))
;;                                        (if (car vals)
;;                                            (if (equal (first args) (rw.trace->lhs (first vals)))
;;                                                (list 'hit (first vals) 'assms-are (rw.trace->assms (first vals)))
;;                                              (list 'hey-somethings-fucked-up (first vals)))
;;                                          (list 'miss)))))

;; (ACL2::trace! (rw.cache-update :entry (let ((args ACL2::arglist))
;;                                         (list (first args)
;;                                               (rw.trace->rhs (second args))
;;                                               (third args)
;;                                               '<cache>))
;;                                :exit (let ((args ACL2::arglist))
;;                                        (declare (ignore args))
;;                                        (list '<new-cache>))))
