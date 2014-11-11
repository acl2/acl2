; UBDD Library
; Copyright (C) 2008-2011 Warren Hunt and Bob Boyer
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.
; Significantly revised in 2008 by Jared Davis and Sol Swords.
; Now maintained by Centaur Technology.
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/

; Recommended version of the bdd library.
; Includes the core bdd-creation operations and reasoning about them.

(in-package "ACL2")
(include-book "witness")
(include-book "subset")
(include-book "misc/untranslate-patterns" :dir :system)

(add-untranslate-pattern (q-ite-fn ?x ?y ?z) (q-ite ?x ?y ?z))
(add-untranslate-pattern (q-implies-fn ?x ?y) (q-implies ?x ?y))
(add-untranslate-pattern (q-or-c2-fn ?x ?y) (q-or-c2 ?x ?y))
(add-untranslate-pattern (q-and-c1-fn ?x ?y) (q-and-c1 ?x ?y))
(add-untranslate-pattern (q-and-c2-fn ?x ?y) (q-and-c2 ?x ?y))




(theory-invariant (incompatible (:rewrite |(qs-subset x nil)|)
                                (:rewrite
                                 bdd-equality-is-double-containment)))

(theory-invariant (incompatible (:rewrite |(qs-subset t x)|)
                                (:rewrite
                                 bdd-equality-is-double-containment)))

(theory-invariant (incompatible (:rewrite equal-by-eval-bdds)
                                (:rewrite
                                 bdd-equality-is-double-containment)))


(def-ruleset non-qs-subset-mode-rules '(|(qs-subset x nil)|
                                        |(qs-subset t x)|
                                        equal-by-eval-bdds
                                        eval-bdd-cp-hint))



(defmacro qs-subset-mode (value)
  (declare (xargs :guard (booleanp value)))
  (if value
      '(in-theory (e/d* ((:ruleset qs-subset-mode-rules))
                        ((:ruleset non-qs-subset-mode-rules))))
    '(in-theory (e/d* () ; (:ruleset non-qs-subset-mode-rules))
                      ((:ruleset qs-subset-mode-rules))))))

(qs-subset-mode nil)


(def-ruleset non-q-witness-mode-rules '(equal-by-eval-bdds
                                        eval-bdd-diff-witness
                                        eval-bdd-diff-witness-corr
                                        eval-bdd-when-qs-subset))


(defmacro q-witness-mode (value)
  (declare (xargs :guard (booleanp value)))
  (if value
      '(in-theory (e/d* ((:ruleset q-witness-mode-rules))
                        ((:ruleset non-q-witness-mode-rules))))
    '(in-theory (e/d* () ; ((:ruleset non-q-witness-mode-rules))
                      ((:ruleset q-witness-mode-rules))))))

(q-witness-mode nil)

(theory-invariant (incompatible (:definition eval-bdd-cp-hint)
                                (:rewrite equal-by-eval-bdds)))

(theory-invariant (incompatible (:definition eval-bdd-cp-hint)
                                (:rewrite bdd-equality-is-double-containment)))


