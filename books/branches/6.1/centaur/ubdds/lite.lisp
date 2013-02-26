; UBDD Library
; Copyright (C) 2008-2011 Warren Hunt and Bob Boyer
; Significantly revised in 2008 by Jared Davis and Sol Swords.
; Now maintained by Centaur Technology.
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.

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


