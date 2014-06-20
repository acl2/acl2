; Dumb Rewriter
; Copyright (C) 2013 Centaur Technology
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
;
; Original authors: Jared Davis <jared@centtech.com>
;                   Sol Swords <sswords@centtech.com>

(in-package "ACL2")
(include-book "std/util/define" :dir :system)

(include-book "std/util/defaggrify-defrec" :dir :system)
(std::defaggrify-defrec rewrite-rule)

(define drw-get-rules ((fn symbolp)
                       (world plist-worldp))
  :returns rules
  (fgetprop fn 'lemmas nil world))

(in-theory (disable rewrite-rule->rune
                    rewrite-rule->hyps
                    rewrite-rule->lhs
                    rewrite-rule->rhs
                    rewrite-rule->equiv
                    rewrite-rule->subclass
                    rewrite-rule->heuristic-info))


;; BOZO should extend defaggrify-defrec to do this sort of thing.

(defmacro make-rewrite-rule (&key rune nume hyps equiv lhs rhs subclass
                                  heuristic-info backchain-limit-lst
                                  var-info match-free)
  `(make-rewrite-rule-fn ,rune ,nume ,hyps ,equiv ,lhs ,rhs ,subclass
                         ,heuristic-info ,backchain-limit-lst
                         ,var-info ,match-free))

(define make-rewrite-rule-fn (rune nume hyps equiv lhs rhs subclass
                                   heuristic-info backchain-limit-lst
                                   var-info match-free)
  :inline t
  (make rewrite-rule :rune rune :nume nume :hyps hyps :equiv equiv :lhs lhs
        :rhs rhs :subclass subclass :heuristic-info heuristic-info
        :backchain-limit-lst backchain-limit-lst :var-info var-info :match-free
        match-free)
  ///
  (defthm weak-rewrite-rule-p-of-make-rewrite-rule-fn
    (weak-rewrite-rule-p (make-rewrite-rule-fn
                          rune nume hyps equiv lhs rhs subclass
                          heuristic-info backchain-limit-lst
                          var-info match-free)))
  (defthm rewrite-rule->hyps-of-make-rewrite-rule-fn
    (equal (rewrite-rule->hyps (make-rewrite-rule-fn
                                rune nume hyps equiv lhs rhs subclass
                                heuristic-info backchain-limit-lst
                                var-info match-free))
           hyps)
    :hints(("Goal" :in-theory (enable rewrite-rule->hyps))))
  (defthm rewrite-rule->lhs-of-make-rewrite-rule-fn
    (equal (rewrite-rule->lhs (make-rewrite-rule-fn
                                rune nume hyps equiv lhs rhs subclass
                                heuristic-info backchain-limit-lst
                                var-info match-free))
           lhs)
    :hints(("Goal" :in-theory (enable rewrite-rule->lhs))))
  (defthm rewrite-rule->rhs-of-make-rewrite-rule-fn
    (equal (rewrite-rule->rhs (make-rewrite-rule-fn
                                rune nume hyps equiv lhs rhs subclass
                                heuristic-info backchain-limit-lst
                                var-info match-free))
           rhs)
    :hints(("Goal" :in-theory (enable rewrite-rule->rhs))))
  (defthm rewrite-rule->equiv-of-make-rewrite-rule-fn
    (equal (rewrite-rule->equiv (make-rewrite-rule-fn
                                rune nume hyps equiv lhs rhs subclass
                                heuristic-info backchain-limit-lst
                                var-info match-free))
           equiv)
    :hints(("Goal" :in-theory (enable rewrite-rule->equiv))))
  (defthm rewrite-rule->subclass-of-make-rewrite-rule-fn
    (equal (rewrite-rule->subclass (make-rewrite-rule-fn
                                rune nume hyps equiv lhs rhs subclass
                                heuristic-info backchain-limit-lst
                                var-info match-free))
           subclass)
    :hints(("Goal" :in-theory (enable rewrite-rule->subclass))))
  (defthm rewrite-rule->heuristic-info-of-make-rewrite-rule-fn
    (equal (rewrite-rule->heuristic-info (make-rewrite-rule-fn
                                rune nume hyps equiv lhs rhs subclass
                                heuristic-info backchain-limit-lst
                                var-info match-free))
           heuristic-info)
    :hints(("Goal" :in-theory (enable rewrite-rule->heuristic-info))))
  (defthm rewrite-rule->rune-of-make-rewrite-rule-fn
    (equal (rewrite-rule->rune (make-rewrite-rule-fn
                                rune nume hyps equiv lhs rhs subclass
                                heuristic-info backchain-limit-lst
                                var-info match-free))
           rune)
    :hints(("Goal" :in-theory (enable rewrite-rule->rune)))))

