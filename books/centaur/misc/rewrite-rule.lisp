; Dumb Rewriter
; Copyright (C) 2013 Centaur Technology
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
                    rewrite-rule->nume
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
    :hints(("Goal" :in-theory (enable rewrite-rule->rune))))

  (defthm rewrite-rule->nume-of-make-rewrite-rule-fn
    (equal (rewrite-rule->nume (make-rewrite-rule-fn
                                rune nume hyps equiv lhs rhs subclass
                                heuristic-info backchain-limit-lst
                                var-info match-free))
           nume)
    :hints(("Goal" :in-theory (enable rewrite-rule->nume)))))

