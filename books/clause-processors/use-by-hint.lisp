; Copyright (C) 2009 Centaur Technology
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


;; This is a computed hint that causes a :by hint to be applied to a subgoal
;; when the first hyp in the clause is (use-by-hint thmname).

;; This can enable clause processors to make use of user-provided,
;; pre-proven ACL2 theorems.  For example, assume a clause processor does
;; something with user-provided theorems and the following theorem is provided
;; to it by the user:
;; (defthm foo-thm (implies (bar x) (equal (foo x) 'baz)))
;; In general, to use the fact provided by this theorem, the clause processor
;; must prove this theorem again.  A quick/easy way to do this is to produce
;; the clause
;; `((not (use-by-hint 'foo-thm))
;;   (implies (bar x) (equal (foo x) 'baz)))
;; If the user (or, say, a computed hint that calls the clause processor)
;; ensures that a (use-by-computed-hint clause) fires when ACL2 attempts to
;; prove this clause, it should then be discharged immediately.

;; See also clause-processors/multi-env-trick for additional help with making
;; clause processors that use user-provided lemmas.

(in-package "ACL2")

;; (include-book "join-thms")
(include-book "remove-hyp")
(include-book "std/util/bstar" :dir :system)

;; USE-BY-HINT is t.  Therefore it can be added as a hyp to any subgoal without
;; affecting its truth value.  It serves to signal use-by-computed-hint to give
;; a particular :by hint.
(defun use-by-hint (x)
  (declare (ignore x))
  t)

(in-theory (disable use-by-hint
                    (use-by-hint)
                    (:type-prescription use-by-hint)))


;; The computed hint.  Checks to see if the first literal in the clause is a
;; hyp of the form (use-by-hint 'rulename).  If so, first remove that literal
;; using remove-first-hyp-cp, then give a :by hint with that rule.
(defun use-by-computed-hint (clause)
  (declare (xargs :mode :program))
  (case-match clause
    ((('not ('use-by-hint ('quote rule . &) . &) . &) . &)
     `(:computed-hint-replacement
       ('(:by ,rule :do-not '(preprocess simplify)))
       :clause-processor remove-first-hyp-cp))
    (& nil)))


(defun use-these-hints (x)
  (declare (ignore x))
  t)

(in-theory (disable use-these-hints (use-these-hints)
                    (:type-prescription use-these-hints)))


(defun use-these-hints-hint (clause)
  (case-match clause
    ((('not ('use-these-hints ('quote the-hints . &) . &) . &) . &)
     `(:computed-hint-replacement
       ,the-hints
       :clause-processor remove-first-hyp-cp))
    (& nil)))

;; Note: the use-termhint utility used to be here but has been moved to std/util/termhints.lisp.
