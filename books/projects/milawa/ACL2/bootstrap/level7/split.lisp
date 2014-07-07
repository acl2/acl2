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
(include-book "lift")
(include-book "limlift")
(include-book "clean-clauses")
(%interactive)


(%autoprove true-listp-of-clause.clean-clauses
            (%enable default clause.clean-clauses))

(%autoprove forcing-logic.term-list-list-atblp-of-remove-supersets1
            (%autoinduct remove-supersets1 x acc)
            (%restrict default remove-supersets1 (equal todo 'x)))

(%autoprove forcing-logic.term-list-list-atblp-of-remove-supersets
            (%enable default remove-supersets))

(%autoprove forcing-logic.term-list-list-atblp-of-remove-duplicates-list
            (%cdr-induction x))

(%autoprove forcing-logic.term-list-list-atblp-of-clause.remove-absurd-terms-from-clauses
            (%cdr-induction x))

(%autoprove logic.term-list-list-atblp-of-third-of-clause.clean-clauses
            (%enable default clause.clean-clauses))

(%autoprove forcing-clause.simple-term-list-listp-of-remove-supersets1
            (%autoinduct remove-supersets1 x acc)
            (%restrict default remove-supersets1 (equal todo 'x)))

(%autoprove forcing-clause.simple-term-list-listp-of-remove-supersets
            (%enable default remove-supersets))

(%autoprove forcing-clause.simple-term-list-listp-of-remove-duplicates-list
            (%cdr-induction x))

(%autoprove forcing-clause.simple-term-list-listp-of-clause.remove-absurd-terms-from-clauses
            (%cdr-induction x))

(%autoprove forcing-clause.simple-term-list-listp-of-clause.remove-complement-clauses
            (%cdr-induction x))

(%autoprove forcing-clause.simple-term-list-listp-of-clause.remove-obvious-clauses
            (%cdr-induction x))

(%autoprove forcing-clause.simple-termp-of-clause.negative-term-guts
            (%enable default
                     clause.negative-termp
                     clause.negative-term-guts))

(%autoprove forcing-clause.simple-termp-of-clause.normalize-nots-term
            (%autoinduct clause.normalize-nots-term)
            (%restrict default clause.normalize-nots-term (equal x 'x)))

(%autoprove forcing-clause.simple-term-listp-of-clause.normalize-nots-term-list
            (%cdr-induction x))

(%autoprove forcing-clause.simple-term-list-listp-of-clause.normalize-nots-clauses
            (%cdr-induction x))

(%autoprove clause.simple-term-list-listp-of-third-of-clause.clean-clauses
            (%enable default clause.clean-clauses))



(%autoadmit clause.split)

(%autoprove true-listp-of-clause.split
            ;; BOZO we don't want this theorem.  We want true-listp of cdr.  Oh well,
            ;; I'll prove this one anyway.
            (%enable default clause.split))

(%autoprove forcing-logic.term-list-listp-of-cdr-of-clause.split
            (%enable default clause.split))

(%autoprove forcing-logic.term-list-list-atblp-of-cdr-of-clause.split
            (%enable default clause.split))

(%autoprove forcing-cons-listp-of-cdr-of-clause.split
            (%enable default clause.split))


;; We don't bother to prove this.  Maybe we should, eventually.
;; (%autoprove forcing-clause.simple-term-list-listp-of-clause.split-of-cdr-of--clause.lift-clause
;;            (%enable default clause.split))


(%autoadmit clause.split-list)

(%autoprove clause.split-list-when-not-consp
            (%restrict default clause.split-list (equal x 'x)))

(%autoprove clause.split-list-of-cons
            (%restrict default clause.split-list (equal x '(cons a x))))

(%autoprove true-listp-of-cdr-of-clause.split-list
            (%cdr-induction x))

(%deflist logic.term-list-list-listp (x)
  (logic.term-list-listp x))

(%deflist logic.term-list-list-list-atblp (x atbl)
  (logic.term-list-list-atblp x atbl))

(%autoprove forcing-logic.term-list-list-listp-of-cdr-of-clause.split-list
            (%cdr-induction x))

(%autoprove forcing-logic.term-list-list-list-atblp-of-cdr-of-clause.split-list
            (%cdr-induction x))

(%deflist cons-list-listp (x)
          (cons-listp x))

(%autoprove forcing-cons-list-listp-of-cdr-of-clause.split-list
            (%cdr-induction x))