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
(%interactive)

(defthmd lemma-split-up-list-of-quoted-nil
  ;; We normally don't break up constants, but this one gets in the way if we don't.
  (equal (equal x '('nil))
         (and (consp x)
              (equal (car x) ''nil)
              (not (cdr x)))))

(%autoprove lemma-split-up-list-of-quoted-nil)

(local (%enable default lemma-split-up-list-of-quoted-nil))

(%autoadmit clause.simple-negativep)
(%autoadmit clause.simple-negative-guts)

(%autoprove booleanp-of-clause.simple-negativep
            (%enable default clause.simple-negativep))

(%autoprove forcing-logic.termp-of-clause.simple-negative-guts
            (%enable default clause.simple-negativep clause.simple-negative-guts))

(%autoprove forcing-logic.term-atblp-of-clause.simple-negative-guts
            (%enable default clause.simple-negativep clause.simple-negative-guts))

(%autoprove clause.simple-negativep-of-logic.function-of-not
            (%enable default clause.simple-negativep))

(%autoprove clause.negative-termp-when-clause.simple-negativep
            (%enable default clause.simple-negativep clause.negative-termp))

(%autoprove clause.simple-negative-guts-of-logic.function-of-not
            (%enable default clause.simple-negative-guts))

(%autoprove clause.simple-negative-guts-identity
            (%enable default clause.simple-negativep clause.simple-negative-guts))

(%autoprove forcing-clause.simple-negative-guts-under-iff
            (%enable default clause.simple-negativep clause.simple-negative-guts))



(%autoadmit clause.double-negative-free-listp)

(%autoprove clause.double-negative-free-listp-when-not-consp
            (%restrict default clause.double-negative-free-listp (equal x 'x)))

(%autoprove clause.double-negative-free-listp-of-cons
            (%restrict default clause.double-negative-free-listp (equal x '(cons a x))))

(%autoprove booleanp-of-clause.double-negative-free-listp
            (%cdr-induction x))

(%autoprove clause.double-negative-free-listp-of-list-fix
            (%cdr-induction x))

(%autoprove clause.double-negative-free-listp-of-app
            (%cdr-induction x))

(%autoprove clause.double-negative-free-listp-of-rev
            (%cdr-induction x))






#|








;; sweet!  now can we fold in the removing duplicates as well?  hrmn.  this seems
;; to create problems because remove-duplicates does not have nice reversibility
;; properties.  that is, the element order is left up to where the elements occur
;; in the cdr.  that's actually a pretty shitty order to choose.  we might want to
;; redesign remove-duplicates to keep the first one of each element instead



;(defund clause.fast-clean-part1 (x acc)
  (declare (xargs :guard (and (logic.term-list-listp x)
                              (cons-listp x))))
  (if (consp x)
      (let ((normalized-clause (clause.fast-normalize-nots-term-list$ (car x) nil)))
        (if (or (clause.find-obvious-term normalized-clause)
                (clause.find-complementary-literal normalized-clause))
            (clause.fast-clean-part1 (cdr x) acc)
          (clause.fast-clean-part1 (cdr x)
                                   (cons (clause.fast-remove-absurd-terms-from-list$ normalized-clause nil)
                                         acc))))
    acc))

(%autoprove clause.fast-clean-part1-removal
  (implies (force (and (true-listp acc)
                       (logic.term-list-listp x)))
           (equal (clause.fast-clean-part1 x acc)
                  (revappend (clause.remove-absurd-terms-from-clauses
                              (clause.remove-complement-clauses
                               (clause.remove-obvious-clauses
                                (clause.normalize-nots-clauses x))))
                             acc)))
  :hints(("Goal"
          :in-theory (e/d (clause.fast-clean-part1
                           clause.normalize-nots-term-list-of-rev)
                          (rev-of-clause.normalize-nots-term-list)))))


;(defund clause.fast-clean-clauses (x)
  (declare (xargs :guard (and (logic.term-list-listp x)
                              (cons-listp x))))
  (let ((pass4 (clause.fast-clean-part1 x nil)))
    (if (not (cons-listp pass4))
        ;; Some clause is absurd.
        (list t nil (list-fix x))
      (let* ((pass5 (fast-remove-duplicates-list$ pass4 nil))
             (pass6 (remove-supersets pass5)))
        (list nil (not (disabled-equal x pass6)) pass6)))))





(%autoprove clause.fast-clean-clauses-removal
  (implies (force (logic.term-list-listp x))
           (equal (clause.fast-clean-clauses x)
                  (clause.clean-clauses x)))
  :hints(("Goal" :in-theory (e/d (clause.clean-clauses
                                  clause.fast-clean-clauses
                                  clause.normalize-nots-clauses-of-rev
                                  clause.remove-obvious-clauses-of-rev
                                  clause.remove-complement-clauses-of-rev
                                  )
                                 (rev-of-clause.normalize-nots-clauses
                                  rev-of-clause.remove-obvious-clauses
                                  rev-of-clause.remove-complement-clauses
                                  )))))


|#