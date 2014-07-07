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
(include-book "lifted-termp")
(include-book "complementary")
(%interactive)


;; BOZO move this to arithmetic

(defthm |(zp (+ 1 a))|
  ;; Why have this silly rule?  It's useful when the more expensive arithmetic
  ;; rules are disabled.  For example, (= 0 (+ a b)) introduces case-splits.
  ;; Yet we often need a fact like this in inductive proofs where some count is
  ;; being decremented.
  (equal (zp (+ 1 a))
         nil))

(%autoprove |(zp (+ 1 a))|)





(%autoadmit clause.split-count)

(%autoprove natp-of-clause.split-count
            (%restrict default clause.split-count (equal x 'x)))

(%autoprove |(< 0 (clause.split-count x))|
            (%restrict default clause.split-count (equal x 'x)))

(%autoprove clause.split-count-when-clause.negative-termp
            (%restrict default clause.split-count (equal x 'x)))

(%autoprove clause.split-count-when-if
            (%restrict default clause.split-count (equal x 'x)))

(%autoadmit clause.split-count-list)

(%autoprove clause.split-count-list-when-not-consp
            (%restrict default clause.split-count-list (equal x 'x)))

(%autoprove clause.split-count-list-of-cons
            (%restrict default clause.split-count-list (equal x '(cons a x))))

(%autoprove natp-of-clause.split-count-list
            (%restrict default clause.split-count-list (equal x 'x)))








;; BOZO consider moving this to a lower level, particularly for the builder.

(%autoadmit clause.aux-split-trivial-branchp)

(%autoprove booleanp-of-clause.aux-split-trivial-branchp
            (%enable default clause.aux-split-trivial-branchp))

(defsection clause.aux-split-trivial-branch-bldr
  (%autoadmit clause.aux-split-trivial-branch-bldr)
  (local (%enable default
                  clause.aux-split-trivial-branchp
                  clause.aux-split-trivial-branch-bldr
                  clause.aux-split-goal))
  (%autoprove logic.appealp-of-clause.aux-split-trivial-branch-bldr)
  (%autoprove logic.conclusion-of-clause.aux-split-trivial-branch-bldr)
  (%autoprove logic.proofp-of-clause.aux-split-trivial-branch-bldr))




(local (%disable default
                 expensive-arithmetic-rules
                 expensive-arithmetic-rules-two
                 type-set-like-rules
                 formula-decomposition
                 expensive-term/formula-inference
                 expensive-subsetp-rules
                 unusual-consp-rules))

(%autoadmit clause.aux-split)


;; (defmacro %clause.aux-split-induction (todo done)
;;   `(%induct (clause.split-count-list ,todo)
;;             ((not (consp ,todo))
;;              nil)
;;             ((and (consp ,todo)
;;                   (clause.negative-termp (car ,todo))
;;                   (clause.negative-termp (clause.negative-term-guts (car ,todo))))
;;              (((,todo (cons (clause.negative-term-guts (clause.negative-term-guts (car ,todo)))
;;                             (cdr ,todo))))))
;;             ((and (consp ,todo)
;;                   (clause.negative-termp (car ,todo))
;;                   (not (clause.negative-termp (clause.negative-term-guts (car ,todo))))
;;                   (logic.functionp (clause.negative-term-guts (car ,todo)))
;;                   (equal (logic.function-name (clause.negative-term-guts (car ,todo))) 'if)
;;                   (equal (len (logic.function-args (clause.negative-term-guts (car ,todo)))) 3))
;;              (((,todo (cons (logic.function 'not (list (first (logic.function-args (clause.negative-term-guts (car ,todo))))))
;;                             (cons (logic.function 'not (list (second (logic.function-args (clause.negative-term-guts (car ,todo))))))
;;                                   (cdr ,todo)))))
;;               ((,todo (cons (first (logic.function-args (clause.negative-term-guts (car ,todo))))
;;                             (cons (logic.function 'not (list (third (logic.function-args (clause.negative-term-guts (car ,todo))))))
;;                                   (cdr ,todo)))))))
;;             ((and (consp ,todo)
;;                   (not (clause.negative-termp (car ,todo)))
;;                   (logic.functionp (car ,todo))
;;                   (equal (logic.function-name (car ,todo)) 'if)
;;                   (equal (len (logic.function-args (car ,todo))) 3))
;;              (((,todo (cons (logic.function 'not (list (first (logic.function-args (car ,todo)))))
;;                             (cons (second (logic.function-args (car ,todo)))
;;                                   (cdr ,todo)))))
;;               ((,todo (cons (first (logic.function-args (car ,todo)))
;;                             (cons (third (logic.function-args (car ,todo)))
;;                                   (cdr ,todo)))))))
;;             ((and (consp ,todo)
;;                   (clause.negative-termp (car ,todo))
;;                   (not (clause.negative-termp (clause.negative-term-guts (car ,todo))))
;;                   (not (and (logic.functionp (clause.negative-term-guts (car ,todo)))
;;                             (equal (logic.function-name (clause.negative-term-guts (car ,todo))) 'if)
;;                             (equal (len (logic.function-args (clause.negative-term-guts (car ,todo)))) 3))))
;;              (((,todo (cdr ,todo))
;;                (,done (cons (logic.function 'not (list (clause.negative-term-guts (car ,todo)))) ,done)))))
;;             ((and (consp ,todo)
;;                   (not (clause.negative-termp (car ,todo)))
;;                   (not (and (logic.functionp (car ,todo))
;;                             (equal (logic.function-name (car ,todo)) 'if)
;;                             (equal (len (logic.function-args (car ,todo))) 3))))
;;              (((,todo (cdr ,todo))
;;                (,done (cons (car ,todo) ,done)))))))



(%autoprove true-listp-of-clause.aux-split
            (%autoinduct clause.aux-split todo done)
            ;(%clause.aux-split-induction todo done)
            (%restrict default clause.aux-split (equal todo 'todo)))

;; (%autoprove consp-of-clause.aux-split
;;             (%clause.aux-split-induction todo done)
;;             (%restrict default clause.aux-split (equal todo 'todo)))

;; (%autoprove clause.aux-split-under-iff
;;             (%use (%instance (%thm consp-of-clause.aux-split)))
;;             (%disable default consp-of-clause.aux-split [outside]consp-of-clause.aux-split))

(%autoprove forcing-term-list-listp-of-clause.aux-split
            (%autoinduct clause.aux-split todo done)
            ;(%clause.aux-split-induction todo done)
            (%restrict default clause.aux-split (equal todo 'todo)))

(%autoprove forcing-term-list-list-atblp-of-clause.aux-split
            (%autoinduct clause.aux-split todo done)
            ;(%clause.aux-split-induction todo done)
            (%restrict default clause.aux-split (equal todo 'todo)))

(%autoprove forcing-cons-listp-of-clause.aux-split
            (%autoinduct clause.aux-split todo done)
            ;(%clause.aux-split-induction todo done)
            (%restrict default clause.aux-split (equal todo 'todo)))



;; BOZO we don't bother to show that splitting is complete in the sense of the
;; lifted-guts terms.  Maybe we eventually want to do that, but I don't think
;; we will need it for now.

;; (local (%enable default logic.term-formula))
;; (local (%disable default
;;                  equal-of-cons-rewrite
;;                  forcing-equal-of-logic.pequal-rewrite-two
;;                  forcing-equal-of-logic.pnot-rewrite-two
;;                  forcing-equal-of-logic.por-rewrite-two
;;                  forcing-equal-of-logic.pequal-rewrite
;;                  forcing-equal-of-logic.pnot-rewrite
;;                  forcing-equal-of-logic.por-rewrite))

;; (%autoprove clause.aux-split-when-double-negative
;;             (%restrict default clause.aux-split (equal todo '(cons a x))))

;; (%autoprove clause.aux-split-when-negative-1
;;             (%restrict default clause.aux-split (equal todo '(cons a x))))

;; (%autoprove clause.aux-split-when-negative-2
;;             (%restrict default clause.aux-split (equal todo '(cons a x))))

;; (%autoprove clause.aux-split-when-negative-3
;;             (%restrict default clause.aux-split (equal todo '(cons a x))))

;; (%autoprove clause.aux-split-when-negative-4
;;             (%restrict default clause.aux-split (equal todo '(cons a x))))

;; (%autoprove clause.aux-split-when-positive-1
;;             (%restrict default clause.aux-split (equal todo '(cons a x))))

;; (%autoprove clause.aux-split-when-positive-2
;;             (%restrict default clause.aux-split (equal todo '(cons a x))))

;; (%autoprove clause.aux-split-when-positive-3
;;             (%restrict default clause.aux-split (equal todo '(cons a x))))

;; (%autoprove clause.aux-split-when-positive-4
;;             (%restrict default clause.aux-split (equal todo '(cons a x))))

;; (%autoprove clause.aux-split-when-not-consp
;;             (%restrict default clause.aux-split (equal todo 'todo)))

;; (%create-theory clause.aux-split-openers)
;; (%enable clause.aux-split-openers
;;          clause.aux-split-when-double-negative
;;          clause.aux-split-when-negative-1
;;          clause.aux-split-when-negative-1
;;          clause.aux-split-when-negative-2
;;          clause.aux-split-when-negative-3
;;          clause.aux-split-when-negative-4
;;          clause.aux-split-when-positive-1
;;          clause.aux-split-when-positive-2
;;          clause.aux-split-when-positive-3
;;          clause.aux-split-when-positive-4
;;          clause.aux-split-when-not-consp)






;; BOZO this does NOT belong here.  It's in aux-split-bldr.lisp but it really belongs
;; in utilities/utilities.

(%autoprove len-when-not-consp-of-cdr-cheap)


