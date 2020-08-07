; Copyright (C) 2014, ForrestHunt, Inc.
; Written by Matt Kaufmann, August, 2014
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(include-book "misc/simp" :dir :system)

; See centaur/regression/composed-stv.lsp for an example of the following
; tool's usage.

; TODO:
;
; -- localize name1 inside an enapsulate.  Call it lemma-something
; -- rename "lhs" to "target"
; -- get rid of need for stv-simvar-inputs-to-bits-open-disabledp

(defmacro normalize-lhs (general target-name
                                 &key
                                 hyp
                                 lhs
                                 verbose)
  (let ((hyps
         (case-match hyp
           (('and . x) x)
           (& (list hyp))))
        (hints `(("Goal"
                  :in-theory (theory 'minimal-theory)) ; beta-reduce lets
                 ("Goal'"
                  :in-theory
                  (union-theories '(return-last)
                                  (stv-decomp-theory))))))
    `(make-event
      (er-let* ((term-hyps-pairs (simp ,lhs ,hyps
                                       :hints ,hints
                                       :verbose ,verbose
                                 ;;:inhibit-output nil ; optional (and not implemented)
                                 )))
        (cond
         ((cdr term-hyps-pairs)
          (er soft 'defthm-stv?
              "Sorry, got two or more goals."))
         (t
          (let* ((new-lhs (caar term-hyps-pairs))
                 (new-hyps (cdar term-hyps-pairs)))
            (declare (ignorable new-hyps))
            (value (list 'encapsulate
                         ()
                         (list 'local
                               (list 'defthmd 'normalize-lhs-generated-lemma
                                     (list 'implies
                                           (cons 'and ',hyps)
                                           (list 'equal ',lhs new-lhs))
                                     :hints ',hints))
                         (list 'defthmd ',target-name
                               (list 'implies
                                     (cons 'and ',hyps)
                                     new-lhs)
                               :hints
                               '(("Goal"
                                  :use
                                  (,general normalize-lhs-generated-lemma)
                                  :in-theory
                                  (theory 'minimal-theory)))))))))))))
