; Copyright (C) 2014, ForrestHunt, Inc.
; Written by Matt Kaufmann, August, 2014
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(include-book "misc/expander" :dir :system)

; See centaur/regression/composed-stv.lsp for an example of the following
; tool's usage.

(defmacro normalize-lhs (general name1 name2
                                 &key
                                 hyp
                                 lhs
                                 stv-simvar-inputs-to-bits-open-disabledp)
  (let ((hyps
         (case-match hyp
           (('and . x) x)
           (& (list hyp))))
        (hints `(("Goal"
                  :in-theory
                  (union-theories '(return-last)
                                  ,(if stv-simvar-inputs-to-bits-open-disabledp
                                       '(set-difference-theories
                                         (stv-decomp-theory)
                                         '(stv-simvar-inputs-to-bits-open))
                                     '(stv-decomp-theory)))))))
    `(make-event
      (er-let* ((lst-lst (symsim ,lhs ,hyps
                                 :hints ,hints)))
        (cond
         ((cdr lst-lst)
          (er soft 'defthm-stv?
              "Sorry, got two or more goals."))
         (t
          (let* ((lst (car lst-lst))
                 (new-lhs (caddr lst)))
            (value (list 'progn
                         (list 'defthmd ',name1
                               (list 'implies
                                     (cons 'and ',hyps)
                                     (list 'equal ',lhs new-lhs))
                               :hints ',hints)
                         (list 'defthmd ',name2
                               (list 'implies
                                     (cons 'and ',hyps)
                                     new-lhs)
                               :hints
                               '(("Goal"
                                  :use
                                  (,general ,name1)
                                  :in-theory
                                  (theory 'minimal-theory)))))))))))))

