; Copyright (C) 2014, ForrestHunt, Inc.
; Written by Matt Kaufmann, August, 2014
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(include-book "misc/bash" :dir :system)

(program)

(defun simp-pairs (clauses wrld state acc)
  (declare (xargs :stobjs state))
  (cond ((endp clauses)
         (value acc))
        (t (let* ((cl (car clauses))
                  (term (assert$ (consp cl)
                                 (car (last cl))))
                  (hyps (dumb-negate-lit-lst (butlast cl 1))))
             (case-match term
               (('equal lhs '?)
                (simp-pairs (cdr clauses)
                            wrld
                            state
                            (cons (cons (untranslate lhs nil wrld)
                                        (untranslate-lst hyps t wrld))
                                  acc)))
               (& (er soft 'simp
                      "A clause returned was ~x0, which doesn't have a final ~
                       literal of the form ~x1."
                      cl '(equal term ?))))))))

(defmacro simp (lhs hyps &key hints verbose)
  `(er-let* ((clauses (bash-term-to-dnf '(implies (and ,@hyps)
                                                  (equal ,lhs ?))
                                        ',hints
                                        ',verbose
                                        t
                                        state)))
     (simp-pairs clauses (w state) state nil)))
