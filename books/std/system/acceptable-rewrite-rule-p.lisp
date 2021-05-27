; Copyright (C) 2016, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This book introduces a Boolean-valued version of chk-acceptable-rewrite-rule,
; returning t when the form of the proposed rewrite rule is acceptable.  Note
; that it avoids the call chk-rewrite-rule-warnings that is found in
; chk-rewrite-rule-warnings.

(in-package "ACL2")

(program)

(defun acceptable-rewrite-rule-p1 (name lst ens wrld)

; Based on ACL2 function chk-acceptable-rewrite-rule1.  Thus:

; Each element of lst is a pair, (hyps . concl) and we check that each
; such pair, when interpreted as the term (implies (and . hyps)
; concl), generates a legal :REWRITE rule.

  (cond
   ((null lst) t)
   (t (mv-let
        (msg eqv lhs rhs ttree)

; J Moore 8/22/2020: Modified call below when new first argument, qc-flg, was added.  By
; specifying qc-flg = nil we require name to be a :rewrite rule rather than
; a :rewrite-quoted-constant rule.

        (interpret-term-as-rewrite-rule nil        ; qc-flg 
                                        name
                                        (caar lst) ; hyps
                                        (cdar lst) ; concl
                                        nil        ; ctx
                                        ens wrld)
        (declare (ignore eqv lhs rhs ttree))
        (and (null msg)
             (acceptable-rewrite-rule-p1 name (cdr lst) ens wrld))))))

(defun acceptable-rewrite-rule-p (term ens wrld)

; Based on ACL2 function chk-acceptable-rewrite-rule.

  (acceptable-rewrite-rule-p1 :some-proposed-rewrite-rule
                              (unprettyify (remove-guard-holders term wrld))
                              ens wrld))
