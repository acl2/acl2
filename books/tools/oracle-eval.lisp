
; Oracle-eval:  Term evaluation in logic mode via the oracle.

; Copyright (C) 2010 Centaur Technology
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
; Original author: Sol Swords <sswords@centtech.com>

(in-package "ACL2")

;; Oracle-eval is a function that logically just reads the
;; state's oracle to produce a result and an error term.  However,
;; under the hood it actually evaluates the given term under the given
;; alist using simple-translate-and-eval.  This allows logic-mode
;; functions to evaluate a term and use its result heuristically;
;; i.e. nothing is known about what the result will be.

;; The given term can involve free variables bound in alist and also
;; state, but must return a single non-stobj value (i.e. it cannot
;; modify state.)

(defttag oracle-eval)

(remove-untouchable 'read-acl2-oracle t)

(defun oracle-eval (term alist state)
  ":Doc-Section Programming
Evaluate a term and return its result, logically obtained by reading
the state's oracle.~/

General form:
~bv[]
 (oracle-eval term alist state) --> (mv error val state)
~ev[]

In the logic, this function reads from the ACL2 oracle twice, to
obtain the error message, if any, and the value.  In the execution, we
instead evaluate the term and return its result.  We believe this is
sound.

The term can involve free variables that appear in the alist, and can
also take state, but it must return a single non-stobj value.
Therefore, it cannot modify state.~/~/"
  (declare (Xargs :guard t
                  :stobjs state
                  :guard-hints (("goal" :in-theory (enable read-acl2-oracle))))
           (ignorable term alist))
  (mv-let (err1 eval-error state)
    (read-acl2-oracle state)
    (mv-let (err2 evaluation state)
      (read-acl2-oracle state)
      (cond ((or err1 err2)
             (mv "Evaluation mysteriously failed (oracle empty)~%"
                 nil state))
            (eval-error
             (mv eval-error nil state))
            (t (mv nil evaluation state))))))

(defthm state-p1-of-read-acl2-oracle
  (implies (state-p1 state)
           (state-p1 (mv-nth 2 (read-acl2-oracle state))))
  :hints(("Goal" :in-theory (enable read-acl2-oracle))))

(defthm state-p1-of-oracle-eval
  (implies (state-p1 state)
           (state-p1 (mv-nth 2 (oracle-eval term alist state)))))

(in-theory (disable oracle-eval))

(progn!
 (set-raw-mode t)
 (defun oracle-eval (term alist state)
   (mv-let (erp translation-and-val state)
     (simple-translate-and-eval
      term alist '(state) "The given term" 'oracle-eval (w state) state t)
     (if erp
         (mv erp nil state)
       (mv nil (cdr translation-and-val) state)))))
