
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

;; This book sets up oracle-eval as a constrained function, with the proper
;; guards and constraints so that real-oracle-eval, defined in
;; oracle-eval-real.lisp, can be attached to it.

;; real-oracle-eval evaluates an input term under an alist, but logically just
;; reads the ACL2 oracle.  However, defining this requires a trust tag, and we
;; wish to allow functions to be defined using oracle-eval without requiring
;; this ttag.  This book allows the following usage model:

;; Include oracle-eval.lisp and define any functions in terms of oracle-eval.
;; This does NOT require a ttag.  However, if these functions are run as-is,
;; oracle-eval will return a useless default value,
;; (MV "See :DOC FAKE-ORACLE-EVAL" NIL STATE).

;; When the real oracle-eval is needed, run the macro
;; (allow-real-oracle-eval).  This includes the real-oracle-eval book, which
;; introduces a ttag and attaches real-oracle-eval to oracle-eval.  Now when
;; oracle-eval is run, the attachment is executed and the real result of
;; evaluating the given term under the alist is returned.

(encapsulate
  (((oracle-eval * * state) => (mv * * state)))

  (local (defun oracle-eval (term alist state)
           (declare (ignore term alist)
                    (xargs :guard t
                           :stobjs state))
           (mv nil nil state)))

  (defthm state-p1-of-oracle-eval
    (implies (state-p1 state)
             (state-p1 (mv-nth 2 (oracle-eval term alist state))))))

(defdoc oracle-eval
  ":Doc-Section Programming
Evaluate a term and return its result, logically obtained by reading
the state's oracle.~/

General form:
~bv[]
 (oracle-eval term alist state) --> (mv error val state)
~ev[]

NOTE: Oracle-eval will not operate as intended until the form
~c[(ALLOW-REAL-ORACLE-EVAL)] is executed at the top level.  However, this
introduces a trust tag.  Ideally, functions should be coded so that
oracle-eval is used only heuristically, so that they can work even
without the correct operation of oracle-eval.

In the logic, this function reads from the ACL2 oracle twice, to
obtain the error message, if any, and the value.  In the execution, we
instead evaluate the term and return its result.  We believe this is
sound.

The term can involve free variables that appear in the alist, and can
also take state, but it must return a single non-stobj value.
Therefore, it cannot modify state.~/

Oracle-eval is a constrained function, and as such has no execution
semantics itself.  Instead, an executable version is attached to it
 (see ~il[DEFATTACH]).  By default, this executable version doesn't do
anything interesting, because a trust tag is necessary to allow
oracle-eval to function as intended.  Running
~c[(ALLOW-REAL-ORACLE-EVAL)] introduces a trust tag and an attachment
that runs the \"real\" oracle-eval. ~/")


(defconst *fake-oracle-eval-msg* "See :DOC FAKE-ORACLE-EVAL")

(defun fake-oracle-eval (term alist state)
  ":Doc-Section Programming
Fake-oracle-eval is the function run by default when ~il[ORACLE-EVAL] is
invoked.~/

Oracle-eval is a constrained function, and fake-oracle-eval is
attached to it by default (see ~il[DEFATTACH]).  Fake-oracle-eval
doesn't do anything useful, but also doesn't require a trust tag.  To
allow oracle-eval to do something useful, run
~c[(ALLOW-REAL-ORACLE-EVAL)]; this introduces a trust tag and attaches the
function real-oracle-eval to oracle-eval.  See ~il[ORACLE-EVAL] for
details.~/~/
"
  (declare (xargs :guard t
                  :stobjs state)
           (ignore term alist))
  (mv *fake-oracle-eval-msg* nil state))

(defattach oracle-eval fake-oracle-eval)

#||

;; Fool dependency scanners:
(include-book "oracle-eval-real")

||#

(defmacro allow-real-oracle-eval ()
  '(progn (include-book
           "tools/oracle-eval-real" :dir :system)
          (defattach oracle-eval real-oracle-eval)))
