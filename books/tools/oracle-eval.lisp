; Oracle-eval:  Term evaluation in logic mode via the oracle.
; Copyright (C) 2010 Centaur Technology
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

(in-package "ACL2")
(include-book "xdoc/top" :dir :system)

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

(defsection oracle-eval
  :parents (programming)
  :short "Evaluate a term and return its result, logically obtained by reading
the state's oracle."

  :long "<p>Note: for many purposes you may be able to use @(see
magic-ev-funcall) @('ev-fncall-w!') instead of @('oracle-eval').  Although
these alternatives are less flexible, they do not require trust tags.</p>

<p>General form:</p>
@({
    (oracle-eval term alist state) --> (mv error val state)
})

<p>NOTE: Oracle-eval will not operate as intended until the form
@('(ALLOW-REAL-ORACLE-EVAL)') is executed at the top level.  However, this
introduces a trust tag.  Ideally, functions should be coded so that
oracle-eval is used only heuristically, so that they can work even
without the correct operation of oracle-eval.</p>

<p>In the logic, this function reads from the ACL2 oracle twice, to obtain the
error message, if any, and the value.  In the execution, we instead evaluate
the term and return its result.  We believe this is sound.</p>

<p>The term can involve free variables that appear in the alist, and can also
take state, but it must return a single non-stobj value.  Therefore, it cannot
modify state.</p>

<p>Oracle-eval is a constrained function, and as such has no execution
semantics itself.  Instead, an executable version is attached to it
 (see @(see DEFATTACH)).  By default, this executable version doesn't do
anything interesting, because a trust tag is necessary to allow
oracle-eval to function as intended.  Running
@('(ALLOW-REAL-ORACLE-EVAL)') introduces a trust tag and an attachment
that runs the \"real\" oracle-eval.</p>

@(def oracle-eval)"

  (encapsulate
    (((oracle-eval * * state) => (mv * * state)))

    (local (defun oracle-eval (term alist state)
             (declare (ignore term alist)
                      (xargs :guard t
                             :stobjs state))
             (mv nil nil state)))

    (defthm state-p1-of-oracle-eval
      (implies (state-p1 state)
               (state-p1 (mv-nth 2 (oracle-eval term alist state)))))))


(defsection fake-oracle-eval
  :parents (programming)
  :short "@('fake-oracle-eval') is the function run by default when @(see
ORACLE-EVAL) is invoked."
  :long "<p>@('Oracle-eval') is a constrained function, and
@('fake-oracle-eval') is attached to it by default (see @(see DEFATTACH)).</p>

<p>Fake-oracle-eval doesn't do anything useful, but also doesn't require a
trust tag.  To allow oracle-eval to do something useful, run
@('(ALLOW-REAL-ORACLE-EVAL)'); this introduces a trust tag and attaches the
function real-oracle-eval to oracle-eval.</p>

<p>See @(see ORACLE-EVAL) for details.</p>"

  (defconst *fake-oracle-eval-msg* "See :DOC FAKE-ORACLE-EVAL")

  (defun fake-oracle-eval (term alist state)
    (declare (xargs :guard t
                    :stobjs state)
             (ignore term alist))
    (mv *fake-oracle-eval-msg* nil state))

  (defattach oracle-eval fake-oracle-eval))

#||

;; Fool dependency scanners:
(include-book "oracle-eval-real")

||#

(defmacro allow-real-oracle-eval ()
  '(progn (include-book
           "tools/oracle-eval-real" :dir :system)
          (defattach oracle-eval real-oracle-eval)))

(defpointer allow-real-oracle-eval oracle-eval)
