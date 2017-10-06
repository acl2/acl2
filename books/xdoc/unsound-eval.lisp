; XDOC Documentation System for ACL2
; Copyright (C) 2009-2015 Centaur Technology
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
; Original author: Jared Davis <jared@centtech.com>

(in-package "ACL2")
(include-book "std/util/define" :dir :system)
(include-book "tools/include-raw" :dir :system)
(local (include-book "oslib/read-acl2-oracle" :dir :system))

; avoid gcl-cltl1 because it doesn't have handler-case
; cert_param: (ansi-only)

(define unsound-eval
  :parents (interfacing-tools programming-with-state)
  :short "A somewhat robust evaluator."
  ((sexpr "An s-expression to evaluate, typically this should be a well-formed
           ACL2 form without guard violations, etc.  It may mention @(see
           stobj)s.")
   &key (state 'state))
  :returns
  (mv (errmsg "An error @(see acl2::msg) on failure, or @('nil') on success.
               Note that this message is likely to be very terse/unhelpful when
               evaluating @('sexpr') causes any ACL2 error.")
      (values "The list of return values from evaluating @('sexpr'), with
               stobjs elided with their names.")
      (state   state-p1 :hyp (state-p1 state)))
  :long "<p>In the logic, this is implemented as oracle reads, so you can't
prove anything about what it returns.  Even so, it is generally <b>unsound</b>
since it lets you to modify @('state') and other @(see stobj)s without
accounting for how they have been modified.</p>

<p>In the execution, we basically call ACL2's @(tsee trans-eval) function
(technically: @('trans-eval-no-warning')).  But we wrap up the call in some
error handlers so that, e.g., guard violations and @('er') calls can be trapped
and returned as error messages.  Unfortunately these error messages are not
very informative&mdash;they will just say something like @('ACL2 Halted')
instead of explaining the problem.</p>"
  (declare (ignorable sexpr))
  (b* ((- (raise "Raw lisp definition not installed?"))
       ((mv err1 errmsg? state) (read-acl2-oracle state))
       ((mv err2 values state) (read-acl2-oracle state))
       ((when (or err1 err2))
        (mv (msg "Reading oracle failed.") nil state))
       ((when errmsg?)
        (mv errmsg? nil state)))
    (mv nil values state)))

(defun unsound-eval-elide (stobjs-out return-vals)
  (declare (xargs :guard (equal (len stobjs-out) (len return-vals))))
  (cond ((atom stobjs-out)
         nil)
        ((car stobjs-out)
         (cons (car stobjs-out)
               (unsound-eval-elide (cdr stobjs-out) (cdr return-vals))))
        (t
         (cons (car return-vals)
               (unsound-eval-elide (cdr stobjs-out) (cdr return-vals))))))

(defttag :unsound-eval)
; (depends-on "unsound-eval-raw.lsp")
(include-raw "unsound-eval-raw.lsp")
