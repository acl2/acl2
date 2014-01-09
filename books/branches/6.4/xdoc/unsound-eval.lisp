; XDOC Documentation System for ACL2
; Copyright (C) 2009-2013 Centaur Technology
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
; Original author: Jared Davis <jared@centtech.com>

(in-package "ACL2")
(include-book "std/util/define" :dir :system)
(include-book "tools/include-raw" :dir :system)
(local (include-book "oslib/read-acl2-oracle" :dir :system))
       
(define unsound-eval
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

<p>In the execution, we basically call ACL2's @('trans-eval') function.  But we
wrap up the call in some error handlers so that, e.g., guard violations and
@('er') calls can be trapped and returned as error messages.  Unfortunately
these error messages are not very informative&mdash;they will just say
something like @('ACL2 Halted') instead of explaining the problem.</p>"
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
