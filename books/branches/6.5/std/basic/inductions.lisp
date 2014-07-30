; Std/basic - Basic definitions
; Copyright (C) 2008-2013 Centaur Technology
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
(include-book "xdoc/top" :dir :system)

(defsection induction-schemes
  :parents (std/basic)
  :short "A variety of basic, widely applicable @(see induction) schemes."

  :long "<p>The definitions here are meant to be used in @(see induct) hints or
as the @(':scheme') for @(see induction) rules.  You would typically include
them only locally, e.g., with:</p>

@({
    (local (include-book \"std/basic/inductions\" :dir :system))
})

<p>For general background on induction schemes, see @(see
logic-knowledge-taken-for-granted-inductive-proof) and @(see
example-inductions).</p>")

(local (xdoc::set-default-parents induction-schemes))


(defsection dec-induct
  :short "@(call dec-induct) is classic natural-number induction on @('n');
we just subtract 1 until reaching 0."

  (defun dec-induct (n)
    (if (zp n)
        nil
      (dec-induct (- n 1)))))


(defsection cdr-induct
  :short "@(call cdr-induct) is classic list induction, i.e., @(see cdr)
until you reach the end of the list."

  (defun cdr-induct (x)
    (if (atom x)
        nil
      (cdr-induct (cdr x)))))


(defsection cdr-dec-induct
  :short "@(call cdr-dec-induct) inducts by simultaneously @(see cdr)'ing
@('x') and subtracting 1 from @('n'), until we reach the end of @('x') or
@('n') reaches 0."

  (defun cdr-dec-induct (x n)
    (if (atom x)
        nil
      (if (zp n)
          nil
        (cdr-dec-induct (cdr x) (- n 1))))))


(defsection dec-dec-induct
  :short "@(call dec-dec-induct) inducts by simultaneously subtracting
1 each from @('n') and @('m'), until either one reaches 0."

  (defun dec-dec-induct (n m)
    (if (or (zp n)
            (zp m))
        nil
      (dec-dec-induct (- n 1) (- m 1)))))


(defsection cdr-cdr-induct
  :short "@(call cdr-cdr-induct) inducts by simultaneously @(see cdr)'ing
@('x') and @('y') until we reach the end of either."

  (defun cdr-cdr-induct (x y)
    (if (or (atom x)
            (atom y))
        nil
      (cdr-cdr-induct (cdr x) (cdr y)))))

