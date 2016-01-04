; VL Verilog Toolkit
; Copyright (C) 2008-2014 Centaur Technology
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

(in-package "VL")
(include-book "../parsetree")
(local (include-book "../util/arithmetic"))

(defsection custom-transform-hooks
  :parents (transforms)
  :short "Ways of extending VL with custom transformations."

  :long "<p>These are hooks for additional transforms that we use at Centaur,
but which have not yet been released for whatever reason.  When it comes time
for us to run our transforms, we just defattach our implementations to these
hooks.  For non-Centaur users, these steps are just no-ops.</p>

<p>Some of these transforms will never be released because they're gross hacks
that are intended to address Centaur-specific things, and they wouldn't be of
any interest outside of Centaur.  We may release the others eventually, but
they may be in beta or tied into other libraries in a deep way that makes it
hard to make them available at this time.</p>")

(local (xdoc::set-default-parents custom-transform-hooks))

(defsection mp-verror-transform-hook
  :short "Centaur specific transform."

  (encapsulate
    (((mp-verror-transform-hook *) => *
      :formals (x)
      :guard (vl-design-p x)))

    (local (defun mp-verror-transform-hook (x)
             (vl-design-fix x)))

    (defthm vl-design-p-of-mp-verror-transform-hook
      (vl-design-p (mp-verror-transform-hook x))))

  (defattach mp-verror-transform-hook vl-design-fix$inline))


(defsection vl-design-constcheck-hook
  :short "Beta transform, not ready for public release."

  (encapsulate
    (((vl-design-constcheck-hook * *) => *
      :formals (x limit)
      :guard (and (vl-design-p x)
                  (natp limit))))

    (local (defun vl-design-constcheck-hook (x limit)
             (declare (ignorable limit))
             (vl-design-fix x)))

    (defthm vl-design-p-of-vl-design-constcheck-hook
      (vl-design-p (vl-design-constcheck-hook x limit))))

  (defun vl-design-constcheck-hook-default (x limit)
    (declare (xargs :guard (and (vl-design-p x)
                                (natp limit)))
             (ignorable limit))
    (vl-design-fix x))

  (defattach vl-design-constcheck-hook vl-design-constcheck-hook-default))


(defsection vl-centaur-seqcheck-hook
  :short "Centaur-specific linter check."

  (encapsulate
    (((vl-centaur-seqcheck-hook *) => *
      :formals (x)
      :guard (vl-design-p x)))

    (local (defun vl-centaur-seqcheck-hook (x)
             (vl-design-fix x)))

    (defthm vl-design-p-of-vl-centaur-seqcheck-hook
      (vl-design-p (vl-centaur-seqcheck-hook x))))

  (defun vl-centaur-seqcheck-hook-default (x)
    (declare (xargs :guard (vl-design-p x)))
    (vl-design-fix x))

  (defattach vl-centaur-seqcheck-hook
    vl-centaur-seqcheck-hook-default))
