; VL Verilog Toolkit
; Copyright (C) 2008-2014 Centaur Technology
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

(in-package "VL")
(include-book "../parsetree")
(local (include-book "../util/arithmetic"))


(defsection custom-transform-hooks
  :parents (transforms)
  :short "Ways of extending @(see vl-simplify) with custom transformations."

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


(defsection vl-design-pre-toe-hook
  :short "Arbitrary hook for adding additional transforms before @(see
e-conversion)."

  (encapsulate
    (((vl-design-pre-toe-hook *) => *
      :formals (x)
      :guard (vl-design-p x)))

    (local (defun vl-design-pre-toe-hook (x)
             (vl-design-fix x)))

    (defthm vl-design-p-of-vl-design-pre-toe-hook
      (vl-design-p (vl-design-pre-toe-hook x))))

  (defattach vl-design-pre-toe-hook vl-design-fix$inline))



(defsection vl-design-post-unparam-hook
  :short "Arbitrary hook for adding additional transforms before @(see
e-conversion)."

  (encapsulate
    (((vl-design-post-unparam-hook *) => *
      :formals (x)
      :guard (vl-design-p x)))

    (local (defun vl-design-post-unparam-hook (x)
             (vl-design-fix x)))

    (defthm vl-design-p-of-vl-design-post-unparam-hook
      (vl-design-p (vl-design-post-unparam-hook x))))

  (defattach vl-design-post-unparam-hook vl-design-fix$inline))


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
