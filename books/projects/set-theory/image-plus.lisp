; Copyright (C) 2026, Matt Kaufmann
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; (Image+ f) is the union of (image f) and {0}.  The addition of 0 allow us to
; prove in-apply-image+ below, giving us a set to collect all applications of
; the function f, even on inputs not in its domain.

(in-package "ZF")

(include-book "base")

(defun image+ (f)
  (union2 (image f) (singleton 0)))

(defthmz in-apply-image+
  (in (apply f x)
      (image+ f))
  :hints (("Goal" :in-theory (enable apply)))
  :props (zfc prod2$prop inverse$prop domain$prop))
