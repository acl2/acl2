; Copyright (C) 2018, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(local (include-book "fmx-cw-support"))

; We need the declare forms below to avoid redefinition errors.  Fortunately we
; can overcome :verify-guards nil with the following:
(set-verify-guards-eagerness 3)

(verify-termination illegal-fmt-string)
(verify-termination fmt-char)
(verify-termination zero-one-or-more)
(verify-termination standard-evisc-tuplep)
(verify-termination fmt-var)
(verify-termination find-alternative-skip
  (declare (xargs :verify-guards nil)))
(verify-termination find-alternative-start1
  (declare (xargs :verify-guards nil)))
(verify-termination find-alternative-start)
(verify-termination find-alternative-stop
  (declare (xargs :verify-guards nil)))
(verify-termination scan-past-whitespace
  (declare (xargs :verify-guards nil)))
(verify-termination fmx-cw-msg-1)
(verify-termination fmx-cw-msg)
(verify-termination fmx-cw-fn-guard)
(verify-termination fmx-cw-fn)
(verify-termination fmx!-cw-fn)
(verify-termination comment-string-p1)
(verify-termination comment-string-p)
(verify-termination print-control-p)
