; Copyright (C) 2023, ForrestHunt, Inc.
; Written by Matt Kaufmann and J Moore, July-August 2023
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(include-book "eviscerate-top")

(local (include-book "fmt-support"))

(verify-termination fmt-char)
(verify-termination fmt-var)
(verify-termination find-alternative-skip
  (declare (xargs :verify-guards t)))
(verify-termination zero-one-or-more)
(verify-termination find-alternative-start1
  (declare (xargs :verify-guards t)))
(verify-termination find-alternative-start)
(verify-termination find-alternative-stop
  (declare (xargs :verify-guards t)))
(verify-termination symbol-to-fixnat-alistp)
(verify-termination fmt-state-p)
(verify-termination punctp)
(verify-termination fmt-soft-right-margin)
(verify-termination fmt-hard-right-margin)
(verify-termination scan-past-whitespace
  (declare (xargs :verify-guards t)))
(verify-termination write-for-read)
(verify-termination newline)
(verify-termination fmt-tilde-s1
  (declare (xargs :verify-guards t)))
(verify-termination fmt-tilde-cap-s1
  (declare (xargs :verify-guards t)))
(verify-termination flsz-integer
  (declare (xargs :verify-guards t)))
(verify-termination flsz-atom)
(verify-termination spaces1)
(verify-termination spaces)
(verify-termination splat-atom)
(verify-termination splat-atom!)
(verify-termination splat-string)
(verify-termination splat
  (declare (xargs :verify-guards t)))
(verify-termination number-of-digits
  (declare (xargs :verify-guards t)))
(verify-termination left-pad-with-blanks)
(verify-termination evisc-tuple)
(verify-termination term-evisc-tuple)
(verify-termination gag-mode-evisc-tuple)
(verify-termination scan-past-empty-fmt-directives1
  (declare (xargs :verify-guards t)))
(verify-termination scan-past-empty-fmt-directives
  (declare (xargs :verify-guards t)))
(verify-termination out-of-time-the2s)
(verify-termination char?)
(verify-termination min-fixnat$inline)
(verify-termination flpr1
  (declare (xargs :verify-guards t)))
(verify-termination flpr)
(verify-termination ppr2-flat)
(verify-termination flsz1
  (declare (xargs :verify-guards t)))
(verify-termination ppr-tuple-p)
(verify-termination max-width)
(verify-termination keyword-param-valuep)
(verify-termination cons-ppr1-guardp)
(verify-termination cons-ppr1)
(verify-termination special-term-num)
(verify-termination ppr1)
(verify-termination ffnnamep)
(verify-termination ppr2-flat)
(verify-termination ppr2)
(verify-termination ppr)
(verify-termination flsz)
(verify-termination fmt-ppr)
(verify-termination fmt0)
(verify-guards fmt0)
(verify-termination fmt1
  (declare (xargs :verify-guards t)))
(verify-termination fmt)
(verify-termination fms)
(verify-termination fmt1!)
(verify-termination fmt!)
(verify-termination fms!)
