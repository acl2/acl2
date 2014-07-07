; Milawa - A Reflective Theorem Prover
; Copyright (C) 2005-2009 Kookamara LLC
;
; Contact:
;
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759, USA
;   http://www.kookamara.com/
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
; Original author: Jared Davis <jared@kookamara.com>

(in-package "MILAWA")
;(include-book "crewrite-tracep")
;(include-book "crewrite-lhs")
;(include-book "crewrite-hypbox")
(include-book "crewrite-trace-okp")
(include-book "crewrite-trace-atblp")
(include-book "crewrite-trace-env-okp")
(%interactive)

(%autoprove map-listp-when-logic.sigma-listp
            (%cdr-induction x))

#||

;; Old -- this isn't needed anymore.

(defsection rw.aux-crewrite
  (%autoadmit rw.aux-crewrite)
  (local (%restrict default rw.aux-crewrite (equal x 'x)))
  (%autoprove forcing-rw.tracep-of-rw.aux-crewrite
              (%autoinduct rw.aux-crewrite))
  (%autoprove forcing-rw.trace->hypbox-of-rw.aux-crewrite)
  (%autoprove forcing-rw.trace->lhs-of-rw.aux-crewrite)
  (%autoprove forcing-rw.trace->iffp-of-rw.aux-crewrite)
  (%autoprove forcing-rw.trace-atblp-of-rw.aux-crewrite
              (%autoinduct rw.aux-crewrite))
  (%autoprove forcing-rw.trace-okp-of-rw.aux-crewrite
              (%autoinduct rw.aux-crewrite))
  (%autoprove forcing-rw.trace-env-okp-of-rw.aux-crewrite
              (%autoinduct rw.aux-crewrite)))
||#

(defsection rw.crewrite
  (%autoadmit rw.crewrite)
  (local (%enable default rw.crewrite))
  (%autoprove forcing-rw.tracep-of-rw.crewrite)
  (%autoprove forcing-rw.trace->hypbox-of-rw.crewrite)
  (%autoprove forcing-rw.trace->lhs-of-rw.crewrite)
  (%autoprove forcing-rw.trace->iffp-of-rw.crewrite)
  (%autoprove forcing-rw.trace-atblp-of-rw.crewrite)
  (%autoprove forcing-rw.trace-okp-of-rw.crewrite)
  (%autoprove forcing-rw.trace-env-okp-of-rw.crewrite))


(%ensure-exactly-these-rules-are-missing "../../rewrite/crewrite"
                                         ;; don't need cheap rules, we have %cheapen
                                         rw.crewrite-try-rules-when-not-consp-cheap)

