; SATLINK - Link from ACL2 to SAT Solvers
; Copyright (C) 2013 Centaur Technology
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
; Original authors: Jared Davis <jared@centtech.com>
;                   Sol Swords <sswords@centtech.com>

(in-package "SATLINK")

(defun satlink-echo (line rlines stream)

; Plugin for tshell printing that skips variable assignment lines.  Otherwise,
; the SAT solver can easily kill your Emacs by printing an extremely long line,
; which Emacs doesn't handle well at all.

  (declare (ignore rlines))
  (if (str::strprefixp "v " line)
      nil
    (progn
      (write-line line stream)
      (force-output stream))))

(defun satlink-echo-time (line rlines stream)

; Plugin for tshell printing that only prints timing summary lines like:
; "c Sat solving took 138.7 seconds."
; Arbitrarily looks for "c " prefix, " seconds." suffix, and " took " substring.

  (declare (ignore rlines))
  (if (and (str::strprefixp "c " line)
           (str::strsuffixp " seconds." line)
           (str::substrp " took " line))
      (progn
        (write-line line stream)
        (force-output stream))
    nil))

(defun satlink-run (config formula env$)
  (b* ((state acl2::*the-live-state*)
       (prev-okp                       (f-get-global 'acl2::writes-okp state))
       (state                          (f-put-global 'acl2::writes-okp t state))
       ((mv res env$ lrat-proof state) (satlink-run-impl config formula env$))
       (?state                         (f-put-global 'acl2::writes-okp prev-okp state)))
    (mv res env$ lrat-proof)))
