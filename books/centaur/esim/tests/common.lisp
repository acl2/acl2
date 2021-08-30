; Copyright David Rager, 2013

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

(in-package "ACL2")
; cert_param: (uses-glucose)
(include-book "../defmodules")
(include-book "centaur/gl/gl" :dir :system)
(include-book "centaur/aig/g-aig-eval" :dir :system)
(include-book "centaur/esim/stv/stv-top" :dir :system)
(include-book "centaur/esim/stv/stv-debug" :dir :system)
(include-book "centaur/4v-sexpr/top" :dir :system)
(include-book "tools/plev-ccl" :dir :system)
(include-book "centaur/misc/memory-mgmt" :dir :system)
(include-book "std/strings/top" :dir :system)
(include-book "misc/without-waterfall-parallelism" :dir :system)

;; Gather benchmarks, mainly to give the benchmark gathering hook some testing
(include-book "centaur/satlink/benchmarks" :dir :system)

; I'm unsure why the below is critical, but the "GL Clock" runs out without it.
; It introduces a GL clause processor that can natively execute at least the
; functions from the above books that get marked with add-clause-proc-exec-fns.

(without-waterfall-parallelism
(def-gl-clause-processor my-glcp))

(include-book "centaur/gl/bfr-satlink" :dir :system)

(make-event (prog2$ (tshell-ensure)
                    '(value-triple :invisible))
            :check-expansion t)

(gl::gl-satlink-mode)

(defun my-glucose-config ()
  (declare (xargs :guard t))
  (satlink::make-config :cmdline "glucose -model"
                        :verbose t
                        :mintime 1/2
                        :remove-temps t))

(defattach gl::gl-satlink-config my-glucose-config)

(local (defthm unsigned-byte-p-re-redef
         (equal (unsigned-byte-p bits x)
                (AND (INTEGERP BITS)
                     (<= 0 BITS)
                     (INTEGER-RANGE-P 0 (EXPT 2 BITS) X)))
         :hints(("Goal" :in-theory (enable unsigned-byte-p)))
         :rule-classes :definition))

(defxdoc verilog-regression-tests
  :parents (ACL2::VL)
  :short "Regression tests for @(see vl) and @(see esim)."
  :long "Regression tests for the ACL2 verilog system can be found in
         books/centaur/regression.")
