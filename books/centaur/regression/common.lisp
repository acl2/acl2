; Copyright David Rager, 2013

; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.

(in-package "ACL2")
; cert_param: (hons-only)
; cert_param: (uses-glucose)

(include-book "centaur/vl/top" :dir :system)
(include-book "centaur/gl/gl" :dir :system)
(include-book "centaur/aig/g-aig-eval" :dir :system)
(include-book "centaur/esim/stv/stv-top" :dir :system)
(include-book "centaur/esim/stv/stv-debug" :dir :system)
(include-book "centaur/4v-sexpr/top" :dir :system)
(include-book "tools/plev-ccl" :dir :system)
(include-book "centaur/misc/memory-mgmt" :dir :system)
(include-book "str/top" :dir :system)

(set-waterfall-parallelism nil) ; for below call of def-gl-clause-processor

; I'm unsure why the below is critical, but the "GL Clock" runs out without it.
; It introduces a GL clause processor that can natively execute at least the
; functions from the above books that get marked with add-clause-proc-exec-fns.

(def-gl-clause-processor my-glcp)

(include-book "centaur/gl/bfr-satlink" :dir :system)

(make-event (prog2$ (tshell-ensure)
                    '(value-triple :invisible))
            :check-expansion t)

(gl::gl-satlink-mode)

(defun my-glucose-config ()
  (declare (xargs :guard t))
  (satlink::make-config :cmdline "glucose"
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
