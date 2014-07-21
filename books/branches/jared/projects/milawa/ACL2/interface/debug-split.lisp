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
(include-book "core")


(defmacro %ensure-no-outstanding-goals (note)
  `(ACL2::make-event (%ensure-no-outstanding-goals-fn ',note (ACL2::w ACL2::state))))

(defun %ensure-no-outstanding-goals-fn (note world)
  (declare (xargs :mode :program))
  (if (consp (tactic.harness->goals world))
      (ACL2::er hard '%ensure-no-outstanding-goals
                "Expected no outstanding goals at ~x0.~%"
                note)
    '(ACL2::value-triple :invisible)))



(defmacro %debug-split ()
  `(ACL2::make-event (%debug-split-fn (ACL2::w ACL2::state))))

(defun %aux-debug-split-fn (goals i)
  (declare (xargs :mode :program))
  (if (consp goals)
      (cons `(defsection ,(ACL2::mksym 'debugging-goal- (ACL2::intern-in-package-of-symbol (STR::dwim-string-fix i) 'foo))
               (ACL2::value-triple (ACL2::cw "Now Debugging Goal ~x0.~%" ,i))
               (ACL2::value-triple (ACL2::cw "~x0~%" '(ACL2::table tactic-harness 'skeleton (tactic.initial-skeleton (list ',(car goals))))))
               (ACL2::table tactic-harness 'skeleton (tactic.initial-skeleton (list ',(car goals))))
               (%auto)
               (%ensure-no-outstanding-goals ,i))
            (%aux-debug-split-fn (cdr goals) (+ i 1)))
    nil))

(defun %debug-split-fn (world)
  (declare (xargs :mode :program))
  `(ACL2::progn ,@(%aux-debug-split-fn (tactic.harness->goals world) 1)))
