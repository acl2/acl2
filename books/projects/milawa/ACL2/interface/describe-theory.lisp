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


;; BOZO I had two versions of this.  Not sure which one is better?

;; (ACL2::defun sort-symbol-list (x)
;;              (declare (xargs :mode :program)
;;                       (ignore x))
;;              (ACL2::er hard 'sort-symbol-list "Error: sort-symbol-list has not been redefined!~%"))

;; (ACL2::defttag sort-symbol-list)

;; (ACL2::progn!
;;  (ACL2::set-raw-mode t)
;;  (ACL2::defun sort-symbol-list (x)
;;               (declare (xargs :mode :program))
;;               (ACL2::sort x #'symbol-<)))

;; (defmacro %describe-theory (theoryname)
;;   `(describe-theory-fn ',theoryname (ACL2::w ACL2::state)))

;; (defun describe-theory-fn (theoryname world)
;;   (declare (xargs :mode :program))
;;   (sort-symbol-list (rw.fast-rule-list-names$ (rw.gather-rules-from-theory
;;                                                (tactic.find-theory theoryname world)
;;                                                ''t
;;                                                (tactic.harness->syndefs world)
;;                                                nil)
;;                                               nil)))



(defmacro %describe-theory (theoryname)
  `(describe-theory-fn ',theoryname (ACL2::w ACL2::state)))

(defun describe-theory-fn (theoryname world)
  (declare (xargs :mode :program))
  (let* ((tactic-world (tactic.harness->world world))
         (theory   (or (tactic.find-theory theoryname tactic-world)
                       (acl2::er hard? 'describe-theory-fn "Theory ~x0 not found." theoryname)))
         (defs     (tactic.world->defs tactic-world))
         (rules    (rw.gather-rules-from-theory (cdr theory) ''t defs nil))
         (names    (rw.rule-list-names rules)))
    (sort-symbols names)))

