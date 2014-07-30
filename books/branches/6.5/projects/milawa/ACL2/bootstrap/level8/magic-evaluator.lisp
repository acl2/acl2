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

;; NOTE: magic evaluation is not used anymore, because it was a lot easier
;; to take it out than try to explain why it is sound. :)

;; (include-book
;;  "../../../rewrite/magic-evaluator")
;; (include-book "evaluator-bldr-2")
;; (%interactive)


;; (%defchoose evaluable-termp-witness n (x defs)
;;             (generic-evaluator x defs n))

;; (defsection evaluable-termp
;;   (%defun evaluable-termp (x defs)
;;           (let ((n (evaluable-termp-witness x defs)))
;;             (generic-evaluator x defs n)))
;;   (%admit))

;; (%autoprove evaluable-termp-suff
;;             (%use (build.axiom (defchoose-axiom-for-evaluable-termp-witness)))
;;             (%use (%instance (%thm evaluable-termp))))

;; (%autoadmit magic-evaluator)

;; (%autoprove forcing-logic.constantp-of-magic-evaluator
;;             (%enable default magic-evaluator))




;; (%autoadmit magic-evaluator-bldr)

;; (%autoprove forcing-logic.appealp-of-magic-evaluator-bldr
;;             (%enable default magic-evaluator magic-evaluator-bldr))

;; (%autoprove forcing-logic.conclusion-of-magic-evaluator-bldr
;;             (%enable default magic-evaluator magic-evaluator-bldr))

;; (%autoprove forcing-logic.proofp-of-magic-evaluator-bldr
;;             (%enable default magic-evaluator magic-evaluator-bldr))

