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
(%interactive)

(defsection build.reflexivity-list
  (%autoadmit build.reflexivity-list)
  (local (%restrict default build.reflexivity-list (equal x 'x)))
  (%autoprove forcing-logic.appeal-listp-of-build.reflexivity-list (%cdr-induction x))
  (%autoprove forcing-logic.strip-conclusions-of-build.reflexivity-list (%cdr-induction x))
  (%autoprove forcing-logic.proof-listp-of-build.reflexivity-list (%cdr-induction x)))

;; There isn't really any reason to bother optimizing these; the
;; modus-ponens-list steps get optimized in level 3 anyway so these will only
;; be like two steps.

(defsection build.pequal-by-args
  (%autoadmit build.pequal-by-args)
  (local (%enable default logic.functional-axiom build.pequal-by-args))
  (%autoprove forcing-build.pequal-by-args-under-iff)
  (%autoprove forcing-logic.appealp-of-build.pequal-by-args)
  (%autoprove forcing-logic.conclusion-of-build.pequal-by-args)
  (%autoprove forcing-logic.proofp-of-build.pequal-by-args))

(defsection build.disjoined-pequal-by-args
  (%autoadmit build.disjoined-pequal-by-args)
  (local (%enable default logic.functional-axiom build.disjoined-pequal-by-args))
  (%autoprove forcing-build.disjoined-pequal-by-args-under-iff)
  (%autoprove forcing-logic.appealp-of-build.disjoined-pequal-by-args)
  (%autoprove forcing-logic.conclusion-of-build.disjoined-pequal-by-args)
  (%autoprove forcing-logic.proofp-of-build.disjoined-pequal-by-args))

