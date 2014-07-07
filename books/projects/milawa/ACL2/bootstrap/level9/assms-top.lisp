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
(include-book "assmsp")
;; (include-book "contradiction-bldr")
(%interactive)


(%autoprove forcing-rw.eqset-okp-when-empty-box
            (%enable default rw.eqset-okp rw.eqsetp rw.eqset->tail))

(%autoprove forcing-rw.eqset-list-okp-when-empty-box
            (%cdr-induction x))

(%autoprove forcing-rw.eqdatabase-okp-when-empty-box
            (%enable default
                     rw.eqdatabasep
                     rw.eqdatabase-okp
                     rw.eqdatabase->equalsets
                     rw.eqdatabase->contradiction))

(%autoprove rw.eqrow-list-lookup-when-not-consp
            (%restrict default rw.eqset-list-lookup (equal eqsets 'eqsets)))

(%autoprove forcing-rw.try-equalities-when-empty-box
            (%enable default rw.try-equiv-database))





(%autoadmit rw.try-assms)

(%autoprove forcing-logic.termp-of-rw.try-assms
            (%enable default rw.try-assms))

(%autoprove forcing-logic.term-atblp-of-rw.try-assms
            (%enable default rw.try-assms))

(%autoprove forcing-rw.try-assms-when-empty-hypbox
            (%enable default
                     rw.try-assms
                     rw.assmsp
                     rw.assms->eqdatabase
                     rw.assms->hypbox))



(defsection rw.try-assms-bldr

  (%autoadmit rw.try-assms-bldr)

  (local (%enable default
                  rw.try-assms
                  rw.try-assms-bldr
                  rw.eqtrace-formula))

  (%autoprove forcing-logic.appealp-of-rw.try-assms-bldr)

  (%autoprove forcing-logic.conclusion-of-rw.try-assms-bldr
              (%auto)
              ;; BOZO: ugh, this shouldn't be necessary
              (%enable default rw.assmsp rw.assms->eqdatabase rw.assms->hypbox))

  (%autoprove forcing-logic.proofp-of-rw.try-assms-bldr))


(%ensure-exactly-these-rules-are-missing "../../rewrite/assms/top")