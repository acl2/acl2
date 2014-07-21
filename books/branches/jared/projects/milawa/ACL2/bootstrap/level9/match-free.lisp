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
(include-book "assms-top")
(%interactive)


(%autoprove submap-of-eachp-when-submapp
            (%cdr-induction x))

(%autoprove submap-of-eachp-when-submapp-alt)

(%autoadmit rw.collect-critical-hyps)

(%autoprove subsetp-of-rw.collect-critical-hyps
            (%autoinduct rw.collect-critical-hyps)
            (%restrict default rw.collect-critical-hyps (equal hyps 'hyps)))




(%autoadmit rw.critical-hyps)

(%autoprove subsetp-of-rw.critical-hyps
            (%enable default rw.critical-hyps))

(%autoprove logic.term-listp-of-rw.critical-hyps
            (%disable default
                      subsetp-of-rw.critical-hyps
                      [outside]subsetp-of-rw.critical-hyps)
            (%use (%instance (%thm subsetp-of-rw.critical-hyps))))



(%autoadmit rw.limit-hyps-aux)

(%autoadmit rw.limit-hyps)




(%autoadmit rw.find-extensions-for-sigma-aux)

(%autoprove forcing-logic.sigma-listp-of-rw.find-extensions-for-sigma-aux
            (%autoinduct rw.find-extensions-for-sigma-aux)
            (%restrict default rw.find-extensions-for-sigma-aux (equal trueterms 'trueterms)))

(%autoprove forcing-logic.sigma-list-atblp-of-rw.find-extensions-for-sigma-aux
            (%autoinduct rw.find-extensions-for-sigma-aux)
            (%restrict default rw.find-extensions-for-sigma-aux (equal trueterms 'trueterms)))

(%autoprove submap-of-eachp-of-rw.find-extensions-for-sigma-aux
            (%autoinduct rw.find-extensions-for-sigma-aux)
            (%restrict default rw.find-extensions-for-sigma-aux (equal trueterms 'trueterms)))

(%autoprove submap-of-eachp-of-rw.find-extensions-for-sigma-aux-free
            (%autoinduct rw.find-extensions-for-sigma-aux)
            (%restrict default rw.find-extensions-for-sigma-aux (equal trueterms 'trueterms)))



(%autoadmit rw.find-extensions-for-sigma)

(%autoprove forcing-logic.sigma-listp-of-rw.find-extensions-for-sigma
            (%enable default rw.find-extensions-for-sigma))

(%autoprove forcing-logic.sigma-list-atblp-of-rw.find-extensions-for-sigma
            (%enable default rw.find-extensions-for-sigma))

(%autoprove submap-of-eachp-of-rw.find-extensions-for-sigma
            (%enable default rw.find-extensions-for-sigma))

(%autoprove submap-of-eachp-of-rw.find-extensions-for-sigma-free
            (%enable default rw.find-extensions-for-sigma))





(%autoadmit rw.find-extensions-for-sigma-list)

(%autoprove forcing-logic.sigma-listp-of-rw.find-extensions-for-sigma-list
            (%autoinduct rw.find-extensions-for-sigma-list)
            (%restrict default rw.find-extensions-for-sigma-list (equal sigmas 'sigmas)))

(%autoprove forcing-logic.sigma-list-atblp-of-rw.find-extensions-for-sigma-list
            (%autoinduct rw.find-extensions-for-sigma-list)
            (%restrict default rw.find-extensions-for-sigma-list (equal sigmas 'sigmas)))

(%autoprove submap-of-eachp-of-rw.find-extensions-for-sigma-list
            (%autoinduct rw.find-extensions-for-sigma-list)
            (%restrict default rw.find-extensions-for-sigma-list (equal sigmas 'sigmas)))




(%autoadmit rw.find-extensions-for-crit-hyps)

(%autoprove forcing-logic.sigma-listp-of-rw.find-extensions-for-crit-hyps
            (%autoinduct rw.find-extensions-for-crit-hyps)
            (%restrict default rw.find-extensions-for-crit-hyps (equal hyps 'hyps)))

(%autoprove forcing-logic.sigma-list-atblp-of-rw.find-extensions-for-crit-hyps
            (%autoinduct rw.find-extensions-for-crit-hyps)
            (%restrict default rw.find-extensions-for-crit-hyps (equal hyps 'hyps)))

(%autoprove submap-of-eachp-of-rw.find-extensions-for-crit-hyps
            (%autoinduct rw.find-extensions-for-crit-hyps)
            (%restrict default rw.find-extensions-for-crit-hyps (equal hyps 'hyps)))





(%autoadmit rw.create-sigmas-to-try)

(%autoprove forcing-logic.sigma-listp-of-rw.create-sigmas-to-try
            (%enable default rw.create-sigmas-to-try))

(%autoprove forcing-logic.sigma-list-atblp-of-rw.create-sigmas-to-try
            (%enable default rw.create-sigmas-to-try))

(%autoprove submap-of-eachp-of-rw.create-sigmas-to-try
            (%enable default rw.create-sigmas-to-try))



(%ensure-exactly-these-rules-are-missing "../../rewrite/match-free")