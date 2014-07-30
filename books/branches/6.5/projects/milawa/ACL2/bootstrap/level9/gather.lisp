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
(include-book "theoryp")
(%interactive)


(%autoadmit rw.rule-components)
(%enable default rw.rule-components)


(%autoadmit rw.consider-rule)

(%autoprove booleanp-of-rw.consider-rule
            (%enable default rw.consider-rule))


(%autoadmit rw.gather-rules-from-list)

(%autoprove true-listp-of-rw.gather-rules-from-list
            (%autoinduct rw.gather-rules-from-list)
            (%restrict default rw.gather-rules-from-list (equal rules 'rules)))

(%autoprove forcing-rw.rule-listp-of-rw.gather-rules-from-list
            (%autoinduct rw.gather-rules-from-list)
            (%restrict default rw.gather-rules-from-list (equal rules 'rules)))

(%autoprove forcing-rw.rule-list-atblp-of-rw.gather-rules-from-list
            (%autoinduct rw.gather-rules-from-list)
            (%restrict default rw.gather-rules-from-list (equal rules 'rules)))

(%autoprove forcing-rw.rule-list-env-okp-of-rw.gather-rules-from-list
            (%autoinduct rw.gather-rules-from-list)
            (%restrict default rw.gather-rules-from-list (equal rules 'rules)))


(%autoadmit rw.gather-rules-from-map)

(%autoprove true-listp-of-rw.gather-rules-from-map
            (%autoinduct rw.gather-rules-from-map)
            (%restrict default rw.gather-rules-from-map (equal rulemap 'rulemap)))

(%autoprove rw.rule-listp-of-rw.gather-rules-from-map
            (%autoinduct rw.gather-rules-from-map)
            (%restrict default rw.gather-rules-from-map (equal rulemap 'rulemap)))

(%autoprove rw.rule-list-atblp-of-rw.gather-rules-from-map
            (%autoinduct rw.gather-rules-from-map)
            (%restrict default rw.gather-rules-from-map (equal rulemap 'rulemap)))

(%autoprove rw.rule-list-env-okp-of-rw.gather-rules-from-map
            (%autoinduct rw.gather-rules-from-map)
            (%restrict default rw.gather-rules-from-map (equal rulemap 'rulemap)))


(%autoadmit rw.gather-rules-from-theory)

(%autoprove true-listp-of-rw.gather-rules-from-theory
            (%autoinduct rw.gather-rules-from-theory)
            (%restrict default rw.gather-rules-from-theory (equal theory 'theory)))

(%autoprove rw.rule-listp-of-rw.gather-rules-from-theory
            (%autoinduct rw.gather-rules-from-theory)
            (%restrict default rw.gather-rules-from-theory (equal theory 'theory)))

(%autoprove rw.rule-list-atblp-of-rw.gather-rules-from-theory
            (%autoinduct rw.gather-rules-from-theory)
            (%restrict default rw.gather-rules-from-theory (equal theory 'theory)))

(%autoprove rw.rule-list-env-okp-of-rw.gather-rules-from-theory
            (%autoinduct rw.gather-rules-from-theory)
            (%restrict default rw.gather-rules-from-theory (equal theory 'theory)))

(%ensure-exactly-these-rules-are-missing "../../rewrite/gather")