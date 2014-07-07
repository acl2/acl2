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
(include-book "proofp-1")
(%interactive)



(%autoadmit logic.make-basis-step)

(%autoprove forcing-logic.formulap-of-logic.make-basis-step
            (%enable default logic.make-basis-step))

(%autoprove forcing-logic.formula-atblp-of-logic.make-basis-step
            (%enable default logic.make-basis-step))



(%autoadmit logic.make-induction-step)

(%autoprove forcing-logic.formulap-of-logic.make-induction-step
            (%enable default logic.make-induction-step))

(%autoprove forcing-logic.formula-atblp-of-logic.make-induction-step
            (%enable default logic.make-induction-step))



(%autoadmit logic.make-induction-steps)

(defmacro %logic.make-induction-steps-induction (qs all-sigmas)
  `(%induct (rank ,qs)
            ((not (consp ,qs))
             nil)
            ((consp ,qs)
             (((,qs         (cdr ,qs))
               (,all-sigmas (cdr ,all-sigmas)))))))

(%autoprove true-listp-of-logic.make-induction-steps
            (%logic.make-induction-steps-induction qs all-sigmas)
            (%restrict default logic.make-induction-steps (equal qs 'qs)))

(%autoprove len-of-logic.make-induction-steps
            (%logic.make-induction-steps-induction qs all-sigmas)
            (%restrict default logic.make-induction-steps (equal qs 'qs)))

(%autoprove forcing-logic.formula-listp-of-logic.make-induction-steps
            (%logic.make-induction-steps-induction qs all-sigmas)
            (%restrict default logic.make-induction-steps (equal qs 'qs)))

(%autoprove forcing-logic.formula-list-atblp-of-logic.make-induction-steps
            (%logic.make-induction-steps-induction qs all-sigmas)
            (%restrict default logic.make-induction-steps (equal qs 'qs)))



(%autoadmit logic.make-ordinal-step)

(%autoprove forcing-logic.formulap-of-logic.make-ordinal-step
            (%enable default logic.make-ordinal-step))

(%autoprove forcing-logic.formula-atblp-of-logic.make-ordinal-step
            (%enable default logic.make-ordinal-step))



(%autoadmit logic.make-measure-step)

(%autoprove forcing-logic.formulap-of-logic.make-measure-step
            (%enable default logic.make-measure-step))

(%autoprove forcing-logic.formula-atblp-of-logic.make-measure-step
            (%enable default logic.make-measure-step))



(%autoadmit logic.make-measure-steps)

(%autoprove forcing-logic.formula-listp-of-logic.make-measure-steps
            (%cdr-induction sigmas-i)
            (%restrict default logic.make-measure-steps (equal sigmas-i 'sigmas-i)))

(%autoprove forcing-logic.formula-list-atblp-of-logic.make-measure-steps
            (%cdr-induction sigmas-i)
            (%restrict default logic.make-measure-steps (equal sigmas-i 'sigmas-i)))



(%autoadmit logic.make-all-measure-steps)

(defmacro %logic.make-all-measure-steps-induction (qs all-sigmas)
  `(%induct (rank ,all-sigmas)
            ((not (consp ,all-sigmas))
             nil)
            ((consp ,all-sigmas)
             (((qs         (cdr ,qs))
               (all-sigmas (cdr ,all-sigmas)))))))

(%autoprove true-listp-of-logic.make-all-measure-steps
            (%logic.make-all-measure-steps-induction qs all-sigmas)
            (%restrict default logic.make-all-measure-steps (equal all-sigmas 'all-sigmas)))

(%autoprove forcing-logic.formula-listp-of-logic.make-all-measure-steps
            (%logic.make-all-measure-steps-induction qs all-sigmas)
            (%restrict default logic.make-all-measure-steps (equal all-sigmas 'all-sigmas)))

(%autoprove forcing-logic.formula-list-atblp-of-logic.make-all-measure-steps
            (%logic.make-all-measure-steps-induction qs all-sigmas)
            (%restrict default logic.make-all-measure-steps (equal all-sigmas 'all-sigmas)))

