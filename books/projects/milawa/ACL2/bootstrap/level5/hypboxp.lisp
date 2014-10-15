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

(%autoadmit rw.hypboxp)
(%autoadmit rw.hypbox)
(%autoadmit rw.hypbox->left)
(%autoadmit rw.hypbox->right)

(encapsulate
 ()
 (local (%enable default rw.hypboxp rw.hypbox rw.hypbox->left rw.hypbox->right))
 (%autoprove booleanp-of-rw.hypboxp)
 (%autoprove forcing-rw.hypboxp-of-rw.hypbox)
 (%autoprove rw.hypbox->left-of-rw.hypbox)
 (%autoprove rw.hypbox->right-of-rw.hypbox)
 (%autoprove forcing-logic.term-listp-of-rw.hypbox->left)
 (%autoprove forcing-logic.term-listp-of-rw.hypbox->right)
 (%autoprove forcing-true-listp-of-rw.hypbox->left)
 (%autoprove forcing-true-listp-of-rw.hypbox->right)
 (%autoprove forcing-equal-of-rw.hypbox-one)
 (%autoprove forcing-equal-of-rw.hypbox-two))

(%autoadmit rw.hypbox-atblp)

(encapsulate
 ()
 (local (%enable default rw.hypbox-atblp))
 (%autoprove booleanp-of-rw.hypbox-atblp)
 (%autoprove forcing-rw.hypbox-atblp-of-quote-nil)
 (%autoprove forcing-logic.term-list-atblp-of-rw.hypbox->left)
 (%autoprove forcing-logic.term-list-atblp-of-rw.hypbox->right)
 (%autoprove forcing-rw.hypbox-atblp-of-rw.hypbox)
 (%autoprove rw.hypbox-atblp-of-nil))

(%autoadmit rw.hypbox-formula)
(%autoprove forcing-logic.formulap-of-rw.hypbox-formula
            (%enable default rw.hypbox-formula))
(%autoprove forcing-logic.formula-atblp-of-rw.hypbox-formula
            (%enable default rw.hypbox-formula))


(%deflist rw.hypbox-listp (x)
  (rw.hypboxp x))

(%deflist rw.hypbox-list-atblp (x atbl)
  (rw.hypbox-atblp x atbl))

(%autoadmit logic.true-term-listp)

(%autoprove logic.true-term-listp-removal
            (%cdr-induction x)
            (%restrict default logic.true-term-listp (equal x 'x)))

(%autoadmit rw.faster-hypboxp)

(%autoprove rw.faster-hypboxp-removal
            (%enable default rw.faster-hypboxp rw.hypboxp))


(%ensure-exactly-these-rules-are-missing "../../rewrite/assms/hypboxp")

