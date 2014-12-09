; Proof Script Using :Type-prescription Rules
; Copyright (C) 2014, Oracle and/or its affiliates. All rights reserved.
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
; Original author: David L. Rager <david.rager@oracle.com>

(in-package "ACL2")

; The below example answers the question, "Can type-prescription rules with a
; conjunction of consequences be used effectively?"  When used in a simple
; example like this, the answer appears to be "yes".

; Note that :type-prescription rules can only describe a single "typed term."

(in-theory
; Tau will prove whatever simple tests we concoct, so we disable it.
 (disable (tau-system)))

(in-theory
; To reduce the amount of things we need to think about.
 (disable natp))

(defund foo (x)
  (* (nfix x) 2))

(defund bar (x)
  (* (nfix x) 4))

(defthm my-foo-type
  (and (natp (foo x))
       (integerp (foo x)))
  :rule-classes :type-prescription)

(defthm call-of-bar
  (implies (natp x)
           (natp (bar x))))

(in-theory
; Disable the automatically generated type-prescription rules.  We do this
; now instead of earlier, because we needed the :type-prescription for bar to
; prove call-of-bar.
 (disable (:type-prescription foo) (:type-prescription bar)))


(defthm use-foo-app
; Proving this theorem in the current theory requires using call-of-bar.  When
; call-of-bar goes to relieve its hypothesis, it will use the
; :type-prescription rule my-foo-type.  Thus, we know ACL2 is able to use
; conclusions that have more than one type description.
  (natp (bar (foo x))))
