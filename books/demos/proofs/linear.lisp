; Proof Script Using :Linear Rules
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

; The below example answers the question, "Can :linear rules with a
; conjunction of consequences be used effectively?"  When used in a simple
; example like this, the answer appears to be yes.

(in-theory
; Tau has some ability to reason about intervals, so we disable it.
 (disable (tau-system)))

(in-theory
; To reduce the amount of things we need to think about.
 (disable natp))

(defun foo (x)
  (min (expt 2 32) (+ (nfix x) (nfix x))))

(defun bar (x)
  (min (expt 2 64) (* (nfix x) 4)))


(defthm my-foo-bar-linear
  (and (<= (foo x) (expt 2 32))
       (<= (bar x) (expt 2 64)))
  :rule-classes :linear)

(in-theory (disable foo bar))

(defthm call-of-foo
; Uses my-foo-bar-linear
  (<= (foo x) (expt 2 40)))


; We've demonstrated the point, but our proof for baz-linear is slightly more
; fun, so we include it anyway.

(defun baz (x)
  (* (bar x) 2))

(defthm baz-linear
; Uses my-foo-bar-linear
  (<= (baz x) (expt 2 130)))
