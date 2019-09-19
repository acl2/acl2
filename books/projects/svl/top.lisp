; SVL - Listener-based Hierachical Symbolic Vector Hardware Analysis Framework
; Copyright (C) 2019 Centaur Technology
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
; Original author: Mertcan Temel <mert@utexas.edu>

;; All the books from SVL package.

;; This book has two main tools: SVL and SVL2.

;; SVL is a listener-based verilog simulator that maintains hierarchy. In this
;; listener-based modal, assignments and instances of modules are listed as
;; occurances and a listener alist structure where keys are occurance names and
;; entries are each a list of occurance names. Whenever an occurance runs, all
;; the entries corresponding to that occurance are pushed on the queue to be
;; run. This model works but its code is not very stable and the simulations
;; are slower.

;; SVL2 implements a simular idea but the listener structure is used to order
;; occurances to have the same effect. The code is much more stable and
;; simulation is faster. Also SVL2 supports a much better flattening
;; functionality for modules that are better off flattened out. In case of a
;; combinational loop, the program will throw an error at the time of
;; translation from SV design to SVL2 design.


(in-package "SVL")

(include-book "svl")

(include-book "svex-lemmas2")

(include-book "bits-sbits")

(include-book "meta/top")

(include-book "svl-openers")

(include-book "svl-guards")

(include-book "macros")

(include-book "sv-update")

(include-book "svl2-openers")
