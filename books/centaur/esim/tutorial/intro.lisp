; ESIM Hardware Verification Tutorial
; Copyright (C) 2008-2015 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
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
; Original author: Jared Davis <jared@centtech.com>

(in-package "ACL2")


; NOTE ---- ESIM is still available but it is no longer being actively
; maintained.  The successor of ESIM is SVEX.  If you don't already have
; projects based on ESIM, you should probably skip this tutorial and learn
; about SVEX instead.



;                  ESIM Hardware Verification Tutorial
;
; This tutorial walks through the verification of some very simple hardware
; designs using Centaur's ESIM books.  These hardware designs are all contrived
; and are far simpler than real hardware.  But this makes them easy to
; understand and verify.
;
; The general flow is:
;
;  - We introduce a few (toy) hardware designs as Verilog modules.
;
;  - We use the VL library to translate these Verilog designs into the E
;    hardware description language.
;
;  - We write some STVs (symbolic test vectors) for the ESIM symbolic
;    simulator.  These test vectors capture certain sets of executions of the
;    modules.
;
;  - We use the GL framework to prove that these executions always satisfy
;    certain correctness properties.
;
; We also make some false conjectures to illustrate debugging features, e.g.,
; dumping out waveforms.
;
;
; NOTE: Before you begin, we assume you have followed the instructions in
; centaur/books/README.html and gotten the Centaur books built!



; intro.lisp
;
; This book just contains a necessary base set of books for using VL, ESIM, and
; GL all together.  Our other tutorial books will include intro.lisp as a
; starting point.

; BOZO probably work on making these includes more coherent.

(include-book "centaur/esim/defmodules" :dir :system)
(include-book "centaur/gl/gl" :dir :system)
(include-book "centaur/aig/g-aig-eval" :dir :system)
(include-book "centaur/esim/stv/stv-top" :dir :system)
(include-book "centaur/esim/stv/stv-debug" :dir :system)
(include-book "centaur/4v-sexpr/top" :dir :system)
(include-book "tools/plev-ccl" :dir :system)
(include-book "centaur/misc/memory-mgmt" :dir :system)
(include-book "misc/without-waterfall-parallelism" :dir :system)

; This is critical.  It introduces a GL clause processor that can natively
; execute at least the functions from the above books that get marked with
; add-clause-proc-exec-fns:

(without-waterfall-parallelism
(def-gl-clause-processor my-glcp))


; NEXT STEP:
;
; To start the real tutorial, please see alu16.lsp.
