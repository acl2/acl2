; Centaur Hardware Verification Tutorial
; Copyright (C) 2012 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "ACL2")


;                  Centaur Hardware Verification Tutorial
;
; This tutorial walks through the verification of some very simple hardware
; designs using the Centaur books.  These hardware designs are all contrived
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

(include-book "centaur/vl/top" :dir :system)
(include-book "centaur/gl/gl" :dir :system)
(include-book "centaur/aig/g-aig-eval" :dir :system)
(include-book "centaur/esim/stv/stv-top" :dir :system)
(include-book "centaur/esim/stv/stv-debug" :dir :system)
(include-book "centaur/4v-sexpr/top" :dir :system)
(include-book "tools/plev-ccl" :dir :system)
(include-book "centaur/misc/memory-mgmt-raw" :dir :system)

(set-waterfall-parallelism nil) ; for below call of def-gl-clause-processor

; This is critical.  It introduces a GL clause processor that can natively
; execute at least the functions from the above books that get marked with
; add-clause-proc-exec-fns:

(def-gl-clause-processor my-glcp nil)


(defxdoc esim-tutorial
  :parents (esim)
  :short "Placeholder topic for tutorial-related things."

  :long "<p>To see the centaur books tutorial, please go to this file:</p>

@({
centaur/tutorial/intro.lisp
})

<p>in your ACL2 books directory (sometimes called @(':dir :system')).</p>")


; NEXT STEP:
;
; To start the real tutorial, please see alu16.lsp.
