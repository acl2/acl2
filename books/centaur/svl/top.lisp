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

;; This book has a Verilog simulation tool: SVL

;; SVL creates an occ listener structure that is used to order occurances such
;; that when run in order will give the correct Verilog simulation result.  The
;; code is deemed stable. Also SVL supports a flattening functionality for
;; sub-modules. In case of a combinational loop, the program will throw an
;; error at the time of translation from SV design to SVL design.


(in-package "SVL")


(include-book "svexl/svexl")
(include-book "svexl/svexl-correct")

(include-book "svex-eval-wog-openers")

(include-book "bits-sbits")

(include-book "macros")

(include-book "svl-openers")

(include-book "svl-flatten")

(include-book "svl-run-to-svex-alist")

(include-book "meta/top")


(xdoc::defxdoc
 acl2::svl
 :parents (acl2::hardware-verification)
 :short "A framework to simulate Verilog designs with retained design hiearchy"
 :long "
<p>Similar to @(see sv::svtv), SVL semantics is converted from @(see acl2::sv)
 to simulate Verilog designs but it can retain design hierarchy by not
 flattening and composing selected modules. It supports combinational and
 sequential circuits but it fails in case of combinational loops.
</p>

<p>  You  need @(see  acl2::VL)  and  @(see  acl2::SV)  designs to  create  SVL
designs. You  can use  functions @(see  svl::svl-flatten-design) to  create SVL
design, and @(see svl::svl-run) to run the generated design.</p>

<p> Using the SVL system, you can perform hierarchical reasoning on Verilog
designs. For combinational submodules, you can have a rewrite rule replacing
@(see svl-run-phase-wog) instance of that submodule with its specification, and
that rule can be applied when rewriting the main module. See @(see
rp::multiplier-verification) for a use case. </p> 
"
 )

