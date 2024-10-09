; Copyright (C) Intel Corporation
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

(in-package "SV")

(include-book "assume-to-sva")

(defsection |Generating SVAs from Assumptions|
  :short "Converting SVTV-based proof assumptions into SystemVerilog assertions."
  :long
  "

<h3> ASSUME-to-SVA </h3>

<p> Proving the correct execution of a micro-operation in a module (or module
instance) of an RTL design typically assumes some properties about the
enclosing environment. For example, in order to carry out a proof about a
multi-stage ALU that accepts opcodes with different latencies, we assume that
opcodes from previous stages do not overwrite the result bus.</p>

<p> This tool converts ACL2 SVTV-based proof assumptions into SystemVerilog
Assertions (SVAs). The SVAs can then be provided to dynamic validation tests,
which will run these assertions and report coverage and failures of these
assertions.</p>

<h2> Assumption Format </h2>

<p>This tool supports converting assumption terms of the following form:</p>

<ol>
<li>Atom: Integers, T or NIL</li>
<li>Function that is supported for conversion into SystemVerilog.</li>
<li>Function with constant arguments, which will be evaluated.</li>
<li>Macros that can be expanded to supported functions or functions with
constant arguments.</li>
<li>Function calls that can be rewritten or expanded into a term consisting of
supported functions or atoms.</li>
</ol>

<p>The functions that are supported for conversion into SystemVerilog: @(`(strip-cars *acl2-fn-to-vl*)`)</p>

")
