; VL 2014 -- VL Verilog Toolkit, 2014 Edition
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

(in-package "VL2014")
(include-book "caseelim")
(include-book "combinational")
(include-book "edgesplit")
(include-book "edgesynth")
(include-book "elimalways")
(include-book "eliminitial")
(include-book "latchsynth")
(include-book "stmttemps")
(include-book "unelse")
(include-book "ifmerge")
(include-book "../../util/cwtime")

(defxdoc always-top
  :parents (transforms)
  :short "Transforms for synthesizing @('always') blocks.")

(local (xdoc::set-default-parents always-top))

(define vl-design-always-backend ((x vl-design-p)
                                  &key
                                  ((careful-p booleanp) 't)
                                  vecp)
  :returns (new-x vl-design-p)
  :short "Normal way to process @('always') blocks after sizing."

  :long "<p>This is a combination of several other transforms.  It is the
typical way that we expect to process @('always') blocks.</p>

<p>Modules that survive this transform will be free of @('always')
blocks&mdash;or, well, that's true except for the primitive VL flop and latch
modules.</p>

<p>Modules that are too difficult to process and will end up having fatal @(see
warnings) added.</p>"

  (b* (;; Preliminary simplifications
       (x (xf-cwtime (vl-design-caseelim x)))
       (x (xf-cwtime (vl-design-eliminitial x)))

       ;; Handle combinational blocks
       (x (xf-cwtime (vl-design-combinational-elim x)))

       ;; Handle edge-triggered blocks
       (x (xf-cwtime (vl-design-edgesplit x)))
       (x (xf-cwtime (vl-design-edgesynth x :Vecp vecp)))

       ;; Handle latch-like blocks.  This is kind of a mess.  I'm not sure
       ;; how many of these transforms are still necessary.  Some of them
       ;; may have only existed to support the old "flopcode" stuff, which
       ;; predated edgesynth

       ;; I don't think we want to run this.  This was only meant for flop-like
       ;; blocks and it doesn't do anything unless we match posedge clk.
       ;;   (x (xf-cwtime (vl-design-stmttemps x)))

       (x (xf-cwtime (vl-design-unelse x)))
       (x (xf-cwtime (vl-design-ifmerge x)))
       (x (xf-cwtime (vl-design-latchsynth x :careful-p careful-p :vecp vecp)))

       ;; Any surviving always blocks are just too hard to support.
       (x (xf-cwtime (vl-design-elimalways x))))
    x))
