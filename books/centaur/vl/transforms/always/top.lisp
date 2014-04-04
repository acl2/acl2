; VL Verilog Toolkit
; Copyright (C) 2008-2014 Centaur Technology
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

(in-package "VL")
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
                                  ((careful-p booleanp) 't))
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
       (x (xf-cwtime (vl-design-edgesynth x)))

       ;; Handle latch-like blocks.  This is kind of a mess.  I'm not sure
       ;; how many of these transforms are still necessary.  Some of them
       ;; may have only existed to support the old "flopcode" stuff, which
       ;; predated edgesynth
       (x (xf-cwtime (vl-design-stmttemps x)))
       (x (xf-cwtime (vl-design-unelse x)))
       (x (xf-cwtime (vl-design-ifmerge x)))
       (x (xf-cwtime (vl-design-latchsynth x :careful-p careful-p)))

       ;; Any surviving always blocks are just too hard to support.
       (x (xf-cwtime (vl-design-elimalways x))))
    x))
