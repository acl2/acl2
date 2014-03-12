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
(include-book "elimalways")
(include-book "eliminitial")
(include-book "elimnegedge")
(include-book "synthalways")
(include-book "stmtrewrite")
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

<p>The heart of this transform is @(see synthalways).  But before we run it, we
first do several preprocessing steps:</p>

<ul>
<li>@(see caseelim) to get rid of @('case') statements</li>
<li>@(see eliminitial) to get rid of any @('initial') blocks</li>
<li>@(see elimnegedge) to get rid of @('negedge clk') constructs</li>
<li>@(see stmttemps) to split out complex conditions and rhs expressions</li>
<li>@(see unelse) to reduce @('if/else') statements to just @('if')s</li>
</ul>

<p>After these steps, our main @(see synthalways) transform converts supported
@('always') blocks into explicit instances of primitive flop/latch modules.
And, as a last step, we use @(see elimalways) to remove any unsupported always
blocks that weren't synthesized, and add fatal warnings to their modules.</p>"

  (b* ((x (xf-cwtime (vl-design-caseelim x)
                     :name xf-caseelim))
       (x (xf-cwtime (vl-design-eliminitial x)
                     :name xf-eliminitial))
       (x (xf-cwtime (vl-design-elimnegedge x)
                     :name xf-elimnegedge))
       (x (xf-cwtime (vl-design-stmttemps x)
                     :name xf-stmttemps))
       (x (xf-cwtime (vl-design-unelse x)
                     :name xf-unelse))
       (x (xf-cwtime (vl-design-ifmerge x)
                     :name xf-ifmerge))
       (x (xf-cwtime (vl-design-synthalways x :careful-p careful-p)
                     :name xf-synthalways))
       (x (xf-cwtime (vl-design-elimalways x)
                     :name xf-elimalways)))
    x))
