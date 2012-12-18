; VL Verilog Toolkit
; Copyright (C) 2008-2011 Centaur Technology
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

(define vl-modulelist-always-backend ((mods vl-modulelist-p)
                                       &key
                                       ((careful-p booleanp) 't))
  :returns (new-mods :hyp :fguard
                     (and (vl-modulelist-p new-mods)
                          (no-duplicatesp-equal (vl-modulelist->names new-mods))))
  :parents (always-top)
  :short "Normal way to process @('always') blocks after sizing."

  :long "<p>This is a combination of several other transforms.  It is the
typical way that we expect to process @('always') blocks.</p>

<p>The heart of this transform is @(see synthalways).  But before we run it, we
first do several preprocessing steps:</p>

<ul>
<li>@(see eliminitial) to get rid of any @('initial') statements</li>
<li>@(see elimnegedge) to get rid of @('negedge clk') constructs</li>
<li>@(see stmttemps) to split out complex conditions and rhs expressions</li>
<li>@(see unelse) to reduce @('if/else') statements to just @('if')s</li>
</ul>

<p>After these steps, our main @(see synthalways) transform converts supported
@('always') blocks into explicit instances of primitive flop/latch modules.
And, as a last step, we use @(see elimalways) to remove any unsupported always
blocks that weren't synthesized, and add fatal warnings to their modules.</p>"

  (b* ((mods (xf-cwtime (vl-modulelist-eliminitial mods)
                        :name xf-eliminitial))
       (mods (xf-cwtime (vl-modulelist-elimnegedge mods)
                        :name xf-elimnegedge))
       (mods (xf-cwtime (vl-modulelist-stmttemps mods)
                        :name xf-stmttemps))
       (mods (xf-cwtime (vl-modulelist-unelse mods)
                        :name xf-unelse))
       (mods (xf-cwtime (vl-modulelist-ifmerge mods)
                        :name xf-ifmerge))
       (mods (xf-cwtime (vl-modulelist-synthalways mods
                                                   :careful-p careful-p)
                        :name xf-synthalways))
       (mods (xf-cwtime (vl-modulelist-elimalways mods)
                        :name xf-elimalways)))
    mods))

