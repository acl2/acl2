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
(include-book "../../parsetree")
(local (include-book "../../util/arithmetic"))

(defxdoc eliminitial
  :parents (always-top)
  :short "Throw away any @('initial') statements and add non-fatal @(see
warnings) to the affected modules."

  :long "<p>This transform can be run at any time, but it is typically done
somewhere before @(see synthalways), since it will not process modules with
@('initial') statements.</p>

<p>Initial statements can be important for simulation, but are meaningless if
we want to consider the post synthesis/build behavior of the actual part.
Throwing them away, then, is basically reasonable for any back-end tool that
wants to analyze the behavior of the synthesized modules.</p>")

(local (xdoc::set-default-parents eliminitial))

(define vl-module-eliminitial ((x vl-module-p))
  :returns (new-x vl-module-p :hyp :fguard)
  (b* (((vl-module x) x)
       ((when (vl-module->hands-offp x))
        x)
       ((unless x.initials)
        x)
       (warnings
        (warn
         :type :vl-warn-initial
         :msg  "Dropped ~x0 initial statement~s1 from module ~m2.  (This is ~
                generally fine: initial statements are just test bench code ~
                that can be ignored when analyzing the module's behavior.)"
         :args (list (len x.initials)
                     (if (vl-plural-p x.initials) "s" "")
                     x.name)
         :acc x.warnings)))
    (change-vl-module x
                      :initials nil
                      :warnings warnings)))

(defprojection vl-modulelist-eliminitial (x)
  (vl-module-eliminitial x)
  :nil-preservingp t
  :guard (vl-modulelist-p x)
  :result-type vl-modulelist-p)

(define vl-design-eliminitial
  :short "Top-level @(see eliminitial) transform."
  ((x vl-design-p))
  :returns (new-x vl-design-p)
  (b* ((x (vl-design-fix x))
       ((vl-design x) x))
    (change-vl-design x :mods (vl-modulelist-eliminitial x.mods))))
