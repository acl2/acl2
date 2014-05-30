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
(local (std::add-default-post-define-hook :fix))

(defxdoc elimalways
  :parents (always-top)
  :short "Add fatal @(see warnings) to any modules with @('always') blocks, and
throw away all @('always') blocks."

  :long "<p>This is typically the very last thing we do to process @('always')
blocks.  It is meant as a catch-all for @('always') blocks that are too complex
to handle.</p>")

(local (xdoc::set-default-parents elimalways))

(define vl-warn-about-bad-always-blocks ((x        vl-alwayslist-p)
                                         (warnings vl-warninglist-p))
  :returns (warnings vl-warninglist-p)
  (b* (((when (atom x))
        (ok))
       (always1 (vl-always-fix (car x)))
       (warnings (fatal :type :vl-bad-always
                        :msg "~a0: always block is not supported."
                        :args (list always1))))
    (vl-warn-about-bad-always-blocks (cdr x) warnings)))

(define vl-module-elimalways ((x vl-module-p))
  :returns (new-x vl-module-p)
  (b* ((x (vl-module-fix x))
       ((vl-module x) x)
       ((when (vl-module->hands-offp x))
        x)
       ((unless x.alwayses)
        x)
       (warnings (vl-warn-about-bad-always-blocks x.alwayses x.warnings)))
    (change-vl-module x
                      :alwayses nil
                      :warnings warnings)))

(defprojection vl-modulelist-elimalways ((x vl-modulelist-p))
  :returns (new-x vl-modulelist-p)
  (vl-module-elimalways x))

(define vl-design-elimalways
  :short "Top-level @(see elimalways) transform."
  ((x vl-design-p))
  :returns (new-x vl-design-p)
  (b* (((vl-design x) x))
    (change-vl-design x :mods (vl-modulelist-elimalways x.mods))))
