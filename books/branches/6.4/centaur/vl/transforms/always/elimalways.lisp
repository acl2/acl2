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
(include-book "../../parsetree")
(local (include-book "../../util/arithmetic"))

(defxdoc elimalways
  :parents (always-top)
  :short "Add fatal @(see warnings) to any modules with @('always') blocks, and
throw away all @('always') blocks."

  :long "<p>This is typically the very last thing we do to process @('always')
blocks.  It is meant as a catch-all for @('always') blocks that are too complex
to handle.</p>")

(define vl-warn-about-bad-always-blocks ((x        vl-alwayslist-p)
                                         (warnings vl-warninglist-p))
  :returns (warnings vl-warninglist-p :hyp :fguard)
  :parents (elimalways)
  (b* (((when (atom x))
        warnings)
       (warnings (fatal :type :vl-bad-always
                        :msg "~a0: always block is not supported."
                        :args (list (car x)))))
    (vl-warn-about-bad-always-blocks (cdr x) warnings)))

(define vl-module-elimalways ((x vl-module-p))
  :returns (new-x vl-module-p :hyp :fguard)
  :parents (elimalways)
  (b* (((vl-module x) x)
       ((when (vl-module->hands-offp x))
        x)
       ((unless x.alwayses)
        x)
       (warnings (vl-warn-about-bad-always-blocks x.alwayses x.warnings)))
    (change-vl-module x
                      :alwayses nil
                      :warnings warnings))
  ///
  (defthm vl-module->name-of-vl-module-elimalways
    (equal (vl-module->name (vl-module-elimalways x))
           (vl-module->name x))))

(defprojection vl-modulelist-elimalways (x)
  (vl-module-elimalways x)
  :nil-preservingp t
  :guard (vl-modulelist-p x)
  :result-type vl-modulelist-p
  :parents (elimalways)
  :short "Top-level elimalways transform."
  :rest
  ((defthm vl-modulelist->names-of-vl-modulelist-elimalways
     (equal (vl-modulelist->names (vl-modulelist-elimalways x))
            (vl-modulelist->names x)))))

