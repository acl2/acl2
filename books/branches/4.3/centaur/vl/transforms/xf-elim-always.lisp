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
(include-book "../parsetree")
(local (include-book "../util/arithmetic"))



; Ugly.  Throw away any modules with always blocks, except for the latch
; and flop primitives.

(defsection vl-warn-about-bad-always-blocks

  (defund vl-warn-about-bad-always-blocks (alwayses warnings)
    (declare (xargs :guard (and (vl-alwayslist-p alwayses)
                                (vl-warninglist-p warnings))))
    (if (atom alwayses)
        warnings
      (b* ((always1 (car alwayses))
           (warning (make-vl-warning
                     :type :vl-bad-always
                     :msg "~a0: always block is not supported."
                     :args (list always1)
                     :fatalp t
                     :fn 'vl-warn-about-bad-always-blocks)))
          (vl-warn-about-bad-always-blocks (cdr alwayses)
                                           (cons warning warnings)))))

  (local (in-theory (enable vl-warn-about-bad-always-blocks)))

  (defthm vl-warninglist-p-of-vl-warn-about-bad-always-blocks
    (implies (vl-warninglist-p warnings)
             (vl-warninglist-p
              (vl-warn-about-bad-always-blocks alwayses warnings)))))


(defsection vl-module-elim-always

  (defund vl-module-elim-always (x)
    (declare (xargs :guard (vl-module-p x)))
    (b* (((when (vl-module->hands-offp x))
          x)
         (alwayses (vl-module->alwayses x))
         ((unless alwayses)
          x)
         (warnings (vl-module->warnings x))
         (warnings (vl-warn-about-bad-always-blocks alwayses warnings))
         (x-prime  (change-vl-module x :warnings warnings)))
        x-prime))

  (local (in-theory (enable vl-module-elim-always)))

  (defthm vl-module-p-of-vl-module-elim-always
    (implies (force (vl-module-p x))
             (vl-module-p (vl-module-elim-always x))))

  (defthm vl-module->name-of-vl-module-elim-always
    (equal (vl-module->name (vl-module-elim-always x))
           (vl-module->name x))))


(defsection vl-modulelist-elim-always

  (defprojection vl-modulelist-elim-always (x)
    (vl-module-elim-always x)
    :nil-preservingp t
    :guard (vl-modulelist-p x)
    :result-type vl-modulelist-p)

  (defthm vl-modulelist->names-of-vl-modulelist-elim-always
    (equal (vl-modulelist->names (vl-modulelist-elim-always x))
           (vl-modulelist->names x))
    :hints(("Goal" :induct (len x)))))
