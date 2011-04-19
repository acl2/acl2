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
(include-book "../mlib/lvalues")
(include-book "../mlib/wirealist")
(local (include-book "../util/arithmetic"))


; Notes about our heuristics:
;
;  - Warnings are minor if "mux" is in the module name.
;  - Warnings are minor for wires whose names include "mux" or "ph1"
;
; BOZO It would be nice to also only issue minor warnings if the module has
; transistor-level stuff in it.  But that's kind of hard to define (e.g.,
; wrapper modules for transistors like upmos).  So, for now I don't try to do
; that.



; Most of the tools we need for finding multiply-driven wires are already
; available.  Recall, from xf-make-defm-command:
;
; (vl-module-wirealist mod warnings) -> (successp warnings walist)
;
;   * walist is a fast alist and must be freed
;
;   * only builds the walist for netdecls
;     (doesn't get regdecls, implicit wires)
;
;   * fails if resulting wires aren't unique
;     (should be extraordinarily unlikely)
;
; And also recall from mu-lvalue:
;
; (vl-msb-expr-bitlist x walist warnings) -> (mv successp warnings bitlist)
;
;   * x is an expression that can have:  constant/weird integers, bit/part
;     selects, concatenations, replications
;
;       NOTE: this is a superset of the valid lvalues
;
;   * fails gracefully (successp = nil, extends warnings) when x is not
;     of this form


(defsection vl-multidrive-filter-innocuous-wires

  (defund vl-multidrive-innocuous-wirename-p (x)
    (declare (xargs :guard (symbolp x)))
    (let ((name (symbol-name x)))
      (or (equal name "latchout")
          (equal name "vss0")
          (equal name "vdd0")
          (equal name "vdd3")
          (str::isubstrp "mux" name)
          (str::isubstrp "clk" name)
          (str::isubstrp "net" name)
          (str::isubstrp "ph1" name))))

  (defund vl-multidrive-filter-innocuous-wires (x innocuous other)
    (declare (xargs :guard (symbol-listp x)))
    (b* (((when (atom x))
          (mv innocuous other))
         (car-innocuousp (vl-multidrive-innocuous-wirename-p (car x)))
         (innocuous (if car-innocuousp
                        (cons (car x) innocuous)
                      innocuous))
         (other (if car-innocuousp
                    other
                  (cons (car x) other))))
      (vl-multidrive-filter-innocuous-wires (cdr x) innocuous other)))

  (local (in-theory (enable vl-multidrive-filter-innocuous-wires)))

  (defthm vl-multidrive-filter-innocuous-wires-basics
    (implies
     (and (force (symbol-listp x))
          (force (symbol-listp innocuous))
          (force (symbol-listp other)))
     (let ((result (vl-multidrive-filter-innocuous-wires x innocuous other)))
       (and (symbol-listp (mv-nth 0 result))
            (symbol-listp (mv-nth 1 result)))))))





(defsection vl-module-multidrive-detect

  (defund vl-module-multidrive-detect (x)
    "Returns x-prime"
    (declare (xargs :guard (vl-module-p x)))
    (b* (((vl-module x) x)

         ;; Note: walist only includes net declarations (it omits registers)
         ((mv successp warnings walist)
          (vl-module-wirealist x x.warnings))
         ((unless successp)
          (fast-alist-free walist)
          (b* ((w (make-vl-warning
                   :type :vl-multidrive-detect-fail
                   :msg "Wire alist construction for ~m0 failed.  We will ~
                         not be able to detect multiply driven wires in ~
                         this module."
                   :args (list x.name)
                   :fatalp nil
                   :fn 'vl-module-multidrive-detect)))
            (change-vl-module x :warnings (cons w warnings))))

         (lvalexprs
          ;; We explicitly remove any initial/always statements because all
          ;; procedural assignments must be to registers instead of wires, and
          ;; this will cause problems since the registers aren't included in the
          ;; wire alist, and we also think it's pretty legitimate for registers
          ;; to be assigned to in multiple places (e.g., it could be given an
          ;; initial value in an initial statement, and be updated in an always
          ;; statement), so we don't want to cause any warnings about them.
          (vl-module-lvalexprs (change-vl-module x
                                                 :alwayses nil
                                                 :initials nil)))
         ((mv successp warnings allbits)
          (vl-msb-exprlist-bitlist lvalexprs walist warnings))
         (warnings
          (if successp
              warnings
            (cons (make-vl-warning
                   :type :vl-multidrive-detect-incomplete
                   :msg "Our detection of multiply-driven wires in ~m0 may be ~
                         incomplete because we failed to generate bit-lists for ~
                         all lvalues.  This is probably caused by a malformed ~
                         lvalue?  Check other warnings for vl-msb-*-bitlist.  ~
                         BOZO this error message is terrible, Jared should make ~
                         it better."
                   :args (list (vl-module->name x))
                   :fatalp nil
                   :fn 'vl-module-multidrive-detect)
                  warnings)))

         (badbits (duplicated-members allbits))

         ((mv minor-bad major-bad)
          ;; We treat everything as minor if it's in a module that has mux in
          ;; its name.
          (if (str::substrp "mux" x.name)
              (mv badbits nil)
            (vl-multidrive-filter-innocuous-wires badbits nil nil)))

         (minor-names
          (if (vl-emodwirelist-p minor-bad)
              (vl-verilogify-emodwirelist minor-bad)
            ;; Expect this not to happen but it wouldn't be too bad.
            (symbol-list-names minor-bad)))

         (major-names
          (if (vl-emodwirelist-p major-bad)
              (vl-verilogify-emodwirelist major-bad)
            ;; Expect this not to happen but it wouldn't be too bad.
            (symbol-list-names major-bad)))

         (warnings
          (if (not major-names)
              warnings
            (cons (make-vl-warning
                   :type :vl-warn-multidrive
                   :msg "Wires ~&0 are driven by multiple sources.  This might ~
                         be expected (e.g., for muxes), but could also suggest ~
                         a copy/paste error."
                   :args (list major-names)
                   :fatalp nil
                   :fn 'vl-module-multidrive-detect)
                  warnings)))

         (warnings
          (if (not minor-names)
              warnings
            (cons (make-vl-warning
                   :type :vl-warn-multidrive-minor
                   :msg "Wires ~&0 are driven by multiple sources.  This is a ~
                         minor warning because our heuristics say this wire ~
                         is probably supposed to have multiple drivers.  But in ~
                         rare cases, this might suggeset a copy/paste error."
                   :args (list minor-names)
                   :fatalp nil
                   :fn 'vl-module-multidrive-detect)
                  warnings))))

      (change-vl-module x :warnings warnings)))

  (local (in-theory (enable vl-module-multidrive-detect)))

  (defthm vl-module-p-of-vl-module-multidrive-detect
    (implies (force (vl-module-p x))
             (vl-module-p (vl-module-multidrive-detect x))))

  (defthm vl-module->name-of-vl-module-multidrive-detect
    (equal (vl-module->name (vl-module-multidrive-detect x))
           (vl-module->name x))))



(defsection vl-modulelist-multidrive-detect

  (defprojection vl-modulelist-multidrive-detect (x)
    (vl-module-multidrive-detect x)
    :guard (vl-modulelist-p x)
    :nil-preservingp nil)

  (local (in-theory (enable vl-modulelist-multidrive-detect)))

  (defthm vl-modulelist-p-of-vl-modulelist-multidrive-detect
    (implies (force (vl-modulelist-p x))
             (vl-modulelist-p (vl-modulelist-multidrive-detect x))))

  (defthm vl-modulelist->names-of-vl-modulelist-multidrive-detect
    (equal (vl-modulelist->names (vl-modulelist-multidrive-detect x))
           (vl-modulelist->names x))))
