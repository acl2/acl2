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
(include-book "../mlib/allexprs")
(include-book "../mlib/modnamespace")
(local (include-book "../util/arithmetic"))

(defsection elim-unused-regs
  :parents (transforms)
  :short "Remove any @('reg') declarations that are never used.")

(local (xdoc::set-default-parents elim-unused-regs))

(define vl-regdecllist-elim-unused-regs
  ((regs   vl-regdecllist-p)
   (used   string-listp)
   (ualist (equal ualist (make-lookup-alist used))))
  :returns (new-regs vl-regdecllist-p :hyp :fguard)
  (cond ((atom regs)
         nil)
        ((fast-memberp (vl-regdecl->name (car regs)) used ualist)
         ;; It's used, keep it
         (cons (car regs) (vl-regdecllist-elim-unused-regs (cdr regs) used ualist)))
        (t
         ;; Not used, eliminate it.
         (vl-regdecllist-elim-unused-regs (cdr regs) used ualist))))

(define vl-module-elim-unused-regs ((x vl-module-p))
  :returns (new-x vl-module-p :hyp :fguard)
  (b* ((regs (vl-module->regdecls x))
       ((unless (consp regs))
        ;; Optimization.  Don't need to do anything if there aren't any
        ;; registers anyway.
        x)
       (used       (vl-exprlist-names (vl-module-allexprs x)))
       (ualist     (make-lookup-alist used))
       (regs-prime (vl-regdecllist-elim-unused-regs regs used ualist))
       (-          (fast-alist-free ualist))
       ((when (same-lengthp regs-prime regs))
        ;; Optimization.  Don't need to do anything more unless we threw
        ;; out some registers.
        x)
       (old-names (mergesort (vl-regdecllist->names regs)))
       (new-names (mergesort (vl-regdecllist->names regs-prime)))
       (unused-names (difference old-names new-names))
       (warnings (warn :type :vl-warn-unused-reg
                       :msg "In ~m0, eliminating spurious registers ~&1."
                       :args (list (vl-module->name x) unused-names)
                       :acc (vl-module->warnings x)))
       (new-x (change-vl-module x
                                :regdecls regs-prime
                                :warnings warnings)))
    new-x))

(defprojection vl-modulelist-elim-unused-regs (x)
  (vl-module-elim-unused-regs x)
  :guard (vl-modulelist-p x)
  :result-type vl-modulelist-p
  :nil-preservingp t)

(define vl-design-elim-unused-regs
  :short "Top-level @(see elim-unused-regs) transform."
  ((x vl-design-p))
  :returns (new-x vl-design-p)
  (b* ((x (vl-design-fix x))
       ((vl-design x) x))
    (change-vl-design x :mods (vl-modulelist-elim-unused-regs x.mods))))


