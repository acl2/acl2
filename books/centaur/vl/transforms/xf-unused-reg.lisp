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
(include-book "../mlib/filter")
(local (include-book "../util/arithmetic"))

(defsection elim-unused-regs
  :parents (transforms)
  :short "Remove any @('reg') and variable declarations that are never used.")

(local (xdoc::set-default-parents elim-unused-regs))

;; (define vl-regdecllist-elim-unused-regs
;;   ((regs   vl-regdecllist-p)
;;    (used   string-listp)
;;    (ualist (equal ualist (make-lookup-alist used))))
;;   :returns (new-regs vl-regdecllist-p :hyp :fguard)
;;   (cond ((atom regs)
;;          nil)
;;         ((fast-memberp (vl-regdecl->name (car regs)) used ualist)
;;          ;; It's used, keep it
;;          (cons (car regs) (vl-regdecllist-elim-unused-regs (cdr regs) used ualist)))
;;         (t
;;          ;; Not used, eliminate it.
;;          (vl-regdecllist-elim-unused-regs (cdr regs) used ualist))))

(define vl-module-elim-unused-regs ((x vl-module-p))
  :returns (new-x vl-module-p :hyp :fguard)
  (b* (((vl-module x) x)
       ((unless (or (consp x.regdecls)
                    (consp x.vardecls)))
        ;; Optimization.  Don't need to do anything if there aren't any
        ;; registers anyway.
        x)
       (used       (vl-exprlist-names (vl-module-allexprs x)))
       (new-regs   (and (consp x.regdecls)
                        (vl-keep-regdecls used x.regdecls)))
       (new-vars   (and (consp x.vardecls)
                        (vl-keep-vardecls used x.vardecls)))

       ((when (and (same-lengthp new-regs x.regdecls)
                   (same-lengthp new-vars x.vardecls)))
        ;; Optimization.  Don't need to do anything more unless we threw out
        ;; some registers.
        x)

       (warnings x.warnings)

       (old-regnames    (mergesort (vl-regdecllist->names x.regdecls)))
       (new-regnames    (mergesort (vl-regdecllist->names new-regs)))
       (unused-regnames (difference old-regnames new-regnames))
       (warnings (if unused-regnames
                     (warn :type :vl-warn-unused-reg
                           :msg "In ~m0, eliminating spurious registers ~&1."
                           :args (list (vl-module->name x) unused-regnames))
                   warnings))

       (old-varnames    (mergesort (vl-vardecllist->names x.vardecls)))
       (new-varnames    (mergesort (vl-vardecllist->names new-vars)))
       (unused-varnames (difference old-varnames new-varnames))
       (warnings (if unused-varnames
                     (warn :type :vl-warn-unused-var
                           :msg "In ~m0, eliminating spurious variables ~&1."
                           :args (list (vl-module->name x) unused-varnames))
                   warnings))

       (new-x (change-vl-module x
                                :regdecls new-regs
                                :vardecls new-vars
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


