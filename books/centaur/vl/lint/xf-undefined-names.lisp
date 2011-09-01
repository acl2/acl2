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

; BOZO removing this transform temporarily, until I'm sure we need it again,
; since it seems to simpleminded and probably doesn't work quite right
; w.r.t. functions, etc.


;(include-book "../loader/make-implicit-wires")
;(include-book "../mlib/modnamespace")
;(include-book "../mlib/allexprs")
;(local (include-book "../util/arithmetic"))
;(local (include-book "../util/osets"))


; VL-Lint Only.
;
; In our ordinary transformation process for adding implicit wires (see
; make-implicit-wires), we try to properly implement Verilog's rules for adding
; implicit wires.  But in VL-Lint, we'd like to continue even if the module has
; some wires that still need to be declared, so here we add implicit wires for
; any names in the module that aren't declared.
;
; This is perhaps unsound in some way so it shouldn't be used in our ordinary
; transformation process.
;
; We expect this to be run after the ordinary implicit-wires transform, so we
; don't deal with port-implicit wires.  We also don't add any warnings because
; implicit-wires should have done that.

;; (defsection vl-module-add-undefined-names

;;   (defund vl-module-add-undefined-names (x)
;;     (declare (xargs :guard (vl-module-p x)))

;;     (b* (((vl-module x) x)

;;          (declared-names
;;           ;; Set of all explicitly declared names in the module
;;           (mergesort (vl-module->modnamespace-exec x)))

;;          (allnames
;;           ;; All names used anywhere in the module
;;           (b* ((exprs (vl-module-allexprs-exec x nil))
;;                (names (vl-exprlist-names-exec exprs nil)))
;;             (mergesort names)))

;;          (implicit-names (difference allnames declared-names))
;;          (implicit-decls (vl-make-ordinary-implicit-wires x.minloc implicit-names)))
;;       (change-vl-module x
;;                         :netdecls (append implicit-decls x.netdecls))))

;;   (local (in-theory (enable vl-module-add-undefined-names)))

;;   (defthm vl-modulep-of-vl-module-add-undefined-names
;;     (implies (force (vl-module-p x))
;;              (vl-module-p (vl-module-add-undefined-names x))))

;;   (defthm vl-module->name-of-vl-module-add-undefined-names
;;     (equal (vl-module->name (vl-module-add-undefined-names x))
;;            (vl-module->name x))))


;; (defsection vl-modulelist-add-undefined-names

;;   (defprojection vl-modulelist-add-undefined-names (x)
;;     (vl-module-add-undefined-names x)
;;     :guard (vl-modulelist-p x)
;;     :result-type vl-modulelist-p)

;;   (local (in-theory (enable vl-modulelist-add-undefined-names)))

;;   (defthm vl-modulelist->names-of-vl-modulelist-add-undefined-names
;;     (equal (vl-modulelist->names (vl-modulelist-add-undefined-names x))
;;            (vl-modulelist->names x))))

