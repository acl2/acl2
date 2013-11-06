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


(defsection vl-gather-portdecls-with-attribute

  (defund vl-gather-portdecls-with-attribute (x att)
    (declare (xargs :guard (and (vl-portdecllist-p x)
                                (stringp att))))
    (cond ((atom x)
           nil)
          ((assoc-equal att (vl-portdecl->atts (car x)))
           (cons (car x) (vl-gather-portdecls-with-attribute (cdr x) att)))
          (t
           (vl-gather-portdecls-with-attribute (cdr x) att))))

  (local (in-theory (enable vl-gather-portdecls-with-attribute)))

  (defthm vl-portdecllist-p-of-vl-gather-portdecls-with-attribute
    (implies (force (vl-portdecllist-p x))
             (vl-portdecllist-p (vl-gather-portdecls-with-attribute x att)))))



(defsection vl-gather-netdecls-with-attribute

  (defund vl-gather-netdecls-with-attribute (x att)
    (declare (xargs :guard (and (vl-netdecllist-p x)
                                (stringp att))))
    (cond ((atom x)
           nil)
          ((assoc-equal att (vl-netdecl->atts (car x)))
           (cons (car x) (vl-gather-netdecls-with-attribute (cdr x) att)))
          (t
           (vl-gather-netdecls-with-attribute (cdr x) att))))

  (local (in-theory (enable vl-gather-netdecls-with-attribute)))

  (defthm vl-netdecllist-p-of-vl-gather-netdecls-with-attribute
    (implies (force (vl-netdecllist-p x))
             (vl-netdecllist-p (vl-gather-netdecls-with-attribute x att)))))



(defsection vl-gather-regdecls-with-attribute

  (defund vl-gather-regdecls-with-attribute (x att)
    (declare (xargs :guard (and (vl-regdecllist-p x)
                                (stringp att))))
    (cond ((atom x)
           nil)
          ((assoc-equal att (vl-regdecl->atts (car x)))
           (cons (car x) (vl-gather-regdecls-with-attribute (cdr x) att)))
          (t
           (vl-gather-regdecls-with-attribute (cdr x) att))))

  (local (in-theory (enable vl-gather-regdecls-with-attribute)))

  (defthm vl-regdecllist-p-of-vl-gather-regdecls-with-attribute
    (implies (force (vl-regdecllist-p x))
             (vl-regdecllist-p (vl-gather-regdecls-with-attribute x att)))))

