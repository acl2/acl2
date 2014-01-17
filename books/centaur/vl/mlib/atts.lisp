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
(include-book "../parsetree")
(local (include-book "../util/arithmetic"))

(define vl-gather-portdecls-with-attribute ((x vl-portdecllist-p)
                                            (att stringp))
  :returns (sub-x vl-portdecllist-p :hyp :fguard)
  (cond ((atom x)
         nil)
        ((assoc-equal att (vl-portdecl->atts (car x)))
         (cons (car x) (vl-gather-portdecls-with-attribute (cdr x) att)))
        (t
         (vl-gather-portdecls-with-attribute (cdr x) att))))

(define vl-gather-netdecls-with-attribute ((x vl-netdecllist-p)
                                           (att stringp))
  :returns (sub-x vl-netdecllist-p :hyp :fguard)
  (cond ((atom x)
         nil)
        ((assoc-equal att (vl-netdecl->atts (car x)))
         (cons (car x) (vl-gather-netdecls-with-attribute (cdr x) att)))
        (t
         (vl-gather-netdecls-with-attribute (cdr x) att))))

(define vl-gather-regdecls-with-attribute ((x vl-regdecllist-p)
                                           (att stringp))
  :returns (sub-x vl-regdecllist-p :hyp :fguard)
  (cond ((atom x)
         nil)
        ((assoc-equal att (vl-regdecl->atts (car x)))
         (cons (car x) (vl-gather-regdecls-with-attribute (cdr x) att)))
        (t
         (vl-gather-regdecls-with-attribute (cdr x) att))))
