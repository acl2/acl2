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
(include-book "namefactory")
(local (include-book "../util/arithmetic"))


(defsection namemangle
  :parents (mlib)
  :short "Basic utilities for name mangling."
  :long "<p>These are some simple functions to do name mangling.  These are
useful when we inline elements from one module into another and want to be sure
they are given fresh names.</p>")


(defsection vl-namemangle-modinsts
  :parents (namemangle)
  :short "Safely rename module instances, preferring names of the form
<tt>prefix_{current-name}</tt>."

  (defund vl-namemangle-modinsts (prefix modinsts nf)
    "Returns (MV MODINSTS' NF')"
    (declare (xargs :guard (and (stringp prefix)
                                (vl-modinstlist-p modinsts)
                                (vl-namefactory-p nf))))
    (b* (((when (atom modinsts))
          (mv nil nf))
         (instname1      (or (vl-modinst->instname (car modinsts)) "inst"))
         (want1          (str::cat prefix "_" instname1))
         ((mv fresh1 nf) (vl-namefactory-plain-name want1 nf))
         (inst1          (change-vl-modinst (car modinsts) :instname fresh1))
         ((mv insts2 nf) (vl-namemangle-modinsts prefix (cdr modinsts) nf)))
      (mv (cons inst1 insts2) nf)))

  (local (in-theory (enable vl-namemangle-modinsts)))

  (defmvtypes vl-namemangle-modinsts (true-listp nil))

  (defthm vl-namemangle-modinsts-basics
    (let ((ret (vl-namemangle-modinsts loc modinsts nf)))
      (implies (and (force (vl-modinstlist-p modinsts))
                    (force (vl-namefactory-p nf)))
               (and (vl-modinstlist-p (mv-nth 0 ret))
                    (vl-namefactory-p (mv-nth 1 ret))))))

  (defthm len-of-vl-namemangle-modinsts
    (let ((ret (vl-namemangle-modinsts loc modinsts nf)))
      (equal (len (mv-nth 0 ret))
             (len modinsts)))))


(defsection vl-namemangle-gateinsts
  :parents (namemangle)
  :short "Safely rename gate instances, preferring names of the form
<tt>prefix_{current-name}</tt>."

  (defund vl-namemangle-gateinsts (prefix gateinsts nf)
    "Returns (MV GATEINSTS' NF')"
    (declare (xargs :guard (and (stringp prefix)
                                (vl-gateinstlist-p gateinsts)
                                (vl-namefactory-p nf))))
    (b* (((when (atom gateinsts))
          (mv nil nf))
         (instname1      (or (vl-gateinst->name (car gateinsts)) "g"))
         (want1          (str::cat prefix "_" instname1))
         ((mv fresh1 nf) (vl-namefactory-plain-name want1 nf))
         (inst1          (change-vl-gateinst (car gateinsts) :name fresh1))
         ((mv insts2 nf) (vl-namemangle-gateinsts prefix (cdr gateinsts) nf)))
      (mv (cons inst1 insts2) nf)))

  (local (in-theory (enable vl-namemangle-gateinsts)))

  (defmvtypes vl-namemangle-gateinsts (true-listp nil))

  (defthm vl-namemangle-gateinsts-basics
    (let ((ret (vl-namemangle-gateinsts loc gateinsts nf)))
      (implies (and (force (vl-gateinstlist-p gateinsts))
                    (force (vl-namefactory-p nf)))
               (and (vl-gateinstlist-p (mv-nth 0 ret))
                    (vl-namefactory-p (mv-nth 1 ret))))))

  (defthm len-of-vl-namemangle-gateinsts
    (let ((ret (vl-namemangle-gateinsts loc gateinsts nf)))
      (equal (len (mv-nth 0 ret))
             (len gateinsts)))))


(defsection vl-namemangle-netdecls
  :parents (namemangle)
  :short "Safely try to give these netdecls new names of the form
<tt>prefix_{current-name}.</tt>"

  :long "<p>You'll generally want to do something like:</p>

<code>
   (pairlis$ (vl-netdecllist->names old-netdecls)
             (vl-netdecllist->names renamed-netdecls))
</code>

<p>And then use this as a substitution.</p>"

  (defund vl-namemangle-netdecls (prefix netdecls nf)
    "Returns (MV NETDECLS' NF')"
    (declare (xargs :guard (and (stringp prefix)
                                (vl-netdecllist-p netdecls)
                                (vl-namefactory-p nf))))
    (b* (((when (atom netdecls))
          (mv nil nf))
         (name1          (vl-netdecl->name (car netdecls)))
         (want1          (str::cat prefix "_" name1))
         ((mv fresh1 nf) (vl-namefactory-plain-name want1 nf))
         (inst1          (change-vl-netdecl (car netdecls) :name fresh1))
         ((mv insts2 nf) (vl-namemangle-netdecls prefix (cdr netdecls) nf)))
      (mv (cons inst1 insts2) nf)))

  (local (in-theory (enable vl-namemangle-netdecls)))

  (defmvtypes vl-namemangle-netdecls (true-listp nil))

  (defthm vl-namemangle-netdecls-basics
    (let ((ret (vl-namemangle-netdecls loc netdecls nf)))
      (implies (and (force (vl-netdecllist-p netdecls))
                    (force (vl-namefactory-p nf)))
               (and (vl-netdecllist-p (mv-nth 0 ret))
                    (vl-namefactory-p (mv-nth 1 ret))))))

  (defthm len-of-vl-namemangle-netdecls
    (let ((ret (vl-namemangle-netdecls loc netdecls nf)))
      (equal (len (mv-nth 0 ret))
             (len netdecls)))))

