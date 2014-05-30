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
(include-book "namefactory")
(local (include-book "../util/arithmetic"))
(local (std::add-default-post-define-hook :fix))

(defsection namemangle
  :parents (mlib)
  :short "Basic utilities for name mangling."
  :long "<p>These are some simple functions to do name mangling.  These are
useful when we inline elements from one module into another and want to be sure
they are given fresh names.</p>")

(local (xdoc::set-default-parents namemangle))


(define vl-namemangle-modinsts
  :short "Safely rename module instances, preferring names of the form
@('prefix_{current-name}')."
  ((prefix   stringp)
   (modinsts vl-modinstlist-p)
   (nf       vl-namefactory-p))
  :returns (mv (new-modinsts vl-modinstlist-p)
               (new-nf       vl-namefactory-p))
  (b* (((when (atom modinsts))
        (mv nil (vl-namefactory-fix nf)))
       (instname1      (or (vl-modinst->instname (car modinsts)) "inst"))
       (want1          (str::cat prefix "_" instname1))
       ((mv fresh1 nf) (vl-namefactory-plain-name want1 nf))
       (inst1          (change-vl-modinst (car modinsts) :instname fresh1))
       ((mv insts2 nf) (vl-namemangle-modinsts prefix (cdr modinsts) nf)))
    (mv (cons inst1 insts2) nf))
  ///
  (defmvtypes vl-namemangle-modinsts (true-listp nil))

  (defthm len-of-vl-namemangle-modinsts
    (b* (((mv new-modinsts ?new-nf)
          (vl-namemangle-modinsts loc modinsts nf)))
      (equal (len new-modinsts)
             (len modinsts)))))


(define vl-namemangle-gateinsts
  :short "Safely rename gate instances, preferring names of the form
@('prefix_{current-name}')."
  ((prefix    stringp)
   (gateinsts vl-gateinstlist-p)
   (nf        vl-namefactory-p))
  :returns (mv (new-gateinsts vl-gateinstlist-p)
               (new-nf        vl-namefactory-p))
  (b* (((when (atom gateinsts))
        (mv nil (vl-namefactory-fix nf)))
       (instname1      (or (vl-gateinst->name (car gateinsts)) "g"))
       (want1          (str::cat prefix "_" instname1))
       ((mv fresh1 nf) (vl-namefactory-plain-name want1 nf))
       (inst1          (change-vl-gateinst (car gateinsts) :name fresh1))
       ((mv insts2 nf) (vl-namemangle-gateinsts prefix (cdr gateinsts) nf)))
    (mv (cons inst1 insts2) nf))
  ///
  (defmvtypes vl-namemangle-gateinsts (true-listp nil))

  (defthm len-of-vl-namemangle-gateinsts
    (b* (((mv new-gateinsts ?new-nf)
          (vl-namemangle-gateinsts loc gateinsts nf)))
      (equal (len new-gateinsts)
             (len gateinsts)))))


(define vl-namemangle-netdecls
  :short "Safely try to give these netdecls new names of the form
@('prefix_{current-name}.')"

  ((prefix   stringp)
   (netdecls vl-netdecllist-p)
   (nf       vl-namefactory-p))
  :returns (mv (new-nets vl-netdecllist-p)
               (new-nf   vl-namefactory-p))

  :long "<p>You'll generally want to do something like:</p>

@({
   (pairlis$ (vl-netdecllist->names old-netdecls)
             (vl-netdecllist->names renamed-netdecls))
})

<p>And then use this as a substitution.</p>"

  (b* (((when (atom netdecls))
        (mv nil (vl-namefactory-fix nf)))
       (name1          (vl-netdecl->name (car netdecls)))
       (want1          (str::cat prefix "_" name1))
       ((mv fresh1 nf) (vl-namefactory-plain-name want1 nf))
       (inst1          (change-vl-netdecl (car netdecls) :name fresh1))
       ((mv insts2 nf) (vl-namemangle-netdecls prefix (cdr netdecls) nf)))
    (mv (cons inst1 insts2) nf))
  ///
  (defmvtypes vl-namemangle-netdecls (true-listp nil))

  (defthm len-of-vl-namemangle-netdecls
    (b* (((mv new-netdecls ?new-nf)
          (vl-namemangle-netdecls loc netdecls nf)))
      (equal (len new-netdecls)
             (len netdecls)))))

