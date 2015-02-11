; VL 2014 -- VL Verilog Toolkit, 2014 Edition
; Copyright (C) 2008-2015 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "VL2014")
(include-book "../mlib/namefactory")
(local (include-book "../util/arithmetic"))
(local (std::add-default-post-define-hook :fix))

(defxdoc addinstnames
  :parents (transforms)
  :short "Name any unnamed gate or module instances"

  :long "<p>This transformation does nothing more than generate a name for
every gate and module instance which are unnamed.  The names are safely
generated using a @(see vl-namefactory-p) and will have names such as
@('modinst_11') and @('gateinst_46').</p>")

(local (xdoc::set-default-parents addinstnames))

(define vl-modinst-addinstnames ((x  vl-modinst-p)
                                 (nf vl-namefactory-p))
  :returns (mv (new-x vl-modinst-p)
               (nf    vl-namefactory-p))
  :short "Name a module instance, if necessary."
  (b* (((when (vl-modinst->instname x))
        ;; No need to generate a name.
        (mv (vl-modinst-fix x) (vl-namefactory-fix nf)))
       ((mv new-name nf) (vl-namefactory-indexed-name "modinst" nf))
       (new-x            (change-vl-modinst x :instname new-name)))
    (mv new-x nf)))

(define vl-modinstlist-addinstnames ((x  vl-modinstlist-p)
                                     (nf vl-namefactory-p))
  :returns (mv (new-x vl-modinstlist-p)
               (nf    vl-namefactory-p))
  :short "Name unnamed module instances."
  (b* (((when (atom x))
        (mv x (vl-namefactory-fix nf)))
       ((mv car nf) (vl-modinst-addinstnames (car x) nf))
       ((mv cdr nf) (vl-modinstlist-addinstnames (cdr x) nf)))
    (mv (cons car cdr) nf)))

(define vl-gateinst-addinstnames ((x  vl-gateinst-p)
                                  (nf vl-namefactory-p))
  :returns (mv (new-x vl-gateinst-p)
               (nf    vl-namefactory-p))
  :short "Name a gate instance, if necessary."
  (b* (((when (vl-gateinst->name x))
        ;; No need to generate a name.
        (mv (vl-gateinst-fix x) (vl-namefactory-fix nf)))
       ((mv new-name nf) (vl-namefactory-indexed-name "gateinst" nf))
       (new-x            (change-vl-gateinst x :name new-name)))
    (mv new-x nf)))

(define vl-gateinstlist-addinstnames ((x vl-gateinstlist-p)
                                      (nf vl-namefactory-p))
  :returns (mv (new-x vl-gateinstlist-p)
               (nf    vl-namefactory-p))
  :short "Name unnamed gate instances."
  (b* (((when (atom x))
        (mv x (vl-namefactory-fix nf)))
       ((mv car nf) (vl-gateinst-addinstnames (car x) nf))
       ((mv cdr nf) (vl-gateinstlist-addinstnames (cdr x) nf)))
    (mv (cons car cdr) nf)))

(define vl-modinstlist-all-named-p ((x vl-modinstlist-p))
  :short "Are there any module instances that need names?"
  (or (atom x)
      (and (vl-modinst->instname (car x))
           (vl-modinstlist-all-named-p (cdr x))))
  ///
  (defthm vl-modinstlist-all-named-p-optimization
    (implies (vl-modinstlist-all-named-p x)
             (equal (vl-modinstlist-addinstnames x nf)
                    (mv (vl-modinstlist-fix x) (vl-namefactory-fix nf))))
    :hints(("Goal" :in-theory (enable vl-modinstlist-addinstnames
                                      vl-modinst-addinstnames)))))

(define vl-gateinstlist-all-named-p ((x vl-gateinstlist-p))
  :short "Are there any gate instances that need names?"
  (or (atom x)
      (and (vl-gateinst->name (car x))
           (vl-gateinstlist-all-named-p (cdr x))))
  ///
  (defthm vl-gateinstlist-all-named-p-optimizaiton
    (implies (vl-gateinstlist-all-named-p x)
             (equal (vl-gateinstlist-addinstnames x nf)
                    (mv (vl-gateinstlist-fix x) (vl-namefactory-fix nf))))
    :hints(("Goal" :in-theory (enable vl-gateinstlist-addinstnames
                                      vl-gateinst-addinstnames)))))

(define vl-module-addinstnames ((x vl-module-p))
  :returns (new-x vl-module-p)
  :short "Name any unnamed module and gate instances throughout a module."
  (mbe :logic
       (b* (((vl-module x) x)
            ((when (vl-module->hands-offp x))
             (vl-module-fix x))
            (nf                 (vl-starting-namefactory x))
            ((mv modinsts nf)   (vl-modinstlist-addinstnames x.modinsts nf))
            ((mv gateinsts ?nf) (vl-gateinstlist-addinstnames x.gateinsts nf)))
         (change-vl-module x
                           :modinsts modinsts
                           :gateinsts gateinsts))
       :exec
       (b* (((vl-module x) x)
            ((when (vl-module->hands-offp x))
             x)
            (mods-namedp  (vl-modinstlist-all-named-p x.modinsts))
            (gates-namedp (vl-gateinstlist-all-named-p x.gateinsts))
            ((when (and mods-namedp gates-namedp))
             ;; Don't need to recons *anything*
             x)
            (nf (vl-starting-namefactory x))
            ((mv modinsts nf)
             ;; Avoid reconsing modinsts when possible
             (if mods-namedp
                 (mv x.modinsts nf)
               (vl-modinstlist-addinstnames x.modinsts nf)))
            ((mv gateinsts nf)
             ;; Avoid reconsing gateinsts when possible
             (if gates-namedp
                 (mv x.gateinsts nf)
               (vl-gateinstlist-addinstnames x.gateinsts nf))))
         (vl-free-namefactory nf)
         (change-vl-module x
                           :modinsts modinsts
                           :gateinsts gateinsts)))
  ///
  (defthm vl-module->name-of-vl-module-addinstnames
    (equal (vl-module->name (vl-module-addinstnames x))
           (vl-module->name x))))

(defprojection vl-modulelist-addinstnames ((x vl-modulelist-p))
  :returns (new-x vl-modulelist-p)
  (vl-module-addinstnames x))

(define vl-design-addinstnames ((x vl-design-p))
  :returns (new-x vl-design-p)
  (b* (((vl-design x) x)
       (new-mods (vl-modulelist-addinstnames x.mods)))
    (change-vl-design x :mods new-mods)))

