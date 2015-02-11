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
(include-book "mlib/range-tools")
(include-book "util/defwellformed")
(local (include-book "util/arithmetic"))



(defwellformed vl-portdecl-range-resolved-p (x)
  :guard (vl-portdecl-p x)
  :body (let ((range (vl-portdecl->range x)))
          (@wf-assert (vl-maybe-range-resolved-p range)
                      :vl-range-unresolved
                      "~l0: failed to resolve range of portdecl ~s1: current range is ~x2."
                      (list (vl-portdecl->loc x)
                            (vl-portdecl->name x)
                            range))))

(defthm vl-maybe-range-resolved-p-of-vl-portdecl->range
  (implies (vl-portdecl-range-resolved-p x)
           (vl-maybe-range-resolved-p (vl-portdecl->range x)))
  :hints(("Goal" :in-theory (enable vl-portdecl-range-resolved-p))))

(defwellformed-list vl-portdecllist-ranges-resolved-p (x)
  :element vl-portdecl-range-resolved-p
  :guard (vl-portdecllist-p x))



(defwellformed vl-netdecl-range-resolved-p (x)
  :guard (vl-netdecl-p x)
  :body (let ((range (vl-netdecl->range x)))
          (@wf-assert (vl-maybe-range-resolved-p range)
                      :vl-range-unresolved
                      "~l0: failed to resolve range of wire ~s1: current range is ~x2."
                      (list (vl-netdecl->loc x)
                            (vl-netdecl->name x)
                            range))))

(deffixequiv vl-netdecl-range-resolved-p :args ((x vl-netdecl-p))
  :hints(("Goal" :in-theory (enable vl-netdecl-range-resolved-p))))

(defthm vl-maybe-range-resolved-p-of-vl-netdecl->range
  (implies (vl-netdecl-range-resolved-p x)
           (vl-maybe-range-resolved-p (vl-netdecl->range x)))
  :hints(("Goal" :in-theory (enable vl-netdecl-range-resolved-p))))

(defwellformed-list vl-netdecllist-ranges-resolved-p (x)
  :element vl-netdecl-range-resolved-p
  :guard (vl-netdecllist-p x))

(defthm vl-range-resolved-p-of-vl-netdecl-range-of-vl-find-netdecl
  (implies (force (vl-netdecllist-ranges-resolved-p x))
           (vl-netdecl-range-resolved-p (vl-find-netdecl name x)))
  :hints(("Goal"
          :in-theory (enable vl-find-netdecl))))



(defwellformed vl-vardecl-range-resolved-p (x)
  :guard (vl-vardecl-p x)
  :body (@wf-assert (or (not (vl-simplereg-p x))
                        (vl-maybe-range-resolved-p (vl-simplereg->range x)))
                    :vl-range-unresolved
                    "~l0: failed to resolve range of variable ~s1: current range is ~x2."
                    (list (vl-vardecl->loc x)
                          (vl-vardecl->name x)
                          (vl-simplereg->range x))))

(deffixequiv vl-vardecl-range-resolved-p :args ((x vl-vardecl-p))
  :hints(("Goal" :in-theory (enable vl-vardecl-range-resolved-p))))

;; (defthm vl-maybe-range-resolved-p-of-vl-vardecl->range
;;   (implies (vl-vardecl-range-resolved-p x)
;;            (vl-maybe-range-resolved-p (vl-vardecl->range x)))
;;   :hints(("Goal" :in-theory (enable vl-vardecl-range-resolved-p))))

(defwellformed-list vl-vardecllist-ranges-resolved-p (x)
  :element vl-vardecl-range-resolved-p
  :guard (vl-vardecllist-p x))

;; (defthm vl-range-resolved-p-of-vl-vardecl-range-of-vl-find-vardecl
;;   (implies (force (vl-vardecllist-ranges-resolved-p x))
;;            (vl-vardecl-range-resolved-p (vl-find-vardecl name x)))
;;   :hints(("Goal"
;;           :in-theory (enable vl-find-vardecl))))



(defwellformed vl-modinst-range-resolved-p (x)
  :guard (vl-modinst-p x)
  :body (let ((range (vl-modinst->range x)))
          (@wf-assert (vl-maybe-range-resolved-p range)
                      :vl-range-unresolved
                      "~l0: failed to resolve range of modinst ~s1: current range is ~x2."
                      (list (vl-modinst->loc x)
                            (or (vl-modinst->instname x)
                                (cat "<unnamed instance of module "
                                     (vl-modinst->modname x)
                                     ">"))
                            range))))

(defthm vl-maybe-range-resolved-p-of-vl-modinst->range
  (implies (vl-modinst-range-resolved-p x)
           (vl-maybe-range-resolved-p (vl-modinst->range x)))
  :hints(("Goal" :in-theory (enable vl-modinst-range-resolved-p))))

(defwellformed-list vl-modinstlist-ranges-resolved-p (x)
  :element vl-modinst-range-resolved-p
  :guard (vl-modinstlist-p x))



(defwellformed vl-gateinst-range-resolved-p (x)
  :guard (vl-gateinst-p x)
  :body (let ((range (vl-gateinst->range x)))
          (@wf-assert (vl-maybe-range-resolved-p range)
                      :vl-range-unresolved
                      "~l0: failed to resolve range of gateinst ~s1: current range is ~x2."
                      (list (vl-gateinst->loc x)
                            (or (vl-gateinst->name x)
                                (cat "<unnamed gate of type "
                                     (symbol-name (vl-gateinst->type x))
                                     ">"))
                            range))))

(defthm vl-maybe-range-resolved-p-of-vl-gateinst->range
  (implies (vl-gateinst-range-resolved-p x)
           (vl-maybe-range-resolved-p (vl-gateinst->range x)))
  :hints(("Goal" :in-theory (enable vl-gateinst-range-resolved-p))))

(defwellformed-list vl-gateinstlist-ranges-resolved-p (x)
  :element vl-gateinst-range-resolved-p
  :guard (vl-gateinstlist-p x))




(defwellformed vl-module-ranges-resolved-p (x)
  :guard (vl-module-p x)
  :body
  (@wf-progn
   (@wf-call vl-portdecllist-ranges-resolved-p (vl-module->portdecls x))
   (@wf-call vl-netdecllist-ranges-resolved-p (vl-module->netdecls x))
   (@wf-call vl-vardecllist-ranges-resolved-p (vl-module->vardecls x))
   (@wf-call vl-modinstlist-ranges-resolved-p (vl-module->modinsts x))
   (@wf-call vl-gateinstlist-ranges-resolved-p (vl-module->gateinsts x))))

(defthm vl-portdecllist-ranges-resolved-p-when-vl-module-ranges-resolved-p
  (implies (force (vl-module-ranges-resolved-p x))
           (vl-portdecllist-ranges-resolved-p (vl-module->portdecls x)))
  :hints(("Goal" :in-theory (enable vl-module-ranges-resolved-p))))

(defthm vl-netdecllist-ranges-resolved-p-when-vl-module-ranges-resolved-p
  (implies (force (vl-module-ranges-resolved-p x))
           (vl-netdecllist-ranges-resolved-p (vl-module->netdecls x)))
  :hints(("Goal" :in-theory (enable vl-module-ranges-resolved-p))))

(defthm vl-vardecllist-ranges-resolved-p-when-vl-module-ranges-resolved-p
  (implies (force (vl-module-ranges-resolved-p x))
           (vl-vardecllist-ranges-resolved-p (vl-module->vardecls x)))
  :hints(("Goal" :in-theory (enable vl-module-ranges-resolved-p))))

(defthm vl-modinstlist-ranges-resolved-p-when-vl-module-ranges-resolved-p
  (implies (force (vl-module-ranges-resolved-p x))
           (vl-modinstlist-ranges-resolved-p (vl-module->modinsts x)))
  :hints(("Goal" :in-theory (enable vl-module-ranges-resolved-p))))

(defthm vl-gateinstlist-ranges-resolved-p-when-vl-module-ranges-resolved-p
  (implies (force (vl-module-ranges-resolved-p x))
           (vl-gateinstlist-ranges-resolved-p (vl-module->gateinsts x)))
  :hints(("Goal" :in-theory (enable vl-module-ranges-resolved-p))))



(defwellformed-list vl-modulelist-ranges-resolved-p (x)
  :element vl-module-ranges-resolved-p
  :guard (vl-modulelist-p x))



