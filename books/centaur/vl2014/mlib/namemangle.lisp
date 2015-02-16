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


(define vl-namemangle-vardecls
  :short "Safely try to give these vardecls new names of the form
@('prefix_{current-name}.')"

  ((prefix   stringp)
   (vardecls vl-vardecllist-p)
   (nf       vl-namefactory-p))
  :returns (mv (new-vars vl-vardecllist-p)
               (new-nf   vl-namefactory-p))

  :long "<p>You'll generally want to do something like:</p>

@({
   (pairlis$ (vl-vardecllist->names old-vardecls)
             (vl-vardecllist->names renamed-vardecls))
})

<p>And then use this as a substitution.</p>"

  (b* (((when (atom vardecls))
        (mv nil (vl-namefactory-fix nf)))
       (name1          (vl-vardecl->name (car vardecls)))
       (want1          (str::cat prefix "_" name1))
       ((mv fresh1 nf) (vl-namefactory-plain-name want1 nf))
       (inst1          (change-vl-vardecl (car vardecls) :name fresh1))
       ((mv insts2 nf) (vl-namemangle-vardecls prefix (cdr vardecls) nf)))
    (mv (cons inst1 insts2) nf))
  ///
  (defmvtypes vl-namemangle-vardecls (true-listp nil))

  (defthm len-of-vl-namemangle-vardecls
    (b* (((mv new-vardecls ?new-nf)
          (vl-namemangle-vardecls loc vardecls nf)))
      (equal (len new-vardecls)
             (len vardecls)))))

