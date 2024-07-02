; SV - Symbolic Vector Hardware Analysis Framework
; Copyright (C) 2024 Intel Corporation
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
; Original author: Sol Swords <sol.swords@intel.com>

(in-package "SV")

(include-book "svmods")
(local (std::add-default-post-define-hook :fix))

(define modinstlist-assoc ((instname name-p)
                           (x modinstlist-p))
  :returns (inst (iff (modinst-p inst) inst))
  (b* (((when (atom x)) nil)
       ((modinst x1) (modinst-fix (car x)))
       ((when (equal (name-fix instname) x1.instname)) x1))
    (modinstlist-assoc instname (cdr x))))

(define modalist-find-hier-instance ((modname modname-p)
                                     (inst-hier namelist-p)
                                     (x modalist-p))
  :measure (len inst-hier)
  :returns (inst (iff (modinst-p inst) inst))
  (b* ((mod (cdr (hons-get (modname-fix modname) (modalist-fix x))))
       ((unless mod) nil)
       ((unless (consp inst-hier)) nil)
       ((module mod))
       (inst (modinstlist-assoc (car inst-hier) mod.insts))
       ((when (atom (cdr inst-hier))) inst)
       ((unless inst) nil)
       ((modinst inst)))
    (modalist-find-hier-instance inst.modname (cdr inst-hier) x)))

(define design-find-modname-for-inst ((inst-hier namelist-p)
                                      (x design-p))
  :returns (modname (iff (modname-p modname) modname))
  (b* (((design x))
       (inst (with-fast-alist x.modalist
               (modalist-find-hier-instance x.top inst-hier x.modalist)))
       ((unless inst) nil))
    (modinst->modname inst)))

