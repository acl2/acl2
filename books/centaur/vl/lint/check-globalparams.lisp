; VL Verilog Toolkit
; Copyright (C) 2016 Centaur Technology
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
; Original author: Sol Swords <sswords@centtech.com>

(in-package "VL")

(include-book "../mlib/scopestack")
(include-book "centaur/fty/visitor" :dir :system)
(local (include-book "../util/arithmetic"))
(local (std::add-default-post-define-hook :fix))

(fty::defalist vl-reservedtable :key-type stringp :val-type stringp)


(define vl-paramdecl-check-globalparams ((x vl-paramdecl-p)
                                         (namespace stringp)
                                         (warnings vl-warninglist-p "Warnings accumulator")
                                         (reserved vl-reservedtable-p))
  :returns (warnings vl-warninglist-p)
  (b* (((vl-paramdecl x))
       (reserved (vl-reservedtable-fix reserved))
       (namespace (string-fix namespace))
       (lookup (hons-get x.name reserved))
       ((unless lookup) (ok))
       ((when (equal namespace (cdr lookup))) (ok)))
    (warn :type :vl-parameter-nameclash
          :msg "Parameter ~s0 is declared both in global-designated namespace ~
                ~s1 and elsewhere, namely inside ~s2 at ~a3."
          :args (list x.name (cdr lookup) (string-fix namespace) x.loc))))
       

(fty::defvisitor-template check-globalparams ((x :object)
                                              (namespace stringp)
                                              (warnings vl-warninglist-p "Warnings accumulator")
                                              (reserved vl-reservedtable-p))

  :returns (warnings (:acc warnings :fix (vl-warninglist-fix warnings))
                     vl-warninglist-p)
  :type-fns ((vl-paramdecl vl-paramdecl-check-globalparams)
             (vl-modulelist :skip)
             (vl-interfacelist :skip)
             (vl-packagelist :skip))
  :renames ((vl-module vl-module-check-globalparams-aux)
            (vl-interface vl-interface-check-globalparams-aux)
            (vl-package vl-package-check-globalparams-aux)
            (vl-design vl-design-check-globalparams-aux))
  :fnname-template <type>-check-globalparams)


(set-bogus-measure-ok t)

(fty::defvisitors vl-module-check-globalparams
  :types (vl-module vl-interface vl-package)
  :template check-globalparams)

(fty::defvisitors vl-design-check-globalparams
  :types (vl-design)
  :template check-globalparams)

(define vl-module-check-globalparams ((x vl-module-p)
                                      (reserved vl-reservedtable-p))
  :returns (new-x vl-module-p)
  (b* (((vl-module x))
       (warnings (vl-module-check-globalparams-aux x x.name nil reserved)))
    (change-vl-module x :warnings (append-without-guard warnings x.warnings))))

(define vl-interface-check-globalparams ((x vl-interface-p)
                                      (reserved vl-reservedtable-p))
  :returns (new-x vl-interface-p)
  (b* (((vl-interface x))
       (warnings (vl-interface-check-globalparams-aux x x.name nil reserved)))
    (change-vl-interface x :warnings (append-without-guard warnings x.warnings))))

(define vl-package-check-globalparams ((x vl-package-p)
                                      (reserved vl-reservedtable-p))
  :returns (new-x vl-package-p)
  (b* (((vl-package x))
       (warnings (vl-package-check-globalparams-aux x x.name nil reserved)))
    (change-vl-package x :warnings (append-without-guard warnings x.warnings))))

(defprojection vl-modulelist-check-globalparams ((x vl-modulelist-p)
                                                 (reserved vl-reservedtable-p))
  :returns (new-x vl-modulelist-p)
  (vl-module-check-globalparams x reserved))

(defprojection vl-interfacelist-check-globalparams ((x vl-interfacelist-p)
                                                 (reserved vl-reservedtable-p))
  :returns (new-x vl-interfacelist-p)
  (vl-interface-check-globalparams x reserved))

(defprojection vl-packagelist-check-globalparams ((x vl-packagelist-p)
                                                 (reserved vl-reservedtable-p))
  :returns (new-x vl-packagelist-p)
  (vl-package-check-globalparams x reserved))

(define vl-paramdecllist-collect-reserved-globalparams ((x vl-paramdecllist-p)
                                                        (namespace stringp)
                                                        (reserved vl-reservedtable-p))
  :returns (reserved vl-reservedtable-p)
  (b* (((when (atom x)) (vl-reservedtable-fix reserved))
       ((vl-paramdecl x1) (car x))
       (reserved (hons-acons x1.name (string-fix namespace) (vl-reservedtable-fix reserved))))
    (vl-paramdecllist-collect-reserved-globalparams (cdr x) namespace reserved)))

(define vl-check-globalparams-collect-reserved ((specials string-listp)
                                                (ss vl-scopestack-p)
                                                (reserved vl-reservedtable-p))
  :returns (reserved vl-reservedtable-p)
  (b* (((when (atom specials)) (vl-reservedtable-fix reserved))
       (pkg (vl-scopestack-find-package (car specials) ss))
       ((unless pkg)
        (er hard? 'vl-check-globalparams "~s0 is listed as a global-designated namespace, but no package of that name was found." (car specials)))
       (reserved (vl-paramdecllist-collect-reserved-globalparams (vl-package->paramdecls pkg)
                                                                 (car specials) reserved)))
    (vl-check-globalparams-collect-reserved (cdr specials) ss reserved)))

(define vl-design-check-globalparams ((x vl-design-p)
                                      (specials string-listp "packages whose parameters should not be defined elsewhere"))
  :returns (new-x vl-design-p)
  (b* (((vl-design x))
       (ss (vl-scopestack-init x))
       (reserved (vl-check-globalparams-collect-reserved specials ss nil))
       ((when (atom reserved))
        ;; no global packages specified, presumably -- skip checks
        (vl-design-fix x))
       (modules (vl-modulelist-check-globalparams x.mods reserved))
       (interfaces (vl-interfacelist-check-globalparams x.interfaces reserved))
       (packages (vl-packagelist-check-globalparams x.packages reserved))
       (warnings (vl-design-check-globalparams-aux x "<global>" nil reserved)))
    (change-vl-design x :mods modules
                      :interfaces interfaces
                      :packages packages
                      :warnings warnings)))


       
  


       
