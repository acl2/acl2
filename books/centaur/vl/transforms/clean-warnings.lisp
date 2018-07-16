; VL Verilog Toolkit
; Copyright (C) 2008-2014 Centaur Technology
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

(in-package "VL")
(include-book "../parsetree")
(local (include-book "../util/arithmetic"))
(local (std::add-default-post-define-hook :fix))

(defxdoc clean-warnings
  :parents (transforms warnings)
  :short "A transform to clean up all the warnings in a design."

  :long "<p>The top-level function here is @(see vl-design-clean-warnings).
This function simply applies @('vl-clean-warnings'), which sorts a list of
warnings and eliminates duplicate warnings, to all of the warnings lists
throughout the design.</p>")

(local (xdoc::set-default-parents clean-warnings))

(defmacro def-vl-clean-warnings (name)
  (b* ((mksym-package-symbol (pkg-witness "VL"))
       (fn         (mksym name '-clean-warnings))
       (foo-p      (mksym name '-p))
       (change-foo (mksym 'change- name)))
    `(define ,fn ((x ,foo-p))
       :short ,(cat "Clean warnings in a @(see " (symbol-name foo-p) ").")
       :returns (new-x ,foo-p)
       (mbe :logic
            (b* (((,name x) x))
              (,change-foo x :warnings (vl-clean-warnings x.warnings)))
            :exec
            (b* (((,name x) x)
                 ((unless x.warnings)
                  ;; Dumb optimization: avoid reconsing when there are no warnings.
                  x))
              (,change-foo x :warnings (vl-clean-warnings x.warnings)))))))

(def-vl-clean-warnings vl-module)
(defprojection vl-modulelist-clean-warnings ((x vl-modulelist-p))
  :returns (new-x vl-modulelist-p)
  (vl-module-clean-warnings x))

(def-vl-clean-warnings vl-udp)
(defprojection vl-udplist-clean-warnings ((x vl-udplist-p))
  :returns (new-x vl-udplist-p)
  (vl-udp-clean-warnings x))

(def-vl-clean-warnings vl-program)
(defprojection vl-programlist-clean-warnings ((x vl-programlist-p))
  :returns (new-x vl-programlist-p)
  (vl-program-clean-warnings x))

(def-vl-clean-warnings vl-class)
(defprojection vl-classlist-clean-warnings ((x vl-classlist-p))
  :returns (new-x vl-classlist-p)
  (vl-class-clean-warnings x))

(def-vl-clean-warnings vl-package)
(defprojection vl-packagelist-clean-warnings ((x vl-packagelist-p))
  :returns (new-x vl-packagelist-p)
  (vl-package-clean-warnings x))

(def-vl-clean-warnings vl-interface)
(defprojection vl-interfacelist-clean-warnings ((x vl-interfacelist-p))
  :returns (new-x vl-interfacelist-p)
  (vl-interface-clean-warnings x))

(def-vl-clean-warnings vl-config)
(defprojection vl-configlist-clean-warnings ((x vl-configlist-p))
  :returns (new-x vl-configlist-p)
  (vl-config-clean-warnings x))


(define vl-design-clean-warnings
  :short "Clean warnings everywhere throughout a design."
  ((x vl-design-p))
  :returns (new-x vl-design-p)
  :long "<p>We apply @(see vl-clean-warnings) everywhere throughout the design.
It may occasionally be useful to run this transformation to clean up any
redundant warnings.</p>"
  (b* (((vl-design x) x))
    (change-vl-design x
                      :mods       (vl-modulelist-clean-warnings x.mods)
                      :udps       (vl-udplist-clean-warnings x.udps)
                      :interfaces (vl-interfacelist-clean-warnings x.interfaces)
                      :programs   (vl-programlist-clean-warnings x.programs)
                      :classes    (vl-classlist-clean-warnings x.classes)
                      :packages   (vl-packagelist-clean-warnings x.packages)
                      :configs    (vl-configlist-clean-warnings x.configs))))

