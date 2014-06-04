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
(local (std::add-default-post-define-hook :fix))

(defxdoc clean-warnings
  :parents (transforms warnings)
  :short "A transform to clean up all the warnings in a design."

  :long "<p>See @(see vl-clean-warnings), which sorts warnings and eliminates
duplicates.  This transform just extends @('vl-clean-warnings') throughout a
design.</p>")

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
                      :packages   (vl-packagelist-clean-warnings x.packages)
                      :configs    (vl-configlist-clean-warnings x.configs))))

