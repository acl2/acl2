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
(include-book "cutil/defaggregate" :dir :system)

(defaggregate vl-simpconfig
  :parents (vl-simplify)
  :short "Options for how to simplify Verilog modules."
  :tag :vl-simpconfig

  ((compress-p   booleanp
                 "Hons the modules at various points.  This takes some time,
                  but can produce smaller translation files.")

   (problem-mods string-listp
                 "Names of modules that should thrown out, perhaps because they
                  cause some kind of problems."
                 :default nil)

   (clean-params-p booleanp
                   "Should we clean parameters with the @(see clean-params) transform
                    before unparameterizing?"
                   :rule-classes :type-prescription
                   :default t)

   (unroll-limit natp
                 "Maximum number of iterations to unroll for loops, etc., when
                  rewriting statements.  This is just a safety valve."
                 :rule-classes :type-prescription
                 :default 1000)

   (safe-mode-p  booleanp
                 "Do extra safety checking.  Probably not actually used for
                  anything."
                 :rule-classes :type-prescription
                 :default t)

   ;; Linting options

   (multidrive-detect-p booleanp
                        "Should we try to detect and report about wires that have
                         multiple drivers?"
                        :rule-classes :type-prescription
                        :default t)

   (use-set-p booleanp
              "Should we construct a @(see use-set) report?"
              :rule-classes :type-prescription
              :default t)

   (use-set-omit-wires string-listp
                       "Wire names to skip when doing @(see use-set) analysis."
                       :default nil)
   ))

(defconst *vl-default-simpconfig*
  (make-vl-simpconfig))

