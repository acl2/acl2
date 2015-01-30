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
(include-book "util/defs")
(include-book "centaur/fty/deftypes" :dir :system)
(include-book "centaur/fty/basetypes" :dir :system)

(defprod vl-simpconfig
  :parents (vl-simplify)
  :short "Options for how to simplify Verilog modules."
  :tag :vl-simpconfig

  ((compress-p   booleanp
                 "Hons the modules at various points.  This takes some time,
                  but can produce smaller translation files."
                 :rule-classes :type-prescription)

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
                 :default 1000)))

(defconst *vl-default-simpconfig*
  (make-vl-simpconfig))

