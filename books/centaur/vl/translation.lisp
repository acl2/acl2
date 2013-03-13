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
(include-book "parsetree")
(include-book "loader/filemap")
(include-book "loader/defines")
(include-book "checkers/use-set-report")
(include-book "transforms/xf-designregs") ;; ugh
(local (include-book "util/arithmetic"))
(local (include-book "util/osets"))


(defaggregate vl-translation
  (mods
   failmods
   filemap
   defines
   loadwarnings
   useset-report
   ;; dregs  awful, trying to deprecate this
   )
  :tag :vl-translation
  :require ((vl-modulelist-p-of-vl-translation->mods
             (vl-modulelist-p mods))
            (vl-modulelist-p-of-vl-translation->failmods
             (vl-modulelist-p failmods))
            (vl-filemap-p-of-vl-translation->filemap
             (vl-filemap-p filemap))
            (vl-defines-p-of-vl-translation->defines
             (vl-defines-p defines))
            (vl-warninglist-p-of-vl-translation->loadwarnings
             (vl-warninglist-p loadwarnings))
            (vl-useset-report-p-of-vl-translation->useset-report
             (vl-useset-report-p useset-report))
            ;; (vl-dregalist-p-of-vl-translation->dregs
            ;;  (vl-dregalist-p dregs))
            )
  :parents (defmodules)
  :short "The result of translating Verilog modules."

  :long "<p>The @(see defmodules) command produces a @('vl-translation-p')
object as its result.</p>

<p>See @(see translation-interface) for high-level functions for extracting E
modules.</p>

<p>Each @('vl-translation-p') object bundles together:</p>

<ul>

<li>@('mods'), a list of fully simplified, successfully translated modules,
represented as @(see vl-module-p)s,</li>

<li>@('failmods'), a list of partially simplified modules which could not be
fully simplified, represented as @(see vl-module-p)s,</li>

<li>@('filemap'), a @(see vl-filemap-p) structure that records the actual
Verilog source code that was read,</li>

<li>@('defines'), a @(see vl-defines-p) structure that records all of the
@('`define') directives encountered</li>

<li>@('loadwarnings'), a @(see vl-warninglist-p) that records any warnings
encountered by the @(see loader).  Note that this list does not include any
warnings produced by the simplifier: such warning are found in the modules of
@('mods') and @('failmods').</li>

<li>@('useset-report'), a @(see vl-useset-report-p) that records the results of
the @(see use-set) tool.</li>

</ul>")

;; <li>@('dregs'), the @(see design-regs) alist for this translation.</li>

(defxdoc translation-interface
  :parents (defmodules)
  :short "Functions for interacting with @(see vl-translation-p) objects."

  :long "<p>The @(see defmodules) command produces a @(see vl-translation-p)
object as its result.  The following functions allow you to conveniently access
parts of this translation.</p>")


(defsection vl-translation-has-module
  :parents (translation-interface)
  :short "Check whether a module was successfully translated."

  :long "<p><b>Signature:</b> @(call vl-translation-has-module) returns a
@('t') or @('nil').</p>

<p>The @('modname') should be the desired module's name as a string, e.g.,
@('\"fadd\"').  If the module's name includes parameters, you will need to say
which version you want, e.g., @('\"adder$width=4\"').</p>

<p>We return @('t') only when the module was successfully translated with no
\"fatal\" warnings.  (See @(see vl-translation-p); failed modules are found in
the translation's @('failmods') field, whereas successful modules are kept in
the @('mods') field.)</p>"

  (defund vl-translation-has-module (modname x)
    (declare (xargs :guard (and (stringp modname)
                                (vl-translation-p x))))
    (if (vl-find-module modname (vl-translation->mods x))
        t
      nil)))


