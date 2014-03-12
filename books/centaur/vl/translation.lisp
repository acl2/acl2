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
(include-book "loader/preprocessor/defines")
(include-book "checkers/use-set-report")
(local (include-book "util/arithmetic"))
(local (include-book "util/osets"))


(defaggregate vl-translation
  :parents (defmodules)
  :short "The result of translating a Verilog or SystemVerilog design."

  ((good          vl-design-p
                  "Fully translated modules, etc., for whatever subset of the
                   overall design we were able to successfully translate.
                   This is the \"good subset\" of the design.")

   (bad           vl-design-p
                  "Partially translated modules, etc., that, for whatever
                   reason, we were unable to successfully translate.  The
                   modules here will typically have fatal warnings.  This This
                   is the \"bad subset\" or at least the \"unsupported subset\"
                   of the design.")

   (orig          vl-design-p
                  "The raw, unsimplified design that we obtained immediately
                   after parsing.  This can be useful for pretty-printing and
                   understanding modules.")

   (filemap       vl-filemap-p
                  "The actual Verilog source code that was read. Occasionally
                   this is useful for understanding warnings that refer to
                   particular file locations.")

   (defines       vl-defines-p
                  "Records all of the @('`define') directives that were
                   encountered during parsing, and their final values. This is
                   sometimes useful for extracting definitions like opcodes,
                   etc.")

   (loadwarnings  vl-warninglist-p
                  "A list of \"floating\" warnings that were encountered during
                   the load process.  This usually does not have anything
                   interesting in it, because most warnings get associated with
                   design elements in @('good') or @('fail') instead.  It may,
                   however, contain miscellaneous warnings from <i>between</i>
                   design elements which, therefore, can't be associated with
                   particular modules.")

   (useset-report vl-useset-report-p
                  "A report that contains the results of running the @(see
                   use-set) analysis; this may help you identify wires that are
                   undriven or unused."))

  :tag :vl-translation

  :long "<p>Translation objects are most commonly produced by the @(see
defmodules) command.</p>")


(define vl-translation-has-module ((modname stringp)
                                   (x       vl-translation-p))
  :parents (vl-translation-p)
  :short "Check whether a module was successfully translated."

  :long "<p>The @('modname') should be the desired module's name as a string,
e.g., @('\"fadd\"').  If the module's name includes parameters, you will need
to say which version you want, e.g., @('\"adder$width=4\"').</p>

<p>We return @('t') only when the module was successfully translated with no
\"fatal\" warnings.  (See @(see vl-translation-p); failed modules are found in
the translation's @('failmods') field, whereas successful modules are kept in
the @('mods') field.)</p>"

  (vl-has-module modname
                 (vl-design->mods
                  (vl-translation->good x))))

(define vl-translation-get-esim ((modname stringp)
                                 (x vl-translation-p))
  :returns (e-mod)
  :guard (vl-translation-has-module modname x)
  :parents (vl-translation-p)
  :short "Get an E Module for a successfully translated module."
  :prepwork ((local (in-theory (enable vl-translation-has-module))))

  (b* ((mod  (vl-find-module modname
                             (vl-design->mods
                              (vl-translation->good x))))
       (esim (vl-module->esim mod))
       ((unless esim)
        (raise "Module ~x0 has no esim?" modname)))
    esim))
