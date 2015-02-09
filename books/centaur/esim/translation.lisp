; ESIM Symbolic Hardware Simulator
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
(include-book "centaur/vl2014/parsetree" :dir :system)
(include-book "centaur/vl2014/mlib/find" :dir :system)
(include-book "centaur/vl2014/loader/filemap" :dir :system)
(include-book "centaur/vl2014/loader/preprocessor/defines" :dir :system)
(local (include-book "centaur/vl2014/util/arithmetic" :dir :system))
(local (include-book "centaur/vl2014/util/osets" :dir :system))


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
                   etc."))

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

  (if (vl-find-module modname (vl-design->mods (vl-translation->good x)))
      t
    nil))

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
