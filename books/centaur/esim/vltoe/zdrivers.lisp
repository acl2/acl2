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
(include-book "wirealist")
(include-book "centaur/esim/esim-sexpr-support" :dir :system)
(include-book "centaur/esim/esim-primitives" :dir :system)
(local (include-book "esim-lemmas"))
(local (include-book "centaur/vl2014/util/arithmetic" :dir :system))



(defsection adding-z-drivers
  :parents (e-conversion)
  :short "How we ensure every wire is driven."

  :long "<p>The @('good-esim-modulep') well-formedness check requires that
every wire of a module is driven by some occurrence (or is an input).  But in
Verilog there is no such requirement, e.g., one can legally write a module like
this:</p>

@({
module does_nothing(out, a, b);
  output out;
  input a;
  input b;
  wire internal;
endmodule
})

<p>Where there aren't any drivers on @('out') or @('internal').</p>

<p>To correct for this, in our @(see e-conversion) we look for any output bits
and also any internal wires that are used as inputs to a submodule but are
never driven by the preliminary occurrences produced by @(see
modinsts-to-eoccs).  For any such bit, we add an explicit @(see acl2::*esim-z*)
module to drive it.</p>")


(defsection vl-make-z-occ
  :parents (adding-z-drivers)
  :short "Generate an instance of @(see acl2::*esim-z*) to drive an
otherwise-undriven output bit."

  (defund vl-make-z-occ (name out)
    (declare (xargs :guard (and (vl-emodwire-p out)
                                name)))
    ;; Note: the I/O here must agree with *esim-z*.
    (list :u  name
          :op acl2::*esim-z*
          :i  nil
          :o  (list (list out))))

  (local (in-theory (enable vl-make-z-occ)))

  (defthm good-esim-occp-of-vl-make-z-occ
    (implies (and (force (vl-emodwire-p out))
                  (force name))
             (good-esim-occp (vl-make-z-occ name out)))
    :hints(("Goal" :in-theory (enable good-esim-occp)))))


(defsection vl-make-z-occs
  :parents (adding-z-drivers)
  :short "Generate instances of @(see acl2::*esim-z*) to drive undriven output
bits."

  :long "<p><b>Signature:</b> @(call vl-make-z-occs) returns a list of
occurrences.</p>

<ul>

<li>@('idx') is a name index used for fresh name generation.  We expect that it
is initially set to the highest index of any emodwire in the module whose
basename is @('vl_zdrive').  We increment it whenever we need to create a new,
fresh occurrence name.</li>

<li>@('outs') are an @(see vl-emodwirelist-p) that should include all of the
output bits that weren't driven by the preliminary occurrences.</li>

</ul>"

  (defund vl-make-z-occs (idx outs)
    (declare (xargs :guard (and (natp idx)
                                (vl-emodwirelist-p outs))
                    :verify-guards nil))
    (b* (((when (atom outs))
          nil)
         (idx (+ 1 idx))
         (fresh (make-vl-emodwire :basename "vl_zdrive" :index idx)))
      (cons (vl-make-z-occ fresh (car outs))
            (vl-make-z-occs idx (cdr outs)))))

  (local (in-theory (enable vl-make-z-occs)))

  (local (defthm l0
           (implies (maybe-natp idx)
                    (iff (vl-emodwire "vl_zdrive" idx)
                         t))
           :hints(("Goal"
                   :in-theory (disable vl-emodwire-p-of-vl-emodwire)
                   :use ((:instance vl-emodwire-p-of-vl-emodwire
                                    (basename "vl_zdrive")
                                    (index idx)))))))

  (verify-guards vl-make-z-occs)

  (defthm good-esim-occsp-of-vl-make-z-occs
    (implies (and (force (natp idx))
                  (force (vl-emodwirelist-p outs)))
             (good-esim-occsp (vl-make-z-occs idx outs)))
    :hints(("Goal" :in-theory (enable good-esim-occsp)))))



(defsection vl-add-zdrivers
  :parents (adding-z-drivers)
  :short "Top-level function for adding drivers for undriven outputs."

  :long "<p><b>Signature:</b> @(call vl-add-zdrivers) returns @('occs'').</p>

<p>@('occs') should be the initial list of occurrences that we generate from
the module instances; see for instance @(see vl-modinst-to-eocc).</p>

<p>@('flat-outs') should be the already-flattened list of the module's output
bits, i.e., @('(pat-flatten (gpl :o mod))').</p>

<p>@('flat-ins') should be the already-flattened list of the module's input
bits, i.e., @('(pat-flatten (gpl :i mod))').</p>

<p>@('all-names') must be a @(see vl-emodwirelist-p)s that captures the
module's namespace.  We expect it to include at least:</p>

<ul>
<li>All signals in :i and :o for the module</li>
<li>All signals used in :i and :o patterns in occs</li>
<li>The names of all occs (i.e., the :u from each occ)</li>
</ul>

<p>However, as a special exception, @('all-names') may exclude names that we
know cannot have the basename @('vl_zdrive').  This includes, for instance, all
of the wires that are added during @(see vl-add-res-modules), and the special
wires that are added to drive T and F in @(see vl-module-make-esim).</p>"

  (defund vl-add-zdrivers (all-names flat-ins flat-outs occs)
    (declare (xargs :guard (and (vl-emodwirelist-p all-names)
                                (vl-emodwirelist-p flat-ins)
                                (vl-emodwirelist-p flat-outs)
                                (vl-emodwirelist-p (collect-signal-list :i occs))
                                (vl-emodwirelist-p (collect-signal-list :o occs)))))

    (b* ((driven-signals
          ;; All signals that are already being driven, either by an occurrence
          ;; or because they are inputs and hence are being driven by the
          ;; superior module.
          (union (mergesort flat-ins)
                 (mergesort (collect-signal-list :o occs))))

         (consumed-signals
          ;; All signals that "need to be" driven, either because they are
          ;; feeding an occurrence or because they are outputs that need to
          ;; feed something in the superior module.
          (union (mergesort flat-outs)
                 (mergesort (collect-signal-list :i occs))))

         (signals-that-need-zdrivers
          (difference (difference consumed-signals driven-signals)
                      ;; We also don't want to add drivers for F and T; fixing
                      ;; them up is the responsibility of vl-module-make-esim.
                      (mergesort '(acl2::f acl2::t))))

         ((unless signals-that-need-zdrivers)
          ;; Optimization.  Most of the time nothing needs to be fixed up so we
          ;; don't have to do anything.  We can avoid computing the highest
          ;; vl_zdrive wire, which can save a lot of string processing.
          occs)

         (idx (vl-emodwirelist-highest "vl_zdrive" all-names))
         (new-occs (vl-make-z-occs idx signals-that-need-zdrivers)))

      (append new-occs occs)))

  (local (in-theory (enable vl-add-zdrivers)))

  (defthm good-esim-occsp-of-vl-add-zdrivers
    (implies (and (force (vl-emodwirelist-p all-names))
                  (force (vl-emodwirelist-p flat-ins))
                  (force (vl-emodwirelist-p flat-outs))
                  (force (vl-emodwirelist-p (collect-signal-list :i occs)))
                  (force (vl-emodwirelist-p (collect-signal-list :o occs)))
                  (force (good-esim-occsp occs)))
             (good-esim-occsp (vl-add-zdrivers all-names flat-ins flat-outs occs)))
    :hints(("Goal" :in-theory (enable good-esim-occsp)))))

