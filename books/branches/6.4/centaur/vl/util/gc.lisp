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
(include-book "std/util/define" :dir :system)
(include-book "centaur/misc/memory-mgmt" :dir :system)
(include-book "tools/include-raw" :dir :system)
;; (depends-on "gc-raw.lsp")

(define vl-gc ()
  :parents (utilities)
  :short "Maybe trigger a garbage collection."

  :long "<p>In the logic @('vl-gc') just returns @('nil').  On CCL, its raw
Lisp definition, it may (or may not) trigger a garbage collection.  On other
Lisps, it just does nothing.</p>

<p>Throughout VL, we call @('vl-gc') at \"good\" places to do garbage
collection.  We typically call it right after computations that allocate a lot
of \"temporary\" memory&mdash;memory that will be garbage once the computation
has finished.  A GC at this time may be cheaper than a GC later, when we just
happen to run out of memory, because GC costs are basically proportional to the
number of live objects.</p>

<p>Running @('vl-gc') only sometimes triggers a GC.  Why?  We sometimes use VL
to process large designs (hundreds of thousands of lines of Verilog), and
sometimes use it on much smaller designs.  Depending on the kind of input, we
probably want to use different GC strategies:</p>

<ul>

<li>When we process large designs, each transformation naturally allocates more
memory.  Some transforms might allocate hundreds of megabytes or gigabytes of
memory.  In this case, we would like to GC more frequently in order to keep our
memory usage down.</li>

<li>When we deal with small designs, nothing is very expensive.  We probably
have ample memory to process the whole design without any garbage collection.
In this case, we would like to avoid GC altogether to maximize
performance.</li>

</ul>

<p>@('vl-gc') is meant to work well with either scenario.  Basically, after
triggering a GC, @('vl-gc') records how much memory are allocated.  This gives
us a rough baseline of how much memory the rest of the program is using.  Then,
each time @('vl-gc') is called, it compares the current memory usage to this
baseline.  A GC is only triggered if the new memory usage exceeds the baseline
by some threshold (e.g., 1 GB).</p>

<p>Here's how this works under either scenario.</p>

<ul>

<li>When we process a large design, our transforms are consuming memory quite
quickly, so the @('vl-gc') calls throughout our program end up causing many
GCs.  These GCs occur at good places (the places where we called @('vl-gc'),
and keep our memory usage down, as desired.</li>

<li>When we process a small design, our transforms don't use much memory so
when we call @('vl-gc'), we haven't exceeded the threshold.  So, we don't waste
our time collecting this insignificant garbage, as desired.</li>

</ul>"

  :returns (nil)

  (raise "Under-the-hood definition not installed?"))


(define set-vl-gc-baseline ()
  :parents (vl-gc)
  :short "Resets the baseline for @(see vl-gc) to however much memory is
currently allocated."
  :long "<p>This may sometimes be worth calling at the start of a script.</p>"
  :returns (nil)
  (raise "Under-the-hood definition not installed?"))

(define set-vl-gc-threshold ((bytes natp))
  :parents (vl-gc)
  :short "Instruct @(see vl-gc) to trigger a garbage collection when the
current memory usage exceeds the baseline by some amount."

  :long "<p>The default is 1 GB (2^30 bytes).  You might want to raise this
threshold if garbage is being collected too frequently.</p>"

  :returns (nil)
  (declare (ignore bytes))
  (raise "Under-the-hood definition not installed?"))


(defttag vl-gc)
(acl2::include-raw "gc-raw.lsp")

