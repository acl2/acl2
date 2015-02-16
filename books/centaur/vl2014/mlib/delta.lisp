; VL 2014 -- VL Verilog Toolkit, 2014 Edition
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
(include-book "namefactory")
(local (include-book "../util/arithmetic"))
(local (std::add-default-post-define-hook :fix))

(defprod vl-delta
  :parents (transforms)
  :short "A set of changes to be made to a module."
  :tag nil
  :layout :tree
  ((nf        vl-namefactory-p)
   (vardecls  vl-vardecllist-p)
   (assigns   vl-assignlist-p)
   (modinsts  vl-modinstlist-p)
   (gateinsts vl-gateinstlist-p)
   (warnings  vl-warninglist-p)
   (addmods   vl-modulelist-p))
  :long "<p>An @(see vl-delta-p) is mostly just a bunch of accumulators of
different types, which may be useful when writing a transform that makes
updates to a module.  It also has a @(see vl-namefactory-p) which can be used
to generate fresh names.</p>

<p>What is this all about?</p>

<p>Many simple transforms just walk through a module's elements and rewrite
them in some \"local\" way.  For instance, to size expressions or resolve
arguments, we're just walking over the existing module elements and annotating
or changing them.  These sorts of transforms usually have no need for a
delta.</p>

<p>Deltas become useful when a transform needs to rewrite the module elements
in some way that depends on <i>other stuff</i> being added to the module and/or
to the module list.  For example:</p>

<ul>

<li>When we split up expressions, we might rewrite @('a + b') into @('tmp'),
while also adding @('wire[3:0] tmp') and @('assign tmp = a + b') to the
module.</li>

<li>When we turn expressions into occurrences, we might delete @('assign tmp =
a + b') altogether, while adding @({VL_4_BIT_PLUS _adder_123 (tmp, a, b)}) to
the module and adding @('VL_4_BIT_PLUS') and its supporting modules in the
module list.</li>

</ul>

<p>We found that writing these kinds of transforms meant passing around several
different accumulators for the different types of elements we wanted to add.
It is quite painful to write a whole set of functions that take, say, five
accumulators, and to prove even the simple type theorems about them.  A delta
is mainly just a bundle of these accumulators, which greatly simplifies the
code for transforms like @(see split).</p>

<p>We found it useful to add a @(see vl-namefactory-p) to the delta, since that
way any transform that wants to generate fresh names can do so easily.</p>")

(local (xdoc::set-default-parents vl-delta-p))

(define vl-warn-delta
  :short "Add a warning to a delta."
  ((warning vl-warning-p) &key ((delta vl-delta-p) 'delta))
  :returns (delta vl-delta-p)
  :long "<p>Usually you will want to use @(see dwarn) instead because it allows
you to construct the warning inline.  But, occasionally, the warning to add has
already been constructed, in which case @('vl-warn-delta') is what you
want.</p>"
  (change-vl-delta delta
                   :warnings (cons (vl-warning-fix warning)
                                   (vl-delta->warnings delta))))


(defsection dwarn
  :short "Make a @(see vl-warning-p) and add it to a @(see vl-delta-p)."
  :long "<p>This is just a convenient shorthand.</p>

<p>@(call dwarn) extends @('delta') with a new warning with the given @('type'),
@('msg'), etc.</p>

<p>Since @('delta') defaults to @(''delta'), you can omit it in the common case
that your @(see vl-delta-p) is called @('delta').</p>"

  (defmacro dwarn (&key (delta 'delta)
                        type msg args fatalp
                        (fn '__function__))
    `(vl-warn-delta (make-vl-warning :type   ,type
                                     :msg    ,msg
                                     :args   ,args
                                     :fatalp ,fatalp
                                     :fn     ,fn)
                    :delta ,delta)))

(define vl-starting-delta
  :short "Build an initial @(see vl-delta-p) for the module @('x')."
 ((x vl-module-p))
  :returns delta
  :long "<p>The new delta has an appropriate starting namefactory for the
module, and is also seeded with the module's @(see warnings).  The other
accumulators are all empty to begin with.</p>"
  :enabled t
  (make-vl-delta :nf       (vl-starting-namefactory x)
                 :warnings (vl-module->warnings x)
                 :vardecls nil
                 :assigns  nil
                 :modinsts nil
                 :addmods  nil))


(define vl-free-delta
  :short "Frees the namefactory within a @(see vl-delta-p) and returns
@('delta')."
 ((delta vl-delta-p))
  :returns (delta vl-delta-p)
  :enabled t
  (b* (((vl-delta delta) delta))
    (vl-free-namefactory delta.nf)
    (vl-delta-fix delta)))

