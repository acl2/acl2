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
(include-book "namefactory")
(local (include-book "../util/arithmetic"))

(defaggregate vl-delta
  :parents (transforms)
  :short "A set of changes to be made to a module."
  ((nf        vl-namefactory-p)
   (netdecls  vl-netdecllist-p)
   (assigns   vl-assignlist-p)
   (modinsts  vl-modinstlist-p)
   (gateinsts vl-gateinstlist-p)
   (warnings  vl-warninglist-p)
   (addmods   vl-modulelist-p))
  :tag nil
  :legiblep nil

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

(define vl-warn-delta ((warning vl-warning-p)
                       &key
                       ((delta vl-delta-p) 'delta))
  :returns (delta vl-delta-p :hyp :fguard)
  :parents (vl-delta-p)
  :short "Add a warning to a delta."
  :long "<p>Usually you will want to use @(see dwarn) instead because it allows
you to construct the warning inline.  But, occasionally, the warning to add has
already been constructed, in which case @('vl-warn-delta') is what you
want.</p>"
  (change-vl-delta delta
                   :warnings (cons warning (vl-delta->warnings delta))))


(defsection dwarn
  :parents (vl-delta-p)
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

(define vl-starting-delta ((x vl-module-p))
  :returns delta
  :parents (vl-delta-p)
  :short "@(call vl-starting-delta) builds a fresh @(see vl-delta-p) for the
module @('x')."

  :long "<p>The new delta has an appropriate starting namefactory for the
module, and is also seeded with the module's @(see warnings).  The other
accumulators are all empty to begin with.</p>"

  :enabled t

  (make-vl-delta :nf       (vl-starting-namefactory x)
                 :warnings (vl-module->warnings x)
                 :netdecls nil
                 :assigns  nil
                 :modinsts nil
                 :addmods  nil))


(define vl-free-delta ((delta vl-delta-p))
  :returns delta
  :parents (vl-delta-p)
  :short "@(call vl-free-delta) frees the namefactory within a @(see
vl-delta-p) and returns @('delta')."
  :enabled t

  (b* (((vl-delta delta) delta))
    (vl-free-namefactory delta.nf)
    delta))

